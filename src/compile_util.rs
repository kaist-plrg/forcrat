use std::{
    ops::ControlFlow,
    path::{Path, PathBuf},
    process::Command,
    sync::{Arc, Mutex},
};

use etrace::ok_or;
use rustc_data_structures::sync::Lrc;
use rustc_errors::{
    emitter::Emitter, registry::Registry, translation::Translate, FluentBundle, Handler, Level,
};
use rustc_feature::UnstableFeatures;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    def::{DefKind, Res},
    definitions::DefPathData,
    Expr, ExprKind, QPath,
};
use rustc_interface::Config;
use rustc_middle::{
    mir::{Body, TerminatorKind},
    query::IntoQueryParam,
    ty::{Ty, TyCtxt, TyKind, TypeVisitor},
};
use rustc_session::{
    config::{CheckCfg, CrateType, ErrorOutputType, Input, Options},
    EarlyErrorHandler,
};
use rustc_span::{
    def_id::DefId,
    edition::Edition,
    source_map::{FileName, SourceMap},
    RealFileName, Span, Symbol,
};

use crate::rustc_middle::ty::{TypeSuperVisitable, TypeVisitable};

pub trait Pass: Sync {
    type Out: Send;

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out;

    #[inline]
    fn config(input: Input) -> Config {
        make_no_warning_config(input)
    }

    #[inline]
    fn run_on_input(&self, input: Input) -> Self::Out {
        let config = Self::config(input);
        run_compiler(config, |tcx| self.run(tcx)).unwrap()
    }

    #[inline]
    fn run_on_path(&self, path: &Path) -> Self::Out {
        self.run_on_input(path_to_input(path))
    }

    #[inline]
    fn run_on_str(&self, code: &str) -> Self::Out {
        self.run_on_input(str_to_input(code))
    }
}

#[inline]
pub fn run_compiler<R: Send, F: FnOnce(TyCtxt<'_>) -> R + Send>(config: Config, f: F) -> Option<R> {
    rustc_driver::catch_fatal_errors(|| {
        rustc_interface::run_compiler(config, |compiler| {
            compiler.enter(|queries| queries.global_ctxt().ok()?.enter(|tcx| Some(f(tcx))))
        })
    })
    .ok()?
}

#[inline]
pub fn make_config(input: Input) -> Config {
    let opts = find_deps();
    Config {
        opts: Options {
            maybe_sysroot: Some(PathBuf::from(sys_root())),
            search_paths: opts.search_paths,
            externs: opts.externs,
            unstable_features: UnstableFeatures::Allow,
            crate_types: vec![CrateType::Rlib],
            debug_assertions: false,
            edition: Edition::Edition2021,
            ..Options::default()
        },
        crate_cfg: FxHashSet::default(),
        crate_check_cfg: CheckCfg::default(),
        input,
        output_dir: None,
        output_file: None,
        ice_file: rustc_driver::ice_path().clone(),
        file_loader: None,
        locale_resources: rustc_driver_impl::DEFAULT_LOCALE_RESOURCES,
        lint_caps: FxHashMap::default(),
        parse_sess_created: None,
        register_lints: None,
        override_queries: None,
        make_codegen_backend: None,
        registry: Registry::new(rustc_error_codes::DIAGNOSTICS),
    }
}

pub fn make_no_warning_config(input: Input) -> Config {
    let mut config = make_config(input);
    config.parse_sess_created = Some(Box::new(|ps| {
        let mut dummy = Handler::with_emitter(Box::new(SilentEmitter));
        std::mem::swap(&mut ps.span_diagnostic, &mut dummy);
        dummy = dummy.disable_warnings();
        std::mem::swap(&mut ps.span_diagnostic, &mut dummy);
    }));
    config
}

pub fn make_silent_config(input: Input) -> Config {
    let mut config = make_config(input);
    config.parse_sess_created = Some(Box::new(|ps| {
        ps.span_diagnostic = Handler::with_emitter(Box::new(SilentEmitter));
    }));
    config
}

pub fn make_counting_config(input: Input) -> (Config, Arc<Mutex<usize>>) {
    let mut config = make_config(input);
    let arc = Arc::new(Mutex::new(0));
    let emitter = CountingEmitter(arc.clone());
    config.parse_sess_created = Some(Box::new(|ps| {
        ps.span_diagnostic = Handler::with_emitter(Box::new(emitter));
    }));
    (config, arc)
}

pub fn str_to_input(code: &str) -> Input {
    Input::Str {
        name: FileName::Custom("main.rs".to_string()),
        input: code.to_string(),
    }
}

pub fn path_to_input(path: &Path) -> Input {
    Input::File(path.to_path_buf())
}

pub fn span_to_path(span: Span, source_map: &SourceMap) -> Option<PathBuf> {
    if let FileName::Real(RealFileName::LocalPath(p)) = source_map.span_to_filename(span) {
        Some(p)
    } else {
        None
    }
}

struct CountingEmitter(Arc<Mutex<usize>>);

impl Translate for CountingEmitter {
    fn fluent_bundle(&self) -> Option<&Lrc<FluentBundle>> {
        None
    }

    fn fallback_fluent_bundle(&self) -> &FluentBundle {
        panic!()
    }
}

impl Emitter for CountingEmitter {
    fn emit_diagnostic(&mut self, diag: &rustc_errors::Diagnostic) {
        if matches!(diag.level(), Level::Error { .. }) {
            *self.0.lock().unwrap() += 1;
        }
    }

    fn source_map(&self) -> Option<&Lrc<SourceMap>> {
        None
    }
}

#[derive(Debug, Clone, Copy)]
pub struct SilentEmitter;

impl Translate for SilentEmitter {
    fn fluent_bundle(&self) -> Option<&Lrc<FluentBundle>> {
        None
    }

    fn fallback_fluent_bundle(&self) -> &FluentBundle {
        panic!()
    }
}

impl Emitter for SilentEmitter {
    fn emit_diagnostic(&mut self, _: &rustc_errors::Diagnostic) {}

    fn source_map(&self) -> Option<&Lrc<SourceMap>> {
        None
    }
}

fn find_deps() -> Options {
    let mut args = vec!["a.rs".to_string()];

    let dir = std::env::var("DIR").unwrap_or_else(|_| ".".to_string());
    let dep = format!("{}/deps_crate/target/debug/deps", dir);
    if let Ok(dir) = std::fs::read_dir(&dep) {
        args.push("-L".to_string());
        args.push(format!("dependency={}", dep));

        for f in dir {
            let f = ok_or!(f, continue);
            let f = f.file_name().to_str().unwrap().to_string();
            if !f.ends_with(".rlib") {
                continue;
            }
            let i = f.find('-').unwrap();
            let name = f[3..i].to_string();
            let d = format!("{}={}/{}", name, dep, f);
            args.push("--extern".to_string());
            args.push(d);
        }
    }

    let mut handler = EarlyErrorHandler::new(ErrorOutputType::default());
    let matches = rustc_driver::handle_options(&handler, &args).unwrap();
    rustc_session::config::build_session_options(&mut handler, &matches)
}

fn sys_root() -> String {
    std::env::var("SYSROOT")
        .ok()
        .map(PathBuf::from)
        .or_else(|| {
            let home = std::env::var("RUSTUP_HOME")
                .or_else(|_| std::env::var("MULTIRUST_HOME"))
                .ok();
            let toolchain = std::env::var("RUSTUP_TOOLCHAIN")
                .or_else(|_| std::env::var("MULTIRUST_TOOLCHAIN"))
                .ok();
            toolchain_path(home, toolchain)
        })
        .or_else(|| {
            Command::new("rustc")
                .arg("--print")
                .arg("sysroot")
                .output()
                .ok()
                .and_then(|out| String::from_utf8(out.stdout).ok())
                .map(|s| PathBuf::from(s.trim()))
        })
        .or_else(|| option_env!("SYSROOT").map(PathBuf::from))
        .or_else(|| {
            let home = option_env!("RUSTUP_HOME")
                .or(option_env!("MULTIRUST_HOME"))
                .map(ToString::to_string);
            let toolchain = option_env!("RUSTUP_TOOLCHAIN")
                .or(option_env!("MULTIRUST_TOOLCHAIN"))
                .map(ToString::to_string);
            toolchain_path(home, toolchain)
        })
        .map(|pb| pb.to_string_lossy().to_string())
        .unwrap()
}

fn toolchain_path(home: Option<String>, toolchain: Option<String>) -> Option<PathBuf> {
    home.and_then(|home| {
        toolchain.map(|toolchain| {
            let mut path = PathBuf::from(home);
            path.push("toolchains");
            path.push(toolchain);
            path
        })
    })
}

pub fn body_to_str(body: &Body<'_>) -> String {
    use std::fmt::Write;
    let mut s = String::new();
    for bbd in body.basic_blocks.iter() {
        for stmt in &bbd.statements {
            writeln!(s, "{:?}", stmt).unwrap();
        }
        if !matches!(
            bbd.terminator().kind,
            TerminatorKind::Return | TerminatorKind::Assert { .. }
        ) {
            writeln!(s, "{:?}", bbd.terminator().kind).unwrap();
        }
    }
    s
}

#[inline]
pub fn def_id_to_value_symbol(id: impl IntoQueryParam<DefId>, tcx: TyCtxt<'_>) -> Option<Symbol> {
    let key = tcx.def_key(id);
    let DefPathData::ValueNs(name) = key.disambiguated_data.data else { return None };
    Some(name)
}

pub fn is_std_io_expr<'tcx>(expr: &Expr<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let ExprKind::Path(QPath::Resolved(_, path)) = expr.kind else { return false };
    let Res::Def(DefKind::Static(_), def_id) = path.res else { return false };
    if !tcx.is_foreign_item(def_id) {
        return false;
    }
    let name = def_id_to_value_symbol(def_id, tcx).unwrap();
    let name = name.as_str();
    name == "stdin" || name == "stdout" || name == "stderr"
}

#[inline]
pub fn is_file_ty(id: impl IntoQueryParam<DefId>, tcx: TyCtxt<'_>) -> bool {
    let key = tcx.def_key(id);
    let DefPathData::TypeNs(name) = key.disambiguated_data.data else { return false };
    name.as_str() == "_IO_FILE"
}

#[inline]
pub fn contains_file_ty<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let mut visitor = FileTypeVisitor { tcx };
    ty.visit_with(&mut visitor).is_break()
}

struct FileTypeVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for FileTypeVisitor<'tcx> {
    type BreakTy = ();

    fn visit_ty(&mut self, t: Ty<'tcx>) -> ControlFlow<Self::BreakTy> {
        if let TyKind::Adt(adt_def, _) = t.kind() {
            if is_file_ty(adt_def.did(), self.tcx) {
                return ControlFlow::Break(());
            }
        }
        t.super_visit_with(self)
    }
}
