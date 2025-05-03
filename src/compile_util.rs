use std::{
    ops::ControlFlow,
    path::{Path, PathBuf},
    process::Command,
    sync::Arc,
};

use etrace::ok_or;
use rustc_errors::{
    emitter::{Emitter, HumanEmitter},
    fallback_fluent_bundle,
    registry::Registry,
    translation::Translate,
    ColorConfig, DiagInner, FatalError, FluentBundle, Level,
};
use rustc_feature::UnstableFeatures;
use rustc_hash::FxHashMap;
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
    config::{CrateType, ErrorOutputType, Input, Options},
    EarlyDiagCtxt,
};
use rustc_span::{def_id::DefId, edition::Edition, source_map::SourceMap, FileName, Symbol};

use crate::rustc_middle::ty::{TypeSuperVisitable, TypeVisitable};

pub trait Pass: Sync {
    type Out: Send;

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out;

    #[inline]
    fn try_on_input(&self, input: Input) -> Result<Self::Out, FatalError> {
        run_compiler(make_config(input), |tcx| self.run(tcx))
    }

    #[inline]
    fn try_on_path(&self, path: &Path) -> Result<Self::Out, FatalError> {
        self.try_on_input(path_to_input(path))
    }

    #[inline]
    fn try_on_str(&self, code: &str) -> Result<Self::Out, FatalError> {
        self.try_on_input(str_to_input(code))
    }

    #[inline]
    fn run_on_input(&self, input: Input) -> Self::Out {
        self.try_on_input(input).unwrap()
    }

    #[inline]
    fn run_on_path(&self, path: &Path) -> Self::Out {
        self.try_on_path(path).unwrap()
    }

    #[inline]
    fn run_on_str(&self, code: &str) -> Self::Out {
        self.try_on_str(code).unwrap()
    }
}

#[inline]
pub fn run_compiler<R: Send, F: FnOnce(TyCtxt<'_>) -> R + Send>(
    config: Config,
    f: F,
) -> Result<R, FatalError> {
    rustc_driver::catch_fatal_errors(|| {
        rustc_interface::run_compiler(config, |compiler| {
            let krate = rustc_interface::parse(&compiler.sess);
            rustc_interface::create_and_enter_global_ctxt(compiler, krate, f)
        })
    })
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
        crate_cfg: Vec::new(),
        crate_check_cfg: Vec::new(),
        input,
        output_dir: None,
        output_file: None,
        ice_file: None,
        file_loader: None,
        locale_resources: rustc_driver::DEFAULT_LOCALE_RESOURCES.to_vec(),
        lint_caps: FxHashMap::default(),
        psess_created: Some(Box::new(|ps| {
            let sm = ps.clone_source_map();
            ps.dcx().set_emitter(Box::new(SilentEmitter::new(sm)));
        })),
        register_lints: None,
        override_queries: None,
        make_codegen_backend: None,
        registry: Registry::new(rustc_errors::codes::DIAGNOSTICS),
        hash_untracked_state: None,
        using_internal_features: &rustc_driver::USING_INTERNAL_FEATURES,
        expanded_args: Vec::new(),
    }
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

struct SilentEmitter(HumanEmitter);

impl SilentEmitter {
    fn new(sm: Arc<SourceMap>) -> Self {
        let bundle = fallback_fluent_bundle(rustc_driver::DEFAULT_LOCALE_RESOURCES.to_vec(), false);
        let emitter = HumanEmitter::new(
            rustc_errors::emitter::stderr_destination(ColorConfig::Auto),
            bundle,
        )
        .sm(Some(sm));
        Self(emitter)
    }
}

impl Translate for SilentEmitter {
    fn fluent_bundle(&self) -> Option<&FluentBundle> {
        #[allow(clippy::needless_borrow)]
        (&self.0).fluent_bundle()
    }

    fn fallback_fluent_bundle(&self) -> &FluentBundle {
        self.0.fallback_fluent_bundle()
    }
}

impl Emitter for SilentEmitter {
    fn source_map(&self) -> Option<&SourceMap> {
        self.0.source_map()
    }

    fn emit_diagnostic(&mut self, diag: DiagInner, registry: &Registry) {
        if matches!(diag.level(), Level::Fatal | Level::Error) {
            self.0.emit_diagnostic(diag, registry);
        }
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

    let mut handler = EarlyDiagCtxt::new(ErrorOutputType::default());
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

#[inline]
pub fn def_id_to_ty_symbol(id: impl IntoQueryParam<DefId>, tcx: TyCtxt<'_>) -> Option<Symbol> {
    let key = tcx.def_key(id);
    let DefPathData::TypeNs(name) = key.disambiguated_data.data else { return None };
    Some(name)
}

pub fn is_std_io_expr<'tcx>(expr: &Expr<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let ExprKind::Path(QPath::Resolved(_, path)) = expr.kind else { return false };
    let Res::Def(DefKind::Static { .. }, def_id) = path.res else { return false };
    if !tcx.is_foreign_item(def_id) {
        return false;
    }
    let name = def_id_to_value_symbol(def_id, tcx).unwrap();
    let name = name.as_str();
    name == "stdin" || name == "stdout" || name == "stderr"
}

#[inline]
pub fn is_file_ty(id: impl IntoQueryParam<DefId>, tcx: TyCtxt<'_>) -> bool {
    def_id_to_ty_symbol(id, tcx).is_some_and(|name| name.as_str() == "_IO_FILE")
}

#[inline]
pub fn is_option_ty(id: impl IntoQueryParam<DefId>, tcx: TyCtxt<'_>) -> bool {
    def_id_to_ty_symbol(id, tcx).is_some_and(|name| name.as_str() == "Option")
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
    type Result = ControlFlow<()>;

    fn visit_ty(&mut self, t: Ty<'tcx>) -> Self::Result {
        if let TyKind::Adt(adt_def, _) = t.kind() {
            if is_file_ty(adt_def.did(), self.tcx) {
                return ControlFlow::Break(());
            }
        }
        t.super_visit_with(self)
    }
}
