use std::collections::{HashMap, HashSet};

use etrace::some_or;
use lazy_static::lazy_static;
use rustc_hir::{
    def::{DefKind, Res},
    def_id::LocalDefId,
    intravisit::{self, Visitor as HVisitor},
    BodyId, Expr, ExprKind, FieldDef, FnDecl, FnRetTy, ForeignItemKind, HirId, Item, ItemKind,
    MutTy, Node, QPath, TyKind,
};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};
use rustc_span::Symbol;
use tracing::info;

use crate::compile_util::Pass;

#[derive(Debug, Clone, Copy)]
pub struct ExternFinder;

impl Pass for ExternFinder {
    type Out = ();

    fn run(&self, tcx: TyCtxt<'_>) {
        let hir = tcx.hir();
        let mut visitor = ExternVisitor::new(tcx);
        hir.visit_all_item_likes_in_crate(&mut visitor);

        println!(
            "{} {} {} {} ",
            visitor.file_locals.len(),
            visitor.file_statics.len(),
            visitor.file_fields.len(),
            visitor.custom_file_fns.len(),
        );

        let mut counts: HashMap<_, usize> = HashMap::new();
        for (_caller, callees) in visitor.file_calls {
            for (callee, not_stdio) in callees {
                let file_fn = &visitor.file_fns[&callee];
                let name = file_fn.name.to_ident_string();
                let name = strip_unlocked(&name).to_string();
                *counts.entry((name, not_stdio)).or_default() += 1;
            }
        }

        for api in FILE_API_NAMES {
            let n = counts.get(&(api.to_string(), true)).copied().unwrap_or(0);
            let m = counts.get(&(api.to_string(), false)).copied().unwrap_or(0);
            print!("{} {} ", n, m);
        }
        for api in STDIO_API_NAMES {
            assert!(!counts.contains_key(&(api.to_string(), true)));
            let n = counts.get(&(api.to_string(), false)).copied().unwrap_or(0);
            print!("{} ", n);
        }
        println!();
    }
}

struct ExternVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    file_fns: HashMap<LocalDefId, FileFn>,
    custom_file_fns: HashSet<LocalDefId>,
    file_internal_fns: HashSet<LocalDefId>,
    file_calls: HashMap<LocalDefId, Vec<(LocalDefId, bool)>>,
    file_locals: HashSet<HirId>,
    file_statics: HashSet<LocalDefId>,
    file_fields: HashSet<LocalDefId>,
}

impl<'tcx> ExternVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            file_fns: HashMap::new(),
            custom_file_fns: HashSet::new(),
            file_internal_fns: HashSet::new(),
            file_calls: HashMap::new(),
            file_locals: HashSet::new(),
            file_statics: HashSet::new(),
            file_fields: HashSet::new(),
        }
    }
}

impl<'tcx> HVisitor<'tcx> for ExternVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        self.handle_expr(expr);
        intravisit::walk_expr(self, expr);
    }

    fn visit_item(&mut self, item: &'tcx Item<'tcx>) {
        self.handle_item(item);
        intravisit::walk_item(self, item);
    }

    fn visit_field_def(&mut self, fd: &'tcx FieldDef<'tcx>) {
        if self.has_file_ty(fd.ty) {
            self.file_fields.insert(fd.def_id);
        }
        intravisit::walk_field_def(self, fd);
    }

    fn visit_local(&mut self, local: &'tcx rustc_hir::Local<'tcx>) {
        self.handle_local(local);
        intravisit::walk_local(self, local);
    }

    fn visit_fn(
        &mut self,
        fk: intravisit::FnKind<'tcx>,
        fd: &'tcx FnDecl<'tcx>,
        body_id: BodyId,
        _: rustc_span::Span,
        def_id: LocalDefId,
    ) {
        if let Some(file_fn) = self.get_file_fn(def_id) {
            if !file_fn.is_libc {
                self.custom_file_fns.insert(def_id);
            }
        }
        intravisit::walk_fn(self, fk, fd, body_id, def_id);
    }
}

impl<'tcx> ExternVisitor<'tcx> {
    fn handle_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        let current_func = expr.hir_id.owner.def_id;
        if let Some(file_fn) = self.get_file_fn(current_func) {
            if file_fn.is_libc {
                return;
            }
        }
        match expr.kind {
            ExprKind::Call(callee, args) => {
                let ExprKind::Path(QPath::Resolved(_, path)) = callee.kind else { return };
                let Res::Def(DefKind::Fn, def_id) = path.res else { return };
                let def_id = some_or!(def_id.as_local(), return);
                let file_fn = some_or!(self.get_file_fn(def_id), return);
                if !file_fn.is_libc {
                    return;
                }
                let not_stdio = file_fn.returns_file
                    || file_fn
                        .file_params
                        .iter()
                        .any(|i| !self.is_std_io(&args[*i]));
                self.file_calls
                    .entry(current_func)
                    .or_default()
                    .push((def_id, not_stdio));
                for i in &file_fn.file_params {
                    let arg = &args[*i];
                    if self.is_std_io(arg) {
                        continue;
                    }
                    info!(
                        "{}",
                        self.tcx
                            .sess
                            .source_map()
                            .span_to_snippet(arg.span)
                            .unwrap()
                    );
                }
            }
            ExprKind::Field(e, _) => {
                let ty = self.tcx.typeck(current_func).expr_ty(e);
                let rustc_middle::ty::TyKind::Adt(adt_def, _) = ty.kind() else { return };
                let node = some_or!(self.tcx.hir().get_if_local(adt_def.did()), return);
                let Node::Item(item) = node else { return };
                if item.ident.name.to_ident_string() == "_IO_FILE" {
                    self.file_internal_fns.insert(current_func);
                }
            }
            _ => {}
        }
    }

    fn handle_item(&mut self, item: &'tcx Item<'tcx>) {
        let ItemKind::Static(ty, _, _) = item.kind else { return };
        if self.has_file_ty(ty) {
            self.file_statics.insert(item.owner_id.def_id);
        }
    }

    fn handle_local(&mut self, local: &'tcx rustc_hir::Local<'tcx>) {
        let ty = some_or!(local.ty, return);
        if self.has_file_ty(ty) {
            self.file_locals.insert(local.hir_id);
        }
    }

    fn get_file_fn(&mut self, def_id: LocalDefId) -> Option<FileFn> {
        if let Some(api_fn) = self.file_fns.get(&def_id) {
            return Some(api_fn.clone());
        }
        let node = self.tcx.hir().get_if_local(def_id.to_def_id()).unwrap();
        let (name, decl, is_extern) = match node {
            Node::Item(item) => {
                let ItemKind::Fn(sig, _, _) = item.kind else { return None };
                (item.ident.name, sig.decl, false)
            }
            Node::ForeignItem(item) => {
                let ForeignItemKind::Fn(decl, _, _) = item.kind else { return None };
                (item.ident.name, decl, true)
            }
            _ => return None,
        };
        let file_params: Vec<_> = decl
            .inputs
            .iter()
            .enumerate()
            .filter_map(|(i, ty)| if self.has_file_ty(ty) { Some(i) } else { None })
            .collect();
        let returns_file = if let FnRetTy::Return(ty) = decl.output {
            self.has_file_ty(ty)
        } else {
            false
        };
        let name_string = name.to_ident_string();
        let name_str = strip_unlocked(&name_string);
        let is_libc = if !file_params.is_empty() || returns_file {
            let is_api = FILE_API_NAME_SET.contains(name_str);
            if is_extern {
                assert!(is_api, "{}", name_string);
                true
            } else {
                is_api
            }
        } else if STDIO_API_NAME_SET.contains(name_str) {
            true
        } else {
            return None;
        };
        let api_fn = FileFn {
            name,
            file_params,
            returns_file,
            is_libc,
        };
        self.file_fns.insert(def_id, api_fn.clone());
        Some(api_fn)
    }

    fn has_file_ty(&self, ty: &'tcx rustc_hir::Ty<'tcx>) -> bool {
        let mut visitor = TyVisitor::new(self.tcx);
        visitor.visit_ty(ty);
        if visitor.has_file {
            info!(
                "{}",
                self.tcx.sess.source_map().span_to_snippet(ty.span).unwrap()
            );
        }
        visitor.has_file
    }

    fn is_std_io(&self, expr: &'tcx Expr<'tcx>) -> bool {
        let ExprKind::Path(QPath::Resolved(_, path)) = expr.kind else { return false };
        let Res::Def(DefKind::Static(_), def_id) = path.res else { return false };
        if !self.tcx.is_foreign_item(def_id) {
            return false;
        }
        let name = path.segments.last().unwrap().ident.name.to_ident_string();
        name == "stdin" || name == "stdout" || name == "stderr"
    }
}

#[derive(Debug, Clone)]
struct FileFn {
    name: Symbol,
    file_params: Vec<usize>,
    returns_file: bool,
    is_libc: bool,
}

struct TyVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    has_file: bool,
}

impl<'tcx> TyVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            has_file: false,
        }
    }
}

impl<'tcx> HVisitor<'tcx> for TyVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_ty(&mut self, t: &'tcx rustc_hir::Ty<'tcx>) {
        if let rustc_hir::TyKind::Path(QPath::Resolved(_, path)) = t.kind {
            let seg = path.segments.last().unwrap();
            let name = seg.ident.name.to_ident_string();
            if name == "FILE" {
                self.has_file = true;
            }
        }
        intravisit::walk_ty(self, t)
    }
}

fn strip_unlocked(name: &str) -> &str {
    name.strip_suffix("_unlocked").unwrap_or(name)
}

static FILE_API_NAMES: [&str; 46] = [
    "fopen",
    "tmpfile",
    "fclose",
    "putc",
    "fputc",
    "fputs",
    "fprintf",
    "vfprintf",
    "fwrite",
    "fflush",
    "getc",
    "fgetc",
    "fgets",
    "fscanf",
    "vfscanf",
    "getline",
    "getdelim",
    "fread",
    "ungetc",
    "fseek",
    "fseeko",
    "ftell",
    "ftello",
    "rewind",
    "funlockfile",
    "flockfile",
    "popen",
    "pclose",
    "fileno",
    "fdopen",
    "ferror",
    "feof",
    "clearerr",
    "freopen",
    "setvbuf",
    "setbuf",
    "setlinebuf",
    "fpurge",
    "endmntent",
    "getmntent",
    "setmntent",
    "fgetpos",
    "fsetpos",
    "__fpending",
    "__freading",
    "__fwriting",
];
static STDIO_API_NAMES: [&str; 8] = [
    "putchar", "puts", "printf", "vprintf", "getchar", "gets", "scanf", "vscanf",
];

lazy_static! {
    static ref FILE_API_NAME_SET: HashSet<&'static str> = FILE_API_NAMES.iter().copied().collect();
    static ref STDIO_API_NAME_SET: HashSet<&'static str> =
        STDIO_API_NAMES.iter().copied().collect();
}

#[derive(Clone, Copy)]
#[repr(transparent)]
struct FmtTy<'tcx>(rustc_hir::Ty<'tcx>);

impl std::fmt::Display for FmtTy<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0.kind {
            TyKind::Slice(t) => write!(f, "[{}]", FmtTy(*t)),
            TyKind::Array(t, _) => write!(f, "[{}; _]", FmtTy(*t)),
            TyKind::Ptr(MutTy { ty, mutbl }) => {
                write!(
                    f,
                    "*{} {}",
                    if mutbl.is_mut() { "mut" } else { "const" },
                    FmtTy(*ty)
                )
            }
            TyKind::Ref(_, MutTy { ty, mutbl }) => {
                write!(
                    f,
                    "&{}{}",
                    if mutbl.is_mut() { "mut " } else { "" },
                    FmtTy(*ty)
                )
            }
            TyKind::BareFn(fn_ty) => {
                write!(f, "fn(")?;
                for t in fn_ty.decl.inputs {
                    write!(f, "{}, ", FmtTy(*t))?;
                }
                write!(f, ")")?;
                if let FnRetTy::Return(t) = fn_ty.decl.output {
                    write!(f, " -> {}", FmtTy(*t))?;
                }
                Ok(())
            }
            TyKind::Never => write!(f, "!"),
            TyKind::Tup(tys) => {
                write!(f, "(")?;
                for t in tys {
                    write!(f, "{}, ", FmtTy(*t))?;
                }
                write!(f, ")")
            }
            TyKind::Path(path) => {
                if let QPath::Resolved(_, path) = path {
                    for seg in path.segments {
                        write!(f, "::{}", seg.ident.name.to_ident_string())?;
                    }
                }
                write!(f, "")
            }
            _ => write!(f, "_"),
        }
    }
}
