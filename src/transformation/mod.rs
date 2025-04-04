use std::{
    fmt::Write as _,
    fs,
    ops::{Deref, DerefMut},
};

use etrace::some_or;
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_ast::{
    ast::*,
    mut_visit,
    mut_visit::MutVisitor,
    ptr::P,
    visit::{self, Visitor},
};
use rustc_ast_pretty::pprust;
use rustc_const_eval::interpret::{ConstValue, Scalar};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{self as hir, def::Res, intravisit, HirId, QPath};
use rustc_index::Idx;
use rustc_lexer::unescape;
use rustc_middle::{
    hir::nested_filter,
    mir::{self, CastKind, Constant, ConstantKind, Location, Operand, Rvalue},
    ty::{self, AdtDef, TyCtxt},
};
use rustc_span::{def_id::LocalDefId, symbol::Ident, FileName, RealFileName, Span, Symbol};
use toml_edit::DocumentMut;
use typed_arena::Arena;

use crate::{
    api_list::{self, Origin, Permission},
    ast_maker::*,
    bit_set::BitSet8,
    compile_util::{self, Pass},
    file_analysis::{self, Loc},
    rustc_middle::mir::visit::Visitor as _,
};

pub fn write_to_files(res: &TransformationResult, dir: &std::path::Path) {
    for (f, s) in &res.files {
        let FileName::Real(RealFileName::LocalPath(p)) = f else { panic!() };
        fs::write(p, s).unwrap();
    }
    if res.tmpfile {
        let path = dir.join("Cargo.toml");
        let content = fs::read_to_string(&path).unwrap();
        let mut doc = content.parse::<DocumentMut>().unwrap();
        let dependencies = doc["dependencies"].as_table_mut().unwrap();
        if !dependencies.contains_key("tempfile") {
            dependencies["tempfile"] = toml_edit::value("3.19.1");
            fs::write(path, doc.to_string()).unwrap();
        }
    }
}

#[derive(Debug)]
pub struct TransformationResult {
    files: Vec<(FileName, String)>,
    tmpfile: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct Transformation;

impl Pass for Transformation {
    type Out = TransformationResult;

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out {
        // collect information from AST
        let stolen = tcx.resolver_for_lowering(()).borrow();
        let (_, krate) = stolen.deref();
        let mut ast_visitor = AstVisitor {
            static_span_to_lit: FxHashMap::default(),
        };
        visit::walk_crate(&mut ast_visitor, krate);
        drop(stolen);

        let hir = tcx.hir();
        let analysis_res = file_analysis::FileAnalysis.run(tcx);

        // collect information from HIR
        let mut hir_visitor = HirVisitor {
            tcx,
            ctx: HirCtx::default(),
        };
        hir.visit_all_item_likes_in_crate(&mut hir_visitor);
        let hir_ctx = hir_visitor.ctx;

        let is_stdin_unsupported = analysis_res
            .unsupported
            .contains(analysis_res.loc_ind_map[&Loc::Stdin]);
        // all unsupported spans
        let mut unsupported: FxHashSet<_> = analysis_res
            .unsupported
            .iter()
            .filter_map(|loc_id| {
                let loc = analysis_res.locs[loc_id];
                match loc {
                    Loc::Var(def_id, local) => {
                        let body = tcx.optimized_mir(def_id);
                        let local_decl = &body.local_decls[local];
                        let span = local_decl.source_info.span;
                        Some(span)
                    }
                    Loc::Field(_, _) => todo!(),
                    Loc::Stdin | Loc::Stdout | Loc::Stderr => None,
                }
            })
            .collect();
        let mut unsupported_locs = FxHashSet::default();
        for (span, loc) in &hir_ctx.binding_span_to_loc {
            if !unsupported.contains(span) {
                continue;
            }
            unsupported_locs.insert(*loc);
            let bounds = some_or!(hir_ctx.loc_to_bound_spans.get(loc), continue);
            for span in bounds {
                // add bound occurrence to unsupported
                unsupported.insert(*span);

                // add rhs to unsupported
                if let Some(span) = hir_ctx.lhs_to_rhs.get(span) {
                    unsupported.insert(*span);
                }
            }
        }

        let arena = Arena::new();
        let type_arena = TypeArena::new(&arena);
        let mut param_to_hir_loc = FxHashMap::default();
        let mut hir_loc_to_pot = FxHashMap::default();
        for ((loc, permissions), origins) in analysis_res
            .locs
            .iter()
            .zip(analysis_res.permissions.iter().copied())
            .zip(analysis_res.origins.iter().copied())
        {
            let (hir_loc, is_param) = match loc {
                Loc::Var(def_id, local) => {
                    let hir::Node::Item(item) = hir.get_by_def_id(*def_id) else { panic!() };
                    match item.kind {
                        hir::ItemKind::Fn(sig, _, _) => {
                            let body = tcx.optimized_mir(*def_id);
                            let local_decl = &body.local_decls[*local];
                            let span = local_decl.source_info.span;
                            let loc = *some_or!(hir_ctx.binding_span_to_loc.get(&span), continue);
                            let arity = sig.decl.inputs.len();
                            let is_param = (1..=arity).contains(&local.as_usize());
                            if is_param {
                                let param = Param {
                                    func: *def_id,
                                    index: local.as_usize() - 1,
                                };
                                param_to_hir_loc.insert(param, loc);
                            }
                            (loc, is_param)
                        }
                        hir::ItemKind::Static(_, _, _) => {
                            if local.as_u32() != 0 {
                                continue;
                            }
                            (HirLoc::Global(*def_id), false)
                        }
                        _ => panic!(),
                    }
                }
                Loc::Field(def_id, field) => (HirLoc::Field(*def_id, *field), false),
                _ => continue,
            };
            if unsupported_locs.contains(&hir_loc) {
                continue;
            }
            let ty = type_arena.make_ty(permissions, origins, is_param);
            let pot = Pot {
                permissions,
                origins,
                ty,
            };
            let old = hir_loc_to_pot.insert(hir_loc, pot);
            assert!(old.is_none());
        }
        for hir_loc in hir_ctx.loc_to_bound_spans.keys() {
            let HirLoc::Global(def_id) = hir_loc else { continue };
            let name = some_or!(compile_util::def_id_to_value_symbol(*def_id, tcx), continue);
            let (loc, ty) = match name.as_str() {
                "stdin" => (Loc::Stdin, &STDIN_TY),
                "stdout" => (Loc::Stdout, &STDOUT_TY),
                "stderr" => (Loc::Stderr, &STDERR_TY),
                _ => continue,
            };
            let loc_id = analysis_res.loc_ind_map[&loc];
            let permissions = analysis_res.permissions[loc_id];
            let origins = analysis_res.origins[loc_id];
            let pot = Pot {
                permissions,
                origins,
                ty,
            };
            let old = hir_loc_to_pot.insert(*hir_loc, pot);
            assert!(old.is_none());
        }

        let mut api_sig_spans = FxHashSet::default();
        let mut null_casts = FxHashSet::default();

        for item_id in hir.items() {
            let item = hir.item(item_id);
            let local_def_id = item.owner_id.def_id;
            if let hir::ItemKind::Fn(sig, _, _) = item.kind {
                if item.ident.name.as_str() == "main" {
                    continue;
                }
                if api_list::is_symbol_api(item.ident.name) {
                    api_sig_spans.insert(sig.span);
                    continue;
                }

                let body = tcx.optimized_mir(local_def_id);
                let mut visitor = MirVisitor {
                    tcx,
                    nulls: FxHashSet::default(),
                };
                visitor.visit_body(body);
                for location in visitor.nulls {
                    let stmt = body.stmt_at(location).left().unwrap();
                    null_casts.insert(stmt.source_info.span);
                }
            }
        }

        let source_map = tcx.sess.source_map();
        let parse_sess = new_parse_sess();
        let mut files = vec![];
        let mut tmpfile = false;

        for file in source_map.files().iter() {
            if !matches!(
                file.name,
                FileName::Real(RealFileName::LocalPath(_)) | FileName::Custom(_)
            ) {
                continue;
            }
            let src = some_or!(file.src.as_ref(), continue);
            let mut parser = rustc_parse::new_parser_from_source_str(
                &parse_sess,
                file.name.clone(),
                src.to_string(),
            );
            let mut krate = parser.parse_crate_mod().unwrap();
            let mut visitor = TransformVisitor {
                tcx,
                static_span_to_lit: &ast_visitor.static_span_to_lit,
                hir: &hir_ctx,
                param_to_loc: &param_to_hir_loc,
                loc_to_pot: &hir_loc_to_pot,
                api_sig_spans: &api_sig_spans,
                null_casts: &null_casts,
                unsupported: &unsupported,
                is_stdin_unsupported,

                updated: false,
                updated_field_spans: FxHashSet::default(),
                tmpfile: false,
            };
            visitor.visit_crate(&mut krate);
            if visitor.updated {
                for item in &mut krate.items {
                    let ItemKind::Struct(vd, _) = &item.kind else { continue };
                    let VariantData::Struct(fs, _) = vd else { continue };
                    if fs
                        .iter()
                        .any(|f| visitor.updated_field_spans.contains(&f.span))
                    {
                        item.attrs.clear();
                    }
                }

                let s = pprust::crate_to_string_for_macros(&krate);
                files.push((file.name.clone(), s));
                tmpfile |= visitor.tmpfile;
            }
        }

        TransformationResult { files, tmpfile }
    }
}

struct AstVisitor {
    /// static variable definition body span to its literal
    static_span_to_lit: FxHashMap<Span, Symbol>,
}

impl<'ast> Visitor<'ast> for AstVisitor {
    fn visit_item(&mut self, item: &'ast Item) {
        if let ItemKind::Static(box StaticItem {
            expr: Some(expr), ..
        }) = &item.kind
        {
            if let LikelyLit::Lit(lit) = LikelyLit::from_expr(expr) {
                self.static_span_to_lit.insert(expr.span, lit);
            }
        }
        visit::walk_item(self, item);
    }
}

fn remove_cast(expr: &Expr) -> &Expr {
    let ExprKind::Cast(expr, _) = &expr.kind else { return expr };
    remove_cast(expr)
}

#[derive(Debug, Clone, Copy)]
struct Pot<'a> {
    permissions: BitSet8<Permission>,
    #[allow(unused)]
    origins: BitSet8<Origin>,
    ty: &'a StreamType<'a>,
}

struct TypeArena<'a> {
    arena: &'a Arena<StreamType<'a>>,
}

impl<'a> TypeArena<'a> {
    #[inline]
    fn new(arena: &'a Arena<StreamType<'a>>) -> Self {
        Self { arena }
    }

    #[inline]
    fn buf_writer(&self, ty: &'a StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(StreamType::BufWriter(ty))
    }

    #[inline]
    fn buf_reader(&self, ty: &'a StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(StreamType::BufReader(ty))
    }

    #[inline]
    fn option(&self, ty: &'a StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(StreamType::Option(ty))
    }

    #[inline]
    fn ptr(&self, ty: &'a StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(StreamType::Ptr(ty))
    }
}

impl<'a> TypeArena<'a> {
    fn alloc(&self, ty: StreamType<'a>) -> &'a StreamType<'a> {
        self.arena.alloc(ty)
    }

    fn make_ty(
        &self,
        permissions: BitSet8<Permission>,
        origins: BitSet8<Origin>,
        is_param: bool,
    ) -> &'a StreamType<'a> {
        if is_param {
            let mut traits = BitSet8::new_empty();
            for p in permissions.iter() {
                traits.insert(some_or!(StreamTrait::from_permission(p), continue));
            }
            let ty = self.alloc(StreamType::Impl(TraitBound(traits)));
            self.option(ty)
        } else if origins.is_empty() {
            self.option(&FILE_TY)
        } else if origins.count() == 1 {
            let origin = origins.iter().next().unwrap();
            let ty = match origin {
                Origin::Stdin => &STDIN_TY,
                Origin::Stdout => &STDOUT_TY,
                Origin::Stderr => &STDERR_TY,
                Origin::File => {
                    if permissions.contains(Permission::Read)
                        && permissions.contains(Permission::Write)
                    {
                        &FILE_TY
                    } else if permissions.contains(Permission::Write) {
                        self.buf_writer(&FILE_TY)
                    } else if permissions.contains(Permission::Read)
                        || permissions.contains(Permission::BufRead)
                    {
                        self.buf_reader(&FILE_TY)
                    } else {
                        &FILE_TY
                    }
                }
                Origin::PipeRead => &CHILD_STDOUT_TY,
                Origin::PipeWrite => &CHILD_STDIN_TY,
                Origin::PipeDyn => todo!(),
                Origin::Buffer => todo!(),
            };
            if permissions.contains(Permission::Close) {
                self.option(ty)
            } else {
                self.ptr(ty)
            }
        } else {
            let mut traits = BitSet8::new_empty();
            for p in permissions.iter() {
                traits.insert(some_or!(StreamTrait::from_permission(p), continue));
            }
            let ty = self.alloc(StreamType::BoxDyn(TraitBound(traits)));
            self.option(ty)
        }
    }
}

#[allow(unused_tuple_struct_fields)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StreamType<'a> {
    File,
    Stdin,
    Stdout,
    Stderr,
    ChildStdin,
    ChildStdout,
    Option(&'a StreamType<'a>),
    BufWriter(&'a StreamType<'a>),
    BufReader(&'a StreamType<'a>),
    Ptr(&'a StreamType<'a>),
    Ref(&'a StreamType<'a>),
    BoxDyn(TraitBound),
    Impl(TraitBound),
}

static STDIN_TY: StreamType<'static> = StreamType::Stdin;
static STDOUT_TY: StreamType<'static> = StreamType::Stdout;
static STDERR_TY: StreamType<'static> = StreamType::Stderr;
static FILE_TY: StreamType<'static> = StreamType::File;
static CHILD_STDIN_TY: StreamType<'static> = StreamType::ChildStdin;
static CHILD_STDOUT_TY: StreamType<'static> = StreamType::ChildStdout;

impl std::fmt::Display for StreamType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::File => write!(f, "std::fs::File"),
            Self::Stdin => write!(f, "std::io::Stdin"),
            Self::Stdout => write!(f, "std::io::Stdout"),
            Self::Stderr => write!(f, "std::io::Stderr"),
            Self::ChildStdin => write!(f, "std::process::ChildStdin"),
            Self::ChildStdout => write!(f, "std::process::ChildStdout"),
            Self::Option(t) => write!(f, "Option<{}>", t),
            Self::BufWriter(t) => write!(f, "std::io::BufWriter<{}>", t),
            Self::BufReader(t) => write!(f, "std::io::BufReader<{}>", t),
            Self::Ptr(t) => write!(f, "*mut {}", t),
            Self::Ref(t) => write!(f, "&mut {}", t),
            Self::BoxDyn(traits) => write!(f, "Box<dyn {}>", traits),
            Self::Impl(traits) => write!(f, "impl {}", traits),
        }
    }
}

fn convert_expr(to: StreamType<'_>, from: StreamType<'_>, expr: &str, consume: bool) -> String {
    tracing::info!("{} := {} // {}", to, from, consume);
    if to == from && (consume || from.is_copyable()) {
        return expr.to_string();
    }
    use StreamType::*;
    match (to, from) {
        (Option(to), Option(from)) => {
            if consume {
                let body = convert_expr(*to, *from, "x", true);
                format!("({}).map(|x| {})", expr, body)
            } else {
                let body = convert_expr(*to, Ref(from), "x", true);
                format!("({}).as_mut().map(|x| {})", expr, body)
            }
        }
        (Ptr(to), Option(from)) if to == from => {
            format!(
                "({}).as_mut().map_or(std::ptr::null_mut(), |r| r as *mut _)",
                expr
            )
        }
        (to, Option(from)) if to == *from => {
            if consume {
                format!("({}).unwrap()", expr)
            } else {
                format!("({}).as_mut().unwrap()", expr)
            }
        }
        (to, Option(from)) => {
            if consume {
                let unwrapped = format!("({}).unwrap()", expr);
                convert_expr(to, *from, &unwrapped, true)
            } else {
                let unwrapped = format!("({}).as_mut().unwrap()", expr);
                convert_expr(to, Ref(from), &unwrapped, true)
            }
        }
        (Option(to), from) => {
            let converted = convert_expr(*to, from, expr, consume);
            format!("Some({})", converted)
        }
        (Impl(traits), File | Stdout | Stderr | ChildStdin | ChildStdout) => {
            if consume {
                expr.to_string()
            } else if traits.deref() == &BitSet8::new([StreamTrait::AsRawFd]) {
                format!("std::os::fd::AsFd::as_fd(&({}))", expr)
            } else {
                format!("&mut ({})", expr)
            }
        }
        (
            Impl(traits),
            Ref(File) | Ref(Stdout) | Ref(Stderr) | Ref(ChildStdin) | Ref(ChildStdout),
        ) => {
            if traits.deref() == &BitSet8::new([StreamTrait::AsRawFd]) {
                format!("std::os::fd::AsFd::as_fd({})", expr)
            } else {
                expr.to_string()
            }
        }
        (Impl(traits), Stdin) => {
            if traits.contains(StreamTrait::BufRead) {
                format!("({}).lock()", expr)
            } else if consume {
                expr.to_string()
            } else if traits.deref() == &BitSet8::new([StreamTrait::AsRawFd]) {
                format!("std::os::fd::AsFd::as_fd(&({}))", expr)
            } else {
                format!("&mut ({})", expr)
            }
        }
        (Impl(traits), BufWriter(from) | BufReader(from)) => {
            if traits.deref() == &BitSet8::new([StreamTrait::AsRawFd]) {
                if consume {
                    let inner = format!("({}).into_inner().unwrap()", expr);
                    convert_expr(to, *from, &inner, true)
                } else {
                    let inner = format!("({}).get_mut()", expr);
                    convert_expr(to, Ref(from), &inner, true)
                }
            } else if consume {
                expr.to_string()
            } else {
                format!("&mut ({})", expr)
            }
        }
        (Impl(traits), Ref(BufWriter(from)) | Ref(BufReader(from))) => {
            if traits.deref() == &BitSet8::new([StreamTrait::AsRawFd]) {
                let inner = format!("({}).get_mut()", expr);
                convert_expr(to, Ref(from), &inner, true)
            } else {
                expr.to_string()
            }
        }
        (Impl(_), Ptr(from)) => {
            let r = format!("({}).as_mut()", expr);
            let from = Ref(from);
            convert_expr(to, Option(&from), &r, true)
        }
        (Impl(_), Ref(Impl(_))) => {
            if consume {
                expr.to_string()
            } else {
                format!("&mut *({})", expr)
            }
        }
        (Impl(_), Ref(BoxDyn(_))) => {
            if consume {
                expr.to_string()
            } else {
                format!("&mut *({})", expr)
            }
        }
        (
            BoxDyn(traits),
            File | Stdout | Stderr | ChildStdin | ChildStdout | BufWriter(_) | BufReader(_),
        ) => {
            assert!(consume);
            format!(
                "{{ let stream: Box<dyn {}> = Box::new({}); stream }}",
                traits, expr
            )
        }
        (BufWriter(to), from) if *to == from => {
            assert!(consume);
            format!("std::io::BufWriter::new({})", expr)
        }
        (BufReader(to), from) if *to == from => {
            assert!(consume);
            format!("std::io::BufReader::new({})", expr)
        }
        _ => panic!("{} := {} // {}", to, from, consume),
    }
}

impl StreamType<'_> {
    fn is_copyable(self) -> bool {
        match self {
            Self::File
            | Self::Stdin
            | Self::Stdout
            | Self::Stderr
            | Self::ChildStdin
            | Self::ChildStdout
            | Self::BufWriter(_)
            | Self::BufReader(_)
            | Self::BoxDyn(_)
            | Self::Impl(_) => false,
            Self::Ref(_) => false,
            Self::Ptr(_) => true,
            Self::Option(t) => t.is_copyable(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct IndicatorCheck<'a> {
    name: &'a str,
    eof: bool,
    error: bool,
}

impl IndicatorCheck<'_> {
    #[inline]
    fn has_check(&self) -> bool {
        self.eof || self.error
    }

    #[inline]
    fn error_handling(&self) -> String {
        match (self.eof, self.error) {
            (true, true) => {
                format!(
                    "if e.kind() == std::io::ErrorKind::UnexpectedEof {{
    {0}_eof = 1;
}} else {{
    {0}_error = 1;
}}",
                    self.name
                )
            }
            (true, false) => {
                format!(
                    "if e.kind() == std::io::ErrorKind::UnexpectedEof {{ {}_eof = 1; }}",
                    self.name,
                )
            }
            (false, true) => {
                format!(
                    "if e.kind() != std::io::ErrorKind::UnexpectedEof {{ {}_error = 1; }}",
                    self.name
                )
            }
            (false, false) => "".to_string(),
        }
    }

    #[inline]
    fn error_handling_no_eof(&self) -> String {
        if self.error {
            format!("{}_error = 1;", self.name)
        } else {
            "".to_string()
        }
    }

    #[inline]
    fn clear(&self) -> String {
        match (self.eof, self.error) {
            (true, true) => format!("{{ {0}_eof = 0; {0}_error = 0; }}", self.name),
            (true, false) => format!("{{ {}_eof = 0; }}", self.name),
            (false, true) => format!("{{ {}_error = 0; }}", self.name),
            (false, false) => "()".to_string(),
        }
    }
}

trait StreamExpr {
    fn expr(&self) -> String;
    fn ty(&self) -> StreamType<'_>;

    #[inline]
    fn borrow_for(&self, tr: StreamTrait) -> String {
        let to = StreamType::Impl(TraitBound::new([tr]));
        convert_expr(to, self.ty(), &self.expr(), false)
    }

    #[inline]
    fn opt_borrow_for(&self, tr: StreamTrait) -> String {
        let ty = StreamType::Impl(TraitBound::new([tr]));
        let to = StreamType::Option(&ty);
        convert_expr(to, self.ty(), &self.expr(), false)
    }
}

#[derive(Debug, Clone, Copy)]
struct TypedExpr<'a> {
    expr: &'a Expr,
    ty: &'a StreamType<'a>,
}

impl<'a> TypedExpr<'a> {
    #[inline]
    fn new(expr: &'a Expr, ty: &'a StreamType<'a>) -> Self {
        Self { expr, ty }
    }
}

impl StreamExpr for TypedExpr<'_> {
    #[inline]
    fn expr(&self) -> String {
        pprust::expr_to_string(self.expr)
    }

    #[inline]
    fn ty(&self) -> StreamType<'_> {
        *self.ty
    }
}

#[derive(Debug, Clone, Copy)]
enum StdStream {
    Stdin,
    Stdout,
    #[allow(unused)]
    Stderr,
}

#[derive(Debug, Clone, Copy)]
struct StdExpr(StdStream);

impl StdExpr {
    #[inline]
    fn stdin() -> Self {
        Self(StdStream::Stdin)
    }

    #[inline]
    fn stdout() -> Self {
        Self(StdStream::Stdout)
    }

    #[allow(unused)]
    #[inline]
    fn stderr() -> Self {
        Self(StdStream::Stderr)
    }
}

impl StreamExpr for StdExpr {
    #[inline]
    fn expr(&self) -> String {
        match self.0 {
            StdStream::Stdin => "std::io::stdin()".to_string(),
            StdStream::Stdout => "std::io::stdout()".to_string(),
            StdStream::Stderr => "std::io::stderr()".to_string(),
        }
    }

    #[inline]
    fn ty(&self) -> StreamType<'_> {
        match self.0 {
            StdStream::Stdin => STDIN_TY,
            StdStream::Stdout => STDOUT_TY,
            StdStream::Stderr => STDERR_TY,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
enum StreamTrait {
    Read = 0,
    BufRead = 1,
    Write = 2,
    Seek = 3,
    AsRawFd = 4,
}

impl std::fmt::Display for StreamTrait {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Read => write!(f, "std::io::Read"),
            Self::BufRead => write!(f, "std::io::BufRead"),
            Self::Write => write!(f, "std::io::Write"),
            Self::Seek => write!(f, "std::io::Seek"),
            Self::AsRawFd => write!(f, "std::os::fd::AsRawFd"),
        }
    }
}

impl StreamTrait {
    const NUM: usize = 5;

    fn from_permission(p: Permission) -> Option<Self> {
        match p {
            Permission::Read => Some(Self::Read),
            Permission::BufRead => Some(Self::BufRead),
            Permission::Write => Some(Self::Write),
            Permission::Seek => Some(Self::Seek),
            Permission::AsRawFd => Some(Self::AsRawFd),
            Permission::Lock | Permission::Close => None,
        }
    }
}

impl Idx for StreamTrait {
    #[inline]
    fn new(idx: usize) -> Self {
        if idx >= Self::NUM {
            panic!()
        }
        unsafe { std::mem::transmute(idx as u8) }
    }

    #[inline]
    fn index(self) -> usize {
        self as _
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct TraitBound(BitSet8<StreamTrait>);

impl std::fmt::Display for TraitBound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, t) in self.0.iter().enumerate() {
            if i != 0 {
                write!(f, " + ")?;
            }
            write!(f, "{}", t)?;
        }
        Ok(())
    }
}

impl Deref for TraitBound {
    type Target = BitSet8<StreamTrait>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for TraitBound {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl TraitBound {
    #[inline]
    fn new<I: IntoIterator<Item = StreamTrait>>(traits: I) -> Self {
        Self(BitSet8::new(traits))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Param {
    func: LocalDefId,
    index: usize,
}

impl Param {
    #[inline]
    fn new(func: LocalDefId, index: usize) -> Self {
        Self { func, index }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum HirLoc {
    Global(LocalDefId),
    Local(HirId),
    Field(LocalDefId, FieldIdx),
}

impl HirLoc {
    fn from_res(res: Res) -> Option<Self> {
        match res {
            Res::Local(hir_id) => Some(Self::Local(hir_id)),
            Res::Def(_, def_id) => {
                let def_id = def_id.as_local()?;
                Some(Self::Global(def_id))
            }
            _ => None,
        }
    }
}

#[derive(Debug, Default)]
struct HirCtx {
    /// location to binding occurrence span
    /// * global (var): body span
    /// * global (fn): sig span
    /// * local: pat span
    /// * field: field span
    loc_to_binding_span: FxHashMap<HirLoc, Span>,
    /// binding occurrence span to location
    binding_span_to_loc: FxHashMap<Span, HirLoc>,

    /// location to bound occurrence spans
    loc_to_bound_spans: FxHashMap<HirLoc, Vec<Span>>,
    /// bound occurrence span to location
    bound_span_to_loc: FxHashMap<Span, HirLoc>,

    /// for each assignment, lhs span to rhs span
    lhs_to_rhs: FxHashMap<Span, Span>,
    /// for each assignment, rhs span to lhs span
    rhs_to_lhs: FxHashMap<Span, Span>,

    /// function def_id to feof argument names
    feof_functions: FxHashMap<LocalDefId, FxHashSet<Symbol>>,
    /// function def_id to ferror argument names
    ferror_functions: FxHashMap<LocalDefId, FxHashSet<Symbol>>,
    /// call span to stream argument name
    callee_span_to_stream_name: FxHashMap<Span, Symbol>,

    /// callee span to expr hir_id
    callee_span_to_hir_id: FxHashMap<Span, HirId>,
}

struct HirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ctx: HirCtx,
}

impl HirVisitor<'_> {
    fn add_binding(&mut self, loc: HirLoc, span: Span) {
        self.ctx.loc_to_binding_span.insert(loc, span);
        self.ctx.binding_span_to_loc.insert(span, loc);
    }

    fn add_bound(&mut self, loc: HirLoc, span: Span) {
        self.ctx
            .loc_to_bound_spans
            .entry(loc)
            .or_default()
            .push(span);
        self.ctx.bound_span_to_loc.insert(span, loc);
    }

    fn add_assignment(&mut self, lhs: Span, rhs: Span) {
        self.ctx.lhs_to_rhs.insert(lhs, rhs);
        self.ctx.rhs_to_lhs.insert(rhs, lhs);
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for HirVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        intravisit::walk_item(self, item);

        match item.kind {
            hir::ItemKind::Static(_, _, body_id) => {
                let loc = HirLoc::Global(item.owner_id.def_id);
                let body = self.tcx.hir().body(body_id);
                self.add_binding(loc, body.value.span);
                self.add_bound(loc, body.value.span);
                self.add_assignment(body.value.span, body.value.span);
            }
            hir::ItemKind::Fn(sig, _, _) => {
                let loc = HirLoc::Global(item.owner_id.def_id);
                self.add_binding(loc, sig.span);
            }
            hir::ItemKind::Struct(vd, _) => {
                let hir::VariantData::Struct(fs, _) = vd else { return };
                let def_id = item.owner_id.def_id;
                for (i, f) in fs.iter().enumerate() {
                    let loc = HirLoc::Field(def_id, FieldIdx::from_usize(i));
                    self.add_binding(loc, f.span);
                }
            }
            _ => {}
        }
    }

    fn visit_local(&mut self, local: &'tcx hir::Local<'tcx>) {
        intravisit::walk_local(self, local);

        if let Some(init) = local.init {
            self.add_assignment(local.pat.span, init.span);
        }

        if let hir::PatKind::Binding(_, hir_id, _, _) = local.pat.kind {
            let loc = HirLoc::Local(hir_id);
            let span = local.pat.span;
            self.add_bound(loc, span);
        }
    }

    fn visit_pat(&mut self, pat: &'tcx hir::Pat<'tcx>) {
        intravisit::walk_pat(self, pat);

        let hir::PatKind::Binding(_, hir_id, _, _) = pat.kind else { return };
        let loc = HirLoc::Local(hir_id);
        self.add_binding(loc, pat.span);
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        intravisit::walk_expr(self, expr);

        match expr.kind {
            hir::ExprKind::Field(e, field) => {
                let (adt_def, def_id) = some_or!(adt_of_expr(e, self.tcx), return);
                let i = some_or!(find_field(field.name, adt_def), return);
                let loc = HirLoc::Field(def_id, i);
                self.add_bound(loc, expr.span);
            }
            hir::ExprKind::Assign(lhs, rhs, _) => {
                self.add_assignment(lhs.span, rhs.span);
            }
            hir::ExprKind::Struct(_, fields, _) => {
                let (adt_def, def_id) = some_or!(adt_of_expr(expr, self.tcx), return);
                for field in fields {
                    let i = some_or!(find_field(field.ident.name, adt_def), continue);
                    let loc = HirLoc::Field(def_id, i);
                    self.add_bound(loc, field.ident.span);
                    self.add_assignment(field.ident.span, field.expr.span);
                }
            }
            hir::ExprKind::Call(callee, args) => {
                let hir::ExprKind::Path(QPath::Resolved(_, path)) = callee.kind else { return };
                self.ctx
                    .callee_span_to_hir_id
                    .insert(path.span, expr.hir_id);
                let name = path.segments.last().unwrap().ident.name;
                let name = api_list::normalize_api_name(name.as_str());
                let i = match name {
                    "fscanf" | "fgetc" | "getc" | "fprintf" | "fflush" | "feof" | "ferror"
                    | "clearerr" => 0,
                    "fputc" | "putc" | "fputs" => 1,
                    "fgets" => 2,
                    "fread" | "fwrite" => 3,
                    _ => return,
                };
                let arg_name = match &args[i].kind {
                    hir::ExprKind::Path(QPath::Resolved(_, path)) => {
                        path.segments.last().unwrap().ident.name
                    }
                    hir::ExprKind::Field(_, field) => field.name,
                    _ => return,
                };
                self.ctx
                    .callee_span_to_stream_name
                    .insert(path.span, arg_name);
                let funcs = match name {
                    "feof" => &mut self.ctx.feof_functions,
                    "ferror" => &mut self.ctx.ferror_functions,
                    _ => return,
                };
                let curr_func = expr.hir_id.owner.def_id;
                funcs.entry(curr_func).or_default().insert(arg_name);
            }
            _ => {}
        }
    }

    fn visit_path(&mut self, path: &hir::Path<'tcx>, _: HirId) {
        intravisit::walk_path(self, path);

        if let Some(loc) = HirLoc::from_res(path.res) {
            self.add_bound(loc, path.span);
        }
    }
}

#[inline]
fn adt_of_expr<'tcx>(
    expr: &hir::Expr<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<(AdtDef<'tcx>, LocalDefId)> {
    let typeck = tcx.typeck(expr.hir_id.owner.def_id);
    let ty = typeck.expr_ty(expr);
    let ty::TyKind::Adt(adt_def, _) = ty.kind() else { return None };
    Some((*adt_def, adt_def.did().as_local()?))
}

#[inline]
fn find_field(field: Symbol, adt_def: AdtDef<'_>) -> Option<FieldIdx> {
    adt_def
        .variant(VariantIdx::from_u32(0))
        .fields
        .iter_enumerated()
        .find_map(|(i, f)| if f.name == field { Some(i) } else { None })
}

struct MirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    nulls: FxHashSet<Location>,
}

impl<'tcx> mir::visit::Visitor<'tcx> for MirVisitor<'tcx> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        if let Rvalue::Cast(
            CastKind::PointerFromExposedAddress,
            Operand::Constant(box Constant {
                literal: ConstantKind::Val(ConstValue::Scalar(Scalar::Int(i)), _),
                ..
            }),
            ty,
        ) = rvalue
        {
            if i.try_to_u64() == Ok(0) && compile_util::contains_file_ty(*ty, self.tcx) {
                self.nulls.insert(location);
            }
        }
        self.super_rvalue(rvalue, location);
    }
}

struct TransformVisitor<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    hir: &'a HirCtx,
    /// function parameter to HIR location
    param_to_loc: &'a FxHashMap<Param, HirLoc>,
    /// HIR location to permissions and origins
    loc_to_pot: &'a FxHashMap<HirLoc, Pot<'a>>,
    /// static variable definition's span to its literal
    static_span_to_lit: &'a FxHashMap<Span, Symbol>,
    /// user-defined API functions' signatures' spans
    api_sig_spans: &'a FxHashSet<Span>,
    /// null to file pointer cast expr spans
    null_casts: &'a FxHashSet<Span>,
    /// unsupported expr spans
    unsupported: &'a FxHashSet<Span>,
    /// is stdin unsupported
    is_stdin_unsupported: bool,

    /// is this file updated
    updated: bool,
    updated_field_spans: FxHashSet<Span>,
    tmpfile: bool,
}

impl<'a> TransformVisitor<'_, 'a> {
    #[inline]
    fn is_unsupported(&self, expr: &Expr) -> bool {
        self.unsupported.contains(&expr.span) || self.unsupported.contains(&remove_cast(expr).span)
    }

    #[inline]
    fn transform_fprintf<S: StreamExpr, E: Deref<Target = Expr>>(
        &self,
        stream: &S,
        fmt: &Expr,
        args: &[E],
        wide: bool,
        ic: IndicatorCheck<'_>,
    ) -> Expr {
        match LikelyLit::from_expr(fmt) {
            LikelyLit::Lit(fmt) => transform_fprintf_lit(stream, fmt, args, wide, ic),
            LikelyLit::If(_, _, _) => todo!(),
            LikelyLit::Path(_, span) => {
                let loc = self.hir.bound_span_to_loc[&span];
                let static_span = self.hir.loc_to_binding_span[&loc];
                let fmt = self.static_span_to_lit[&static_span];
                transform_fprintf_lit(stream, fmt, args, wide, ic)
            }
            LikelyLit::Other(e) => todo!("{:?}", e),
        }
    }

    #[inline]
    fn param_pot(&self, param: Param) -> Option<&'a Pot<'a>> {
        let loc = self.param_to_loc.get(&param)?;
        self.loc_to_pot.get(loc)
    }

    #[inline]
    fn bound_pot(&self, span: Span) -> Option<&'a Pot<'a>> {
        let loc = self.hir.bound_span_to_loc.get(&span)?;
        self.loc_to_pot.get(loc)
    }

    #[inline]
    fn binding_ty(&self, span: Span) -> Option<Ty> {
        let loc = self.hir.binding_span_to_loc.get(&span)?;
        let pot = self.loc_to_pot.get(loc)?;
        Some(ty!("{}", pot.ty))
    }

    #[inline]
    fn indicator_check(&self, span: Span) -> IndicatorCheck<'_> {
        let curr_func = self.hir.callee_span_to_hir_id[&span].owner.def_id;
        let name = self.hir.callee_span_to_stream_name.get(&span).unwrap();
        let eof = self
            .hir
            .feof_functions
            .get(&curr_func)
            .map_or(false, |s| s.contains(name));
        let error = self
            .hir
            .ferror_functions
            .get(&curr_func)
            .map_or(false, |s| s.contains(name));
        IndicatorCheck {
            name: name.as_str(),
            eof,
            error,
        }
    }

    #[inline]
    fn indicator_check_std<'s>(&self, span: Span, name: &'s str) -> IndicatorCheck<'s> {
        let curr_func = self.hir.callee_span_to_hir_id[&span].owner.def_id;
        let eof = self
            .hir
            .feof_functions
            .get(&curr_func)
            .map_or(false, |s| s.iter().any(|n| n.as_str() == name));
        let error = self
            .hir
            .ferror_functions
            .get(&curr_func)
            .map_or(false, |s| s.iter().any(|n| n.as_str() == name));
        IndicatorCheck { name, eof, error }
    }

    #[inline]
    fn replace_expr(&mut self, old: &mut Expr, new: Expr) {
        self.updated = true;
        let span = old.span;
        *old = new;
        old.span = span;
    }

    #[inline]
    fn replace_ty(&mut self, old: &mut Ty, new: Ty) {
        self.updated = true;
        let span = old.span;
        *old = new;
        old.span = span;
    }

    #[inline]
    fn replace_ident(&mut self, old: &mut Ident, new: Ident) {
        self.updated = true;
        let span = old.span;
        *old = new;
        old.span = span;
    }
}

impl MutVisitor for TransformVisitor<'_, '_> {
    fn visit_item_kind(&mut self, item: &mut ItemKind) {
        if let ItemKind::Fn(f) = item {
            if self.api_sig_spans.contains(&f.sig.span) {
                return;
            }
        }

        mut_visit::noop_visit_item_kind(item, self);

        match item {
            ItemKind::Static(box item) => {
                let body = some_or!(&item.expr, return);
                let loc = self.hir.binding_span_to_loc[&body.span];
                let pot = some_or!(self.loc_to_pot.get(&loc), return);
                self.replace_ty(&mut item.ty, ty!("{}", pot.ty));
            }
            ItemKind::Fn(box item) => {
                let HirLoc::Global(def_id) = self.hir.binding_span_to_loc[&item.sig.span] else {
                    panic!()
                };
                let mut tparams = vec![];
                for (i, param) in item.sig.decl.inputs.iter_mut().enumerate() {
                    if self.unsupported.contains(&param.pat.span) {
                        continue;
                    }
                    let p = Param::new(def_id, i);
                    let pot = some_or!(self.param_pot(p), continue);
                    self.replace_ty(&mut param.ty, ty!("Option<TT{}>", i));
                    if let PatKind::Ident(BindingAnnotation(_, m), _, _) = &mut param.pat.kind {
                        *m = Mutability::Mut;
                    }
                    tparams.push((i, pot));
                }
                for (i, po) in tparams {
                    let StreamType::Option(StreamType::Impl(bound)) = po.ty else { panic!() };
                    let tparam = if bound.is_empty() {
                        ty_param!("TT{}", i)
                    } else {
                        ty_param!("TT{}: {}", i, bound)
                    };
                    item.generics.params.push(tparam);
                }
                if let Some(eofs) = self.hir.feof_functions.get(&def_id) {
                    let stmts = &mut item.body.as_mut().unwrap().stmts;
                    for eof in eofs {
                        let stmt = stmt!("let mut {}_eof = 0;", eof);
                        stmts.insert(0, stmt);
                    }
                }
                if let Some(errors) = self.hir.ferror_functions.get(&def_id) {
                    let stmts = &mut item.body.as_mut().unwrap().stmts;
                    for error in errors {
                        let stmt = stmt!("let mut {}_error = 0;", error);
                        stmts.insert(0, stmt);
                    }
                }
            }
            _ => {}
        }
    }

    fn visit_variant_data(&mut self, vdata: &mut VariantData) {
        mut_visit::noop_visit_variant_data(vdata, self);

        let VariantData::Struct(fields, _) = vdata else { return };
        for f in fields {
            if let Some(ty) = self.binding_ty(f.span) {
                self.updated_field_spans.insert(f.span);
                self.replace_ty(&mut f.ty, ty);
            }
        }
    }

    fn visit_local(&mut self, local: &mut P<Local>) {
        mut_visit::noop_visit_local(local, self);

        if self.unsupported.contains(&local.pat.span) {
            return;
        }

        if let Some(ty) = self.binding_ty(local.pat.span) {
            self.replace_ty(local.ty.as_mut().unwrap(), ty);
        }
    }

    fn visit_expr(&mut self, expr: &mut P<Expr>) {
        mut_visit::noop_visit_expr(expr, self);
        let expr_span = expr.span;
        if self.is_unsupported(expr) {
            return;
        }
        match &mut expr.kind {
            ExprKind::Call(callee, args) => {
                let Some(HirLoc::Global(def_id)) = self.hir.bound_span_to_loc.get(&callee.span)
                else {
                    return;
                };
                let name = compile_util::def_id_to_value_symbol(*def_id, self.tcx).unwrap();
                let name = api_list::normalize_api_name(name.as_str());
                match name {
                    "fopen" => {
                        let lhs = self.hir.rhs_to_lhs[&expr_span];
                        let pot = self.bound_pot(lhs).unwrap();
                        let new_expr = transform_fopen(&args[0], &args[1], pot);
                        self.replace_expr(expr, new_expr);
                    }
                    "tmpfile" => {
                        let lhs = self.hir.rhs_to_lhs[&expr_span];
                        let pot = self.bound_pot(lhs).unwrap();
                        let new_expr = transform_tmpfile(pot);
                        self.replace_expr(expr, new_expr);
                        self.tmpfile = true;
                    }
                    "popen" => {
                        let lhs = self.hir.rhs_to_lhs[&expr_span];
                        let pot = self.bound_pot(lhs).unwrap();
                        let new_expr = transform_popen(&args[0], &args[1], pot);
                        self.replace_expr(expr, new_expr);
                    }
                    "fclose" | "pclose" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let loc = self.hir.bound_span_to_loc[&args[0].span];
                        let is_static = matches!(loc, HirLoc::Global(_));
                        let new_expr = transform_fclose(&args[0], is_static);
                        self.replace_expr(expr, new_expr);
                    }
                    "fscanf" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let ic = self.indicator_check(callee.span);
                        let new_expr = transform_fscanf(&stream, &args[1], &args[2..], ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "fgetc" | "getc" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let ic = self.indicator_check(callee.span);
                        let new_expr = transform_fgetc(&stream, ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "getchar" => {
                        if self.is_stdin_unsupported {
                            return;
                        }
                        let stream = StdExpr::stdin();
                        let ic = self.indicator_check_std(callee.span, "stdin");
                        let new_expr = transform_fgetc(&stream, ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "fgets" => {
                        if self.is_unsupported(&args[2]) {
                            return;
                        }
                        let ty = self.bound_pot(args[2].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[2], ty);
                        let ic = self.indicator_check(callee.span);
                        let new_expr = transform_fgets(&stream, &args[0], &args[1], ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "fread" => {
                        if self.is_unsupported(&args[3]) {
                            return;
                        }
                        let ty = self.bound_pot(args[3].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[3], ty);
                        let ic = self.indicator_check(callee.span);
                        let new_expr = transform_fread(&stream, &args[0], &args[1], &args[2], ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "getdelim" => todo!(),
                    "getline" => todo!(),
                    "feof" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let name = self.hir.callee_span_to_stream_name[&callee.span];
                        let new_expr = expr!("{}_eof", name);
                        self.replace_expr(expr, new_expr);
                    }
                    "ferror" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let name = self.hir.callee_span_to_stream_name[&callee.span];
                        let new_expr = expr!("{}_error", name);
                        self.replace_expr(expr, new_expr);
                    }
                    "clearerr" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ic = self.indicator_check(callee.span);
                        let new_expr = expr!("{}", ic.clear());
                        self.replace_expr(expr, new_expr);
                    }
                    "fprintf" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let ic = self.indicator_check(callee.span);
                        let new_expr =
                            self.transform_fprintf(&stream, &args[1], &args[2..], false, ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "printf" => {
                        let stream = StdExpr::stdout();
                        let ic = self.indicator_check_std(callee.span, "stdout");
                        let new_expr =
                            self.transform_fprintf(&stream, &args[0], &args[1..], false, ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "wprintf" => {
                        let stream = StdExpr::stdout();
                        let ic = self.indicator_check_std(callee.span, "stdout");
                        let new_expr =
                            self.transform_fprintf(&stream, &args[0], &args[1..], true, ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "fputc" | "putc" => {
                        if self.is_unsupported(&args[1]) {
                            return;
                        }
                        let ty = self.bound_pot(args[1].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[1], ty);
                        let ic = self.indicator_check(callee.span);
                        let new_expr = transform_fputc(&stream, &args[0], ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "putchar" => {
                        let stream = StdExpr::stdout();
                        let ic = self.indicator_check_std(callee.span, "stdout");
                        let new_expr = transform_fputc(&stream, &args[0], ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "fputs" => {
                        if self.is_unsupported(&args[1]) {
                            return;
                        }
                        let ty = self.bound_pot(args[1].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[1], ty);
                        let ic = self.indicator_check(callee.span);
                        let new_expr = transform_fputs(&stream, &args[0], ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "puts" => {
                        let ic = self.indicator_check_std(callee.span, "stdout");
                        let new_expr = transform_puts(&args[0], ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "fwrite" => {
                        if self.is_unsupported(&args[3]) {
                            return;
                        }
                        let ty = self.bound_pot(args[3].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[3], ty);
                        let ic = self.indicator_check(callee.span);
                        let new_expr = transform_fwrite(&stream, &args[0], &args[1], &args[2], ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "fflush" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let ic = self.indicator_check(callee.span);
                        let new_expr = transform_fflush(&stream, ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "fseek" | "fseeko" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let new_expr = transform_fseek(&stream, &args[1], &args[2]);
                        self.replace_expr(expr, new_expr);
                    }
                    "ftell" | "ftello" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let new_expr = transform_ftell(&stream);
                        self.replace_expr(expr, new_expr);
                    }
                    "rewind" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let new_expr = transform_rewind(&stream);
                        self.replace_expr(expr, new_expr);
                    }
                    "fgetpos" => todo!(),
                    "fsetpos" => todo!(),
                    "fileno" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let new_expr = transform_fileno(&stream);
                        self.replace_expr(expr, new_expr);
                    }
                    _ => {
                        let hir::Node::Item(item) = self.tcx.hir().get_by_def_id(*def_id) else {
                            return;
                        };
                        let hir::ItemKind::Fn(sig, _, _) = item.kind else { panic!() };
                        let mut targs = vec![];
                        for (i, arg) in args[..sig.decl.inputs.len()].iter_mut().enumerate() {
                            if self.is_unsupported(arg) {
                                continue;
                            }
                            let p = Param::new(*def_id, i);
                            let param_pot = some_or!(self.param_pot(p), continue);
                            let permissions = param_pot.permissions;
                            assert!(!permissions.contains(Permission::Close));
                            if self.null_casts.contains(&arg.span) {
                                self.replace_expr(arg, expr!("None"));
                                let targ = if permissions.contains(Permission::BufRead) {
                                    "std::io::BufReader<std::fs::File>"
                                } else {
                                    "std::fs::File"
                                };
                                targs.push(targ);
                            } else {
                                let arg_pot = self.bound_pot(arg.span).unwrap();
                                let permission = permissions
                                    .iter()
                                    .find(|p| !matches!(p, Permission::Lock | Permission::Close))
                                    .unwrap();
                                let stream = TypedExpr::new(arg, arg_pot.ty);
                                let tr = StreamTrait::from_permission(permission).unwrap();
                                let new_arg = stream.opt_borrow_for(tr);
                                self.replace_expr(arg, expr!("{}", new_arg));
                                targs.push("_");
                            }
                        }
                        if targs.iter().any(|targ| *targ != "_") {
                            let c = pprust::expr_to_string(callee);
                            let new_expr = expr!("{}::<{}>", c, targs.join(", "));
                            self.replace_expr(callee, new_expr);
                        }
                    }
                }
            }
            ExprKind::Path(None, path) => {
                if let [seg] = &path.segments[..] {
                    match seg.ident.name.as_str() {
                        "stdin" => {
                            let new_expr = expr!("std::io::stdin()");
                            self.replace_expr(expr, new_expr);
                        }
                        "stdout" => {
                            let new_expr = expr!("std::io::stdout()");
                            self.replace_expr(expr, new_expr);
                        }
                        "stderr" => {
                            let new_expr = expr!("std::io::stderr()");
                            self.replace_expr(expr, new_expr);
                        }
                        _ => {}
                    }
                }
            }
            ExprKind::MethodCall(box MethodCall { receiver, seg, .. }) => {
                if self.is_unsupported(receiver) {
                    return;
                }
                let ty = some_or!(self.bound_pot(receiver.span), return).ty;
                match ty {
                    StreamType::Option(_) => {
                        self.replace_ident(&mut seg.ident, Ident::from_str("is_none"));
                    }
                    StreamType::Ptr(_) => {}
                    _ => panic!(),
                }
            }
            ExprKind::Cast(_, _) => {
                let lhs = some_or!(self.hir.rhs_to_lhs.get(&expr_span), return);
                if self.unsupported.contains(lhs) {
                    return;
                }
                let pot = some_or!(self.bound_pot(*lhs), return);
                match pot.ty {
                    StreamType::Option(_) => {
                        self.replace_expr(expr, expr!("None"));
                    }
                    StreamType::Ptr(_) => {
                        self.replace_expr(expr, expr!("std::ptr::null_mut()"));
                    }
                    _ => panic!(),
                }
            }
            ExprKind::Assign(lhs, rhs, _) => {
                let lhs_pot = some_or!(self.bound_pot(lhs.span), return);
                let rhs_pot = some_or!(self.bound_pot(rhs.span), return);
                let rhs_str = pprust::expr_to_string(rhs);
                let new_rhs = convert_expr(*lhs_pot.ty, *rhs_pot.ty, &rhs_str, false);
                let new_rhs = expr!("{}", new_rhs);
                self.replace_expr(rhs, new_rhs);
            }
            ExprKind::Struct(se) => {
                for f in se.fields.iter_mut() {
                    let lhs_pot = some_or!(self.bound_pot(f.ident.span), return);
                    let rhs_pot = some_or!(self.bound_pot(f.expr.span), return);
                    let rhs_str = pprust::expr_to_string(&f.expr);
                    let new_rhs = convert_expr(*lhs_pot.ty, *rhs_pot.ty, &rhs_str, false);
                    let new_rhs = expr!("{}", new_rhs);
                    self.replace_expr(&mut f.expr, new_rhs);
                }
            }
            _ => {}
        }
    }
}

fn transform_fopen(path: &Expr, mode: &Expr, pot: &Pot<'_>) -> Expr {
    let path = pprust::expr_to_string(path);
    let mode = LikelyLit::from_expr(mode);
    let expr = match mode {
        LikelyLit::Lit(mode) => {
            let path = format!(
                "std::ffi::CStr::from_ptr(({}) as _).to_str().unwrap()",
                path
            );
            let (prefix, suffix) = mode.as_str().split_at(1);
            let plus = suffix.contains('+');
            match prefix {
                "r" => {
                    if plus {
                        format!(
                            "std::fs::OpenOptions::new()
                                .read(true)
                                .write(true)
                                .open({})
                                .ok()",
                            path,
                        )
                    } else {
                        format!("std::fs::File::open({}).ok()", path)
                    }
                }
                "w" => {
                    if plus {
                        format!(
                            "std::fs::OpenOptions::new()
                                .write(true)
                                .create(true)
                                .truncate(true)
                                .read(true)
                                .open({})
                                .ok()",
                            path,
                        )
                    } else {
                        format!("std::fs::File::create({}).ok()", path)
                    }
                }
                "a" => {
                    if plus {
                        format!(
                            "std::fs::OpenOptions::new()
                                .append(true)
                                .create(true)
                                .read(true)
                                .open({})
                                .ok()",
                            path,
                        )
                    } else {
                        format!(
                            "std::fs::OpenOptions::new()
                                .append(true)
                                .create(true)
                                .open({})
                                .ok()",
                            path,
                        )
                    }
                }
                _ => panic!("{:?}", mode),
            }
        }
        LikelyLit::If(_, _, _) => todo!(),
        LikelyLit::Path(symbol, _) => {
            format!(
                r#"{{
    let pathname = std::ffi::CStr::from_ptr(({}) as _).to_str().unwrap();
    let mode = std::ffi::CStr::from_ptr(({}) as _).to_str().unwrap();
    let (prefix, suffix) = mode.split_at(1);
    match prefix {{
        "r" => {{
            if suffix.contains('+') {{
                std::fs::OpenOptions::new().read(true).write(true).open(pathname)
            }} else {{
                std::fs::File::open(pathname)
            }}
        }}
        "w" => {{
            if suffix.contains('+') {{
                std::fs::OpenOptions::new()
                    .write(true)
                    .create(true)
                    .truncate(true)
                    .read(true)
                    .open(pathname)
            }} else {{
                std::fs::File::create(pathname)
            }}
        }}
        "a" => {{
            if suffix.contains('+') {{
                std::fs::OpenOptions::new()
                    .append(true)
                    .create(true)
                    .read(true)
                    .open(pathname)
            }} else {{
                std::fs::OpenOptions::new().append(true).create(true).open(pathname)
            }}
        }}
        _ => panic!(),
    }}.ok()
}}"#,
                path,
                symbol.as_str()
            )
        }
        LikelyLit::Other(_) => todo!(),
    };
    let new_expr = convert_expr(*pot.ty, StreamType::Option(&FILE_TY), &expr, true);
    expr!("{}", new_expr)
}

fn transform_tmpfile(pot: &Pot<'_>) -> Expr {
    let expr = "tempfile::tempfile().ok()";
    let ty = StreamType::Option(&FILE_TY);
    let new_expr = convert_expr(*pot.ty, ty, expr, true);
    expr!("{}", new_expr)
}

fn transform_popen(command: &Expr, mode: &Expr, pot: &Pot<'_>) -> Expr {
    let command = pprust::expr_to_string(command);
    let command = format!(
        "std::ffi::CStr::from_ptr(({}) as _).to_str().unwrap()",
        command
    );
    let mode = LikelyLit::from_expr(mode);
    let (expr, ty) = match mode {
        LikelyLit::Lit(mode) => {
            let (field, ty) = match &mode.as_str()[..1] {
                "r" => ("stdout", &CHILD_STDOUT_TY),
                "w" => ("stdin", &CHILD_STDIN_TY),
                _ => panic!("{:?}", mode),
            };
            let expr = format!(
                r#"std::process::Command::new("sh")
                .arg("-c")
                .arg("--")
                .arg({})
                .{1}(std::process::Stdio::piped())
                .spawn()
                .ok()
                .and_then(|child| child.{1})"#,
                command, field
            );
            (expr, StreamType::Option(ty))
        }
        LikelyLit::If(_, _, _) => todo!(),
        LikelyLit::Path(_, _) => todo!(),
        LikelyLit::Other(_) => todo!(),
    };
    let new_expr = convert_expr(*pot.ty, ty, &expr, true);
    expr!("{}", new_expr)
}

fn transform_fclose(stream: &Expr, is_static: bool) -> Expr {
    let stream = pprust::expr_to_string(stream);
    let take = if is_static { ".take()" } else { "" };
    expr!("{{ drop(({}){}); 0 }}", stream, take)
}

fn transform_fscanf<S: StreamExpr, E: Deref<Target = Expr>>(
    stream: &S,
    fmt: &Expr,
    args: &[E],
    ic: IndicatorCheck<'_>,
) -> Expr {
    assert!(!ic.has_check());
    let stream = stream.borrow_for(StreamTrait::BufRead);
    let fmt = LikelyLit::from_expr(fmt);
    match fmt {
        LikelyLit::Lit(fmt) => {
            let fmt = fmt.to_string().into_bytes();
            let specs = scanf::parse_specs(&fmt);
            let mut i = 0;
            let mut code = String::new();
            for spec in specs {
                let arg = if spec.assign {
                    i += 1;
                    Some(pprust::expr_to_string(&args[i - 1]))
                } else {
                    None
                };
                let check_width = if let Some(width) = spec.width {
                    format!("if chars.len() == {} {{ break; }}", width)
                } else {
                    "".to_string()
                };
                if let Some(_scan_set) = spec.scan_set() {
                    todo!();
                } else {
                    let assign = if let Some(arg) = arg {
                        let ty = spec.ty();
                        if ty == "&str" {
                            format!(
                                "
    let bytes = s.as_bytes();
    let buf: &mut [u8] = std::slice::from_raw_parts_mut(({}) as _, bytes.len() + 1);
    buf.copy_from_slice(bytes);
    buf[bytes.len()] = 0;",
                                arg
                            )
                        } else {
                            format!(
                                "
    *(({}) as *mut {}) = s.parse().unwrap();
    count += 1;",
                                arg, ty
                            )
                        }
                    } else {
                        "".to_string()
                    };
                    write!(
                        code,
                        "{{
    let mut chars = vec![];
    loop {{
        {}
        let available = match stream.fill_buf() {{
            Ok(buf) => buf,
            Err(_) => break,
        }};
        if available.is_empty() {{
            break;
        }}
        let c = available[0];
        if !c.is_ascii_whitespace() {{
            chars.push(c);
        }} else if !chars.is_empty() {{
            break;
        }}
        stream.consume(1);
    }}
    let s = String::from_utf8(chars).unwrap();
    {}
}}",
                        check_width, assign
                    )
                    .unwrap();
                }
            }
            expr!(
                "{{
    use std::io::BufRead;
    let mut stream = {};
    let mut count = 0i32;
    {}
    count
}}",
                stream,
                code
            )
        }
        LikelyLit::If(_, _, _) => todo!(),
        LikelyLit::Path(_, _) => todo!(),
        LikelyLit::Other(_) => todo!(),
    }
}

#[inline]
fn transform_fgetc<S: StreamExpr>(stream: &S, ic: IndicatorCheck<'_>) -> Expr {
    let stream_str = stream.borrow_for(StreamTrait::Read);
    if ic.has_check() {
        expr!(
            "{{
    use std::io::Read;
    let mut ___buf = [0];
    match ({}).read_exact(&mut ___buf) {{
        Ok(_) => ___buf[0] as _,
        Err(e) => {{
            {}
            libc::EOF
        }}
    }}
}}",
            stream_str,
            ic.error_handling(),
        )
    } else {
        expr!(
            "{{
    use std::io::Read;
    let mut ___buf = [0];
    ({}).read_exact(&mut ___buf).map_or(libc::EOF, |_| ___buf[0] as _)
}}",
            stream_str
        )
    }
}

#[inline]
fn transform_fgets<S: StreamExpr>(stream: &S, s: &Expr, n: &Expr, ic: IndicatorCheck<'_>) -> Expr {
    let stream_str = stream.borrow_for(StreamTrait::BufRead);
    let s = pprust::expr_to_string(s);
    let n = pprust::expr_to_string(n);
    let handling = ic.error_handling();
    expr!(
        "{{
    use std::io::BufRead;
    let mut stream = {};
    let s = {};
    let n = ({}) as usize;
    let ___buf: &mut [u8] = std::slice::from_raw_parts_mut(s as _, n);
    let mut pos = 0;
    while pos < n - 1 {{
        let available = match stream.fill_buf() {{
            Ok(___buf) => ___buf,
            Err(e) => {{
                {}
                pos = 0;
                break
            }}
        }};
        if available.is_empty() {{
            break;
        }}
        ___buf[pos] = available[0];
        stream.consume(1);
        pos += 1;
        if ___buf[pos - 1] == b'\\n' {{
            break;
        }}
    }}
    if pos == 0 {{
        std::ptr::null_mut()
    }} else {{
        ___buf[pos] = 0;
        s
    }}
}}",
        stream_str,
        s,
        n,
        handling
    )
}

#[inline]
fn transform_fread<S: StreamExpr>(
    stream: &S,
    ptr: &Expr,
    size: &Expr,
    nitems: &Expr,
    ic: IndicatorCheck<'_>,
) -> Expr {
    let stream_str = stream.borrow_for(StreamTrait::Read);
    let ptr = pprust::expr_to_string(ptr);
    let size = pprust::expr_to_string(size);
    let nitems = pprust::expr_to_string(nitems);
    let handling = ic.error_handling();
    expr!(
        "{{
    use std::io::Read;
    let mut stream = {};
    let size = {};
    let ptr: &mut [u8] = std::slice::from_raw_parts_mut(({}) as _, (size * ({})) as usize);
    let mut i = 0;
    for data in ptr.chunks_mut(size as usize) {{
        if let Err(e) = stream.read_exact(data) {{
            {}
            break;
        }}
        i += 1;
    }}
    i
}}",
        stream_str,
        size,
        ptr,
        nitems,
        handling
    )
}

fn transform_fprintf_lit<S: StreamExpr, E: Deref<Target = Expr>>(
    stream: &S,
    fmt: Symbol,
    args: &[E],
    wide: bool,
    ic: IndicatorCheck<'_>,
) -> Expr {
    assert!(!ic.has_check());
    // from rustc_ast/src/util/literal.rs
    let s = fmt.as_str();
    let mut buf = Vec::with_capacity(s.len());
    unescape::unescape_literal(fmt.as_str(), unescape::Mode::ByteStr, &mut |_, c| {
        buf.push(unescape::byte_from_char(c.unwrap()))
    });

    if wide {
        let mut new_buf: Vec<u8> = vec![];
        for c in buf.chunks_exact(4) {
            let c = u32::from_le_bytes(c.try_into().unwrap());
            new_buf.push(c.try_into().unwrap());
        }
        buf = new_buf;
    }
    let (fmt, casts) = printf::to_rust_format(&buf);
    assert!(args.len() == casts.len());
    let mut new_args = String::new();
    for (arg, cast) in args.iter().zip(casts) {
        let arg = pprust::expr_to_string(arg);
        match cast {
            "&str" => write!(
                new_args,
                "std::ffi::CStr::from_ptr(({}) as _).to_str().unwrap(), ",
                arg
            )
            .unwrap(),
            "String" => write!(
                new_args,
                "{{
    let mut p: *const u8 = {} as _;
    let mut s: String = String::new();
    loop {{
        let slice = std::slice::from_raw_parts(p, 4);
        let i = u32::from_le_bytes([slice[0], slice[1], slice[2], slice[3]]);
        if i == 0 {{
            break s;
        }}
        s.push(std::char::from_u32(i).unwrap());
        p = p.offset(4);
    }}
}}",
                arg
            )
            .unwrap(),
            _ => write!(new_args, "({}) as {}, ", arg, cast).unwrap(),
        }
    }
    let stream = stream.borrow_for(StreamTrait::Write);
    expr!(
        "{{
    use std::io::Write;
    write!({}, \"{}\", {})
}}",
        stream,
        fmt,
        new_args
    )
}

#[inline]
fn transform_fputc<S: StreamExpr>(stream: &S, c: &Expr, ic: IndicatorCheck<'_>) -> Expr {
    let stream_str = stream.borrow_for(StreamTrait::Write);
    let c = pprust::expr_to_string(c);
    if ic.has_check() {
        expr!(
            "{{
    use std::io::Write;
    let c = {};
    match ({}).write_all(&[c as u8]) {{
        Ok(_) => c,
        Err(e) => {{
            {}
            libc::EOF
        }}
    }}
}}",
            c,
            stream_str,
            ic.error_handling_no_eof(),
        )
    } else {
        expr!(
            "{{
    use std::io::Write;
    let c = {};
    ({}).write_all(&[c as u8]).map_or(libc::EOF, |_| c)
}}",
            c,
            stream_str
        )
    }
}

#[inline]
fn transform_fputs<S: StreamExpr>(stream: &S, s: &Expr, ic: IndicatorCheck<'_>) -> Expr {
    let stream_str = stream.borrow_for(StreamTrait::Write);
    let s = pprust::expr_to_string(s);
    if ic.has_check() {
        expr!(
            "{{
    use std::io::Write;
    match ({}).write_all(std::ffi::CStr::from_ptr(({}) as _).to_bytes()) {{
        Ok(_) => 0,
        Err(e) => {{
            {}
            libc::EOF
        }}
    }}
}}",
            stream_str,
            s,
            ic.error_handling_no_eof(),
        )
    } else {
        expr!(
            "{{
    use std::io::Write;
    ({}).write_all(std::ffi::CStr::from_ptr(({}) as _).to_bytes())
        .map_or(libc::EOF, |_| 0)
}}",
            stream_str,
            s
        )
    }
}

#[inline]
fn transform_fwrite<S: StreamExpr>(
    stream: &S,
    ptr: &Expr,
    size: &Expr,
    nitems: &Expr,
    ic: IndicatorCheck<'_>,
) -> Expr {
    let stream_str = stream.borrow_for(StreamTrait::Write);
    let ptr = pprust::expr_to_string(ptr);
    let size = pprust::expr_to_string(size);
    let nitems = pprust::expr_to_string(nitems);
    let handling = ic.error_handling_no_eof();
    expr!(
        "{{
    use std::io::Write;
    let mut stream = {};
    let size = {};
    let ptr: &[u8] = std::slice::from_raw_parts({} as _, (size * ({})) as usize);
    let mut i = 0;
    for data in ptr.chunks(size as usize) {{
        if let Err(e) = stream.write_all(data) {{
            {}
            break;
        }}
        i += 1;
    }}
    i
}}",
        stream_str,
        size,
        ptr,
        nitems,
        handling
    )
}

#[inline]
fn transform_fflush<S: StreamExpr>(stream: &S, ic: IndicatorCheck<'_>) -> Expr {
    let stream_str = stream.borrow_for(StreamTrait::Write);
    if ic.has_check() {
        expr!(
            "{{
    use std::io::Write;
    match ({}).flush() {{
        Ok(_) => 0,
        Err(e) => {{
            {}
            libc::EOF
        }}
    }}
}}",
            stream_str,
            ic.error_handling_no_eof(),
        )
    } else {
        expr!(
            "{{
    use std::io::Write;
    ({}).flush().map_or(libc::EOF, |_| 0)
}}",
            stream_str
        )
    }
}

#[inline]
fn transform_puts(s: &Expr, ic: IndicatorCheck<'_>) -> Expr {
    let s = pprust::expr_to_string(s);
    if ic.has_check() {
        expr!(
            r#"{{
    use std::io::Write;
    let mut stream = std::io::stdout();
    match stream
        .write_all(std::ffi::CStr::from_ptr(({}) as _).to_bytes())
        .and_then(|_| stream.write_all(b"\n")) {{
        Ok(_) => 0,
        Err(e) => {{
            {}
            libc::EOF
        }}
    }}
}}"#,
            s,
            ic.error_handling_no_eof(),
        )
    } else {
        expr!(
            r#"{{
    use std::io::Write;
    let mut stream = std::io::stdout();
    stream
        .write_all(std::ffi::CStr::from_ptr(({}) as _).to_bytes())
        .and_then(|_| stream.write_all(b"\n"))
        .map_or(libc::EOF, |_| 0)
}}"#,
            s
        )
    }
}

#[inline]
fn transform_fseek<S: StreamExpr>(stream: &S, off: &Expr, whence: &Expr) -> Expr {
    let stream = stream.borrow_for(StreamTrait::Seek);
    let off = pprust::expr_to_string(off);
    let whence = LikelyLit::from_expr(whence);
    match whence {
        LikelyLit::Lit(lit) => {
            let v = match lit.as_str() {
                "0" => "Start",
                "1" => "Current",
                "2" => "End",
                lit => panic!("{}", lit),
            };
            expr!(
                "{{
    use std::io::Seek;
    ({}).seek(std::io::SeekFrom::{}(({}) as _)).map_or(-1, |_| 0)
}}",
                stream,
                v,
                off
            )
        }
        LikelyLit::If(_, _, _) => todo!(),
        LikelyLit::Path(_, _) => todo!(),
        LikelyLit::Other(_) => todo!(),
    }
}

#[inline]
fn transform_ftell<S: StreamExpr>(stream: &S) -> Expr {
    let stream = stream.borrow_for(StreamTrait::Seek);
    expr!(
        "{{
    use std::io::Seek;
    ({}).stream_position().map_or(-1, |p| p as i64)
}}",
        stream
    )
}

#[inline]
fn transform_rewind<S: StreamExpr>(stream: &S) -> Expr {
    let stream = stream.borrow_for(StreamTrait::Seek);
    expr!(
        "{{
    use std::io::Seek;
    ({}).rewind();
}}",
        stream
    )
}

#[inline]
fn transform_fileno<S: StreamExpr>(stream: &S) -> Expr {
    let stream = stream.borrow_for(StreamTrait::AsRawFd);
    expr!(
        "{{
    use std::os::fd::AsRawFd;
    ({}).as_raw_fd()
}}",
        stream
    )
}

#[derive(Debug)]
pub enum LikelyLit<'a> {
    Lit(Symbol),
    If(&'a Expr, Box<LikelyLit<'a>>, Box<LikelyLit<'a>>),
    Path(Symbol, Span),
    Other(&'a Expr),
}

impl<'a> LikelyLit<'a> {
    pub fn from_expr(expr: &'a Expr) -> Self {
        match &expr.kind {
            ExprKind::MethodCall(box MethodCall { receiver: e, .. }) | ExprKind::Cast(e, _) => {
                Self::from_expr(e)
            }
            ExprKind::Lit(lit) => LikelyLit::Lit(lit.symbol),
            ExprKind::If(c, t, Some(f)) => {
                let [t] = &t.stmts[..] else { panic!() };
                let StmtKind::Expr(t) = &t.kind else { panic!() };
                let t = Self::from_expr(t);
                let f = Self::from_expr(f);
                LikelyLit::If(c, Box::new(t), Box::new(f))
            }
            ExprKind::Call(callee, args) => {
                if let ExprKind::Path(_, path) = &callee.kind {
                    let callee = path.segments.last().unwrap().ident.name.as_str();
                    match callee {
                        "dcgettext" => Self::from_expr(&args[1]),
                        "transmute" => Self::from_expr(&args[0]),
                        _ => LikelyLit::Other(expr),
                    }
                } else {
                    LikelyLit::Other(expr)
                }
            }
            ExprKind::Paren(e) => Self::from_expr(e),
            ExprKind::Unary(UnOp::Deref, e) => Self::from_expr(e),
            ExprKind::Path(_, path) => {
                let symbol = path.segments.last().unwrap().ident.name;
                LikelyLit::Path(symbol, path.span)
            }
            ExprKind::Block(block, _) => {
                let [.., stmt] = &block.stmts[..] else { return LikelyLit::Other(expr) };
                let StmtKind::Expr(expr) = &stmt.kind else { return LikelyLit::Other(expr) };
                Self::from_expr(expr)
            }
            _ => LikelyLit::Other(expr),
        }
    }
}

mod printf;
mod scanf;

#[cfg(test)]
mod tests;
