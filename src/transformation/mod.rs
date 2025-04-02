use std::{fmt::Write as _, fs, ops::Deref};

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
use rustc_hir::{self as hir, def::Res, intravisit, HirId};
use rustc_index::{bit_set::BitSet, Idx};
use rustc_lexer::unescape;
use rustc_middle::{
    hir::nested_filter,
    mir::{self, CastKind, Constant, ConstantKind, Location, Operand, Rvalue},
    ty::{self, AdtDef, TyCtxt},
};
use rustc_span::{def_id::LocalDefId, symbol::Ident, FileName, RealFileName, Span, Symbol};
use typed_arena::Arena;

use crate::{
    api_list::{self, Origin, Permission},
    ast_maker::*,
    bit_set::BitSet8,
    compile_util::{self, Pass},
    file_analysis::{self, Loc},
    rustc_middle::mir::visit::Visitor as _,
};

pub fn write_to_files(fss: &[(FileName, String)]) -> std::io::Result<()> {
    for (f, s) in fss {
        let FileName::Real(RealFileName::LocalPath(p)) = f else { panic!() };
        fs::write(p, s)?;
    }
    Ok(())
}

#[derive(Debug, Clone, Copy)]
pub struct Transformation;

impl Pass for Transformation {
    type Out = Vec<(FileName, String)>;

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
        for (span, loc) in &hir_ctx.binding_span_to_loc {
            if !unsupported.contains(span) {
                continue;
            }
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
            .zip(&analysis_res.permissions)
            .zip(&analysis_res.origins)
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
                            todo!()
                        }
                        _ => panic!(),
                    }
                }
                Loc::Field(def_id, field) => (HirLoc::Field(*def_id, *field), false),
                _ => continue,
            };
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
            let permissions = &analysis_res.permissions[loc_id];
            let origins = &analysis_res.origins[loc_id];
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

        let parse_sess = new_parse_sess();
        let mut updated = vec![];

        let source_map = tcx.sess.source_map();
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
                updated: false,
                static_span_to_lit: &ast_visitor.static_span_to_lit,
                hir: &hir_ctx,
                param_to_loc: &param_to_hir_loc,
                loc_to_pot: &hir_loc_to_pot,
                api_sig_spans: &api_sig_spans,
                null_casts: &null_casts,
                unsupported: &unsupported,
                is_stdin_unsupported,
                updated_field_spans: FxHashSet::default(),
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
                updated.push((file.name.clone(), s));
            }
        }

        updated
    }
}

struct AstVisitor {
    /// static variable definition's span to its literal
    static_span_to_lit: FxHashMap<Span, Symbol>,
}

impl<'ast> Visitor<'ast> for AstVisitor {
    fn visit_item(&mut self, item: &'ast Item) {
        if let ItemKind::Static(box StaticItem {
            expr: Some(expr), ..
        }) = &item.kind
        {
            if let LikelyLit::Lit(lit) = LikelyLit::from_expr(expr) {
                self.static_span_to_lit.insert(item.span, lit);
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
    permissions: &'a BitSet<Permission>,
    #[allow(unused)]
    origins: &'a BitSet<Origin>,
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
        permissions: &BitSet<Permission>,
        origins: &BitSet<Origin>,
        is_param: bool,
    ) -> &'a StreamType<'a> {
        if is_param {
            let mut traits = BitSet8::new_empty();
            for p in permissions.iter() {
                traits.insert(some_or!(StreamTrait::from_permission(p), continue));
            }
            let ty = self.alloc(StreamType::Impl(traits));
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
                    if permissions.contains(Permission::Write) {
                        self.buf_writer(&FILE_TY)
                    // } else if permissions.contains(Permission::Read)
                    //     || permissions.contains(Permission::BufRead)
                    // {
                    //     self.buf_reader(self.file)
                    } else {
                        // self.file
                        self.buf_reader(&FILE_TY)
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
            todo!("{:?}", origins)
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
    Impl(BitSet8<StreamTrait>),
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
            Self::Impl(traits) => {
                for (i, t) in traits.iter().enumerate() {
                    if i != 0 {
                        write!(f, " + ")?;
                    }
                    write!(f, "{}", t)?;
                }
                Ok(())
            }
        }
    }
}

impl StreamType<'_> {
    fn borrow_expr_for(self, expr: &str, tr: StreamTrait) -> String {
        match self {
            Self::File | Self::Stdout | Self::Stderr | Self::ChildStdin | Self::ChildStdout => {
                expr.to_string()
            }
            Self::Stdin => {
                if tr == StreamTrait::BufRead {
                    format!("({}).lock()", expr)
                } else {
                    expr.to_string()
                }
            }
            Self::BufWriter(t) | Self::BufReader(t) => {
                if tr == StreamTrait::AsRawFd {
                    let expr = format!("std::os::fd::AsFd::as_fd(({}).get_ref())", expr);
                    t.borrow_expr_for(&expr, tr)
                } else {
                    expr.to_string()
                }
            }
            Self::Impl(traits) => {
                assert!(traits.contains(tr));
                expr.to_string()
            }
            Self::Option(t) => {
                let expr = format!("({}).as_mut().unwrap()", expr);
                t.borrow_expr_for(&expr, tr)
            }
            Self::Ptr(t) => {
                let expr = format!("&mut *({})", expr);
                t.borrow_expr_for(&expr, tr)
            }
        }
    }

    fn opt_borrow_expr_for(self, expr: &str, tr: StreamTrait) -> String {
        match self {
            Self::File | Self::Stdout | Self::Stderr | Self::ChildStdin | Self::ChildStdout => {
                format!("Some({})", expr)
            }
            Self::Stdin => {
                if tr == StreamTrait::BufRead {
                    format!("Some(({}).lock())", expr)
                } else {
                    format!("Some({})", expr)
                }
            }
            Self::BufWriter(t) | Self::BufReader(t) => {
                if tr == StreamTrait::AsRawFd {
                    let expr = format!("std::os::fd::AsFd::as_fd(({}).get_ref())", expr);
                    t.opt_borrow_expr_for(&expr, tr)
                } else {
                    format!("Some({})", expr)
                }
            }
            Self::Impl(traits) => {
                assert!(traits.contains(tr));
                format!("Some({})", expr)
            }
            Self::Option(t) | Self::Ptr(t) => {
                let body = t.opt_borrow_expr_for("x", tr);
                format!("({}).as_mut().and_then(|x| {})", expr, body)
            }
        }
    }

    //     fn null_to_expr(self, null: &str) -> &str {
    //         match self {
    //             Self::Option(_) => "None",
    //             Self::Ptr(_) => null,
    //             _ => panic!(),
    //         }
    //     }

    //     fn assign(self, rty: StreamType<'a>, rhs: &str) -> String {
    //         if self == rty {
    //             return rhs.to_string();
    //         }
    //         if let Self::Option(this) = self {
    //             if *this == rty {
    //                 return format!("Some({})", rhs);
    //             }
    //         }
    //         if let Self::Ptr(this) = self {
    //             if *this == rty {
    //                 return format!("&mut ({})", rhs);
    //             }
    //         }
    //         todo!("{:?} {:?}", self, rty)
    //     }
}

trait StreamExpr {
    fn expr(&self) -> String;
    fn ty(&self) -> StreamType<'_>;

    #[inline]
    fn borrow_for(&self, tr: StreamTrait) -> String {
        self.ty().borrow_expr_for(&self.expr(), tr)
    }

    #[inline]
    fn opt_borrow_for(&self, tr: StreamTrait) -> String {
        self.ty().opt_borrow_expr_for(&self.expr(), tr)
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
    /// * global (var): item span
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
            hir::ItemKind::Static(_, _, _) => {
                let loc = HirLoc::Global(item.owner_id.def_id);
                self.add_binding(loc, item.span);
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
    ) -> Expr {
        match LikelyLit::from_expr(fmt) {
            LikelyLit::Lit(fmt) => transform_fprintf_lit(stream, fmt, args, wide),
            LikelyLit::If(_, _, _) => todo!(),
            LikelyLit::Path(span) => {
                let loc = self.hir.bound_span_to_loc[&span];
                let static_span = self.hir.loc_to_binding_span[&loc];
                let fmt = self.static_span_to_lit[&static_span];
                transform_fprintf_lit(stream, fmt, args, wide)
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

        if let ItemKind::Fn(f) = item {
            let HirLoc::Global(def_id) = self.hir.binding_span_to_loc[&f.sig.span] else {
                panic!()
            };
            let mut tparams = vec![];
            for (i, param) in f.sig.decl.inputs.iter_mut().enumerate() {
                if self.unsupported.contains(&param.pat.span) {
                    continue;
                }
                let p = Param::new(def_id, i);
                let pot = some_or!(self.param_pot(p), continue);
                *param.ty = ty!("Option<TT{}>", i);
                self.updated = true;
                tparams.push((i, pot));
            }
            for (i, po) in tparams {
                let tparam = if po.permissions.is_empty() {
                    ty_param!("TT{}", i)
                } else {
                    let StreamType::Option(ty) = po.ty else { panic!() };
                    ty_param!("TT{}: {}", i, ty)
                };
                f.generics.params.push(tparam);
            }
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
                        let loc = self.hir.bound_span_to_loc[&lhs];
                        let permissions = self.loc_to_pot[&loc].permissions;
                        let new_expr = transform_fopen(&args[0], &args[1], permissions);
                        self.replace_expr(expr, new_expr);
                    }
                    "popen" => {
                        let new_expr = transform_popen(&args[0], &args[1]);
                        self.replace_expr(expr, new_expr);
                    }
                    "fclose" | "pclose" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        self.replace_expr(callee, expr!("drop"));
                    }
                    "fscanf" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let new_expr = transform_fscanf(&stream, &args[1], &args[2..]);
                        self.replace_expr(expr, new_expr);
                    }
                    "fgetc" | "getc" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let new_expr = transform_fgetc(&stream);
                        self.replace_expr(expr, new_expr);
                    }
                    "getchar" => {
                        if self.is_stdin_unsupported {
                            return;
                        }
                        let stream = StdExpr::stdin();
                        let new_expr = transform_fgetc(&stream);
                        self.replace_expr(expr, new_expr);
                    }
                    "fgets" => {
                        if self.is_unsupported(&args[2]) {
                            return;
                        }
                        let ty = self.bound_pot(args[2].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[2], ty);
                        let new_expr = transform_fgets(&stream, &args[0], &args[1]);
                        self.replace_expr(expr, new_expr);
                    }
                    "fread" => {
                        if self.is_unsupported(&args[3]) {
                            return;
                        }
                        let ty = self.bound_pot(args[3].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[3], ty);
                        let new_expr = transform_fread(&stream, &args[0], &args[1], &args[2]);
                        self.replace_expr(expr, new_expr);
                    }
                    "getdelim" => todo!(),
                    "getline" => todo!(),
                    "feof" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let new_expr = transform_feof(&stream);
                        self.replace_expr(expr, new_expr);
                    }
                    "fprintf" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let new_expr = self.transform_fprintf(&stream, &args[1], &args[2..], false);
                        self.replace_expr(expr, new_expr);
                    }
                    "printf" => {
                        let stream = StdExpr::stdout();
                        let new_expr = self.transform_fprintf(&stream, &args[0], &args[1..], false);
                        self.replace_expr(expr, new_expr);
                    }
                    "wprintf" => {
                        let stream = StdExpr::stdout();
                        let new_expr = self.transform_fprintf(&stream, &args[0], &args[1..], true);
                        self.replace_expr(expr, new_expr);
                    }
                    "fputc" | "putc" => {
                        if self.is_unsupported(&args[1]) {
                            return;
                        }
                        let ty = self.bound_pot(args[1].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[1], ty);
                        let new_expr = transform_fputc(&stream, &args[0]);
                        self.replace_expr(expr, new_expr);
                    }
                    "putchar" => {
                        let stream = StdExpr::stdout();
                        let new_expr = transform_fputc(&stream, &args[0]);
                        self.replace_expr(expr, new_expr);
                    }
                    "fputs" => {
                        if self.is_unsupported(&args[1]) {
                            return;
                        }
                        let ty = self.bound_pot(args[1].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[1], ty);
                        let new_expr = transform_fputs(&stream, &args[0]);
                        self.replace_expr(expr, new_expr);
                    }
                    "puts" => {
                        let new_expr = transform_puts(&args[0]);
                        self.replace_expr(expr, new_expr);
                    }
                    "fwrite" => {
                        if self.is_unsupported(&args[3]) {
                            return;
                        }
                        let ty = self.bound_pot(args[3].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[3], ty);
                        let new_expr = transform_fwrite(&stream, &args[0], &args[1], &args[2]);
                        self.replace_expr(expr, new_expr);
                    }
                    "fflush" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let new_expr = transform_fflush(&stream);
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
                if self.null_casts.contains(&expr_span) {
                    self.replace_expr(expr, expr!("None"));
                }
            }
            _ => {}
        }
    }
}

fn transform_fopen(path: &Expr, mode: &Expr, permissions: &BitSet<Permission>) -> Expr {
    let path = pprust::expr_to_string(path);
    let path = format!(
        "std::ffi::CStr::from_ptr(({}) as _).to_str().unwrap()",
        path
    );
    let mode = LikelyLit::from_expr(mode);
    let wrapper = if permissions.contains(Permission::Write) {
        "std::io::BufWriter"
    } else {
        "std::io::BufReader"
    };
    match mode {
        LikelyLit::Lit(mode) => {
            let (prefix, suffix) = mode.as_str().split_at(1);
            let plus = suffix.contains('+');
            match prefix {
                "r" => {
                    if plus {
                        expr!(
                            "std::fs::OpenOptions::new()
                                .read(true)
                                .write(true)
                                .open({})
                                .ok()
                                .map({}::new)",
                            path,
                            wrapper
                        )
                    } else {
                        expr!("std::fs::File::open({}).ok().map({}::new)", path, wrapper)
                    }
                }
                "w" => {
                    if plus {
                        expr!(
                            "std::fs::OpenOptions::new()
                                .write(true)
                                .create(true)
                                .truncate(true)
                                .read(true)
                                .open({})
                                .ok()
                                .map({}::new)",
                            path,
                            wrapper
                        )
                    } else {
                        expr!("std::fs::File::create({}).ok().map({}::new)", path, wrapper)
                    }
                }
                "a" => {
                    if plus {
                        expr!(
                            "std::fs::OpenOptions::new()
                                .append(true)
                                .create(true)
                                .read(true)
                                .open({})
                                .ok()
                                .map({}::new)",
                            path,
                            wrapper
                        )
                    } else {
                        expr!(
                            "std::fs::OpenOptions::new()
                                .append(true)
                                .create(true)
                                .open({})
                                .ok()
                                .map({}::new)",
                            path,
                            wrapper
                        )
                    }
                }
                _ => panic!("{:?}", mode),
            }
        }
        LikelyLit::If(_, _, _) => todo!(),
        LikelyLit::Path(_) => todo!(),
        LikelyLit::Other(_) => todo!(),
    }
}

fn transform_popen(command: &Expr, mode: &Expr) -> Expr {
    let command = pprust::expr_to_string(command);
    let command = format!(
        "std::ffi::CStr::from_ptr(({}) as _).to_str().unwrap()",
        command
    );
    let mode = LikelyLit::from_expr(mode);
    match mode {
        LikelyLit::Lit(mode) => {
            let field = match &mode.as_str()[..1] {
                "r" => "stdout",
                "w" => "stdin",
                _ => panic!("{:?}", mode),
            };
            expr!(
                r#"std::process::Command::new("sh")
                .arg("-c")
                .arg("--")
                .arg({})
                .{1}(std::process::Stdio::piped())
                .spawn()
                .ok()
                .and_then(|child| child.{1})"#,
                command,
                field
            )
        }
        LikelyLit::If(_, _, _) => todo!(),
        LikelyLit::Path(_) => todo!(),
        LikelyLit::Other(_) => todo!(),
    }
}

fn transform_fscanf<S: StreamExpr, E: Deref<Target = Expr>>(
    stream: &S,
    fmt: &Expr,
    args: &[E],
) -> Expr {
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
        LikelyLit::Path(_) => todo!(),
        LikelyLit::Other(_) => todo!(),
    }
}

#[inline]
fn transform_fgetc<S: StreamExpr>(stream: &S) -> Expr {
    let stream = stream.borrow_for(StreamTrait::Read);
    expr!(
        "{{
    use std::io::Read;
    let mut buf = [0];
    ({}).read_exact(&mut buf).map_or(libc::EOF, |_| buf[0] as _)
}}",
        stream
    )
}

#[inline]
fn transform_fgets<S: StreamExpr>(stream: &S, s: &Expr, n: &Expr) -> Expr {
    let stream = stream.borrow_for(StreamTrait::BufRead);
    let s = pprust::expr_to_string(s);
    let n = pprust::expr_to_string(n);
    expr!(
        "{{
    use std::io::BufRead;
    let mut stream = {};
    let s = {};
    let n = ({}) as usize;
    let buf: &mut [u8] = std::slice::from_raw_parts_mut(s as _, n);
    let mut pos = 0;
    while pos < n - 1 {{
        let available = match stream.fill_buf() {{
            Ok(buf) => buf,
            Err(_) => {{
                pos = 0;
                break
            }}
        }};
        if available.is_empty() {{
            break;
        }}
        buf[pos] = available[0];
        stream.consume(1);
        pos += 1;
        if buf[pos - 1] == b'\\n' {{
            break;
        }}
    }}
    if pos == 0 {{
        std::ptr::null_mut()
    }} else {{
        buf[pos] = 0;
        s
    }}
}}",
        stream,
        s,
        n
    )
}

#[inline]
fn transform_fread<S: StreamExpr>(stream: &S, ptr: &Expr, size: &Expr, nitems: &Expr) -> Expr {
    let stream = stream.borrow_for(StreamTrait::Read);
    let ptr = pprust::expr_to_string(ptr);
    let size = pprust::expr_to_string(size);
    let nitems = pprust::expr_to_string(nitems);
    expr!(
        "{{
    use std::io::Read;
    let mut stream = {};
    let size = {};
    let ptr: &mut [u8] = std::slice::from_raw_parts_mut(({}) as _, (size * ({})) as usize);
    let mut i = 0;
    for data in ptr.chunks_mut(size as usize) {{
        if stream.read_exact(data).is_err() {{
            break;
        }}
        i += 1;
    }}
    i
}}",
        stream,
        size,
        ptr,
        nitems,
    )
}

#[inline]
fn transform_feof<S: StreamExpr>(stream: &S) -> Expr {
    let stream = stream.borrow_for(StreamTrait::Read);
    expr!(
        "{{
    use std::io::Read;
    let mut buf = [0];
    ({}).read_exact(&mut buf).map_or(1, |_| 0)
}}",
        stream
    )
}

fn transform_fprintf_lit<S: StreamExpr, E: Deref<Target = Expr>>(
    stream: &S,
    fmt: Symbol,
    args: &[E],
    wide: bool,
) -> Expr {
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
fn transform_fputc<S: StreamExpr>(stream: &S, c: &Expr) -> Expr {
    let stream = stream.borrow_for(StreamTrait::Write);
    let c = pprust::expr_to_string(c);
    expr!(
        "{{
    use std::io::Write;
    let c = {};
    ({}).write_all(&[c as u8]).map_or(libc::EOF, |_| c)
}}",
        c,
        stream
    )
}

#[inline]
fn transform_fputs<S: StreamExpr>(stream: &S, s: &Expr) -> Expr {
    let stream = stream.borrow_for(StreamTrait::Write);
    let s = pprust::expr_to_string(s);
    expr!(
        "{{
    use std::io::Write;
    ({}).write_all(std::ffi::CStr::from_ptr(({}) as _).to_bytes())
        .map_or(libc::EOF, |_| 0)
}}",
        stream,
        s
    )
}

#[inline]
fn transform_fwrite<S: StreamExpr>(stream: &S, ptr: &Expr, size: &Expr, nitems: &Expr) -> Expr {
    let stream = stream.borrow_for(StreamTrait::Write);
    let ptr = pprust::expr_to_string(ptr);
    let size = pprust::expr_to_string(size);
    let nitems = pprust::expr_to_string(nitems);
    expr!(
        "{{
    use std::io::Write;
    let mut stream = {};
    let size = {};
    let ptr: &[u8] = std::slice::from_raw_parts({} as _, (size * ({})) as usize);
    let mut i = 0;
    for data in ptr.chunks(size as usize) {{
        if stream.write_all(data).is_err() {{
            break;
        }}
        i += 1;
    }}
    i
}}",
        stream,
        size,
        ptr,
        nitems
    )
}

#[inline]
fn transform_fflush<S: StreamExpr>(stream: &S) -> Expr {
    let stream = stream.borrow_for(StreamTrait::Write);
    expr!(
        "{{
    use std::io::Write;
    ({}).flush().map_or(libc::EOF, |_| 0)
}}",
        stream
    )
}

#[inline]
fn transform_puts(s: &Expr) -> Expr {
    let s = pprust::expr_to_string(s);
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
        LikelyLit::Path(_) => todo!(),
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
    Path(Span),
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
            ExprKind::Path(_, path) => LikelyLit::Path(path.span),
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
