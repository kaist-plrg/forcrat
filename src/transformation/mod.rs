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
use rustc_hir::{self as hir, def::Res, intravisit, HirId};
use rustc_index::bit_set::BitSet;
use rustc_lexer::unescape;
use rustc_middle::{
    hir::nested_filter,
    mir::{self, CastKind, Constant, ConstantKind, Location, Operand, Rvalue, TerminatorKind},
    ty::{self, TyCtxt},
};
use rustc_span::{def_id::LocalDefId, symbol::Ident, FileName, RealFileName, Span, Symbol};

use crate::{
    api_list::{self, Origin, Permission},
    ast_maker::*,
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
struct Po<'a> {
    permissions: &'a BitSet<Permission>,
    origins: &'a BitSet<Origin>,
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

        let mut loc_to_po = FxHashMap::default();
        let mut hir_loc_to_po = FxHashMap::default();

        for ((loc, permissions), origins) in analysis_res
            .locs
            .iter()
            .zip(&analysis_res.permissions)
            .zip(&analysis_res.origins)
        {
            let hir_loc = match loc {
                Loc::Var(def_id, local) => {
                    let hir::Node::Item(item) = hir.get_by_def_id(*def_id) else { unreachable!() };
                    match item.kind {
                        hir::ItemKind::Fn(_, _, _) => {
                            let body = tcx.optimized_mir(*def_id);
                            let local_decl = &body.local_decls[*local];
                            let span = local_decl.source_info.span;
                            *some_or!(hir_ctx.binding_span_to_loc.get(&span), continue)
                        }
                        hir::ItemKind::Static(_, _, _) => {
                            todo!()
                        }
                        _ => unreachable!(),
                    }
                }
                Loc::Field(def_id, field) => HirLoc::Field(*def_id, *field),
                _ => continue,
            };
            let po = Po {
                permissions,
                origins,
            };
            loc_to_po.insert(*loc, po);
            let old = hir_loc_to_po.insert(hir_loc, po);
            assert!(old.is_none());
        }

        let mut api_sig_spans = FxHashSet::default();
        let mut call_file_args = FxHashMap::default();
        let mut null_checks = FxHashSet::default();
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

                for bbd in body.basic_blocks.iter() {
                    let terminator = bbd.terminator();
                    let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
                        continue;
                    };
                    let span = terminator.source_info.span;
                    let file_args: Vec<_> = args
                        .iter()
                        .enumerate()
                        .filter_map(|(i, arg)| {
                            let ty = arg.ty(&body.local_decls, tcx);
                            if compile_util::contains_file_ty(ty, tcx) {
                                Some(i)
                            } else {
                                None
                            }
                        })
                        .collect();
                    if !file_args.is_empty() {
                        call_file_args.insert(span, file_args);
                    }

                    let [arg] = &args[..] else { continue };
                    let ty = arg.ty(&body.local_decls, tcx);
                    if !compile_util::contains_file_ty(ty, tcx) {
                        continue;
                    }
                    let constant = some_or!(func.constant(), continue);
                    let ConstantKind::Val(_, ty) = constant.literal else { unreachable!() };
                    let ty::TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                    let sym = compile_util::def_id_to_value_symbol(def_id, tcx);
                    let sym = some_or!(sym, continue);
                    if sym.as_str() == "is_null" {
                        null_checks.insert(span);
                    }
                }

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
                updated: false,
                static_span_to_lit: &ast_visitor.static_span_to_lit,
                hir_ctx: &hir_ctx,
                hir_loc_to_po: &hir_loc_to_po,
                loc_to_po: &loc_to_po,
                api_sig_spans: &api_sig_spans,
                call_file_args: &call_file_args,
                null_checks: &null_checks,
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
                let typeck = self.tcx.typeck(expr.hir_id.owner.def_id);
                let ty = typeck.expr_ty(e);
                let ty::TyKind::Adt(adt_def, _) = ty.kind() else { return };
                let def_id = some_or!(adt_def.did().as_local(), return);
                let variant = adt_def.variant(VariantIdx::from_u32(0));
                let i = variant
                    .fields
                    .iter_enumerated()
                    .find(|(_, f)| f.name == field.name)
                    .unwrap()
                    .0;
                let loc = HirLoc::Field(def_id, i);
                self.add_bound(loc, expr.span);
            }
            hir::ExprKind::Assign(lhs, rhs, _) => {
                self.add_assignment(lhs.span, rhs.span);
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

struct TransformVisitor<'a> {
    hir_ctx: &'a HirCtx,
    /// location to permissions and origins
    loc_to_po: &'a FxHashMap<Loc, Po<'a>>,
    /// HIR location to permissions and origins
    hir_loc_to_po: &'a FxHashMap<HirLoc, Po<'a>>,
    /// static variable definition's span to its literal
    static_span_to_lit: &'a FxHashMap<Span, Symbol>,
    /// user-defined API functions' signatures' spans
    api_sig_spans: &'a FxHashSet<Span>,
    /// call expr span to file argument positions
    call_file_args: &'a FxHashMap<Span, Vec<usize>>,
    /// file pointer null check expr spans
    null_checks: &'a FxHashSet<Span>,
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

impl TransformVisitor<'_> {
    #[inline]
    fn is_unsupported(&self, expr: &Expr) -> bool {
        self.unsupported.contains(&expr.span) || self.unsupported.contains(&remove_cast(expr).span)
    }

    #[inline]
    fn transform_fprintf<E: Deref<Target = Expr>>(
        &self,
        stream: &str,
        fmt: &Expr,
        args: &[E],
        wide: bool,
    ) -> Expr {
        match LikelyLit::from_expr(fmt) {
            LikelyLit::Lit(fmt) => transform_fprintf_lit(stream, fmt, args, wide),
            LikelyLit::If(_, _, _) => todo!(),
            LikelyLit::Path(span) => {
                let loc = self.hir_ctx.bound_span_to_loc[&span];
                let static_span = self.hir_ctx.loc_to_binding_span[&loc];
                let fmt = self.static_span_to_lit[&static_span];
                transform_fprintf_lit(stream, fmt, args, wide)
            }
            LikelyLit::Other(e) => todo!("{:?}", e),
        }
    }

    fn binding_ty(&self, span: Span) -> Option<Ty> {
        let loc = self.hir_ctx.binding_span_to_loc.get(&span)?;
        let Po {
            origins,
            permissions,
        } = self.hir_loc_to_po.get(loc)?;
        if origins.is_empty() {
            return None;
        }
        let origins: Vec<_> = origins.iter().collect();
        let [origin] = &origins[..] else { panic!("{:?}", span) };
        let ty = match origin {
            Origin::File => {
                if permissions.contains(Permission::Write) {
                    ty!("Option<std::io::BufWriter<std::fs::File>>")
                } else {
                    ty!("Option<std::io::BufReader<std::fs::File>>")
                }
            }
            Origin::Stdin => ty!("Option<std::io::Stdin>"),
            Origin::Stdout => ty!("Option<std::io::Stdout>"),
            Origin::Stderr => ty!("Option<std::io::Stderr>"),
            Origin::PipeRead => ty!("Option<std::process::ChildStdout>"),
            Origin::PipeWrite => ty!("Option<std::process::ChildStdin>"),
            Origin::PipeDyn => todo!(),
            Origin::Buffer => todo!(),
        };
        Some(ty)
    }
}

impl MutVisitor for TransformVisitor<'_> {
    fn visit_item_kind(&mut self, item: &mut ItemKind) {
        if let ItemKind::Fn(f) = item {
            if self.api_sig_spans.contains(&f.sig.span) {
                return;
            }
        }

        mut_visit::noop_visit_item_kind(item, self);

        if let ItemKind::Fn(f) = item {
            let HirLoc::Global(def_id) = self.hir_ctx.binding_span_to_loc[&f.sig.span] else {
                unreachable!()
            };
            let mut tparams = vec![];
            for (i, param) in f.sig.decl.inputs.iter_mut().enumerate() {
                if self.unsupported.contains(&param.pat.span) {
                    continue;
                }
                let loc = Loc::Var(def_id, mir::Local::from_usize(i + 1));
                let po = some_or!(self.loc_to_po.get(&loc), continue);
                *param.ty = ty!("Option<TT{}>", i);
                self.updated = true;
                tparams.push((i, po));
            }
            for (i, po) in tparams {
                let tparam = if po.permissions.is_empty() {
                    ty_param!("TT{}", i)
                } else {
                    let mut traits = String::new();
                    for (i, p) in po.permissions.iter().enumerate() {
                        if i > 0 {
                            traits.push_str(" + ");
                        }
                        traits.push_str(p.full_name());
                    }
                    ty_param!("TT{}: {}", i, traits)
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
                self.updated = true;
                self.updated_field_spans.insert(f.span);
                *f.ty = ty;
            }
        }
    }

    fn visit_local(&mut self, local: &mut P<Local>) {
        mut_visit::noop_visit_local(local, self);

        if self.unsupported.contains(&local.pat.span) {
            return;
        }

        if let Some(ty) = self.binding_ty(local.pat.span) {
            self.updated = true;
            **local.ty.as_mut().unwrap() = ty;
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
                if let ExprKind::Path(None, path) = &callee.kind {
                    if let [seg] = &path.segments[..] {
                        let symbol = seg.ident.name;
                        let name = api_list::normalize_api_name(symbol.as_str());
                        match name {
                            "fopen" => {
                                self.updated = true;
                                let lhs = self.hir_ctx.rhs_to_lhs[&expr_span];
                                let loc = self.hir_ctx.bound_span_to_loc[&lhs];
                                let permissions = self.hir_loc_to_po[&loc].permissions;
                                let new_expr = transform_fopen(&args[0], &args[1], permissions);
                                *expr.deref_mut() = new_expr;
                            }
                            "popen" => {
                                self.updated = true;
                                let new_expr = transform_popen(&args[0], &args[1]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fclose" | "pclose" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
                                self.updated = true;
                                *callee.deref_mut() = expr!("drop");
                            }
                            "fscanf" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr = transform_fscanf(&args[0], &args[1], &args[2..]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fgetc" | "getc" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
                                self.updated = true;
                                let stream = pprust::expr_to_string(&args[0]);
                                let new_expr = transform_fgetc(&stream);
                                *expr.deref_mut() = new_expr;
                            }
                            "getchar" => {
                                if self.is_stdin_unsupported {
                                    return;
                                }
                                self.updated = true;
                                let stream = "Some(std::io::stdin())";
                                let new_expr = transform_fgetc(stream);
                                *expr.deref_mut() = new_expr;
                            }
                            "fgets" => {
                                if self.is_unsupported(&args[2]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr = transform_fgets(&args[2], &args[0], &args[1]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fread" => {
                                if self.is_unsupported(&args[3]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr =
                                    transform_fread(&args[3], &args[0], &args[1], &args[2]);
                                *expr.deref_mut() = new_expr;
                            }
                            "getdelim" => todo!(),
                            "getline" => todo!(),
                            "feof" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr = transform_feof(&args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fprintf" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
                                self.updated = true;
                                let stream = pprust::expr_to_string(&args[0]);
                                let new_expr =
                                    self.transform_fprintf(&stream, &args[1], &args[2..], false);
                                *expr.deref_mut() = new_expr;
                            }
                            "printf" => {
                                self.updated = true;
                                let stream = "Some(std::io::stdout())";
                                let new_expr =
                                    self.transform_fprintf(stream, &args[0], &args[1..], false);
                                *expr.deref_mut() = new_expr;
                            }
                            "wprintf" => {
                                self.updated = true;
                                let stream = "Some(std::io::stdout())";
                                let new_expr =
                                    self.transform_fprintf(stream, &args[0], &args[1..], true);
                                *expr.deref_mut() = new_expr;
                            }
                            "fputc" | "putc" => {
                                if self.is_unsupported(&args[1]) {
                                    return;
                                }
                                self.updated = true;
                                let stream = pprust::expr_to_string(&args[1]);
                                let new_expr = transform_fputc(&stream, &args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "putchar" => {
                                self.updated = true;
                                let stream = "Some(std::io::stdout())";
                                let new_expr = transform_fputc(stream, &args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fputs" => {
                                if self.is_unsupported(&args[1]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr = transform_fputs(&args[1], &args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "puts" => {
                                self.updated = true;
                                let new_expr = transform_puts(&args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fwrite" => {
                                if self.is_unsupported(&args[3]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr =
                                    transform_fwrite(&args[3], &args[0], &args[1], &args[2]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fflush" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr = transform_fflush(&args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fseek" | "fseeko" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr = transform_fseek(&args[0], &args[1], &args[2]);
                                *expr.deref_mut() = new_expr;
                            }
                            "ftell" | "ftello" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr = transform_ftell(&args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "rewind" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr = transform_rewind(&args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fgetpos" => todo!(),
                            "fsetpos" => todo!(),
                            "fileno" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr = transform_fileno(&args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            _ => {
                                if let Some(pos) = self.call_file_args.get(&expr_span) {
                                    let mut none = false;
                                    for i in pos {
                                        let arg = &mut args[*i];
                                        if self.is_unsupported(arg) {
                                            continue;
                                        }
                                        let a = pprust::expr_to_string(arg);
                                        let new_expr = expr!("({}).as_mut()", a);
                                        **arg = new_expr;
                                        self.updated = true;
                                        if a == "None" {
                                            none = true;
                                        }
                                    }
                                    if none {
                                        let c = pprust::expr_to_string(callee);
                                        let new_expr = expr!("{}::<&mut std::fs::File>", c);
                                        **callee = new_expr;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            ExprKind::Path(None, path) => {
                if let [seg] = &path.segments[..] {
                    match seg.ident.name.as_str() {
                        "stdin" => {
                            self.updated = true;
                            **expr = expr!("Some(std::io::stdin())");
                        }
                        "stdout" => {
                            self.updated = true;
                            **expr = expr!("Some(std::io::stdout())");
                        }
                        "stderr" => {
                            self.updated = true;
                            **expr = expr!("Some(std::io::stderr())");
                        }
                        _ => {}
                    }
                }
            }
            ExprKind::MethodCall(box MethodCall { receiver, seg, .. }) => {
                if !self.is_unsupported(receiver) && self.null_checks.contains(&expr_span) {
                    self.updated = true;
                    seg.ident = Ident::from_str("is_none");
                }
            }
            ExprKind::Cast(_, _) => {
                if self.null_casts.contains(&expr_span) {
                    self.updated = true;
                    **expr = expr!("None");
                }
            }
            _ => {}
        }
    }
}

#[inline]
fn unwrap_some_call(expr: &Expr) -> Option<&Expr> {
    let ExprKind::Call(callee, args) = &expr.kind else { return None };
    let ExprKind::Path(None, path) = &callee.kind else { return None };
    if path.segments.last().unwrap().ident.name.as_str() != "Some" {
        return None;
    }
    let [arg] = &args[..] else { return None };
    let ExprKind::Call(callee, _) = &arg.kind else { return None };
    let ExprKind::Path(None, _) = &callee.kind else { return None };
    Some(callee)
}

#[inline]
fn make_stream_def(stream: &Expr) -> String {
    if let Some(stream) = unwrap_some_call(stream) {
        let stream = pprust::expr_to_string(stream);
        format!("let mut stream = {}();", stream)
    } else {
        let stream = pprust::expr_to_string(stream);
        format!("let stream = ({}).as_mut().unwrap();", stream)
    }
}

#[inline]
fn make_buf_stream_def(stream: &Expr) -> String {
    if let Some(stream) = unwrap_some_call(stream) {
        let stream = pprust::expr_to_string(stream);
        format!("let stream = {}(); let mut stream = stream.lock();", stream)
    } else {
        let stream = pprust::expr_to_string(stream);
        format!("let stream = ({}).as_mut().unwrap();", stream)
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

fn transform_fscanf<E: Deref<Target = Expr>>(stream: &Expr, fmt: &Expr, args: &[E]) -> Expr {
    let stream_def = make_buf_stream_def(stream);
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
    {}
    let mut count = 0i32;
    {}
    count
}}",
                stream_def,
                code
            )
        }
        LikelyLit::If(_, _, _) => todo!(),
        LikelyLit::Path(_) => todo!(),
        LikelyLit::Other(_) => todo!(),
    }
}

#[inline]
fn transform_fgetc(stream: &str) -> Expr {
    expr!(
        "{{
    use std::io::Read;
    let mut buf = [0];
    ({}).as_mut().unwrap().read_exact(&mut buf).map_or(libc::EOF, |_| buf[0] as _)
}}",
        stream
    )
}

#[inline]
fn transform_fgets(stream: &Expr, s: &Expr, n: &Expr) -> Expr {
    let stream_def = make_buf_stream_def(stream);
    let s = pprust::expr_to_string(s);
    let n = pprust::expr_to_string(n);
    expr!(
        "{{
    use std::io::BufRead;
    {}
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
        stream_def,
        s,
        n
    )
}

#[inline]
fn transform_fread(stream: &Expr, ptr: &Expr, size: &Expr, nitems: &Expr) -> Expr {
    let stream_def = make_stream_def(stream);
    let ptr = pprust::expr_to_string(ptr);
    let size = pprust::expr_to_string(size);
    let nitems = pprust::expr_to_string(nitems);
    expr!(
        "{{
    use std::io::Read;
    {}
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
        stream_def,
        size,
        ptr,
        nitems,
    )
}

#[inline]
fn transform_feof(stream: &Expr) -> Expr {
    let stream = pprust::expr_to_string(stream);
    expr!(
        "{{
    use std::io::Read;
    let mut buf = [0];
    ({}).as_mut().unwrap().read_exact(&mut buf).map_or(1, |_| 0)
}}",
        stream
    )
}

fn transform_fprintf_lit<E: Deref<Target = Expr>>(
    stream: &str,
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
    expr!(
        "{{
    use std::io::Write;
    write!(({}).as_mut().unwrap(), \"{}\", {})
}}",
        stream,
        fmt,
        new_args
    )
}

#[inline]
fn transform_fputc(stream: &str, c: &Expr) -> Expr {
    let c = pprust::expr_to_string(c);
    expr!(
        "{{
    use std::io::Write;
    let c = {};
    ({}).as_mut().unwrap().write_all(&[c as u8]).map_or(libc::EOF, |_| c)
}}",
        c,
        stream
    )
}

#[inline]
fn transform_fputs(stream: &Expr, s: &Expr) -> Expr {
    let stream = pprust::expr_to_string(stream);
    let s = pprust::expr_to_string(s);
    expr!(
        "{{
    use std::io::Write;
    ({}).as_mut().unwrap()
        .write_all(std::ffi::CStr::from_ptr(({}) as _).to_bytes())
        .map_or(libc::EOF, |_| 0)
}}",
        stream,
        s
    )
}

#[inline]
fn transform_fwrite(stream: &Expr, ptr: &Expr, size: &Expr, nitems: &Expr) -> Expr {
    let stream_def = make_stream_def(stream);
    let ptr = pprust::expr_to_string(ptr);
    let size = pprust::expr_to_string(size);
    let nitems = pprust::expr_to_string(nitems);
    expr!(
        "{{
    use std::io::Write;
    {}
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
        stream_def,
        size,
        ptr,
        nitems
    )
}

#[inline]
fn transform_fflush(stream: &Expr) -> Expr {
    let stream = pprust::expr_to_string(stream);
    expr!(
        "{{
    use std::io::Write;
    ({}).as_mut().unwrap().flush().map_or(libc::EOF, |_| 0)
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
fn transform_fseek(stream: &Expr, off: &Expr, whence: &Expr) -> Expr {
    let stream = pprust::expr_to_string(stream);
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
    ({}).as_mut().unwrap().seek(std::io::SeekFrom::{}(({}) as _)).map_or(-1, |_| 0)
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
fn transform_ftell(stream: &Expr) -> Expr {
    let stream = pprust::expr_to_string(stream);
    expr!(
        "{{
    use std::io::Seek;
    ({}).as_mut().unwrap().stream_position().map_or(-1, |p| p as i64)
}}",
        stream
    )
}

#[inline]
fn transform_rewind(stream: &Expr) -> Expr {
    let stream = pprust::expr_to_string(stream);
    expr!(
        "{{
    use std::io::Seek;
    ({}).as_mut().unwrap().rewind();
}}",
        stream
    )
}

#[inline]
fn transform_fileno(stream: &Expr) -> Expr {
    let stream = pprust::expr_to_string(stream);
    expr!(
        "{{
    use std::os::fd::AsRawFd;
    ({}).as_ref().unwrap().as_raw_fd()
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
