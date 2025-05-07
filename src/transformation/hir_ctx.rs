use etrace::some_or;
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir,
    def::{DefKind, Res},
    intravisit, HirId, QPath,
};
use rustc_middle::{
    hir::nested_filter,
    ty::{AdtDef, TyCtxt, TyKind},
};
use rustc_span::{def_id::LocalDefId, Span, Symbol};

use crate::{api_list, compile_util};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum HirLoc {
    Global(LocalDefId),
    Return(LocalDefId),
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
pub(super) struct HirCtx {
    /// location to binding occurrence span
    /// * global (var): ident span
    /// * global (fn): ident span
    /// * local: pat span
    /// * field: field span
    pub(super) loc_to_binding_span: FxHashMap<HirLoc, Span>,
    /// binding occurrence span to location
    pub(super) binding_span_to_loc: FxHashMap<Span, HirLoc>,

    /// location to bound occurrence spans
    pub(super) loc_to_bound_spans: FxHashMap<HirLoc, Vec<Span>>,
    /// bound occurrence span to location
    pub(super) bound_span_to_loc: FxHashMap<Span, HirLoc>,

    /// for each assignment, lhs span to rhs span
    pub(super) lhs_to_rhs: FxHashMap<Span, Span>,
    /// for each assignment, rhs span to lhs span
    pub(super) rhs_to_lhs: FxHashMap<Span, Span>,

    /// function def_id to feof argument names
    pub(super) feof_functions: FxHashMap<LocalDefId, FxHashSet<Symbol>>,
    /// function def_id to ferror argument names
    pub(super) ferror_functions: FxHashMap<LocalDefId, FxHashSet<Symbol>>,
    /// callee span to stream argument name
    pub(super) callee_span_to_stream_name: FxHashMap<Span, Symbol>,
    /// fn ptr call argument spans
    pub(super) fn_ptr_arg_spans: Vec<Span>,

    /// callee span to expr hir_id
    pub(super) callee_span_to_hir_id: FxHashMap<Span, HirId>,
    /// call expr span to callee id
    pub(super) call_span_to_callee_id: FxHashMap<Span, LocalDefId>,

    /// function def_id to returned local hir_ids
    pub(super) return_locals: FxHashMap<LocalDefId, FxHashSet<Option<HirId>>>,
    /// function def_id to returned static def_ids
    pub(super) return_statics: FxHashMap<LocalDefId, FxHashSet<LocalDefId>>,
    /// spans of function calls whose return values are used
    pub(super) retval_used_spans: FxHashSet<Span>,
    /// function def_id to returned expr spans
    pub(super) return_spans: FxHashMap<LocalDefId, Vec<Span>>,

    /// struct id to owning struct ids and field indices
    pub(super) struct_to_owning_structs: FxHashMap<LocalDefId, FxHashSet<(LocalDefId, FieldIdx)>>,
}

pub(super) struct HirVisitor<'tcx> {
    pub(super) tcx: TyCtxt<'tcx>,
    pub(super) ctx: HirCtx,
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

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        intravisit::walk_item(self, item);

        match item.kind {
            hir::ItemKind::Static(_, _, body_id) => {
                let loc = HirLoc::Global(item.owner_id.def_id);
                let body = self.tcx.hir_body(body_id);
                self.add_binding(loc, item.ident.span);
                self.add_bound(loc, item.ident.span);
                self.add_assignment(item.ident.span, body.value.span);
            }
            hir::ItemKind::Fn { .. } => {
                let loc = HirLoc::Global(item.owner_id.def_id);
                self.add_binding(loc, item.ident.span);
            }
            hir::ItemKind::Struct(vd, _) | hir::ItemKind::Union(vd, _) => {
                let hir::VariantData::Struct { fields, .. } = vd else { return };
                let def_id = item.owner_id.def_id;
                for (i, f) in fields.iter().enumerate() {
                    let loc = HirLoc::Field(def_id, FieldIdx::from_usize(i));
                    self.add_binding(loc, f.span);
                }
                let adt_def = self.tcx.adt_def(def_id);
                for variant in adt_def.variants() {
                    for (i, field) in variant.fields.iter_enumerated() {
                        let ty = field.ty(self.tcx, rustc_middle::ty::List::empty());
                        let owned_def_id = some_or!(owned_def_id(ty), continue);
                        self.ctx
                            .struct_to_owning_structs
                            .entry(owned_def_id)
                            .or_default()
                            .insert((def_id, i));
                    }
                }
            }
            _ => {}
        }
    }

    fn visit_local(&mut self, local: &'tcx hir::LetStmt<'tcx>) {
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
                if let hir::ExprKind::Path(QPath::Resolved(_, path)) = callee.kind {
                    self.ctx
                        .callee_span_to_hir_id
                        .insert(path.span, expr.hir_id);
                    if let Res::Def(DefKind::Fn, def_id) = path.res {
                        if let Some(def_id) = def_id.as_local() {
                            self.ctx.call_span_to_callee_id.insert(expr.span, def_id);
                        }
                    }
                    let name = path.segments.last().unwrap().ident.name;
                    if api_list::is_symbol_api(name) {
                        for (_, parent) in self.tcx.hir().parent_iter(expr.hir_id) {
                            match parent {
                                hir::Node::Expr(e) => {
                                    if !matches!(e.kind, hir::ExprKind::DropTemps(_)) {
                                        self.ctx.retval_used_spans.insert(expr.span);
                                        break;
                                    }
                                }
                                hir::Node::ExprField(_)
                                | hir::Node::LetStmt(_)
                                | hir::Node::Block(_) => {
                                    self.ctx.retval_used_spans.insert(expr.span);
                                    break;
                                }
                                hir::Node::Stmt(_) => {
                                    break;
                                }
                                _ => panic!("{:?}", parent),
                            }
                        }
                    }
                    let name = api_list::normalize_api_name(name.as_str());
                    let i = match name {
                        "fscanf" | "fgetc" | "getc" | "fprintf" | "fflush" | "feof" | "ferror"
                        | "clearerr" | "flockfile" | "funlockfile" => 0,
                        "fputc" | "putc" | "fputwc" | "putwc" | "fputs" => 1,
                        "fgets" | "getline" => 2,
                        "fread" | "getdelim" | "fwrite" => 3,
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
                } else {
                    for arg in args {
                        self.ctx.fn_ptr_arg_spans.push(arg.span);
                    }
                }
            }
            hir::ExprKind::Ret(Some(e)) => {
                let curr_func = expr.hir_id.owner.def_id;
                self.ctx
                    .return_spans
                    .entry(curr_func)
                    .or_default()
                    .push(e.span);
                let local = if let hir::ExprKind::Path(QPath::Resolved(_, path)) = e.kind {
                    match path.res {
                        Res::Local(hir_id) => Some(hir_id),
                        Res::Def(DefKind::Static { .. }, def_id) => {
                            if let Some(def_id) = def_id.as_local() {
                                let name =
                                    compile_util::def_id_to_value_symbol(def_id, self.tcx).unwrap();
                                let name = name.as_str();
                                if name != "stdin" && name != "stdout" && name != "stderr" {
                                    self.ctx
                                        .return_statics
                                        .entry(curr_func)
                                        .or_default()
                                        .insert(def_id);
                                }
                            }
                            None
                        }
                        _ => None,
                    }
                } else {
                    None
                };
                self.ctx
                    .return_locals
                    .entry(curr_func)
                    .or_default()
                    .insert(local);
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
fn find_field(field: Symbol, adt_def: AdtDef<'_>) -> Option<FieldIdx> {
    adt_def
        .variant(VariantIdx::from_u32(0))
        .fields
        .iter_enumerated()
        .find_map(|(i, f)| if f.name == field { Some(i) } else { None })
}

#[inline]
fn adt_of_expr<'tcx>(
    expr: &hir::Expr<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<(AdtDef<'tcx>, LocalDefId)> {
    let typeck = tcx.typeck(expr.hir_id.owner.def_id);
    let ty = typeck.expr_ty(expr);
    let TyKind::Adt(adt_def, _) = ty.kind() else { return None };
    Some((*adt_def, adt_def.did().as_local()?))
}

fn owned_def_id(ty: rustc_middle::ty::Ty<'_>) -> Option<LocalDefId> {
    match ty.kind() {
        TyKind::Adt(adt_def, _) => adt_def.did().as_local(),
        TyKind::Array(ty, _) => owned_def_id(*ty),
        _ => None,
    }
}
