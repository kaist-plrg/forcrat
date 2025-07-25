use std::ops::Deref as _;

use etrace::some_or;
use rustc_abi::{FieldIdx, FIRST_VARIANT};
use rustc_const_eval::interpret::{GlobalAlloc, Scalar};
use rustc_data_structures::graph::{scc::Sccs, DirectedGraph, Successors};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    def::{DefKind, Res},
    def_id::{DefId, LocalDefId},
    definitions::DefPathData,
    intravisit, HirId, ItemKind, Node,
};
use rustc_index::{bit_set::MixedBitSet, Idx, IndexVec};
use rustc_middle::{
    hir::nested_filter,
    mir::{
        AggregateKind, CastKind, Const, ConstOperand, ConstValue, Local, LocalDecl, Operand, Place,
        PlaceElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, UnevaluatedConst,
        RETURN_PLACE,
    },
    query::IntoQueryParam,
    ty::{adjustment::PointerCoercion, List, Ty, TyCtxt, TyKind},
};
use rustc_span::{source_map::Spanned, Span, Symbol};
use typed_arena::Arena;

use crate::{
    api_list::{def_id_api_kind, is_def_id_api, ApiKind, Origin, Permission},
    bit_set::{BitSet16, BitSet8},
    compile_util::{self, Pass},
    disjoint_set::DisjointSet,
    error_analysis::{self, ErrorPropagation, ExprLoc, Indicator},
    graph,
    likely_lit::LikelyLit,
    rustc_ast::visit::Visitor as _,
    rustc_index::bit_set::BitRelations,
};

#[derive(Debug)]
pub struct AnalysisResult<'a> {
    pub locs: IndexVec<LocId, Loc>,
    pub loc_ind_map: FxHashMap<Loc, LocId>,
    pub permissions: IndexVec<LocId, BitSet8<Permission>>,
    pub origins: IndexVec<LocId, BitSet8<Origin>>,
    pub unsupported: UnsupportedLocs,
    pub static_span_to_lit: FxHashMap<Span, Symbol>,
    pub defined_apis: FxHashSet<LocalDefId>,
    pub fn_ptrs: FxHashSet<LocalDefId>,
    pub tracking_fns: FxHashMap<LocalDefId, FxHashSet<(&'a ExprLoc, Indicator)>>,
    pub returning_fns: FxHashMap<LocalDefId, FxHashSet<(&'a ExprLoc, Indicator)>>,
    pub taking_fns: FxHashMap<LocalDefId, FxHashSet<(&'a ExprLoc, Indicator)>>,
    pub span_to_expr_loc: FxHashMap<Span, &'a ExprLoc>,
    pub propagations: FxHashSet<ErrorPropagation<'a>>,
    pub unsupported_stdout_errors: bool,
    pub unsupported_stderr_errors: bool,
    pub stat: Statistics,
}

#[derive(Debug)]
pub struct Statistics {
    pub error_visit_nums: Vec<usize>,
    pub error_analysis_time: u128,
    pub file_analysis_time: u128,
    pub solving_time: u128,
    pub loc_num: usize,
    pub unsupported_num: usize,
}

#[derive(Debug, Clone, Copy)]
pub struct FileAnalysis;

impl Pass for FileAnalysis {
    type Out = ();

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out {
        let arena = Arena::new();
        let result = analyze(&arena, tcx);
        println!("{result:#?}");
    }
}

pub fn analyze<'a>(arena: &'a Arena<ExprLoc>, tcx: TyCtxt<'_>) -> AnalysisResult<'a> {
    let start = std::time::Instant::now();
    let stolen = tcx.resolver_for_lowering().borrow();
    let (_, krate) = stolen.deref();
    let mut ast_visitor = AstVisitor::default();
    ast_visitor.visit_crate(krate);
    let static_span_to_lit = ast_visitor.static_span_to_lit;
    drop(stolen);

    let error_analysis = error_analysis::analyze(arena, tcx);
    let error_analysis_time = start.elapsed().as_millis();

    let start = std::time::Instant::now();
    let defined_apis = find_defined_apis(tcx);
    tracing::info!("Defined APIs:");
    for def_id in &defined_apis {
        tracing::info!("{:?}", def_id);
    }

    let mut locs: IndexVec<LocId, Loc> =
        IndexVec::from_raw(vec![Loc::Stdin, Loc::Stdout, Loc::Stderr]);

    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        let local_def_id = item.owner_id.def_id;
        let body = match item.kind {
            ItemKind::Fn { ident, .. } => {
                if defined_apis.contains(&local_def_id) || ident.name.as_str() == "main" {
                    continue;
                }
                tcx.optimized_mir(local_def_id)
            }
            ItemKind::Static(_, _, _, _) => tcx.mir_for_ctfe(local_def_id),
            ItemKind::Struct(ident, _, _) | ItemKind::Union(ident, _, _)
                if ident.as_str() != "_IO_FILE" =>
            {
                let adt_def = tcx.adt_def(item.owner_id);
                for (i, fd) in adt_def.variant(FIRST_VARIANT).fields.iter_enumerated() {
                    let ty = fd.ty(tcx, List::empty());
                    if compile_util::contains_file_ty(ty, tcx) {
                        locs.push(Loc::Field(local_def_id, i));
                    }
                }
                continue;
            }
            _ => continue,
        };
        for (i, local_decl) in body.local_decls.iter_enumerated() {
            if compile_util::contains_file_ty(local_decl.ty, tcx) {
                let loc = Loc::Var(local_def_id, i);
                locs.push(loc);
            }
        }
    }

    for (i, loc) in locs.iter_enumerated() {
        tracing::info!("{:?}: {:?}", i, loc);
    }
    let loc_ind_map: FxHashMap<_, _> = locs.iter_enumerated().map(|(i, l)| (*l, i)).collect();

    let permission_graph: Graph<LocId, Permission> = Graph::new(locs.len(), Permission::NUM);
    let mut origin_graph: Graph<LocId, Origin> = Graph::new(locs.len(), Origin::NUM);
    origin_graph.add_solution(loc_ind_map[&Loc::Stdin], Origin::Stdin);
    origin_graph.add_solution(loc_ind_map[&Loc::Stdout], Origin::Stdout);
    origin_graph.add_solution(loc_ind_map[&Loc::Stderr], Origin::Stderr);

    let arena = Arena::new();
    let mut analyzer = Analyzer {
        tcx,
        loc_ind_map: &loc_ind_map,
        fn_ptrs: FxHashSet::default(),
        permission_graph,
        origin_graph,
        unsupported: UnsupportedTracker::new(&arena, locs.len()),
    };

    for loc in &error_analysis.no_source_locs {
        let loc_id = loc_ind_map[loc];
        analyzer
            .unsupported
            .add(loc_id, UnsupportedReason::ErrorHandling);
    }

    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        let local_def_id = item.owner_id.def_id;
        let body = match item.kind {
            ItemKind::Fn { ident, .. } => {
                if defined_apis.contains(&local_def_id) || ident.name.as_str() == "main" {
                    continue;
                }
                tcx.optimized_mir(local_def_id)
            }
            ItemKind::Static(_, _, _, _) => tcx.mir_for_ctfe(local_def_id),
            _ => continue,
        };
        tracing::info!("{:?}", local_def_id);
        let ctx = Ctx {
            function: local_def_id,
            local_decls: &body.local_decls,
        };
        for bbd in body.basic_blocks.iter() {
            for stmt in &bbd.statements {
                tracing::info!("{:?}", stmt);
                analyzer.transfer_stmt(stmt, ctx);
            }
            tracing::info!("{:?}", bbd.terminator().kind);
            analyzer.transfer_term(bbd.terminator(), ctx);
        }
    }

    let graph = &analyzer.permission_graph;
    let sccs: Sccs<_, usize> = Sccs::new(&VecBitSet(&graph.edges));
    let mut components = vec![MixedBitSet::new_empty(locs.len()); sccs.num_sccs()];
    for i in graph.solutions.indices() {
        let scc = sccs.scc(i);
        components[scc.index()].insert(i);
    }
    let mut cycles = vec![];
    'l: for component in components {
        for i in component.iter() {
            for j in component.iter() {
                if i == j {
                    continue;
                }
                if graph.edges[i].contains(j) != graph.edges[j].contains(i) {
                    cycles.push(component);
                    continue 'l;
                }
            }
        }
    }

    let origin_edges = analyzer.origin_graph.edges.clone();

    let file_analysis_time = start.elapsed().as_millis();

    let start = std::time::Instant::now();
    let permissions = analyzer.permission_graph.solve();
    let mut origins = analyzer.origin_graph.solve();

    let origins_clone = origins.clone();
    for (loc_id, origins) in origins.iter_enumerated_mut() {
        if !origins.is_empty() {
            continue;
        }
        let mut new_origins: Option<BitSet8<Origin>> = None;
        for reachable in graph::bitset_reachable_vertices(&origin_edges, loc_id).iter() {
            let origins = origins_clone[reachable];
            if origins.is_empty() {
                continue;
            }
            if let Some(new_origins) = &mut new_origins {
                new_origins.intersect(&origins);
            } else {
                new_origins = Some(origins);
            }
        }
        if let Some(new_origins) = new_origins {
            assert!(!new_origins.is_empty());
            *origins = new_origins;
        }
    }

    for cycle in cycles {
        if cycle
            .iter()
            .any(|loc_id| permissions[loc_id].contains(Permission::Close))
        {
            for loc_id in cycle.iter() {
                analyzer
                    .unsupported
                    .add(loc_id, UnsupportedReason::CloseCycle);
            }
        }
    }

    for (((i, loc), permissions), origins) in locs.iter_enumerated().zip(&permissions).zip(&origins)
    {
        tracing::info!("{:?} {:?}: {:?}, {:?}", i, loc, permissions, origins);

        if permissions.contains(Permission::Seek)
            && (origins.contains(Origin::Stdin)
                || origins.contains(Origin::Stdout)
                || origins.contains(Origin::Stderr))
            || permissions.contains(Permission::Write) && origins.contains(Origin::Stdin)
            || permissions.contains(Permission::Read)
                && (origins.contains(Origin::Stdout) || origins.contains(Origin::Stderr))
        {
            analyzer.unsupported.add(i, UnsupportedReason::Permission);
        }
    }

    let stdout = analyzer.loc_ind_map[&Loc::Stdout];
    if analyzer.unsupported.unsupported.contains_key(&stdout) {
        analyzer.unsupported.unsupport_stdout(stdout);
    }
    let stderr = analyzer.loc_ind_map[&Loc::Stderr];
    if analyzer.unsupported.unsupported.contains_key(&stderr) {
        analyzer.unsupported.unsupport_stderr(stderr);
    }

    let unsupported = analyzer.unsupported.compute_all();
    for loc_id in unsupported.iter() {
        tracing::info!("{:?} unsupported", locs[loc_id]);
    }

    let mut tracking_fns: FxHashMap<_, FxHashSet<_>> = FxHashMap::default();
    let mut returning_fns: FxHashMap<_, FxHashSet<_>> = FxHashMap::default();
    let mut taking_fns: FxHashMap<_, FxHashSet<_>> = FxHashMap::default();
    let mut propagations = FxHashSet::default();
    let mut unsupported_stdout_errors = false;
    let mut unsupported_stderr_errors = false;

    for (loc, res) in error_analysis.loc_results {
        let loc_id = loc_ind_map[&loc];
        if unsupported.contains(loc_id) {
            if origins[loc_id].contains(Origin::Stdout) {
                unsupported_stdout_errors = true;
            }
            if origins[loc_id].contains(Origin::Stderr) {
                unsupported_stderr_errors = true;
            }
            continue;
        }
        for (func, locs) in res.tracking_fns {
            tracking_fns.entry(func).or_default().extend(locs);
        }
        for (func, locs) in res.returning_fns {
            returning_fns.entry(func).or_default().extend(locs);
        }
        for (func, locs) in res.taking_fns {
            taking_fns.entry(func).or_default().extend(locs);
        }
        propagations.extend(res.propagations);
    }

    for loc in &error_analysis.no_source_locs {
        let loc_id = loc_ind_map[loc];
        if origins[loc_id].contains(Origin::Stdout) {
            unsupported_stdout_errors = true;
        }
        if origins[loc_id].contains(Origin::Stderr) {
            unsupported_stderr_errors = true;
        }
    }

    let solving_time = start.elapsed().as_millis();

    let fn_ptrs = analyzer.fn_ptrs;
    let stat = Statistics {
        error_visit_nums: error_analysis.visit_nums,
        error_analysis_time,
        file_analysis_time,
        solving_time,
        loc_num: locs.len(),
        unsupported_num: unsupported.loc_to_root.len(),
    };

    AnalysisResult {
        locs,
        loc_ind_map,
        permissions,
        origins,
        unsupported,
        static_span_to_lit,
        defined_apis,
        fn_ptrs,
        tracking_fns,
        returning_fns,
        taking_fns,
        span_to_expr_loc: error_analysis.span_to_loc,
        propagations,
        unsupported_stdout_errors,
        unsupported_stderr_errors,
        stat,
    }
}

struct Analyzer<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    loc_ind_map: &'a FxHashMap<Loc, LocId>,
    fn_ptrs: FxHashSet<LocalDefId>,
    permission_graph: Graph<LocId, Permission>,
    origin_graph: Graph<LocId, Origin>,
    unsupported: UnsupportedTracker<'a>,
}

#[derive(Clone, Copy)]
struct Ctx<'a, 'tcx> {
    function: LocalDefId,
    local_decls: &'a IndexVec<Local, LocalDecl<'tcx>>,
}

impl<'tcx> Analyzer<'_, 'tcx> {
    fn transfer_stmt(&mut self, stmt: &Statement<'tcx>, ctx: Ctx<'_, 'tcx>) {
        let StatementKind::Assign(box (l, r)) = &stmt.kind else { return };
        let ty = l.ty(ctx.local_decls, self.tcx).ty;
        let variance = file_type_variance(ty, self.tcx);
        match r {
            Rvalue::Cast(CastKind::PtrToPtr | CastKind::Transmute, op, _) => {
                let rty = op.ty(ctx.local_decls, self.tcx);
                match (variance, compile_util::contains_file_ty(rty, self.tcx)) {
                    (Some(variance), true) => {
                        let l = self.transfer_place(*l, ctx);
                        let r = self.transfer_operand(op, ctx);
                        self.assign(l, r, variance);
                    }
                    (Some(_), false) => {
                        let l = self.transfer_place(*l, ctx);
                        self.unsupported.add(l, UnsupportedReason::Cast);
                    }
                    (None, true) => {
                        let r = self.transfer_operand(op, ctx);
                        self.unsupported.add(r, UnsupportedReason::Cast);
                    }
                    (None, false) => {}
                }
            }
            Rvalue::Cast(CastKind::PointerWithExposedProvenance, op, _) => {
                if variance.is_some() {
                    let l = self.transfer_place(*l, ctx);
                    if let Operand::Constant(box ConstOperand {
                        const_: Const::Val(ConstValue::Scalar(Scalar::Int(i)), _),
                        ..
                    }) = op
                    {
                        if i.to_int(i.size()) != 0 {
                            self.unsupported.add(l, UnsupportedReason::Cast);
                        }
                    } else {
                        self.unsupported.add(l, UnsupportedReason::Cast);
                    }
                }
            }
            Rvalue::Cast(CastKind::PointerExposeProvenance, op, _) => {
                let rty = op.ty(ctx.local_decls, self.tcx);
                if compile_util::contains_file_ty(rty, self.tcx) {
                    let r = self.transfer_operand(op, ctx);
                    self.unsupported.add(r, UnsupportedReason::Cast);
                }
            }
            Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer, _), op, _) => {
                if let Some(variance) = variance {
                    let Const::Val(value, ty) = op.constant().unwrap().const_ else { panic!() };
                    assert_eq!(value, ConstValue::ZeroSized);
                    let TyKind::FnDef(def_id, _) = ty.kind() else { panic!() };
                    let def_id = def_id.expect_local();
                    let sig = self.tcx.fn_sig(def_id).skip_binder().skip_binder();
                    let l = self.transfer_place(*l, ctx);
                    for (i, ty) in sig.inputs().iter().enumerate() {
                        if compile_util::contains_file_ty(*ty, self.tcx) {
                            let node = self.tcx.hir_node_by_def_id(def_id);
                            if matches!(node, Node::ForeignItem(_)) {
                                self.unsupported.add(l, UnsupportedReason::ApiFnPtr);
                            } else {
                                let r = Loc::Var(def_id, Local::new(i + 1));
                                let r = self.loc_ind_map[&r];
                                self.assign(l, r, variance);
                                self.fn_ptrs.insert(def_id);
                            }
                        }
                    }
                }
            }
            Rvalue::Cast(kind, op, _) => {
                assert!(variance.is_none(), "{:?} {:?}", kind, stmt.source_info.span);
                let rty = op.ty(ctx.local_decls, self.tcx);
                assert!(
                    !compile_util::contains_file_ty(rty, self.tcx),
                    "{:?} {:?}",
                    kind,
                    stmt.source_info.span
                );
            }
            Rvalue::BinaryOp(_, box (op1, op2)) => {
                let ty = op1.ty(ctx.local_decls, self.tcx);
                if compile_util::contains_file_ty(ty, self.tcx) {
                    let op1 = self.transfer_operand(op1, ctx);
                    self.unsupported.add(op1, UnsupportedReason::Cmp);
                    let op2 = self.transfer_operand(op2, ctx);
                    self.unsupported.add(op2, UnsupportedReason::Cmp);
                }
            }
            Rvalue::Aggregate(box AggregateKind::Adt(def_id, _, _, _, field_idx), fields) => {
                if compile_util::is_option_ty(def_id, self.tcx) {
                    if !fields.is_empty()
                        && let Some(variance) = variance
                    {
                        let l = self.transfer_place(*l, ctx);
                        let [f] = &fields.as_slice().raw else { panic!() };
                        let r = self.transfer_operand(f, ctx);
                        self.assign(l, r, variance);
                    }
                } else {
                    assert!(variance.is_none());
                    if self.tcx.adt_def(def_id).is_union() {
                        let f = &fields[FieldIdx::from_u32(0)];
                        let ty = f.ty(ctx.local_decls, self.tcx);
                        if let Some(variance) = file_type_variance(ty, self.tcx) {
                            let l = Loc::Field(def_id.expect_local(), field_idx.unwrap());
                            let l = self.loc_ind_map[&l];
                            let r = self.transfer_operand(f, ctx);
                            self.assign(l, r, variance);
                        }
                    } else {
                        for (idx, f) in fields.iter_enumerated() {
                            let ty = f.ty(ctx.local_decls, self.tcx);
                            if let Some(variance) = file_type_variance(ty, self.tcx) {
                                let l = Loc::Field(def_id.expect_local(), idx);
                                let l = self.loc_ind_map[&l];
                                let r = self.transfer_operand(f, ctx);
                                self.assign(l, r, variance);
                            }
                        }
                    }
                }
            }
            _ => {
                let variance = some_or!(variance, return);
                let l = self.transfer_place(*l, ctx);
                match r {
                    Rvalue::Use(op) | Rvalue::Repeat(op, _) => {
                        if !matches!(
                            op,
                            Operand::Constant(box ConstOperand {
                                const_:
                                    Const::Unevaluated(
                                        UnevaluatedConst {
                                            promoted: Some(_), ..
                                        },
                                        _,
                                    ),
                                ..
                            })
                        ) {
                            let r = self.transfer_operand(op, ctx);
                            self.assign(l, r, variance);
                        }
                    }
                    Rvalue::Cast(_, _, _) => unreachable!(),
                    Rvalue::Ref(_, _, place)
                    | Rvalue::RawPtr(_, place)
                    | Rvalue::CopyForDeref(place) => {
                        let r = self.transfer_place(*place, ctx);
                        self.assign(l, r, variance);
                    }
                    Rvalue::Aggregate(box kind, fields) => {
                        assert!(matches!(kind, AggregateKind::Array(_)));
                        for f in fields {
                            let r = self.transfer_operand(f, ctx);
                            self.assign(l, r, variance);
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    fn transfer_operand(&self, operand: &Operand<'tcx>, ctx: Ctx<'_, 'tcx>) -> LocId {
        match operand {
            Operand::Copy(p) | Operand::Move(p) => self.transfer_place(*p, ctx),
            Operand::Constant(box c) => self.transfer_constant(*c),
        }
    }

    fn transfer_place(&self, place: Place<'tcx>, ctx: Ctx<'_, 'tcx>) -> LocId {
        let loc = if let Some((init, f)) = strip_index_projection(place.projection) {
            let ty = Place::ty_from(place.local, init, ctx.local_decls, self.tcx).ty;
            let def_id = ty.ty_adt_def().unwrap().did().expect_local();
            Loc::Field(def_id, f)
        } else {
            Loc::Var(ctx.function, place.local)
        };
        self.loc_ind_map[&loc]
    }

    fn transfer_constant(&self, constant: ConstOperand<'tcx>) -> LocId {
        let Const::Val(value, _) = constant.const_ else { panic!() };
        let ConstValue::Scalar(scalar) = value else { panic!() };
        let Scalar::Ptr(ptr, _) = scalar else { panic!() };
        let GlobalAlloc::Static(def_id) = self.tcx.global_alloc(ptr.provenance.alloc_id()) else {
            panic!()
        };
        let def_id = def_id.expect_local();
        let node = self.tcx.hir_node_by_def_id(def_id);
        let loc = if matches!(node, Node::ForeignItem(_)) {
            let key = self.tcx.def_key(def_id);
            let DefPathData::ValueNs(name) = key.disambiguated_data.data else { panic!() };
            match name.as_str() {
                "stdin" => Loc::Stdin,
                "stdout" => Loc::Stdout,
                "stderr" => Loc::Stderr,
                x => panic!("{}", x),
            }
        } else {
            Loc::Var(def_id, RETURN_PLACE)
        };
        self.loc_ind_map[&loc]
    }

    fn transfer_term(&mut self, term: &Terminator<'tcx>, ctx: Ctx<'_, 'tcx>) {
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &term.kind
        else {
            return;
        };
        assert!(!destination.is_indirect_first_projection());
        match func {
            Operand::Copy(callee) | Operand::Move(callee) => {
                assert!(callee.projection.is_empty());
                let ty = callee.ty(ctx.local_decls, self.tcx).ty;
                let TyKind::FnPtr(binder, _) = ty.kind() else { panic!() };
                let arity = binder.as_ref().skip_binder().inputs().len();
                for (i, arg) in args.iter().enumerate() {
                    let ty = arg.node.ty(ctx.local_decls, self.tcx);
                    if i < arity {
                        if let Some(variance) = file_type_variance(ty, self.tcx) {
                            let l = Loc::Var(ctx.function, callee.local);
                            let l = self.loc_ind_map[&l];
                            let r = self.transfer_operand(&arg.node, ctx);
                            self.assign(l, r, variance);
                        }
                    } else if compile_util::contains_file_ty(ty, self.tcx) {
                        let arg = self.transfer_operand(&arg.node, ctx);
                        self.unsupported.add(arg, UnsupportedReason::Variadic);
                    }
                }
            }
            Operand::Constant(box constant) => {
                let Const::Val(value, ty) = constant.const_ else { unreachable!() };
                assert!(matches!(value, ConstValue::ZeroSized));
                let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                if let Some(kind) = def_id_api_kind(def_id, self.tcx) {
                    match kind {
                        ApiKind::Open(origin) => {
                            let x = self.transfer_place(*destination, ctx);
                            self.add_origin(x, origin);
                        }
                        ApiKind::NonPosixOpen => {
                            let x = self.transfer_place(*destination, ctx);
                            self.unsupported.add(x, UnsupportedReason::NonPosix);
                        }
                        ApiKind::Operation(Some(permission)) => {
                            let sig = self.tcx.fn_sig(def_id).skip_binder().skip_binder();
                            for (t, arg) in sig.inputs().iter().zip(args) {
                                if compile_util::contains_file_ty(*t, self.tcx) {
                                    let x = self.transfer_operand(&arg.node, ctx);
                                    self.add_permission(x, permission);
                                    break;
                                }
                            }
                        }
                        ApiKind::Unsupported | ApiKind::NonPosix => {
                            let name =
                                compile_util::def_id_to_value_symbol(def_id, self.tcx).unwrap();
                            let reason = match name.as_str() {
                                "setbuf" | "setvbuf" => UnsupportedReason::Setbuf,
                                "ungetc" => UnsupportedReason::Ungetc,
                                "freopen" => UnsupportedReason::Freopen,
                                _ => UnsupportedReason::NonPosix,
                            };
                            let sig = self.tcx.fn_sig(def_id).skip_binder().skip_binder();
                            for (t, arg) in sig.inputs().iter().zip(args) {
                                if compile_util::contains_file_ty(*t, self.tcx) {
                                    let x = self.transfer_operand(&arg.node, ctx);
                                    self.unsupported.add(x, reason);
                                    break;
                                }
                            }
                        }
                        ApiKind::Operation(None)
                        | ApiKind::StdioOperation
                        | ApiKind::FileSysOperation
                        | ApiKind::FileDescrOperation
                        | ApiKind::StringOperation => {}
                    }
                } else if let Some(callee) = def_id.as_local() {
                    self.transfer_non_api_call(callee, args, *destination, ctx);
                } else {
                    let name = compile_util::def_id_to_value_symbol(def_id, self.tcx).unwrap();
                    match name.as_str() {
                        "arg" => {
                            let ty = Place::ty(destination, ctx.local_decls, self.tcx).ty;
                            if compile_util::contains_file_ty(ty, self.tcx) {
                                let x = self.transfer_place(*destination, ctx);
                                self.unsupported.add(x, UnsupportedReason::Variadic);
                            }
                        }
                        "unwrap" => {
                            let ty = Place::ty(destination, ctx.local_decls, self.tcx).ty;
                            if let Some(variance) = file_type_variance(ty, self.tcx) {
                                let l = self.transfer_place(*destination, ctx);
                                let r = self.transfer_operand(&args[0].node, ctx);
                                self.assign(l, r, variance);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    fn transfer_non_api_call(
        &mut self,
        callee: LocalDefId,
        args: &[Spanned<Operand<'tcx>>],
        destination: Place<'tcx>,
        ctx: Ctx<'_, 'tcx>,
    ) {
        let sig = self.tcx.fn_sig(callee).skip_binder().skip_binder();
        let arity = sig.inputs().len();
        for (i, arg) in args.iter().enumerate() {
            let ty = arg.node.ty(ctx.local_decls, self.tcx);
            if i < arity {
                if let Some(variance) = file_type_variance(ty, self.tcx) {
                    let l = Loc::Var(callee, Local::new(i + 1));
                    let l = self.loc_ind_map[&l];
                    let r = self.transfer_operand(&arg.node, ctx);
                    self.assign(l, r, variance);
                }
            } else if compile_util::contains_file_ty(ty, self.tcx) {
                let arg = self.transfer_operand(&arg.node, ctx);
                self.unsupported.add(arg, UnsupportedReason::Variadic);
            }
        }
        if let Some(variance) = file_type_variance(sig.output(), self.tcx) {
            let l = self.transfer_place(destination, ctx);
            let r = Loc::Var(callee, RETURN_PLACE);
            let r = self.loc_ind_map[&r];
            self.assign(l, r, variance);
        }
    }

    #[inline]
    fn add_permission(&mut self, loc: LocId, permission: Permission) {
        tracing::info!("{:?} {:?}", loc, permission);
        self.permission_graph.add_solution(loc, permission);
    }

    #[inline]
    fn add_origin(&mut self, loc: LocId, origin: Origin) {
        tracing::info!("{:?} {:?}", loc, origin);
        self.origin_graph.add_solution(loc, origin);
    }

    #[inline]
    fn assign(&mut self, lhs: LocId, rhs: LocId, v: Variance) {
        tracing::info!("{:?} := {:?} {:?}", lhs, rhs, v);
        match v {
            Variance::Covariant => {
                self.permission_graph.add_edge(lhs, rhs);
                self.origin_graph.add_edge(rhs, lhs);
            }
            Variance::Invariant => {
                self.permission_graph.add_edge(lhs, rhs);
                self.permission_graph.add_edge(rhs, lhs);
                self.origin_graph.add_edge(lhs, rhs);
                self.origin_graph.add_edge(rhs, lhs);
            }
        }

        let stdout = self.loc_ind_map[&Loc::Stdout];
        let stderr = self.loc_ind_map[&Loc::Stderr];
        if lhs == stdout {
            self.unsupported.stdout_locs.insert(rhs);
        } else if rhs == stdout {
            self.unsupported.stdout_locs.insert(lhs);
        } else if lhs == stderr {
            self.unsupported.stderr_locs.insert(rhs);
        } else if rhs == stderr {
            self.unsupported.stderr_locs.insert(lhs);
        } else {
            self.unsupported.union(lhs, rhs);
        }
    }
}

fn strip_index_projection<'a, 'tcx>(
    projection: &'a [PlaceElem<'tcx>],
) -> Option<(&'a [PlaceElem<'tcx>], FieldIdx)> {
    if projection.is_empty() {
        return None;
    }
    let (last, init) = projection.split_last().unwrap();
    match last {
        PlaceElem::Deref => {
            assert!(init.is_empty());
            None
        }
        PlaceElem::Field(f, _) => Some((init, *f)),
        PlaceElem::Index(_) => strip_index_projection(init),
        _ => panic!("{projection:?}"),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Variance {
    Covariant,
    Invariant,
}

fn file_type_variance<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Option<Variance> {
    let v = match ty.kind() {
        TyKind::RawPtr(ty, mutbl) | TyKind::Ref(_, ty, mutbl) => {
            if let TyKind::Adt(adt_def, _) = ty.kind()
                && compile_util::is_file_ty(adt_def.did(), tcx)
            {
                return Some(Variance::Covariant);
            }
            let v = file_type_variance(*ty, tcx)?;
            if mutbl.is_not() {
                Some(v)
            } else {
                Some(Variance::Invariant)
            }
        }
        TyKind::Array(ty, _) | TyKind::Slice(ty) => file_type_variance(*ty, tcx),
        TyKind::Adt(adt_def, targs) => {
            if compile_util::is_option_ty(adt_def.did(), tcx) {
                let targs = targs.into_type_list(tcx);
                file_type_variance(targs[0], tcx)
            } else {
                None
            }
        }
        TyKind::FnPtr(binder, _) => binder
            .as_ref()
            .skip_binder()
            .inputs()
            .iter()
            // use invariance instead of contravariance
            // because fn(A) cannot be coerced to fn(B) if A != B
            .find_map(|ty| file_type_variance(*ty, tcx).map(|_| Variance::Invariant)),
        _ => None,
    };
    assert_eq!(
        v.is_some(),
        compile_util::contains_file_ty(ty, tcx),
        "{ty:?}"
    );
    v
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Loc {
    Stdin,
    Stdout,
    Stderr,
    Var(LocalDefId, Local),
    Field(LocalDefId, FieldIdx),
}

fn fmt_def_id(
    f: &mut std::fmt::Formatter<'_>,
    key: impl IntoQueryParam<DefId>,
) -> std::fmt::Result {
    let def_id = key.into_query_param();
    rustc_middle::ty::tls::with_opt(|opt_tcx| {
        if let Some(tcx) = opt_tcx {
            write!(f, "{}", tcx.def_path_str(def_id))
        } else {
            write!(f, "{}", def_id.index.index())
        }
    })
}

impl std::fmt::Debug for Loc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Loc::Stdin => write!(f, "stdin"),
            Loc::Stdout => write!(f, "stdout"),
            Loc::Stderr => write!(f, "stderr"),
            Loc::Var(def_id, local) => {
                fmt_def_id(f, *def_id)?;
                write!(f, ":{}", local.index())
            }
            Loc::Field(def_id, field) => {
                fmt_def_id(f, *def_id)?;
                write!(f, ".{}", field.index())
            }
        }
    }
}

rustc_index::newtype_index! {
    #[debug_format = "L{}"]
    pub struct LocId {}
}

struct Graph<V: Idx, T: Idx> {
    tok_num: usize,
    solutions: IndexVec<V, BitSet8<T>>,
    edges: IndexVec<V, MixedBitSet<V>>,
}

impl<V: Idx, T: Idx> Graph<V, T> {
    #[inline]
    fn new(size: usize, tok_num: usize) -> Self {
        assert!(tok_num <= 8);
        Self {
            tok_num,
            solutions: IndexVec::from_raw(vec![BitSet8::new_empty(); size]),
            edges: IndexVec::from_raw(vec![MixedBitSet::new_empty(size); size]),
        }
    }

    #[inline]
    fn add_solution(&mut self, v: V, t: T) {
        self.solutions[v].insert(t);
    }

    #[inline]
    fn add_edge(&mut self, from: V, to: V) {
        self.edges[from].insert(to);
    }

    fn solve(self) -> IndexVec<V, BitSet8<T>> {
        let Self {
            tok_num,
            mut solutions,
            mut edges,
        } = self;
        let size = solutions.len();

        let mut deltas = solutions.clone();
        let mut id_to_rep: IndexVec<V, _> = IndexVec::from_raw((0..size).map(V::new).collect());

        while deltas.iter().any(|s| !s.is_empty()) {
            let sccs: Sccs<_, usize> = Sccs::new(&VecBitSet(&edges));

            let mut components = vec![MixedBitSet::new_empty(size); sccs.num_sccs()];
            for i in solutions.indices() {
                let scc = sccs.scc(i);
                components[scc.index()].insert(i);
            }

            let mut scc_to_rep = vec![];
            let mut cycles = vec![];
            let mut new_id_to_rep = FxHashMap::default();
            for component in components.iter() {
                let rep = component.iter().next().unwrap();
                scc_to_rep.push(rep);
                if contains_multiple(component) {
                    cycles.push((rep, component));
                    for id in component.iter() {
                        if id != rep {
                            new_id_to_rep.insert(id, rep);
                        }
                    }
                }
            }

            let mut po = vec![];
            for scc in sccs.all_sccs() {
                po.push(scc_to_rep[scc]);
            }

            if sccs.num_sccs() != size {
                // update id_to_rep
                for rep in &mut id_to_rep {
                    if let Some(new_rep) = new_id_to_rep.get(rep) {
                        *rep = *new_rep;
                    }
                }

                // update deltas
                for (rep, ids) in &cycles {
                    for id in ids.iter() {
                        if *rep != id {
                            let set = std::mem::take(&mut deltas[id]);
                            deltas[*rep].union(&set);
                        }
                    }
                }

                // update solutions
                for (rep, ids) in &cycles {
                    let mut intersection = BitSet8::new_empty();
                    intersection.insert_all(tok_num as _);
                    for id in ids.iter() {
                        intersection.intersect(&solutions[id]);
                        if *rep != id {
                            let set = std::mem::take(&mut solutions[id]);
                            solutions[*rep].union(&set);
                        }
                    }
                    let mut union = solutions[*rep];
                    union.subtract(&intersection);
                    deltas[*rep].union(&union);
                }

                // update edges
                edges = IndexVec::from_raw(vec![MixedBitSet::new_empty(size); size]);
                for (scc, rep) in scc_to_rep.iter().enumerate() {
                    let succs = &mut edges[*rep];
                    for succ in sccs.successors(scc) {
                        succs.insert(scc_to_rep[*succ]);
                    }
                }
            }

            for v in po.into_iter().rev() {
                if deltas[v].is_empty() {
                    continue;
                }
                let delta = std::mem::take(&mut deltas[v]);

                for l in edges[v].iter() {
                    if l == v {
                        continue;
                    }
                    for f in delta.iter() {
                        if solutions[l].insert(f) {
                            deltas[l].insert(f);
                        }
                    }
                }
            }
        }

        for (id, rep) in id_to_rep.iter_enumerated() {
            if id != *rep {
                solutions[id] = solutions[*rep];
            }
        }

        solutions
    }
}

#[inline]
fn contains_multiple<T: Idx>(set: &MixedBitSet<T>) -> bool {
    let mut iter = set.iter();
    iter.next().is_some() && iter.next().is_some()
}

#[repr(transparent)]
struct VecBitSet<'a, T: Idx>(&'a IndexVec<T, MixedBitSet<T>>);

impl<T: Idx> DirectedGraph for VecBitSet<'_, T> {
    type Node = T;

    fn num_nodes(&self) -> usize {
        self.0.len()
    }
}

impl<T: Idx> Successors for VecBitSet<'_, T> {
    fn successors(&self, node: T) -> impl Iterator<Item = Self::Node> {
        self.0[node].iter()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum UnsupportedReason {
    Setbuf = 0,
    Ungetc = 1,
    Freopen = 2,
    ErrorHandling = 3,
    CloseCycle = 4,
    Permission = 5,
    Cast = 6,
    Variadic = 7,
    ApiFnPtr = 8,
    Cmp = 9,
    NonPosix = 10,
}

impl UnsupportedReason {
    pub const NUM: usize = 11;
}

impl Idx for UnsupportedReason {
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

struct UnsupportedTracker<'a> {
    arena: &'a Arena<DisjointSet<'a, LocId>>,
    locs: FxHashMap<LocId, &'a DisjointSet<'a, LocId>>,
    unsupported: FxHashMap<LocId, BitSet16<UnsupportedReason>>,

    stdout_locs: MixedBitSet<LocId>,
    stderr_locs: MixedBitSet<LocId>,
}

impl<'a> UnsupportedTracker<'a> {
    fn new(arena: &'a Arena<DisjointSet<'a, LocId>>, len: usize) -> Self {
        Self {
            arena,
            locs: FxHashMap::default(),
            unsupported: FxHashMap::default(),

            stdout_locs: MixedBitSet::new_empty(len),
            stderr_locs: MixedBitSet::new_empty(len),
        }
    }

    fn union(&mut self, loc1: LocId, loc2: LocId) {
        let loc1 = *self
            .locs
            .entry(loc1)
            .or_insert_with(|| self.arena.alloc(DisjointSet::new(loc1)));
        let loc2 = *self
            .locs
            .entry(loc2)
            .or_insert_with(|| self.arena.alloc(DisjointSet::new(loc2)));
        if loc1.find_set() != loc2.find_set() {
            loc1.union(loc2);
        }
    }

    fn add(&mut self, loc: LocId, reason: UnsupportedReason) {
        self.locs
            .entry(loc)
            .or_insert_with(|| self.arena.alloc(DisjointSet::new(loc)));
        self.unsupported.entry(loc).or_default().insert(reason);
    }

    fn unsupport_stdout(&mut self, stdout: LocId) {
        let v: Vec<_> = self.stdout_locs.iter().collect();
        for loc in v {
            self.union(stdout, loc);
        }
    }

    fn unsupport_stderr(&mut self, stderr: LocId) {
        let v: Vec<_> = self.stderr_locs.iter().collect();
        for loc in v {
            self.union(stderr, loc);
        }
    }

    fn compute_all(&self) -> UnsupportedLocs {
        let mut loc_to_root = FxHashMap::default();
        let mut reasons: FxHashMap<_, BitSet16<_>> = FxHashMap::default();
        for (loc_id, r) in &self.unsupported {
            let root = self.locs[loc_id].find_set().id();
            loc_to_root.insert(root, root);
            reasons.entry(root).or_default().union(r);
        }
        for (loc, set) in &self.locs {
            let root = set.find_set().id();
            if loc_to_root.contains_key(&root) {
                loc_to_root.insert(*loc, root);
            }
        }
        UnsupportedLocs {
            loc_to_root,
            reasons,
        }
    }
}

#[derive(Debug)]
pub struct UnsupportedLocs {
    loc_to_root: FxHashMap<LocId, LocId>,
    reasons: FxHashMap<LocId, BitSet16<UnsupportedReason>>,
}

impl UnsupportedLocs {
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = LocId> + '_ {
        self.loc_to_root.keys().copied()
    }

    #[inline]
    pub fn contains(&self, loc: LocId) -> bool {
        self.loc_to_root.contains_key(&loc)
    }

    #[inline]
    pub fn get_reasons(&self, loc: LocId) -> BitSet16<UnsupportedReason> {
        self.reasons[&self.loc_to_root[&loc]]
    }
}

#[derive(Default)]
struct AstVisitor {
    /// static ident span to its literal
    static_span_to_lit: FxHashMap<Span, Symbol>,
}

impl rustc_ast::visit::Visitor<'_> for AstVisitor {
    fn visit_item(&mut self, item: &rustc_ast::Item) {
        rustc_ast::visit::walk_item(self, item);

        let rustc_ast::ItemKind::Static(box rustc_ast::StaticItem {
            ident,
            expr: Some(expr),
            ..
        }) = &item.kind
        else {
            return;
        };
        if let LikelyLit::Lit(lit) = LikelyLit::from_expr(expr) {
            self.static_span_to_lit.insert(ident.span, lit);
        }
    }
}

pub fn find_defined_apis(tcx: TyCtxt<'_>) -> FxHashSet<LocalDefId> {
    let mut visitor = HirVisitor::new(tcx);
    tcx.hir_visit_all_item_likes_in_crate(&mut visitor);

    let mut defined_apis = FxHashSet::default();
    let mut worklist = visitor.defined_apis;
    while let Some(def_id) = worklist.pop() {
        if !defined_apis.insert(def_id) {
            continue;
        }
        let callees = some_or!(visitor.dependencies.get(&def_id), continue);
        for def_id in callees {
            worklist.push(*def_id);
        }
    }

    defined_apis
}

struct HirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    defined_apis: Vec<LocalDefId>,
    dependencies: FxHashMap<LocalDefId, Vec<LocalDefId>>,
}

impl<'tcx> HirVisitor<'tcx> {
    #[inline]
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            defined_apis: vec![],
            dependencies: FxHashMap::default(),
        }
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for HirVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx rustc_hir::Item<'tcx>) {
        intravisit::walk_item(self, item);

        if matches!(item.kind, ItemKind::Fn { .. }) {
            let def_id = item.owner_id.def_id;
            if is_def_id_api(def_id, self.tcx) {
                self.defined_apis.push(def_id);
            }
        }
    }

    fn visit_path(&mut self, path: &rustc_hir::Path<'tcx>, hir_id: HirId) {
        intravisit::walk_path(self, path);

        let Res::Def(kind, def_id) = path.res else { return };
        let def_id = some_or!(def_id.as_local(), return);
        if kind == DefKind::Fn {
            self.dependencies
                .entry(hir_id.owner.def_id)
                .or_default()
                .push(def_id);
        }
    }
}
