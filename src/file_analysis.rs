use std::{collections::hash_map::Entry, ops::Deref as _};

use etrace::some_or;
use rustc_abi::{FieldIdx, FIRST_VARIANT};
use rustc_const_eval::interpret::{ConstValue, GlobalAlloc, Scalar};
use rustc_data_structures::graph::{
    scc::Sccs, DirectedGraph, GraphSuccessors, WithNumNodes, WithSuccessors,
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    definitions::DefPathData,
    ItemKind, Node,
};
use rustc_index::{
    bit_set::{HybridBitSet, HybridIter},
    Idx, IndexVec,
};
use rustc_middle::{
    mir::{
        AggregateKind, CastKind, Constant, ConstantKind, Local, LocalDecl, Operand, Place,
        ProjectionElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, RETURN_PLACE,
    },
    query::{IntoQueryParam, Key},
    ty::{List, Ty, TyCtxt, TyKind, TypeAndMut},
};
use rustc_span::Span;
use typed_arena::Arena;

use crate::{
    api_list::{def_id_api_kind, is_def_id_api, is_symbol_api, ApiKind, Origin, Permission},
    bit_set::BitSet8,
    compile_util::{contains_file_ty, is_file_ty, Pass},
    disjoint_set::DisjointSet,
    rustc_ast::visit::Visitor as _,
    rustc_index::bit_set::BitRelations,
    steensgaard,
    transformation::LikelyLit,
};

#[derive(Debug)]
pub struct AnalysisResult {
    pub locs: IndexVec<LocId, Loc>,
    pub loc_ind_map: FxHashMap<Loc, LocId>,
    pub permissions: IndexVec<LocId, BitSet8<Permission>>,
    pub origins: IndexVec<LocId, BitSet8<Origin>>,
    pub unsupported: HybridBitSet<LocId>,
}

#[derive(Debug, Clone, Copy)]
pub struct FileAnalysis;

impl Pass for FileAnalysis {
    type Out = AnalysisResult;

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out {
        let krate = tcx.resolver_for_lowering(());
        let krate_ref = krate.borrow();
        let (_, krate) = krate_ref.deref();
        let mut ast_visitor = AstVisitor::default();
        ast_visitor.visit_crate(krate);
        let popen_read: FxHashMap<_, _> = ast_visitor
            .popen_args
            .into_iter()
            .filter_map(|(span, arg)| match arg {
                LikelyLit::Lit(lit) => match &lit.as_str()[..1] {
                    "r" => Some((span, true)),
                    "w" => Some((span, false)),
                    _ => panic!("{:?}", lit),
                },
                LikelyLit::If(_, _, _) => todo!(),
                LikelyLit::Path(_, _) => todo!(),
                LikelyLit::Other(_) => todo!(),
            })
            .collect();
        drop(krate_ref);

        let steensgaard = steensgaard::Steensgaard.run(tcx);
        tracing::info!("\n{:?}", steensgaard);
        let hir = tcx.hir();

        // let mut visitor = StdioArgVisitor::new(tcx);
        // hir.visit_all_item_likes_in_crate(&mut visitor);
        // let stdio_args = visitor.stdio_args;
        // for span in &stdio_args {
        //     tracing::info!("{:?}", span);
        // }

        // let mut stdio_arg_locs: FxHashSet<Loc> = FxHashSet::default();
        let mut fn_ty_functions: FxHashMap<steensgaard::FnId, Vec<LocalDefId>> =
            FxHashMap::default();
        let mut locs: IndexVec<LocId, Loc> =
            IndexVec::from_raw(vec![Loc::Stdin, Loc::Stdout, Loc::Stderr]);

        for item_id in hir.items() {
            let item = hir.item(item_id);
            let local_def_id = item.owner_id.def_id;
            let body = match item.kind {
                ItemKind::Fn(_, _, _) => {
                    if is_symbol_api(item.ident.name) || item.ident.name.as_str() == "main" {
                        continue;
                    }
                    let ty = steensgaard.var_ty(steensgaard.global(local_def_id));
                    fn_ty_functions
                        .entry(ty.fn_ty)
                        .or_default()
                        .push(local_def_id);
                    tcx.optimized_mir(local_def_id)
                }
                ItemKind::Static(_, _, _) => tcx.mir_for_ctfe(local_def_id),
                ItemKind::Struct(_, _) | ItemKind::Union(_, _)
                    if item.ident.as_str() != "_IO_FILE" =>
                {
                    let adt_def = tcx.adt_def(item.owner_id);
                    for (i, fd) in adt_def.variant(FIRST_VARIANT).fields.iter_enumerated() {
                        let ty = fd.ty(tcx, List::empty());
                        if contains_file_ty(ty, tcx) {
                            locs.push(Loc::Field(local_def_id, i));
                        }
                    }
                    continue;
                }
                _ => continue,
            };
            // for bbd in body.basic_blocks.iter() {
            //     for stmt in &bbd.statements {
            //         if stdio_args.contains(&stmt.source_info.span) {
            //             let StatementKind::Assign(box (l, _)) = stmt.kind else { continue };
            //             assert!(l.projection.is_empty());
            //             stdio_arg_locs.insert(Loc::Var(local_def_id, l.local));
            //         }
            //     }
            // }
            for (i, local_decl) in body.local_decls.iter_enumerated() {
                if contains_file_ty(local_decl.ty, tcx) {
                    let loc = Loc::Var(local_def_id, i);
                    locs.push(loc);
                    // if !stdio_arg_locs.contains(&loc) {
                    //     locs.push(loc);
                    // }
                }
            }
        }

        for (i, fs) in &fn_ty_functions {
            tracing::info!("{:?}: {:?}", i, fs);
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
            popen_read,
            steensgaard: &steensgaard,
            fn_ty_functions,
            // stdio_arg_locs,
            loc_ind_map: &loc_ind_map,
            permission_graph,
            origin_graph,
            unsupported: UnsupportedTracker::new(&arena),
        };

        for item_id in hir.items() {
            let item = hir.item(item_id);
            let local_def_id = item.owner_id.def_id;
            let body = match item.kind {
                ItemKind::Fn(_, _, _) => {
                    if is_symbol_api(item.ident.name) || item.ident.name.as_str() == "main" {
                        continue;
                    }
                    tcx.optimized_mir(local_def_id)
                }
                ItemKind::Static(_, _, _) => tcx.mir_for_ctfe(local_def_id),
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

        let permissions = analyzer.permission_graph.solve();
        let origins = analyzer.origin_graph.solve();

        for (((i, loc), permissions), origins) in
            locs.iter_enumerated().zip(&permissions).zip(&origins)
        {
            tracing::info!("{:?} {:?}: {:?}, {:?}", i, loc, permissions, origins);
        }

        let unsupported = analyzer.unsupported.compute_all(locs.len());
        if unsupported.is_empty() {
            tracing::info!("No unsupported locations");
        } else {
            tracing::info!("Unsupported locations:");
        }
        for loc_id in unsupported.iter() {
            tracing::info!("{:?}", locs[loc_id]);
        }

        AnalysisResult {
            locs,
            loc_ind_map,
            permissions,
            origins,
            unsupported,
        }
    }
}

struct Analyzer<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    popen_read: FxHashMap<Span, bool>,
    // stdio_arg_locs: FxHashSet<Loc>,
    loc_ind_map: &'a FxHashMap<Loc, LocId>,
    fn_ty_functions: FxHashMap<steensgaard::FnId, Vec<LocalDefId>>,
    steensgaard: &'a steensgaard::AnalysisResult,
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
            Rvalue::Cast(CastKind::PtrToPtr, op, _) => {
                let rty = op.ty(ctx.local_decls, self.tcx);
                match (variance, contains_file_ty(rty, self.tcx)) {
                    (Some(variance), true) => {
                        let l = self.transfer_place(*l, ctx).unwrap();
                        let r = self.transfer_operand(op, ctx).unwrap();
                        self.assign(l, r, variance);
                    }
                    (Some(_), false) => {
                        println!("{:?}", rty);
                        let l = self.transfer_place(*l, ctx).unwrap();
                        self.unsupported.add(l);
                    }
                    (None, true) => {
                        println!("{:?}", ty);
                        let r = self.transfer_operand(op, ctx).unwrap();
                        self.unsupported.add(r);
                    }
                    (None, false) => {}
                }
            }
            Rvalue::Cast(CastKind::PointerFromExposedAddress, _, _) => {}
            Rvalue::Cast(_, _, _) => assert!(variance.is_none()),
            Rvalue::BinaryOp(_, box (op1, op2)) => {
                let ty = op1.ty(ctx.local_decls, self.tcx);
                if contains_file_ty(ty, self.tcx) {
                    if let Some(op1) = self.transfer_operand(op1, ctx) {
                        self.unsupported.add(op1);
                    }
                    if let Some(op2) = self.transfer_operand(op2, ctx) {
                        self.unsupported.add(op2);
                    }
                }
            }
            Rvalue::Aggregate(box AggregateKind::Adt(def_id, _, _, _, field_idx), fields) => {
                assert!(variance.is_none());
                if self.tcx.adt_def(def_id).is_union() {
                    let f = &fields[FieldIdx::from_u32(0)];
                    let ty = f.ty(ctx.local_decls, self.tcx);
                    if let Some(variance) = file_type_variance(ty, self.tcx) {
                        let l = Loc::Field(def_id.expect_local(), field_idx.unwrap());
                        let l = self.loc_ind_map[&l];
                        let r = self.transfer_operand(f, ctx).unwrap();
                        self.assign(l, r, variance);
                    }
                } else {
                    for (idx, f) in fields.iter_enumerated() {
                        let ty = f.ty(ctx.local_decls, self.tcx);
                        if let Some(variance) = file_type_variance(ty, self.tcx) {
                            let l = Loc::Field(def_id.expect_local(), idx);
                            let l = self.loc_ind_map[&l];
                            let r = self.transfer_operand(f, ctx).unwrap();
                            self.assign(l, r, variance);
                        }
                    }
                }
            }
            _ => {
                let variance = some_or!(variance, return);
                let l = some_or!(self.transfer_place(*l, ctx), return);
                match r {
                    Rvalue::Use(op) | Rvalue::Repeat(op, _) => {
                        if let Some(r) = self.transfer_operand(op, ctx) {
                            self.assign(l, r, variance);
                        }
                    }
                    Rvalue::Cast(_, _, _) => unreachable!(),
                    Rvalue::Ref(_, _, place)
                    | Rvalue::AddressOf(_, place)
                    | Rvalue::CopyForDeref(place) => {
                        let r = self.transfer_place(*place, ctx).unwrap();
                        self.assign(l, r, variance);
                    }
                    Rvalue::Aggregate(box kind, fields) => {
                        assert!(matches!(kind, AggregateKind::Array(_)));
                        for f in fields {
                            let r = self.transfer_operand(f, ctx).unwrap();
                            self.assign(l, r, variance);
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    fn transfer_operand(&self, operand: &Operand<'tcx>, ctx: Ctx<'_, 'tcx>) -> Option<LocId> {
        match operand {
            Operand::Copy(p) | Operand::Move(p) => self.transfer_place(*p, ctx),
            Operand::Constant(box c) => Some(self.transfer_constant(*c)),
        }
    }

    fn transfer_place(&self, place: Place<'tcx>, ctx: Ctx<'_, 'tcx>) -> Option<LocId> {
        let loc = if place.projection.is_empty()
            || place.projection.len() == 1 && place.is_indirect_first_projection()
        {
            Loc::Var(ctx.function, place.local)
            // let loc = Loc::Var(ctx.function, place.local);
            // if self.stdio_arg_locs.contains(&loc) {
            //     return None;
            // }
            // loc
        } else {
            let (last, init) = place.projection.split_last().unwrap();
            let ty = Place::ty_from(place.local, init, ctx.local_decls, self.tcx).ty;
            let def_id = ty.ty_adt_id().unwrap().expect_local();
            let ProjectionElem::Field(f, _) = last else { panic!() };
            Loc::Field(def_id, *f)
        };
        Some(self.loc_ind_map[&loc])
    }

    fn transfer_constant(&self, constant: Constant<'tcx>) -> LocId {
        let ConstantKind::Val(value, _) = constant.literal else { panic!() };
        let ConstValue::Scalar(scalar) = value else { panic!() };
        let Scalar::Ptr(ptr, _) = scalar else { panic!() };
        let GlobalAlloc::Static(def_id) = self.tcx.global_alloc(ptr.provenance) else { panic!() };
        let def_id = def_id.expect_local();
        let node = self.tcx.hir().find_by_def_id(def_id).unwrap();
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
                let ty = self
                    .steensgaard
                    .var_ty(self.steensgaard.local(ctx.function, callee.local));
                if let Some(callees) = self.fn_ty_functions.get(&ty.fn_ty) {
                    for callee in callees.clone() {
                        assert!(!is_def_id_api(callee, self.tcx));
                        self.transfer_non_api_call(callee, args, *destination, ctx);
                    }
                }
            }
            Operand::Constant(box constant) => {
                let ConstantKind::Val(value, ty) = constant.literal else { unreachable!() };
                assert!(matches!(value, ConstValue::ZeroSized));
                let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                if let Some(kind) = def_id_api_kind(def_id, self.tcx) {
                    match kind {
                        ApiKind::Open(origin) => {
                            let x = self.transfer_place(*destination, ctx).unwrap();
                            self.add_origin(x, origin);
                        }
                        ApiKind::PipeOpen => {
                            let x = self.transfer_place(*destination, ctx).unwrap();
                            if let Some(read) = self.popen_read.get(&term.source_info.span) {
                                let origin = if *read {
                                    Origin::PipeRead
                                } else {
                                    Origin::PipeWrite
                                };
                                self.add_origin(x, origin);
                            } else {
                                todo!()
                            }
                        }
                        ApiKind::Operation(Some(permission)) => {
                            let sig = self.tcx.fn_sig(def_id).skip_binder().skip_binder();
                            for (t, arg) in sig.inputs().iter().zip(args) {
                                if contains_file_ty(*t, self.tcx) {
                                    if let Some(x) = self.transfer_operand(arg, ctx) {
                                        self.add_permission(x, permission);
                                    }
                                    break;
                                }
                            }
                        }
                        ApiKind::Unsupported => {
                            println!("{:?}", def_id);
                            let sig = self.tcx.fn_sig(def_id).skip_binder().skip_binder();
                            for (t, arg) in sig.inputs().iter().zip(args) {
                                if contains_file_ty(*t, self.tcx) {
                                    if let Some(x) = self.transfer_operand(arg, ctx) {
                                        self.unsupported.add(x);
                                    }
                                    break;
                                }
                            }
                        }
                        ApiKind::Operation(None)
                        | ApiKind::StdioOperation
                        | ApiKind::Ignore
                        | ApiKind::NotIO => {}
                    }
                } else if let Some(callee) = def_id.as_local() {
                    self.transfer_non_api_call(callee, args, *destination, ctx);
                }
            }
        }
    }

    fn transfer_non_api_call(
        &mut self,
        callee: LocalDefId,
        args: &[Operand<'tcx>],
        destination: Place<'tcx>,
        ctx: Ctx<'_, 'tcx>,
    ) {
        let sig = self.tcx.fn_sig(callee).skip_binder().skip_binder();
        for (i, (t, arg)) in sig.inputs().iter().zip(args).enumerate() {
            if let Some(variance) = file_type_variance(*t, self.tcx) {
                let l = Loc::Var(callee, Local::new(i + 1));
                let l = self.loc_ind_map[&l];
                let r = self.transfer_operand(arg, ctx).unwrap();
                self.assign(l, r, variance);
            }
        }
        if let Some(variance) = file_type_variance(sig.output(), self.tcx) {
            let l = self.transfer_place(destination, ctx).unwrap();
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
        if lhs != stdout && rhs != stdout && lhs != stderr && rhs != stderr {
            self.unsupported.union(lhs, rhs);
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Variance {
    Covariant,
    Invariant,
}

fn file_type_variance<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Option<Variance> {
    match ty.kind() {
        TyKind::RawPtr(TypeAndMut { ty, mutbl }) | TyKind::Ref(_, ty, mutbl) => {
            if let TyKind::Adt(adt_def, _) = ty.kind() {
                if is_file_ty(adt_def.did(), tcx) {
                    Some(Variance::Covariant)
                } else {
                    None
                }
            } else {
                let v = file_type_variance(*ty, tcx)?;
                if mutbl.is_not() {
                    Some(v)
                } else {
                    Some(Variance::Invariant)
                }
            }
        }
        TyKind::Array(ty, _) | TyKind::Slice(ty) => file_type_variance(*ty, tcx),
        _ => None,
    }
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
    edges: IndexVec<V, HybridBitSet<V>>,
}

impl<V: Idx, T: Idx> Graph<V, T> {
    #[inline]
    fn new(size: usize, tok_num: usize) -> Self {
        assert!(tok_num <= 8);
        Self {
            tok_num,
            solutions: IndexVec::from_raw(vec![BitSet8::new_empty(); size]),
            edges: IndexVec::from_raw(vec![HybridBitSet::new_empty(size); size]),
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

            let mut components = vec![HybridBitSet::new_empty(size); sccs.num_sccs()];
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
                            let set = std::mem::replace(&mut deltas[id], BitSet8::new_empty());
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
                            let set = std::mem::replace(&mut solutions[id], BitSet8::new_empty());
                            solutions[*rep].union(&set);
                        }
                    }
                    let mut union = solutions[*rep];
                    union.subtract(&intersection);
                    deltas[*rep].union(&union);
                }

                // update edges
                edges = IndexVec::from_raw(vec![HybridBitSet::new_empty(size); size]);
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
                let delta = std::mem::replace(&mut deltas[v], BitSet8::new_empty());

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
fn contains_multiple<T: Idx>(set: &HybridBitSet<T>) -> bool {
    let mut iter = set.iter();
    iter.next().is_some() && iter.next().is_some()
}

#[repr(transparent)]
struct VecBitSet<'a, T: Idx>(&'a IndexVec<T, HybridBitSet<T>>);

impl<T: Idx> DirectedGraph for VecBitSet<'_, T> {
    type Node = T;
}

impl<T: Idx> WithNumNodes for VecBitSet<'_, T> {
    fn num_nodes(&self) -> usize {
        self.0.len()
    }
}

impl<'a, T: Idx> GraphSuccessors<'_> for VecBitSet<'a, T> {
    type Item = T;
    type Iter = HybridIter<'a, T>;
}

impl<T: Idx> WithSuccessors for VecBitSet<'_, T> {
    fn successors(&self, node: Self::Node) -> <Self as GraphSuccessors<'_>>::Iter {
        self.0[node].iter()
    }
}

struct UnsupportedTracker<'a> {
    arena: &'a Arena<DisjointSet<'a, LocId>>,
    locs: FxHashMap<LocId, &'a DisjointSet<'a, LocId>>,
    unsupported: FxHashSet<LocId>,
}

impl<'a> UnsupportedTracker<'a> {
    fn new(arena: &'a Arena<DisjointSet<'a, LocId>>) -> Self {
        Self {
            arena,
            locs: FxHashMap::default(),
            unsupported: FxHashSet::default(),
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

    fn add(&mut self, loc: LocId) {
        if let Entry::Vacant(e) = self.locs.entry(loc) {
            e.insert(self.arena.alloc(DisjointSet::new(loc)));
        }
        self.unsupported.insert(loc);
    }

    fn compute_all(&self, len: usize) -> HybridBitSet<LocId> {
        let mut unsupported = HybridBitSet::new_empty(len);
        for loc_id in &self.unsupported {
            unsupported.insert(self.locs[loc_id].find_set().id());
        }
        for (loc, set) in &self.locs {
            let root = set.find_set().id();
            if unsupported.contains(root) {
                unsupported.insert(*loc);
            }
        }
        unsupported
    }
}

// struct StdioArgVisitor<'tcx> {
//     tcx: TyCtxt<'tcx>,
//     stdio_args: FxHashSet<Span>,
// }

// impl<'tcx> StdioArgVisitor<'tcx> {
//     #[inline]
//     fn new(tcx: TyCtxt<'tcx>) -> Self {
//         Self {
//             tcx,
//             stdio_args: FxHashSet::default(),
//         }
//     }

//     #[inline]
//     fn handle_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
//         let ExprKind::Call(callee, args) = expr.kind else { return };
//         let ExprKind::Path(QPath::Resolved(_, path)) = callee.kind else { return };
//         let Res::Def(DefKind::Fn, def_id) = path.res else { return };
//         if !is_def_id_api(def_id, self.tcx) {
//             return;
//         }
//         for arg in args {
//             if is_std_io_expr(arg, self.tcx) {
//                 self.stdio_args.insert(arg.span);
//             }
//         }
//     }
// }

// impl<'tcx> intravisit::Visitor<'tcx> for StdioArgVisitor<'tcx> {
//     type NestedFilter = nested_filter::OnlyBodies;

//     fn nested_visit_map(&mut self) -> Self::Map {
//         self.tcx.hir()
//     }

//     fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
//         self.handle_expr(expr);
//         intravisit::walk_expr(self, expr);
//     }
// }

#[derive(Default)]
struct AstVisitor<'ast> {
    popen_args: Vec<(Span, LikelyLit<'ast>)>,
}

impl<'ast> rustc_ast::visit::Visitor<'ast> for AstVisitor<'ast> {
    fn visit_expr(&mut self, expr: &'ast rustc_ast::Expr) {
        rustc_ast::visit::walk_expr(self, expr);

        use rustc_ast::ExprKind;
        let ExprKind::Call(callee, args) = &expr.kind else { return };
        let ExprKind::Path(_, path) = &callee.kind else { return };
        if path.segments.last().unwrap().ident.name.as_str() != "popen" {
            return;
        }
        self.popen_args
            .push((expr.span, LikelyLit::from_expr(&args[1])));
    }
}
