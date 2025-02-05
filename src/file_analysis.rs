use std::ops::ControlFlow;

use lazy_static::lazy_static;
use rustc_abi::{FieldIdx, FIRST_VARIANT};
use rustc_const_eval::interpret::{ConstValue, GlobalAlloc, Scalar};
use rustc_data_structures::graph::{
    scc::Sccs, DirectedGraph, GraphSuccessors, WithNumNodes, WithSuccessors,
};
use rustc_hash::FxHashMap;
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    definitions::DefPathData,
    ItemKind, Node,
};
use rustc_index::{
    bit_set::{BitSet, HybridBitSet, HybridIter},
    Idx, IndexVec,
};
use rustc_middle::{
    mir::{
        AggregateKind, CastKind, Constant, ConstantKind, Local, LocalDecl, Operand, Place,
        ProjectionElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, RETURN_PLACE,
    },
    query::{IntoQueryParam, Key},
    ty::{List, Ty, TyCtxt, TyKind, TypeAndMut, TypeVisitable, TypeVisitor},
};
use tracing::info;

use crate::{compile_util::Pass, rustc_middle::ty::TypeSuperVisitable, steensgaard};

#[derive(Debug)]
pub struct FileAnalysis {
    pub steensgaard: steensgaard::AnalysisResult,
}

impl Pass for FileAnalysis {
    type Out = ();

    fn run(&self, tcx: TyCtxt<'_>) {
        info!("\n{:?}", self.steensgaard);
        let hir = tcx.hir();

        let mut fn_ty_functions: FxHashMap<steensgaard::FnId, Vec<LocalDefId>> =
            FxHashMap::default();
        let mut locs: IndexVec<LocId, Loc> =
            IndexVec::from_raw(vec![Loc::Stdin, Loc::Stdout, Loc::Stderr]);

        for item_id in hir.items() {
            let item = hir.item(item_id);
            let local_def_id = item.owner_id.def_id;
            let body = match item.kind {
                ItemKind::Fn(_, _, _) if item.ident.name.as_str() != "main" => {
                    let ty = self
                        .steensgaard
                        .var_ty(self.steensgaard.global(local_def_id));
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
            for (i, local_decl) in body.local_decls.iter_enumerated() {
                if contains_file_ty(local_decl.ty, tcx) {
                    locs.push(Loc::Var(local_def_id, i));
                }
            }
        }

        for (i, fs) in &fn_ty_functions {
            info!("{:?}: {:?}", i, fs);
        }
        for (i, loc) in locs.iter_enumerated() {
            info!("{:?}: {:?}", i, loc);
        }
        let loc_ind_map: FxHashMap<_, _> = locs.iter_enumerated().map(|(i, l)| (*l, i)).collect();

        let mut origin_graph: Graph<LocId, Origin> = Graph::new(locs.len(), 6);
        origin_graph.add_solution(loc_ind_map[&Loc::Stdin], Origin::Stdin);
        origin_graph.add_solution(loc_ind_map[&Loc::Stdout], Origin::Stdout);
        origin_graph.add_solution(loc_ind_map[&Loc::Stderr], Origin::Stderr);
        let mut analyzer = Analyzer {
            tcx,
            steensgaard: &self.steensgaard,
            fn_ty_functions,
            loc_ind_map,
            permission_graph: Graph::new(locs.len(), 4),
            origin_graph,
        };

        for item_id in hir.items() {
            let item = hir.item(item_id);
            let local_def_id = item.owner_id.def_id;
            let body = match item.kind {
                ItemKind::Fn(_, _, _) if item.ident.name.as_str() != "main" => {
                    tcx.optimized_mir(local_def_id)
                }
                ItemKind::Static(_, _, _) => tcx.mir_for_ctfe(local_def_id),
                _ => continue,
            };
            let ctx = Ctx {
                function: local_def_id,
                local_decls: &body.local_decls,
            };
            for bbd in body.basic_blocks.iter() {
                for stmt in &bbd.statements {
                    info!("{:?}", stmt);
                    analyzer.transfer_stmt(stmt, ctx);
                }
                info!("{:?}", bbd.terminator().kind);
                analyzer.transfer_term(bbd.terminator(), ctx);
            }
        }

        let permissions = analyzer.permission_graph.solve();
        let origins = analyzer.origin_graph.solve();

        for (((i, loc), permissions), origins) in
            locs.iter_enumerated().zip(permissions).zip(origins)
        {
            info!("{:?} {:?}: {:?}, {:?}", i, loc, permissions, origins);
        }
    }
}

struct Analyzer<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    loc_ind_map: FxHashMap<Loc, LocId>,
    fn_ty_functions: FxHashMap<steensgaard::FnId, Vec<LocalDefId>>,
    steensgaard: &'a steensgaard::AnalysisResult,
    permission_graph: Graph<LocId, Permission>,
    origin_graph: Graph<LocId, Origin>,
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
        if let Some(variance) = file_type_variance(ty, self.tcx) {
            let l = self.transfer_place(*l, ctx);
            match r {
                Rvalue::Use(op) | Rvalue::Repeat(op, _) => {
                    let r = self.transfer_operand(op, ctx);
                    self.assign(l, r, variance);
                }
                Rvalue::Cast(kind, op, _) => match kind {
                    CastKind::PtrToPtr => {
                        let rty = op.ty(ctx.local_decls, self.tcx);
                        if contains_file_ty(rty, self.tcx) {
                            let r = self.transfer_operand(op, ctx);
                            self.assign(l, r, variance);
                        }
                    }
                    CastKind::PointerFromExposedAddress => {
                        self.add_origin(l, Origin::Null);
                    }
                    _ => {
                        assert!(!contains_file_ty(ty, self.tcx));
                    }
                },
                Rvalue::Ref(_, _, place)
                | Rvalue::AddressOf(_, place)
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
        } else if let Rvalue::Aggregate(box kind, fields) = r {
            let AggregateKind::Adt(def_id, _, _, _, field_idx) = kind else { panic!() };
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

    fn transfer_operand(&self, operand: &Operand<'tcx>, ctx: Ctx<'_, 'tcx>) -> LocId {
        match operand {
            Operand::Copy(p) | Operand::Move(p) => self.transfer_place(*p, ctx),
            Operand::Constant(box c) => self.transfer_constant(*c),
        }
    }

    fn transfer_place(&self, place: Place<'tcx>, ctx: Ctx<'_, 'tcx>) -> LocId {
        let loc = if place.projection.is_empty()
            || place.projection.len() == 1 && place.is_indirect_first_projection()
        {
            Loc::Var(ctx.function, place.local)
        } else {
            let (last, init) = place.projection.split_last().unwrap();
            let ty = Place::ty_from(place.local, init, ctx.local_decls, self.tcx).ty;
            let def_id = ty.ty_adt_id().unwrap().expect_local();
            let ProjectionElem::Field(f, _) = last else { panic!() };
            Loc::Field(def_id, *f)
        };
        self.loc_ind_map[&loc]
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
                let callees = self.fn_ty_functions[&ty.fn_ty].clone();
                for callee in callees {
                    assert!(file_api_kind(callee, self.tcx).is_none());
                    self.transfer_non_api_call(callee, args, *destination, ctx);
                }
            }
            Operand::Constant(box constant) => {
                let ConstantKind::Val(value, ty) = constant.literal else { unreachable!() };
                assert!(matches!(value, ConstValue::ZeroSized));
                let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                if let Some(kind) = file_api_kind(def_id, self.tcx) {
                    match kind {
                        FileApiKind::FileOpen => {
                            let x = self.transfer_place(*destination, ctx);
                            self.add_origin(x, Origin::File);
                        }
                        FileApiKind::PipeOpen => {
                            let x = self.transfer_place(*destination, ctx);
                            self.add_origin(x, Origin::Pipe);
                        }
                        FileApiKind::Operation(permission) => {
                            let sig = self.tcx.fn_sig(def_id).skip_binder().skip_binder();
                            for (t, arg) in sig.inputs().iter().zip(args) {
                                if contains_file_ty(*t, self.tcx) {
                                    let x = self.transfer_operand(arg, ctx);
                                    self.add_permission(x, permission);
                                    break;
                                }
                            }
                        }
                        FileApiKind::NotSupported => panic!(),
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
                let r = self.transfer_operand(arg, ctx);
                self.assign(l, r, variance);
            }
        }
        if let Some(variance) = file_type_variance(sig.output(), self.tcx) {
            let l = self.transfer_place(destination, ctx);
            let r = Loc::Var(callee, RETURN_PLACE);
            let r = self.loc_ind_map[&r];
            self.assign(l, r, variance);
        }
    }

    fn add_permission(&mut self, loc: LocId, permission: Permission) {
        info!("{:?} {:?}", loc, permission);
        self.permission_graph.add_solution(loc, permission);
    }

    fn add_origin(&mut self, loc: LocId, origin: Origin) {
        info!("{:?} {:?}", loc, origin);
        self.origin_graph.add_solution(loc, origin);
    }

    fn assign(&mut self, lhs: LocId, rhs: LocId, v: Variance) {
        info!("{:?} := {:?} {:?}", lhs, rhs, v);
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Loc {
    Stdin,
    Stdout,
    Stderr,
    Var(LocalDefId, Local),
    Field(LocalDefId, FieldIdx),
}

rustc_index::newtype_index! {
    #[debug_format = "L{}"]
    pub struct LocId {}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
enum Permission {
    Read = 0,
    Write = 1,
    Seek = 2,
    Close = 3,
}

impl Idx for Permission {
    #[inline]
    fn new(idx: usize) -> Self {
        if idx > 3 {
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
#[repr(u8)]
enum Origin {
    Null = 0,
    File = 1,
    Stdin = 2,
    Stdout = 3,
    Stderr = 4,
    Pipe = 5,
}

impl Idx for Origin {
    #[inline]
    fn new(idx: usize) -> Self {
        if idx > 5 {
            panic!()
        }
        unsafe { std::mem::transmute(idx as u8) }
    }

    #[inline]
    fn index(self) -> usize {
        self as _
    }
}

struct Graph<V: Idx, T: Idx> {
    tok_num: usize,
    solutions: IndexVec<V, BitSet<T>>,
    edges: IndexVec<V, HybridBitSet<V>>,
}

impl<V: Idx, T: Idx> Graph<V, T> {
    fn new(size: usize, tok_num: usize) -> Self {
        Self {
            tok_num,
            solutions: IndexVec::from_raw(vec![BitSet::new_empty(tok_num); size]),
            edges: IndexVec::from_raw(vec![HybridBitSet::new_empty(size); size]),
        }
    }

    fn add_solution(&mut self, v: V, t: T) {
        self.solutions[v].insert(t);
    }

    fn add_edge(&mut self, from: V, to: V) {
        self.edges[from].insert(to);
    }

    fn solve(self) -> IndexVec<V, BitSet<T>> {
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
                            let set = std::mem::replace(&mut deltas[id], BitSet::new_empty(size));
                            deltas[*rep].union(&set);
                        }
                    }
                }

                // update solutions
                for (rep, ids) in &cycles {
                    let mut intersection = BitSet::new_empty(tok_num);
                    intersection.insert_all();
                    for id in ids.iter() {
                        intersection.intersect(&solutions[id]);
                        if *rep != id {
                            let set =
                                std::mem::replace(&mut solutions[id], BitSet::new_empty(tok_num));
                            solutions[*rep].union(&set);
                        }
                    }
                    let mut union = solutions[*rep].clone();
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
                let delta = std::mem::replace(&mut deltas[v], BitSet::new_empty(size));

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
                solutions[id] = solutions[*rep].clone();
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

fn contains_file_ty<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let mut visitor = FileTypeVisitor { tcx };
    ty.visit_with(&mut visitor).is_break()
}

fn is_file_ty(id: impl IntoQueryParam<DefId>, tcx: TyCtxt<'_>) -> bool {
    let key = tcx.def_key(id);
    let DefPathData::TypeNs(name) = key.disambiguated_data.data else { return false };
    name.as_str() == "_IO_FILE"
}

fn file_api_kind(id: impl IntoQueryParam<DefId>, tcx: TyCtxt<'_>) -> Option<FileApiKind> {
    let key = tcx.def_key(id);
    let DefPathData::ValueNs(name) = key.disambiguated_data.data else { return None };
    FILE_API_NAME_SET
        .get(strip_unlocked(name.as_str()))
        .copied()
}

fn strip_unlocked(name: &str) -> &str {
    name.strip_suffix("_unlocked").unwrap_or(name)
}

#[derive(Debug, Clone, Copy)]
enum FileApiKind {
    FileOpen,
    PipeOpen,
    Operation(Permission),
    NotSupported,
}

static FILE_API_NAMES: [(&str, FileApiKind); 46] = [
    ("fopen", FileApiKind::FileOpen),
    ("tmpfile", FileApiKind::FileOpen),
    ("fclose", FileApiKind::Operation(Permission::Close)),
    ("popen", FileApiKind::PipeOpen),
    ("pclose", FileApiKind::Operation(Permission::Close)),
    ("putc", FileApiKind::Operation(Permission::Write)),
    ("fputc", FileApiKind::Operation(Permission::Write)),
    ("fputs", FileApiKind::Operation(Permission::Write)),
    ("fprintf", FileApiKind::Operation(Permission::Write)),
    ("vfprintf", FileApiKind::Operation(Permission::Write)),
    ("fwrite", FileApiKind::Operation(Permission::Write)),
    ("fflush", FileApiKind::Operation(Permission::Write)),
    ("getc", FileApiKind::Operation(Permission::Read)),
    ("fgetc", FileApiKind::Operation(Permission::Read)),
    ("fgets", FileApiKind::Operation(Permission::Read)),
    ("fscanf", FileApiKind::Operation(Permission::Read)),
    ("vfscanf", FileApiKind::Operation(Permission::Read)),
    ("getline", FileApiKind::Operation(Permission::Read)),
    ("getdelim", FileApiKind::Operation(Permission::Read)),
    ("fread", FileApiKind::Operation(Permission::Read)),
    ("fseek", FileApiKind::Operation(Permission::Seek)),
    ("fseeko", FileApiKind::Operation(Permission::Seek)),
    ("ftell", FileApiKind::Operation(Permission::Seek)),
    ("ftello", FileApiKind::Operation(Permission::Seek)),
    ("rewind", FileApiKind::Operation(Permission::Seek)),
    ("ungetc", FileApiKind::NotSupported),
    ("funlockfile", FileApiKind::NotSupported),
    ("flockfile", FileApiKind::NotSupported),
    ("fileno", FileApiKind::NotSupported),
    ("fdopen", FileApiKind::NotSupported),
    ("ferror", FileApiKind::NotSupported),
    ("feof", FileApiKind::NotSupported),
    ("clearerr", FileApiKind::NotSupported),
    ("freopen", FileApiKind::NotSupported),
    ("setvbuf", FileApiKind::NotSupported),
    ("setbuf", FileApiKind::NotSupported),
    ("setlinebuf", FileApiKind::NotSupported),
    ("fpurge", FileApiKind::NotSupported),
    ("endmntent", FileApiKind::NotSupported),
    ("getmntent", FileApiKind::NotSupported),
    ("setmntent", FileApiKind::NotSupported),
    ("fgetpos", FileApiKind::NotSupported),
    ("fsetpos", FileApiKind::NotSupported),
    ("__fpending", FileApiKind::NotSupported),
    ("__freading", FileApiKind::NotSupported),
    ("__fwriting", FileApiKind::NotSupported),
];

lazy_static! {
    static ref FILE_API_NAME_SET: FxHashMap<&'static str, FileApiKind> =
        FILE_API_NAMES.iter().copied().collect();
}
