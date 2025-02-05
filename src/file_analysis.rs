use std::ops::ControlFlow;

use etrace::some_or;
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_hash::FxHashMap;
use rustc_hir::{
    def_id::{DefId, LocalDefId, LocalDefIdMap},
    definitions::DefPathData,
    ItemKind,
};
use rustc_index::{
    bit_set::{BitSet, HybridBitSet},
    Idx, IndexVec,
};
use rustc_middle::{
    mir::{
        AggregateKind, CastKind, Local, LocalDecl, Operand, Place, ProjectionElem, Rvalue,
        Statement, StatementKind, Terminator, TerminatorKind,
    },
    query::{IntoQueryParam, Key},
    ty::{List, Ty, TyCtxt, TyKind, TypeVisitable, TypeVisitor},
};

use crate::{compile_util::Pass, rustc_middle::ty::TypeSuperVisitable, steensgaard};

#[derive(Debug)]
pub struct FileAnalysis {
    pub steensgaard: steensgaard::AnalysisResult,
}

impl Pass for FileAnalysis {
    type Out = ();

    fn run(&self, tcx: TyCtxt<'_>) {
        let hir = tcx.hir();

        let mut locs: IndexVec<LocId, Loc> = IndexVec::new();

        for item_id in hir.items() {
            let item = hir.item(item_id);
            let local_def_id = item.owner_id.def_id;
            let body = match item.kind {
                ItemKind::Fn(_, _, _) if item.ident.name.as_str() != "main" => {
                    tcx.optimized_mir(local_def_id)
                }
                ItemKind::Static(_, _, _) => tcx.mir_for_ctfe(local_def_id),
                ItemKind::Struct(_, _) | ItemKind::Union(_, _)
                    if item.ident.as_str() != "_IO_FILE" =>
                {
                    let adt_def = tcx.adt_def(item.owner_id);
                    for (i, fd) in adt_def
                        .variant(VariantIdx::from_u32(0))
                        .fields
                        .iter_enumerated()
                    {
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

        println!("{:?}", locs);
        let loc_ind_map: FxHashMap<_, _> = locs.iter_enumerated().map(|(i, l)| (*l, i)).collect();

        let mut analyzer = Analyzer {
            tcx,
            loc_ind_map,
            graph: Graph::new(locs.len()),
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
                    analyzer.transfer_stmt(stmt, ctx);
                }
                // analyzer.transfer_term(local_def_id, &body.local_decls, bbd.terminator());
            }
        }
    }
}

struct Analyzer<'tcx> {
    tcx: TyCtxt<'tcx>,
    loc_ind_map: FxHashMap<Loc, LocId>,
    graph: Graph,
}

#[derive(Clone, Copy)]
struct Ctx<'a, 'tcx> {
    function: LocalDefId,
    local_decls: &'a IndexVec<Local, LocalDecl<'tcx>>,
}

impl<'tcx> Analyzer<'tcx> {
    fn transfer_stmt(&mut self, stmt: &Statement<'tcx>, ctx: Ctx<'_, 'tcx>) {
        let StatementKind::Assign(box (l, r)) = &stmt.kind else { return };
        println!("{:?}", stmt);
        let ty = l.ty(ctx.local_decls, self.tcx).ty;
        match r {
            Rvalue::Use(op) | Rvalue::Repeat(op, _) => {
                if contains_file_ty(ty, self.tcx) {
                    if let Some(r) = self.transfer_operand(op, ctx) {
                        let l = self.transfer_place(*l, ctx);
                        self.graph.add_edge(l, r);
                    }
                }
            }
            Rvalue::Cast(kind, _, _) => {
                assert!(
                    *kind == CastKind::PointerFromExposedAddress || !contains_file_ty(ty, self.tcx)
                );
            }
            Rvalue::Ref(_, _, place)
            | Rvalue::AddressOf(_, place)
            | Rvalue::CopyForDeref(place) => {
                if contains_file_ty(ty, self.tcx) {
                    let r = self.transfer_place(*place, ctx);
                    let l = self.transfer_place(*l, ctx);
                    self.graph.add_edge(l, r);
                }
            }
            Rvalue::Aggregate(box kind, fields) => match kind {
                AggregateKind::Array(_) => {
                    if contains_file_ty(ty, self.tcx) {
                        let l = self.transfer_place(*l, ctx);
                        for f in fields {
                            let r = some_or!(self.transfer_operand(f, ctx), continue);
                            self.graph.add_edge(l, r);
                        }
                    }
                }
                AggregateKind::Adt(def_id, _, _, _, field_idx) => {
                    if self.tcx.adt_def(def_id).is_union() {
                        let f = &fields[FieldIdx::from_u32(0)];
                        let ty = f.ty(ctx.local_decls, self.tcx);
                        if contains_file_ty(ty, self.tcx) {
                            if let Some(r) = self.transfer_operand(f, ctx) {
                                let l = Loc::Field(def_id.expect_local(), field_idx.unwrap());
                                let l = self.loc_ind_map[&l];
                                self.graph.add_edge(l, r);
                            }
                        }
                    } else {
                        for (idx, f) in fields.iter_enumerated() {
                            let ty = f.ty(ctx.local_decls, self.tcx);
                            if contains_file_ty(ty, self.tcx) {
                                if let Some(r) = self.transfer_operand(f, ctx) {
                                    let l = Loc::Field(def_id.expect_local(), idx);
                                    let l = self.loc_ind_map[&l];
                                    self.graph.add_edge(l, r);
                                }
                            }
                        }
                    }
                }
                _ => {}
            },
            _ => panic!(),
        }
    }

    fn transfer_operand(&self, operand: &Operand<'tcx>, ctx: Ctx<'_, 'tcx>) -> Option<LocId> {
        operand.place().map(|p| self.transfer_place(p, ctx))
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
        // let ty = destination.ty(ctx.local_decls, self.tcx).ty;
        // let mut visitor = FileTypeVisitor { tcx: self.tcx };
        // ty.visit_with(&mut visitor);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Loc {
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

struct Graph {
    permissions: IndexVec<LocId, BitSet<Permission>>,
    edges: IndexVec<LocId, HybridBitSet<LocId>>,
}

impl Graph {
    fn new(size: usize) -> Self {
        Self {
            permissions: IndexVec::from_raw(vec![BitSet::new_empty(4); size]),
            edges: IndexVec::from_raw(vec![HybridBitSet::new_empty(size); size]),
        }
    }

    fn add_permission(&mut self, loc: LocId, permission: Permission) {
        self.permissions[loc].insert(permission);
    }

    fn add_edge(&mut self, from: LocId, to: LocId) {
        println!("{:?} -> {:?}", from, to);
        self.edges[from].insert(to);
    }
}

#[derive(Default)]
struct AdtVisitor {
    adts: Vec<LocalDefId>,
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for AdtVisitor {
    type BreakTy = ();

    fn visit_ty(&mut self, t: Ty<'tcx>) -> ControlFlow<Self::BreakTy> {
        if let TyKind::Adt(adt_def, _) = t.kind() {
            if let Some(def_id) = adt_def.did().as_local() {
                self.adts.push(def_id);
            }
        }
        t.super_visit_with(self)
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
