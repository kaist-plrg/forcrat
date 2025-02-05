use tracing::info;
use std::ops::ControlFlow;

use lazy_static::lazy_static;
use rustc_abi::{FieldIdx, FIRST_VARIANT};
use rustc_const_eval::interpret::{ConstValue, GlobalAlloc, Scalar};
use rustc_hash::FxHashMap;
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    definitions::DefPathData,
    ItemKind,
};
use rustc_index::{
    bit_set::{BitSet, HybridBitSet},
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

        for (i, loc) in locs.iter_enumerated() {
            info!("{:?}: {:?}", i, loc);
        }
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
                    info!("{:?}", stmt);
                    analyzer.transfer_stmt(stmt, ctx);
                }
                info!("{:?}", bbd.terminator().kind);
                analyzer.transfer_term(bbd.terminator(), ctx);
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
        let ty = l.ty(ctx.local_decls, self.tcx).ty;
        if let Some(variance) = file_type_variance(ty, self.tcx) {
            let l = self.transfer_place(*l, ctx);
            match r {
                Rvalue::Use(op) | Rvalue::Repeat(op, _) => {
                    let r = self.transfer_operand(op, ctx);
                    self.graph.add_edge(l, r, variance);
                }
                Rvalue::Cast(kind, op, _) => {
                    if *kind == CastKind::PtrToPtr {
                        let rty = op.ty(ctx.local_decls, self.tcx);
                        if contains_file_ty(rty, self.tcx) {
                            let r = self.transfer_operand(op, ctx);
                            self.graph.add_edge(l, r, variance);
                        }
                    } else {
                        assert!(
                            *kind == CastKind::PointerFromExposedAddress
                                || !contains_file_ty(ty, self.tcx)
                        );
                    }
                }
                Rvalue::Ref(_, _, place)
                | Rvalue::AddressOf(_, place)
                | Rvalue::CopyForDeref(place) => {
                    let r = self.transfer_place(*place, ctx);
                    self.graph.add_edge(l, r, variance);
                }
                Rvalue::Aggregate(box kind, fields) => {
                    assert!(matches!(kind, AggregateKind::Array(_)));
                    for f in fields {
                        let r = self.transfer_operand(f, ctx);
                        self.graph.add_edge(l, r, variance);
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
                    self.graph.add_edge(l, r, variance);
                }
            } else {
                for (idx, f) in fields.iter_enumerated() {
                    let ty = f.ty(ctx.local_decls, self.tcx);
                    if let Some(variance) = file_type_variance(ty, self.tcx) {
                        let l = Loc::Field(def_id.expect_local(), idx);
                        let l = self.loc_ind_map[&l];
                        let r = self.transfer_operand(f, ctx);
                        self.graph.add_edge(l, r, variance);
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
        let ConstantKind::Val(value, ty) = constant.literal else { panic!() };
        match value {
            ConstValue::Scalar(scalar) => {
                let Scalar::Ptr(ptr, _) = scalar else { panic!() };
                let GlobalAlloc::Static(def_id) = self.tcx.global_alloc(ptr.provenance) else {
                    panic!()
                };
                let loc = Loc::Var(def_id.expect_local(), RETURN_PLACE);
                self.loc_ind_map[&loc]
            }
            ConstValue::ZeroSized => {
                let TyKind::FnDef(_def_id, _) = ty.kind() else { panic!() };
                todo!()
            }
            _ => panic!(),
        }
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
        match func {
            Operand::Copy(func) | Operand::Move(func) => {
                assert!(func.projection.is_empty());
                todo!();
            }
            Operand::Constant(box constant) => {
                let ConstantKind::Val(value, ty) = constant.literal else { unreachable!() };
                assert!(matches!(value, ConstValue::ZeroSized));
                let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                if let Some(kind) = file_api_kind(def_id, self.tcx) {
                    match kind {
                        FileApiKind::Open => {}
                        FileApiKind::Operation(permission) => {
                            let sig = self.tcx.fn_sig(def_id).skip_binder().skip_binder();
                            for (t, arg) in sig.inputs().iter().zip(args) {
                                if contains_file_ty(*t, self.tcx) {
                                    let x = self.transfer_operand(arg, ctx);
                                    self.graph.add_permission(x, permission);
                                    break;
                                }
                            }
                        }
                        FileApiKind::NotSupported => panic!(),
                    }
                } else {
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Variance {
    Covariant,
    Invariant,
    Contravariant,
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
        TyKind::FnDef(_def_id, _) => todo!(),
        TyKind::FnPtr(_sig) => todo!(),
        _ => None,
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
        info!("{:?} {:?}", loc, permission);
        self.permissions[loc].insert(permission);
    }

    fn add_edge(&mut self, from: LocId, to: LocId, v: Variance) {
        match v {
            Variance::Covariant => {
                info!("{:?} --> {:?}", from, to);
                self.edges[from].insert(to);
            }
            Variance::Contravariant => {
                info!("{:?} <-- {:?}", from, to);
                self.edges[to].insert(from);
            }
            Variance::Invariant => {
                info!("{:?} <-> {:?}", from, to);
                self.edges[from].insert(to);
                self.edges[to].insert(from);
            }
        }
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
    Open,
    Operation(Permission),
    NotSupported,
}

static FILE_API_NAMES: [(&str, FileApiKind); 46] = [
    ("fopen", FileApiKind::Open),
    ("tmpfile", FileApiKind::Open),
    ("fclose", FileApiKind::Operation(Permission::Close)),
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
    ("fseek", FileApiKind::Operation(Permission::Read)),
    ("fseeko", FileApiKind::Operation(Permission::Read)),
    ("ftell", FileApiKind::Operation(Permission::Read)),
    ("ftello", FileApiKind::Operation(Permission::Read)),
    ("rewind", FileApiKind::Operation(Permission::Read)),
    ("ungetc", FileApiKind::NotSupported),
    ("funlockfile", FileApiKind::NotSupported),
    ("flockfile", FileApiKind::NotSupported),
    ("popen", FileApiKind::NotSupported),
    ("pclose", FileApiKind::NotSupported),
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
