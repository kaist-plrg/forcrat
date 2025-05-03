use rustc_abi::FIRST_VARIANT;
use rustc_hir::{
    intravisit::{self, Visitor as HVisitor},
    ItemKind, Pat, PatKind,
};
use rustc_middle::{
    hir::nested_filter,
    mir,
    ty::{self, List, TyCtxt},
};

use crate::compile_util::{self, Pass};

#[derive(Debug, Clone, Copy)]
pub struct TyFinder {
    pub mir: bool,
}

impl Pass for TyFinder {
    type Out = ();

    fn run(&self, tcx: TyCtxt<'_>) {
        if self.mir {
            for item_id in tcx.hir_free_items() {
                let item = tcx.hir_item(item_id);
                let local_def_id = item.owner_id.def_id;
                let body = match item.kind {
                    ItemKind::Fn { .. } => {
                        if item.ident.name.as_str() == "main" {
                            continue;
                        }
                        tcx.optimized_mir(local_def_id)
                    }
                    ItemKind::Static(_, _, _) => tcx.mir_for_ctfe(local_def_id),
                    _ => continue,
                };
                for local_decl in body.local_decls.iter() {
                    if compile_util::contains_file_ty(local_decl.ty, tcx) {
                        println!("{:?}", local_decl.ty);
                    }
                }
            }
            return;
        }

        let mut visitor = Visitor::new(tcx);
        tcx.hir_visit_all_item_likes_in_crate(&mut visitor);

        for item_id in tcx.hir_free_items() {
            let item = tcx.hir_item(item_id);
            match item.kind {
                ItemKind::Static(_, _, _) => {
                    let body = tcx.mir_for_ctfe(item_id.owner_id.def_id);
                    let ty = body.local_decls[mir::RETURN_PLACE].ty;
                    if visitor.is_non_trivial_file_ty(ty) {
                        println!("{:?} {:?}", ty, item.span);
                    }
                }
                ItemKind::Struct(_, _) | ItemKind::Union(_, _) => {
                    let adt_def = tcx.adt_def(item_id.owner_id.def_id);
                    let variant = adt_def.variant(FIRST_VARIANT);
                    for field in &variant.fields {
                        let ty = field.ty(tcx, List::empty());
                        if visitor.is_non_trivial_file_ty(ty) {
                            println!("{:?} {:?}", ty, item.span);
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

struct Visitor<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Visitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    fn is_non_trivial_file_ty(&self, ty: ty::Ty<'tcx>) -> bool {
        if !compile_util::contains_file_ty(ty, self.tcx) {
            return false;
        }
        match ty.kind() {
            ty::TyKind::RawPtr(ty, _) => !ty.is_adt(),
            ty::TyKind::Adt(adt_def, _) => {
                let name = compile_util::def_id_to_ty_symbol(adt_def.did(), self.tcx).unwrap();
                name.as_str() != "AssertParamIsClone"
            }
            _ => true,
        }
    }
}

impl<'tcx> HVisitor<'tcx> for Visitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_pat(&mut self, pat: &'tcx Pat<'tcx>) -> Self::Result {
        intravisit::walk_pat(self, pat);

        if let PatKind::Binding(_, _, ident, _) = pat.kind {
            if ident.name.as_str() == "self" {
                return;
            }
        }

        let typeck = self.tcx.typeck(pat.hir_id.owner.def_id);
        let ty = typeck.pat_ty(pat);
        if self.is_non_trivial_file_ty(ty) {
            println!("{:?} {:?}", ty, pat.span);
        }
    }
}
