use rustc_hir::ItemKind;
use rustc_middle::{mir::Local, ty::TyCtxt};

use crate::{compile_util, compile_util::Pass};

#[derive(Debug, Clone, Copy)]
pub struct ReturnFinder;

impl Pass for ReturnFinder {
    type Out = ();

    fn run(&self, tcx: TyCtxt<'_>) {
        for item_id in tcx.hir_free_items() {
            let item = tcx.hir_item(item_id);
            if !matches!(item.kind, ItemKind::Fn { .. }) {
                continue;
            }
            let body = tcx.optimized_mir(item_id.owner_id);
            let ret_ty = &body.local_decls[Local::ZERO].ty;
            if compile_util::contains_file_ty(*ret_ty, tcx) {
                println!("{:?}", item_id);
            }
        }
    }
}
