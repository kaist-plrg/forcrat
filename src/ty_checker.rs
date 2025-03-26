use rustc_middle::ty::TyCtxt;

use crate::compile_util::Pass;

#[derive(Debug, Clone, Copy)]
pub struct TyChecker;

impl Pass for TyChecker {
    type Out = bool;

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out {
        tcx.analysis(()).is_ok()
    }
}
