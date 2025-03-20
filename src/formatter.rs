use std::ops::Deref;

use rustc_middle::ty::TyCtxt;

use crate::compile_util::Pass;

#[derive(Debug, Clone, Copy)]
pub struct Formatter;

impl Pass for Formatter {
    type Out = String;

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out {
        let r = tcx.crate_for_resolver(()).borrow();
        let (krate, _) = r.deref();
        rustc_ast_pretty::pprust::crate_to_string_for_macros(krate)
    }
}
