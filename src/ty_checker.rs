use rustc_interface::Config;
use rustc_middle::ty::TyCtxt;
use rustc_session::config::Input;

use crate::compile_util::{self, Pass};

#[derive(Debug, Clone, Copy)]
pub struct TyChecker;

impl Pass for TyChecker {
    type Out = bool;

    fn config(input: Input) -> Config {
        compile_util::make_no_warning_config(input)
    }

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out {
        tcx.analysis(()).is_ok()
    }
}
