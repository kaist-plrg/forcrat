use etrace::some_or;
use rustc_ast_pretty::pprust;
use rustc_middle::ty::TyCtxt;
use rustc_span::{FileName, RealFileName};

use crate::compile_util::Pass;

#[derive(Debug, Clone, Copy)]
pub struct Format;

impl Pass for Format {
    type Out = ();

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out {
        tcx.resolver_for_lowering();

        let source_map = tcx.sess.source_map();
        let parse_sess = crate::ast_maker::new_parse_sess();

        for file in source_map.files().iter() {
            let FileName::Real(RealFileName::LocalPath(p)) = &file.name else { continue };
            let src = some_or!(file.src.as_ref(), continue);
            let mut parser = rustc_parse::new_parser_from_source_str(
                &parse_sess,
                file.name.clone(),
                src.to_string(),
            )
            .unwrap();
            let krate = parser.parse_crate_mod().unwrap();
            let s = pprust::crate_to_string_for_macros(&krate);
            std::fs::write(p, s).unwrap();
        }
    }
}
