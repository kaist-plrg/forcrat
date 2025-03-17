use std::{fs, path::PathBuf};

use etrace::ok_or;
use rustc_ast::{mut_visit, mut_visit::MutVisitor};
use rustc_data_structures::sync::Lrc;
use rustc_hash::FxHashMap;
use rustc_index::bit_set::BitSet;
use rustc_middle::{mir, ty::TyCtxt};
use rustc_session::parse::ParseSess;
use rustc_span::{
    source_map::{FilePathMapping, SourceMap},
    FileName, RealFileName,
};

use crate::{
    api_list::{is_symbol_api, Permission},
    ast_maker::*,
    compile_util::{self, LoHi, Pass, SilentEmitter},
    file_analysis::{self, Loc},
};

#[derive(Debug)]
pub struct Transformation {
    pub analysis_result: file_analysis::AnalysisResult,
}

impl Pass for Transformation {
    type Out = ();

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out {
        let source_map = tcx.sess.source_map();

        let files = source_map.files();
        let lib = files.iter().next().unwrap();
        let FileName::Real(RealFileName::LocalPath(lib_path)) = &lib.name else { panic!() };
        let dir = fs::canonicalize(lib_path.parent().unwrap()).unwrap();
        drop(files);

        let hir = tcx.hir();
        let mut fn_permissions: FxHashMap<PathBuf, FxHashMap<LoHi, _>> = FxHashMap::default();
        for item_id in hir.items() {
            let item = hir.item(item_id);
            let local_def_id = item.owner_id.def_id;
            if let rustc_hir::ItemKind::Fn(sig, _, _) = item.kind {
                if is_symbol_api(item.ident.name) || item.ident.name.as_str() == "main" {
                    continue;
                }
                let mut permissions = vec![];
                for i in 0..sig.decl.inputs.len() {
                    let loc = Loc::Var(local_def_id, mir::Local::from_usize(i + 1));
                    let loc_id = self.analysis_result.loc_ind_map[&loc];
                    let p = &self.analysis_result.permissions[loc_id];
                    permissions.push(p);
                }
                let span = sig.span;
                let (p, lh) = compile_util::span_to_plh(span, source_map).unwrap();
                fn_permissions.entry(p).or_default().insert(lh, permissions);
            }
        }

        let empty = FxHashMap::default();
        for file in source_map.files().iter() {
            let FileName::Real(RealFileName::LocalPath(path)) = &file.name else { continue };
            let path = ok_or!(fs::canonicalize(path), continue);
            if !path.starts_with(&dir) {
                continue;
            }
            let handler = rustc_errors::Handler::with_emitter(Box::new(SilentEmitter));
            let source_map = Lrc::new(SourceMap::new(FilePathMapping::empty()));
            let parse_sess = ParseSess::with_span_handler(handler, source_map);
            let mut parser = rustc_parse::new_parser_from_file(&parse_sess, &path, None);
            let mut krate = parser.parse_crate_mod().unwrap();
            let mut visitor = TransformVisitor {
                source_map: parse_sess.source_map(),
                fn_permissions: fn_permissions.get(&path).unwrap_or(&empty),
            };
            visitor.visit_crate(&mut krate);
            let s = rustc_ast_pretty::pprust::crate_to_string_for_macros(&krate);
            fs::write(path, s).unwrap();
        }
    }
}

struct TransformVisitor<'a> {
    source_map: &'a SourceMap,
    fn_permissions: &'a FxHashMap<LoHi, Vec<&'a BitSet<Permission>>>,
}

impl MutVisitor for TransformVisitor<'_> {
    fn visit_item_kind(&mut self, item: &mut rustc_ast::ItemKind) {
        mut_visit::noop_visit_item_kind(item, self);

        if let rustc_ast::ItemKind::Fn(f) = item {
            let (_, lh) = compile_util::span_to_plh(f.sig.span, self.source_map).unwrap();
            if let Some(permissions) = self.fn_permissions.get(&lh) {
                let mut ps = BitSet::new_empty(Permission::NUM);
                for (param, perm) in f.sig.decl.inputs.iter_mut().zip(permissions) {
                    if !perm.is_empty() {
                        let path = mk_path(vec![mk_path_segment(mk_ident("TTT"), None)]);
                        *param.ty = mk_path_ty(path);
                        ps.union(*perm);
                    }
                }
                if !ps.is_empty() {
                    let mut bounds = vec![];
                    for p in ps.iter() {
                        let p = format!("{:?}", p);
                        let bound = rustc_ast::GenericBound::Trait(
                            mk_poly_trait_ref(
                                vec![],
                                mk_trait_ref(mk_path(vec![
                                    mk_path_segment(mk_ident("std"), None),
                                    mk_path_segment(mk_ident("io"), None),
                                    mk_path_segment(mk_ident(&p), None),
                                ])),
                            ),
                            rustc_ast::TraitBoundModifier::None,
                        );
                        bounds.push(bound);
                    }
                    let gp = mk_generic_param(
                        mk_ident("TTT"),
                        bounds,
                        rustc_ast::GenericParamKind::Type { default: None },
                    );
                    f.generics.params.push(gp);
                }
            }
        }
    }

    //     fn visit_block(&mut self, block: &mut P<rustc_ast::Block>) {
    //         mut_visit::noop_visit_block(block, self);

    //         let expr = mk_lit_expr(rustc_ast::token::LitKind::Bool, "true");
    //         let pat = mk_ident_pat(
    //             rustc_ast::ByRef::No,
    //             rustc_ast::Mutability::Not,
    //             "newly_defined_x",
    //         );
    //         let stmt = mk_local_init_stmt(pat, None, expr);
    //         block.stmts.insert(0, stmt);
    //     }
}
