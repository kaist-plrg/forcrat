use std::fs;

use etrace::ok_or;
use rustc_ast::{mut_visit::MutVisitor, ptr::P, AttrVec};
use rustc_data_structures::sync::Lrc;
use rustc_middle::ty::TyCtxt;
use rustc_session::parse::ParseSess;
use rustc_span::{
    source_map::{FilePathMapping, SourceMap},
    symbol::Ident,
    FileName, RealFileName,
};

use crate::compile_util::{Pass, SilentEmitter};

#[derive(Debug, Clone, Copy)]
pub struct Transformation;

impl Pass for Transformation {
    type Out = ();

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out {
        let source_map = tcx.sess.source_map();

        let files = source_map.files();
        let lib = files.iter().next().unwrap();
        let FileName::Real(RealFileName::LocalPath(lib_path)) = &lib.name else { panic!() };
        let dir = fs::canonicalize(lib_path.parent().unwrap()).unwrap();
        drop(files);

        tcx.ensure().early_lint_checks(());
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
            TransformVisitor.visit_crate(&mut krate);
            let s = rustc_ast_pretty::pprust::crate_to_string_for_macros(&krate);
            fs::write(path, s).unwrap();
        }
    }
}

struct TransformVisitor;

impl MutVisitor for TransformVisitor {
    fn visit_expr(&mut self, expr: &mut P<rustc_ast::Expr>) {
        rustc_ast::mut_visit::noop_visit_expr(expr, self);
        if let rustc_ast::ExprKind::Block(block, _) = &mut expr.kind {
            let lit = rustc_ast::token::Lit {
                kind: rustc_ast::token::LitKind::Bool,
                symbol: rustc_span::Symbol::intern("true"),
                suffix: None,
            };
            let expr_kind = rustc_ast::ExprKind::Lit(lit);
            let expr = rustc_ast::Expr {
                id: rustc_ast::node_id::DUMMY_NODE_ID,
                kind: expr_kind,
                span: rustc_span::DUMMY_SP,
                attrs: AttrVec::new(),
                tokens: None,
            };
            let local_kind = rustc_ast::LocalKind::Init(P(expr));
            let pat_kind = rustc_ast::PatKind::Ident(
                rustc_ast::BindingAnnotation(rustc_ast::ByRef::No, rustc_ast::Mutability::Not),
                Ident {
                    name: rustc_span::Symbol::intern("newly_defined_x"),
                    span: rustc_span::DUMMY_SP,
                },
                None,
            );
            let pat = rustc_ast::Pat {
                id: rustc_ast::node_id::DUMMY_NODE_ID,
                kind: pat_kind,
                span: rustc_span::DUMMY_SP,
                tokens: None,
            };
            let local = rustc_ast::Local {
                id: rustc_ast::node_id::DUMMY_NODE_ID,
                pat: P(pat),
                ty: None,
                kind: local_kind,
                span: rustc_span::DUMMY_SP,
                attrs: AttrVec::new(),
                tokens: None,
            };
            let stmt_kind = rustc_ast::StmtKind::Local(P(local));
            let stmt = rustc_ast::Stmt {
                id: rustc_ast::node_id::DUMMY_NODE_ID,
                kind: stmt_kind,
                span: rustc_span::DUMMY_SP,
            };
            block.stmts.insert(0, stmt);
        }
    }
}
