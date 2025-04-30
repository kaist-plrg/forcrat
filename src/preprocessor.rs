use etrace::some_or;
use rustc_ast::{mut_visit::MutVisitor, ptr::P, *};
use rustc_ast_pretty::pprust;
use rustc_middle::ty::TyCtxt;
use rustc_span::{FileName, RealFileName};

use crate::{ast_maker::parse_expr, compile_util::Pass};

pub fn write_to_files(res: &PreprocessResult) {
    for (f, s) in &res.files {
        let FileName::Real(RealFileName::LocalPath(p)) = f else { panic!() };
        println!("{:?}", p);
        std::fs::write(p, s).unwrap();
    }
}

#[derive(Debug)]
pub struct PreprocessResult {
    files: Vec<(FileName, String)>,
}

#[derive(Debug, Clone, Copy)]
pub struct Preprocessor;

impl Pass for Preprocessor {
    type Out = PreprocessResult;

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out {
        tcx.resolver_for_lowering();

        let source_map = tcx.sess.source_map();
        let parse_sess = crate::ast_maker::new_parse_sess();
        let mut files = vec![];

        for file in source_map.files().iter() {
            if !matches!(
                file.name,
                FileName::Real(RealFileName::LocalPath(_)) | FileName::Custom(_)
            ) {
                continue;
            }
            let src = some_or!(file.src.as_ref(), continue);
            let mut parser = rustc_parse::new_parser_from_source_str(
                &parse_sess,
                file.name.clone(),
                src.to_string(),
            )
            .unwrap();
            let mut krate = parser.parse_crate_mod().unwrap();
            let mut visitor = PreprocessVisitor { updated: false };
            visitor.visit_crate(&mut krate);
            if visitor.updated {
                let s = pprust::crate_to_string_for_macros(&krate);
                files.push((file.name.clone(), s));
            }
        }

        PreprocessResult { files }
    }
}

struct PreprocessVisitor {
    updated: bool,
}

impl MutVisitor for PreprocessVisitor {
    fn visit_expr(&mut self, expr: &mut P<Expr>) {
        if let ExprKind::If(c, t, f) = &mut expr.kind {
            if let Some(b) = eval_expr_to_bool(c) {
                self.updated = true;
                if b {
                    let e = Expr {
                        id: DUMMY_NODE_ID,
                        kind: ExprKind::Block(t.clone(), None),
                        span: expr.span,
                        attrs: expr.attrs.clone(),
                        tokens: expr.tokens.clone(),
                    };
                    *expr = P(e);
                } else if let Some(f) = f {
                    *expr = f.clone();
                } else {
                    *expr = P(expr!("()"));
                }
            }
        }
        mut_visit::walk_expr(self, expr);
    }
}

fn eval_expr_to_bool(expr: &Expr) -> Option<bool> {
    match &expr.kind {
        ExprKind::Binary(op, l, r) => match op.node {
            BinOpKind::And => match (eval_expr_to_bool(l), eval_expr_to_bool(r)) {
                (Some(true), Some(true)) => Some(true),
                (Some(false), _) | (_, Some(false)) => Some(false),
                _ => None,
            },
            BinOpKind::Or => match (eval_expr_to_bool(l), eval_expr_to_bool(r)) {
                (Some(true), _) | (_, Some(true)) => Some(true),
                (Some(false), Some(false)) => Some(false),
                _ => None,
            },
            BinOpKind::Eq | BinOpKind::Ne => {
                if let (ExprKind::Lit(l), ExprKind::Lit(r)) = (&l.kind, &r.kind) {
                    if matches!(l.kind, token::LitKind::Integer)
                        && matches!(r.kind, token::LitKind::Integer)
                    {
                        let l: usize = l.symbol.as_str().parse().unwrap();
                        let r: usize = r.symbol.as_str().parse().unwrap();
                        Some(if matches!(op.node, BinOpKind::Eq) {
                            l == r
                        } else {
                            l != r
                        })
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => None,
        },
        ExprKind::Unary(op, v) => {
            if *op == UnOp::Not {
                Some(!eval_expr_to_bool(v)?)
            } else {
                None
            }
        }
        ExprKind::Paren(expr) => eval_expr_to_bool(expr),
        _ => None,
    }
}
