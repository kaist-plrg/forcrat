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
            if let Some(Value::Bool(b)) = eval_expr(c) {
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

    fn visit_block(&mut self, b: &mut P<Block>) {
        let mut assert = false;
        for stmt in &mut b.stmts {
            if assert {
                assert = false;
                let StmtKind::Semi(e) = &mut stmt.kind else { continue };
                let ExprKind::Block(b, Some(_)) = &mut e.kind else { continue };
                let [stmt] = &b.stmts[..] else { continue };
                if is_assert_stmt(stmt) {
                    self.updated = true;
                    b.stmts.clear();
                }
            } else {
                assert = is_assert_stmt(stmt);
            }
        }
        mut_visit::walk_block(self, b);
    }
}

fn is_assert_stmt(stmt: &Stmt) -> bool {
    let StmtKind::Expr(e) = &stmt.kind else { return false };
    let ExprKind::If(_, t, f) = &e.kind else { return false };
    if !t.stmts.is_empty() {
        return false;
    }
    let f = some_or!(f.as_ref(), return false);
    let ExprKind::Block(b, None) = &f.kind else { return false };
    let [s] = &b.stmts[..] else { return false };
    let StmtKind::Semi(e) = &s.kind else { return false };
    let ExprKind::Call(e, _) = &e.kind else { return false };
    let ExprKind::Path(_, path) = &e.kind else { return false };
    let [segment] = &path.segments[..] else { return false };
    segment.ident.name.as_str() == "__assert_fail"
}

#[allow(variant_size_differences)]
enum Value {
    Bool(bool),
    Int(usize),
}

fn eval_expr(expr: &Expr) -> Option<Value> {
    use Value::*;
    match &expr.kind {
        ExprKind::Binary(op, l, r) => match op.node {
            BinOpKind::And => match (eval_expr(l), eval_expr(r)) {
                (Some(Bool(true)), Some(Bool(true))) => Some(Bool(true)),
                (Some(Bool(false)), _) | (_, Some(Bool(false))) => Some(Bool(false)),
                _ => None,
            },
            BinOpKind::Or => match (eval_expr(l), eval_expr(r)) {
                (Some(Bool(true)), _) | (_, Some(Bool(true))) => Some(Bool(true)),
                (Some(Bool(false)), Some(Bool(false))) => Some(Bool(false)),
                _ => None,
            },
            BinOpKind::Eq => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Bool(l == r)),
                _ => None,
            },
            BinOpKind::Ne => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Bool(l != r)),
                _ => None,
            },
            BinOpKind::Gt => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Bool(l > r)),
                _ => None,
            },
            BinOpKind::Ge => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Bool(l >= r)),
                _ => None,
            },
            BinOpKind::Lt => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Bool(l < r)),
                _ => None,
            },
            BinOpKind::Le => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Bool(l <= r)),
                _ => None,
            },
            BinOpKind::Add => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l + r)),
                _ => None,
            },
            BinOpKind::Sub => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l - r)),
                _ => None,
            },
            BinOpKind::Mul => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l * r)),
                _ => None,
            },
            BinOpKind::Div => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l / r)),
                _ => None,
            },
            BinOpKind::Rem => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l % r)),
                _ => None,
            },
            BinOpKind::BitAnd => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l & r)),
                _ => None,
            },
            BinOpKind::BitOr => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l | r)),
                _ => None,
            },
            BinOpKind::BitXor => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l ^ r)),
                _ => None,
            },
            BinOpKind::Shl => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l << r)),
                _ => None,
            },
            BinOpKind::Shr => match (eval_expr(l), eval_expr(r)) {
                (Some(Int(l)), Some(Int(r))) => Some(Int(l >> r)),
                _ => None,
            },
        },
        ExprKind::Cast(e, ty) => {
            let v = eval_expr(e)?;
            let TyKind::Path(_, path) = &ty.kind else {
                return None;
            };
            match path.segments.last()?.ident.name.as_str() {
                "bool" => match v {
                    Bool(b) => Some(Bool(b)),
                    Int(i) => Some(Bool(i != 0)),
                },
                "u8" | "u16" | "u32" | "u64" | "usize" | "i8" | "i16" | "i32" | "i64" | "isize"
                | "c_char" | "c_int" | "c_long" | "c_longlong" | "c_schar" | "c_short"
                | "c_uchar" | "c_uint" | "c_ulong" | "c_ulonglong" | "c_ushort" => match v {
                    Bool(b) => Some(Int(b as usize)),
                    Int(i) => Some(Int(i)),
                },
                _ => None,
            }
        }
        ExprKind::Lit(l) => {
            if matches!(l.kind, token::LitKind::Integer) {
                l.symbol.as_str().parse().ok().map(Int)
            } else {
                None
            }
        }
        ExprKind::Unary(op, v) => {
            if *op == UnOp::Not {
                if let Some(Bool(b)) = eval_expr(v) {
                    Some(Bool(!b))
                } else {
                    None
                }
            } else {
                None
            }
        }
        ExprKind::Paren(expr) => eval_expr(expr),
        _ => None,
    }
}
