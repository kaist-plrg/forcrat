use std::fmt::Write as _;

use etrace::some_or;
use hir::{intravisit, HirId};
use rustc_ast::{mut_visit::MutVisitor, ptr::P, *};
use rustc_ast_pretty::pprust;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::{self as hir, def::Res, QPath};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};
use rustc_span::{FileName, RealFileName, Span};

use crate::{
    ast_maker::parse_expr,
    compile_util::{self, Pass},
};

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
        let mut visitor = HirVisitor {
            tcx,
            call_span_to_if_args: FxHashMap::default(),
            call_span_to_args: FxHashMap::default(),
            call_span_to_nested_args: FxHashMap::default(),
        };
        tcx.hir_visit_all_item_likes_in_crate(&mut visitor);

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
            let mut visitor = PreprocessVisitor {
                call_span_to_if_args: &visitor.call_span_to_if_args,
                call_span_to_nested_args: &visitor.call_span_to_nested_args,
                updated: false,
            };
            visitor.visit_crate(&mut krate);
            if visitor.updated {
                let s = pprust::crate_to_string_for_macros(&krate);
                files.push((file.name.clone(), s));
            }
        }

        PreprocessResult { files }
    }
}

#[derive(Debug, Clone, Copy)]
struct BoundOccurrence {
    var_id: HirId,
    expr_id: HirId,
}

struct HirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    call_span_to_args: FxHashMap<HirId, Vec<(Span, Vec<BoundOccurrence>)>>,
    call_span_to_nested_args: FxHashMap<Span, Vec<usize>>,
    call_span_to_if_args: FxHashMap<Span, Vec<usize>>,
}

impl HirVisitor<'_> {
    fn find_call_parent(&self, hir_id: HirId) -> HirId {
        for (hir_id, node) in self.tcx.hir().parent_iter(hir_id) {
            if matches!(
                node,
                hir::Node::Expr(hir::Expr {
                    kind: hir::ExprKind::Call(_, _),
                    ..
                })
            ) {
                return hir_id;
            }
        }
        panic!()
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for HirVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        match &expr.kind {
            hir::ExprKind::Call(_, args) => {
                let mut if_args = vec![];
                for (i, arg) in args.iter().enumerate() {
                    if !matches!(arg.kind, hir::ExprKind::If(_, _, _)) {
                        continue;
                    }
                    let typeck = self.tcx.typeck(expr.hir_id.owner.def_id);
                    let ty = typeck.expr_ty(arg);
                    if compile_util::contains_file_ty(ty, self.tcx) {
                        if_args.push(i);
                    }
                }
                if !if_args.is_empty() {
                    self.call_span_to_if_args.insert(expr.span, if_args);
                }
                let args = args.iter().map(|arg| (arg.span, vec![])).collect();
                self.call_span_to_args.insert(expr.hir_id, args);
            }
            hir::ExprKind::Path(QPath::Resolved(_, path)) => {
                if let Res::Local(hir_id) = path.res {
                    let typeck = self.tcx.typeck(expr.hir_id.owner.def_id);
                    let ty = typeck.expr_ty(expr);
                    if compile_util::contains_file_ty(ty, self.tcx) {
                        for v in self.call_span_to_args.values_mut() {
                            for (span, v) in v {
                                if span.contains(expr.span) {
                                    v.push(BoundOccurrence {
                                        var_id: hir_id,
                                        expr_id: expr.hir_id,
                                    });
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }

        intravisit::walk_expr(self, expr);

        if let hir::ExprKind::Call(_, args) = expr.kind {
            let arg_bound_ids = self.call_span_to_args.remove(&expr.hir_id).unwrap();
            let nested_args: Vec<_> = arg_bound_ids
                .iter()
                .enumerate()
                .filter_map(|(i, (_, ids))| {
                    for boi in ids {
                        if self.find_call_parent(boi.expr_id) == expr.hir_id {
                            continue;
                        }
                        for ((_, ids), arg) in arg_bound_ids.iter().zip(args) {
                            if !matches!(arg.kind, hir::ExprKind::Path(QPath::Resolved(_, _))) {
                                continue;
                            }
                            if ids.is_empty() {
                                continue;
                            }
                            let [boj] = &ids[..] else { panic!() };
                            if boi.var_id == boj.var_id {
                                return Some(i);
                            }
                        }
                    }
                    None
                })
                .collect();
            if !nested_args.is_empty() {
                self.call_span_to_nested_args.insert(expr.span, nested_args);
            }
        }
    }
}

struct PreprocessVisitor<'a> {
    call_span_to_if_args: &'a FxHashMap<Span, Vec<usize>>,
    call_span_to_nested_args: &'a FxHashMap<Span, Vec<usize>>,
    updated: bool,
}

impl MutVisitor for PreprocessVisitor<'_> {
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
        let expr_span = expr.span;
        if let ExprKind::Call(_, args) = &mut expr.kind {
            let mut indices: Vec<usize> = vec![];
            if let Some(if_args) = self.call_span_to_if_args.get(&expr_span) {
                indices.extend(if_args);
            }
            if let Some(nested_args) = self.call_span_to_nested_args.get(&expr_span) {
                indices.extend(nested_args);
            }
            if !indices.is_empty() {
                self.updated = true;
                indices.sort();
                indices.dedup();
                let mut new_expr = "{".to_string();
                for i in indices {
                    let a = pprust::expr_to_string(&args[i]);
                    write!(new_expr, "let __arg_{} = {};", i, a).unwrap();
                    *args[i] = expr!("__arg_{}", i);
                }
                new_expr.push_str(&pprust::expr_to_string(expr));
                new_expr.push('}');
                **expr = expr!("{}", new_expr);
            }
        }
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
