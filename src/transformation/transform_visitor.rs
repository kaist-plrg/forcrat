use std::{
    ops::{Deref, DerefMut},
    sync::Arc,
};

use etrace::some_or;
use rustc_ast::{
    ast::*,
    mut_visit::{self, MutVisitor},
    ptr::P,
    token::TokenKind,
    tokenstream::{
        AttrTokenStream, AttrTokenTree, AttrsTarget, LazyAttrTokenStream, TokenStream, TokenTree,
    },
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{self as hir};
use rustc_lexer::unescape;
use rustc_middle::ty::TyCtxt;
use rustc_span::{def_id::LocalDefId, symbol::Ident, Span, Symbol};

use super::*;
use crate::{
    api_list::{self, Permission},
    ast_maker::*,
    compile_util, file_analysis,
    likely_lit::LikelyLit,
};

pub(super) struct TransformVisitor<'tcx, 'a> {
    pub(super) tcx: TyCtxt<'tcx>,
    pub(super) analysis_res: &'a file_analysis::AnalysisResult,
    pub(super) hir: &'a HirCtx,

    /// function parameter to HIR location
    pub(super) param_to_loc: &'a FxHashMap<Parameter, HirLoc>,
    /// HIR location to permissions and origins
    pub(super) loc_to_pot: &'a FxHashMap<HirLoc, Pot<'a>>,
    /// user-defined API functions' signatures' spans
    pub(super) api_ident_spans: &'a FxHashSet<Span>,
    /// uncopiable struct ident spans
    pub(super) uncopiable: &'a FxHashSet<Span>,

    /// unsupported expr spans
    pub(super) unsupported: &'a FxHashSet<Span>,
    /// unsupported return fn ids
    pub(super) unsupported_returns: &'a FxHashSet<LocalDefId>,
    /// is stdin unsupported
    pub(super) is_stdin_unsupported: bool,
    /// is stdout unsupported
    #[allow(unused)]
    pub(super) is_stdout_unsupported: bool,
    /// is stderr unsupported
    #[allow(unused)]
    pub(super) is_stderr_unsupported: bool,

    /// is this file updated
    pub(super) updated: bool,
    pub(super) tmpfile: bool,
    pub(super) current_fn: Option<LocalDefId>,
    pub(super) bounds: Vec<TraitBound>,
}

fn remove_cast(expr: &Expr) -> &Expr {
    let ExprKind::Cast(expr, _) = &expr.kind else { return expr };
    remove_cast(expr)
}

#[derive(Debug, Clone, Copy)]
struct FprintfCtx<'a> {
    wide: bool,
    retval_used: bool,
    ic: IndicatorCheck<'a>,
}

impl<'a> TransformVisitor<'_, 'a> {
    #[inline]
    fn is_unsupported(&self, expr: &Expr) -> bool {
        self.unsupported.contains(&expr.span) || self.unsupported.contains(&remove_cast(expr).span)
    }

    #[inline]
    fn transform_fprintf<S: StreamExpr, E: Deref<Target = Expr>>(
        &self,
        stream: &S,
        fmt: &Expr,
        args: &[E],
        ctx: FprintfCtx<'_>,
    ) -> Expr {
        match LikelyLit::from_expr(fmt) {
            LikelyLit::Lit(fmt) => transform_fprintf_lit(stream, fmt, args, ctx),
            LikelyLit::If(_, _, _) => todo!("{:?}", fmt.span),
            LikelyLit::Path(_, span) => {
                let loc = self.hir.bound_span_to_loc[&span];
                let static_span = self.hir.loc_to_binding_span[&loc];
                let fmt = self.analysis_res.static_span_to_lit[&static_span];
                transform_fprintf_lit(stream, fmt, args, ctx)
            }
            LikelyLit::Other(e) => todo!("{:?}", e),
        }
    }

    #[inline]
    fn param_pot(&self, param: Parameter) -> Option<Pot<'a>> {
        let loc = self.param_to_loc.get(&param)?;
        self.loc_to_pot.get(loc).copied()
    }

    #[inline]
    fn bound_pot(&self, span: Span) -> Option<Pot<'a>> {
        let loc = self.hir.bound_span_to_loc.get(&span)?;
        self.loc_to_pot.get(loc).copied()
    }

    #[inline]
    fn binding_pot(&self, span: Span) -> Option<Pot<'a>> {
        let loc = self.hir.binding_span_to_loc.get(&span)?;
        self.loc_to_pot.get(loc).copied()
    }

    #[inline]
    fn return_pot(&self, func: LocalDefId) -> Option<Pot<'a>> {
        if self.unsupported_returns.contains(&func) {
            return None;
        }
        self.loc_to_pot.get(&HirLoc::Return(func)).copied()
    }

    #[inline]
    fn indicator_check(&self, span: Span) -> IndicatorCheck<'_> {
        let curr_func = self.hir.callee_span_to_hir_id[&span].owner.def_id;
        let name = self.hir.callee_span_to_stream_name.get(&span).unwrap();
        let eof = self
            .hir
            .feof_functions
            .get(&curr_func)
            .is_some_and(|s| s.contains(name));
        let error = self
            .hir
            .ferror_functions
            .get(&curr_func)
            .is_some_and(|s| s.contains(name));
        IndicatorCheck {
            name: name.as_str(),
            eof,
            error,
        }
    }

    #[inline]
    fn indicator_check_std<'s>(&self, span: Span, name: &'s str) -> IndicatorCheck<'s> {
        let curr_func = self.hir.callee_span_to_hir_id[&span].owner.def_id;
        let eof = self
            .hir
            .feof_functions
            .get(&curr_func)
            .is_some_and(|s| s.iter().any(|n| n.as_str() == name));
        let error = self
            .hir
            .ferror_functions
            .get(&curr_func)
            .is_some_and(|s| s.iter().any(|n| n.as_str() == name));
        IndicatorCheck { name, eof, error }
    }

    #[inline]
    fn replace_expr(&mut self, old: &mut Expr, new: Expr) {
        self.updated = true;
        let span = old.span;
        *old = new;
        old.span = span;
    }

    #[inline]
    fn replace_ty_with_pot(&mut self, old: &mut Ty, pot: Pot<'_>) {
        if let Some(bound) = pot.ty.get_dyn_bound() {
            if bound.count() > 1 {
                self.bounds.push(bound);
            }
        }
        self.replace_ty(old, ty!("{}", pot.ty));
    }

    #[inline]
    fn replace_ty(&mut self, old: &mut Ty, new: Ty) {
        self.updated = true;
        let span = old.span;
        *old = new;
        old.span = span;
    }

    #[inline]
    fn replace_ident(&mut self, old: &mut Ident, new: Ident) {
        self.updated = true;
        let span = old.span;
        *old = new;
        old.span = span;
    }

    #[inline]
    fn is_non_local(&self, span: Span) -> bool {
        matches!(
            self.hir.bound_span_to_loc.get(&span),
            Some(HirLoc::Global(_) | HirLoc::Field(_, _))
        )
    }

    fn convert_rhs(&mut self, rhs: &mut Expr, lhs_pot: Pot<'_>, consume: bool) {
        let rhs_span = rhs.span;
        let is_non_local = self.is_non_local(rhs_span);
        if let Some(rhs_pot) = self.bound_pot(rhs.span) {
            let rhs_str = pprust::expr_to_string(rhs);
            let new_rhs = convert_expr(*lhs_pot.ty, *rhs_pot.ty, &rhs_str, consume, is_non_local);
            let new_rhs = expr!("{}", new_rhs);
            self.replace_expr(rhs, new_rhs);
        } else if let Some(def_id) = self.hir.call_span_to_callee_id.get(&rhs_span) {
            let name = compile_util::def_id_to_value_symbol(*def_id, self.tcx).unwrap();
            let name = api_list::normalize_api_name(name.as_str());
            let rhs_str = pprust::expr_to_string(rhs);
            let rhs_ty = match name {
                "fopen" | "tmpfile" => StreamType::Option(&FILE_TY),
                "fdopen" => FILE_TY,
                "popen" => {
                    if rhs_str.contains("child.stdin") {
                        StreamType::Option(&StreamType::ChildStdin)
                    } else if rhs_str.contains("child.stdout") {
                        StreamType::Option(&StreamType::ChildStdout)
                    } else {
                        panic!("{}", rhs_str)
                    }
                }
                _ => *self.return_pot(*def_id).unwrap().ty,
            };
            let new_rhs = convert_expr(*lhs_pot.ty, rhs_ty, &rhs_str, consume, is_non_local);
            let new_rhs = expr!("{}", new_rhs);
            self.replace_expr(rhs, new_rhs);
        } else {
            match &mut rhs.kind {
                ExprKind::If(_, t, Some(f)) => {
                    let StmtKind::Expr(t) = &mut t.stmts.last_mut().unwrap().kind else { panic!() };
                    self.convert_rhs(t, lhs_pot, consume);

                    let ExprKind::Block(f, _) = &mut f.kind else { panic!() };
                    let StmtKind::Expr(f) = &mut f.stmts.last_mut().unwrap().kind else { panic!() };
                    self.convert_rhs(f, lhs_pot, consume);
                }
                ExprKind::Cast(_, _) => {
                    assert!(matches!(remove_cast(rhs).kind, ExprKind::Lit(_)));
                    match lhs_pot.ty {
                        StreamType::Option(_) => {
                            self.replace_expr(rhs, expr!("None"));
                        }
                        StreamType::Ptr(_) => {
                            self.replace_expr(rhs, expr!("std::ptr::null_mut()"));
                        }
                        _ => panic!(),
                    }
                }
                _ => panic!("{:?}", rhs),
            }
        }
    }
}

impl MutVisitor for TransformVisitor<'_, '_> {
    fn visit_item(&mut self, item: &mut P<Item>) {
        if self.api_ident_spans.contains(&item.ident.span) {
            return;
        }

        if let Some(HirLoc::Global(def_id)) = self.hir.binding_span_to_loc.get(&item.ident.span) {
            self.current_fn = Some(*def_id);
        }

        mut_visit::walk_item(self, item);

        let ident_span = item.ident.span;
        match &mut item.kind {
            ItemKind::Static(box item) => {
                let body = some_or!(&mut item.expr, return);
                if self.unsupported.contains(&body.span) {
                    return;
                }
                let loc = self.hir.binding_span_to_loc[&ident_span];
                let pot = some_or!(self.loc_to_pot.get(&loc), return);
                self.replace_ty_with_pot(&mut item.ty, *pot);
                self.convert_rhs(body, *pot, true);
            }
            ItemKind::Fn(box item) => {
                let HirLoc::Global(def_id) = self.hir.binding_span_to_loc[&ident_span] else {
                    panic!()
                };
                let mut tparams = vec![];
                for (i, param) in item.sig.decl.inputs.iter_mut().enumerate() {
                    if self.unsupported.contains(&param.pat.span) {
                        continue;
                    }
                    let p = Parameter::new(def_id, i);
                    let pot = some_or!(self.param_pot(p), continue);
                    if let StreamType::Option(StreamType::Impl(bound)) = pot.ty {
                        self.replace_ty(&mut param.ty, ty!("Option<TT{}>", i));
                        tparams.push((i, *bound));
                    } else {
                        self.replace_ty_with_pot(&mut param.ty, pot);
                    }
                    if let PatKind::Ident(BindingMode(_, m), _, _) = &mut param.pat.kind {
                        *m = Mutability::Mut;
                    }
                }
                for (i, bound) in tparams {
                    let tparam = if bound.is_empty() {
                        ty_param!("TT{}", i)
                    } else {
                        ty_param!("TT{}: {}", i, bound)
                    };
                    item.generics.params.push(tparam);
                }
                if let Some(pot) = self.return_pot(def_id) {
                    let FnRetTy::Ty(ty) = &mut item.sig.decl.output else { panic!() };
                    self.replace_ty_with_pot(ty, pot);
                }
                if let Some(eofs) = self.hir.feof_functions.get(&def_id) {
                    let stmts = &mut item.body.as_mut().unwrap().stmts;
                    for eof in eofs {
                        let stmt = stmt!("let mut {}_eof = 0;", eof);
                        stmts.insert(0, stmt);
                    }
                }
                if let Some(errors) = self.hir.ferror_functions.get(&def_id) {
                    let stmts = &mut item.body.as_mut().unwrap().stmts;
                    for error in errors {
                        let stmt = stmt!("let mut {}_error = 0;", error);
                        stmts.insert(0, stmt);
                    }
                }
            }
            ItemKind::Struct(_, _) | ItemKind::Union(_, _) => {
                if self.uncopiable.contains(&item.ident.span) {
                    for attr in &mut item.attrs {
                        let AttrKind::Normal(attr) = &mut attr.kind else { continue };
                        let AttrArgs::Delimited(args) = &mut attr.item.args else { continue };
                        let mut tokens = vec![];
                        let mut remove_comma = false;
                        for tree in args.tokens.iter() {
                            if let TokenTree::Token(token, _) = tree {
                                match token.kind {
                                    TokenKind::Ident(symbol, _) => {
                                        let name = symbol.as_str();
                                        if name == "Copy" || name == "Clone" {
                                            remove_comma = true;
                                            continue;
                                        }
                                    }
                                    TokenKind::Comma => {
                                        if remove_comma {
                                            remove_comma = false;
                                            continue;
                                        }
                                    }
                                    _ => {}
                                }
                            }
                            tokens.push(tree.clone());
                        }
                        args.tokens = TokenStream::new(tokens);
                    }
                }
            }
            _ => {}
        }
    }

    fn visit_variant_data(&mut self, vd: &mut VariantData) {
        walk_variant_data(self, vd);

        let VariantData::Struct { fields, .. } = vd else { return };
        for f in fields {
            if self.unsupported.contains(&f.span) {
                continue;
            }
            let pot = some_or!(self.binding_pot(f.span), continue);
            self.replace_ty_with_pot(&mut f.ty, pot);
        }
    }

    fn visit_local(&mut self, local: &mut P<Local>) {
        walk_local(self, local);

        if self.unsupported.contains(&local.pat.span) {
            return;
        }

        let pot = some_or!(self.binding_pot(local.pat.span), return);
        self.replace_ty_with_pot(local.ty.as_mut().unwrap(), pot);

        let LocalKind::Init(rhs) = &mut local.kind else { return };
        self.convert_rhs(rhs, pot, true);
    }

    fn visit_expr(&mut self, expr: &mut P<Expr>) {
        mut_visit::walk_expr(self, expr);

        let expr_span = expr.span;
        if self.is_unsupported(expr) {
            return;
        }
        match &mut expr.kind {
            ExprKind::Call(callee, args) => {
                let Some(HirLoc::Global(def_id)) = self.hir.bound_span_to_loc.get(&callee.span)
                else {
                    return;
                };
                let name = compile_util::def_id_to_value_symbol(*def_id, self.tcx).unwrap();
                let name = api_list::normalize_api_name(name.as_str());
                match name {
                    "fopen" => {
                        let new_expr = transform_fopen(&args[0], &args[1]);
                        self.replace_expr(expr, new_expr);
                    }
                    "fdopen" => {
                        let new_expr = transform_fdopen(&args[0]);
                        self.replace_expr(expr, new_expr);
                    }
                    "tmpfile" => {
                        let new_expr = transform_tmpfile();
                        self.replace_expr(expr, new_expr);
                        self.tmpfile = true;
                    }
                    "popen" => {
                        let new_expr = transform_popen(&args[0], &args[1]);
                        self.replace_expr(expr, new_expr);
                    }
                    "fclose" | "pclose" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let is_non_local = self.is_non_local(args[0].span);
                        let new_expr = transform_fclose(&args[0], *ty, is_non_local);
                        self.replace_expr(expr, new_expr);
                    }
                    "fscanf" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let ic = self.indicator_check(callee.span);
                        let new_expr = transform_fscanf(&stream, &args[1], &args[2..], ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "fgetc" | "getc" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let ic = self.indicator_check(callee.span);
                        let new_expr = transform_fgetc(&stream, ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "getchar" => {
                        if self.is_stdin_unsupported {
                            return;
                        }
                        let stream = StdExpr::stdin();
                        let ic = self.indicator_check_std(callee.span, "stdin");
                        let new_expr = transform_fgetc(&stream, ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "fgets" => {
                        if self.is_unsupported(&args[2]) {
                            return;
                        }
                        let ty = self.bound_pot(args[2].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[2], ty);
                        let ic = self.indicator_check(callee.span);
                        let new_expr = transform_fgets(&stream, &args[0], &args[1], ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "fread" => {
                        if self.is_unsupported(&args[3]) {
                            return;
                        }
                        let ty = self.bound_pot(args[3].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[3], ty);
                        let ic = self.indicator_check(callee.span);
                        let new_expr = transform_fread(&stream, &args[0], &args[1], &args[2], ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "getdelim" => todo!(),
                    "getline" => todo!(),
                    "feof" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let name = self.hir.callee_span_to_stream_name[&callee.span];
                        let new_expr = expr!("{}_eof", name);
                        self.replace_expr(expr, new_expr);
                    }
                    "ferror" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let name = self.hir.callee_span_to_stream_name[&callee.span];
                        let new_expr = expr!("{}_error", name);
                        self.replace_expr(expr, new_expr);
                    }
                    "clearerr" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ic = self.indicator_check(callee.span);
                        let new_expr = expr!("{}", ic.clear());
                        self.replace_expr(expr, new_expr);
                    }
                    "fprintf" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let retval_used = self.hir.retval_used_spans.contains(&expr_span);
                        let ic = self.indicator_check(callee.span);
                        let ctx = FprintfCtx {
                            wide: false,
                            retval_used,
                            ic,
                        };
                        let new_expr = self.transform_fprintf(&stream, &args[1], &args[2..], ctx);
                        self.replace_expr(expr, new_expr);
                    }
                    "printf" => {
                        // if self.is_stdout_unsupported {
                        //     return;
                        // }
                        if self
                            .analysis_res
                            .unsupported_printf_spans
                            .contains(&expr_span)
                        {
                            return;
                        }
                        let stream = StdExpr::stdout();
                        let retval_used = self.hir.retval_used_spans.contains(&expr_span);
                        let ic = self.indicator_check_std(callee.span, "stdout");
                        let ctx = FprintfCtx {
                            wide: false,
                            retval_used,
                            ic,
                        };
                        let new_expr = self.transform_fprintf(&stream, &args[0], &args[1..], ctx);
                        self.replace_expr(expr, new_expr);
                    }
                    "wprintf" => {
                        // if self.is_stdout_unsupported {
                        //     return;
                        // }
                        if self
                            .analysis_res
                            .unsupported_printf_spans
                            .contains(&expr_span)
                        {
                            return;
                        }
                        let stream = StdExpr::stdout();
                        let retval_used = self.hir.retval_used_spans.contains(&expr_span);
                        let ic = self.indicator_check_std(callee.span, "stdout");
                        let ctx = FprintfCtx {
                            wide: true,
                            retval_used,
                            ic,
                        };
                        let new_expr = self.transform_fprintf(&stream, &args[0], &args[1..], ctx);
                        self.replace_expr(expr, new_expr);
                    }
                    "fputc" | "putc" => {
                        if self.is_unsupported(&args[1]) {
                            return;
                        }
                        let ty = self.bound_pot(args[1].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[1], ty);
                        let ic = self.indicator_check(callee.span);
                        let new_expr = transform_fputc(&stream, &args[0], ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "putchar" => {
                        // if self.is_stdout_unsupported {
                        //     return;
                        // }
                        let stream = StdExpr::stdout();
                        let ic = self.indicator_check_std(callee.span, "stdout");
                        let new_expr = transform_fputc(&stream, &args[0], ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "fputs" => {
                        if self.is_unsupported(&args[1]) {
                            return;
                        }
                        let ty = self.bound_pot(args[1].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[1], ty);
                        let ic = self.indicator_check(callee.span);
                        let new_expr = transform_fputs(&stream, &args[0], ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "puts" => {
                        // if self.is_stdout_unsupported {
                        //     return;
                        // }
                        let ic = self.indicator_check_std(callee.span, "stdout");
                        let new_expr = transform_puts(&args[0], ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "fwrite" => {
                        if self.is_unsupported(&args[3]) {
                            return;
                        }
                        let ty = self.bound_pot(args[3].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[3], ty);
                        let ic = self.indicator_check(callee.span);
                        let new_expr = transform_fwrite(&stream, &args[0], &args[1], &args[2], ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "fflush" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let ic = self.indicator_check(callee.span);
                        let new_expr = transform_fflush(&stream, ic);
                        self.replace_expr(expr, new_expr);
                    }
                    "fseek" | "fseeko" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let new_expr = transform_fseek(&stream, &args[1], &args[2]);
                        self.replace_expr(expr, new_expr);
                    }
                    "ftell" | "ftello" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let new_expr = transform_ftell(&stream);
                        self.replace_expr(expr, new_expr);
                    }
                    "rewind" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let new_expr = transform_rewind(&stream);
                        self.replace_expr(expr, new_expr);
                    }
                    "fgetpos" => todo!(),
                    "fsetpos" => todo!(),
                    "fileno" => {
                        if self.is_unsupported(&args[0]) {
                            return;
                        }
                        let ty = self.bound_pot(args[0].span).unwrap().ty;
                        let stream = TypedExpr::new(&args[0], ty);
                        let new_expr = transform_fileno(&stream);
                        self.replace_expr(expr, new_expr);
                    }
                    _ => {
                        let hir::Node::Item(item) = self.tcx.hir_node_by_def_id(*def_id) else {
                            return;
                        };
                        let hir::ItemKind::Fn { sig, .. } = item.kind else { panic!() };
                        let mut targs = vec![];
                        for (i, arg) in args[..sig.decl.inputs.len()].iter_mut().enumerate() {
                            if self.is_unsupported(arg) {
                                continue;
                            }
                            let p = Parameter::new(*def_id, i);
                            let param_pot = some_or!(self.param_pot(p), continue);
                            let is_null = matches!(remove_cast(arg).kind, ExprKind::Lit(_));
                            let permissions = param_pot.permissions;
                            let consume = permissions.contains(Permission::Close)
                                || matches!(
                                    arg.kind,
                                    ExprKind::Call(_, _) | ExprKind::MethodCall(_)
                                );
                            self.convert_rhs(arg, param_pot, consume);
                            if param_pot.ty.contains_impl() {
                                if is_null {
                                    let targ = if permissions.contains(Permission::BufRead) {
                                        "std::io::BufReader<std::fs::File>"
                                    } else {
                                        "std::fs::File"
                                    };
                                    targs.push(targ);
                                } else {
                                    targs.push("_");
                                }
                            }
                        }
                        if targs.iter().any(|targ| *targ != "_") {
                            let c = pprust::expr_to_string(callee);
                            let new_expr = expr!("{}::<{}>", c, targs.join(", "));
                            self.replace_expr(callee, new_expr);
                        }
                        if let Some(nested_args) = self.hir.call_span_to_nested_args.get(&expr_span)
                        {
                            println!("Nested");
                            let mut new_expr = "{".to_string();
                            for i in nested_args {
                                let a = pprust::expr_to_string(&args[*i]);
                                write!(new_expr, "let __arg_{} = {};", i, a).unwrap();
                                self.replace_expr(&mut args[*i], expr!("__arg_{}", i));
                            }
                            new_expr.push_str(&pprust::expr_to_string(expr));
                            new_expr.push('}');
                            self.replace_expr(expr, expr!("{}", new_expr));
                        }
                    }
                }
            }
            ExprKind::Path(None, path) => {
                if let [seg] = &path.segments[..] {
                    let name = seg.ident.name.as_str();
                    if (name == "stdin" && !self.is_stdin_unsupported)
                        || name == "stdout"
                        || name == "stderr"
                    {
                        let new_expr = expr!("std::io::{}()", name);
                        self.replace_expr(expr, new_expr);
                    }
                }
            }
            ExprKind::MethodCall(box MethodCall { receiver, seg, .. }) => {
                if self.is_unsupported(receiver) {
                    return;
                }
                let ty = some_or!(self.bound_pot(receiver.span), return).ty;
                match ty {
                    StreamType::ManuallyDrop(StreamType::Option(_)) | StreamType::Option(_) => {
                        self.replace_ident(&mut seg.ident, Ident::from_str("is_none"));
                    }
                    StreamType::Ptr(_) => {}
                    _ => panic!(),
                }
            }
            ExprKind::Assign(lhs, rhs, _) => {
                let lhs_pot = some_or!(self.bound_pot(lhs.span), return);
                self.convert_rhs(rhs, lhs_pot, true);
            }
            ExprKind::Struct(se) => {
                for f in se.fields.iter_mut() {
                    let lhs_pot = some_or!(self.bound_pot(f.ident.span), continue);
                    self.convert_rhs(&mut f.expr, lhs_pot, true);
                }
            }
            ExprKind::Ret(Some(e)) => {
                let Some(pot) = self.return_pot(self.current_fn.unwrap()) else { return };
                self.convert_rhs(e, pot, true);
            }
            _ => {}
        }
    }
}

fn walk_local<T: MutVisitor>(vis: &mut T, local: &mut P<Local>) {
    let Local {
        id,
        pat,
        ty,
        kind,
        span,
        colon_sp,
        attrs,
        tokens,
    } = local.deref_mut();
    vis.visit_id(id);
    visit_attrs(vis, attrs);
    vis.visit_pat(pat);
    visit_opt(ty, |ty| vis.visit_ty(ty));
    match kind {
        LocalKind::Decl => {}
        LocalKind::Init(init) => {
            vis.visit_expr(init);
        }
        LocalKind::InitElse(init, els) => {
            vis.visit_expr(init);
            vis.visit_block(els);
        }
    }
    visit_lazy_tts(vis, tokens);
    visit_opt(colon_sp, |sp| vis.visit_span(sp));
    vis.visit_span(span);
}

#[inline]
fn visit_opt<T, F>(opt: &mut Option<T>, mut visit_elem: F)
where F: FnMut(&mut T) {
    if let Some(elem) = opt {
        visit_elem(elem);
    }
}

#[inline]
fn visit_attrs<T: MutVisitor>(vis: &mut T, attrs: &mut AttrVec) {
    for attr in attrs.iter_mut() {
        vis.visit_attribute(attr);
    }
}

fn visit_lazy_tts_opt_mut<T: MutVisitor>(vis: &mut T, lazy_tts: Option<&mut LazyAttrTokenStream>) {
    if T::VISIT_TOKENS {
        if let Some(lazy_tts) = lazy_tts {
            let mut tts = lazy_tts.to_attr_token_stream();
            visit_attr_tts(vis, &mut tts);
            *lazy_tts = LazyAttrTokenStream::new(tts);
        }
    }
}

#[inline]
fn visit_lazy_tts<T: MutVisitor>(vis: &mut T, lazy_tts: &mut Option<LazyAttrTokenStream>) {
    visit_lazy_tts_opt_mut(vis, lazy_tts.as_mut());
}

fn visit_attr_tts<T: MutVisitor>(vis: &mut T, AttrTokenStream(tts): &mut AttrTokenStream) {
    if T::VISIT_TOKENS && !tts.is_empty() {
        let tts = Arc::make_mut(tts);
        visit_vec(tts, |tree| visit_attr_tt(vis, tree));
    }
}

fn visit_attr_tt<T: MutVisitor>(vis: &mut T, tt: &mut AttrTokenTree) {
    match tt {
        AttrTokenTree::Token(token, _spacing) => {
            mut_visit::visit_token(vis, token);
        }
        AttrTokenTree::Delimited(dspan, _spacing, _delim, tts) => {
            visit_attr_tts(vis, tts);
            mut_visit::visit_delim_span(vis, dspan);
        }
        AttrTokenTree::AttrsTarget(AttrsTarget { attrs, tokens }) => {
            visit_attrs(vis, attrs);
            visit_lazy_tts_opt_mut(vis, Some(tokens));
        }
    }
}

#[inline]
fn visit_vec<T, F>(elems: &mut Vec<T>, mut visit_elem: F)
where F: FnMut(&mut T) {
    for elem in elems {
        visit_elem(elem);
    }
}

fn walk_variant_data<T: MutVisitor>(vis: &mut T, vdata: &mut VariantData) {
    use rustc_data_structures::flat_map_in_place::FlatMapInPlace;
    match vdata {
        VariantData::Struct {
            fields,
            recovered: _,
        } => {
            fields.flat_map_in_place(|field| vis.flat_map_field_def(field));
        }
        VariantData::Tuple(fields, id) => {
            vis.visit_id(id);
            fields.flat_map_in_place(|field| vis.flat_map_field_def(field));
        }
        VariantData::Unit(id) => vis.visit_id(id),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OpenMode {
    Read(bool),
    Write(bool),
    Append(bool),
    Unknown,
}

impl OpenMode {
    fn from_lit(mode: Symbol) -> Self {
        let (prefix, suffix) = mode.as_str().split_at(1);
        let plus = suffix.contains('+');
        match prefix {
            "r" => Self::Read(plus),
            "w" => Self::Write(plus),
            "a" => Self::Append(plus),
            _ => panic!("{:?}", mode),
        }
    }

    fn from_likely_lit(mode: &LikelyLit<'_>) -> Self {
        match mode {
            LikelyLit::Lit(mode) => Self::from_lit(*mode),
            LikelyLit::If(_, t, f) => {
                let t = Self::from_likely_lit(t);
                let f = Self::from_likely_lit(f);
                if t == f {
                    t
                } else {
                    Self::Unknown
                }
            }
            LikelyLit::Path(_, _) => Self::Unknown,
            LikelyLit::Other(_) => todo!(),
        }
    }

    fn make_expr(self, path: &Expr, mode: &Expr) -> Expr {
        let path = pprust::expr_to_string(path);
        let path = format!(
            "std::ffi::CStr::from_ptr(({}) as _).to_str().unwrap()",
            path
        );
        match self {
            Self::Read(plus) => {
                if plus {
                    expr!(
                        "std::fs::OpenOptions::new()
                            .read(true)
                            .write(true)
                            .open({})
                            .ok()",
                        path,
                    )
                } else {
                    expr!("std::fs::File::open({}).ok()", path)
                }
            }
            Self::Write(plus) => {
                if plus {
                    expr!(
                        "std::fs::OpenOptions::new()
                            .write(true)
                            .create(true)
                            .truncate(true)
                            .read(true)
                            .open({})
                            .ok()",
                        path,
                    )
                } else {
                    expr!("std::fs::File::create({}).ok()", path)
                }
            }
            Self::Append(plus) => {
                if plus {
                    expr!(
                        "std::fs::OpenOptions::new()
                            .append(true)
                            .create(true)
                            .read(true)
                            .open({})
                            .ok()",
                        path,
                    )
                } else {
                    expr!(
                        "std::fs::OpenOptions::new()
                            .append(true)
                            .create(true)
                            .open({})
                            .ok()",
                        path,
                    )
                }
            }
            Self::Unknown => {
                expr!(
                    r#"{{
    let pathname = {};
    let mode = std::ffi::CStr::from_ptr(({}) as _).to_str().unwrap();
    let (prefix, suffix) = mode.split_at(1);
    match prefix {{
        "r" => {{
            if suffix.contains('+') {{
                std::fs::OpenOptions::new().read(true).write(true).open(pathname)
            }} else {{
                std::fs::File::open(pathname)
            }}
        }}
        "w" => {{
            if suffix.contains('+') {{
                std::fs::OpenOptions::new()
                    .write(true)
                    .create(true)
                    .truncate(true)
                    .read(true)
                    .open(pathname)
            }} else {{
                std::fs::File::create(pathname)
            }}
        }}
        "a" => {{
            if suffix.contains('+') {{
                std::fs::OpenOptions::new()
                    .append(true)
                    .create(true)
                    .read(true)
                    .open(pathname)
            }} else {{
                std::fs::OpenOptions::new().append(true).create(true).open(pathname)
            }}
        }}
        _ => panic!(),
    }}.ok()
}}"#,
                    path,
                    pprust::expr_to_string(mode),
                )
            }
        }
    }
}

fn transform_fopen(path: &Expr, mode_expr: &Expr) -> Expr {
    let mode = LikelyLit::from_expr(mode_expr);
    match mode {
        LikelyLit::Lit(mode) => {
            let mode = OpenMode::from_lit(mode);
            mode.make_expr(path, mode_expr)
        }
        LikelyLit::If(c, t, f) => {
            let t = OpenMode::from_likely_lit(&t);
            let f = OpenMode::from_likely_lit(&f);
            if t == f {
                t.make_expr(path, mode_expr)
            } else {
                let t = t.make_expr(path, mode_expr);
                let f = f.make_expr(path, mode_expr);
                let c = pprust::expr_to_string(c);
                let t = pprust::expr_to_string(&t);
                let f = pprust::expr_to_string(&f);
                expr!("if {} {{ {} }} else {{ {} }}", c, t, f)
            }
        }
        LikelyLit::Path(_, _) => OpenMode::Unknown.make_expr(path, mode_expr),
        LikelyLit::Other(_) => todo!(),
    }
}

#[inline]
fn transform_fdopen(fd: &Expr) -> Expr {
    let fd = pprust::expr_to_string(fd);
    expr!("std::os::fd::FromRawFd::from_raw_fd({})", fd)
}

#[inline]
fn transform_tmpfile() -> Expr {
    expr!("tempfile::tempfile().ok()")
}

fn transform_popen(command: &Expr, mode: &Expr) -> Expr {
    let command = pprust::expr_to_string(command);
    let command = format!(
        "std::ffi::CStr::from_ptr(({}) as _).to_str().unwrap()",
        command
    );
    let mode = LikelyLit::from_expr(mode);
    match file_analysis::is_popen_read(&mode) {
        Some(read) => {
            let field = if read { "stdout" } else { "stdin" };
            expr!(
                r#"std::process::Command::new("sh")
                .arg("-c")
                .arg("--")
                .arg({})
                .{1}(std::process::Stdio::piped())
                .spawn()
                .ok()
                .and_then(|child| child.{1})"#,
                command,
                field
            )
        }
        None => todo!("{:?}", mode),
    }
}

fn transform_fclose(stream: &Expr, ty: StreamType<'_>, is_non_local: bool) -> Expr {
    let stream = pprust::expr_to_string(stream);
    match ty {
        StreamType::Ref(_) | StreamType::Ptr(_) => panic!(),
        StreamType::Option(_) => {
            if is_non_local {
                expr!("{{ drop(({}).take().unwrap()); 0 }}", stream)
            } else {
                expr!("{{ drop(({}).unwrap()); 0 }}", stream)
            }
        }
        StreamType::ManuallyDrop(StreamType::Option(_)) => expr!(
            "{{ drop(std::mem::ManuallyDrop::take(&mut ({})).take().unwrap()); 0 }}",
            stream
        ),
        StreamType::ManuallyDrop(_) => {
            expr!(
                "{{ drop(std::mem::ManuallyDrop::take(&mut ({}))); 0 }}",
                stream
            )
        }
        _ => expr!("{{ drop({}); 0 }}", stream),
    }
}

fn transform_fscanf<S: StreamExpr, E: Deref<Target = Expr>>(
    stream: &S,
    fmt: &Expr,
    args: &[E],
    ic: IndicatorCheck<'_>,
) -> Expr {
    assert!(!ic.has_check());
    let stream = stream.borrow_for(StreamTrait::BufRead);
    let fmt = LikelyLit::from_expr(fmt);
    match fmt {
        LikelyLit::Lit(fmt) => {
            let fmt = fmt.to_string().into_bytes();
            let specs = scanf::parse_specs(&fmt);
            let mut i = 0;
            let mut code = String::new();
            for spec in specs {
                let arg = if spec.assign {
                    i += 1;
                    Some(pprust::expr_to_string(&args[i - 1]))
                } else {
                    None
                };
                let check_width = if let Some(width) = spec.width {
                    format!("if chars.len() == {} {{ break; }}", width)
                } else {
                    "".to_string()
                };
                if let Some(_scan_set) = spec.scan_set() {
                    todo!();
                } else {
                    let assign = if let Some(arg) = arg {
                        let ty = spec.ty();
                        if ty == "&str" {
                            format!(
                                "
    let bytes = s.as_bytes();
    let buf: &mut [u8] = std::slice::from_raw_parts_mut(({}) as _, bytes.len() + 1);
    buf.copy_from_slice(bytes);
    buf[bytes.len()] = 0;",
                                arg
                            )
                        } else {
                            format!(
                                "
    *(({}) as *mut {}) = s.parse().unwrap();
    count += 1;",
                                arg, ty
                            )
                        }
                    } else {
                        "".to_string()
                    };
                    write!(
                        code,
                        "{{
    let mut chars = vec![];
    loop {{
        {}
        let available = match stream.fill_buf() {{
            Ok(buf) => buf,
            Err(_) => break,
        }};
        if available.is_empty() {{
            break;
        }}
        let c = available[0];
        if !c.is_ascii_whitespace() {{
            chars.push(c);
        }} else if !chars.is_empty() {{
            break;
        }}
        stream.consume(1);
    }}
    let s = String::from_utf8(chars).unwrap();
    {}
}}",
                        check_width, assign
                    )
                    .unwrap();
                }
            }
            expr!(
                "{{
    use std::io::BufRead;
    let mut stream = {};
    let mut count = 0i32;
    {}
    count
}}",
                stream,
                code
            )
        }
        LikelyLit::If(_, _, _) => todo!(),
        LikelyLit::Path(_, _) => todo!(),
        LikelyLit::Other(_) => todo!(),
    }
}

#[inline]
fn transform_fgetc<S: StreamExpr>(stream: &S, ic: IndicatorCheck<'_>) -> Expr {
    let stream_str = stream.borrow_for(StreamTrait::Read);
    if ic.has_check() {
        expr!(
            "{{
    use std::io::Read;
    let mut ___buf = [0];
    match ({}).read_exact(&mut ___buf) {{
        Ok(_) => ___buf[0] as _,
        Err(e) => {{
            {}
            libc::EOF
        }}
    }}
}}",
            stream_str,
            ic.error_handling(),
        )
    } else {
        expr!(
            "{{
    use std::io::Read;
    let mut ___buf = [0];
    ({}).read_exact(&mut ___buf).map_or(libc::EOF, |_| ___buf[0] as _)
}}",
            stream_str
        )
    }
}

#[inline]
fn transform_fgets<S: StreamExpr>(stream: &S, s: &Expr, n: &Expr, ic: IndicatorCheck<'_>) -> Expr {
    let stream_str = stream.borrow_for(StreamTrait::BufRead);
    let s = pprust::expr_to_string(s);
    let n = pprust::expr_to_string(n);
    let handling = ic.error_handling();
    expr!(
        "{{
    use std::io::BufRead;
    let mut stream = {};
    let s = {};
    let n = ({}) as usize;
    let ___buf: &mut [u8] = std::slice::from_raw_parts_mut(s as _, n);
    let mut pos = 0;
    while pos < n - 1 {{
        let available = match stream.fill_buf() {{
            Ok(___buf) => ___buf,
            Err(e) => {{
                {}
                pos = 0;
                break
            }}
        }};
        if available.is_empty() {{
            break;
        }}
        ___buf[pos] = available[0];
        stream.consume(1);
        pos += 1;
        if ___buf[pos - 1] == b'\\n' {{
            break;
        }}
    }}
    if pos == 0 {{
        std::ptr::null_mut()
    }} else {{
        ___buf[pos] = 0;
        s
    }}
}}",
        stream_str,
        s,
        n,
        handling
    )
}

#[inline]
fn transform_fread<S: StreamExpr>(
    stream: &S,
    ptr: &Expr,
    size: &Expr,
    nitems: &Expr,
    ic: IndicatorCheck<'_>,
) -> Expr {
    let stream_str = stream.borrow_for(StreamTrait::Read);
    let ptr = pprust::expr_to_string(ptr);
    let size = pprust::expr_to_string(size);
    let nitems = pprust::expr_to_string(nitems);
    let handling = ic.error_handling();
    expr!(
        "{{
    use std::io::Read;
    let mut stream = {};
    let size = {};
    let ptr: &mut [u8] = std::slice::from_raw_parts_mut(({}) as _, (size * ({})) as usize);
    let mut i = 0;
    for data in ptr.chunks_mut(size as usize) {{
        if let Err(e) = stream.read_exact(data) {{
            {}
            break;
        }}
        i += 1;
    }}
    i
}}",
        stream_str,
        size,
        ptr,
        nitems,
        handling
    )
}

fn transform_fprintf_lit<S: StreamExpr, E: Deref<Target = Expr>>(
    stream: &S,
    fmt: Symbol,
    args: &[E],
    ctx: FprintfCtx<'_>,
) -> Expr {
    // from rustc_ast/src/util/literal.rs
    let s = fmt.as_str();
    let mut buf = Vec::with_capacity(s.len());
    unescape::unescape_unicode(fmt.as_str(), unescape::Mode::ByteStr, &mut |_, c| {
        buf.push(unescape::byte_from_char(c.unwrap()))
    });

    if ctx.wide {
        let mut new_buf: Vec<u8> = vec![];
        for c in buf.chunks_exact(4) {
            let c = u32::from_le_bytes(c.try_into().unwrap());
            new_buf.push(c.try_into().unwrap());
        }
        buf = new_buf;
    }
    let rsfmt = printf::to_rust_format(&buf);
    assert!(args.len() == rsfmt.casts.len());
    let mut new_args = String::new();
    let mut width_args = String::new();
    for (i, (arg, cast)) in args.iter().zip(rsfmt.casts).enumerate() {
        let width_arg_idx =
            rsfmt
                .width_args
                .iter()
                .enumerate()
                .find_map(|(width_arg_idx, arg_idx)| {
                    if *arg_idx == i {
                        Some(width_arg_idx)
                    } else {
                        None
                    }
                });
        let args = if let Some(width_arg_idx) = width_arg_idx {
            write!(width_args, "width{} = ", width_arg_idx).unwrap();
            &mut width_args
        } else {
            &mut new_args
        };
        let arg = pprust::expr_to_string(arg);
        match cast {
            "&str" => write!(
                args,
                "std::ffi::CStr::from_ptr(({}) as _).to_str().unwrap(), ",
                arg
            )
            .unwrap(),
            "String" => write!(
                args,
                "{{
    let mut p: *const u8 = {} as _;
    let mut s: String = String::new();
    loop {{
        let slice = std::slice::from_raw_parts(p, 4);
        let i = u32::from_le_bytes([slice[0], slice[1], slice[2], slice[3]]);
        if i == 0 {{
            break s;
        }}
        s.push(std::char::from_u32(i).unwrap());
        p = p.offset(4);
    }}
}}",
                arg
            )
            .unwrap(),
            _ => write!(args, "({}) as {}, ", arg, cast).unwrap(),
        }
    }
    let stream = stream.borrow_for(StreamTrait::Write);
    if ctx.retval_used {
        if ctx.ic.has_check() {
            expr!(
                "{{
    use std::io::Write;
    let string_to_print = format!(\"{}\", {}{});
    match write!({}, \"{{}}\", string_to_print) {{
        Ok(_) => {{}}
        Err(e) => {{
            {}
        }}
    }}
    string_to_print.len() as i32
}}",
                rsfmt.format,
                new_args,
                width_args,
                stream,
                ctx.ic.error_handling_no_eof(),
            )
        } else {
            expr!(
                "{{
    use std::io::Write;
    let string_to_print = format!(\"{}\", {}{});
    write!({}, \"{{}}\", string_to_print);
    string_to_print.len() as i32
}}",
                rsfmt.format,
                new_args,
                width_args,
                stream,
            )
        }
    } else if ctx.ic.has_check() {
        expr!(
            "{{
    use std::io::Write;
    match write!({}, \"{}\", {}{}) {{
        Ok(_) => {{}}
        Err(e) => {{
            {}
        }}
    }}
}}",
            stream,
            rsfmt.format,
            new_args,
            width_args,
            ctx.ic.error_handling_no_eof(),
        )
    } else {
        expr!(
            "{{
    use std::io::Write;
    write!({}, \"{}\", {}{})
}}",
            stream,
            rsfmt.format,
            new_args,
            width_args,
        )
    }
}

#[inline]
fn transform_fputc<S: StreamExpr>(stream: &S, c: &Expr, ic: IndicatorCheck<'_>) -> Expr {
    let stream_str = stream.borrow_for(StreamTrait::Write);
    let c = pprust::expr_to_string(c);
    if ic.has_check() {
        expr!(
            "{{
    use std::io::Write;
    let c = {};
    match ({}).write_all(&[c as u8]) {{
        Ok(_) => c,
        Err(e) => {{
            {}
            libc::EOF
        }}
    }}
}}",
            c,
            stream_str,
            ic.error_handling_no_eof(),
        )
    } else {
        expr!(
            "{{
    use std::io::Write;
    let c = {};
    ({}).write_all(&[c as u8]).map_or(libc::EOF, |_| c)
}}",
            c,
            stream_str
        )
    }
}

#[inline]
fn transform_fputs<S: StreamExpr>(stream: &S, s: &Expr, ic: IndicatorCheck<'_>) -> Expr {
    let stream_str = stream.borrow_for(StreamTrait::Write);
    let s = pprust::expr_to_string(s);
    if ic.has_check() {
        expr!(
            "{{
    use std::io::Write;
    match ({}).write_all(std::ffi::CStr::from_ptr(({}) as _).to_bytes()) {{
        Ok(_) => 0,
        Err(e) => {{
            {}
            libc::EOF
        }}
    }}
}}",
            stream_str,
            s,
            ic.error_handling_no_eof(),
        )
    } else {
        expr!(
            "{{
    use std::io::Write;
    ({}).write_all(std::ffi::CStr::from_ptr(({}) as _).to_bytes())
        .map_or(libc::EOF, |_| 0)
}}",
            stream_str,
            s
        )
    }
}

#[inline]
fn transform_fwrite<S: StreamExpr>(
    stream: &S,
    ptr: &Expr,
    size: &Expr,
    nitems: &Expr,
    ic: IndicatorCheck<'_>,
) -> Expr {
    let stream_str = stream.borrow_for(StreamTrait::Write);
    let ptr = pprust::expr_to_string(ptr);
    let size = pprust::expr_to_string(size);
    let nitems = pprust::expr_to_string(nitems);
    let handling = ic.error_handling_no_eof();
    expr!(
        "{{
    use std::io::Write;
    let mut stream = {};
    let size = {};
    let ptr: &[u8] = std::slice::from_raw_parts({} as _, (size * ({})) as usize);
    let mut i = 0;
    for data in ptr.chunks(size as usize) {{
        if let Err(e) = stream.write_all(data) {{
            {}
            break;
        }}
        i += 1;
    }}
    i
}}",
        stream_str,
        size,
        ptr,
        nitems,
        handling
    )
}

#[inline]
fn transform_fflush<S: StreamExpr>(stream: &S, ic: IndicatorCheck<'_>) -> Expr {
    let stream_str = stream.borrow_for(StreamTrait::Write);
    if ic.has_check() {
        expr!(
            "{{
    use std::io::Write;
    match ({}).flush() {{
        Ok(_) => 0,
        Err(e) => {{
            {}
            libc::EOF
        }}
    }}
}}",
            stream_str,
            ic.error_handling_no_eof(),
        )
    } else {
        expr!(
            "{{
    use std::io::Write;
    ({}).flush().map_or(libc::EOF, |_| 0)
}}",
            stream_str
        )
    }
}

#[inline]
fn transform_puts(s: &Expr, ic: IndicatorCheck<'_>) -> Expr {
    let s = pprust::expr_to_string(s);
    if ic.has_check() {
        expr!(
            r#"{{
    use std::io::Write;
    let mut stream = std::io::stdout();
    match stream
        .write_all(std::ffi::CStr::from_ptr(({}) as _).to_bytes())
        .and_then(|_| stream.write_all(b"\n")) {{
        Ok(_) => 0,
        Err(e) => {{
            {}
            libc::EOF
        }}
    }}
}}"#,
            s,
            ic.error_handling_no_eof(),
        )
    } else {
        expr!(
            r#"{{
    use std::io::Write;
    let mut stream = std::io::stdout();
    stream
        .write_all(std::ffi::CStr::from_ptr(({}) as _).to_bytes())
        .and_then(|_| stream.write_all(b"\n"))
        .map_or(libc::EOF, |_| 0)
}}"#,
            s
        )
    }
}

#[inline]
fn transform_fseek<S: StreamExpr>(stream: &S, off: &Expr, whence: &Expr) -> Expr {
    let stream = stream.borrow_for(StreamTrait::Seek);
    let off = pprust::expr_to_string(off);
    let whence = LikelyLit::from_expr(whence);
    match whence {
        LikelyLit::Lit(lit) => {
            let v = match lit.as_str() {
                "0" => "Start",
                "1" => "Current",
                "2" => "End",
                lit => panic!("{}", lit),
            };
            expr!(
                "{{
    use std::io::Seek;
    ({}).seek(std::io::SeekFrom::{}(({}) as _)).map_or(-1, |_| 0)
}}",
                stream,
                v,
                off
            )
        }
        LikelyLit::If(_, _, _) => todo!(),
        LikelyLit::Path(path, _) => {
            expr!(
                "{{
    use std::io::Seek;
    ({}).seek(match {} {{
        0 => std::io::SeekFrom::Start(({2}) as _),
        1 => std::io::SeekFrom::Current(({2}) as _),
        2 => std::io::SeekFrom::End(({2}) as _),
        _ => panic!(),
    }}).map_or(-1, |_| 0)
}}",
                stream,
                path.as_str(),
                off
            )
        }
        LikelyLit::Other(_) => todo!(),
    }
}

#[inline]
fn transform_ftell<S: StreamExpr>(stream: &S) -> Expr {
    let stream = stream.borrow_for(StreamTrait::Seek);
    expr!(
        "{{
    use std::io::Seek;
    ({}).stream_position().map_or(-1, |p| p as i64)
}}",
        stream
    )
}

#[inline]
fn transform_rewind<S: StreamExpr>(stream: &S) -> Expr {
    let stream = stream.borrow_for(StreamTrait::Seek);
    expr!(
        "{{
    use std::io::Seek;
    ({}).rewind();
}}",
        stream
    )
}

#[inline]
fn transform_fileno<S: StreamExpr>(stream: &S) -> Expr {
    let stream = stream.borrow_for(StreamTrait::AsRawFd);
    expr!(
        "{{
    use crate::AsRawFd;
    ({}).as_raw_fd()
}}",
        stream
    )
}
