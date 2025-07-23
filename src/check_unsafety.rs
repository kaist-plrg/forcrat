//! Check unsafety.
//! The code is from `rustc_mir_build/src/check_unsafety.rs`.
//! We removed code related to error/warning emission.
//! <https://github.com/rust-lang/rust/blob/99b18d6c5062449db8e7ccded4cb69b555a239c3/compiler/rustc_mir_build/src/check_unsafety.rs>

use std::ops::Bound;

use rustc_ast::AsmMacro;
use rustc_data_structures::stack::ensure_sufficient_stack;
use rustc_hash::FxHashSet;
use rustc_hir::{self as hir, def::DefKind, BindingMode, ByRef, HirId, Mutability};
use rustc_middle::{
    middle::codegen_fn_attrs::TargetFeature,
    mir::BorrowKind,
    span_bug,
    thir::{visit::Visitor, *},
    ty::{self, Ty, TyCtxt},
};
use rustc_span::{
    def_id::{DefId, LocalDefId},
    sym, Span, Symbol,
};

#[derive(Debug, Clone, Copy)]
pub struct UnsafetyChecker;

impl Pass for UnsafetyChecker {
    type Out = ();

    fn run(&self, tcx: TyCtxt<'_>) {
        let mut unsafe_byte_positions = FxHashSet::default();
        let mut unsafe_lines = FxHashSet::default();
        for item_id in tcx.hir_free_items() {
            let item = tcx.hir_item(item_id);
            let rustc_hir::ItemKind::Fn { ident, .. } = item.kind else { continue };
            if ident.name.as_str() == "main" {
                continue;
            }
            let local_def_id = item.owner_id.def_id;
            let def_path_str = tcx.def_path_str(local_def_id);
            if def_path_str.starts_with("stdio::") {
                continue;
            }
            let unsafes = check_unsafety(tcx, local_def_id);
            let source_map = tcx.sess.source_map();
            for (span, _) in unsafes {
                for pos in span.lo().0..=span.hi().0 {
                    unsafe_byte_positions.insert(pos);
                }

                let fname = source_map.span_to_filename(span);
                let file = source_map.get_source_file(&fname).unwrap();
                let lo = file.lookup_file_pos_with_col_display(span.lo());
                let hi = file.lookup_file_pos_with_col_display(span.hi());
                for line in lo.0..=hi.0 {
                    unsafe_lines.insert((fname.clone(), line));
                }
            }
        }
        println!("{} {}", unsafe_byte_positions.len(), unsafe_lines.len());
    }
}

struct UnsafetyVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    thir: &'a Thir<'tcx>,
    /// The `HirId` of the current scope, which would be the `HirId`
    /// of the current HIR node, modulo adjustments. Used for lint levels.
    hir_context: HirId,
    /// The `#[target_feature]` attributes of the body. Used for checking
    /// calls to functions with `#[target_feature]` (RFC 2396).
    body_target_features: &'tcx [TargetFeature],
    /// When inside the LHS of an assignment to a field, this is the type
    /// of the LHS and the span of the assignment expression.
    assignment_info: Option<Ty<'tcx>>,
    in_union_destructure: bool,
    typing_env: ty::TypingEnv<'tcx>,
    inside_adt: bool,

    unsafes: Vec<(Span, UnsafeOpKind)>,
}

impl UnsafetyVisitor<'_, '_> {
    fn requires_unsafe(&mut self, span: Span, kind: UnsafeOpKind) {
        self.unsafes.push((span, kind));
    }

    /// Handle closures/coroutines/inline-consts, which is unsafecked with their parent body.
    fn visit_inner_body(&mut self, def: LocalDefId) {
        if let Ok((inner_thir, expr)) = self.tcx.thir_body(def) {
            // Run all other queries that depend on THIR.
            self.tcx.ensure_done().mir_built(def);
            let inner_thir = &inner_thir.steal();
            let hir_context = self.tcx.local_def_id_to_hir_id(def);
            let mut inner_visitor = UnsafetyVisitor {
                tcx: self.tcx,
                thir: inner_thir,
                hir_context,
                body_target_features: self.body_target_features,
                assignment_info: self.assignment_info,
                in_union_destructure: false,
                typing_env: self.typing_env,
                inside_adt: false,
                unsafes: vec![],
            };
            // params in THIR may be unsafe, e.g. a union pattern.
            for param in &inner_thir.params {
                if let Some(param_pat) = param.pat.as_deref() {
                    inner_visitor.visit_pat(param_pat);
                }
            }
            // Visit the body.
            inner_visitor.visit_expr(&inner_thir[expr]);

            self.unsafes.extend(inner_visitor.unsafes);
        }
    }
}

// Searches for accesses to layout constrained fields.
struct LayoutConstrainedPlaceVisitor<'a, 'tcx> {
    found: bool,
    thir: &'a Thir<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'a, 'tcx> LayoutConstrainedPlaceVisitor<'a, 'tcx> {
    fn new(thir: &'a Thir<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self {
            found: false,
            thir,
            tcx,
        }
    }
}

#[derive(Debug, PartialEq)]
enum ExprCategory {
    /// An assignable memory location like `x`, `x.f`, `foo()[3]`, that
    /// sort of thing. Something that could appear on the LHS of an `=`
    /// sign.
    Place,

    /// A literal like `23` or `"foo"`. Does not include constant
    /// expressions like `3 + 5`.
    Constant,

    /// Something that generates a new value at runtime, like `x + y`
    /// or `foo()`.
    Rvalue(RvalueFunc),
}

/// Rvalues fall into different "styles" that will determine which fn
/// is best suited to generate them.
#[derive(Debug, PartialEq)]
pub(crate) enum RvalueFunc {
    /// Best generated by `into`. This is generally exprs that
    /// cause branching, like `match`, but also includes calls.
    Into,

    /// Best generated by `as_rvalue`. This is usually the case.
    AsRvalue,
}

impl ExprCategory {
    /// Determines the category for a given expression. Note that scope
    /// and paren expressions have no category.
    fn of(ek: &ExprKind<'_>) -> Option<ExprCategory> {
        match *ek {
            ExprKind::Scope { .. } => None,

            ExprKind::Field { .. }
            | ExprKind::Deref { .. }
            | ExprKind::Index { .. }
            | ExprKind::UpvarRef { .. }
            | ExprKind::VarRef { .. }
            | ExprKind::PlaceTypeAscription { .. }
            | ExprKind::ValueTypeAscription { .. }
            | ExprKind::PlaceUnwrapUnsafeBinder { .. }
            | ExprKind::ValueUnwrapUnsafeBinder { .. } => Some(ExprCategory::Place),

            ExprKind::LogicalOp { .. }
            | ExprKind::Match { .. }
            | ExprKind::If { .. }
            | ExprKind::Let { .. }
            | ExprKind::NeverToAny { .. }
            | ExprKind::Use { .. }
            | ExprKind::Adt { .. }
            | ExprKind::Borrow { .. }
            | ExprKind::RawBorrow { .. }
            | ExprKind::Yield { .. }
            | ExprKind::Call { .. }
            | ExprKind::ByUse { .. }
            | ExprKind::InlineAsm { .. } => Some(ExprCategory::Rvalue(RvalueFunc::Into)),

            ExprKind::Array { .. }
            | ExprKind::Tuple { .. }
            | ExprKind::Closure { .. }
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Box { .. }
            | ExprKind::Cast { .. }
            | ExprKind::PointerCoercion { .. }
            | ExprKind::Repeat { .. }
            | ExprKind::Assign { .. }
            | ExprKind::AssignOp { .. }
            | ExprKind::ThreadLocalRef(_)
            | ExprKind::OffsetOf { .. }
            | ExprKind::WrapUnsafeBinder { .. } => Some(ExprCategory::Rvalue(RvalueFunc::AsRvalue)),

            ExprKind::ConstBlock { .. }
            | ExprKind::Literal { .. }
            | ExprKind::NonHirLiteral { .. }
            | ExprKind::ZstLiteral { .. }
            | ExprKind::ConstParam { .. }
            | ExprKind::StaticRef { .. }
            | ExprKind::NamedConst { .. } => Some(ExprCategory::Constant),

            ExprKind::Loop { .. }
            | ExprKind::Block { .. }
            | ExprKind::Break { .. }
            | ExprKind::Continue { .. }
            | ExprKind::Return { .. }
            | ExprKind::Become { .. } =>
            // FIXME(#27840) these probably want their own
            // category, like "nonterminating"
            {
                Some(ExprCategory::Rvalue(RvalueFunc::Into))
            }
        }
    }
}

#[allow(clippy::collapsible_if)]
impl<'a, 'tcx> Visitor<'a, 'tcx> for LayoutConstrainedPlaceVisitor<'a, 'tcx> {
    fn thir(&self) -> &'a Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &'a Expr<'tcx>) {
        match expr.kind {
            ExprKind::Field { lhs, .. } => {
                if let ty::Adt(adt_def, _) = self.thir[lhs].ty.kind() {
                    if (Bound::Unbounded, Bound::Unbounded)
                        != self.tcx.layout_scalar_valid_range(adt_def.did())
                    {
                        self.found = true;
                    }
                }
                visit::walk_expr(self, expr);
            }

            // Keep walking through the expression as long as we stay in the same
            // place, i.e. the expression is a place expression and not a dereference
            // (since dereferencing something leads us to a different place).
            ExprKind::Deref { .. } => {}
            ref kind if ExprCategory::of(kind).is_none_or(|cat| cat == ExprCategory::Place) => {
                visit::walk_expr(self, expr);
            }

            _ => {}
        }
    }
}

#[allow(clippy::collapsible_if)]
impl<'a, 'tcx> Visitor<'a, 'tcx> for UnsafetyVisitor<'a, 'tcx> {
    fn thir(&self) -> &'a Thir<'tcx> {
        self.thir
    }

    fn visit_pat(&mut self, pat: &'a Pat<'tcx>) {
        if self.in_union_destructure {
            match pat.kind {
                PatKind::Missing => unreachable!(),
                // binding to a variable allows getting stuff out of variable
                PatKind::Binding { .. }
                // match is conditional on having this value
                | PatKind::Constant { .. }
                | PatKind::Variant { .. }
                | PatKind::Leaf { .. }
                | PatKind::Deref { .. }
                | PatKind::DerefPattern { .. }
                | PatKind::Range { .. }
                | PatKind::Slice { .. }
                | PatKind::Array { .. }
                // Never constitutes a witness of uninhabitedness.
                | PatKind::Never => {
                    self.requires_unsafe(pat.span, AccessToUnionField);
                    return; // we can return here since this already requires unsafe
                }
                // wildcard doesn't read anything.
                PatKind::Wild |
                // these just wrap other patterns, which we recurse on below.
                PatKind::Or { .. } |
                PatKind::ExpandedConstant { .. } |
                PatKind::AscribeUserType { .. } |
                PatKind::Error(_) => {}
            }
        };

        match &pat.kind {
            PatKind::Leaf { subpatterns, .. } => {
                if let ty::Adt(adt_def, ..) = pat.ty.kind() {
                    for pat in subpatterns {
                        if adt_def.non_enum_variant().fields[pat.field]
                            .safety
                            .is_unsafe()
                        {
                            self.requires_unsafe(pat.pattern.span, UseOfUnsafeField);
                        }
                    }
                    if adt_def.is_union() {
                        let old_in_union_destructure =
                            std::mem::replace(&mut self.in_union_destructure, true);
                        visit::walk_pat(self, pat);
                        self.in_union_destructure = old_in_union_destructure;
                    } else if (Bound::Unbounded, Bound::Unbounded)
                        != self.tcx.layout_scalar_valid_range(adt_def.did())
                    {
                        let old_inside_adt = std::mem::replace(&mut self.inside_adt, true);
                        visit::walk_pat(self, pat);
                        self.inside_adt = old_inside_adt;
                    } else {
                        visit::walk_pat(self, pat);
                    }
                } else {
                    visit::walk_pat(self, pat);
                }
            }
            PatKind::Variant {
                adt_def,
                args: _,
                variant_index,
                subpatterns,
            } => {
                for pat in subpatterns {
                    let field = &pat.field;
                    if adt_def.variant(*variant_index).fields[*field]
                        .safety
                        .is_unsafe()
                    {
                        self.requires_unsafe(pat.pattern.span, UseOfUnsafeField);
                    }
                }
                visit::walk_pat(self, pat);
            }
            PatKind::Binding {
                mode: BindingMode(ByRef::Yes(rm), _),
                ty,
                ..
            } => {
                if self.inside_adt {
                    let ty::Ref(_, ty, _) = ty.kind() else {
                        span_bug!(
                            pat.span,
                            "ByRef::Yes in pattern, but found non-reference type {}",
                            ty
                        );
                    };
                    match rm {
                        Mutability::Not => {
                            if !ty.is_freeze(self.tcx, self.typing_env) {
                                self.requires_unsafe(pat.span, BorrowOfLayoutConstrainedField);
                            }
                        }
                        Mutability::Mut => {
                            self.requires_unsafe(pat.span, MutationOfLayoutConstrainedField);
                        }
                    }
                }
                visit::walk_pat(self, pat);
            }
            PatKind::Deref { .. } | PatKind::DerefPattern { .. } => {
                let old_inside_adt = std::mem::replace(&mut self.inside_adt, false);
                visit::walk_pat(self, pat);
                self.inside_adt = old_inside_adt;
            }
            PatKind::ExpandedConstant { def_id, .. } => {
                if let Some(def) = def_id.as_local()
                    && matches!(self.tcx.def_kind(def_id), DefKind::InlineConst)
                {
                    self.visit_inner_body(def);
                }
                visit::walk_pat(self, pat);
            }
            _ => {
                visit::walk_pat(self, pat);
            }
        }
    }

    fn visit_expr(&mut self, expr: &'a Expr<'tcx>) {
        // could we be in the LHS of an assignment to a field?
        match expr.kind {
            ExprKind::Field { .. }
            | ExprKind::VarRef { .. }
            | ExprKind::UpvarRef { .. }
            | ExprKind::Scope { .. }
            | ExprKind::Cast { .. } => {}

            ExprKind::RawBorrow { .. }
            | ExprKind::Adt { .. }
            | ExprKind::Array { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Block { .. }
            | ExprKind::Borrow { .. }
            | ExprKind::Literal { .. }
            | ExprKind::NamedConst { .. }
            | ExprKind::NonHirLiteral { .. }
            | ExprKind::ZstLiteral { .. }
            | ExprKind::ConstParam { .. }
            | ExprKind::ConstBlock { .. }
            | ExprKind::Deref { .. }
            | ExprKind::Index { .. }
            | ExprKind::NeverToAny { .. }
            | ExprKind::PlaceTypeAscription { .. }
            | ExprKind::ValueTypeAscription { .. }
            | ExprKind::PlaceUnwrapUnsafeBinder { .. }
            | ExprKind::ValueUnwrapUnsafeBinder { .. }
            | ExprKind::WrapUnsafeBinder { .. }
            | ExprKind::PointerCoercion { .. }
            | ExprKind::Repeat { .. }
            | ExprKind::StaticRef { .. }
            | ExprKind::ThreadLocalRef { .. }
            | ExprKind::Tuple { .. }
            | ExprKind::Unary { .. }
            | ExprKind::Call { .. }
            | ExprKind::ByUse { .. }
            | ExprKind::Assign { .. }
            | ExprKind::AssignOp { .. }
            | ExprKind::Break { .. }
            | ExprKind::Closure { .. }
            | ExprKind::Continue { .. }
            | ExprKind::Return { .. }
            | ExprKind::Become { .. }
            | ExprKind::Yield { .. }
            | ExprKind::Loop { .. }
            | ExprKind::Let { .. }
            | ExprKind::Match { .. }
            | ExprKind::Box { .. }
            | ExprKind::If { .. }
            | ExprKind::InlineAsm { .. }
            | ExprKind::OffsetOf { .. }
            | ExprKind::LogicalOp { .. }
            | ExprKind::Use { .. } => {
                // We don't need to save the old value and restore it
                // because all the place expressions can't have more
                // than one child.
                self.assignment_info = None;
            }
        };
        match expr.kind {
            ExprKind::Scope {
                value,
                lint_level: LintLevel::Explicit(hir_id),
                region_scope: _,
            } => {
                let prev_id = self.hir_context;
                self.hir_context = hir_id;
                ensure_sufficient_stack(|| {
                    self.visit_expr(&self.thir[value]);
                });
                self.hir_context = prev_id;
                return; // don't visit the whole expression
            }
            ExprKind::Call {
                fun,
                ty: _,
                args: _,
                from_hir_call: _,
                fn_span: _,
            } => {
                let fn_ty = self.thir[fun].ty;
                let sig = fn_ty.fn_sig(self.tcx);
                let (callee_features, safe_target_features): (&[_], _) = match fn_ty.kind() {
                    ty::FnDef(func_id, ..) => {
                        let cg_attrs = self.tcx.codegen_fn_attrs(func_id);
                        (&cg_attrs.target_features, cg_attrs.safe_target_features)
                    }
                    _ => (&[], false),
                };
                if sig.safety().is_unsafe() && !safe_target_features {
                    let func_id = if let ty::FnDef(func_id, _) = fn_ty.kind() {
                        Some(*func_id)
                    } else {
                        None
                    };
                    self.requires_unsafe(expr.span, CallToUnsafeFunction(func_id));
                } else if let &ty::FnDef(func_did, _) = fn_ty.kind() {
                    if !self
                        .tcx
                        .is_target_feature_call_safe(callee_features, self.body_target_features)
                    {
                        let missing: Vec<_> = callee_features
                            .iter()
                            .copied()
                            .filter(|feature| {
                                !feature.implied
                                    && !self
                                        .body_target_features
                                        .iter()
                                        .any(|body_feature| body_feature.name == feature.name)
                            })
                            .map(|feature| feature.name)
                            .collect();
                        let build_enabled = self
                            .tcx
                            .sess
                            .target_features
                            .iter()
                            .copied()
                            .filter(|feature| missing.contains(feature))
                            .collect();
                        self.requires_unsafe(
                            expr.span,
                            CallToFunctionWith {
                                function: func_did,
                                missing,
                                build_enabled,
                            },
                        );
                    }
                }
            }
            ExprKind::RawBorrow { arg, .. } => {
                if let ExprKind::Scope { value: arg, .. } = self.thir[arg].kind
                    && let ExprKind::Deref { arg } = self.thir[arg].kind
                {
                    // Taking a raw ref to a deref place expr is always safe.
                    // Make sure the expression we're deref'ing is safe, though.
                    visit::walk_expr(self, &self.thir[arg]);
                    return;
                }
            }
            ExprKind::Deref { arg } => {
                if let ExprKind::StaticRef { def_id, .. } | ExprKind::ThreadLocalRef(def_id) =
                    self.thir[arg].kind
                {
                    if self.tcx.is_mutable_static(def_id) {
                        self.requires_unsafe(expr.span, UseOfMutableStatic);
                    } else if self.tcx.is_foreign_item(def_id) {
                        match self.tcx.def_kind(def_id) {
                            DefKind::Static {
                                safety: hir::Safety::Safe,
                                ..
                            } => {}
                            _ => self.requires_unsafe(expr.span, UseOfExternStatic),
                        }
                    }
                } else if self.thir[arg].ty.is_raw_ptr() {
                    self.requires_unsafe(expr.span, DerefOfRawPointer);
                }
            }
            ExprKind::InlineAsm(box InlineAsmExpr {
                asm_macro: asm_macro @ (AsmMacro::Asm | AsmMacro::NakedAsm),
                ref operands,
                template: _,
                options: _,
                line_spans: _,
            }) => {
                // The `naked` attribute and the `naked_asm!` block form one atomic unit of
                // unsafety, and `naked_asm!` does not itself need to be wrapped in an unsafe block.
                if let AsmMacro::Asm = asm_macro {
                    self.requires_unsafe(expr.span, UseOfInlineAssembly);
                }

                // For inline asm, do not use `walk_expr`, since we want to handle the label block
                // specially.
                for op in &**operands {
                    use rustc_middle::thir::InlineAsmOperand::*;
                    match op {
                        In { expr, reg: _ }
                        | Out {
                            expr: Some(expr),
                            reg: _,
                            late: _,
                        }
                        | InOut {
                            expr,
                            reg: _,
                            late: _,
                        } => self.visit_expr(&self.thir()[*expr]),
                        SplitInOut {
                            in_expr,
                            out_expr,
                            reg: _,
                            late: _,
                        } => {
                            self.visit_expr(&self.thir()[*in_expr]);
                            if let Some(out_expr) = out_expr {
                                self.visit_expr(&self.thir()[*out_expr]);
                            }
                        }
                        Out {
                            expr: None,
                            reg: _,
                            late: _,
                        }
                        | Const { value: _, span: _ }
                        | SymFn { value: _ }
                        | SymStatic { def_id: _ } => {}
                        Label { block } => {
                            // Label blocks are safe context.
                            // `asm!()` is forced to be wrapped inside unsafe. If there's no special
                            // treatment, the label blocks would also always be unsafe with no way
                            // of opting out.
                            visit::walk_block(self, &self.thir()[*block])
                        }
                    }
                }
                return;
            }
            ExprKind::Adt(box AdtExpr {
                adt_def,
                variant_index,
                args: _,
                user_ty: _,
                fields: _,
                base: _,
            }) => {
                if adt_def.variant(variant_index).has_unsafe_fields() {
                    self.requires_unsafe(expr.span, InitializingTypeWithUnsafeField)
                }
                match self.tcx.layout_scalar_valid_range(adt_def.did()) {
                    (Bound::Unbounded, Bound::Unbounded) => {}
                    _ => self.requires_unsafe(expr.span, InitializingTypeWith),
                }
            }
            ExprKind::Closure(box ClosureExpr {
                closure_id,
                args: _,
                upvars: _,
                movability: _,
                fake_reads: _,
            }) => {
                self.visit_inner_body(closure_id);
            }
            ExprKind::ConstBlock { did, args: _ } => {
                let def_id = did.expect_local();
                self.visit_inner_body(def_id);
            }
            ExprKind::Field {
                lhs,
                variant_index,
                name,
            } => {
                let lhs = &self.thir[lhs];
                if let ty::Adt(adt_def, _) = lhs.ty.kind() {
                    if adt_def.variant(variant_index).fields[name]
                        .safety
                        .is_unsafe()
                    {
                        self.requires_unsafe(expr.span, UseOfUnsafeField);
                    } else if adt_def.is_union() {
                        if let Some(assigned_ty) = self.assignment_info {
                            if assigned_ty.needs_drop(self.tcx, self.typing_env) {
                                // This would be unsafe, but should be outright impossible since we
                                // reject such unions.
                                assert!(
                                    self.tcx.dcx().has_errors().is_some(),
                                    "union fields that need dropping should be impossible: {assigned_ty}"
                                );
                            }
                        } else {
                            self.requires_unsafe(expr.span, AccessToUnionField);
                        }
                    }
                }
            }
            ExprKind::Assign { lhs, rhs } | ExprKind::AssignOp { lhs, rhs, .. } => {
                let lhs = &self.thir[lhs];
                // First, check whether we are mutating a layout constrained field
                let mut visitor = LayoutConstrainedPlaceVisitor::new(self.thir, self.tcx);
                visit::walk_expr(&mut visitor, lhs);
                if visitor.found {
                    self.requires_unsafe(expr.span, MutationOfLayoutConstrainedField);
                }

                // Second, check for accesses to union fields. Don't have any
                // special handling for AssignOp since it causes a read *and*
                // write to lhs.
                if matches!(expr.kind, ExprKind::Assign { .. }) {
                    self.assignment_info = Some(lhs.ty);
                    visit::walk_expr(self, lhs);
                    self.assignment_info = None;
                    visit::walk_expr(self, &self.thir()[rhs]);
                    return; // We have already visited everything by now.
                }
            }
            ExprKind::Borrow { borrow_kind, arg } => {
                let mut visitor = LayoutConstrainedPlaceVisitor::new(self.thir, self.tcx);
                visit::walk_expr(&mut visitor, expr);
                if visitor.found {
                    match borrow_kind {
                        BorrowKind::Fake(_) | BorrowKind::Shared
                            if !self.thir[arg].ty.is_freeze(self.tcx, self.typing_env) =>
                        {
                            self.requires_unsafe(expr.span, BorrowOfLayoutConstrainedField)
                        }
                        BorrowKind::Mut { .. } => {
                            self.requires_unsafe(expr.span, MutationOfLayoutConstrainedField)
                        }
                        BorrowKind::Fake(_) | BorrowKind::Shared => {}
                    }
                }
            }
            ExprKind::PlaceUnwrapUnsafeBinder { .. }
            | ExprKind::ValueUnwrapUnsafeBinder { .. }
            | ExprKind::WrapUnsafeBinder { .. } => {
                self.requires_unsafe(expr.span, UnsafeBinderCast);
            }
            _ => {}
        }
        visit::walk_expr(self, expr);
    }
}

#[derive(Clone, PartialEq)]
pub enum UnsafeOpKind {
    CallToUnsafeFunction(Option<DefId>),
    UseOfInlineAssembly,
    InitializingTypeWith,
    InitializingTypeWithUnsafeField,
    UseOfMutableStatic,
    UseOfExternStatic,
    UseOfUnsafeField,
    DerefOfRawPointer,
    AccessToUnionField,
    MutationOfLayoutConstrainedField,
    BorrowOfLayoutConstrainedField,
    CallToFunctionWith {
        function: DefId,
        /// Target features enabled in callee's `#[target_feature]` but missing in
        /// caller's `#[target_feature]`.
        missing: Vec<Symbol>,
        /// Target features in `missing` that are enabled at compile time
        /// (e.g., with `-C target-feature`).
        build_enabled: Vec<Symbol>,
    },
    UnsafeBinderCast,
}

use UnsafeOpKind::*;

use crate::compile_util::Pass;

fn check_unsafety(tcx: TyCtxt<'_>, def: LocalDefId) -> Vec<(Span, UnsafeOpKind)> {
    // Closures and inline consts are handled by their owner, if it has a body
    assert!(!tcx.is_typeck_child(def.to_def_id()));
    // Also, don't safety check custom MIR
    if tcx.has_attr(def, sym::custom_mir) {
        panic!();
    }

    let Ok((thir, expr)) = tcx.thir_body(def) else { panic!() };
    // Runs all other queries that depend on THIR.
    tcx.ensure_done().mir_built(def);
    let thir = &thir.steal();

    let hir_id = tcx.local_def_id_to_hir_id(def);
    let body_target_features = &tcx.body_codegen_attrs(def.to_def_id()).target_features;
    let mut visitor = UnsafetyVisitor {
        tcx,
        thir,
        hir_context: hir_id,
        body_target_features,
        assignment_info: None,
        in_union_destructure: false,
        // FIXME(#132279): we're clearly in a body here.
        typing_env: ty::TypingEnv::non_body_analysis(tcx, def),
        inside_adt: false,
        unsafes: vec![],
    };
    // params in THIR may be unsafe, e.g. a union pattern.
    for param in &thir.params {
        if let Some(param_pat) = param.pat.as_deref() {
            visitor.visit_pat(param_pat);
        }
    }
    // Visit the body.
    visitor.visit_expr(&thir[expr]);

    visitor.unsafes
}
