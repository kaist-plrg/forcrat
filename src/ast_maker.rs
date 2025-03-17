use rustc_ast::{
    ptr::P,
    token::{Lit, LitKind},
    *,
};
use rustc_span::{symbol::Ident, DUMMY_SP};

#[inline]
pub fn mk_stmt(kind: StmtKind) -> Stmt {
    Stmt {
        id: DUMMY_NODE_ID,
        kind,
        span: DUMMY_SP,
    }
}

#[inline]
pub fn mk_local(pat: Pat, ty: Option<Ty>, init: Expr) -> Local {
    Local {
        id: DUMMY_NODE_ID,
        pat: P(pat),
        ty: ty.map(P),
        kind: LocalKind::Init(P(init)),
        span: DUMMY_SP,
        attrs: AttrVec::new(),
        tokens: None,
    }
}

#[inline]
pub fn mk_local_init_stmt(pat: Pat, ty: Option<Ty>, init: Expr) -> Stmt {
    mk_stmt(StmtKind::Local(P(mk_local(pat, ty, init))))
}

#[inline]
pub fn mk_pat(kind: PatKind) -> Pat {
    Pat {
        id: DUMMY_NODE_ID,
        kind,
        span: DUMMY_SP,
        tokens: None,
    }
}

#[inline]
pub fn mk_ident_pat(by_ref: ByRef, mutability: Mutability, symbol: &str) -> Pat {
    mk_pat(PatKind::Ident(
        BindingAnnotation(by_ref, mutability),
        mk_ident(symbol),
        None,
    ))
}

#[inline]
pub fn mk_expr(kind: ExprKind) -> Expr {
    Expr {
        id: DUMMY_NODE_ID,
        kind,
        span: DUMMY_SP,
        attrs: AttrVec::new(),
        tokens: None,
    }
}

#[inline]
pub fn mk_lit_expr(kind: LitKind, symbol: &str) -> Expr {
    mk_expr(ExprKind::Lit(mk_lit(kind, symbol)))
}

#[inline]
pub fn mk_ty(kind: TyKind) -> Ty {
    Ty {
        id: DUMMY_NODE_ID,
        kind,
        span: DUMMY_SP,
        tokens: None,
    }
}

#[inline]
pub fn mk_path_ty(path: Path) -> Ty {
    mk_ty(TyKind::Path(None, path))
}

#[inline]
pub fn mk_generic_param(
    ident: Ident,
    bounds: GenericBounds,
    kind: GenericParamKind,
) -> GenericParam {
    GenericParam {
        id: DUMMY_NODE_ID,
        ident,
        attrs: AttrVec::new(),
        bounds,
        is_placeholder: false,
        kind,
        colon_span: None,
    }
}

#[inline]
pub fn mk_trait_ref(path: Path) -> TraitRef {
    TraitRef {
        path,
        ref_id: DUMMY_NODE_ID,
    }
}

#[inline]
pub fn mk_poly_trait_ref(
    bound_generic_params: Vec<GenericParam>,
    trait_ref: TraitRef,
) -> PolyTraitRef {
    PolyTraitRef {
        bound_generic_params: bound_generic_params.into(),
        trait_ref,
        span: DUMMY_SP,
    }
}

#[inline]
pub fn mk_path(segments: Vec<PathSegment>) -> Path {
    Path {
        span: DUMMY_SP,
        segments: segments.into(),
        tokens: None,
    }
}

#[inline]
pub fn mk_path_segment(ident: Ident, args: Option<GenericArgs>) -> PathSegment {
    PathSegment {
        ident,
        id: DUMMY_NODE_ID,
        args: args.map(P),
    }
}

#[inline]
pub fn mk_ident(symbol: &str) -> Ident {
    Ident {
        name: rustc_span::Symbol::intern(symbol),
        span: DUMMY_SP,
    }
}

#[inline]
pub fn mk_lit(kind: LitKind, symbol: &str) -> Lit {
    Lit {
        kind,
        symbol: rustc_span::Symbol::intern(symbol),
        suffix: None,
    }
}
