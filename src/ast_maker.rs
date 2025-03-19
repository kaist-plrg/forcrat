use rustc_ast::{
    ptr::P,
    token::{Lit, LitKind},
    *,
};
use rustc_data_structures::sync::Lrc;
use rustc_parse::parser::{ForceCollect, Parser};
use rustc_session::parse::ParseSess;
use rustc_span::{
    source_map::{FilePathMapping, SourceMap},
    symbol::Ident,
    FileName, DUMMY_SP,
};

use crate::compile_util::SilentEmitter;

#[inline]
pub fn new_parse_sess() -> ParseSess {
    let handler = rustc_errors::Handler::with_emitter(Box::new(SilentEmitter));
    let source_map = Lrc::new(SourceMap::new(FilePathMapping::empty()));
    ParseSess::with_span_handler(handler, source_map)
}

#[inline]
pub fn new_parser_from_str(parse_sess: &ParseSess, s: String) -> Parser<'_> {
    let file_name = FileName::Custom("".to_string());
    rustc_parse::new_parser_from_source_str(parse_sess, file_name, s)
}

#[inline]
pub fn parse_item(item: String) -> Item {
    let parse_sess = new_parse_sess();
    let mut parser = new_parser_from_str(&parse_sess, item);
    parser
        .parse_item(ForceCollect::No)
        .unwrap()
        .unwrap()
        .into_inner()
}

#[macro_export]
macro_rules! item {
    ($($arg:tt)*) => {{
        parse_item(format!($($arg)*))
    }};
}

pub fn parse_ty_param(param: String) -> GenericParam {
    let item = item!("fn f<{}>() {{}}", param);
    let ItemKind::Fn(box mut f) = item.kind else { panic!() };
    f.generics.params.pop().unwrap()
}

#[macro_export]
macro_rules! ty_param {
    ($($arg:tt)*) => {{
        parse_ty_param(format!($($arg)*))
    }};
}

#[inline]
pub fn parse_stmt(stmt: String) -> Stmt {
    let parse_sess = new_parse_sess();
    let mut parser = new_parser_from_str(&parse_sess, stmt);
    parser.parse_stmt(ForceCollect::No).unwrap().unwrap()
}

#[macro_export]
macro_rules! stmt {
    ($($arg:tt)*) => {{
        parse_stmt(format!($($arg)*))
    }};
}

#[inline]
pub fn parse_expr(expr: String) -> Expr {
    let parse_sess = new_parse_sess();
    let mut parser = new_parser_from_str(&parse_sess, expr);
    parser.parse_expr().unwrap().into_inner()
}

#[macro_export]
macro_rules! expr {
    ($($arg:tt)*) => {{
        parse_expr(format!($($arg)*))
    }};
}

#[inline]
pub fn parse_ty(ty: String) -> Ty {
    let parse_sess = new_parse_sess();
    let mut parser = new_parser_from_str(&parse_sess, ty);
    parser.parse_ty().unwrap().into_inner()
}

#[macro_export]
macro_rules! ty {
    ($($arg:tt)*) => {{
        parse_ty(format!($($arg)*))
    }};
}

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
    symbol: &str,
    bounds: GenericBounds,
    kind: GenericParamKind,
) -> GenericParam {
    GenericParam {
        id: DUMMY_NODE_ID,
        ident: mk_ident(symbol),
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
pub fn mk_path_segment(symbol: &str, args: Option<GenericArgs>) -> PathSegment {
    PathSegment {
        ident: mk_ident(symbol),
        id: DUMMY_NODE_ID,
        args: args.map(P),
    }
}

#[inline]
pub fn mk_angle_generic_args(args: Vec<AngleBracketedArg>) -> GenericArgs {
    AngleBracketed(AngleBracketedArgs {
        span: DUMMY_SP,
        args: args.into(),
    })
}

#[inline]
pub fn mk_angle_arg(ty: Ty) -> AngleBracketedArg {
    AngleBracketedArg::Arg(GenericArg::Type(P(ty)))
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
