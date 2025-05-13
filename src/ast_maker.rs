use rustc_ast::*;
use rustc_parse::parser::{AttemptLocalParseRecovery, ForceCollect, Parser};
use rustc_session::parse::ParseSess;
use rustc_span::FileName;

#[inline]
pub fn new_parse_sess() -> ParseSess {
    ParseSess::with_silent_emitter(vec![], "".to_string(), false)
}

#[inline]
pub fn new_parser_from_str(parse_sess: &ParseSess, s: String) -> Parser<'_> {
    let file_name = FileName::Custom("main.rs".to_string());
    rustc_parse::new_parser_from_source_str(parse_sess, file_name, s).unwrap()
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

pub fn parse_param(param: String) -> Param {
    let item = item!("fn f({}) {{}}", param);
    let ItemKind::Fn(box mut f) = item.kind else { panic!() };
    f.sig.decl.inputs.pop().unwrap()
}

#[macro_export]
macro_rules! param {
    ($($arg:tt)*) => {{
        parse_param(format!($($arg)*))
    }};
}

#[inline]
pub fn parse_stmt(stmt: String) -> Stmt {
    let parse_sess = new_parse_sess();
    let mut parser = new_parser_from_str(&parse_sess, stmt);
    parser
        .parse_full_stmt(AttemptLocalParseRecovery::No)
        .unwrap()
        .unwrap()
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
