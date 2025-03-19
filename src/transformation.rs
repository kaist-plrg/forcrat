use std::{fs, ops::DerefMut, path::PathBuf};

use etrace::ok_or;
use rustc_ast::{ast::*, mut_visit, mut_visit::MutVisitor, ptr::P};
use rustc_ast_pretty::pprust;
use rustc_hash::FxHashMap;
use rustc_index::bit_set::BitSet;
use rustc_middle::{mir, ty::TyCtxt};
use rustc_span::{source_map::SourceMap, FileName, RealFileName, Symbol};

use crate::{
    api_list::{is_symbol_api, Permission},
    ast_maker::*,
    compile_util::{self, LoHi, Pass},
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
            let parse_sess = new_parse_sess();
            let mut parser = rustc_parse::new_parser_from_file(&parse_sess, &path, None);
            let mut krate = parser.parse_crate_mod().unwrap();
            let mut visitor = TransformVisitor {
                source_map: parse_sess.source_map(),
                fn_permissions: fn_permissions.get(&path).unwrap_or(&empty),
            };
            visitor.visit_crate(&mut krate);
            let s = pprust::crate_to_string_for_macros(&krate);
            fs::write(path, s).unwrap();
        }
    }
}

struct TransformVisitor<'a> {
    source_map: &'a SourceMap,
    fn_permissions: &'a FxHashMap<LoHi, Vec<&'a BitSet<Permission>>>,
}

impl MutVisitor for TransformVisitor<'_> {
    fn visit_item_kind(&mut self, item: &mut ItemKind) {
        mut_visit::noop_visit_item_kind(item, self);

        if let ItemKind::Fn(f) = item {
            let (_, lh) = compile_util::span_to_plh(f.sig.span, self.source_map).unwrap();
            if let Some(permissions) = self.fn_permissions.get(&lh) {
                let mut ps = BitSet::new_empty(Permission::NUM);
                for (param, perm) in f.sig.decl.inputs.iter_mut().zip(permissions) {
                    if !perm.is_empty() {
                        *param.ty = ty!("Option<TTT>");
                        ps.union(*perm);
                    }
                }
                if !ps.is_empty() {
                    let mut param = "TTT: ".to_string();
                    for (i, p) in ps.iter().enumerate() {
                        if i > 0 {
                            param.push_str(" + ");
                        }
                        use std::fmt::Write;
                        write!(param, "std::io::{:?}", p).unwrap();
                    }
                    f.generics.params.push(parse_ty_param(param));
                }
            }
        }
    }

    fn visit_expr(&mut self, expr: &mut P<Expr>) {
        mut_visit::noop_visit_expr(expr, self);
        if let ExprKind::Call(callee, args) = &mut expr.kind {
            if let ExprKind::Path(None, path) = &callee.kind {
                if let [seg] = &path.segments[..] {
                    let symbol = seg.ident.name;
                    match symbol.as_str() {
                        "fopen" => {
                            let [path, mode] = &args[..] else { panic!() };
                            let mode = normalize_open_mode(mode);
                            match mode {
                                OpenMode::Lit(mode) => {
                                    let (prefix, _suffix) = mode.as_str().split_at(1);
                                    match prefix {
                                        "r" => {
                                            let new_expr = expr!(
                                                "std::fs::File::open(std::ffi::CStr::from_ptr(({}) as _).to_str().unwrap()).ok()",
                                                pprust::expr_to_string(path)
                                            );
                                            *expr.deref_mut() = new_expr;
                                        }
                                        "w" => todo!(),
                                        "a" => todo!(),
                                        _ => panic!("{:?}", mode),
                                    }
                                }
                                OpenMode::If(_c, _t, _f) => todo!(),
                                OpenMode::Other(_e) => todo!(),
                            }
                        }
                        "fclose" => {
                            *callee.deref_mut() = expr!("drop");
                        }
                        "fgetc" | "getc" => {
                            let [stream] = &args[..] else { panic!() };
                            let stream = pprust::expr_to_string(stream);
                            let new_expr = expr!("{{
                                let mut buf = [0];
                                ({}).unwrap().read_exact(&mut buf).map_or(libc::EOF, |_| buf[0] as _)
                            }}", stream);
                            *expr.deref_mut() = new_expr;
                        }
                        _ => {}
                    }
                }
            }
        }
    }
}

#[derive(Debug)]
enum OpenMode<'a> {
    Lit(Symbol),
    If(&'a Expr, Box<OpenMode<'a>>, Box<OpenMode<'a>>),
    Other(&'a Expr),
}

fn normalize_open_mode(expr: &Expr) -> OpenMode<'_> {
    match &expr.kind {
        ExprKind::MethodCall(box MethodCall { receiver: e, .. }) | ExprKind::Cast(e, _) => {
            normalize_open_mode(e)
        }
        ExprKind::Lit(lit) => OpenMode::Lit(lit.symbol),
        ExprKind::If(c, t, Some(f)) => {
            let [t] = &t.stmts[..] else { panic!() };
            let StmtKind::Expr(t) = &t.kind else { panic!() };
            let t = normalize_open_mode(t);
            let f = normalize_open_mode(f);
            OpenMode::If(c, Box::new(t), Box::new(f))
        }
        _ => OpenMode::Other(expr),
    }
}
