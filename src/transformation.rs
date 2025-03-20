use std::{fs, ops::DerefMut, path::PathBuf};

use etrace::{ok_or, some_or};
use rustc_ast::{ast::*, mut_visit, mut_visit::MutVisitor, ptr::P};
use rustc_ast_pretty::pprust;
use rustc_hash::FxHashMap;
use rustc_index::bit_set::BitSet;
use rustc_middle::{mir, ty::TyCtxt};
use rustc_span::{source_map::SourceMap, FileName, RealFileName, Symbol};

use crate::{
    api_list::{is_symbol_api, Origin, Permission},
    ast_maker::*,
    compile_util::{self, contains_file_ty, LoHi, Pass},
    file_analysis::{self, Loc},
};

#[derive(Debug, Clone, Copy)]
pub struct Transformation;

impl Pass for Transformation {
    type Out = Vec<(PathBuf, String)>;

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out {
        let source_map = tcx.sess.source_map();

        let files = source_map.files();
        let lib = files.iter().next().unwrap();
        let dir = match &lib.name {
            // normal input
            FileName::Real(RealFileName::LocalPath(lib_path)) => {
                Some(fs::canonicalize(lib_path.parent().unwrap()).unwrap())
            }
            // test input
            FileName::Custom(_) => None,
            _ => panic!(),
        };
        drop(files);

        let analysis_result = file_analysis::FileAnalysis.run(tcx);

        let hir = tcx.hir();
        let mut fn_permissions: FxHashMap<_, FxHashMap<_, _>> = FxHashMap::default();
        let mut local_origins: FxHashMap<_, FxHashMap<_, _>> = FxHashMap::default();
        let mut call_file_args: FxHashMap<_, FxHashMap<_, _>> = FxHashMap::default();

        for item_id in hir.items() {
            let item = hir.item(item_id);
            let local_def_id = item.owner_id.def_id;
            if let rustc_hir::ItemKind::Fn(sig, _, _) = item.kind {
                if is_symbol_api(item.ident.name) || item.ident.name.as_str() == "main" {
                    continue;
                }
                let body = tcx.optimized_mir(local_def_id);
                let mut permissions = vec![];
                for (i, local) in body.local_decls.iter_enumerated() {
                    let loc = Loc::Var(local_def_id, i);
                    let loc_id = some_or!(analysis_result.loc_ind_map.get(&loc), continue);
                    let i = i.as_usize();
                    if i == 0 {
                        // return value
                    } else if i <= sig.decl.inputs.len() {
                        // parameters
                        let p = &analysis_result.permissions[*loc_id];
                        permissions.push(p);
                    } else {
                        let o = &analysis_result.origins[*loc_id];
                        let span = local.source_info.span;
                        let (fname, lh) = compile_util::span_to_flh(span, source_map);
                        local_origins.entry(fname).or_default().insert(lh, o);
                    }
                }
                let (fname, lh) = compile_util::span_to_flh(sig.span, source_map);
                fn_permissions
                    .entry(fname)
                    .or_default()
                    .insert(lh, permissions);

                for bbd in body.basic_blocks.iter() {
                    let terminator = bbd.terminator();
                    let mir::TerminatorKind::Call { args, .. } = &terminator.kind else { continue };
                    let span = terminator.source_info.span;
                    let file_args: Vec<_> = args
                        .iter()
                        .enumerate()
                        .filter_map(|(i, arg)| {
                            let ty = arg.ty(&body.local_decls, tcx);
                            if contains_file_ty(ty, tcx) {
                                Some(i)
                            } else {
                                None
                            }
                        })
                        .collect();
                    if file_args.is_empty() {
                        continue;
                    }
                    let (fname, lh) = compile_util::span_to_flh(span, source_map);
                    call_file_args
                        .entry(fname)
                        .or_default()
                        .insert(lh, file_args);
                }
            }
        }

        let mut updated = vec![];
        for file in source_map.files().iter() {
            let parse_sess = new_parse_sess();
            let (path, mut parser) = if let Some(dir) = &dir {
                // normal input
                let FileName::Real(RealFileName::LocalPath(path)) = &file.name else { continue };
                let path = ok_or!(fs::canonicalize(path), continue);
                if !path.starts_with(dir) {
                    continue;
                }
                let parser = rustc_parse::new_parser_from_file(&parse_sess, &path, None);
                (path, parser)
            } else {
                // test input
                let FileName::Custom(path) = &file.name else { continue };
                if path != "main.rs" {
                    continue;
                }
                let code = file.src.as_ref().unwrap();
                let parser = new_parser_from_str(&parse_sess, code.to_string());
                (PathBuf::from("main.rs"), parser)
            };
            let mut krate = parser.parse_crate_mod().unwrap();
            let mut visitor = TransformVisitor {
                updated: false,
                source_map: parse_sess.source_map(),
                fn_permissions: fn_permissions.get(&file.name),
                local_origins: local_origins.get(&file.name),
                call_file_args: call_file_args.get(&file.name),
            };
            visitor.visit_crate(&mut krate);
            if visitor.updated {
                let s = pprust::crate_to_string_for_macros(&krate);
                updated.push((path, s));
            }
        }

        updated
    }
}

struct TransformVisitor<'a> {
    updated: bool,
    source_map: &'a SourceMap,
    fn_permissions: Option<&'a FxHashMap<LoHi, Vec<&'a BitSet<Permission>>>>,
    local_origins: Option<&'a FxHashMap<LoHi, &'a BitSet<Origin>>>,
    call_file_args: Option<&'a FxHashMap<LoHi, Vec<usize>>>,
}

impl<'a> TransformVisitor<'a> {
    #[inline]
    fn fn_permissions(&self, lh: LoHi) -> Option<&[&'a BitSet<Permission>]> {
        self.fn_permissions?.get(&lh).map(|v| &v[..])
    }

    #[inline]
    fn local_origins(&self, lh: LoHi) -> Option<&'a BitSet<Origin>> {
        self.local_origins?.get(&lh).copied()
    }

    #[inline]
    fn call_file_args(&self, lh: LoHi) -> Option<&[usize]> {
        self.call_file_args?.get(&lh).map(|v| &v[..])
    }
}

impl MutVisitor for TransformVisitor<'_> {
    fn visit_item_kind(&mut self, item: &mut ItemKind) {
        mut_visit::noop_visit_item_kind(item, self);

        if let ItemKind::Fn(f) = item {
            let (_, lh) = compile_util::span_to_flh(f.sig.span, self.source_map);
            if let Some(permissions) = self.fn_permissions(lh) {
                let mut ps = BitSet::new_empty(Permission::NUM);
                for (param, perm) in f.sig.decl.inputs.iter_mut().zip(permissions) {
                    if !perm.is_empty() {
                        *param.ty = ty!("Option<TTT>");
                        ps.union(*perm);
                    }
                }
                if !ps.is_empty() {
                    self.updated = true;
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

    fn visit_local(&mut self, local: &mut P<Local>) {
        mut_visit::noop_visit_local(local, self);

        let (_, lh) = compile_util::span_to_flh(local.pat.span, self.source_map);
        if let Some(origins) = self.local_origins(lh) {
            if !origins.is_empty() {
                self.updated = true;
                let origins: Vec<_> = origins.iter().collect();
                let [origin] = &origins[..] else { panic!() };
                match origin {
                    Origin::File => {
                        *local.ty.as_mut().unwrap() = P(ty!("Option<std::fs::File>"));
                    }
                    Origin::Stdin => todo!(),
                    Origin::Stdout => todo!(),
                    Origin::Stderr => todo!(),
                    _ => panic!(),
                }
            }
        }
    }

    fn visit_expr(&mut self, expr: &mut P<Expr>) {
        mut_visit::noop_visit_expr(expr, self);
        let (_, lh) = compile_util::span_to_flh(expr.span, self.source_map);
        if let ExprKind::Call(callee, args) = &mut expr.kind {
            if let ExprKind::Path(None, path) = &callee.kind {
                if let [seg] = &path.segments[..] {
                    let symbol = seg.ident.name;
                    match symbol.as_str() {
                        "fopen" => {
                            self.updated = true;
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
                            self.updated = true;
                            *callee.deref_mut() = expr!("drop");
                        }
                        "fgetc" | "getc" => {
                            self.updated = true;
                            let [stream] = &args[..] else { panic!() };
                            let stream = pprust::expr_to_string(stream);
                            let new_expr = expr!("{{
                                let mut buf = [0];
                                ({}).as_mut().unwrap().read_exact(&mut buf).map_or(libc::EOF, |_| buf[0] as _)
                            }}", stream);
                            *expr.deref_mut() = new_expr;
                        }
                        _ => {
                            if let Some(pos) = self.call_file_args(lh) {
                                for i in pos {
                                    let arg = &mut args[*i];
                                    let a = pprust::expr_to_string(arg);
                                    let new_expr = expr!("({}).as_mut()", a);
                                    *arg = P(new_expr);
                                }
                                self.updated = true;
                            }
                        }
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

#[cfg(test)]
mod tests;
