use std::{
    fs,
    ops::{Deref, DerefMut},
};

use etrace::some_or;
use rustc_ast::{ast::*, mut_visit, mut_visit::MutVisitor, ptr::P};
use rustc_ast_pretty::pprust;
use rustc_hash::FxHashMap;
use rustc_index::bit_set::BitSet;
use rustc_middle::{mir, ty::TyCtxt};
use rustc_span::{FileName, RealFileName, Span, Symbol};

use crate::{
    api_list::{is_symbol_api, Origin, Permission},
    ast_maker::*,
    compile_util::{self, Pass},
    file_analysis::{self, Loc},
    printf,
};

pub fn write_to_files(fss: &[(FileName, String)]) -> std::io::Result<()> {
    for (f, s) in fss {
        let FileName::Real(RealFileName::LocalPath(p)) = f else { panic!() };
        fs::write(p, s)?;
    }
    Ok(())
}

#[derive(Debug, Clone, Copy)]
pub struct Transformation;

impl Pass for Transformation {
    type Out = Vec<(FileName, String)>;

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out {
        let analysis_result = file_analysis::FileAnalysis.run(tcx);
        let hir = tcx.hir();
        let source_map = tcx.sess.source_map();

        let mut fn_permissions: FxHashMap<_, _> = FxHashMap::default();
        let mut local_origins: FxHashMap<_, _> = FxHashMap::default();
        let mut call_file_args: FxHashMap<_, _> = FxHashMap::default();

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
                        local_origins.insert(local.source_info.span, o);
                    }
                }
                fn_permissions.insert(sig.span, permissions);

                for bbd in body.basic_blocks.iter() {
                    let terminator = bbd.terminator();
                    let mir::TerminatorKind::Call { args, .. } = &terminator.kind else { continue };
                    let span = terminator.source_info.span;
                    let file_args: Vec<_> = args
                        .iter()
                        .enumerate()
                        .filter_map(|(i, arg)| {
                            let ty = arg.ty(&body.local_decls, tcx);
                            if compile_util::contains_file_ty(ty, tcx) {
                                Some(i)
                            } else {
                                None
                            }
                        })
                        .collect();
                    if file_args.is_empty() {
                        continue;
                    }
                    call_file_args.insert(span, file_args);
                }
            }
        }

        let parse_sess = new_parse_sess();
        let mut updated = vec![];

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
            );
            let mut krate = parser.parse_crate_mod().unwrap();
            let mut visitor = TransformVisitor {
                updated: false,
                fn_permissions: &fn_permissions,
                local_origins: &local_origins,
                call_file_args: &call_file_args,
            };
            visitor.visit_crate(&mut krate);
            if visitor.updated {
                let s = pprust::crate_to_string_for_macros(&krate);
                updated.push((file.name.clone(), s));
            }
        }

        updated
    }
}

struct TransformVisitor<'a> {
    updated: bool,
    fn_permissions: &'a FxHashMap<Span, Vec<&'a BitSet<Permission>>>,
    local_origins: &'a FxHashMap<Span, &'a BitSet<Origin>>,
    call_file_args: &'a FxHashMap<Span, Vec<usize>>,
}

impl MutVisitor for TransformVisitor<'_> {
    fn visit_item_kind(&mut self, item: &mut ItemKind) {
        mut_visit::noop_visit_item_kind(item, self);

        if let ItemKind::Fn(f) = item {
            if let Some(permissions) = self.fn_permissions.get(&f.sig.span) {
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

        if let Some(origins) = self.local_origins.get(&local.pat.span) {
            if !origins.is_empty() {
                self.updated = true;
                let origins: Vec<_> = origins.iter().collect();
                let [origin] = &origins[..] else { panic!() };
                let ty = match origin {
                    Origin::File => ty!("Option<std::fs::File>"),
                    Origin::Stdin => ty!("Option<std::io::Stdin>"),
                    Origin::Stdout => ty!("Option<std::io::Stdout>"),
                    Origin::Stderr => ty!("Option<std::io::Stderr>"),
                    _ => panic!(),
                };
                *local.ty.as_mut().unwrap() = P(ty);
            }
        }
    }

    fn visit_expr(&mut self, expr: &mut P<Expr>) {
        mut_visit::noop_visit_expr(expr, self);
        let expr_span = expr.span;
        match &mut expr.kind {
            ExprKind::Call(callee, args) => {
                if let ExprKind::Path(None, path) = &callee.kind {
                    if let [seg] = &path.segments[..] {
                        let symbol = seg.ident.name;
                        match symbol.as_str() {
                            "fopen" => {
                                self.updated = true;
                                let new_expr = transform_fopen(&args[0], &args[1]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fclose" => {
                                self.updated = true;
                                *callee.deref_mut() = expr!("drop");
                            }
                            "fscanf" => todo!(),
                            "fgetc" | "getc" => {
                                self.updated = true;
                                let stream = pprust::expr_to_string(&args[0]);
                                let new_expr = transform_fgetc(&stream);
                                *expr.deref_mut() = new_expr;
                            }
                            "getchar" => {
                                self.updated = true;
                                let stream = "Some(std::io::stdin())";
                                let new_expr = transform_fgetc(stream);
                                *expr.deref_mut() = new_expr;
                            }
                            "fgets" => todo!(),
                            "fread" => todo!(),
                            "getdelim" => todo!(),
                            "getline" => todo!(),
                            "fprintf" => {
                                self.updated = true;
                                let stream = pprust::expr_to_string(&args[0]);
                                let new_expr = transform_fprintf(&stream, &args[1..]);
                                *expr.deref_mut() = new_expr;
                            }
                            "printf" => {
                                self.updated = true;
                                let stream = "Some(std::io::stdout())";
                                let new_expr = transform_fprintf(stream, args);
                                *expr.deref_mut() = new_expr;
                            }
                            "wprintf" => todo!(),
                            "vfprintf" => todo!(),
                            "vprintf" => todo!(),
                            "fputc" | "putc" => {
                                self.updated = true;
                                let stream = pprust::expr_to_string(&args[1]);
                                let new_expr = transform_fputc(&stream, &args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "putchar" => {
                                self.updated = true;
                                let stream = "Some(std::io::stdout())";
                                let new_expr = transform_fputc(stream, &args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fputs" => {
                                self.updated = true;
                                let new_expr = transform_fputs(&args[1], &args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "puts" => {
                                self.updated = true;
                                let new_expr = transform_puts(&args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fwrite" => todo!(),
                            "fflush" => {
                                self.updated = true;
                                let new_expr = transform_fflush(&args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fseek" | "fseeko" => todo!(),
                            "ftell" | "ftello" => {
                                self.updated = true;
                                let new_expr = transform_ftell(&args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "rewind" => {
                                self.updated = true;
                                let new_expr = transform_rewind(&args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fgetpos" => todo!(),
                            "fsetpos" => todo!(),
                            _ => {
                                if let Some(pos) = self.call_file_args.get(&expr_span) {
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
            ExprKind::Path(None, path) => {
                if let [seg] = &path.segments[..] {
                    match seg.ident.name.as_str() {
                        "stdin" => *expr = P(expr!("Some(std::io::stdin())")),
                        "stdout" => *expr = P(expr!("Some(std::io::stdout())")),
                        "stderr" => *expr = P(expr!("Some(std::io::stderr())")),
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }
}

#[inline]
fn transform_fopen(path: &Expr, mode: &Expr) -> Expr {
    let path = pprust::expr_to_string(path);
    let path = format!(
        "std::ffi::CStr::from_ptr(({}) as _).to_str().unwrap()",
        path
    );
    let mode = StringArg::from_expr(mode);
    match mode {
        StringArg::Lit(mode) => {
            let (prefix, suffix) = mode.as_str().split_at(1);
            let plus = suffix.contains('+');
            match prefix {
                "r" => {
                    if plus {
                        expr!(
                            "std::fs::OpenOptions::new()
                                .read(true)
                                .write(true)
                                .open({})
                                .ok()",
                            path
                        )
                    } else {
                        expr!("std::fs::File::open({}).ok()", path)
                    }
                }
                "w" => {
                    if plus {
                        expr!(
                            "std::fs::OpenOptions::new()
                                .write(true)
                                .create(true)
                                .truncate(true)
                                .read(true)
                                .open({})
                                .ok()",
                            path
                        )
                    } else {
                        expr!("std::fs::File::create({}).ok()", path)
                    }
                }
                "a" => {
                    if plus {
                        expr!(
                            "std::fs::OpenOptions::new()
                                .append(true)
                                .create(true)
                                .read(true)
                                .open({})
                                .ok()",
                            path
                        )
                    } else {
                        expr!(
                            "std::fs::OpenOptions::new()
                                .append(true)
                                .create(true)
                                .open({})
                                .ok()",
                            path
                        )
                    }
                }
                _ => panic!("{:?}", mode),
            }
        }
        StringArg::If(_c, _t, _f) => todo!(),
        StringArg::Other(_e) => todo!(),
    }
}

#[inline]
fn transform_fgetc(stream: &str) -> Expr {
    expr!(
        "{{
    use std::io::Read;
    let mut buf = [0];
    ({}).as_mut().unwrap().read_exact(&mut buf).map_or(libc::EOF, |_| buf[0] as _)
}}",
        stream
    )
}

fn transform_fprintf<E: Deref<Target = Expr>>(stream: &str, args: &[E]) -> Expr {
    let [fmt, args @ ..] = args else { panic!() };
    let fmt = StringArg::from_expr(fmt);
    match fmt {
        StringArg::Lit(fmt) => {
            let fmt = fmt.to_string().into_bytes();
            let (fmt, casts) = printf::to_rust_format(&fmt);
            assert!(args.len() == casts.len());
            let mut new_args = String::new();
            for (arg, cast) in args.iter().zip(casts) {
                use std::fmt::Write;
                let arg = pprust::expr_to_string(arg);
                if cast == "&str" {
                    write!(
                        new_args,
                        "std::ffi::CStr::from_ptr(({}) as _).to_str().unwrap(), ",
                        arg
                    )
                    .unwrap();
                } else {
                    write!(new_args, "({}) as {}, ", arg, cast).unwrap();
                }
            }
            expr!(
                "{{
    use std::io::Write;
    write!(({}).as_mut().unwrap(), \"{}\", {})
}}",
                stream,
                fmt,
                new_args
            )
        }
        StringArg::If(_, _, _) => todo!(),
        StringArg::Other(_) => todo!(),
    }
}

#[inline]
fn transform_fputc(stream: &str, c: &Expr) -> Expr {
    let c = pprust::expr_to_string(c);
    expr!(
        "{{
    use std::io::Write;
    let c = {};
    ({}).as_mut().unwrap().write_all(&[c as u8]).map_or(libc::EOF, |_| c)
}}",
        c,
        stream
    )
}

#[inline]
fn transform_fputs(stream: &Expr, s: &Expr) -> Expr {
    let stream = pprust::expr_to_string(stream);
    let s = pprust::expr_to_string(s);
    expr!(
        "{{
    use std::io::Write;
    ({}).as_mut().unwrap()
        .write_all(std::ffi::CStr::from_ptr(({}) as _).to_bytes())
        .map_or(libc::EOF, |_| 0)
}}",
        stream,
        s
    )
}

#[inline]
fn transform_fflush(stream: &Expr) -> Expr {
    let stream = pprust::expr_to_string(stream);
    expr!(
        "{{
    use std::io::Write;
    ({}).as_mut().unwrap().flush().map_or(libc::EOF, |_| 0)
}}",
        stream
    )
}

#[inline]
fn transform_puts(s: &Expr) -> Expr {
    let s = pprust::expr_to_string(s);
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

#[inline]
fn transform_ftell(stream: &Expr) -> Expr {
    let stream = pprust::expr_to_string(stream);
    expr!(
        "{{
    use std::io::Seek;
    ({}).as_mut().unwrap().stream_position().map_or(-1, |p| p as i64)
}}",
        stream
    )
}

#[inline]
fn transform_rewind(stream: &Expr) -> Expr {
    let stream = pprust::expr_to_string(stream);
    expr!(
        "{{
    use std::io::Seek;
    ({}).as_mut().unwrap().rewind();
}}",
        stream
    )
}

#[derive(Debug)]
enum StringArg<'a> {
    Lit(Symbol),
    If(&'a Expr, Box<StringArg<'a>>, Box<StringArg<'a>>),
    Other(&'a Expr),
}

impl<'a> StringArg<'a> {
    fn from_expr(expr: &'a Expr) -> Self {
        match &expr.kind {
            ExprKind::MethodCall(box MethodCall { receiver: e, .. }) | ExprKind::Cast(e, _) => {
                Self::from_expr(e)
            }
            ExprKind::Lit(lit) => StringArg::Lit(lit.symbol),
            ExprKind::If(c, t, Some(f)) => {
                let [t] = &t.stmts[..] else { panic!() };
                let StmtKind::Expr(t) = &t.kind else { panic!() };
                let t = Self::from_expr(t);
                let f = Self::from_expr(f);
                StringArg::If(c, Box::new(t), Box::new(f))
            }
            _ => StringArg::Other(expr),
        }
    }
}

#[cfg(test)]
mod tests;
