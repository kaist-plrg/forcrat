use std::{
    fmt::Write as _,
    fs,
    ops::{Deref, DerefMut},
};

use etrace::some_or;
use rustc_ast::{ast::*, mut_visit, mut_visit::MutVisitor, ptr::P};
use rustc_ast_pretty::pprust;
use rustc_const_eval::interpret::{ConstValue, Scalar};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{def::Res, intravisit, HirId};
use rustc_index::bit_set::BitSet;
use rustc_middle::{
    hir::nested_filter,
    mir::{self, CastKind, Constant, ConstantKind, Location, Operand, Rvalue, TerminatorKind},
    ty::TyCtxt,
};
use rustc_span::{symbol::Ident, FileName, RealFileName, Span, Symbol};

use crate::{
    api_list::{self, Origin, Permission},
    ast_maker::*,
    compile_util::{self, Pass},
    file_analysis::{self, Loc},
    rustc_middle::mir::visit::Visitor as _,
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

        // all binding occurrences of unsupported
        let mut unsupported: FxHashSet<_> = analysis_result
            .unsupported
            .iter()
            .filter_map(|loc_id| {
                let loc = analysis_result.locs[loc_id];
                match loc {
                    Loc::Var(def_id, local) => {
                        let body = tcx.optimized_mir(def_id);
                        let local_decl = &body.local_decls[local];
                        let span = local_decl.source_info.span;
                        Some(span)
                    }
                    Loc::Field(_, _) => todo!(),
                    Loc::Stdin | Loc::Stdout | Loc::Stderr => None,
                }
            })
            .collect();
        let mut hir_visitor = HirVisitor {
            tcx,
            rhs_span_to_lhs_id: FxHashMap::default(),
            lhs_id_to_rhs_spans: FxHashMap::default(),
            pat_span_to_id: FxHashMap::default(),
            path_id_to_spans: FxHashMap::default(),
        };
        hir.visit_all_item_likes_in_crate(&mut hir_visitor);
        for (span, hir_id) in &hir_visitor.pat_span_to_id {
            if !unsupported.contains(span) {
                continue;
            }
            // add all bound occurrences to unsupported
            if let Some(spans) = hir_visitor.path_id_to_spans.get(hir_id) {
                for span in spans {
                    unsupported.insert(*span);
                }
            }
            // add all rhs to unsupported
            if let Some(spans) = hir_visitor.lhs_id_to_rhs_spans.get(hir_id) {
                for span in spans {
                    unsupported.insert(*span);
                }
            }
        }

        let mut fn_permissions = FxHashMap::default();
        let mut local_origins = FxHashMap::default();
        let mut local_permissions = FxHashMap::default();
        let mut hir_id_permissions = FxHashMap::default();
        let mut call_file_args = FxHashMap::default();
        let mut null_checks = FxHashSet::default();
        let mut null_casts = FxHashSet::default();

        for item_id in hir.items() {
            let item = hir.item(item_id);
            let local_def_id = item.owner_id.def_id;
            if let rustc_hir::ItemKind::Fn(sig, _, _) = item.kind {
                if api_list::is_symbol_api(item.ident.name) || item.ident.name.as_str() == "main" {
                    continue;
                }

                let body = tcx.optimized_mir(local_def_id);
                let mut permissions = vec![];
                for (i, local) in body.local_decls.iter_enumerated() {
                    let loc = Loc::Var(local_def_id, i);
                    let i = i.as_usize();
                    if i == 0 {
                        // return value
                    } else if i <= sig.decl.inputs.len() {
                        // parameters
                        let p = analysis_result
                            .loc_ind_map
                            .get(&loc)
                            .map(|loc_id| &analysis_result.permissions[*loc_id]);
                        permissions.push(p);
                    } else {
                        let loc_id = some_or!(analysis_result.loc_ind_map.get(&loc), continue);

                        let span = local.source_info.span;

                        let o = &analysis_result.origins[*loc_id];
                        local_origins.insert(span, o);

                        let p = &analysis_result.permissions[*loc_id];
                        local_permissions.insert(span, p);
                        if let Some(hid_id) = hir_visitor.pat_span_to_id.get(&span) {
                            hir_id_permissions.insert(*hid_id, p);
                        }
                    }
                }
                if permissions.iter().any(|p| p.is_some()) {
                    fn_permissions.insert(sig.span, permissions);
                }

                for bbd in body.basic_blocks.iter() {
                    let terminator = bbd.terminator();
                    let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
                        continue;
                    };
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
                    if !file_args.is_empty() {
                        call_file_args.insert(span, file_args);
                    }

                    let [arg] = &args[..] else { continue };
                    let ty = arg.ty(&body.local_decls, tcx);
                    if !compile_util::contains_file_ty(ty, tcx) {
                        continue;
                    }
                    let constant = some_or!(func.constant(), continue);
                    let ConstantKind::Val(_, ty) = constant.literal else { unreachable!() };
                    let rustc_middle::ty::TyKind::FnDef(def_id, _) = ty.kind() else {
                        unreachable!()
                    };
                    let sym = compile_util::def_id_to_value_symbol(def_id, tcx);
                    let sym = some_or!(sym, continue);
                    if sym.as_str() == "is_null" {
                        null_checks.insert(span);
                    }
                }

                let mut visitor = MirVisitor {
                    tcx,
                    nulls: FxHashSet::default(),
                };
                visitor.visit_body(body);
                for location in visitor.nulls {
                    let stmt = body.stmt_at(location).left().unwrap();
                    null_casts.insert(stmt.source_info.span);
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
                local_permissions: &local_permissions,
                hir_id_permissions: &hir_id_permissions,
                rhs_span_to_lhs_id: &hir_visitor.rhs_span_to_lhs_id,
                call_file_args: &call_file_args,
                null_checks: &null_checks,
                null_casts: &null_casts,
                unsupported: &unsupported,
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

struct MirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    nulls: FxHashSet<Location>,
}

impl<'tcx> mir::visit::Visitor<'tcx> for MirVisitor<'tcx> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        if let Rvalue::Cast(
            CastKind::PointerFromExposedAddress,
            Operand::Constant(box Constant {
                literal: ConstantKind::Val(ConstValue::Scalar(Scalar::Int(i)), _),
                ..
            }),
            ty,
        ) = rvalue
        {
            if i.try_to_u64() == Ok(0) && compile_util::contains_file_ty(*ty, self.tcx) {
                self.nulls.insert(location);
            }
        }
        self.super_rvalue(rvalue, location);
    }
}

struct HirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// for each x = rhs, maps rhs's span to x's hir_id
    rhs_span_to_lhs_id: FxHashMap<Span, HirId>,
    /// for each x = rhs, maps x's hir_id to rhs's spans
    lhs_id_to_rhs_spans: FxHashMap<HirId, Vec<Span>>,
    /// for each x, maps binding's span to x's hir_id
    pat_span_to_id: FxHashMap<Span, HirId>,
    /// for each x, maps x's hir_id to bound occurrences' spans
    path_id_to_spans: FxHashMap<HirId, Vec<Span>>,
}

impl<'tcx> HirVisitor<'tcx> {
    fn handle_local(&mut self, local: &'tcx rustc_hir::Local<'tcx>) {
        let rustc_hir::PatKind::Binding(_, hir_id, _, _) = local.pat.kind else { return };
        let init = some_or!(local.init, return);
        self.rhs_span_to_lhs_id.insert(init.span, hir_id);
        self.lhs_id_to_rhs_spans
            .entry(hir_id)
            .or_default()
            .push(init.span);
    }

    fn handle_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
        let rustc_hir::ExprKind::Assign(lhs, rhs, _) = expr.kind else { return };
        let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = lhs.kind else {
            return;
        };
        let Res::Local(hir_id) = path.res else { return };
        self.rhs_span_to_lhs_id.insert(rhs.span, hir_id);
        self.lhs_id_to_rhs_spans
            .entry(hir_id)
            .or_default()
            .push(rhs.span);
    }

    fn handle_pat(&mut self, pat: &'tcx rustc_hir::Pat<'tcx>) {
        let rustc_hir::PatKind::Binding(_, hir_id, _, _) = pat.kind else { return };
        self.pat_span_to_id.insert(pat.span, hir_id);
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for HirVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_local(&mut self, local: &'tcx rustc_hir::Local<'tcx>) {
        self.handle_local(local);
        intravisit::walk_local(self, local);
    }

    fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
        self.handle_expr(expr);
        intravisit::walk_expr(self, expr);
    }

    fn visit_pat(&mut self, pat: &'tcx rustc_hir::Pat<'tcx>) {
        self.handle_pat(pat);
        intravisit::walk_pat(self, pat);
    }

    fn visit_path(&mut self, path: &rustc_hir::Path<'tcx>, _: HirId) {
        if let Res::Local(id) = path.res {
            self.path_id_to_spans.entry(id).or_default().push(path.span);
        }
        intravisit::walk_path(self, path);
    }
}

struct TransformVisitor<'a> {
    updated: bool,
    fn_permissions: &'a FxHashMap<Span, Vec<Option<&'a BitSet<Permission>>>>,
    local_origins: &'a FxHashMap<Span, &'a BitSet<Origin>>,
    local_permissions: &'a FxHashMap<Span, &'a BitSet<Permission>>,
    hir_id_permissions: &'a FxHashMap<HirId, &'a BitSet<Permission>>,
    rhs_span_to_lhs_id: &'a FxHashMap<Span, HirId>,
    call_file_args: &'a FxHashMap<Span, Vec<usize>>,
    null_checks: &'a FxHashSet<Span>,
    null_casts: &'a FxHashSet<Span>,
    unsupported: &'a FxHashSet<Span>,
}

impl TransformVisitor<'_> {
    fn is_unsupported(&self, expr: &Expr) -> bool {
        self.unsupported.contains(&expr.span) || self.unsupported.contains(&remove_cast(expr).span)
    }
}

fn remove_cast(expr: &Expr) -> &Expr {
    let ExprKind::Cast(expr, _) = &expr.kind else { return expr };
    remove_cast(expr)
}

impl MutVisitor for TransformVisitor<'_> {
    fn visit_item_kind(&mut self, item: &mut ItemKind) {
        mut_visit::noop_visit_item_kind(item, self);

        if let ItemKind::Fn(f) = item {
            if let Some(permissions) = self.fn_permissions.get(&f.sig.span) {
                let mut ps = BitSet::new_empty(Permission::NUM);
                for (param, perm) in f.sig.decl.inputs.iter_mut().zip(permissions) {
                    if self.unsupported.contains(&param.pat.span) {
                        continue;
                    }
                    let perm = some_or!(perm, continue);
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
                        param.push_str(p.full_name());
                    }
                    f.generics.params.push(parse_ty_param(param));
                }
            }
        }
    }

    fn visit_local(&mut self, local: &mut P<Local>) {
        mut_visit::noop_visit_local(local, self);

        if self.unsupported.contains(&local.pat.span) {
            return;
        }

        if let Some(origins) = self.local_origins.get(&local.pat.span) {
            if !origins.is_empty() {
                self.updated = true;
                let origins: Vec<_> = origins.iter().collect();
                let [origin] = &origins[..] else { panic!() };
                let ty = match origin {
                    Origin::File => {
                        let permissions = self.local_permissions[&local.pat.span];
                        if permissions.contains(Permission::Write) {
                            ty!("Option<std::io::BufWriter<std::fs::File>>")
                        } else {
                            ty!("Option<std::io::BufReader<std::fs::File>>")
                        }
                    }
                    Origin::Stdin => ty!("Option<std::io::Stdin>"),
                    Origin::Stdout => ty!("Option<std::io::Stdout>"),
                    Origin::Stderr => ty!("Option<std::io::Stderr>"),
                    Origin::PipeRead => ty!("Option<std::process::ChildStdout>"),
                    Origin::PipeWrite => ty!("Option<std::process::ChildStdin>"),
                    Origin::PipeDyn => todo!(),
                    Origin::Buffer => todo!(),
                };
                *local.ty.as_mut().unwrap() = P(ty);
            }
        }
    }

    fn visit_expr(&mut self, expr: &mut P<Expr>) {
        mut_visit::noop_visit_expr(expr, self);
        let expr_span = expr.span;
        if self.is_unsupported(expr) {
            return;
        }
        match &mut expr.kind {
            ExprKind::Call(callee, args) => {
                if let ExprKind::Path(None, path) = &callee.kind {
                    if let [seg] = &path.segments[..] {
                        let symbol = seg.ident.name;
                        match symbol.as_str() {
                            "fopen" => {
                                self.updated = true;
                                let lhs_id = self.rhs_span_to_lhs_id[&expr_span];
                                let permissions = self.hir_id_permissions[&lhs_id];
                                let new_expr = transform_fopen(&args[0], &args[1], permissions);
                                *expr.deref_mut() = new_expr;
                            }
                            "popen" => {
                                self.updated = true;
                                let new_expr = transform_popen(&args[0], &args[1]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fclose" | "pclose" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
                                self.updated = true;
                                *callee.deref_mut() = expr!("drop");
                            }
                            "fscanf" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr = transform_fscanf(&args[0], &args[1], &args[2..]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fgetc" | "getc" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
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
                            "fgets" => {
                                if self.is_unsupported(&args[2]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr = transform_fgets(&args[2], &args[0], &args[1]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fread" => {
                                if self.is_unsupported(&args[3]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr =
                                    transform_fread(&args[3], &args[0], &args[1], &args[2]);
                                *expr.deref_mut() = new_expr;
                            }
                            "getdelim" => todo!(),
                            "getline" => todo!(),
                            "feof" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr = transform_feof(&args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fprintf" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
                                self.updated = true;
                                let stream = pprust::expr_to_string(&args[0]);
                                let new_expr = transform_fprintf(&stream, &args[1], &args[2..]);
                                *expr.deref_mut() = new_expr;
                            }
                            "printf" => {
                                self.updated = true;
                                let stream = "Some(std::io::stdout())";
                                let new_expr = transform_fprintf(stream, &args[0], &args[1..]);
                                *expr.deref_mut() = new_expr;
                            }
                            "wprintf" => todo!(),
                            "vfprintf" => todo!(),
                            "vprintf" => todo!(),
                            "fputc" | "putc" => {
                                if self.is_unsupported(&args[1]) {
                                    return;
                                }
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
                                if self.is_unsupported(&args[1]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr = transform_fputs(&args[1], &args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "puts" => {
                                self.updated = true;
                                let new_expr = transform_puts(&args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fwrite" => {
                                if self.is_unsupported(&args[3]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr =
                                    transform_fwrite(&args[3], &args[0], &args[1], &args[2]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fflush" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr = transform_fflush(&args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fseek" | "fseeko" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr = transform_fseek(&args[0], &args[1], &args[2]);
                                *expr.deref_mut() = new_expr;
                            }
                            "ftell" | "ftello" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr = transform_ftell(&args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "rewind" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr = transform_rewind(&args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            "fgetpos" => todo!(),
                            "fsetpos" => todo!(),
                            "fileno" => {
                                if self.is_unsupported(&args[0]) {
                                    return;
                                }
                                self.updated = true;
                                let new_expr = transform_fileno(&args[0]);
                                *expr.deref_mut() = new_expr;
                            }
                            _ => {
                                if let Some(pos) = self.call_file_args.get(&expr_span) {
                                    let mut none = false;
                                    for i in pos {
                                        let arg = &mut args[*i];
                                        if self.is_unsupported(arg) {
                                            continue;
                                        }
                                        let a = pprust::expr_to_string(arg);
                                        let new_expr = expr!("({}).as_mut()", a);
                                        *arg = P(new_expr);
                                        self.updated = true;
                                        if a == "None" {
                                            none = true;
                                        }
                                    }
                                    if none {
                                        let c = pprust::expr_to_string(callee);
                                        let new_expr = expr!("{}::<&mut std::fs::File>", c);
                                        *callee = P(new_expr);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            ExprKind::Path(None, path) => {
                if let [seg] = &path.segments[..] {
                    match seg.ident.name.as_str() {
                        "stdin" => {
                            self.updated = true;
                            *expr = P(expr!("Some(std::io::stdin())"));
                        }
                        "stdout" => {
                            self.updated = true;
                            *expr = P(expr!("Some(std::io::stdout())"));
                        }
                        "stderr" => {
                            self.updated = true;
                            *expr = P(expr!("Some(std::io::stderr())"));
                        }
                        _ => {}
                    }
                }
            }
            ExprKind::MethodCall(box MethodCall { seg, .. }) => {
                if self.null_checks.contains(&expr_span) {
                    self.updated = true;
                    seg.ident = Ident::from_str("is_none");
                }
            }
            ExprKind::Cast(_, _) => {
                if self.null_casts.contains(&expr_span) {
                    self.updated = true;
                    *expr = P(expr!("None"));
                }
            }
            _ => {}
        }
    }
}

#[inline]
fn unwrap_some_call(expr: &Expr) -> Option<&Expr> {
    let ExprKind::Call(callee, args) = &expr.kind else { return None };
    let ExprKind::Path(None, path) = &callee.kind else { return None };
    if path.segments.last().unwrap().ident.name.as_str() != "Some" {
        return None;
    }
    let [arg] = &args[..] else { return None };
    let ExprKind::Call(callee, _) = &arg.kind else { return None };
    let ExprKind::Path(None, _) = &callee.kind else { return None };
    Some(callee)
}

#[inline]
fn make_stream_def(stream: &Expr) -> String {
    if let Some(stream) = unwrap_some_call(stream) {
        let stream = pprust::expr_to_string(stream);
        format!("let mut stream = {}();", stream)
    } else {
        let stream = pprust::expr_to_string(stream);
        format!("let stream = ({}).as_mut().unwrap();", stream)
    }
}

#[inline]
fn make_buf_stream_def(stream: &Expr) -> String {
    if let Some(stream) = unwrap_some_call(stream) {
        let stream = pprust::expr_to_string(stream);
        format!("let stream = {}(); let mut stream = stream.lock();", stream)
    } else {
        let stream = pprust::expr_to_string(stream);
        format!("let stream = ({}).as_mut().unwrap();", stream)
    }
}

fn transform_fopen(path: &Expr, mode: &Expr, permissions: &BitSet<Permission>) -> Expr {
    let path = pprust::expr_to_string(path);
    let path = format!(
        "std::ffi::CStr::from_ptr(({}) as _).to_str().unwrap()",
        path
    );
    let mode = LikelyLit::from_expr(mode);
    let wrapper = if permissions.contains(Permission::Write) {
        "std::io::BufWriter"
    } else {
        "std::io::BufReader"
    };
    match mode {
        LikelyLit::Lit(mode) => {
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
                                .ok()
                                .map({}::new)",
                            path,
                            wrapper
                        )
                    } else {
                        expr!("std::fs::File::open({}).ok().map({}::new)", path, wrapper)
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
                                .ok()
                                .map({}::new)",
                            path,
                            wrapper
                        )
                    } else {
                        expr!("std::fs::File::create({}).ok().map({}::new)", path, wrapper)
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
                                .ok()
                                .map({}::new)",
                            path,
                            wrapper
                        )
                    } else {
                        expr!(
                            "std::fs::OpenOptions::new()
                                .append(true)
                                .create(true)
                                .open({})
                                .ok()
                                .map({}::new)",
                            path,
                            wrapper
                        )
                    }
                }
                _ => panic!("{:?}", mode),
            }
        }
        LikelyLit::If(_c, _t, _f) => todo!(),
        LikelyLit::Other(_e) => todo!(),
    }
}

fn transform_popen(command: &Expr, mode: &Expr) -> Expr {
    let command = pprust::expr_to_string(command);
    let command = format!(
        "std::ffi::CStr::from_ptr(({}) as _).to_str().unwrap()",
        command
    );
    let mode = LikelyLit::from_expr(mode);
    match mode {
        LikelyLit::Lit(mode) => {
            let field = match &mode.as_str()[..1] {
                "r" => "stdout",
                "w" => "stdin",
                _ => panic!("{:?}", mode),
            };
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
        LikelyLit::If(_c, _t, _f) => todo!(),
        LikelyLit::Other(_e) => todo!(),
    }
}

fn transform_fscanf<E: Deref<Target = Expr>>(stream: &Expr, fmt: &Expr, args: &[E]) -> Expr {
    let stream_def = make_buf_stream_def(stream);
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
    {}
    let mut count = 0i32;
    {}
    count
}}",
                stream_def,
                code
            )
        }
        LikelyLit::If(_, _, _) => todo!(),
        LikelyLit::Other(_) => todo!(),
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

#[inline]
fn transform_fgets(stream: &Expr, s: &Expr, n: &Expr) -> Expr {
    let stream_def = make_buf_stream_def(stream);
    let s = pprust::expr_to_string(s);
    let n = pprust::expr_to_string(n);
    expr!(
        "{{
    use std::io::BufRead;
    {}
    let s = {};
    let n = ({}) as usize;
    let buf: &mut [u8] = std::slice::from_raw_parts_mut(s as _, n);
    let mut pos = 0;
    while pos < n - 1 {{
        let available = match stream.fill_buf() {{
            Ok(buf) => buf,
            Err(_) => {{
                pos = 0;
                break
            }}
        }};
        if available.is_empty() {{
            break;
        }}
        buf[pos] = available[0];
        stream.consume(1);
        pos += 1;
        if buf[pos - 1] == b'\\n' {{
            break;
        }}
    }}
    if pos == 0 {{
        std::ptr::null_mut()
    }} else {{
        buf[pos] = 0;
        s
    }}
}}",
        stream_def,
        s,
        n
    )
}

#[inline]
fn transform_fread(stream: &Expr, ptr: &Expr, size: &Expr, nitems: &Expr) -> Expr {
    let stream_def = make_stream_def(stream);
    let ptr = pprust::expr_to_string(ptr);
    let size = pprust::expr_to_string(size);
    let nitems = pprust::expr_to_string(nitems);
    expr!(
        "{{
    use std::io::Read;
    {}
    let size = {};
    let ptr: &mut [u8] = std::slice::from_raw_parts_mut(({}) as _, (size * ({})) as usize);
    let mut i = 0;
    for data in ptr.chunks_mut(size as usize) {{
        if stream.read_exact(data).is_err() {{
            break;
        }}
        i += 1;
    }}
    i
}}",
        stream_def,
        size,
        ptr,
        nitems,
    )
}

#[inline]
fn transform_feof(stream: &Expr) -> Expr {
    let stream = pprust::expr_to_string(stream);
    expr!(
        "{{
    use std::io::Read;
    let mut buf = [0];
    ({}).as_mut().unwrap().read_exact(&mut buf).map_or(1, |_| 0)
}}",
        stream
    )
}

fn transform_fprintf<E: Deref<Target = Expr>>(stream: &str, fmt: &Expr, args: &[E]) -> Expr {
    let fmt = LikelyLit::from_expr(fmt);
    match fmt {
        LikelyLit::Lit(fmt) => {
            let fmt = fmt.to_string().into_bytes();
            let (fmt, casts) = printf::to_rust_format(&fmt);
            assert!(args.len() == casts.len());
            let mut new_args = String::new();
            for (arg, cast) in args.iter().zip(casts) {
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
        LikelyLit::If(_, _, _) => todo!(),
        LikelyLit::Other(_) => todo!(),
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
fn transform_fwrite(stream: &Expr, ptr: &Expr, size: &Expr, nitems: &Expr) -> Expr {
    let stream_def = make_stream_def(stream);
    let ptr = pprust::expr_to_string(ptr);
    let size = pprust::expr_to_string(size);
    let nitems = pprust::expr_to_string(nitems);
    expr!(
        "{{
    use std::io::Write;
    {}
    let size = {};
    let ptr: &[u8] = std::slice::from_raw_parts({} as _, (size * ({})) as usize);
    let mut i = 0;
    for data in ptr.chunks(size as usize) {{
        if stream.write_all(data).is_err() {{
            break;
        }}
        i += 1;
    }}
    i
}}",
        stream_def,
        size,
        ptr,
        nitems
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
fn transform_fseek(stream: &Expr, off: &Expr, whence: &Expr) -> Expr {
    let stream = pprust::expr_to_string(stream);
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
    ({}).as_mut().unwrap().seek(std::io::SeekFrom::{}(({}) as _)).map_or(-1, |_| 0)
}}",
                stream,
                v,
                off
            )
        }
        LikelyLit::If(_, _, _) => todo!(),
        LikelyLit::Other(_) => todo!(),
    }
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

#[inline]
fn transform_fileno(stream: &Expr) -> Expr {
    let stream = pprust::expr_to_string(stream);
    expr!(
        "{{
    use std::os::fd::AsRawFd;
    ({}).as_ref().unwrap().as_raw_fd()
}}",
        stream
    )
}

#[derive(Debug)]
pub enum LikelyLit<'a> {
    Lit(Symbol),
    If(&'a Expr, Box<LikelyLit<'a>>, Box<LikelyLit<'a>>),
    Other(&'a Expr),
}

impl<'a> LikelyLit<'a> {
    pub fn from_expr(expr: &'a Expr) -> Self {
        match &expr.kind {
            ExprKind::MethodCall(box MethodCall { receiver: e, .. }) | ExprKind::Cast(e, _) => {
                Self::from_expr(e)
            }
            ExprKind::Lit(lit) => LikelyLit::Lit(lit.symbol),
            ExprKind::If(c, t, Some(f)) => {
                let [t] = &t.stmts[..] else { panic!() };
                let StmtKind::Expr(t) = &t.kind else { panic!() };
                let t = Self::from_expr(t);
                let f = Self::from_expr(f);
                LikelyLit::If(c, Box::new(t), Box::new(f))
            }
            _ => LikelyLit::Other(expr),
        }
    }
}

mod printf;
mod scanf;

#[cfg(test)]
mod tests;
