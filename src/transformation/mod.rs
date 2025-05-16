use std::{fmt::Write as _, fs};

use etrace::some_or;
use hir_ctx::*;
use rustc_abi::FIRST_VARIANT;
use rustc_ast::mut_visit::MutVisitor;
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{self as hir, HirId};
use rustc_index::IndexVec;
use rustc_middle::{
    mir,
    ty::{List, TyCtxt},
};
use rustc_span::{def_id::LocalDefId, FileName, RealFileName, Span};
use stream_ty::*;
use toml_edit::DocumentMut;
use transform_visitor::*;
use typed_arena::Arena;

use crate::{
    api_list::Permission,
    compile_util::{self, Pass},
    file_analysis::{self, Loc},
    graph,
};

pub fn write_to_files(res: &TransformationResult, dir: &std::path::Path) {
    for (f, s) in &res.files {
        let FileName::Real(RealFileName::LocalPath(p)) = f else { panic!() };
        fs::write(p, s).unwrap();
    }

    if res.tmpfile {
        let path = dir.join("Cargo.toml");
        let content = fs::read_to_string(&path).unwrap();
        let mut doc = content.parse::<DocumentMut>().unwrap();
        let dependencies = doc["dependencies"].as_table_mut().unwrap();
        if !dependencies.contains_key("tempfile") {
            dependencies["tempfile"] = toml_edit::value("3.19.1");
            fs::write(path, doc.to_string()).unwrap();
        }
    }

    let path = dir.join("c2rust-lib.rs");
    let mut contents = fs::read_to_string(&path).unwrap();
    if !contents.contains("#![feature(c_variadic)]") {
        contents = format!("#![feature(c_variadic)]\n{}", contents);
    }
    if !contents.contains("#![feature(formatting_options)]") {
        contents = format!("#![feature(formatting_options)]\n{}", contents);
    }
    contents.push_str(&res.stdio_mod());
    fs::write(path, contents).unwrap();
}

#[derive(Debug)]
pub struct TransformationResult {
    files: Vec<(FileName, String)>,
    tmpfile: bool,
    bounds: FxHashSet<TraitBound>,
}

impl TransformationResult {
    fn stdio_mod(&self) -> String {
        let mut m = "mod stdio {".to_string();
        m.push_str(LIB);
        for bound in &self.bounds {
            write!(
                m,
                " pub trait {0} : {1} {{}} impl<T: {1}> {0} for T {{}}",
                bound.trait_name(),
                bound
            )
            .unwrap();
        }
        m.push('}');
        m
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Transformation;

impl Pass for Transformation {
    type Out = TransformationResult;

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out {
        let arena = Arena::new();
        let analysis_res = file_analysis::analyze(&arena, true, tcx);

        let error_returning_fns: FxHashMap<_, Vec<_>> = analysis_res
            .returning_fns
            .iter()
            .map(|(def_id, set)| (*def_id, set.iter().copied().collect()))
            .collect();
        let error_taking_fns: FxHashMap<_, Vec<_>> = analysis_res
            .taking_fns
            .iter()
            .map(|(def_id, set)| (*def_id, set.iter().copied().collect()))
            .collect();

        // collect information from HIR
        let mut hir_visitor = HirVisitor {
            tcx,
            ctx: HirCtx::default(),
        };
        tcx.hir_visit_all_item_likes_in_crate(&mut hir_visitor);
        let hir_ctx = hir_visitor.ctx;
        let return_locals: FxHashMap<_, _> = hir_ctx
            .return_locals
            .iter()
            .filter_map(|(f, locals)| {
                if locals.len() == 1 {
                    locals.iter().next().unwrap().map(|l| (*f, l))
                } else {
                    None
                }
            })
            .collect();

        let is_stdin_unsupported = analysis_res
            .unsupported
            .contains(&analysis_res.loc_ind_map[&Loc::Stdin]);
        let is_stdout_unsupported = analysis_res
            .unsupported
            .contains(&analysis_res.loc_ind_map[&Loc::Stdout]);
        let is_stderr_unsupported = analysis_res
            .unsupported
            .contains(&analysis_res.loc_ind_map[&Loc::Stderr]);

        // all unsupported spans
        let mut unsupported = FxHashSet::default();
        let mut unsupported_returns = FxHashSet::default();
        for loc_id in &analysis_res.unsupported {
            let loc = analysis_res.locs[*loc_id];
            match loc {
                Loc::Var(def_id, local) => {
                    let span = mir_local_span(def_id, local, &return_locals, &hir_ctx, tcx);
                    unsupported.insert(span);
                    if local == mir::Local::ZERO {
                        unsupported_returns.insert(def_id);
                        if let Some(spans) = hir_ctx.return_spans.get(&def_id) {
                            for span in spans {
                                unsupported.insert(*span);
                            }
                        }
                    }
                }
                Loc::Field(def_id, field_idx) => {
                    let node = tcx.hir_node_by_def_id(def_id);
                    let hir::Node::Item(item) = node else { panic!() };
                    let (hir::ItemKind::Struct(vd, _) | hir::ItemKind::Union(vd, _)) = item.kind
                    else {
                        panic!()
                    };
                    let hir::VariantData::Struct { fields, .. } = vd else { panic!() };
                    unsupported.insert(fields[field_idx.as_usize()].span);
                }
                Loc::Stdin | Loc::Stdout | Loc::Stderr => {}
            }
        }
        let mut unsupported_locs = FxHashSet::default();
        for (span, loc) in &hir_ctx.binding_span_to_loc {
            if !unsupported.contains(span) {
                continue;
            }
            unsupported_locs.insert(*loc);
            let bounds = some_or!(hir_ctx.loc_to_bound_spans.get(loc), continue);
            for span in bounds {
                // add bound occurrence to unsupported
                unsupported.insert(*span);

                // add rhs to unsupported
                if let Some(span) = hir_ctx.lhs_to_rhs.get(span) {
                    unsupported.extend(span);
                }
            }
        }

        let fn_ptr_args: FxHashSet<_> = hir_ctx
            .fn_ptr_arg_spans
            .iter()
            .filter_map(|span| hir_ctx.bound_span_to_loc.get(span))
            .collect();

        let mut param_to_hir_loc = FxHashMap::default();
        let mut hir_loc_to_param = FxHashMap::default();
        let mut non_generic_params = FxHashSet::default();
        let mut loc_id_to_hir_locs = IndexVec::from_raw(vec![None; analysis_res.locs.len()]);
        let mut hir_loc_to_loc_id = FxHashMap::default();
        for (loc_id, loc) in analysis_res.locs.iter_enumerated() {
            let (hir_locs, ctx) = match loc {
                Loc::Var(def_id, local) => {
                    let hir::Node::Item(item) = tcx.hir_node_by_def_id(*def_id) else { panic!() };
                    match item.kind {
                        hir::ItemKind::Fn { sig, .. } => {
                            let mut locs = vec![];
                            let is_static_return = if *local == mir::Local::ZERO {
                                locs.push(HirLoc::Return(*def_id));
                                hir_ctx.return_statics.contains_key(def_id)
                            } else {
                                false
                            };
                            let span =
                                mir_local_span(*def_id, *local, &return_locals, &hir_ctx, tcx);
                            if let Some(loc) = hir_ctx.binding_span_to_loc.get(&span) {
                                locs.push(*loc);
                            }
                            if locs.is_empty() {
                                continue;
                            }

                            let body = tcx.optimized_mir(*def_id);
                            let ty = body.local_decls[*local].ty;
                            let mut is_param_without_assign = false;

                            if (1..=sig.decl.inputs.len()).contains(&local.as_usize()) {
                                // if this local is a parameter
                                let param = Parameter {
                                    func: *def_id,
                                    index: local.as_usize() - 1,
                                };
                                let loc = locs[0];
                                param_to_hir_loc.insert(param, loc);
                                hir_loc_to_param.insert(loc, param);

                                if analysis_res.fn_ptrs.contains(def_id)
                                    || fn_ptr_args.contains(&loc)
                                    || analysis_res.permissions[loc_id].contains(Permission::Lock)
                                    || compile_util::is_file_ptr_ptr(ty, tcx)
                                    || file_param_index(ty, tcx).is_some()
                                    || hir_ctx.is_loc_used_in_assign(loc)
                                {
                                    non_generic_params.insert(param);
                                }

                                if !hir_ctx.is_loc_used_in_assign(locs[0]) {
                                    is_param_without_assign = true;
                                }
                            }

                            let mut ctx = LocCtx::new(ty);
                            ctx.is_non_local_assign = is_static_return;
                            ctx.is_param_without_assign |= is_param_without_assign;
                            (locs, ctx)
                        }
                        hir::ItemKind::Static(_, _, _) => {
                            if *local != mir::Local::ZERO {
                                continue;
                            }
                            let body = tcx.mir_for_ctfe(*def_id);
                            let ty = body.local_decls[*local].ty;
                            (vec![HirLoc::Global(*def_id)], LocCtx::new(ty))
                        }
                        _ => panic!(),
                    }
                }
                Loc::Field(def_id, field) => {
                    let hir::Node::Item(item) = tcx.hir_node_by_def_id(*def_id) else { panic!() };
                    let adt_def = tcx.adt_def(*def_id);
                    let ty = adt_def.variant(FIRST_VARIANT).fields[*field].ty(tcx, List::empty());
                    let mut ctx = LocCtx::new(ty);
                    ctx.is_union = matches!(item.kind, rustc_hir::ItemKind::Union(_, _));
                    (vec![HirLoc::Field(*def_id, *field)], ctx)
                }
                _ => continue,
            };
            for hir_loc in &hir_locs {
                hir_loc_to_loc_id.insert(*hir_loc, loc_id);
            }
            loc_id_to_hir_locs[loc_id] = Some((hir_locs, ctx));
        }

        let mut param_flow: FxHashMap<Parameter, FxHashSet<Parameter>> = param_to_hir_loc
            .keys()
            .map(|p| (*p, FxHashSet::default()))
            .collect();
        for ((func, index), spans) in &hir_ctx.fn_param_to_arg_spans {
            let param = Parameter {
                func: *func,
                index: *index,
            };
            if !param_to_hir_loc.contains_key(&param) {
                continue;
            }
            let set = param_flow.get_mut(&param).unwrap();
            for span in spans {
                let loc = some_or!(hir_ctx.bound_span_to_loc.get(span), continue);
                let param = some_or!(hir_loc_to_param.get(loc), continue);
                set.insert(*param);
            }
        }
        let transitive_param_flow = graph::transitive_closure(&param_flow);
        let non_generic_params: FxHashSet<_> = non_generic_params
            .into_iter()
            .flat_map(|param| {
                transitive_param_flow[&param]
                    .iter()
                    .copied()
                    .chain(std::iter::once(param))
            })
            .collect();

        let arena = Arena::new();
        let type_arena = TypeArena::new(&arena);
        let mut hir_loc_to_pot = FxHashMap::default();
        let mut uncopiable = vec![];
        for (loc_id, v) in loc_id_to_hir_locs.into_iter_enumerated() {
            let (hir_locs, mut ctx) = some_or!(v, continue);
            let permissions = analysis_res.permissions[loc_id];
            let origins = analysis_res.origins[loc_id];

            for hir_loc in hir_locs {
                if unsupported_locs.contains(&hir_loc) {
                    continue;
                }

                let non_local_assign =
                    // is a global variable or a field assigned to this location without assigning
                    // a local variable to the variable/field in the same function
                    hir_ctx.rhs_locs_of_lhs(hir_loc).any(|rhs| {
                        match rhs {
                            HirLoc::Local(_) | HirLoc::Return(_) => return false,
                            HirLoc::Global(def_id) => {
                                let name = compile_util::def_id_to_value_symbol(def_id, tcx).unwrap();
                                let name = name.as_str();
                                if name == "stdin" || name == "stdout" || name == "stderr" {
                                    return false;
                                }
                            }
                            HirLoc::Field(_, _) => {}
                        }
                        if matches!(rhs, HirLoc::Local(_)) {
                            return false;
                        }
                        let HirLoc::Local(loc_id) = hir_loc else { return true };
                        // to handle `test_return_old_static`-like cases
                        !hir_ctx.rhs_locs_of_lhs(rhs).any(|rhs| {
                            let HirLoc::Local(hir_id) = rhs else { return false };
                            hir_id.owner == loc_id.owner
                        })
                    });
                ctx.is_non_local_assign |= non_local_assign;

                if let Some(param) = hir_loc_to_param.get(&hir_loc) {
                    if !non_generic_params.contains(param) {
                        ctx.is_generic = true;
                    }
                }

                if file_param_index(ctx.ty, tcx).is_some() {
                    ctx.is_param_without_assign = true;
                }

                let ty = type_arena.make_ty(permissions, origins, ctx, tcx);
                if !ty.is_copyable() {
                    if let HirLoc::Field(def_id, field) = hir_loc {
                        uncopiable.push((def_id, field));
                    }
                }

                let pot = Pot {
                    permissions,
                    origins,
                    ty,
                    file_param_index: file_param_index(ctx.ty, tcx),
                };
                let old = hir_loc_to_pot.insert(hir_loc, pot);
                if let Some(old) = old {
                    assert_eq!(pot, old, "{:?}", hir_loc);
                }
            }
        }

        for hir_loc in hir_ctx.loc_to_bound_spans.keys() {
            let HirLoc::Global(def_id) = hir_loc else { continue };
            let name = some_or!(compile_util::def_id_to_value_symbol(*def_id, tcx), continue);
            let (loc, ty) = match name.as_str() {
                "stdin" => (Loc::Stdin, &STDIN_TY),
                "stdout" => (Loc::Stdout, &STDOUT_TY),
                "stderr" => (Loc::Stderr, &STDERR_TY),
                _ => continue,
            };
            let loc_id = analysis_res.loc_ind_map[&loc];
            hir_loc_to_loc_id.insert(*hir_loc, loc_id);
            let permissions = analysis_res.permissions[loc_id];
            let origins = analysis_res.origins[loc_id];
            let pot = Pot {
                permissions,
                origins,
                ty,
                file_param_index: None,
            };
            let old = hir_loc_to_pot.insert(*hir_loc, pot);
            assert!(old.is_none());
        }

        for param_loc in param_to_hir_loc.values() {
            let bound = some_or!(hir_ctx.loc_to_bound_spans.get(param_loc), continue);
            let mut tys = vec![];
            for rhs in bound {
                let lhs = some_or!(hir_ctx.rhs_to_lhs.get(rhs), continue);
                let lhs_loc = some_or!(hir_ctx.bound_span_to_loc.get(lhs), continue);
                let lhs_pot = some_or!(hir_loc_to_pot.get(lhs_loc), continue);
                tys.push(lhs_pot.ty);
            }
            let ty = some_or!(tys.pop(), continue);
            for t in tys {
                assert_eq!(ty, t);
            }
            let pot = hir_loc_to_pot.get_mut(param_loc).unwrap();
            pot.ty = ty;
        }

        let mut visited = FxHashSet::default();
        let mut work_list = uncopiable;
        let mut uncopiable: FxHashMap<_, Vec<_>> = FxHashMap::default();
        let mut uncopiable_union_fields = vec![];
        while let Some((def_id, field)) = work_list.pop() {
            if !visited.insert(def_id) {
                continue;
            }
            let node = tcx.hir_node_by_def_id(def_id);
            let hir::Node::Item(item) = node else { panic!() };
            uncopiable.entry(item.ident.span).or_default().push(field);
            if matches!(item.kind, hir::ItemKind::Union(_, _)) {
                uncopiable_union_fields.push((def_id, field));
            }
            let owning_structs = some_or!(hir_ctx.struct_to_owning_structs.get(&def_id), continue);
            work_list.extend(owning_structs.iter().copied());
        }

        let mut manually_drop_projections: FxHashSet<Span> = FxHashSet::default();
        for (def_id, field) in uncopiable_union_fields {
            let loc = HirLoc::Field(def_id, field);
            if hir_loc_to_pot.contains_key(&loc) {
                continue;
            }
            let bounds = some_or!(hir_ctx.loc_to_bound_spans.get(&loc), continue);
            manually_drop_projections.extend(bounds);
        }

        let mut api_ident_spans = FxHashSet::default();

        for item_id in tcx.hir_free_items() {
            let item = tcx.hir_item(item_id);
            let local_def_id = item.owner_id.def_id;
            if let hir::ItemKind::Fn { .. } = item.kind {
                if item.ident.name.as_str() == "main" {
                    continue;
                }
                if analysis_res.defined_apis.contains(&local_def_id) {
                    api_ident_spans.insert(item.ident.span);
                }
            }
        }

        let source_map = tcx.sess.source_map();
        let parse_sess = crate::ast_maker::new_parse_sess();
        let mut files = vec![];
        let mut tmpfile = false;
        let mut bounds = FxHashSet::default();

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
            let mut visitor = TransformVisitor {
                tcx,
                type_arena: &type_arena,
                analysis_res: &analysis_res,
                hir: &hir_ctx,

                error_returning_fns: &error_returning_fns,
                error_taking_fns: &error_taking_fns,

                hir_loc_to_loc_id: &hir_loc_to_loc_id,

                param_to_loc: &param_to_hir_loc,
                loc_to_pot: &hir_loc_to_pot,
                api_ident_spans: &api_ident_spans,
                uncopiable: &uncopiable,
                manually_drop_projections: &manually_drop_projections,

                unsupported,
                unsupported_returns: &unsupported_returns,
                is_stdin_unsupported,
                is_stdout_unsupported,
                is_stderr_unsupported,

                updated: false,
                tmpfile: false,
                current_fns: vec![],
                bounds: vec![],
                guards: FxHashSet::default(),
                foreign_statics: FxHashSet::default(),
            };
            visitor.visit_crate(&mut krate);
            if visitor.updated {
                let s = pprust::crate_to_string_for_macros(&krate);
                files.push((file.name.clone(), s));
                tmpfile |= visitor.tmpfile;
                bounds.extend(visitor.bounds);
            }
            unsupported = visitor.unsupported;
        }

        TransformationResult {
            files,
            tmpfile,
            bounds,
        }
    }
}

fn mir_local_span(
    def_id: LocalDefId,
    local: mir::Local,
    return_locals: &FxHashMap<LocalDefId, HirId>,
    hir_ctx: &HirCtx,
    tcx: TyCtxt<'_>,
) -> Span {
    let node = tcx.hir_node_by_def_id(def_id);
    let hir::Node::Item(item) = node else { panic!() };
    let body = match item.kind {
        hir::ItemKind::Fn { .. } => {
            if local == mir::Local::ZERO {
                if let Some(hir_id) = return_locals.get(&def_id) {
                    let loc = HirLoc::Local(*hir_id);
                    return hir_ctx.loc_to_binding_span[&loc];
                }
            }
            tcx.optimized_mir(def_id)
        }
        hir::ItemKind::Static(_, _, _) => {
            if local == mir::Local::ZERO {
                return item.ident.span;
            }
            tcx.mir_for_ctfe(def_id)
        }
        _ => panic!(),
    };
    let local_decl = &body.local_decls[local];
    local_decl.source_info.span
}

fn file_param_index<'tcx>(ty: rustc_middle::ty::Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Option<usize> {
    match ty.kind() {
        rustc_middle::ty::TyKind::Adt(adt_def, targs) => {
            if compile_util::is_option_ty(adt_def.did(), tcx) {
                let targs = targs.into_type_list(tcx);
                file_param_index(targs[0], tcx)
            } else {
                None
            }
        }
        rustc_middle::ty::TyKind::FnPtr(binder, _) => binder
            .as_ref()
            .skip_binder()
            .inputs()
            .iter()
            .enumerate()
            .find_map(|(i, ty)| {
                if compile_util::is_file_ptr(*ty, tcx) {
                    Some(i)
                } else {
                    None
                }
            }),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Parameter {
    func: LocalDefId,
    index: usize,
}

impl Parameter {
    #[inline]
    fn new(func: LocalDefId, index: usize) -> Self {
        Self { func, index }
    }
}

mod hir_ctx;
mod printf;
mod scanf;
mod stream_ty;
mod transform_visitor;

#[cfg(test)]
mod tests;

static LIB: &str = r#"
pub trait AsRawFd { fn as_raw_fd(&self) -> i32; } impl AsRawFd for std::fs::File { fn as_raw_fd(&self) -> i32 { std::os::unix::io::AsRawFd::as_raw_fd(self) } } impl AsRawFd for std::io::Stdin { fn as_raw_fd(&self) -> i32 { std::os::unix::io::AsRawFd::as_raw_fd(self) } } impl AsRawFd for std::io::StdinLock<'_> { fn as_raw_fd(&self) -> i32 { std::os::unix::io::AsRawFd::as_raw_fd(self) } } impl AsRawFd for std::io::Stdout { fn as_raw_fd(&self) -> i32 { std::os::unix::io::AsRawFd::as_raw_fd(self) } } impl AsRawFd for std::io::Stderr { fn as_raw_fd(&self) -> i32 { std::os::unix::io::AsRawFd::as_raw_fd(self) } } impl<T: AsRawFd + ?Sized> AsRawFd for &T { fn as_raw_fd(&self) -> i32 { (*self).as_raw_fd() } } impl<T: AsRawFd + ?Sized> AsRawFd for &mut T { fn as_raw_fd(&self) -> i32 { (**self).as_raw_fd() } } impl<T: AsRawFd + ?Sized> AsRawFd for Box<T> { fn as_raw_fd(&self) -> i32 { (**self).as_raw_fd() } } impl<T: AsRawFd> AsRawFd for std::io::BufReader<T> { fn as_raw_fd(&self) -> i32 { self.get_ref().as_raw_fd() } } impl<T: AsRawFd + std::io::Write> AsRawFd for std::io::BufWriter<T> { fn as_raw_fd(&self) -> i32 { self.get_ref().as_raw_fd() } } pub struct Child(pub std::process::Child); impl std::io::Read for Child { fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> { self.0.stdout.as_mut().unwrap().read(buf) } } impl std::io::Write for Child { fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> { self.0.stdin.as_mut().unwrap().write(buf) } fn flush(&mut self) -> std::io::Result<()> { self.0.stdin.as_mut().unwrap().flush() } } impl AsRawFd for Child { fn as_raw_fd(&self) -> i32 { self.0 .stdout .as_ref() .map(std::os::fd::AsRawFd::as_raw_fd) .or_else(|| self.0.stdin.as_ref().map(std::os::fd::AsRawFd::as_raw_fd)) .unwrap() } } pub trait Close { fn close(&mut self) -> i32; } impl Close for Child { fn close(&mut self) -> i32 { self.0.wait().ok().and_then(|e| e.code()).unwrap_or(-1) } } impl Close for std::fs::File { fn close(&mut self) -> i32 { 0 } } impl Close for std::io::Stdin { fn close(&mut self) -> i32 { 0 } } impl Close for std::io::Stdout { fn close(&mut self) -> i32 { 0 } } impl Close for std::io::Stderr { fn close(&mut self) -> i32 { 0 } } impl<T: Close> Close for std::io::BufReader<T> { fn close(&mut self) -> i32 { self.get_mut().close() } } impl<T: Close + std::io::Write> Close for std::io::BufWriter<T> { fn close(&mut self) -> i32 { self.get_mut().close() } } impl<T: Close + ?Sized> Close for Box<T> { fn close(&mut self) -> i32 { self.as_mut().close() } } pub trait Lock { fn lock(&self) -> Box<dyn Guard>; } impl Lock for std::io::Stdin { fn lock(&self) -> Box<dyn Guard> { Box::new(self.lock()) } } impl Lock for std::io::Stdout { fn lock(&self) -> Box<dyn Guard> { Box::new(self.lock()) } } impl Lock for std::io::Stderr { fn lock(&self) -> Box<dyn Guard> { Box::new(self.lock()) } } pub trait Guard {} impl Guard for std::io::StdinLock<'_> {} impl Guard for std::io::StdoutLock<'_> {} impl Guard for std::io::StderrLock<'_> {} pub unsafe fn fopen(pathname: *const i8, mode: *const i8) -> Option<std::fs::File> { let pathname = std::ffi::CStr::from_ptr(pathname as _).to_str().unwrap(); let mode = std::ffi::CStr::from_ptr(mode as _).to_str().unwrap(); let (prefix, suffix) = mode.split_at(1); match prefix { "r" => { if suffix.contains('+') { std::fs::OpenOptions::new() .read(true) .write(true) .open(pathname) } else { std::fs::File::open(pathname) } } "w" => { if suffix.contains('+') { std::fs::OpenOptions::new() .write(true) .create(true) .truncate(true) .read(true) .open(pathname) } else { std::fs::File::create(pathname) } } "a" => { if suffix.contains('+') { std::fs::OpenOptions::new() .append(true) .create(true) .read(true) .open(pathname) } else { std::fs::OpenOptions::new() .append(true) .create(true) .open(pathname) } } _ => panic!(), } .ok() } #[inline] pub fn fgetc<R: std::io::Read>(mut stream: R) -> (i32, i32, i32) { let mut buf = [0]; match stream.read_exact(&mut buf) { Ok(_) => (buf[0] as i32, 0, 0), Err(e) => { if e.kind() != std::io::ErrorKind::UnexpectedEof { (libc::EOF, 1, 0) } else { (libc::EOF, 0, 1) } } } } pub unsafe fn fgets<R: std::io::BufRead>(s: *mut i8, n: i32, mut stream: R) -> (*mut i8, i32, i32) { let buf: &mut [u8] = std::slice::from_raw_parts_mut(s as _, n as _); let mut pos = 0; while pos < n as usize - 1 { let available = match stream.fill_buf() { Ok(buf) => buf, Err(e) => { return if e.kind() != std::io::ErrorKind::UnexpectedEof { (std::ptr::null_mut(), 1, 0) } else { (std::ptr::null_mut(), 0, 1) }; } }; if available.is_empty() { break; } buf[pos] = available[0]; stream.consume(1); pos += 1; if buf[pos - 1] == b'\n' { break; } } let res = if pos == 0 { std::ptr::null_mut() } else { buf[pos] = 0; s }; (res, 0, 0) } pub unsafe fn getdelim<R: std::io::BufRead>( lineptr: *mut *mut i8, n: *mut u64, delimiter: i32, mut stream: R, ) -> (i64, i32, i32) { let mut buf = Vec::new(); match stream.read_until(delimiter as _, &mut buf) { Ok(_) => { let len = buf.len(); if len == 0 { return (-1, 0, 0); } buf.push(0); if (*lineptr).is_null() { *lineptr = libc::malloc(buf.len() as _) as _; *n = buf.len() as _; } else if buf.len() > *n as _ { *lineptr = libc::realloc(*lineptr as _, buf.len() as _) as _; *n = buf.len() as _; } let ptr: &mut [u8] = std::slice::from_raw_parts_mut(*lineptr as _, buf.len()); ptr.copy_from_slice(&buf); (len as _, 0, 0) } Err(e) => { if e.kind() != std::io::ErrorKind::UnexpectedEof { (-1, 1, 0) } else { (-1, 0, 1) } } } } #[inline] pub unsafe fn getline<R: std::io::BufRead>( lineptr: *mut *mut i8, n: *mut u64, stream: R, ) -> (i64, i32, i32) { getdelim(lineptr, n, b'\n' as _, stream) } pub unsafe fn fread<R: std::io::Read>( ptr: *mut libc::c_void, size: u64, nitems: u64, mut stream: R, ) -> (u64, i32, i32) { let ptr: &mut [u8] = std::slice::from_raw_parts_mut(ptr as _, (size * nitems) as usize); let mut i = 0; for data in ptr.chunks_mut(size as usize) { match stream.read_exact(data) { Ok(_) => i += 1, Err(e) => { if e.kind() != std::io::ErrorKind::UnexpectedEof { return (i, 1, 0); } else { return (i, 0, 1); } } } } (i, 0, 0) } #[inline] pub unsafe extern "C" fn fprintf<W: std::io::Write>( stream: W, fmt: *const i8, args: ... ) -> (i32, i32) { let mut args_0: ::std::ffi::VaListImpl; args_0 = args.clone(); vfprintf(stream, fmt, args_0.as_va_list()) } pub unsafe fn vfprintf<W: std::io::Write>( mut stream: W, fmt: *const i8, mut args: std::ffi::VaList, ) -> (i32, i32) { let fmt = std::ffi::CStr::from_ptr(fmt as _); let mut state = State::Percent; let mut flags = vec![]; let mut width = None; let mut precision = None; let mut length = None; let mut conversion = None; let mut count = 0; for c in fmt.to_bytes() { if state == State::Percent { if *c == b'%' { state = State::Flag; } else { match stream.write_all(&[*c]) { Ok(_) => count += 1, Err(_) => return (-1, 1), } } } else if (b'1'..=b'9').contains(c) || (*c == b'0' && state != State::Flag) { match state { State::Flag => { width = Some(Width::Decimal((c - b'0') as usize)); state = State::Width; } State::Width => { let Some(Width::Decimal(n)) = &mut width else { panic!() }; *n = *n * 10 + (c - b'0') as usize; } State::Precision => match &mut precision { None => precision = Some(Width::Decimal((c - b'0') as usize)), Some(Width::Decimal(n)) => *n = *n * 10 + (c - b'0') as usize, _ => panic!(), }, _ => panic!(), } } else if let Some(flag) = FlagChar::from_u8(*c) { flags.push(flag); } else if *c == b'*' { match state { State::Flag => { width = Some(Width::Asterisk); state = State::Period; } State::Precision => { precision = Some(Width::Asterisk); state = State::Length; } _ => panic!(), } } else if *c == b'.' { if matches!(state, State::Flag | State::Width | State::Period) { state = State::Precision; } else { panic!() } } else if let Some(len) = LengthMod::from_u8(*c) { match len { LengthMod::Short => match state { State::Flag | State::Width | State::Period | State::Precision | State::Length => { state = State::H; } State::H => { length = Some(LengthMod::Char); state = State::Conversion; } _ => panic!(), }, LengthMod::Long => match state { State::Flag | State::Width | State::Period | State::Precision | State::Length => { state = State::L; } State::L => { length = Some(LengthMod::LongLong); state = State::Conversion; } _ => panic!(), }, _ => { length = Some(len); state = State::Conversion; } } } else if let Some(conv) = Conversion::from_u8(*c) { match state { State::Flag | State::Width | State::Period | State::Precision | State::Length | State::Conversion => { conversion = Some(conv); } State::H => { length = Some(LengthMod::Short); conversion = Some(conv); } State::L => { length = Some(LengthMod::Long); conversion = Some(conv); } _ => panic!(), } } else { panic!() } if let Some(conversion) = conversion.take() { let mut opt = std::fmt::FormattingOptions::new(); let mut minus = false; for flag in flags.drain(..) { match flag { FlagChar::Apostrophe => panic!(), FlagChar::Minus => { minus = true; } FlagChar::Plus => { opt.sign(Some(std::fmt::Sign::Plus)); } FlagChar::Space => panic!(), FlagChar::Hash => { opt.alternate(true); } FlagChar::Zero => { opt.sign_aware_zero_pad(true); } } } if minus { opt.align(Some(std::fmt::Alignment::Left)); } else { opt.align(Some(std::fmt::Alignment::Right)); } if let Some(width) = width.take() { match width { Width::Asterisk => { let width = args.arg::<usize>(); opt.width(Some(width)); } Width::Decimal(n) => { opt.width(Some(n)); } } } if let Some(precision) = precision.take() { match precision { Width::Asterisk => { let precision = args.arg::<usize>(); opt.precision(Some(precision)); } Width::Decimal(n) => { opt.precision(Some(n)); } } } match conversion { Conversion::Double => { if opt.get_precision().is_none() { opt.precision(Some(6)); } } Conversion::Pointer => { opt.alternate(true); } _ => {} } let mut s = String::new(); let mut fmt = std::fmt::Formatter::new(&mut s, opt); match (conversion, length.take()) { (Conversion::Int, None) => { let v = args.arg::<i32>(); if std::fmt::Display::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::Int, Some(LengthMod::Char)) => { let v = args.arg::<i8>(); if std::fmt::Display::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::Int, Some(LengthMod::Short)) => { let v = args.arg::<i16>(); if std::fmt::Display::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } ( Conversion::Int, Some( LengthMod::Long | LengthMod::LongLong | LengthMod::IntMax | LengthMod::Size, ), ) => { let v = args.arg::<i64>(); if std::fmt::Display::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::Int, Some(LengthMod::PtrDiff)) => { let v = args.arg::<u64>(); if std::fmt::Display::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::Int, Some(LengthMod::LongDouble)) => panic!(), (Conversion::Octal, None) => { let v = args.arg::<u32>(); if std::fmt::Octal::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::Octal, Some(LengthMod::Char)) => { let v = args.arg::<u8>(); if std::fmt::Octal::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::Octal, Some(LengthMod::Short)) => { let v = args.arg::<u16>(); if std::fmt::Octal::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } ( Conversion::Octal, Some( LengthMod::Long | LengthMod::LongLong | LengthMod::IntMax | LengthMod::Size | LengthMod::PtrDiff, ), ) => { let v = args.arg::<u64>(); if std::fmt::Octal::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::Octal, Some(LengthMod::LongDouble)) => panic!(), (Conversion::Unsigned, None) => { let v = args.arg::<u32>(); if std::fmt::Display::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::Unsigned, Some(LengthMod::Char)) => { let v = args.arg::<u8>(); if std::fmt::Display::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::Unsigned, Some(LengthMod::Short)) => { let v = args.arg::<u16>(); if std::fmt::Display::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } ( Conversion::Unsigned, Some( LengthMod::Long | LengthMod::LongLong | LengthMod::IntMax | LengthMod::Size | LengthMod::PtrDiff, ), ) => { let v = args.arg::<u64>(); if std::fmt::Display::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::Unsigned, Some(LengthMod::LongDouble)) => panic!(), (Conversion::Hexadecimal, None) => { let v = args.arg::<u32>(); if std::fmt::LowerHex::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::Hexadecimal, Some(LengthMod::Char)) => { let v = args.arg::<u8>(); if std::fmt::LowerHex::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::Hexadecimal, Some(LengthMod::Short)) => { let v = args.arg::<u16>(); if std::fmt::LowerHex::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } ( Conversion::Hexadecimal, Some( LengthMod::Long | LengthMod::LongLong | LengthMod::IntMax | LengthMod::Size | LengthMod::PtrDiff, ), ) => { let v = args.arg::<u64>(); if std::fmt::LowerHex::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::Hexadecimal, Some(LengthMod::LongDouble)) => panic!(), (Conversion::HexadecimalUpper, None) => { let v = args.arg::<u32>(); if std::fmt::UpperHex::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::HexadecimalUpper, Some(LengthMod::Char)) => { let v = args.arg::<u8>(); if std::fmt::UpperHex::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::HexadecimalUpper, Some(LengthMod::Short)) => { let v = args.arg::<u16>(); if std::fmt::UpperHex::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } ( Conversion::HexadecimalUpper, Some( LengthMod::Long | LengthMod::LongLong | LengthMod::IntMax | LengthMod::Size | LengthMod::PtrDiff, ), ) => { let v = args.arg::<u64>(); if std::fmt::UpperHex::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::HexadecimalUpper, Some(LengthMod::LongDouble)) => panic!(), (Conversion::Double | Conversion::DoubleAuto, None | Some(LengthMod::Long)) => { let v = args.arg::<f64>(); if std::fmt::Display::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::Double | Conversion::DoubleAuto, _) => panic!(), (Conversion::DoubleExp, None | Some(LengthMod::Long)) => { let v = args.arg::<f64>(); if std::fmt::LowerExp::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::DoubleExp, _) => panic!(), (Conversion::Char, _) => { let v = args.arg::<u8>() as char; if std::fmt::Display::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::Str, None) => { let v = args.arg::<*const u8>(); let v = std::ffi::CStr::from_ptr(v as _).to_str().unwrap(); if std::fmt::Display::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::Str, _) => panic!(), (Conversion::Pointer, _) => { let v = args.arg::<*const libc::c_void>() as usize; if std::fmt::LowerHex::fmt(&v, &mut fmt).is_err() { return (-1, 1); } } (Conversion::DoubleError | Conversion::Num | Conversion::C | Conversion::S, _) => { panic!() } (Conversion::Percent, _) => s.push('%'), } match stream.write_all(s.as_bytes()) { Ok(_) => count += s.len() as i32, Err(_) => return (-1, 1), } state = State::Percent; } } (count, 0) } #[inline] pub fn fputc<W: std::io::Write>(c: i32, mut stream: W) -> (i32, i32) { let c = c as u8; match stream.write_all(&[c]) { Ok(_) => (c as i32, 0), Err(_) => (libc::EOF, 1), } } #[inline] pub fn fputwc<W: std::io::Write>(c: i32, mut stream: W) -> (i32, i32) { match write!(stream, "{}", std::char::from_u32(c as _).unwrap()) { Ok(_) => (c, 0), Err(_) => (libc::EOF, 1), } } #[inline] pub unsafe fn fputs<W: std::io::Write>(s: *const i8, mut stream: W) -> (i32, i32) { match stream.write_all(std::ffi::CStr::from_ptr(s as _).to_bytes()) { Ok(_) => (0, 0), Err(_) => (libc::EOF, 1), } } #[inline] pub unsafe fn puts(s: *const i8) -> (i32, i32) { use std::io::Write as _; let mut stream = std::io::stdout(); match stream .write_all(std::ffi::CStr::from_ptr(s as _).to_bytes()) .and_then(|_| stream.write_all(b"\n")) { Ok(_) => (0, 0), Err(_) => (libc::EOF, 1), } } #[inline] pub unsafe fn perror(s: *const i8) { use std::io::Write as _; let mut stream = std::io::stderr(); let _ = if s.is_null() || *s == 0 { writeln!(stream) } else { let s = std::ffi::CStr::from_ptr(s as _).to_str().unwrap(); writeln!(stream, "{}: ", s) }; } pub unsafe fn fwrite<W: std::io::Write>( ptr: *const libc::c_void, size: u64, nitems: u64, mut stream: W, ) -> (u64, i32) { let ptr: &[u8] = std::slice::from_raw_parts(ptr as _, (size * nitems) as usize); let mut i = 0; for data in ptr.chunks(size as usize) { match stream.write_all(data) { Ok(_) => i += 1, Err(_) => return (i, 1), } } (i, 0) } #[inline] pub fn fflush<W: std::io::Write>(mut stream: W) -> (i32, i32) { match stream.flush() { Ok(_) => (0, 0), Err(_) => (libc::EOF, 1), } } #[inline] pub fn fseek<S: std::io::Seek>(mut stream: S, offset: i64, whence: i32) -> i32 { let seek_from = match whence { 0 => std::io::SeekFrom::Start(offset as _), 1 => std::io::SeekFrom::Current(offset), 2 => std::io::SeekFrom::End(offset), _ => panic!(), }; stream.seek(seek_from).map_or(-1, |_| 0) } #[inline] pub fn ftell<S: std::io::Seek>(mut stream: S) -> i64 { stream.stream_position().map_or(-1, |pos| pos as i64) } #[inline] pub fn rewind<S: std::io::Seek>(mut stream: S) { let _ = stream.rewind(); } #[derive(Debug, Clone, Copy, PartialEq, Eq)] enum State { Percent, Flag, Width, Period, Precision, Length, H, L, Conversion, } #[derive(Debug, Clone, Copy, PartialEq, Eq)] enum FlagChar { Apostrophe, Minus, Plus, Space, Hash, Zero, } impl FlagChar { #[inline] fn from_u8(c: u8) -> Option<Self> { match c { b'\'' => Some(Self::Apostrophe), b'-' => Some(Self::Minus), b'+' => Some(Self::Plus), b' ' => Some(Self::Space), b'#' => Some(Self::Hash), b'0' => Some(Self::Zero), _ => None, } } } #[derive(Debug, Clone, Copy, PartialEq, Eq)] enum Width { Asterisk, Decimal(usize), } #[derive(Debug, Clone, Copy, PartialEq, Eq)] enum LengthMod { Char, Short, Long, LongLong, IntMax, Size, PtrDiff, LongDouble, } impl LengthMod { #[inline] fn from_u8(c: u8) -> Option<Self> { match c { b'h' => Some(Self::Short), b'l' => Some(Self::Long), b'j' => Some(Self::IntMax), b'z' => Some(Self::Size), b't' => Some(Self::PtrDiff), b'L' => Some(Self::LongDouble), _ => None, } } } #[derive(Debug, Clone, Copy, PartialEq, Eq)] enum Conversion { Int, Octal, Unsigned, Hexadecimal, HexadecimalUpper, Double, DoubleExp, DoubleAuto, DoubleError, Char, Str, Pointer, Num, C, S, Percent, } impl Conversion { #[inline] fn from_u8(c: u8) -> Option<Self> { match c { b'd' | b'i' => Some(Self::Int), b'o' => Some(Self::Octal), b'u' => Some(Self::Unsigned), b'x' => Some(Self::Hexadecimal), b'X' => Some(Self::HexadecimalUpper), b'f' | b'F' => Some(Self::Double), b'e' | b'E' => Some(Self::DoubleExp), b'g' | b'G' => Some(Self::DoubleAuto), b'a' | b'A' => Some(Self::DoubleError), b'c' => Some(Self::Char), b's' => Some(Self::Str), b'p' => Some(Self::Pointer), b'n' => Some(Self::Num), b'C' => Some(Self::C), b'S' => Some(Self::S), b'%' => Some(Self::Percent), _ => None, } } }
"#;
