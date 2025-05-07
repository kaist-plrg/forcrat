use std::{fmt::Write as _, fs};

use etrace::some_or;
use hir_ctx::*;
use rustc_abi::FIRST_VARIANT;
use rustc_ast::mut_visit::MutVisitor;
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{self as hir, HirId};
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
    compile_util::{self, Pass},
    file_analysis::{self, Loc},
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
    let mut file = fs::OpenOptions::new().append(true).open(path).unwrap();
    use std::io::Write;
    writeln!(file, "{}", res.trait_defs()).unwrap();
}

#[derive(Debug)]
pub struct TransformationResult {
    files: Vec<(FileName, String)>,
    tmpfile: bool,
    bounds: FxHashSet<TraitBound>,
}

impl TransformationResult {
    fn trait_defs(&self) -> String {
        let mut defs = "
trait AsRawFd { fn as_raw_fd(&self) -> i32; }
impl AsRawFd for std::fs::File { fn as_raw_fd(&self) -> i32 { std::os::unix::io::AsRawFd::as_raw_fd(self) } }
impl AsRawFd for std::io::Stdin { fn as_raw_fd(&self) -> i32 { std::os::unix::io::AsRawFd::as_raw_fd(self) } }
impl AsRawFd for std::io::StdinLock<'_> { fn as_raw_fd(&self) -> i32 { std::os::unix::io::AsRawFd::as_raw_fd(self) } }
impl AsRawFd for std::io::Stdout { fn as_raw_fd(&self) -> i32 { std::os::unix::io::AsRawFd::as_raw_fd(self) } }
impl AsRawFd for std::io::Stderr { fn as_raw_fd(&self) -> i32 { std::os::unix::io::AsRawFd::as_raw_fd(self) } }
impl AsRawFd for std::process::ChildStdin { fn as_raw_fd(&self) -> i32 { std::os::unix::io::AsRawFd::as_raw_fd(self) } }
impl AsRawFd for std::process::ChildStdout { fn as_raw_fd(&self) -> i32 { std::os::unix::io::AsRawFd::as_raw_fd(self) } }
impl<T: AsRawFd> AsRawFd for &T { fn as_raw_fd(&self) -> i32 { (*self).as_raw_fd() } }
impl<T: AsRawFd> AsRawFd for &mut T { fn as_raw_fd(&self) -> i32 { (**self).as_raw_fd() } }
impl<T: AsRawFd> AsRawFd for Box<T> { fn as_raw_fd(&self) -> i32 { (**self).as_raw_fd() } }
impl<T: AsRawFd> AsRawFd for std::io::BufReader<T> { fn as_raw_fd(&self) -> i32 { self.get_ref().as_raw_fd() } }
impl<T: AsRawFd + std::io::Write> AsRawFd for std::io::BufWriter<T> { fn as_raw_fd(&self) -> i32 { self.get_ref().as_raw_fd() } }
".to_string();
        for bound in &self.bounds {
            writeln!(
                defs,
                "trait {0} : {1} {{}}\nimpl<T: {1}> {0} for T {{}}",
                bound.trait_name(),
                bound
            )
            .unwrap();
        }
        defs
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Transformation;

impl Pass for Transformation {
    type Out = TransformationResult;

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out {
        let analysis_res = file_analysis::FileAnalysis.run(tcx);

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
                    unsupported.insert(*span);
                }
            }
        }

        let arena = Arena::new();
        let type_arena = TypeArena::new(&arena);
        let mut param_to_hir_loc = FxHashMap::default();
        let mut hir_loc_to_pot = FxHashMap::default();
        let mut uncopiable = vec![];
        for ((loc, permissions), origins) in analysis_res
            .locs
            .iter()
            .zip(analysis_res.permissions.iter().copied())
            .zip(analysis_res.origins.iter().copied())
        {
            let (hir_locs, mut ctx) = match loc {
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

                            let arity = sig.decl.inputs.len();
                            let is_param = (1..=arity).contains(&local.as_usize());
                            let is_generic = if is_param {
                                let param = Parameter {
                                    func: *def_id,
                                    index: local.as_usize() - 1,
                                };
                                let loc = locs[0];
                                param_to_hir_loc.insert(param, loc);
                                let bounds = hir_ctx.loc_to_bound_spans.get(&loc);
                                file_param_index(ty, tcx).is_none()
                                    && !analysis_res.fn_ptrs.contains(def_id)
                                    && bounds.is_none_or(|bounds| {
                                        bounds
                                            .iter()
                                            .all(|bound| !hir_ctx.lhs_to_rhs.contains_key(bound))
                                    })
                            } else {
                                false
                            };
                            (locs, LocCtx::new(is_generic, false, is_static_return, ty))
                        }
                        hir::ItemKind::Static(_, _, _) => {
                            if *local != mir::Local::ZERO {
                                continue;
                            }
                            let body = tcx.mir_for_ctfe(*def_id);
                            let ty = body.local_decls[*local].ty;
                            (
                                vec![HirLoc::Global(*def_id)],
                                LocCtx::new(false, false, false, ty),
                            )
                        }
                        _ => panic!(),
                    }
                }
                Loc::Field(def_id, field) => {
                    let hir::Node::Item(item) = tcx.hir_node_by_def_id(*def_id) else { panic!() };
                    let adt_def = tcx.adt_def(*def_id);
                    let ty = adt_def.variant(FIRST_VARIANT).fields[*field].ty(tcx, List::empty());
                    let is_union = matches!(item.kind, rustc_hir::ItemKind::Union(_, _));
                    (
                        vec![HirLoc::Field(*def_id, *field)],
                        LocCtx::new(false, is_union, false, ty),
                    )
                }
                _ => continue,
            };
            for hir_loc in hir_locs {
                if unsupported_locs.contains(&hir_loc) {
                    continue;
                }
                let bounds = hir_ctx.loc_to_bound_spans.get(&hir_loc);
                let non_local_assign = bounds.is_some_and(|bounds| {
                    bounds.iter().any(|bound| {
                        let rhs = some_or!(hir_ctx.lhs_to_rhs.get(bound), return false);
                        let loc = some_or!(hir_ctx.bound_span_to_loc.get(rhs), return false);
                        matches!(loc, HirLoc::Global(_) | HirLoc::Field(_, _))
                    })
                });
                ctx.non_local_assign |= non_local_assign;
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
                current_fn: None,
                bounds: vec![],
                guards: FxHashSet::default(),
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
