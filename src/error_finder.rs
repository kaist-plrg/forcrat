use etrace::some_or;
use rustc_ast::UnOp;
use rustc_data_structures::fx::FxHashSet;
use rustc_hash::FxHashMap;
use rustc_hir::{
    def::{DefKind, Res},
    def_id::{DefId, LocalDefId},
    intravisit::{self, Visitor},
    Expr, ExprKind, HirId, ItemKind, Node, PatKind, QPath,
};
use rustc_index::Idx;
use rustc_middle::{
    hir::nested_filter,
    mir::{BasicBlock, Const, Operand, TerminatorKind},
    query::IntoQueryParam,
    ty::{self, TyCtxt},
};
use rustc_span::{Span, Symbol};
use typed_arena::Arena;

use crate::{
    api_list,
    bit_set::BitSet8,
    compile_util::{self, Pass},
    file_analysis::Loc,
    graph,
};

#[derive(Debug, Clone, Copy)]
pub struct ErrorFinder;

impl Pass for ErrorFinder {
    type Out = ();

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out {
        let mut visitor = HirVisitor::new(tcx);
        tcx.hir_visit_all_item_likes_in_crate(&mut visitor);

        let arena = Arena::new();
        let mut propagations = CollectedPropagations::default();

        for def_id in &visitor.ctx.error_handling_fns {
            let body = tcx.optimized_mir(*def_id);

            for (bb, bbd) in body.basic_blocks.iter_enumerated() {
                let term = bbd.terminator();
                let TerminatorKind::Call { func, args, .. } = &term.kind else { continue };

                let handle_callee = some_or!(operand_to_def_id(func), continue);
                let indicator = some_or!(handling_api_indicator(handle_callee, tcx), continue);

                let place = args[0].node.place().unwrap();
                let hir_loc = Loc::Var(*def_id, place.local);

                let span = term.source_info.span;
                let func = *def_id;
                let loc = visitor.ctx.call_span_to_args[&span][0].as_ref().unwrap();
                let label = Label::new(func, bb, loc);
                let result = analyze(label, FxHashSet::default(), &arena, &visitor.ctx, tcx);

                if result.sources.is_empty() {
                    propagations.no_source_locs.push(hir_loc);
                    continue;
                }

                propagations.add_tracking_fn(label.func_loc, indicator);

                if result.call_graph.is_empty() {
                    continue;
                }

                let mut call_graph = result.call_graph;
                let mut nodes: FxHashSet<FuncLoc<'_>> = FxHashSet::default();
                for succs in call_graph.values() {
                    nodes.extend(succs.iter().filter(|succ| !call_graph.contains_key(succ)));
                }
                for node in nodes {
                    assert!(call_graph.insert(node, FxHashSet::default()).is_none());
                }
                let transitive_call_graph = graph::transitive_closure(&call_graph);
                let inv_call_graph = graph::inverse(&call_graph);
                let transitive_inv_call_graph = graph::transitive_closure(&inv_call_graph);

                if inv_call_graph[&label.func_loc].is_empty() {
                    let source_reachables: FxHashSet<_> = result
                        .sources
                        .iter()
                        .flat_map(|source| &transitive_inv_call_graph[source])
                        .chain(&result.sources)
                        .copied()
                        .collect();
                    for l in &transitive_call_graph[&label.func_loc] {
                        if source_reachables.contains(l) {
                            propagations.add_returning_fn(*l, indicator);
                        }
                    }
                } else {
                    let sink_reachables = &transitive_inv_call_graph[&label.func_loc];
                    for source in result.sources {
                        let source_reachables = &transitive_inv_call_graph[&source];
                        for caller in sink_reachables {
                            if *caller != source && !source_reachables.contains(caller) {
                                continue;
                            }
                            propagations.add_tracking_fn(*caller, indicator);

                            for l in &transitive_call_graph[caller] {
                                if *l == source || source_reachables.contains(l) {
                                    propagations.add_returning_fn(*l, indicator);
                                }
                                if *l == label.func_loc || sink_reachables.contains(l) {
                                    propagations.add_taking_fn(*l, indicator);
                                }
                            }
                        }
                    }
                }
            }
        }

        println!("No source locs: {:#?}", propagations.no_source_locs);
        println!("Tracking fns: {:#?}", propagations.tracking_fns);
        println!("Returning fns: {:#?}", propagations.returning_fns);
        println!("Taking fns: {:#?}", propagations.taking_fns);
    }
}

#[derive(Debug, Default)]
struct CollectedPropagations<'a> {
    no_source_locs: Vec<Loc>,
    tracking_fns: FxHashMap<LocalDefId, FxHashMap<&'a ExprLoc, BitSet8<Indicator>>>,
    returning_fns: FxHashMap<LocalDefId, FxHashMap<&'a ExprLoc, BitSet8<Indicator>>>,
    taking_fns: FxHashMap<LocalDefId, FxHashMap<&'a ExprLoc, BitSet8<Indicator>>>,
}

impl<'a> CollectedPropagations<'a> {
    #[inline]
    fn add_tracking_fn(&mut self, func_loc: FuncLoc<'a>, indicator: Indicator) {
        self.tracking_fns
            .entry(func_loc.func)
            .or_default()
            .entry(func_loc.loc)
            .or_default()
            .insert(indicator);
    }

    #[inline]
    fn add_returning_fn(&mut self, func_loc: FuncLoc<'a>, indicator: Indicator) {
        self.returning_fns
            .entry(func_loc.func)
            .or_default()
            .entry(func_loc.loc)
            .or_default()
            .insert(indicator);
        self.add_tracking_fn(func_loc, indicator);
    }

    #[inline]
    fn add_taking_fn(&mut self, func_loc: FuncLoc<'a>, indicator: Indicator) {
        self.taking_fns
            .entry(func_loc.func)
            .or_default()
            .entry(func_loc.loc)
            .or_default()
            .insert(indicator);
        self.add_tracking_fn(func_loc, indicator);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Indicator {
    Error,
    Eof,
}

impl Indicator {
    pub const NUM: usize = 2;
}

impl Idx for Indicator {
    #[inline]
    fn new(idx: usize) -> Self {
        if idx >= Self::NUM {
            panic!()
        }
        unsafe { std::mem::transmute(idx as u8) }
    }

    #[inline]
    fn index(self) -> usize {
        self as _
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Label<'a> {
    func_loc: FuncLoc<'a>,
    bb: BasicBlock,
}

impl<'a> Label<'a> {
    #[inline]
    fn new(func: LocalDefId, bb: BasicBlock, loc: &'a ExprLoc) -> Self {
        Self {
            func_loc: FuncLoc::new(func, loc),
            bb,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct FuncLoc<'a> {
    func: LocalDefId,
    loc: &'a ExprLoc,
}

impl<'a> FuncLoc<'a> {
    #[inline]
    fn new(func: LocalDefId, loc: &'a ExprLoc) -> Self {
        Self { func, loc }
    }
}

#[derive(Debug, Clone)]
struct AnalysisResult<'a> {
    sources: Vec<FuncLoc<'a>>,
    call_graph: FxHashMap<FuncLoc<'a>, FxHashSet<FuncLoc<'a>>>,
}

fn analyze<'a>(
    start_label: Label<'a>,
    mut analyzed_labels: FxHashSet<Label<'a>>,
    arena: &'a Arena<ExprLoc>,
    ctx: &'a HirCtx,
    tcx: TyCtxt<'_>,
) -> AnalysisResult<'a> {
    analyzed_labels.insert(start_label);
    let callers = ctx.callee_to_callers.get(&start_label.func_loc.func);
    let used_as_fn_ptr = ctx.ptr_used_fns.contains(&start_label.func_loc.func);

    let mut worklist = vec![start_label];
    let mut visited = FxHashSet::default();
    let mut func_to_return_bb = FxHashMap::default();
    let mut sources = vec![];
    let mut call_graph: FxHashMap<_, FxHashSet<_>> = FxHashMap::default();
    let mut fn_ptr_call = false;

    'l: while let Some(label) = worklist.pop() {
        if !visited.insert(label) {
            continue;
        }

        let body = tcx.optimized_mir(label.func_loc.func);
        let bbd = &body.basic_blocks[label.bb];
        let term = bbd.terminator();

        if let TerminatorKind::Call { func, .. } = &term.kind
            && let Some(args) = ctx.call_span_to_args.get(&term.source_info.span)
        {
            for (i, arg) in args.iter().enumerate() {
                let arg = some_or!(arg, continue);
                if !arg.is_prefix_of(label.func_loc.loc) {
                    continue;
                }

                if let Some(callee) = operand_to_def_id(func) {
                    if !api_list::is_def_id_api(callee, tcx) {
                        // intra call
                        let return_bb = *func_to_return_bb.entry(callee).or_insert_with(|| {
                            let body = tcx.optimized_mir(callee);
                            for (bb, bbd) in body.basic_blocks.iter_enumerated().rev() {
                                let term = bbd.terminator();
                                if matches!(term.kind, TerminatorKind::Return) {
                                    return bb;
                                }
                            }
                            panic!()
                        });
                        let node = tcx.hir_get_if_local(callee.to_def_id()).unwrap();
                        let Node::Item(item) = node else { panic!() };
                        let ItemKind::Fn { body, .. } = item.kind else { panic!() };
                        let body = tcx.hir_body(body);
                        let param = &body.params[i];
                        let PatKind::Binding(_, id, _, _) = param.pat.kind else { panic!() };
                        let base = ExprBase::Local(id);
                        let new_arg = arena.alloc(label.func_loc.loc.subst_prefix(base, arg));
                        let new_label = Label::new(callee, return_bb, new_arg);
                        call_graph
                            .entry(label.func_loc)
                            .or_default()
                            .insert(new_label.func_loc);
                        worklist.push(new_label);
                    } else if handling_api_indicator(callee, tcx).is_none() {
                        // api call
                        sources.push(label.func_loc);
                        continue 'l;
                    }
                } else {
                    fn_ptr_call = true;
                    sources.clear();
                    break 'l;
                }
            }
        }

        let predecessors = body.basic_blocks.predecessors();
        for pred in &predecessors[label.bb] {
            let label = Label { bb: *pred, ..label };
            worklist.push(label);
        }
    }

    if let ExprBase::Local(hir_id) = start_label.func_loc.loc.base
        && let Some(param_idx) = ctx.param_indices.get(&hir_id)
        && let Some(callers) = callers
        && !fn_ptr_call
        && !used_as_fn_ptr
        && sources.is_empty()
    {
        let mut failed = false;

        'l: for caller in callers {
            let body = tcx.optimized_mir(*caller);

            for (bb, bbd) in body.basic_blocks.iter_enumerated() {
                let term = bbd.terminator();
                let TerminatorKind::Call { func, .. } = &term.kind else { continue };
                let callee = some_or!(operand_to_def_id(func), continue);
                if callee != start_label.func_loc.func {
                    continue;
                }

                let args = &ctx.call_span_to_args[&term.source_info.span];
                let arg = args[*param_idx].as_ref().unwrap();
                let loc = start_label.func_loc.loc.change_base(arg);
                let label = Label::new(*caller, bb, arena.alloc(loc));

                if !analyzed_labels.contains(&label) {
                    let res = analyze(label, analyzed_labels.clone(), arena, ctx, tcx);
                    if !res.sources.is_empty() {
                        sources.extend(res.sources);
                        for (caller, callees) in res.call_graph {
                            call_graph.entry(caller).or_default().extend(callees);
                        }
                        continue;
                    }
                }

                failed = true;
                break 'l;
            }
        }

        if failed {
            sources.clear();
        }
    }

    AnalysisResult {
        sources,
        call_graph,
    }
}

#[inline]
fn handling_api_indicator(
    def_id: impl IntoQueryParam<DefId>,
    tcx: TyCtxt<'_>,
) -> Option<Indicator> {
    let name = compile_util::def_id_to_value_symbol(def_id, tcx).unwrap();
    let name = api_list::normalize_api_name(name.as_str());
    match name {
        "ferror" => Some(Indicator::Error),
        "feof" => Some(Indicator::Eof),
        _ => None,
    }
}

fn operand_to_def_id(op: &Operand<'_>) -> Option<LocalDefId> {
    let constant = op.constant()?;
    let Const::Val(_, ty) = constant.const_ else { unreachable!() };
    let ty::TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
    def_id.as_local()
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct ExprLoc {
    base: ExprBase,
    projections: Vec<ExprProj>,
}

impl std::fmt::Debug for ExprLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.base)?;
        for proj in &self.projections {
            write!(f, "{:?}", proj)?;
        }
        Ok(())
    }
}

impl ExprLoc {
    fn is_prefix_of(&self, other: &Self) -> bool {
        self.base == other.base
            && self.projections.len() <= other.projections.len()
            && self
                .projections
                .iter()
                .zip(&other.projections)
                .all(|(a, b)| a == b)
    }

    fn subst_prefix(&self, base: ExprBase, prefix: &Self) -> Self {
        assert!(prefix.is_prefix_of(self));
        Self {
            base,
            projections: self.projections[prefix.projections.len()..].to_vec(),
        }
    }

    fn change_base(&self, new: &Self) -> Self {
        let projections = new
            .projections
            .iter()
            .chain(&self.projections)
            .cloned()
            .collect();
        Self {
            base: new.base,
            projections,
        }
    }

    #[allow(unused)]
    #[inline]
    fn is_std(&self) -> bool {
        self.base.is_std()
    }

    #[allow(unused)]
    #[inline]
    fn is_global(&self) -> bool {
        self.base.is_global()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum ExprBase {
    Stdin,
    Stdout,
    Stderr,
    Global(LocalDefId),
    Local(HirId),
}

impl std::fmt::Debug for ExprBase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExprBase::Stdin => write!(f, "stdin"),
            ExprBase::Stdout => write!(f, "stdout"),
            ExprBase::Stderr => write!(f, "stderr"),
            ExprBase::Global(def_id) => write!(f, "{}", def_id_to_string(*def_id)),
            ExprBase::Local(hir_id) => write!(
                f,
                "{}:{:?}",
                def_id_to_string(hir_id.owner),
                hir_id.local_id
            ),
        }
    }
}

impl ExprBase {
    #[allow(unused)]
    #[inline]
    fn is_std(self) -> bool {
        matches!(self, ExprBase::Stdin | ExprBase::Stdout | ExprBase::Stderr)
    }

    #[allow(unused)]
    #[inline]
    fn is_global(self) -> bool {
        matches!(self, ExprBase::Global(_))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum ExprProj {
    Field(Symbol),
    Index,
}

impl std::fmt::Debug for ExprProj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExprProj::Field(name) => write!(f, ".{}", name),
            ExprProj::Index => write!(f, "[*]"),
        }
    }
}

fn expr_to_path(mut expr: &Expr<'_>, tcx: TyCtxt<'_>) -> Option<ExprLoc> {
    let mut projections = vec![];
    loop {
        match expr.kind {
            ExprKind::Unary(UnOp::Deref, e)
            | ExprKind::AddrOf(_, _, e)
            | ExprKind::Cast(e, _)
            | ExprKind::DropTemps(e) => expr = e,
            ExprKind::Field(e, f) => {
                projections.push(ExprProj::Field(f.name));
                expr = e;
            }
            ExprKind::Index(e, _, _) => {
                projections.push(ExprProj::Index);
                expr = e;
            }
            ExprKind::Path(QPath::Resolved(_, path)) => {
                let base = match path.res {
                    Res::Def(DefKind::Static { .. }, def_id) => {
                        let def_id = def_id.as_local()?;
                        let name = compile_util::def_id_to_value_symbol(def_id, tcx).unwrap();
                        match name.as_str() {
                            "stdin" => ExprBase::Stdin,
                            "stdout" => ExprBase::Stdout,
                            "stderr" => ExprBase::Stderr,
                            _ => ExprBase::Global(def_id),
                        }
                    }
                    Res::Local(hir_id) => ExprBase::Local(hir_id),
                    _ => return None,
                };
                projections.reverse();
                return Some(ExprLoc { base, projections });
            }
            _ => return None,
        }
    }
}

#[derive(Debug, Default)]
struct HirCtx {
    call_span_to_args: FxHashMap<Span, Vec<Option<ExprLoc>>>,
    error_handling_fns: FxHashSet<LocalDefId>,
    callee_to_callers: FxHashMap<LocalDefId, FxHashSet<LocalDefId>>,
    ptr_used_fns: FxHashSet<LocalDefId>,
    param_indices: FxHashMap<HirId, usize>,
}

struct HirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ctx: HirCtx,
}

impl<'tcx> HirVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            ctx: HirCtx::default(),
        }
    }
}

impl<'tcx> Visitor<'tcx> for HirVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_body(&mut self, body: &rustc_hir::Body<'tcx>) {
        intravisit::walk_body(self, body);

        for (i, param) in body.params.iter().enumerate() {
            let PatKind::Binding(_, hir_id, _, _) = param.pat.kind else { continue };
            self.ctx.param_indices.insert(hir_id, i);
        }
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        intravisit::walk_expr(self, expr);

        match expr.kind {
            ExprKind::Call(path, args) => {
                let mut v = vec![];
                for arg in args {
                    v.push(expr_to_path(arg, self.tcx));
                }
                if !v.is_empty() {
                    self.ctx.call_span_to_args.insert(expr.span, v);
                }

                let ExprKind::Path(QPath::Resolved(_, path)) = path.kind else { return };
                let Res::Def(DefKind::Fn, def_id) = path.res else { return };
                let curr_fn = expr.hir_id.owner.def_id;
                if handling_api_indicator(def_id, self.tcx).is_some() {
                    self.ctx.error_handling_fns.insert(curr_fn);
                }
                let def_id = some_or!(def_id.as_local(), return);
                self.ctx
                    .callee_to_callers
                    .entry(def_id)
                    .or_default()
                    .insert(curr_fn);
            }
            ExprKind::Path(QPath::Resolved(_, path)) => {
                let Res::Def(DefKind::Fn, def_id) = path.res else { return };
                let def_id = some_or!(def_id.as_local(), return);
                let mut parents = self.tcx.hir().parent_iter(expr.hir_id);
                let (_, parent) = parents.next().unwrap();
                let Node::Expr(parent) = parent else { panic!() };
                if let ExprKind::Call(callee, _) = parent.kind {
                    if callee.hir_id == expr.hir_id {
                        return;
                    }
                }
                self.ctx.ptr_used_fns.insert(def_id);
            }
            _ => {}
        }
    }
}

fn def_id_to_string(def_id: impl IntoQueryParam<DefId>) -> String {
    ty::tls::with_opt(|tcx| {
        let tcx = tcx.unwrap();
        let name = compile_util::def_id_to_value_symbol(def_id, tcx).unwrap();
        name.as_str().to_string()
    })
}
