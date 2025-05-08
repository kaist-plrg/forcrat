use etrace::some_or;
use rustc_ast::UnOp;
use rustc_data_structures::fx::FxHashSet;
use rustc_hash::FxHashMap;
use rustc_hir::{
    def::{DefKind, Res},
    def_id::{DefId, LocalDefId},
    intravisit::{self, Visitor},
    Expr, ExprKind, HirId, QPath,
};
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
    compile_util::{self, Pass},
};

#[derive(Debug, Clone, Copy)]
pub struct ErrorFinder;

impl Pass for ErrorFinder {
    type Out = ();

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out {
        let mut visitor = HirVisitor::new(tcx);
        tcx.hir_visit_all_item_likes_in_crate(&mut visitor);

        for def_id in visitor.error_handling_fns {
            println!("{}", def_id_to_string(def_id));

            let body = tcx.optimized_mir(def_id);
            let predecessors = body.basic_blocks.predecessors();

            for (handle_bb, bbd) in body.basic_blocks.iter_enumerated() {
                let term = bbd.terminator();
                let TerminatorKind::Call { func, .. } = &term.kind else { continue };

                let handle_callee = some_or!(operand_to_def_id(func), continue);
                if !is_error_handling_fn(handle_callee, tcx) {
                    continue;
                }

                println!("{:?}", handle_bb);

                let handle_arg = visitor.call_span_to_args[&term.source_info.span][0]
                    .as_ref()
                    .unwrap();
                let arena = Arena::new();
                let arena = ListArena::new(&arena);
                let mut worklist = vec![(handle_bb, arena.nil)];
                let mut bb_to_calls = FxHashMap::default();
                let mut existing_call_bbss = FxHashSet::default();
                let mut completed_call_bbss = vec![];
                while let Some((bb, mut call_bbs)) = worklist.pop() {
                    if call_bbs.iter().any(|cbb: &BasicBlock| *cbb == bb) {
                        continue;
                    }

                    let bbd = &body.basic_blocks[bb];
                    let term = bbd.terminator();

                    if let TerminatorKind::Call { func, .. } = &term.kind {
                        let callee = operand_to_def_id(func);
                        let args = visitor.call_span_to_args.get(&term.source_info.span);
                        if args.is_some_and(|args| {
                            args.iter().any(|arg| {
                                arg.as_ref().is_some_and(|arg| arg.is_prefix_of(handle_arg))
                            })
                        }) {
                            call_bbs = arena.cons(bb, call_bbs);
                            if !existing_call_bbss.insert(call_bbs) {
                                continue;
                            }
                            bb_to_calls
                                .entry(bb)
                                .or_insert_with(|| Call { callee, args });
                        }

                        if callee.is_some_and(|callee| {
                            api_list::is_def_id_api(callee, tcx)
                                && !is_error_handling_fn(callee, tcx)
                        }) {
                            completed_call_bbss.push(call_bbs);
                            continue;
                        }
                    }

                    let preds = &predecessors[bb];
                    if preds.is_empty() {
                        completed_call_bbss.push(call_bbs);
                        continue;
                    }
                    for pred in preds {
                        worklist.push((*pred, call_bbs));
                    }
                }

                for (bb, call) in bb_to_calls {
                    println!("  {:?}: {:?}", bb, call);
                }
                for path in completed_call_bbss {
                    println!("  {:?}", path);
                }
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum List<'a, T> {
    Nil,
    Cons(T, &'a List<'a, T>),
}

impl<T: std::fmt::Debug> std::fmt::Debug for List<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T> List<'_, T> {
    fn iter(&self) -> ListIter<'_, T> {
        ListIter { list: self }
    }
}

struct ListIter<'a, T> {
    list: &'a List<'a, T>,
}

impl<'a, T> Iterator for ListIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.list {
            List::Nil => None,
            List::Cons(h, t) => {
                self.list = t;
                Some(h)
            }
        }
    }
}

struct ListArena<'a, T> {
    arena: &'a Arena<List<'a, T>>,
    nil: &'a List<'a, T>,
}

impl<'a, T> ListArena<'a, T> {
    fn new(arena: &'a Arena<List<'a, T>>) -> Self {
        Self {
            arena,
            nil: arena.alloc(List::Nil),
        }
    }

    fn cons(&self, head: T, tail: &'a List<'a, T>) -> &'a List<'a, T> {
        self.arena.alloc(List::Cons(head, tail))
    }
}

#[derive(Clone, Copy)]
struct Call<'a> {
    callee: Option<LocalDefId>,
    args: Option<&'a Vec<Option<ExprPath>>>,
}

impl std::fmt::Debug for Call<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(callee) = self.callee {
            write!(f, "{}(", def_id_to_string(callee))?;
        } else {
            write!(f, "?(")?;
        }
        if let Some(args) = self.args {
            for arg in args {
                if let Some(arg) = arg {
                    write!(f, "{:?}, ", arg)?;
                } else {
                    write!(f, "?, ")?;
                }
            }
        } else {
            write!(f, "??")?;
        }
        write!(f, ")")
    }
}

#[inline]
fn is_error_handling_fn(def_id: impl IntoQueryParam<DefId>, tcx: TyCtxt<'_>) -> bool {
    let name = compile_util::def_id_to_value_symbol(def_id, tcx).unwrap();
    let name = api_list::normalize_api_name(name.as_str());
    name == "feof" || name == "ferror" || name == "clearerr"
}

fn operand_to_def_id(op: &Operand<'_>) -> Option<LocalDefId> {
    let constant = op.constant()?;
    let Const::Val(_, ty) = constant.const_ else { unreachable!() };
    let ty::TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
    def_id.as_local()
}
// let name = compile_util::def_id_to_value_symbol(def_id, tcx).unwrap();
// let name = api_list::normalize_api_name(name.as_str());
// Some(name.to_string())

#[derive(Clone, PartialEq, Eq, Hash)]
struct ExprPath {
    base: ExprBase,
    projections: Vec<ExprProj>,
}

impl std::fmt::Debug for ExprPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.base)?;
        for proj in &self.projections {
            write!(f, "{:?}", proj)?;
        }
        Ok(())
    }
}

impl ExprPath {
    fn is_prefix_of(&self, other: &Self) -> bool {
        self.base == other.base
            && self.projections.len() <= other.projections.len()
            && self
                .projections
                .iter()
                .zip(&other.projections)
                .all(|(a, b)| a == b)
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

fn expr_to_path(mut expr: &Expr<'_>, tcx: TyCtxt<'_>) -> Option<ExprPath> {
    let mut projections = vec![];
    loop {
        match expr.kind {
            ExprKind::Unary(UnOp::Deref, e) | ExprKind::Cast(e, _) | ExprKind::DropTemps(e) => {
                expr = e
            }
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
                return Some(ExprPath { base, projections });
            }
            _ => return None,
        }
    }
}

struct HirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    call_span_to_args: FxHashMap<Span, Vec<Option<ExprPath>>>,
    error_handling_fns: FxHashSet<LocalDefId>,
}

impl<'tcx> HirVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            call_span_to_args: FxHashMap::default(),
            error_handling_fns: FxHashSet::default(),
        }
    }
}

impl<'tcx> Visitor<'tcx> for HirVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        intravisit::walk_expr(self, expr);

        let ExprKind::Call(path, args) = expr.kind else { return };
        let mut v = vec![];
        for arg in args {
            v.push(expr_to_path(arg, self.tcx));
        }
        if !v.is_empty() {
            self.call_span_to_args.insert(expr.span, v);
        }

        let ExprKind::Path(QPath::Resolved(_, path)) = path.kind else { return };
        let Res::Def(DefKind::Fn, def_id) = path.res else { return };
        if is_error_handling_fn(def_id, self.tcx) {
            self.error_handling_fns.insert(expr.hir_id.owner.def_id);
        }
    }
}

fn def_id_to_string(def_id: impl IntoQueryParam<DefId>) -> String {
    ty::tls::with_opt(|tcx| {
        tcx.unwrap()
            .def_path(def_id.into_query_param())
            .to_string_no_crate_verbose()
    })
}
