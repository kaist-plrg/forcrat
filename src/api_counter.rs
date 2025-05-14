use etrace::some_or;
use rustc_hash::FxHashMap;
use rustc_hir::{
    def::{DefKind, Res},
    intravisit,
    intravisit::Visitor,
    Expr, ExprKind, HirId, ItemKind, Path, QPath,
};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};

use crate::{
    api_list::{is_symbol_api, normalize_api_name, API_MAP},
    compile_util::{def_id_to_value_symbol, is_std_io_expr, Pass},
};

#[derive(Debug, Clone, Copy)]
pub struct ApiCounter;

impl Pass for ApiCounter {
    type Out = (
        FxHashMap<&'static str, usize>,
        FxHashMap<&'static str, usize>,
    );

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out {
        let mut visitor = ApiVisitor::new(tcx);

        for item_id in tcx.hir_free_items() {
            let item = tcx.hir_item(item_id);
            let name = item.ident.name;
            if name.as_str() == "main" || is_symbol_api(name) {
                continue;
            }
            let (ItemKind::Fn { body: body_id, .. }
            | ItemKind::Static(_, _, body_id)
            | ItemKind::Const(_, _, body_id)) = item.kind
            else {
                continue;
            };
            let body = tcx.hir_body(body_id);
            visitor.visit_body(body);
        }

        (visitor.counts, visitor.std_arg_counts)
    }
}

struct ApiVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    counts: FxHashMap<&'static str, usize>,
    std_arg_counts: FxHashMap<&'static str, usize>,
}

impl<'tcx> ApiVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            counts: FxHashMap::default(),
            std_arg_counts: FxHashMap::default(),
        }
    }

    fn handle_expr(&mut self, expr: &'tcx Expr<'tcx>) -> bool {
        let ExprKind::Call(callee, args) = &expr.kind else { return false };
        let ExprKind::Path(QPath::Resolved(_, path)) = &callee.kind else { return false };
        let Res::Def(DefKind::Fn, def_id) = path.res else { return true };
        let symbol = some_or!(def_id_to_value_symbol(def_id, self.tcx), return true);
        let name = normalize_api_name(symbol.as_str());
        let (name, api_kind) = some_or!(API_MAP.get_key_value(name), return true);
        if !api_kind.is_posix_io() {
            return true;
        }
        let counts = if (api_kind.is_read() || api_kind.is_write())
            && args.iter().any(|arg| is_std_io_expr(arg, self.tcx))
        {
            &mut self.std_arg_counts
        } else {
            &mut self.counts
        };
        *counts.entry(*name).or_default() += 1;
        true
    }

    fn handle_path(&mut self, path: &Path<'tcx>) {
        let Res::Def(DefKind::Fn, def_id) = path.res else { return };
        let symbol = some_or!(def_id_to_value_symbol(def_id, self.tcx), return);
        let name = normalize_api_name(symbol.as_str());
        let (name, _) = some_or!(API_MAP.get_key_value(name), return);
        *self.counts.entry(*name).or_default() += 1;
    }
}

impl<'tcx> Visitor<'tcx> for ApiVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if !self.handle_expr(expr) {
            intravisit::walk_expr(self, expr);
        }
    }

    fn visit_path(&mut self, path: &Path<'tcx>, _: HirId) {
        self.handle_path(path);
        intravisit::walk_path(self, path);
    }
}
