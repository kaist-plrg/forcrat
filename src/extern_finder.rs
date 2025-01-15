use std::collections::{HashMap, HashSet};

use etrace::some_or;
use rustc_hir::{
    def::{DefKind, Res},
    def_id::{DefId, LocalDefId},
    intravisit::{self, Visitor as HVisitor},
    BodyId, Expr, ExprKind, FnDecl, FnRetTy, ForeignItem, ForeignItemKind, ItemKind, Node, OwnerId,
    QPath,
};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};

use crate::compile_util::Pass;

#[derive(Debug, Clone, Copy)]
pub struct ExternFinder;

impl Pass for ExternFinder {
    type Out = ();

    fn run(&self, tcx: TyCtxt<'_>) {
        let hir = tcx.hir();
        let mut visitor = ExternVisitor::new(tcx);
        hir.visit_all_item_likes_in_crate(&mut visitor);
        // for f in visitor.file_fns {
        //     println!("{:?}", f);
        // }
        for (op, n) in visitor.file_calls {
            println!("{} {:?}", tcx.def_path_str(op), n);
        }
    }
}

struct ExternVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    file_fns: HashSet<LocalDefId>,
    file_externs: HashSet<String>,
    file_calls: HashMap<LocalDefId, HashSet<String>>,
    file_calls_count: HashMap<String, usize>,
}

impl<'tcx> ExternVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            file_fns: HashSet::new(),
            file_externs: HashSet::new(),
            file_calls: HashMap::new(),
            file_calls_count: HashMap::new(),
        }
    }
}

impl<'tcx> HVisitor<'tcx> for ExternVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_foreign_item(&mut self, item: &'tcx ForeignItem<'tcx>) {
        if self.is_file_extern_item(item) {
            self.file_externs.insert(item.ident.name.to_ident_string());
        }
        intravisit::walk_foreign_item(self, item)
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        self.handle_expr(expr);
        intravisit::walk_expr(self, expr)
    }

    fn visit_fn(
        &mut self,
        fk: intravisit::FnKind<'tcx>,
        fd: &'tcx FnDecl<'tcx>,
        body_id: BodyId,
        _: rustc_span::Span,
        def_id: LocalDefId,
    ) {
        if self.is_file_op_decl(fd) {
            self.file_fns.insert(def_id);
        }
        intravisit::walk_fn(self, fk, fd, body_id, def_id)
    }
}

impl<'tcx> ExternVisitor<'tcx> {
    fn handle_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        let current_func = expr.hir_id.owner.def_id;
        if self.is_defined_file_extern(current_func.to_def_id()) {
            return;
        }
        match expr.kind {
            ExprKind::Call(callee, _) => {
                let ExprKind::Path(QPath::Resolved(_, path)) = callee.kind else { return };
                let Res::Def(DefKind::Fn, def_id) = path.res else { return };
                if !self.is_file_extern(def_id) {
                    return;
                }
                let name = path.segments.last().unwrap().ident.name.to_ident_string();
                self.file_calls
                    .entry(current_func)
                    .or_default()
                    .insert(name.clone());
                *self.file_calls_count.entry(name.clone()).or_default() += 1;

                // let ForeignItemKind::Fn(decl, _, _) = item.kind else { return };
                // if decl
                //     .inputs
                //     .iter()
                //     .zip(args)
                //     .any(|(ty, arg)| self.has_file_ty(ty) && !self.is_std_io(arg))
                // {
                //     println!("{:?} {}", current_func, name);
                // }
            }
            ExprKind::Field(e, _) => {
                let ty = self.tcx.typeck(current_func).expr_ty(e);
                let rustc_middle::ty::TyKind::Adt(adt_def, _) = ty.kind() else { return };
                let node = some_or!(self.tcx.hir().get_if_local(adt_def.did()), return);
                let Node::Item(item) = node else { return };
                if item.ident.name.to_ident_string() == "_IO_FILE" {
                    // println!("{}", self.tcx.def_path_str(current_func));
                }
            }
            _ => {}
        }
    }

    fn is_file_extern(&self, def_id: DefId) -> bool {
        self.is_defined_file_extern(def_id) || self.is_linked_file_extern(def_id)
    }

    fn is_defined_file_extern(&self, def_id: DefId) -> bool {
        let node = some_or!(self.tcx.hir().get_if_local(def_id), return false);
        let Node::Item(item) = node else { return false };
        matches!(item.kind, ItemKind::Fn(_, _, _)) && {
            let name = item.ident.name.to_ident_string();
            name == "putc_unlocked"
                || name == "fputc_unlocked"
                || name == "getc_unlocked"
                || name == "ferror_unlocked"
                || name == "getline"
                || name == "feof_unlocked"
                || name == "fpurge"
                || name == "feof_unlocked"
        }
    }

    fn is_linked_file_extern(&self, def_id: DefId) -> bool {
        if !self.tcx.is_foreign_item(def_id) {
            return false;
        }
        let local_def_id = some_or!(def_id.as_local(), return false);
        let id = OwnerId {
            def_id: local_def_id,
        };
        let item = self.tcx.hir().expect_foreign_item(id);
        self.is_file_extern_item(item)
    }

    fn is_file_extern_item(&self, item: &'tcx ForeignItem<'tcx>) -> bool {
        match item.kind {
            ForeignItemKind::Fn(decl, _, _) => self.is_file_op_decl(decl),
            ForeignItemKind::Static(ty, _) => self.has_file_ty(ty),
            _ => false,
        }
    }

    fn is_file_op_decl(&self, decl: &'tcx FnDecl<'tcx>) -> bool {
        decl.inputs.iter().any(|ty| self.has_file_ty(ty))
            || if let FnRetTy::Return(ty) = decl.output {
                self.has_file_ty(ty)
            } else {
                false
            }
    }

    fn has_file_ty(&self, ty: &'tcx rustc_hir::Ty<'tcx>) -> bool {
        let mut visitor = TyVisitor::new(self.tcx);
        visitor.visit_ty(ty);
        visitor.has_file
    }

    fn is_std_io(&self, expr: &'tcx Expr<'tcx>) -> bool {
        let ExprKind::Path(QPath::Resolved(_, path)) = expr.kind else { return false };
        let Res::Def(DefKind::Static(_), def_id) = path.res else { return false };
        if !self.tcx.is_foreign_item(def_id) {
            return false;
        }
        let name = path.segments.last().unwrap().ident.name.to_ident_string();
        name == "stdin" || name == "stdout" || name == "stderr"
    }
}

struct TyVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    has_file: bool,
}

impl<'tcx> TyVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            has_file: false,
        }
    }
}

impl<'tcx> HVisitor<'tcx> for TyVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_ty(&mut self, t: &'tcx rustc_hir::Ty<'tcx>) {
        if let rustc_hir::TyKind::Path(QPath::Resolved(_, path)) = t.kind {
            let seg = path.segments.last().unwrap();
            let name = seg.ident.name.to_ident_string();
            if name == "FILE" {
                self.has_file = true;
            }
        }
        intravisit::walk_ty(self, t)
    }
}
