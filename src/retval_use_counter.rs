use etrace::some_or;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::ItemKind;
use rustc_middle::{
    mir::{
        visit::{MutatingUseContext, PlaceContext, Visitor},
        ConstantKind, Local, Location, Place, Terminator, TerminatorKind,
    },
    ty::{TyCtxt, TyKind},
};

use crate::{
    api_list::{is_symbol_api, normalize_api_name, API_MAP},
    compile_util::{def_id_to_value_symbol, Pass},
};

#[derive(Debug, Clone, Copy, Default)]
pub struct UseCounts {
    pub used: usize,
    pub unused: usize,
}

#[derive(Debug, Clone, Copy)]
pub struct RetValCounter;

impl Pass for RetValCounter {
    type Out = FxHashMap<&'static str, UseCounts>;

    fn run(&self, tcx: TyCtxt<'_>) -> Self::Out {
        let hir = tcx.hir();
        let mut counts: FxHashMap<&'static str, UseCounts> = FxHashMap::default();
        for item_id in hir.items() {
            let item = hir.item(item_id);
            let name = item.ident.name;
            if name.as_str() == "main" || is_symbol_api(name) {
                continue;
            }
            let def_id = item.owner_id.to_def_id();
            let body = match item.kind {
                ItemKind::Fn(_, _, _) => tcx.optimized_mir(def_id),
                ItemKind::Static(_, _, _) | ItemKind::Const(_, _, _) => tcx.mir_for_ctfe(def_id),
                _ => continue,
            };
            let mut visitor = RetValVisitor::new(tcx);
            visitor.visit_body(body);
            for (api, dst) in visitor.destinations {
                let counts = counts.entry(api).or_default();
                if visitor.used_places.contains(&dst) {
                    counts.used += 1;
                } else {
                    counts.unused += 1;
                }
            }
        }
        counts
    }
}

struct RetValVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    destinations: Vec<(&'static str, Local)>,
    used_places: FxHashSet<Local>,
}

impl<'tcx> RetValVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            destinations: vec![],
            used_places: FxHashSet::default(),
        }
    }

    fn handle_terminator(&mut self, terminator: &Terminator<'tcx>) {
        let TerminatorKind::Call {
            destination, func, ..
        } = &terminator.kind
        else {
            return;
        };
        let constant = some_or!(func.constant(), return);
        let ConstantKind::Val(_, ty) = constant.literal else { return };
        let TyKind::FnDef(def_id, _) = ty.kind() else { return };
        let symbol = some_or!(def_id_to_value_symbol(def_id, self.tcx), return);
        let name = normalize_api_name(symbol.as_str());
        let (name, _) = some_or!(API_MAP.get_key_value(name), return);
        self.destinations.push((name, destination.local));
    }
}

impl<'tcx> Visitor<'tcx> for RetValVisitor<'tcx> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        self.handle_terminator(terminator);
        self.super_terminator(terminator, location);
    }

    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if !matches!(
            context,
            PlaceContext::MutatingUse(MutatingUseContext::Call | MutatingUseContext::Store)
        ) {
            self.used_places.insert(place.local);
        }
        self.super_place(place, context, location);
    }
}
