use rustc_data_structures::{
    fx::{FxHashMap, FxHashSet},
    graph::{scc::Sccs, vec_graph::VecGraph},
};

pub fn transitive_closure<T: Copy + Eq + std::hash::Hash>(
    graph: &FxHashMap<T, FxHashSet<T>>,
) -> FxHashMap<T, FxHashSet<T>> {
    for succs in graph.values() {
        for succ in succs {
            assert!(graph.contains_key(succ));
        }
    }
    let id_to_v: Vec<_> = graph.keys().copied().collect();
    let v_to_id: FxHashMap<_, _> = id_to_v
        .iter()
        .copied()
        .enumerate()
        .map(|(k, v)| (v, k))
        .collect();
    let len = id_to_v.len();

    let mut reachability = vec![vec![false; len]; len];
    for (v, succs) in graph.iter() {
        for succ in succs {
            reachability[v_to_id[v]][v_to_id[succ]] = true;
        }
    }

    for k in 0..len {
        for i in 0..len {
            for j in 0..len {
                reachability[i][j] =
                    reachability[i][j] || (reachability[i][k] && reachability[k][j]);
            }
        }
    }

    let mut new_graph = FxHashMap::default();
    for (i, reachability) in reachability.iter().enumerate() {
        let neighbors = reachability
            .iter()
            .enumerate()
            .filter_map(|(to, is_reachable)| {
                if *is_reachable {
                    Some(id_to_v[to])
                } else {
                    None
                }
            })
            .collect();
        new_graph.insert(id_to_v[i], neighbors);
    }
    new_graph
}

pub fn inverse<T: Copy + Eq + std::hash::Hash>(
    map: &FxHashMap<T, FxHashSet<T>>,
) -> FxHashMap<T, FxHashSet<T>> {
    let mut inv = FxHashMap::default();
    for node in map.keys() {
        inv.insert(*node, FxHashSet::default());
    }
    for (node, succs) in map {
        for succ in succs {
            inv.get_mut(succ).unwrap().insert(*node);
        }
    }
    inv
}

pub fn compute_sccs<T: Copy + Eq + std::hash::Hash>(
    map: &FxHashMap<T, FxHashSet<T>>,
) -> (
    FxHashMap<SccId, FxHashSet<SccId>>,
    FxHashMap<SccId, FxHashSet<T>>,
) {
    let id_map: FxHashMap<_, _> = map.keys().enumerate().map(|(i, f)| (i, *f)).collect();
    let inv_id_map: FxHashMap<_, _> = id_map.iter().map(|(i, f)| (*f, *i)).collect();
    let edges = map
        .iter()
        .flat_map(|(node, succs)| {
            succs.iter().map(|succ| {
                (
                    SccId::from_usize(*inv_id_map.get(node).unwrap()),
                    SccId::from_usize(*inv_id_map.get(succ).unwrap()),
                )
            })
        })
        .collect();
    let vec_graph: VecGraph<SccId> = VecGraph::new(map.len(), edges);
    let sccs: Sccs<SccId, SccId> = Sccs::new(&vec_graph);

    let component_graph: FxHashMap<_, _> = sccs
        .all_sccs()
        .map(|node| (node, sccs.successors(node).iter().copied().collect()))
        .collect();

    let mut component_elems: FxHashMap<_, FxHashSet<_>> = FxHashMap::default();
    for i in 0..(map.len()) {
        let scc = sccs.scc(SccId::from_usize(i));
        let node = id_map[&i];
        component_elems.entry(scc).or_default().insert(node);
    }

    (component_graph, component_elems)
}

rustc_index::newtype_index! {
    #[orderable]
    #[debug_format = "Scc{}"]
    pub struct SccId {}
}
