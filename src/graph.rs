use std::collections::VecDeque;

use rustc_data_structures::{
    fx::{FxHashMap, FxHashSet},
    graph::{scc::Sccs, vec_graph::VecGraph},
};
use rustc_index::{bit_set::MixedBitSet, Idx, IndexVec};

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

    let mut reachability = IndexVec::from_raw(vec![MixedBitSet::new_empty(len); len]);
    for (v, succs) in graph.iter() {
        for succ in succs {
            reachability[v_to_id[v]].insert(v_to_id[succ]);
        }
    }

    bitset_transitive_closure(&mut reachability);

    let mut new_graph = FxHashMap::default();
    for (i, reachability) in reachability.iter().enumerate() {
        let neighbors = reachability.iter().map(|to| id_to_v[to]).collect();
        new_graph.insert(id_to_v[i], neighbors);
    }
    new_graph
}

pub fn bitset_transitive_closure<T: Idx>(graph: &mut IndexVec<T, MixedBitSet<T>>) {
    for k in graph.indices() {
        for i in graph.indices() {
            for j in graph.indices() {
                if graph[i].contains(k) && graph[k].contains(j) {
                    graph[i].insert(j);
                }
            }
        }
    }
}

pub fn bitset_reachable_vertices<T: Idx>(
    graph: &IndexVec<T, MixedBitSet<T>>,
    v: T,
) -> MixedBitSet<T> {
    let mut visited = MixedBitSet::new_empty(graph.len());
    let mut worklist = VecDeque::new();
    worklist.push_back(v);
    while let Some(u) = worklist.pop_front() {
        if visited.insert(u) {
            for w in graph[u].iter() {
                worklist.push_back(w);
            }
        }
    }
    visited
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
