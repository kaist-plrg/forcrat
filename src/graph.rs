use rustc_data_structures::fx::{FxHashMap, FxHashSet};

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
    let mut inv: FxHashMap<_, FxHashSet<_>> = FxHashMap::default();
    for (node, succs) in map {
        for succ in succs {
            inv.entry(*succ).or_default().insert(*node);
        }
    }
    inv
}
