// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Budgeted admission of a body at its greatest reached remaining depth.
//!
//! This is the production walk's visitation rule, not a second MIR analysis.
//! A repeated body can expose more callees when a shorter route reaches it.
//! Every admitted read, including such a revisit, consumes the same budget.
//! Exhaustion still supplies no absence or traversal-order-independence claim.

use std::collections::{HashMap, hash_map::Entry};
use std::hash::Hash;

pub(super) fn admit<K: Eq + Hash>(
    seen: &mut HashMap<K, usize>,
    budget: &mut usize,
    key: K,
    depth: usize,
) -> bool {
    if *budget == 0 {
        return false;
    }
    // One hash lookup per attempt; a revisit updates the existing entry.
    match seen.entry(key) {
        Entry::Occupied(mut entry) => {
            if *entry.get() >= depth {
                return false;
            }
            entry.insert(depth);
        }
        Entry::Vacant(entry) => {
            entry.insert(depth);
        }
    }
    *budget -= 1;
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Body {
        pad: bool,
        callees: Vec<usize>,
    }

    // Exercise the actual admission rule on an independent finite graph;
    // no rustc/MIR authority or native unwind outcome is inferred here.
    fn walk(
        bodies: &[Body],
        key: usize,
        depth: usize,
        seen: &mut HashMap<usize, usize>,
        budget: &mut usize,
    ) -> bool {
        if !admit(seen, budget, key, depth) {
            return false;
        }
        bodies[key].pad
            || (depth != 0
                && bodies[key]
                    .callees
                    .iter()
                    .any(|callee| walk(bodies, *callee, depth - 1, seen, budget)))
    }

    // Independent depth-bounded reference: no visited set or admission helper.
    fn reference(bodies: &[Body], key: usize, depth: usize) -> bool {
        bodies[key].pad
            || (depth != 0
                && bodies[key]
                    .callees
                    .iter()
                    .any(|callee| reference(bodies, *callee, depth - 1)))
    }

    fn diamond(deep_first: bool) -> Vec<Body> {
        // A -> B -> C -> X first reaches X at depth zero. A -> X can
        // instead reach Y's pad; X must not be discarded as merely seen.
        vec![
            Body {
                pad: false,
                callees: if deep_first { vec![1, 3] } else { vec![3, 1] },
            },
            Body {
                pad: false,
                callees: vec![2],
            },
            Body {
                pad: false,
                callees: vec![3],
            },
            Body {
                pad: false,
                callees: vec![4],
            },
            Body {
                pad: true,
                callees: vec![],
            },
        ]
    }

    #[test]
    fn admit_keeps_maximum_depth_and_charges_only_admitted_reads() {
        let mut seen = HashMap::new();
        let mut budget = 5;
        assert!(admit(&mut seen, &mut budget, "callee", 0));
        assert_eq!((seen["callee"], budget), (0, 4));
        assert!(!admit(&mut seen, &mut budget, "callee", 0));
        assert_eq!((seen["callee"], budget), (0, 4));
        assert!(admit(&mut seen, &mut budget, "callee", 2));
        assert_eq!((seen["callee"], budget), (2, 3));
        for depth in [0, 1, 2] {
            assert!(!admit(&mut seen, &mut budget, "callee", depth));
            assert_eq!((seen["callee"], budget), (2, 3));
        }
        assert!(admit(&mut seen, &mut budget, "other", 1));
        assert_eq!((seen["other"], budget), (1, 2));
    }

    #[test]
    fn exhausted_budget_changes_neither_new_nor_previously_seen_keys() {
        let mut seen = HashMap::from([("old", 0)]);
        let original = seen.clone();
        let mut budget = 0;
        assert!(!admit(&mut seen, &mut budget, "new", 3));
        assert!(!admit(&mut seen, &mut budget, "old", 3));
        assert_eq!(seen, original);
        assert_eq!(budget, 0);
    }

    #[test]
    fn diamond_finds_the_deeper_pad_in_both_callee_orders() {
        for (deep_first, reads) in [(true, 6), (false, 3)] {
            let bodies = diamond(deep_first);
            let mut seen = HashMap::new();
            let mut budget = 256;
            assert!(reference(&bodies, 0, 3));
            assert!(walk(&bodies, 0, 3, &mut seen, &mut budget));
            assert_eq!(seen[&3], 2);
            assert_eq!(seen[&4], 1);
            assert_eq!(256 - budget, reads);
        }
    }

    #[test]
    fn depth_walk_matches_reference_for_all_three_body_graphs() {
        // All nine directed edges, including cycles and shared successors;
        // every pad assignment and every production-depth value. This budget
        // cannot exhaust: three keys can each increase at most four times.
        for edges in 0_u16..(1 << 9) {
            for pads in 0_u8..(1 << 3) {
                let bodies = (0..3)
                    .map(|key| Body {
                        pad: pads & (1 << key) != 0,
                        callees: (0..3)
                            .filter(|callee| edges & (1 << (key * 3 + *callee)) != 0)
                            .collect(),
                    })
                    .collect::<Vec<_>>();
                for depth in 0..=3 {
                    let mut seen = HashMap::new();
                    let mut budget = 256;
                    assert_eq!(
                        walk(&bodies, 0, depth, &mut seen, &mut budget),
                        reference(&bodies, 0, depth),
                        "edges={edges:#x} pads={pads:#x} depth={depth}"
                    );
                    assert!(256 - budget <= 3 * (depth + 1));
                }
            }
        }
    }

    #[test]
    fn cycle_without_any_pad_remains_false_and_bounded() {
        let bodies = vec![
            Body {
                pad: false,
                callees: vec![1],
            },
            Body {
                pad: false,
                callees: vec![0],
            },
        ];
        let mut seen = HashMap::new();
        let mut budget = 256;
        assert!(!reference(&bodies, 0, 3));
        assert!(!walk(&bodies, 0, 3, &mut seen, &mut budget));
        assert_eq!(seen, HashMap::from([(0, 3), (1, 2)]));
        assert_eq!(budget, 254);
    }

    #[test]
    fn exhaustion_retains_the_open_direction_without_order_independence() {
        let mut deep_seen = HashMap::new();
        let mut deep_budget = 4;
        assert!(!walk(
            &diamond(true),
            0,
            3,
            &mut deep_seen,
            &mut deep_budget
        ));
        assert_eq!(deep_budget, 0);
        assert_eq!(deep_seen[&3], 0);
        assert!(!deep_seen.contains_key(&4));
        let mut short_seen = HashMap::new();
        let mut short_budget = 4;
        assert!(walk(
            &diamond(false),
            0,
            3,
            &mut short_seen,
            &mut short_budget,
        ));
        assert_eq!(short_budget, 1);
        assert_eq!(short_seen[&3], 2);
    }
}
