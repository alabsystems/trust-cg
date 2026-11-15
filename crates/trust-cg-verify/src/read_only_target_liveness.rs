// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Target-local lexical liveness of architectural register/flag slots.
//!
//! Every template is inspected, even a dead result or a constant untaken arm.
//! Loads always consume their address; no memory demand is removed. This is
//! not source-guided simplification, an equivalence proof or instruction credit.

use super::{E, MAX_STEPS, MAX_TERM_NODES, ReadOnlyTargetError, SmtSort, Step, validate};
use std::collections::HashSet;

const FLAG_MASK: u64 = 0b1111 << 31;

fn input(expression: &E) -> Result<Option<u64>, ReadOnlyTargetError> {
    match expression {
        E::Var { name, width: 64 } => {
            let index = name.strip_prefix('x').and_then(|n| n.parse::<usize>().ok());
            let index = index
                .filter(|i| *i < 31 && name == &format!("x{i}"))
                .ok_or(ReadOnlyTargetError::Control(
                    "unknown architectural template input",
                ))?;
            Ok(Some(1 << index))
        }
        E::Var { .. } => Err(ReadOnlyTargetError::Control(
            "wrong-sort architectural template input",
        )),
        E::UF {
            name,
            args,
            ret_sort,
        } => {
            let index = ["flag_n", "flag_z", "flag_c", "flag_v"]
                .iter()
                .position(|n| *n == name);
            let index = index
                .filter(|_| args.is_empty() && *ret_sort == SmtSort::Bool)
                .ok_or(ReadOnlyTargetError::Control(
                    "unknown architectural template UF",
                ))?;
            Ok(Some(1 << (31 + index)))
        }
        _ => Ok(None),
    }
}

fn dependencies(
    expression: &E,
    seen: &mut HashSet<*const E>,
    work: &mut usize,
) -> Result<u64, ReadOnlyTargetError> {
    let mut pending = vec![expression];
    let mut used = 0;
    while let Some(node) = pending.pop() {
        if !seen.insert(node as *const E) {
            continue;
        }
        *work = work
            .checked_add(1)
            .filter(|n| *n <= MAX_TERM_NODES * MAX_STEPS)
            .ok_or(ReadOnlyTargetError::Budget(
                "target dependency template work",
            ))?;
        if seen.len() > MAX_TERM_NODES {
            return Err(ReadOnlyTargetError::Budget(
                "target dependency template work",
            ));
        }
        if let Some(slot) = input(node)? {
            used |= slot;
        }
        node.for_each_child(&mut |child| pending.push(child));
    }
    Ok(used)
}

/// Bit 0..30 names X0..X30; bits 31..34 name N/Z/C/V. Return each step's
/// live-IN set, derived solely from its exact templates and actual edges.
/// Uses precede definitions, preserving destination/flag read-before-write.
/// Unknown inputs are refused before any caller can use these sets to prune.
pub(super) fn compute(steps: &[Step]) -> Result<Vec<u64>, ReadOnlyTargetError> {
    compute_returning(steps, &[0])
}

/// The observed source ABI owns this list; no instruction hint can select or
/// omit a returned lane. Keep the one-result entry point exactly X0.
pub(super) fn compute_returning(
    steps: &[Step],
    registers: &[usize],
) -> Result<Vec<u64>, ReadOnlyTargetError> {
    if registers.is_empty() || registers.len() > 8 {
        return Err(ReadOnlyTargetError::Control("return register inventory"));
    }
    let mut returned = 0u64;
    for &register in registers {
        if register >= 8 || returned & (1u64 << register) != 0 {
            return Err(ReadOnlyTargetError::Control("return register inventory"));
        }
        returned |= 1u64 << register;
    }
    // Reuse the parent's exact shape/sort/reachability/acyclic-control checks.
    // A caller need not trust that a previous validation covered these steps.
    validate(steps)?;
    let mut uses = vec![0u64; steps.len()];
    let mut defs = vec![0u64; steps.len()];
    let mut edges = Vec::with_capacity(steps.len());
    let mut indegrees = vec![0usize; steps.len()];
    let mut work = 0usize;
    for (pc, step) in steps.iter().enumerate() {
        let mut seen = HashSet::new();
        let successors = match step {
            Step::Scalar {
                destination,
                value,
                flags,
            } => {
                uses[pc] |= dependencies(value, &mut seen, &mut work)?;
                if let Some(destination) = destination {
                    defs[pc] |= 1u64 << *destination;
                }
                if let Some(flags) = flags {
                    for flag in [&flags.n, &flags.z, &flags.c, &flags.v] {
                        uses[pc] |= dependencies(flag, &mut seen, &mut work)?;
                    }
                    defs[pc] |= FLAG_MASK;
                }
                vec![pc + 1]
            }
            Step::Load {
                destination,
                address,
                ..
            }
            | Step::MemoryLoad {
                destination,
                address,
                ..
            } => {
                uses[pc] |= dependencies(address, &mut seen, &mut work)?;
                if *destination != 31 {
                    defs[pc] |= 1u64 << *destination;
                }
                vec![pc + 1]
            }
            Step::MemoryStore { address, value, .. } => {
                uses[pc] |= dependencies(address, &mut seen, &mut work)?;
                uses[pc] |= dependencies(value, &mut seen, &mut work)?;
                // A memory write has no register/flag destination. Current
                // memory is owned by the observer, outside these slot sets.
                vec![pc + 1]
            }
            Step::LoadPair {
                destinations,
                address,
                ..
            } => {
                // The exact effective address is read before EITHER load
                // destination changes, including base/destination overlap.
                uses[pc] |= dependencies(address, &mut seen, &mut work)?;
                for destination in destinations {
                    if *destination != 31 {
                        defs[pc] |= 1u64 << *destination;
                    }
                }
                vec![pc + 1]
            }
            Step::Branch { condition, taken } => {
                uses[pc] |= dependencies(condition, &mut seen, &mut work)?;
                vec![*taken, pc + 1]
            }
            Step::Jump(target) => vec![*target],
            Step::Return => {
                uses[pc] |= returned;
                vec![]
            }
            Step::Inert => vec![pc + 1],
        };
        for &successor in &successors {
            indegrees[successor] += 1;
        }
        edges.push(successors);
    }
    // Physical layout order is NOT topological order. Legal acyclic branches
    // may run backwards in the byte stream, so derive the order from edges.
    let mut ready = indegrees
        .iter()
        .enumerate()
        .filter_map(|(i, &n)| (n == 0).then_some(i))
        .collect::<Vec<_>>();
    let mut order = Vec::with_capacity(steps.len());
    while let Some(pc) = ready.pop() {
        order.push(pc);
        for &successor in &edges[pc] {
            indegrees[successor] -= 1;
            if indegrees[successor] == 0 {
                ready.push(successor);
            }
        }
    }
    if order.len() != steps.len() {
        return Err(ReadOnlyTargetError::Control("cyclic target control"));
    }
    let mut live = vec![0u64; steps.len()];
    for pc in order.into_iter().rev() {
        let outgoing = edges[pc]
            .iter()
            .fold(0, |slots, &successor| slots | live[successor]);
        live[pc] = uses[pc] | (outgoing & !defs[pc]);
    }
    Ok(live)
}

#[cfg(test)]
mod tests {
    use super::super::{flags, register};
    use super::*;
    use crate::nzcv::NzcvFlags;

    fn scalar(destination: usize, value: E) -> Step {
        Step::Scalar {
            destination: Some(destination),
            value,
            flags: None,
        }
    }

    fn memory_value(index: usize, byte_width: u32) -> E {
        if byte_width == 4 {
            register(index).extract(31, 0)
        } else {
            register(index)
        }
    }

    fn store(address: E, value: E, byte_width: u32) -> Step {
        Step::MemoryStore {
            address,
            value: Box::new(value),
            byte_width,
            alignment: 1,
        }
    }

    fn assigned_flags(n: E) -> NzcvFlags {
        NzcvFlags {
            n,
            z: E::BoolConst(false),
            c: E::BoolConst(false),
            v: E::BoolConst(false),
        }
    }

    #[test]
    fn register_alias_uses_before_def_and_full_x0_return_is_live() {
        let live = compute(&[scalar(0, register(0).bvadd(register(1))), Step::Return]).unwrap();
        assert_eq!(live, [0b11, 1]);
        assert_eq!(
            compute(&[scalar(0, E::bv_const(7, 64)), Step::Return]).unwrap(),
            [0, 1]
        );
    }

    #[test]
    fn all_written_flags_are_inputs_before_latest_complete_definition() {
        let steps = [
            Step::Scalar {
                destination: None,
                value: E::bv_const(0, 64),
                flags: Some(Box::new(assigned_flags(
                    register(1).eq_expr(E::bv_const(0, 64)),
                ))),
            },
            Step::Scalar {
                destination: None,
                value: E::bv_const(0, 64),
                flags: Some(Box::new(assigned_flags(
                    register(2).eq_expr(E::bv_const(0, 64)),
                ))),
            },
            Step::Branch {
                condition: flags().n,
                taken: 4,
            },
            Step::Return,
            Step::Return,
        ];
        let live = compute(&steps).unwrap();
        assert_eq!(
            live[0],
            1 | (1 << 1) | (1 << 2),
            "dead flag producer is still inspected lexically"
        );
        assert_eq!(live[1], 1 | (1 << 2));
        assert_eq!(live[2], 1 | (1 << 31));
        let alias = Step::Scalar {
            destination: None,
            value: E::bv_const(0, 64),
            flags: Some(Box::new(NzcvFlags {
                n: flags().v,
                z: flags().z,
                c: flags().c,
                v: flags().n,
            })),
        };
        assert_eq!(compute(&[alias, Step::Return]).unwrap()[0], 1 | FLAG_MASK);
    }

    #[test]
    fn dead_and_discarded_load_results_never_erase_address_use() {
        let dead = [
            Step::Load {
                destination: 1,
                address: register(2),
                alignment: 8,
            },
            scalar(1, E::bv_const(0, 64)),
            Step::Return,
        ];
        assert_eq!(compute(&dead).unwrap()[0], 1 | (1 << 2));
        let discarded = [
            Step::Load {
                destination: 31,
                address: register(3),
                alignment: 8,
            },
            Step::Return,
        ];
        assert_eq!(compute(&discarded).unwrap()[0], 1 | (1 << 3));
        let alias = [
            Step::Load {
                destination: 0,
                address: register(0),
                alignment: 8,
            },
            Step::Return,
        ];
        assert_eq!(compute(&alias).unwrap(), [1, 1]);
    }

    #[test]
    fn scalar_memory_loads_keep_dead_discarded_and_aliased_address_reads() {
        for byte_width in [4, 8] {
            let dead = [
                Step::MemoryLoad {
                    destination: 1,
                    address: register(2),
                    byte_width,
                    alignment: 1,
                },
                scalar(1, E::bv_const(0, 64)),
                Step::Return,
            ];
            assert_eq!(compute(&dead).unwrap(), [1 | (1 << 2), 1, 1]);
            let discarded = [
                Step::MemoryLoad {
                    destination: 31,
                    address: register(3),
                    byte_width,
                    alignment: 1,
                },
                Step::Return,
            ];
            assert_eq!(compute(&discarded).unwrap(), [1 | (1 << 3), 1]);
            let alias = [
                Step::MemoryLoad {
                    destination: 0,
                    address: register(0),
                    byte_width,
                    alignment: 1,
                },
                Step::Return,
            ];
            assert_eq!(compute(&alias).unwrap(), [1, 1]);
        }
    }

    #[test]
    fn memory_stores_consume_both_inputs_without_killing_register_slots() {
        for byte_width in [4, 8] {
            let steps = [
                scalar(1, register(2)),
                store(register(1), memory_value(3, byte_width), byte_width),
                scalar(0, E::bv_const(9, 64)),
                Step::Return,
            ];
            assert_eq!(compute(&steps).unwrap(), [0b1100, 0b1010, 0, 1]);
            let aliased = [
                store(register(0), memory_value(0, byte_width), byte_width),
                Step::Return,
            ];
            assert_eq!(compute(&aliased).unwrap(), [1, 1]);
            let pass_through = [
                store(register(1), memory_value(2, byte_width), byte_width),
                scalar(0, register(3)),
                Step::Return,
            ];
            assert_eq!(compute(&pass_through).unwrap(), [0b1110, 0b1000, 1]);
        }
    }

    #[test]
    fn paired_loads_read_address_before_both_definitions_and_skip_zr_slots() {
        for byte_width in [4, 8] {
            let aliases = [
                Step::LoadPair {
                    destinations: [0, 1],
                    address: Box::new(register(0).bvadd(register(1))),
                    byte_width,
                    alignment: 1,
                },
                Step::Return,
            ];
            assert_eq!(compute(&aliases).unwrap(), [0b11, 1]);
            let both_used = [
                Step::LoadPair {
                    destinations: [1, 2],
                    address: Box::new(register(3)),
                    byte_width,
                    alignment: 1,
                },
                scalar(0, register(1).bvadd(register(2))),
                Step::Return,
            ];
            assert_eq!(compute(&both_used).unwrap(), [0b1000, 0b110, 1]);
            let dead_and_discarded = [
                Step::LoadPair {
                    destinations: [1, 31],
                    address: Box::new(register(2)),
                    byte_width,
                    alignment: 1,
                },
                scalar(1, E::bv_const(0, 64)),
                Step::Return,
            ];
            assert_eq!(compute(&dead_and_discarded).unwrap(), [0b101, 1, 1]);
            let discarded = [
                Step::LoadPair {
                    destinations: [31, 5],
                    address: Box::new(register(3)),
                    byte_width,
                    alignment: 1,
                },
                Step::Return,
            ];
            assert_eq!(compute(&discarded).unwrap(), [0b1001, 1]);
            let flags_after_discard = [
                Step::LoadPair {
                    destinations: [31, 5],
                    address: Box::new(register(3)),
                    byte_width,
                    alignment: 1,
                },
                Step::Branch {
                    condition: flags().n,
                    taken: 3,
                },
                Step::Return,
                Step::Return,
            ];
            assert_eq!(
                compute(&flags_after_discard).unwrap(),
                [0b1001 | (1 << 31), 1 | (1 << 31), 1, 1],
                "discarded register31 must not kill the N-flag slot"
            );
            assert!(matches!(
                compute(&[
                    Step::LoadPair {
                        destinations: [31, 31],
                        address: Box::new(register(3)),
                        byte_width,
                        alignment: 1,
                    },
                    Step::Return,
                ]),
                Err(ReadOnlyTargetError::Control(_))
            ));
            let base_and_discard = [
                Step::LoadPair {
                    destinations: [0, 31],
                    address: Box::new(register(0).bvadd(register(2))),
                    byte_width,
                    alignment: 1,
                },
                Step::Return,
            ];
            assert_eq!(compute(&base_and_discard).unwrap(), [0b101, 1]);
        }
    }

    #[test]
    fn constant_memory_branch_arms_remain_lexically_live() {
        for condition in [E::BoolConst(true), E::BoolConst(false), flags().z] {
            let condition_slots = if matches!(&condition, E::UF { .. }) {
                1 << 32
            } else {
                0
            };
            let steps = [
                Step::Branch {
                    condition,
                    taken: 3,
                },
                store(register(1), memory_value(2, 4), 4),
                Step::Return,
                store(register(3), memory_value(4, 8), 8),
                Step::Return,
            ];
            assert_eq!(
                compute(&steps).unwrap(),
                [0b11111 | condition_slots, 0b111, 1, 0b11001, 1]
            );
        }
    }

    #[test]
    fn malformed_memory_templates_refuse_even_discarded_or_untaken() {
        for (step, error) in [
            (
                Step::MemoryLoad {
                    destination: 31,
                    address: E::var("x01", 64),
                    byte_width: 4,
                    alignment: 1,
                },
                "unknown architectural template input",
            ),
            (
                Step::MemoryLoad {
                    destination: 1,
                    address: E::var("x0", 32).zero_ext(32),
                    byte_width: 8,
                    alignment: 1,
                },
                "wrong-sort architectural template input",
            ),
            (
                Step::LoadPair {
                    destinations: [31, 5],
                    address: Box::new(register(31)),
                    byte_width: 8,
                    alignment: 1,
                },
                "unknown architectural template input",
            ),
            (
                store(E::var("sp", 64), E::bv_const(0, 32), 4),
                "unknown architectural template input",
            ),
            (
                store(register(0), E::var("x1", 32), 4),
                "wrong-sort architectural template input",
            ),
            (
                store(register(0), E::uf("flag_n", vec![], SmtSort::BitVec(64)), 8),
                "unknown architectural template UF",
            ),
            (
                store(
                    register(0),
                    E::uf("unproved_memory", vec![], SmtSort::BitVec(32)),
                    4,
                ),
                "unknown architectural template UF",
            ),
        ] {
            // All four instructions are structurally reachable. A constant
            // taken branch must not hide an invalid memory template on the
            // other arm, even a load with discarded/dead register results.
            assert_eq!(
                compute(&[
                    Step::Branch {
                        condition: E::BoolConst(true),
                        taken: 3,
                    },
                    step,
                    Step::Return,
                    Step::Return,
                ])
                .unwrap_err(),
                ReadOnlyTargetError::Control(error)
            );
        }
    }

    #[test]
    fn independent_branch_successors_union_without_constant_pruning() {
        for condition in [flags().z, E::BoolConst(true), E::BoolConst(false)] {
            let expect_condition = if matches!(&condition, E::UF { .. }) {
                1 << 32
            } else {
                0
            };
            let steps = [
                Step::Branch {
                    condition,
                    taken: 3,
                },
                scalar(0, register(1)),
                Step::Return,
                scalar(0, register(2)),
                Step::Return,
            ];
            let live = compute(&steps).unwrap();
            assert_eq!(live[0], (1 << 1) | (1 << 2) | expect_condition);
            assert_eq!(live[1], 1 << 1);
            assert_eq!(live[3], 1 << 2);
        }
    }

    #[test]
    fn backward_layout_edges_use_actual_reverse_topology() {
        let steps = [
            Step::Jump(3),
            scalar(0, register(1)),
            Step::Return,
            Step::Jump(1),
        ];
        assert_eq!(compute(&steps).unwrap(), [1 << 1, 1 << 1, 1, 1 << 1]);
    }

    #[test]
    fn unknown_inputs_refuse_even_dead_outputs_and_untaken_arms() {
        for (value, error) in [
            (E::var("x01", 64), "unknown architectural template input"),
            (register(31), "unknown architectural template input"),
            (E::var("sp", 64), "unknown architectural template input"),
            (
                E::var("x0", 32).zero_ext(32),
                "wrong-sort architectural template input",
            ),
            (
                E::uf("not_a_flag", vec![], SmtSort::BitVec(64)),
                "unknown architectural template UF",
            ),
        ] {
            let dead = Step::Scalar {
                destination: None,
                value,
                flags: None,
            };
            assert_eq!(
                compute(&[
                    Step::Branch {
                        condition: E::BoolConst(true),
                        taken: 3
                    },
                    dead,
                    Step::Return,
                    Step::Return
                ])
                .unwrap_err(),
                ReadOnlyTargetError::Control(error)
            );
        }
        let wrong_flag = E::uf("flag_n", vec![E::bv_const(0, 64)], SmtSort::Bool);
        assert_eq!(
            compute(&[
                Step::Branch {
                    condition: wrong_flag,
                    taken: 1
                },
                Step::Return
            ])
            .unwrap_err(),
            ReadOnlyTargetError::Control("unknown architectural template UF")
        );
    }

    #[test]
    fn shared_template_walk_is_bounded_by_distinct_nodes_not_expanded_tree() {
        let mut expression = register(1);
        for _ in 0..20 {
            expression = expression.clone().bvadd(expression);
        }
        assert_eq!(
            compute(&[scalar(0, expression), Step::Return]).unwrap(),
            [1 << 1, 1]
        );
        // Dependency discovery does not construct the expanded term or alter
        // the parent's separate pre-substitution expression-work limits.
        assert_eq!(
            compute(&[Step::Jump(0)]).unwrap_err(),
            ReadOnlyTargetError::Control("cyclic target control")
        );
        assert_eq!(
            compute(&[]).unwrap_err(),
            ReadOnlyTargetError::Budget("endpoint steps")
        );
    }
}
