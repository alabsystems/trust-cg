// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Private driver controls, not solver replay or source/native qualification.
//! Each Step is a semantic template from the driver's internal boundary.
//! Production word/MachIR adapter controls remain separate owning tests.

use super::*;
use crate::smt::EvalEnv;

fn rejected<T>(result: Result<T, ReadOnlyTargetError>, expected: ReadOnlyTargetError) {
    assert_eq!(result.err(), Some(expected));
}

fn scalar(destination: usize, value: E) -> Step {
    Step::Scalar {
        destination: Some(destination),
        value,
        flags: None,
    }
}

fn inputs() -> Vec<(String, u32)> {
    vec![("abi_x0".into(), 64)]
}

fn environment(input: u64) -> EvalEnv {
    let mut env = EvalEnv::default();
    env.insert("abi_x0".into(), input);
    env
}

fn selected(observation: &Observations, input: u64) -> u64 {
    let env = environment(input);
    let mut matching = observation
        .returns
        .iter()
        .filter(|(guard, _)| guard.expr.try_eval(&env).unwrap().as_bool());
    let (_, result) = matching.next().expect("one complete path");
    assert!(
        matching.next().is_none(),
        "mutually exclusive complete paths"
    );
    result.expr.try_eval(&env).unwrap().as_u64()
}

fn shared(depth: usize, mut expression: E) -> E {
    // Only two shallow root copies per level; existing Arc children are shared.
    // Expanded tree size is 2^(depth+1)-1 although distinct nodes are linear.
    for _ in 0..depth {
        expression = expression.clone().bvadd(expression);
    }
    expression
}

fn state() -> State {
    State {
        pc: 0,
        x: std::array::from_fn(|i| Some(Term::leaf(E::var(format!("entry_x{i}"), 64)))),
        flags: std::array::from_fn(|_| Some(Term::leaf(E::BoolConst(false)))),
        guard: Term::leaf(E::BoolConst(true)),
        memory: None,
    }
}

fn large_registers(count: usize) -> Vec<Step> {
    // 13 self-ADDs leave x0 with 16,383 expanded nodes. Subsequent copies
    // duplicate no large subtree in the test builder or production rewriter.
    let mut steps = (0..13)
        .map(|_| scalar(0, register(0).bvadd(register(0))))
        .collect::<Vec<_>>();
    steps.extend((1..count).map(|index| scalar(index, register(0))));
    steps
}

fn same_successor_forks(count: usize, mut steps: Vec<Step>) -> Vec<Step> {
    for _ in 0..count {
        let next = steps.len() + 1;
        steps.push(Step::Branch {
            condition: E::BoolConst(true),
            taken: next,
        });
    }
    steps.push(Step::Return);
    steps
}

/// Give the resource fixtures real lexical consumers on every return path.
/// Edges naming a former Return now enter its consumers, not the new Return.
/// No production liveness switch, smaller limit or artificial state weight.
fn retain_before_each_return(steps: Vec<Step>, registers: usize) -> Vec<Step> {
    let consumers = registers + 4;
    let mut mapping = Vec::with_capacity(steps.len());
    let mut next = 0;
    for step in &steps {
        mapping.push(next);
        next += if matches!(step, Step::Return) {
            consumers + 1
        } else {
            1
        };
    }
    assert!(next <= MAX_STEPS, "resource fixture remains bounded");
    let mut retained = Vec::with_capacity(next);
    for step in steps {
        match step {
            Step::Branch { condition, taken } => retained.push(Step::Branch {
                condition,
                taken: mapping[taken],
            }),
            Step::Jump(target) => retained.push(Step::Jump(mapping[target])),
            Step::Return => {
                for i in 0..registers {
                    retained.push(Step::Scalar {
                        destination: None,
                        value: register(i),
                        flags: None,
                    });
                }
                // Initial Bool flags have three logical nodes each. Retain
                // their actual terms through both forks; metadata is no use.
                let flags = flags();
                for flag in [flags.n, flags.z, flags.c, flags.v] {
                    retained.push(Step::Scalar {
                        destination: None,
                        value: E::ite(flag, E::bv_const(1, 64), E::bv_const(0, 64)),
                        flags: None,
                    });
                }
                retained.push(Step::Return);
            }
            other => retained.push(other),
        }
    }
    assert_eq!(retained.len(), next);
    retained
}

#[test]
fn dag_accounting_charges_expanded_work_and_substitution_before_clone() {
    let expression = shared(14, register(0));
    assert_eq!(
        expression_nodes(&expression, None, MAX_TERM_NODES).unwrap(),
        MAX_TERM_NODES - 1
    );
    let boundary = expression.bvneg();
    assert_eq!(
        expression_nodes(&boundary, None, MAX_TERM_NODES).unwrap(),
        MAX_TERM_NODES
    );
    let mut before = state();
    let composed = compose(&boundary, &before).unwrap();
    assert_eq!(composed.nodes, MAX_TERM_NODES);
    rejected(
        compose(&boundary.clone().bvneg(), &before),
        ReadOnlyTargetError::Budget("logical expression work"),
    );
    before.x[0] = Some(composed);
    assert_eq!(
        compose(&register(0), &before).unwrap().nodes,
        MAX_TERM_NODES
    );
    rejected(
        compose(&register(0).bvneg(), &before),
        ReadOnlyTargetError::Budget("logical expression work"),
    );
    rejected(
        expression_nodes(&shared(20, E::bv_const(1, 64)), None, MAX_QUERY_NODES),
        ReadOnlyTargetError::Budget("logical expression work"),
    );
    assert_eq!(
        bounded_sum([MAX_TOTAL_QUERY_NODES - 1, 1], MAX_TOTAL_QUERY_NODES).unwrap(),
        MAX_TOTAL_QUERY_NODES
    );
    rejected(
        bounded_sum([MAX_TOTAL_QUERY_NODES, 1], MAX_TOTAL_QUERY_NODES),
        ReadOnlyTargetError::Budget("logical expression work"),
    );
    rejected(
        bounded_sum([usize::MAX, 1], usize::MAX),
        ReadOnlyTargetError::Budget("logical expression work"),
    );
}

#[test]
fn fork_budget_includes_new_condition_guards_before_cloning() {
    let old_state_nodes = 7 * 16_383 + 12 + 1;
    assert!(2 * old_state_nodes < MAX_STATE_NODES);
    let next_guard_nodes = 1 + (16_383 + 2) + 2;
    assert!(next_guard_nodes < MAX_TERM_NODES);
    assert!(2 * (old_state_nodes - 1 + next_guard_nodes) > MAX_STATE_NODES);

    let branch = |condition| {
        let mut steps = large_registers(7);
        let taken = steps.len() + 2;
        steps.push(Step::Branch { condition, taken });
        steps.extend([Step::Return, Step::Return]);
        retain_before_each_return(steps, 7)
    };
    assert_eq!(
        observe(&branch(E::BoolConst(true)), &inputs())
            .unwrap()
            .returns
            .len(),
        2
    );
    rejected(
        observe(&branch(register(0).eq_expr(E::bv_const(0, 64))), &inputs()),
        ReadOnlyTargetError::Budget("logical expression work"),
    );
}

#[test]
fn fork_budget_includes_already_held_pending_environments() {
    // Pair-local accounting admits both runs; only the held environments
    // distinguish four nested forks from five. Both stay far below 64 paths.
    let per_state = 3 * 16_383 + 12 + 16;
    assert!(5 * per_state < MAX_STATE_NODES);
    assert!(6 * per_state > MAX_STATE_NODES);
    let admitted = observe(
        &retain_before_each_return(same_successor_forks(4, large_registers(3)), 3),
        &inputs(),
    )
    .unwrap();
    assert_eq!(admitted.returns.len(), 16);
    rejected(
        observe(
            &retain_before_each_return(same_successor_forks(5, large_registers(3)), 3),
            &inputs(),
        ),
        ReadOnlyTargetError::Budget("logical expression work"),
    );
}

#[test]
fn post_fork_register_growth_is_charged_with_held_sibling_before_compose() {
    // The eight future growth destinations are genuine one-node input
    // placeholders on the held sibling before the other arm overwrites them.
    let held_nodes = 7 * 16_383 + 8 + 12 + 4;
    // On the active growth successor those inputs die before their defining
    // copies. Each new destination therefore adds the complete large term.
    let active_nodes = 7 * 16_383 + 12 + 4;
    assert!(
        held_nodes + active_nodes < MAX_STATE_NODES,
        "the tiny fork itself fits"
    );
    assert!(
        held_nodes + active_nodes + 16_383 < MAX_STATE_NODES,
        "one new copy fits"
    );
    assert!(
        held_nodes + active_nodes + 2 * 16_383 > MAX_STATE_NODES,
        "two new copies exceed the aggregate"
    );
    let growth = |copies| {
        let mut steps = large_registers(7);
        let taken = steps.len() + copies + 2;
        steps.push(Step::Branch {
            condition: E::BoolConst(true),
            taken,
        });
        steps.extend((7..7 + copies).map(|i| scalar(i, register(0))));
        steps.extend([Step::Return, Step::Return]);
        retain_before_each_return(steps, 7 + copies)
    };
    // Constant-true control does not prune the other arm. Its active state
    // must still be checked against the ~114k-node pending taken sibling.
    assert_eq!(observe(&growth(1), &inputs()).unwrap().returns.len(), 2);
    rejected(
        observe(&growth(8), &inputs()),
        ReadOnlyTargetError::Budget("logical expression work"),
    );
}

#[test]
fn lexical_retirement_removes_only_the_old_phantom_environment_pressure() {
    let mut branch = large_registers(7);
    let taken = branch.len() + 2;
    branch.push(Step::Branch {
        condition: register(0).eq_expr(E::bv_const(0, 64)),
        taken,
    });
    branch.extend([Step::Return, Step::Return]);
    let branched = observe(&branch, &inputs()).unwrap();
    assert_eq!(branched.returns.len(), 2);

    let pending = observe(&same_successor_forks(5, large_registers(3)), &inputs()).unwrap();
    assert_eq!(pending.returns.len(), 32);

    let mut growth = large_registers(7);
    let taken = growth.len() + 10;
    growth.push(Step::Branch {
        condition: E::BoolConst(true),
        taken,
    });
    growth.extend((7..15).map(|i| scalar(i, register(0))));
    growth.extend([Step::Return, Step::Return]);
    let grown = observe(&growth, &inputs()).unwrap();
    assert_eq!(grown.returns.len(), 2);
    for input in [0, 1, u64::MAX] {
        let expected = input.wrapping_shl(13);
        assert_eq!(selected(&branched, input), expected);
        assert_eq!(selected(&pending, input), expected);
        assert_eq!(selected(&grown, input), expected);
    }
}

#[test]
fn retired_register_and_flag_slots_never_fall_back_to_stale_or_zero_terms() {
    let mut before = state();
    before.x[0] = None;
    rejected(
        compose(&register(0), &before),
        ReadOnlyTargetError::Control("read of retired architectural slot"),
    );
    before.flags[0] = None;
    rejected(
        compose(&flags().n, &before),
        ReadOnlyTargetError::Control("read of retired architectural slot"),
    );
    assert_eq!(
        compose(&register(1), &before).unwrap().expr,
        E::var("entry_x1", 64),
        "unretired slots remain exact"
    );
}

#[test]
fn paths_reads_steps_and_load_expansion_have_connected_boundaries() {
    assert_eq!(
        observe(&same_successor_forks(6, vec![]), &inputs())
            .unwrap()
            .returns
            .len(),
        MAX_PATHS
    );
    rejected(
        observe(&same_successor_forks(7, vec![]), &inputs()),
        ReadOnlyTargetError::Budget("target execution paths"),
    );
    let loads = |count| {
        let mut steps = (0..count)
            .map(|_| Step::Load {
                destination: 31,
                address: register(0),
                alignment: 8,
            })
            .collect::<Vec<_>>();
        steps.push(Step::Return);
        steps
    };
    let observation = observe(&loads(MAX_READS), &inputs()).unwrap();
    assert_eq!(observation.reads.len(), MAX_READS);
    assert_eq!(
        selected(&observation, 0x1000),
        0x1000,
        "all loads are discarded, not erased"
    );
    rejected(
        observe(&loads(MAX_READS + 1), &inputs()),
        ReadOnlyTargetError::Budget("target read demands"),
    );
    let mut steps = (0..MAX_STEPS - 1).map(|_| Step::Inert).collect::<Vec<_>>();
    steps.push(Step::Return);
    assert!(validate(&steps).is_ok());
    steps.insert(0, Step::Inert);
    rejected(
        validate(&steps),
        ReadOnlyTargetError::Budget("endpoint steps"),
    );
    rejected(validate(&[]), ReadOnlyTargetError::Budget("endpoint steps"));

    let load_expansion = |depth| {
        vec![
            scalar(0, shared(depth, register(0))),
            Step::Load {
                destination: 31,
                address: register(0),
                alignment: 8,
            },
            Step::Return,
        ]
    };
    assert_eq!(
        observe(&load_expansion(10), &inputs()).unwrap().reads.len(),
        1
    );
    rejected(
        observe(&load_expansion(11), &inputs()),
        ReadOnlyTargetError::Budget("logical expression work"),
    );
}

#[test]
fn dead_discarded_and_constant_false_loads_still_record_demands() {
    let steps = [
        Step::Branch {
            condition: E::BoolConst(true),
            taken: 3,
        },
        Step::Load {
            destination: 31,
            address: register(0),
            alignment: 8,
        },
        Step::Return,
        Step::Return,
    ];
    let observation = observe(&steps, &inputs()).unwrap();
    assert_eq!(observation.returns.len(), 2);
    assert_eq!(observation.reads.len(), 1);
    let read = &observation.reads[0];
    assert_eq!(read.step, 1);
    assert_eq!(read.alignment, 8);
    assert!(
        !read
            .guard
            .expr
            .try_eval(&environment(0x1000))
            .unwrap()
            .as_bool()
    );
    assert_eq!(
        read.address
            .expr
            .try_eval(&environment(0x1000))
            .unwrap()
            .as_u64(),
        0x1000
    );
    assert_eq!(selected(&observation, 0x1000), 0x1000);

    let overwritten = [
        Step::Load {
            destination: 1,
            address: register(0),
            alignment: 8,
        },
        scalar(1, E::bv_const(0, 64)),
        Step::Return,
    ];
    let observation = observe(&overwritten, &inputs()).unwrap();
    assert_eq!(
        observation.reads.len(),
        1,
        "dead result does not erase its read"
    );
    assert_eq!(selected(&observation, 0x1000), 0x1000);
}

#[test]
fn register_and_flags_aliases_read_before_write_and_latest_flags_win() {
    let produce = || Step::Scalar {
        destination: Some(0),
        value: register(0).bvadd(E::bv_const(1, 64)),
        flags: Some(Box::new(NzcvFlags {
            n: register(0).eq_expr(E::bv_const(2, 64)),
            z: register(0).eq_expr(E::bv_const(3, 64)),
            c: E::BoolConst(false),
            v: E::BoolConst(false),
        })),
    };
    let suffix = |mut steps: Vec<Step>| {
        let taken = steps.len() + 3;
        steps.push(Step::Branch {
            condition: flags().n,
            taken,
        });
        steps.push(scalar(0, E::bv_const(50, 64)));
        steps.push(Step::Return);
        steps.push(scalar(0, E::bv_const(60, 64)));
        steps.push(Step::Return);
        steps
    };
    let observation = observe(&suffix(vec![produce()]), &inputs()).unwrap();
    assert_eq!(
        selected(&observation, 2),
        60,
        "N reads old x0=2, not new x0=3"
    );
    assert_eq!(selected(&observation, 1), 50, "N must not read new x0=2");
    let replace_flags = Step::Scalar {
        destination: None,
        value: E::bv_const(0, 64),
        flags: Some(Box::new(NzcvFlags {
            n: E::BoolConst(false),
            z: E::BoolConst(false),
            c: E::BoolConst(false),
            v: E::BoolConst(false),
        })),
    };
    let observation = observe(&suffix(vec![produce(), replace_flags]), &inputs()).unwrap();
    assert_eq!(
        selected(&observation, 2),
        50,
        "latest complete NZCV replaces the old producer"
    );

    let observation = observe(
        &[
            Step::Load {
                destination: 0,
                address: register(0),
                alignment: 8,
            },
            Step::Return,
        ],
        &inputs(),
    )
    .unwrap();
    assert_eq!(observation.reads[0].address.expr, E::var("abi_x0", 64));
    assert_eq!(
        observation.returns[0].1.expr,
        encode_load_le(
            &E::uf("entry_memory", vec![], memory_sort()),
            &E::var("abi_x0", 64),
            8
        )
    );
}

#[test]
fn unknown_template_inputs_and_ufs_refuse_even_when_discarded() {
    for value in [
        register(31),
        E::var("x01", 64),
        E::var("sp", 64),
        E::var("abi_x0", 64),
    ] {
        rejected(
            observe(
                &[
                    Step::Scalar {
                        destination: None,
                        value,
                        flags: None,
                    },
                    Step::Return,
                ],
                &inputs(),
            ),
            ReadOnlyTargetError::Control("unknown architectural template input"),
        );
    }
    rejected(
        observe(
            &[scalar(0, E::var("x0", 32).zero_ext(32)), Step::Return],
            &inputs(),
        ),
        ReadOnlyTargetError::Control("wrong-sort architectural template input"),
    );
    rejected(
        observe(
            &[
                scalar(0, E::uf("unexpected", vec![], SmtSort::BitVec(64))),
                Step::Return,
            ],
            &inputs(),
        ),
        ReadOnlyTargetError::Control("unknown architectural template UF"),
    );
    for condition in [
        E::uf("flag_n", vec![E::bv_const(0, 64)], SmtSort::Bool),
        E::uf("unexpected", vec![], SmtSort::Bool),
    ] {
        rejected(
            observe(
                &[
                    Step::Branch {
                        condition,
                        taken: 2,
                    },
                    Step::Return,
                    Step::Return,
                ],
                &inputs(),
            ),
            ReadOnlyTargetError::Control("unknown architectural template UF"),
        );
    }
}

#[test]
fn all_constant_arms_are_checked_and_control_cannot_escape_or_cycle() {
    let valid = [
        Step::Branch {
            condition: E::BoolConst(true),
            taken: 3,
        },
        scalar(0, E::bv_const(11, 64)),
        Step::Return,
        scalar(0, E::bv_const(12, 64)),
        Step::Return,
    ];
    let observation = observe(&valid, &inputs()).unwrap();
    assert_eq!(observation.returns.len(), 2);
    assert_eq!(selected(&observation, 0), 12);
    let invalid_untaken = [
        Step::Branch {
            condition: E::BoolConst(true),
            taken: 3,
        },
        scalar(0, E::var("unknown", 64)),
        Step::Return,
        scalar(0, E::bv_const(12, 64)),
        Step::Return,
    ];
    rejected(
        observe(&invalid_untaken, &inputs()),
        ReadOnlyTargetError::Control("unknown architectural template input"),
    );
    for (steps, reason) in [
        (
            vec![Step::Return, Step::Return],
            "unreachable/uninspected instruction",
        ),
        (
            vec![Step::Jump(2), Step::Return, Step::Return],
            "unreachable/uninspected instruction",
        ),
        (vec![Step::Jump(0)], "cyclic target control"),
        (
            vec![
                Step::Branch {
                    condition: E::BoolConst(false),
                    taken: 2,
                },
                Step::Jump(0),
                Step::Return,
            ],
            "cyclic target control",
        ),
        (vec![Step::Jump(1)], "edge leaves endpoint"),
        (
            vec![
                Step::Branch {
                    condition: E::BoolConst(true),
                    taken: 2,
                },
                Step::Return,
            ],
            "edge leaves endpoint",
        ),
        (vec![Step::Inert], "edge leaves endpoint"),
    ] {
        rejected(validate(&steps), ReadOnlyTargetError::Control(reason));
    }
}

#[test]
fn writes_loads_conditions_and_flag_sorts_are_fail_closed() {
    for (step, reason) in [
        (
            scalar(18, E::bv_const(0, 64)),
            "unsupported destination or effect sort",
        ),
        (
            scalar(0, E::bv_const(0, 32)),
            "unsupported destination or effect sort",
        ),
        (
            Step::Scalar {
                destination: None,
                value: E::bv_const(0, 64),
                flags: Some(Box::new(NzcvFlags {
                    n: E::bv_const(0, 1),
                    z: E::BoolConst(false),
                    c: E::BoolConst(false),
                    v: E::BoolConst(false),
                })),
            },
            "unsupported destination or effect sort",
        ),
        (
            Step::Branch {
                condition: E::bv_const(0, 1),
                taken: 1,
            },
            "branch condition is not Boolean",
        ),
        (
            Step::Load {
                destination: 18,
                address: register(0),
                alignment: 8,
            },
            "unsupported load effect",
        ),
        (
            Step::Load {
                destination: 0,
                address: E::BoolConst(false),
                alignment: 8,
            },
            "unsupported load effect",
        ),
        (
            Step::Load {
                destination: 0,
                address: register(0),
                alignment: 0,
            },
            "unsupported load effect",
        ),
        (
            Step::Load {
                destination: 0,
                address: register(0),
                alignment: 3,
            },
            "unsupported load effect",
        ),
        (
            Step::Load {
                destination: 0,
                address: register(0),
                alignment: 16,
            },
            "unsupported load effect",
        ),
    ] {
        rejected(
            validate(&[step, Step::Return]),
            ReadOnlyTargetError::Control(reason),
        );
    }
    // Destination 17 is the exact last admitted caller-scratch register; a
    // discarded load has its own admission but still retains the demand.
    assert!(
        validate(&[
            scalar(17, E::bv_const(0, 64)),
            Step::Load {
                destination: 31,
                address: register(0),
                alignment: 1
            },
            Step::Return
        ])
        .is_ok()
    );
}
#[test]
#[cfg(target_pointer_width = "64")]
fn optional_flags_do_not_expand_every_observation_step() {
    use std::mem::size_of;

    assert_eq!(size_of::<Option<Box<NzcvFlags>>>(), size_of::<usize>());
    assert!(size_of::<Step>() <= 2 * size_of::<E>());
    println!(
        "A64_READ_ONLY_STEP_STORAGE step_bytes={} expression_bytes={} optional_flags_bytes={} physical_rss_measurement=none",
        size_of::<Step>(),
        size_of::<E>(),
        size_of::<Option<Box<NzcvFlags>>>()
    );
}
