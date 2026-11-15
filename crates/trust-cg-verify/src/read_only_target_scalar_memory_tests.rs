// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Finite controls for the existing target current-memory observer. Expanding
//! exact semantic equations here is not solver replay, machine verification,
//! native execution, caller permission or initialized-memory authority.

use super::*;
use crate::memory_proofs::encode_store_le;
use crate::smt::{EvalEnv, EvalResult};
use std::collections::HashSet;
use std::convert::Infallible;

const A: u64 = 0x1000;
const B: u64 = 0x3000;
const ORIGINAL: u64 = 0x8877_6655_4433_2211;
const OTHER: u64 = 0xffee_ddcc_bbaa_0099;
const REPLACEMENT: u64 = 0xfeed_beef_0123_4567;

fn scalar(destination: usize, value: E) -> Step {
    Step::Scalar {
        destination: Some(destination),
        value,
        flags: None,
    }
}

fn load(destination: usize, address: E, byte_width: u32) -> Step {
    Step::MemoryLoad {
        destination,
        address,
        byte_width,
        alignment: 1,
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

fn pair(destinations: [usize; 2], address: E, byte_width: u32) -> Step {
    Step::LoadPair {
        destinations,
        address: Box::new(address),
        byte_width,
        alignment: 1,
    }
}

fn inputs(arity: usize) -> Vec<(String, u32)> {
    let mut inputs = (0..arity)
        .map(|i| (format!("abi_x{i}"), 64))
        .collect::<Vec<_>>();
    inputs.push(("observe".into(), 64));
    inputs
}

fn observe(steps: &[Step], arity: usize, stage: Stage) -> Observations {
    observe_profile_at(steps, &inputs(arity), arity, Some(stage), &mut 0)
        .expect("bounded scalar-memory observation")
}

fn prefix(stage: Stage) -> &'static str {
    match stage {
        Stage::Machine => "scalar_memory_machine_d",
        Stage::Words => "scalar_memory_words_d",
        _ => panic!("these are target-stage controls"),
    }
}

fn environment(arguments: &[u64]) -> EvalEnv {
    let mut env = EvalEnv::default();
    for (i, value) in arguments.iter().enumerate() {
        env.insert(format!("abi_x{i}"), *value);
    }
    for i in 0..31 {
        env.insert(format!("entry_x{i}"), 0x5000 + i as u64);
    }
    for flag in ["entry_n", "entry_z", "entry_c", "entry_v"] {
        env.insert(flag.into(), 0);
    }
    env.insert("observe".into(), A);
    env
}

fn finite_memory(words: &[(u64, u64, u32)]) -> E {
    // This is one concrete array instance with heterogeneous explicit cells,
    // never a premise restricting the production arbitrary entry array.
    words.iter().fold(
        E::const_array(SmtSort::BitVec(64), E::bv_const(0xa5, 8)),
        |memory, &(address, value, bytes)| {
            encode_store_le(
                &memory,
                &E::bv_const(address, 64),
                &E::bv_const(value, bytes * 8),
                bytes,
            )
        },
    )
}

pub(crate) type Substitutions = HashMap<String, (SmtSort, E)>;

fn substitute(expression: &E, substitutions: &Substitutions) -> E {
    expression
        .try_rewrite_dag::<Infallible>(&mut |node| {
            Ok(match node {
                E::UF {
                    name,
                    args,
                    ret_sort,
                } if args.is_empty() => substitutions.get(name).map(|(sort, value)| {
                    assert_eq!(ret_sort, sort, "concrete substitution retains exact sort");
                    value.clone()
                }),
                _ => None,
            })
        })
        .unwrap()
        .unwrap_or_else(|| expression.clone())
}

fn expand(observation: &Observations, memory: &E, stage: Stage) -> Substitutions {
    for (index, equation) in observation.definitions.iter().enumerate() {
        let E::Eq { lhs, .. } = equation else {
            panic!("exact semantic equality");
        };
        let E::UF { name, .. } = lhs.as_ref() else {
            panic!("defined occurrence");
        };
        assert_eq!(name, &format!("{}{index}", prefix(stage)));
    }
    expand_equations(&observation.definitions, memory)
}

pub(crate) fn expand_equations(equations: &[E], memory: &E) -> Substitutions {
    let mut substitutions =
        HashMap::from([("entry_memory".into(), (memory_sort(), memory.clone()))]);
    for equation in equations {
        let E::Eq { lhs, rhs } = equation else {
            panic!("exact semantic equality, not an assumed caller premise");
        };
        let E::UF {
            name,
            args,
            ret_sort,
        } = lhs.as_ref()
        else {
            panic!("defined zero-argument occurrence");
        };
        assert!(args.is_empty());
        assert!(
            !substitutions.contains_key(name),
            "fresh immutable occurrence"
        );
        let expanded = substitute(rhs, &substitutions);
        assert_eq!(expanded.sort(), *ret_sort);
        let mut pending = vec![&expanded];
        let mut seen = HashSet::new();
        while let Some(node) = pending.pop() {
            if seen.insert(node as *const E) {
                assert!(
                    !matches!(node, E::UF { .. }),
                    "only past same-stage equations and entry memory may occur"
                );
                node.for_each_child(&mut |child| pending.push(child));
            }
        }
        substitutions.insert(name.clone(), (ret_sort.clone(), expanded));
    }
    substitutions
}

pub(crate) fn evaluate(expression: &E, substitutions: &Substitutions, env: &EvalEnv) -> EvalResult {
    substitute(expression, substitutions)
        .try_eval(env)
        .expect("finite exact array/bitvector instance")
}

fn selected(observation: &Observations, substitutions: &Substitutions, env: &EvalEnv) -> usize {
    assert_eq!(observation.returns.len(), observation.memories.len());
    let mut active = observation
        .returns
        .iter()
        .enumerate()
        .filter(|(_, (guard, _))| evaluate(&guard.expr, substitutions, env).as_bool());
    let index = active.next().expect("one selected complete path").0;
    assert!(active.next().is_none(), "mutually exclusive return guards");
    index
}

fn status(observation: &Observations, substitutions: &Substitutions, env: &EvalEnv) -> u64 {
    evaluate(
        &observation.returns[selected(observation, substitutions, env)]
            .1
            .expr,
        substitutions,
        env,
    )
    .as_u64()
}

fn byte(
    observation: &Observations,
    substitutions: &Substitutions,
    env: &EvalEnv,
    address: u64,
) -> u64 {
    let memory = &observation.memories[selected(observation, substitutions, env)].expr;
    evaluate(
        &E::select(memory.clone(), E::bv_const(address, 64)),
        substitutions,
        env,
    )
    .as_u64()
}

#[test]
fn store_then_alias_load_uses_current_memory_not_entry_memory() {
    let steps = [
        store(register(0), register(2), 8),
        load(0, register(1), 8),
        Step::Return,
    ];
    let memory = finite_memory(&[(A, ORIGINAL, 8), (B, OTHER, 8)]);
    for stage in [Stage::Machine, Stage::Words] {
        let observed = observe(&steps, 3, stage);
        assert_eq!(observed.writes.len(), 1);
        assert_eq!(observed.reads.len(), 1);
        assert_eq!((observed.writes[0].step, observed.reads[0].step), (0, 1));
        let substitutions = expand(&observed, &memory, stage);
        for output in [A, B] {
            let env = environment(&[A, output, REPLACEMENT]);
            let expected = if output == A { REPLACEMENT } else { OTHER };
            assert_eq!(status(&observed, &substitutions, &env), expected);
            let stale = encode_load_le(&memory, &E::bv_const(output, 64), 8)
                .try_eval(&env)
                .unwrap()
                .as_u64();
            if output == A {
                assert_eq!(stale, ORIGINAL);
                assert_ne!(expected, stale, "the alias control must expose stale loads");
            } else {
                assert_eq!(stale, expected);
            }
            for offset in 0..8 {
                assert_eq!(
                    byte(&observed, &substitutions, &env, A + offset),
                    (REPLACEMENT >> (8 * offset)) & 0xff
                );
                assert_eq!(
                    byte(&observed, &substitutions, &env, B + offset),
                    (OTHER >> (8 * offset)) & 0xff
                );
            }
        }
    }
}

#[test]
fn four_byte_store_preserves_neighbors_and_exposes_wide_store_mutant() {
    let memory = finite_memory(&[(A, ORIGINAL, 8)]);
    let incoming = 0xffff_eeee_a1b2_c3d4;
    let env = environment(&[A, A, incoming]);
    for stage in [Stage::Machine, Stage::Words] {
        let observed = observe(
            &[
                store(register(0), register(2).extract(31, 0), 4),
                load(0, register(1), 8),
                Step::Return,
            ],
            3,
            stage,
        );
        let substitutions = expand(&observed, &memory, stage);
        assert_eq!(observed.writes[0].byte_width, 4);
        assert_eq!(
            status(&observed, &substitutions, &env),
            0x8877_6655_a1b2_c3d4
        );
        for offset in 0..8 {
            let word = if offset < 4 { incoming } else { ORIGINAL };
            assert_eq!(
                byte(&observed, &substitutions, &env, A + offset),
                (word >> (8 * offset)) & 0xff
            );
        }
        for neighbor in [A - 1, A + 8] {
            assert_eq!(byte(&observed, &substitutions, &env, neighbor), 0xa5);
        }
        let wide = observe(
            &[
                store(register(0), register(2), 8),
                load(0, register(1), 8),
                Step::Return,
            ],
            3,
            stage,
        );
        let wide_substitutions = expand(&wide, &memory, stage);
        assert_eq!(status(&wide, &wide_substitutions, &env), incoming);
        assert_ne!(
            byte(&observed, &substitutions, &env, A + 4),
            byte(&wide, &wide_substitutions, &env, A + 4)
        );
    }
}

#[test]
fn word_load_zeroes_old_x_high_bits_and_returns_full_x0_status() {
    let memory = finite_memory(&[(A, ORIGINAL, 8)]);
    let env = environment(&[u64::MAX, A]);
    for stage in [Stage::Machine, Stage::Words] {
        let narrow = observe(&[load(0, register(1), 4), Step::Return], 2, stage);
        let substitutions = expand(&narrow, &memory, stage);
        assert_eq!(narrow.returns[0].1.expr.sort(), SmtSort::BitVec(64));
        assert_eq!(
            status(&narrow, &substitutions, &env),
            ORIGINAL & 0xffff_ffff
        );
        assert_eq!(status(&narrow, &substitutions, &env) >> 32, 0);
        let wide = observe(&[load(0, register(1), 8), Step::Return], 2, stage);
        let wide_substitutions = expand(&wide, &memory, stage);
        assert_eq!(status(&wide, &wide_substitutions, &env), ORIGINAL);
        assert_ne!(status(&narrow, &substitutions, &env), ORIGINAL);
    }
}

#[test]
fn paired_loads_snapshot_base_before_both_writes_and_retain_every_lane() {
    for stage in [Stage::Machine, Stage::Words] {
        for width in [4, 8] {
            let (first, second): (u64, u64) = if width == 4 {
                (0xfedc_ba98, 0x8765_4321)
            } else {
                (ORIGINAL, OTHER)
            };
            let memory = finite_memory(&[
                (A, first, width),
                (A + u64::from(width), second, width),
                (first.wrapping_add(u64::from(width)), 1, width),
            ]);
            let observed = observe(
                &[
                    pair([0, 1], register(0), width),
                    scalar(0, register(0).bvadd(register(1))),
                    Step::Return,
                ],
                1,
                stage,
            );
            let substitutions = expand(&observed, &memory, stage);
            let env = environment(&[A]);
            assert_eq!(
                status(&observed, &substitutions, &env),
                first.wrapping_add(second)
            );
            assert_eq!(observed.reads.len(), 2);
            for (lane, read) in observed.reads.iter().enumerate() {
                assert_eq!(
                    (read.step, read.lane, read.byte_width, read.alignment),
                    (0, lane, width, 1)
                );
                assert_eq!(
                    evaluate(&read.address.expr, &substitutions, &env).as_u64(),
                    A + lane as u64 * u64::from(width)
                );
            }
            let discarded = observe(
                &[
                    pair([31, 1], register(0), width),
                    load(31, register(2), 4),
                    scalar(0, E::bv_const(0x1234_5678_0000_0001, 64)),
                    Step::Return,
                ],
                3,
                stage,
            );
            let discarded_substitutions = expand(&discarded, &memory, stage);
            let env = environment(&[A, 0, B]);
            assert_eq!(
                discarded.reads.len(),
                3,
                "dead/discarded loads still demand bytes"
            );
            assert_eq!(discarded.writes.len(), 0);
            assert_eq!((discarded.reads[0].step, discarded.reads[0].lane), (0, 0));
            assert_eq!((discarded.reads[1].step, discarded.reads[1].lane), (0, 1));
            assert_eq!((discarded.reads[2].step, discarded.reads[2].lane), (1, 0));
            assert_eq!(
                status(&discarded, &discarded_substitutions, &env),
                0x1234_5678_0000_0001
            );
            for read in &discarded.reads {
                assert!(evaluate(&read.guard.expr, &discarded_substitutions, &env).as_bool());
            }
        }
    }
}

#[test]
fn branch_memories_are_separate_restore_keeps_write_demands_and_status_high_bits() {
    let steps = [
        load(3, register(0), 8),
        Step::Branch {
            condition: register(2).eq_expr(E::bv_const(0, 64)),
            taken: 6,
        },
        store(register(0), E::bv_const(REPLACEMENT, 64), 8),
        store(register(0), register(3), 8),
        scalar(0, E::bv_const(0x1000_0000_0000_0001, 64)),
        Step::Return,
        store(register(1), E::bv_const(REPLACEMENT, 64), 8),
        scalar(0, E::bv_const(0x2000_0000_0000_0001, 64)),
        Step::Return,
    ];
    let memory = finite_memory(&[(A, ORIGINAL, 8), (B, OTHER, 8)]);
    for stage in [Stage::Machine, Stage::Words] {
        let observed = observe(&steps, 3, stage);
        assert_eq!(observed.returns.len(), 2);
        assert_eq!(observed.memories.len(), 2);
        assert_eq!(observed.reads.len(), 1);
        assert_eq!(
            observed.writes.len(),
            3,
            "a restored write is still an access"
        );
        let substitutions = expand(&observed, &memory, stage);
        for branch in [0, 1] {
            let env = environment(&[A, B, branch]);
            let expected_status = if branch == 0 {
                0x2000_0000_0000_0001
            } else {
                0x1000_0000_0000_0001
            };
            assert_eq!(status(&observed, &substitutions, &env), expected_status);
            let active_writes = observed
                .writes
                .iter()
                .filter(|write| evaluate(&write.guard.expr, &substitutions, &env).as_bool())
                .collect::<Vec<_>>();
            assert_eq!(active_writes.len(), if branch == 0 { 1 } else { 2 });
            for write in active_writes {
                assert_eq!(
                    evaluate(&write.address.expr, &substitutions, &env).as_u64(),
                    if branch == 0 { B } else { A }
                );
            }
            for offset in 0..8 {
                assert_eq!(
                    byte(&observed, &substitutions, &env, A + offset),
                    (ORIGINAL >> (8 * offset)) & 0xff
                );
                let expected = if branch == 0 { REPLACEMENT } else { OTHER };
                assert_eq!(
                    byte(&observed, &substitutions, &env, B + offset),
                    (expected >> (8 * offset)) & 0xff
                );
            }
        }
    }
}

#[test]
fn observer_input_is_not_a_fifth_architectural_argument() {
    let steps = [scalar(0, register(4)), Step::Return];
    let memory = finite_memory(&[]);
    for stage in [Stage::Machine, Stage::Words] {
        let observed = observe(&steps, 4, stage);
        let substitutions = expand(&observed, &memory, stage);
        let mut env = environment(&[A, B, 3, 4]);
        env.insert("entry_x4".into(), 0x1234_5678_9876_5432);
        for observer in [0, u64::MAX, A] {
            env.insert("observe".into(), observer);
            assert_eq!(
                status(&observed, &substitutions, &env),
                0x1234_5678_9876_5432
            );
        }
        for tamper in 0..4 {
            let mut bad = inputs(4);
            match tamper {
                0 => bad[0].0 = "entry_x0".into(),
                1 => bad[1].1 = 32,
                2 => bad.swap(1, 2),
                _ => {
                    bad.remove(3);
                }
            }
            assert_eq!(
                observe_profile_at(&steps, &bad, 4, Some(stage), &mut 0).err(),
                Some(ReadOnlyTargetError::Control("scalar-memory ABI inputs"))
            );
        }
    }
}

#[test]
fn unknown_and_cross_stage_templates_refuse_without_definition_credit() {
    for value in [
        E::var("observe", 64),
        E::uf("scalar_memory_machine_d0", vec![], SmtSort::BitVec(64)),
        E::uf("scalar_memory_words_d0", vec![], SmtSort::BitVec(64)),
        E::uf("entry_memory", vec![], SmtSort::BitVec(64)),
    ] {
        for stage in [Stage::Machine, Stage::Words] {
            let steps = [
                Step::Branch {
                    condition: E::BoolConst(true),
                    taken: 3,
                },
                store(register(0), value.clone(), 8),
                Step::Return,
                Step::Return,
            ];
            assert!(matches!(
                observe_profile_at(&steps, &inputs(1), 1, Some(stage), &mut 0),
                Err(ReadOnlyTargetError::Control(_))
            ));
        }
    }
}

fn shared(depth: usize, mut expression: E) -> E {
    for _ in 0..depth {
        expression = expression.clone().bvadd(expression);
    }
    expression
}

fn direct_state(address: E) -> State {
    let nodes = expression_nodes(&address, None, MAX_TERM_NODES).unwrap();
    let mut x = std::array::from_fn(|_| None);
    x[0] = Some(Term {
        expr: address,
        nodes,
    });
    State {
        pc: 0,
        x,
        flags: std::array::from_fn(|_| None),
        guard: Term::leaf(E::BoolConst(true)),
        memory: Some(Arc::new(Term::leaf(E::uf(
            "entry_memory",
            vec![],
            memory_sort(),
        )))),
    }
}

fn empty_observations() -> Observations {
    Observations {
        returns: vec![],
        vector_returns: vec![],
        reads: vec![],
        writes: vec![],
        memories: vec![],
        definitions: vec![],
    }
}

fn definitions(stage: Stage) -> Definitions {
    Definitions::new(
        stage,
        1,
        Limits {
            rhs_nodes: MAX_TERM_NODES,
            collection_nodes: MAX_STATE_NODES,
            occurrences: MAX_STEPS * MAX_PATHS,
        },
    )
}

#[test]
fn term_expansion_refuses_before_definitions_or_accesses_are_retained() {
    for stage in [Stage::Machine, Stage::Words] {
        for kind in 0..3 {
            let step = match kind {
                0 => load(31, register(0), 8),
                1 => store(register(0), E::bv_const(REPLACEMENT, 64), 8),
                _ => pair([31, 1], register(0), 8),
            };
            let mut small = direct_state(shared(10, E::var("abi_x0", 64)));
            let mut small_observed = empty_observations();
            let mut small_definitions = definitions(stage);
            memory::observe(
                &step,
                &mut small,
                &[],
                &mut small_observed,
                &mut small_definitions,
            )
            .unwrap();
            assert_eq!(
                small_observed.reads.len(),
                if kind == 0 {
                    1
                } else if kind == 2 {
                    2
                } else {
                    0
                }
            );
            assert_eq!(small_observed.writes.len(), usize::from(kind == 1));

            let mut large = direct_state(shared(11, E::var("abi_x0", 64)));
            let before = large.clone();
            let mut observed = empty_observations();
            let mut definitions = definitions(stage);
            let expected = if kind == 1 {
                "current-memory store expansion"
            } else {
                "current-memory load expansion"
            };
            assert_eq!(
                memory::observe(&step, &mut large, &[], &mut observed, &mut definitions).err(),
                Some(ReadOnlyTargetError::Budget(expected))
            );
            assert!(observed.reads.is_empty() && observed.writes.is_empty());
            assert!(definitions.equations.is_empty() && definitions.sorts.is_empty());
            assert_eq!(definitions.nodes, 0);
            assert_eq!(
                large.memory.as_ref().unwrap().expr,
                before.memory.as_ref().unwrap().expr
            );
            assert_eq!(
                large.x[0].as_ref().unwrap().nodes,
                before.x[0].as_ref().unwrap().nodes
            );
            assert!(large.x[1].is_none());
        }
    }
}

#[test]
fn paired_second_lane_limit_refuses_before_first_lane_binding_or_demand() {
    let mut address = shared(10, E::var("abi_x0", 64));
    for depth in [9, 8, 7, 6, 5, 4, 3, 1, 1] {
        address = address.bvadd(shared(depth, E::var("abi_x0", 64)));
    }
    assert_eq!(
        expression_nodes(&address, None, MAX_TERM_NODES).unwrap(),
        4087
    );
    for stage in [Stage::Machine, Stage::Words] {
        let mut first = direct_state(address.clone());
        let mut first_observed = empty_observations();
        let mut first_definitions = definitions(stage);
        memory::observe(
            &load(1, register(0), 8),
            &mut first,
            &[],
            &mut first_observed,
            &mut first_definitions,
        )
        .unwrap();
        assert_eq!(first_observed.reads.len(), 1);
        assert_eq!(first_definitions.equations.len(), 1);
        let mut both = direct_state(address.clone());
        let mut both_observed = empty_observations();
        let mut both_definitions = definitions(stage);
        assert_eq!(
            memory::observe(
                &pair([1, 2], register(0), 8),
                &mut both,
                &[],
                &mut both_observed,
                &mut both_definitions
            )
            .err(),
            Some(ReadOnlyTargetError::Budget("current-memory load expansion"))
        );
        assert!(both_observed.reads.is_empty());
        assert!(both_definitions.equations.is_empty() && both_definitions.sorts.is_empty());
        assert_eq!(both_definitions.nodes, 0);
        assert!(both.x[1].is_none() && both.x[2].is_none());
    }
}

#[test]
fn paired_occurrence_limit_refuses_atomically_with_one_real_slot_remaining() {
    let capacity = MAX_STEPS * MAX_PATHS;
    for stage in [Stage::Machine, Stage::Words] {
        let mut definitions = definitions(stage);
        for _ in 0..capacity - 1 {
            definitions
                .bind(E::var("abi_x0", 64), 1, SmtSort::BitVec(64))
                .unwrap_or_else(|_| panic!("actual occurrence boundary must be reachable"));
        }
        assert_eq!(definitions.equations.len(), capacity - 1);
        assert_eq!(definitions.nodes, 3 * (capacity - 1));
        assert!(definitions.preflight_occurrences(1).is_ok());
        assert!(matches!(
            definitions.preflight_occurrences(2),
            Err(DefinitionError::Budget(
                "scalar-memory definition occurrences"
            ))
        ));
        let equations = definitions.equations.clone();
        let sorts = definitions.sorts.clone();
        let nodes = definitions.nodes;
        let mut state = direct_state(E::var("abi_x0", 64));
        let before = state.clone();
        let mut observed = empty_observations();
        assert_eq!(
            memory::observe(
                &pair([0, 1], register(0), 8),
                &mut state,
                &[],
                &mut observed,
                &mut definitions,
            )
            .err(),
            Some(ReadOnlyTargetError::Budget(
                "scalar-memory definition occurrences"
            ))
        );
        assert_eq!(definitions.equations, equations);
        assert_eq!(definitions.sorts, sorts);
        assert_eq!(definitions.nodes, nodes);
        assert!(observed.reads.is_empty() && observed.writes.is_empty());
        assert!(observed.returns.is_empty() && observed.memories.is_empty());
        assert!(observed.definitions.is_empty());
        assert_eq!(state.pc, before.pc);
        for (actual, expected) in state
            .x
            .iter()
            .chain(&state.flags)
            .zip(before.x.iter().chain(&before.flags))
        {
            assert_eq!(
                actual.as_ref().map(|term| (&term.expr, term.nodes)),
                expected.as_ref().map(|term| (&term.expr, term.nodes))
            );
        }
        assert_eq!(state.guard.expr, before.guard.expr);
        assert_eq!(state.guard.nodes, before.guard.nodes);
        assert_eq!(
            state.memory.as_ref().map(|term| (&term.expr, term.nodes)),
            before.memory.as_ref().map(|term| (&term.expr, term.nodes))
        );

        // The exact same collection and state still have their one slot. A
        // one-result load must consume it successfully after the pair refuses.
        memory::observe(
            &load(0, register(0), 8),
            &mut state,
            &[],
            &mut observed,
            &mut definitions,
        )
        .unwrap();
        assert_eq!(definitions.equations.len(), capacity);
        assert_eq!(&definitions.equations[..capacity - 1], &equations);
        assert_eq!(observed.reads.len(), 1);
        assert!(observed.writes.is_empty());
        assert!(matches!(
            definitions.preflight_occurrences(1),
            Err(DefinitionError::Budget(
                "scalar-memory definition occurrences"
            ))
        ));
    }
}

#[test]
fn access_inventory_limits_preserve_discarded_reads_and_restored_writes() {
    for stage in [Stage::Machine, Stage::Words] {
        let mut pairs = (0..MAX_READS / 2)
            .map(|_| pair([31, 1], register(0), 8))
            .collect::<Vec<_>>();
        pairs.push(Step::Return);
        assert_eq!(observe(&pairs, 1, stage).reads.len(), MAX_READS);
        pairs.insert(0, pair([31, 1], register(0), 8));
        assert_eq!(
            observe_profile_at(&pairs, &inputs(1), 1, Some(stage), &mut 0).err(),
            Some(ReadOnlyTargetError::Budget("target paired read demands"))
        );
        let mut stores = (0..MAX_READS)
            .map(|_| store(register(0), E::bv_const(7, 64), 8))
            .collect::<Vec<_>>();
        stores.push(Step::Return);
        assert_eq!(observe(&stores, 1, stage).writes.len(), MAX_READS);
        stores.insert(0, store(register(0), E::bv_const(7, 64), 8));
        assert_eq!(
            observe_profile_at(&stores, &inputs(1), 1, Some(stage), &mut 0).err(),
            Some(ReadOnlyTargetError::Budget("target write demands"))
        );
    }
}
