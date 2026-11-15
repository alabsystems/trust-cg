// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Namespace/sort controls for private semantic equations. Admission here
//! installs only an exact pending equation, never a proof or execution credit.

use super::*;

const STAGES: [Stage; 4] = [Stage::Core, Stage::Lir, Stage::Machine, Stage::Words];

fn builder(stage: Stage, arity: usize) -> Definitions {
    Definitions::new(
        stage,
        arity,
        Limits {
            rhs_nodes: 128,
            collection_nodes: 4096,
            occurrences: 128,
        },
    )
}

fn admitted(definitions: &mut Definitions, value: E, nodes: usize, sort: SmtSort) -> E {
    match definitions.bind(value, nodes, sort) {
        Ok(symbol) => symbol,
        Err(Error::Invalid(reason) | Error::Budget(reason)) => {
            panic!("unexpected private definition refusal: {reason}")
        }
    }
}

fn reject_without_mutation(definitions: &mut Definitions, value: E, nodes: usize, sort: SmtSort) {
    let equations = definitions.equations.clone();
    let sorts = definitions.sorts.clone();
    let before_nodes = definitions.nodes;
    assert!(matches!(
        definitions.bind(value, nodes, sort),
        Err(Error::Invalid(_))
    ));
    assert_eq!(definitions.equations, equations);
    assert_eq!(definitions.sorts, sorts);
    assert_eq!(definitions.nodes, before_nodes);
}

#[test]
fn canonical_numbered_bounds_partition_source_and_target_inputs() {
    for stage in STAGES {
        for arity in [0, 4, 8] {
            let mut definitions = builder(stage, arity);
            for index in 0..=32 {
                let abi_name = format!("abi_x{index}");
                let entry_name = format!("entry_x{index}");
                for (name, expected) in [
                    (abi_name, index < arity),
                    (entry_name, stage.target() && (arity..31).contains(&index)),
                ] {
                    assert_eq!(
                        definitions.input(&name, 64),
                        expected,
                        "{} arity={arity} input={name}",
                        stage.prefix()
                    );
                    if expected {
                        let value = E::var(&name, 64);
                        let symbol =
                            admitted(&mut definitions, value.clone(), 1, SmtSort::BitVec(64));
                        let E::Eq { lhs, rhs } = definitions.equations.last().unwrap() else {
                            panic!("exact defining equation required")
                        };
                        assert_eq!(lhs.as_ref(), &symbol);
                        assert_eq!(rhs.as_ref(), &value);
                    } else {
                        reject_without_mutation(
                            &mut definitions,
                            E::var(&name, 64),
                            1,
                            SmtSort::BitVec(64),
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn noncanonical_numeric_spellings_never_alias_a_canonical_input() {
    let huge = "9".repeat(512);
    for stage in STAGES {
        for arity in [0, 4, 8] {
            let mut definitions = builder(stage, arity);
            for prefix in ["abi_x", "entry_x"] {
                for suffix in [
                    "",
                    "00",
                    "01",
                    "04",
                    "+4",
                    "-4",
                    "4 ",
                    "4\n",
                    " 4",
                    "4tail",
                    "４",
                    huge.as_str(),
                ] {
                    let name = format!("{prefix}{suffix}");
                    assert!(!definitions.input(&name, 64), "{name:?}");
                    reject_without_mutation(
                        &mut definitions,
                        E::var(name, 64),
                        1,
                        SmtSort::BitVec(64),
                    );
                }
            }
        }
    }
}

#[test]
fn input_widths_observer_and_reserved_names_are_exact() {
    for stage in STAGES {
        let mut definitions = builder(stage, 4);
        for name in ["abi_x0", "abi_x3", "entry_x4", "entry_x30"] {
            for width in [1, 8, 16, 32, 128] {
                assert!(!definitions.input(name, width), "{name}:{width}");
                // BV1/BV32 are admitted definition sorts, so these refusals
                // specifically exercise input width, not just result width.
                if matches!(width, 1 | 32) {
                    reject_without_mutation(
                        &mut definitions,
                        E::var(name, width),
                        1,
                        SmtSort::BitVec(width),
                    );
                }
            }
        }
        for name in [
            "observe",
            "x0",
            "w0",
            "abi_w0",
            "entry_x31",
            "entry_x32",
            "entry_N",
            "entry_n0",
            "entry_memory",
        ] {
            assert!(!definitions.input(name, 64), "{name}");
            reject_without_mutation(&mut definitions, E::var(name, 64), 1, SmtSort::BitVec(64));
        }
    }
}

#[test]
fn flags_and_boolean_equations_are_target_only_and_width_exact() {
    for stage in STAGES {
        for arity in [0, 4, 8] {
            let mut definitions = builder(stage, arity);
            for name in ["entry_n", "entry_z", "entry_c", "entry_v"] {
                assert_eq!(definitions.input(name, 1), stage.target());
                for width in [8, 32, 64] {
                    assert!(!definitions.input(name, width));
                }
                let value = E::var(name, 1).eq_expr(E::bv_const(1, 1));
                if stage.target() {
                    let symbol = admitted(&mut definitions, value.clone(), 3, SmtSort::Bool);
                    assert_eq!(symbol.sort(), SmtSort::Bool);
                    let E::Eq { rhs, .. } = definitions.equations.last().unwrap() else {
                        panic!("Bool equation required")
                    };
                    assert_eq!(rhs.as_ref(), &value);
                } else {
                    reject_without_mutation(&mut definitions, value, 3, SmtSort::Bool);
                }
                reject_without_mutation(&mut definitions, E::var(name, 64), 1, SmtSort::BitVec(64));
            }
            if stage.target() {
                let literal = admitted(&mut definitions, E::BoolConst(true), 1, SmtSort::Bool);
                admitted(&mut definitions, literal, 1, SmtSort::Bool);
            } else {
                reject_without_mutation(&mut definitions, E::BoolConst(true), 1, SmtSort::Bool);
            }
            // Canonical source B1 storage is a BV1, not a target Bool equation.
            assert_eq!(
                admitted(&mut definitions, E::bv_const(1, 1), 1, SmtSort::BitVec(1)).sort(),
                SmtSort::BitVec(1)
            );
        }
    }
}

#[test]
fn past_symbols_are_same_stage_exact_sort_and_never_future_or_self_references() {
    for stage in STAGES {
        let mut definitions = builder(stage, 4);
        let first = admitted(
            &mut definitions,
            E::var("abi_x0", 64),
            1,
            SmtSort::BitVec(64),
        );
        let second = admitted(&mut definitions, first.clone(), 1, SmtSort::BitVec(64));
        let E::UF {
            name,
            args,
            ret_sort,
        } = &first
        else {
            panic!("fresh typed symbol required")
        };
        assert!(args.is_empty());
        assert_eq!(name, &format!("{}0", stage.prefix()));
        assert_eq!(ret_sort, &SmtSort::BitVec(64));
        assert_ne!(first, second);
        for other in STAGES {
            if other.prefix() != stage.prefix() {
                reject_without_mutation(
                    &mut definitions,
                    E::uf(format!("{}0", other.prefix()), vec![], SmtSort::BitVec(64)),
                    1,
                    SmtSort::BitVec(64),
                );
            }
        }
        for index in [2, 3, usize::MAX] {
            reject_without_mutation(
                &mut definitions,
                E::uf(
                    format!("{}{index}", stage.prefix()),
                    vec![],
                    SmtSort::BitVec(64),
                ),
                1,
                SmtSort::BitVec(64),
            );
        }
        reject_without_mutation(
            &mut definitions,
            E::uf(name, vec![], SmtSort::BitVec(32)),
            1,
            SmtSort::BitVec(32),
        );
        reject_without_mutation(
            &mut definitions,
            E::uf(name, vec![E::bv_const(0, 64)], SmtSort::BitVec(64)),
            2,
            SmtSort::BitVec(64),
        );
    }
}

#[test]
fn memory_equations_require_exact_entry_and_past_version_array_sorts() {
    let exact = memory_sort();
    let wrong_index = SmtSort::Array(Box::new(SmtSort::BitVec(32)), Box::new(SmtSort::BitVec(8)));
    let wrong_element =
        SmtSort::Array(Box::new(SmtSort::BitVec(64)), Box::new(SmtSort::BitVec(32)));
    for stage in STAGES {
        let mut definitions = builder(stage, 4);
        let store = |memory| E::store(memory, E::var("abi_x0", 64), E::bv_const(0xab, 8));
        let first = admitted(
            &mut definitions,
            store(E::uf("entry_memory", vec![], exact.clone())),
            4,
            exact.clone(),
        );
        assert_eq!(first.sort(), exact);
        let second = admitted(&mut definitions, store(first.clone()), 4, exact.clone());
        assert_eq!(second.sort(), exact);
        let load = E::select(second, E::var("abi_x1", 64)).zero_ext(56);
        admitted(&mut definitions, load, 4, SmtSort::BitVec(64));
        for wrong in [&wrong_index, &wrong_element] {
            reject_without_mutation(
                &mut definitions,
                store(E::uf("entry_memory", vec![], wrong.clone())),
                4,
                exact.clone(),
            );
            reject_without_mutation(&mut definitions, store(first.clone()), 4, wrong.clone());
        }
        reject_without_mutation(
            &mut definitions,
            store(E::uf("other_memory", vec![], exact.clone())),
            4,
            exact.clone(),
        );
        let E::UF { name, .. } = &first else {
            panic!("array version symbol required")
        };
        reject_without_mutation(
            &mut definitions,
            store(E::uf(name, vec![], wrong_element.clone())),
            4,
            exact.clone(),
        );
        // Array equations deliberately define actual Store terms, not an
        // unconstrained initial-memory alias or arbitrary constant array.
        reject_without_mutation(
            &mut definitions,
            E::uf("entry_memory", vec![], exact.clone()),
            1,
            exact.clone(),
        );
        reject_without_mutation(
            &mut definitions,
            E::const_array(SmtSort::BitVec(64), E::bv_const(0, 8)),
            2,
            exact.clone(),
        );
    }
}

#[test]
fn invalid_arity_and_result_sorts_refuse_without_installing_symbols() {
    for stage in STAGES {
        let mut bad_arity = builder(stage, 9);
        assert!(matches!(
            bad_arity.bind(E::bv_const(0, 64), 1, SmtSort::BitVec(64)),
            Err(Error::Invalid("scalar-memory ABI arity"))
        ));
        assert!(bad_arity.equations.is_empty() && bad_arity.sorts.is_empty());
        assert_eq!(bad_arity.nodes, 0);
        let mut definitions = builder(stage, 4);
        for (value, sort) in [
            (E::bv_const(0, 64), SmtSort::BitVec(32)),
            (E::bv_const(0, 32), SmtSort::BitVec(64)),
            (E::bv_const(0, 8), SmtSort::BitVec(8)),
            (E::bv_const(0, 64), SmtSort::Bool),
            (E::BoolConst(true), SmtSort::BitVec(1)),
        ] {
            reject_without_mutation(&mut definitions, value, 1, sort);
        }
    }
}

#[test]
fn group_occurrence_preflight_is_read_only_and_checks_overflow_and_remaining_slots() {
    for stage in STAGES {
        let mut definitions = builder(stage, 0);
        let limit = definitions.limits.occurrences;
        assert!(definitions.preflight_occurrences(limit).is_ok());
        assert!(matches!(
            definitions.preflight_occurrences(usize::MAX),
            Err(Error::Budget("scalar-memory definition occurrences"))
        ));
        assert!(definitions.equations.is_empty() && definitions.sorts.is_empty());
        assert_eq!(definitions.nodes, 0);
        admitted(&mut definitions, E::bv_const(0, 64), 1, SmtSort::BitVec(64));
        let equations = definitions.equations.clone();
        let sorts = definitions.sorts.clone();
        let nodes = definitions.nodes;
        assert!(definitions.preflight_occurrences(limit - 1).is_ok());
        assert!(definitions.preflight_occurrences(0).is_ok());
        assert!(matches!(
            definitions.preflight_occurrences(limit),
            Err(Error::Budget("scalar-memory definition occurrences"))
        ));
        assert!(matches!(
            definitions.preflight_occurrences(usize::MAX),
            Err(Error::Budget("scalar-memory definition occurrences"))
        ));
        assert_eq!(definitions.equations, equations);
        assert_eq!(definitions.sorts, sorts);
        assert_eq!(definitions.nodes, nodes);
    }
}
