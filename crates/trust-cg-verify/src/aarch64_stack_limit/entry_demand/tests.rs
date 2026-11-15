// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::aarch64_stack_limit::{function_stack_facts, module_bound};
use trust_cg_ir::aarch64_regs::X1;
use trust_cg_ir::types::BlockId;
use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, Signature, SpecialReg};

fn facts(name: &str, frame: u32, callees: &[&str]) -> FunctionStackFacts {
    FunctionStackFacts {
        name: name.to_string(),
        role: StackRole::Plain,
        frame: Some(frame),
        direct_callees: callees.iter().map(|symbol| (*symbol).to_string()).collect(),
        indirect_call: false,
    }
}

fn fixed(bytes: u64) -> EntryStackDemand {
    EntryStackDemand::Fixed {
        bytes,
        external_assumptions: BTreeMap::new(),
    }
}

fn checked(name: &str, frame: u32, callees: &[&str], handler: Option<&str>) -> FunctionStackFacts {
    let mut function = facts(name, frame, callees);
    function.role = StackRole::Checked {
        csa: 16,
        handler: handler.map(str::to_string),
    };
    function
}

#[test]
fn entry_demand_composes_existing_hand_built_final_stream_facts() {
    let stream = |name: &str, frame: i64, callee: Option<&str>, dynamic: bool| {
        let mut function = MachFunction::new(name.to_string(), Signature::new(vec![], vec![]));
        let sp = MachOperand::Special(SpecialReg::SP);
        let mut instructions = vec![MachInst::new(
            AArch64Opcode::SubRI,
            vec![sp.clone(), sp.clone(), MachOperand::Imm(frame)],
        )];
        if dynamic {
            instructions.push(MachInst::new(
                AArch64Opcode::SubRR,
                vec![sp.clone(), sp.clone(), MachOperand::PReg(X1)],
            ));
        }
        if let Some(callee) = callee {
            instructions.push(MachInst::new(
                AArch64Opcode::Bl,
                vec![MachOperand::Symbol(callee.to_string())],
            ));
        }
        instructions.push(MachInst::new(
            AArch64Opcode::AddRI,
            vec![sp.clone(), sp, MachOperand::Imm(frame)],
        ));
        instructions.push(MachInst::new(AArch64Opcode::Ret, vec![]));
        for instruction in instructions {
            let id = function.push_inst(instruction);
            function.append_inst(BlockId(0), id);
        }
        function_stack_facts(&function, None)
    };
    let entry = stream("entry", 32, Some("callee"), false);
    let callee = stream("callee", 16, None, false);
    assert_eq!(entry.frame, Some(32));
    assert_eq!(entry.direct_callees, BTreeSet::from(["callee".to_string()]));
    assert_eq!(
        entry_stack_demand(&[entry.clone(), callee], "entry"),
        fixed(48)
    );
    let dynamic = stream("callee", 16, None, true);
    assert_eq!(dynamic.frame, None);
    assert_eq!(
        entry_stack_demand(&[entry, dynamic], "entry"),
        EntryStackDemand::Unknown(EntryStackDemandUnknown::UnknownFrame {
            function: "callee".to_string(),
        })
    );
}

#[test]
fn entry_demand_counts_full_frames_and_maximum_not_sequential_sum() {
    let functions = vec![
        facts("entry", 16, &["small", "large"]),
        facts("small", 8, &[]),
        facts("large", 32, &["leaf"]),
        facts("leaf", 4, &[]),
    ];
    assert_eq!(entry_stack_demand(&functions, "entry"), fixed(52));
    assert_eq!(entry_stack_demand(&functions, "leaf"), fixed(4));
}

#[test]
fn entry_demand_distinguishes_zero_missing_and_unknown() {
    assert_eq!(
        entry_stack_demand(&[facts("zero", 0, &[])], "zero"),
        fixed(0)
    );
    assert_eq!(
        entry_stack_demand(&[], "missing"),
        EntryStackDemand::Unknown(EntryStackDemandUnknown::MissingRoot {
            root: "missing".to_string(),
        })
    );
    let mut unknown = checked("unknown", 0, &[], None);
    unknown.frame = None;
    assert_eq!(
        entry_stack_demand(&[unknown], "unknown"),
        EntryStackDemand::Unknown(EntryStackDemandUnknown::UnknownFrame {
            function: "unknown".to_string(),
        })
    );
}

#[test]
fn entry_demand_does_not_interpret_no_requester_u10_reserve_as_entry_zero() {
    let functions = [facts("entry", 64, &[])];
    assert_eq!(module_bound(&functions, 0).reserve, Some(0));
    assert_eq!(entry_stack_demand(&functions, "entry"), fixed(64));
}

#[test]
fn entry_demand_checks_do_not_reset_full_frame_demand() {
    let functions = [
        checked("entry", 64, &["leaf"], None),
        facts("leaf", 32, &[]),
    ];
    assert_eq!(module_bound(&functions, 0).reserve, Some(32));
    assert_eq!(entry_stack_demand(&functions, "entry"), fixed(96));
    let mut contradictory = checked("entry", 8, &[], None);
    contradictory.role = StackRole::Checked {
        csa: 32,
        handler: None,
    };
    assert_eq!(entry_stack_demand(&[contradictory], "entry"), fixed(32));
}

#[test]
fn entry_demand_checked_recursive_cycle_is_unknown_despite_finite_u10_reserve() {
    let functions = [
        checked("entry", 64, &["callee"], None),
        facts("callee", 48, &["entry"]),
    ];
    assert_eq!(module_bound(&functions, 0).reserve, Some(64));
    assert_eq!(
        entry_stack_demand(&functions, "entry"),
        EntryStackDemand::Unknown(EntryStackDemandUnknown::ReachableCycle {
            cycle: vec![
                "entry".to_string(),
                "callee".to_string(),
                "entry".to_string()
            ],
        })
    );
}

#[test]
fn entry_demand_role_only_handler_is_a_real_callee_and_cycle_edge() {
    let functions = [
        checked("entry", 64, &[], Some("handler")),
        facts("handler", 32, &[]),
    ];
    assert_eq!(entry_stack_demand(&functions, "entry"), fixed(96));
    assert_eq!(
        entry_stack_demand(&[checked("entry", 64, &[], Some("entry"))], "entry"),
        EntryStackDemand::Unknown(EntryStackDemandUnknown::ReachableCycle {
            cycle: vec!["entry".to_string(), "entry".to_string()],
        })
    );
    let functions = [
        checked("entry", 64, &[], Some("handler")),
        checked("handler", 32, &[], Some("entry")),
    ];
    assert!(matches!(
        entry_stack_demand(&functions, "entry"),
        EntryStackDemand::Unknown(EntryStackDemandUnknown::ReachableCycle { .. })
    ));
    let functions = [
        checked("entry", 64, &["handler"], Some("handler")),
        facts("handler", 32, &[]),
    ];
    assert_eq!(entry_stack_demand(&functions, "entry"), fixed(96));
}

#[test]
fn entry_demand_external_callees_and_handlers_are_unknown_by_default() {
    assert_eq!(
        entry_stack_demand(&[facts("entry", 16, &["external"])], "entry"),
        EntryStackDemand::Unknown(EntryStackDemandUnknown::UnboundExternalCall {
            caller: "entry".to_string(),
            callee: "external".to_string(),
        })
    );
    assert_eq!(
        entry_stack_demand(&[checked("entry", 64, &[], Some("handler"))], "entry"),
        EntryStackDemand::Unknown(EntryStackDemandUnknown::UnboundOverflowHandler {
            function: "entry".to_string(),
            handler: "handler".to_string(),
        })
    );
}

#[test]
fn entry_demand_named_assumptions_are_explicit_and_only_used_names_survive() {
    let functions = [checked("entry", 64, &["external"], Some("handler"))];
    let assumptions = BTreeMap::from([
        ("external".to_string(), 8),
        ("handler".to_string(), 32),
        ("unused".to_string(), 4096),
    ]);
    assert_eq!(
        entry_stack_demand_with_assumptions(&functions, "entry", &assumptions),
        EntryStackDemand::Fixed {
            bytes: 96,
            external_assumptions: BTreeMap::from([
                ("external".to_string(), 8),
                ("handler".to_string(), 32)
            ]),
        }
    );
    let zero = BTreeMap::from([("external".to_string(), 0)]);
    assert_eq!(
        entry_stack_demand_with_assumptions(&[facts("entry", 16, &["external"])], "entry", &zero),
        EntryStackDemand::Fixed {
            bytes: 16,
            external_assumptions: zero
        }
    );
}

#[test]
fn entry_demand_assumptions_cannot_override_bodies_roots_or_indirect_calls() {
    let assumptions = BTreeMap::from([("entry".to_string(), 0), ("callee".to_string(), 0)]);
    let functions = [facts("entry", 16, &["callee"]), facts("callee", 32, &[])];
    assert_eq!(
        entry_stack_demand_with_assumptions(&functions, "entry", &assumptions),
        fixed(48)
    );
    assert!(matches!(
        entry_stack_demand_with_assumptions(&[], "entry", &assumptions),
        EntryStackDemand::Unknown(EntryStackDemandUnknown::MissingRoot { .. })
    ));
    let mut indirect = facts("entry", 16, &[]);
    indirect.indirect_call = true;
    assert_eq!(
        entry_stack_demand_with_assumptions(&[indirect], "entry", &assumptions),
        EntryStackDemand::Unknown(EntryStackDemandUnknown::IndirectCall {
            function: "entry".to_string()
        })
    );
}

#[test]
fn entry_demand_diamond_memoization_is_not_a_cycle_and_is_order_independent() {
    let functions = vec![
        facts("entry", 16, &["left", "right"]),
        facts("left", 8, &["shared"]),
        facts("right", 32, &["shared"]),
        facts("shared", 4, &[]),
    ];
    let expected = fixed(52);
    assert_eq!(entry_stack_demand(&functions, "entry"), expected);
    let reversed: Vec<_> = functions.into_iter().rev().collect();
    assert_eq!(entry_stack_demand(&reversed, "entry"), expected);
}

#[test]
fn entry_demand_unknown_diagnostics_are_symbol_ordered() {
    let functions = vec![
        facts("entry", 16, &["z", "a"]),
        facts("z", 8, &["z"]),
        facts("a", 8, &["a"]),
    ];
    let expected = EntryStackDemand::Unknown(EntryStackDemandUnknown::ReachableCycle {
        cycle: vec!["a".to_string(), "a".to_string()],
    });
    assert_eq!(entry_stack_demand(&functions, "entry"), expected);
    let reversed: Vec<_> = functions.into_iter().rev().collect();
    assert_eq!(entry_stack_demand(&reversed, "entry"), expected);
}

#[test]
fn entry_demand_unreachable_cycles_unknown_frames_and_imports_do_not_poison_root() {
    let mut unknown = facts("unknown", 0, &[]);
    unknown.frame = None;
    let mut indirect = facts("indirect", 8, &[]);
    indirect.indirect_call = true;
    let functions = [
        facts("entry", 16, &[]),
        facts("cycle", 8, &["cycle"]),
        unknown,
        indirect,
        facts("import", 8, &["external"]),
    ];
    assert_eq!(entry_stack_demand(&functions, "entry"), fixed(16));
}

#[test]
fn entry_demand_duplicate_roster_is_unknown_even_for_unreachable_symbols() {
    let functions = vec![
        facts("entry", 16, &[]),
        facts("z", 8, &[]),
        facts("z", 32, &[]),
        facts("a", 8, &[]),
        facts("a", 32, &[]),
    ];
    let expected = EntryStackDemand::Unknown(EntryStackDemandUnknown::DuplicateSymbol {
        symbol: "a".to_string(),
    });
    assert_eq!(entry_stack_demand(&functions, "entry"), expected);
    let reversed: Vec<_> = functions.into_iter().rev().collect();
    assert_eq!(entry_stack_demand(&reversed, "entry"), expected);
}

#[test]
fn entry_demand_checked_addition_overflow_is_unknown() {
    let functions = [facts("entry", 1, &["external"])];
    let assumptions = BTreeMap::from([("external".to_string(), u64::MAX)]);
    assert_eq!(
        entry_stack_demand_with_assumptions(&functions, "entry", &assumptions),
        EntryStackDemand::Unknown(EntryStackDemandUnknown::AdditionOverflow {
            function: "entry".to_string(),
            frame: 1,
            callee_demand: u64::MAX
        })
    );
    assert_eq!(
        entry_stack_demand_with_assumptions(
            &[facts("entry", 0, &["external"])],
            "entry",
            &assumptions
        ),
        EntryStackDemand::Fixed {
            bytes: u64::MAX,
            external_assumptions: assumptions
        }
    );
}

#[test]
fn entry_demand_large_acyclic_chain_uses_iterative_traversal() {
    let count = 20_000;
    let functions: Vec<_> = (0..count)
        .map(|position| FunctionStackFacts {
            name: format!("f{position}"),
            role: StackRole::Plain,
            frame: Some(16),
            direct_callees: if position + 1 < count {
                BTreeSet::from([format!("f{}", position + 1)])
            } else {
                BTreeSet::new()
            },
            indirect_call: false,
        })
        .collect();
    assert_eq!(entry_stack_demand(&functions, "f0"), fixed(count * 16));
}
