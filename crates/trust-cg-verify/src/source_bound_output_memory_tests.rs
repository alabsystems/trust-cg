// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use crate::source_bound_frame::{diagnostic_output_memory_obligation, source_bound_frame};
use trust_cg_ir::function::Signature;
use trust_cg_ir::regs::{PReg, SpecialReg, X29};
use trust_cg_lower::function::BasicBlock;
use trust_cg_lower::instructions::{DirectCallBinding, Instruction};

fn p(n: u16) -> O {
    O::PReg(PReg::new(n))
}

// Explicit source/machine fixtures test the independent checker, not the Rust
// frontend. The separately authored Rust writer still needs a real backend run.
pub(super) fn fixture(paired: bool) -> (Function, MachFunction) {
    let mut source = Function::new(
        "output_writer",
        trust_cg_lower::function::Signature {
            params: vec![Type::I64; 6],
            returns: vec![],
        },
    );
    let mut instructions = Vec::new();
    for slot in 0..5 {
        let constant = Value(6 + slot * 2);
        let address = Value(7 + slot * 2);
        instructions.push(Instruction {
            opcode: L::Iconst {
                ty: Type::I64,
                imm: i64::from(slot) * 8,
            },
            args: vec![],
            results: vec![constant],
        });
        instructions.push(Instruction {
            opcode: L::Iadd,
            args: vec![Value(0), constant],
            results: vec![address],
        });
        instructions.push(Instruction {
            opcode: L::Store {
                ty: Type::I64,
                align: Some(8),
            },
            args: vec![Value(slot + 1), address],
            results: vec![],
        });
    }
    instructions.push(Instruction {
        opcode: L::Return,
        args: vec![],
        results: vec![],
    });
    source.blocks.insert(
        source.entry_block,
        BasicBlock {
            params: (0..6).map(|i| (Value(i), Type::I64)).collect(),
            instructions,
            ..BasicBlock::default()
        },
    );
    let mut machine = MachFunction::new(
        source.name.clone(),
        Signature::new(vec![MachineType::I64; 6], vec![]),
    );
    let sp = O::Special(SpecialReg::SP);
    let mut instructions = vec![
        MachInst::new(
            M::StpPreIndex,
            vec![O::PReg(X29), O::PReg(X30), sp.clone(), O::Imm(-16)],
        ),
        MachInst::new(M::AddRI, vec![O::PReg(X29), sp.clone(), O::Imm(0)]),
    ];
    if paired {
        for slot in [0_u16, 2] {
            instructions.push(MachInst::new(
                M::StpRI,
                vec![p(slot + 1), p(slot + 2), p(0), O::Imm(i64::from(slot) * 8)],
            ));
        }
        instructions.push(MachInst::new(M::StrRI, vec![p(5), p(0), O::Imm(32)]));
    } else {
        for slot in 0..5_u16 {
            instructions.push(MachInst::new(
                M::StrRI,
                vec![p(slot + 1), p(0), O::Imm(i64::from(slot) * 8)],
            ));
        }
    }
    instructions.push(MachInst::new(
        M::LdpPostIndex,
        vec![O::PReg(X29), O::PReg(X30), sp, O::Imm(16)],
    ));
    instructions.push(MachInst::new(M::Ret, vec![O::PReg(X30)]));
    for inst in instructions {
        let id = machine.push_inst(inst);
        machine.append_inst(machine.entry, id);
    }
    (source, machine)
}

#[test]
fn output_store_queries_match_scalar_and_paired_streams_without_admission() {
    for paired in [false, true] {
        let (source, machine) = fixture(paired);
        let proof = diagnostic_output_memory_obligation(&source, &machine).unwrap();
        assert_eq!(proof.inputs.len(), 10);
        assert_eq!(proof.preconditions.len(), 5);
        assert!(source_bound_frame(&source, &machine).is_err());
        let query = crate::ay_bridge::generate_smt2_query_raw(
            &proof,
            &crate::ay_bridge::AYConfig::default(),
        );
        for required in [
            "entry_memory",
            "entry_fp",
            "entry_lr",
            "observe",
            "arg_0",
            "arg_5",
            "store",
            "select",
        ] {
            assert!(query.contains(required), "missing {required}");
        }
        // Export is diagnostic: no solver is run and no formal credit is claimed.
        println!(
            "OUTPUT_MEMORY_QUERY={}",
            serde_json::to_string(&query).unwrap()
        );
    }
}

#[test]
fn output_store_range_premises_cover_the_last_byte_without_wrapped_separation() {
    let (source, machine) = fixture(false);
    let proof = diagnostic_output_memory_obligation(&source, &machine).unwrap();
    let holds = |output: u64, sp: u64| {
        let env: HashMap<String, u64> = [("arg_0".into(), output), ("entry_sp".into(), sp)]
            .into_iter()
            .collect();
        proof.preconditions.iter().all(|p| p.eval(&env).as_bool())
    };
    assert!(holds(u64::MAX - 39, 16));
    assert!(holds(u64::MAX - 39, u64::MAX - 47));
    assert!(!holds(u64::MAX - 39, u64::MAX - 15));
    assert!(!holds(u64::MAX - 31, 16));
    let addresses: Vec<_> = (0..=80).chain((0..=80).map(|n| u64::MAX - n)).collect();
    for &output in &addresses {
        for &sp in &addresses {
            // Independent unbounded-end oracle. The exclusive endpoint is
            // allowed to be 2^64; no u64 addition defines the oracle's range.
            let end = u128::from(output) + 40;
            let expected = sp >= 16
                && sp % 16 == 0
                && output % 8 == 0
                && end <= 1_u128 << 64
                && (end <= u128::from(sp - 16) || output >= sp);
            assert_eq!(holds(output, sp), expected, "output={output:#x} sp={sp:#x}");
        }
    }
}

#[test]
fn output_store_addresses_values_widths_and_pair_order_are_independent() {
    for paired in [false, true] {
        let (source, machine) = fixture(paired);
        for mutation in 0..10 {
            let mut wrong = machine.clone();
            match mutation {
                0 => wrong.insts[2].operands[0] = p(5),
                1 => *wrong.insts[2].operands.last_mut().unwrap() = O::Imm(8),
                2 => wrong.insts[2].operands[if paired { 2 } else { 1 }] = p(1),
                3 => wrong.insts[2].operands[0] = p(33), // W alias: not eight bytes
                4 => wrong.insts[2].operands[0] = p(19), // unproved callee-save value
                5 => wrong.insts[2].implicit_defs = &[X30],
                6 => wrong.insts[2].flags |= trust_cg_ir::InstFlags::IS_PSEUDO,
                7 => wrong.insts[2].operands.push(O::Imm(0)),
                8 => wrong.insts[2].opcode = M::Bl,
                _ => {
                    wrong.insts[2].operands[if paired { 2 } else { 1 }] = O::Special(SpecialReg::SP)
                }
            }
            assert!(
                diagnostic_output_memory_obligation(&source, &wrong).is_none(),
                "paired={paired} mutation={mutation}"
            );
        }
    }
}

#[test]
fn output_store_source_validation_and_hidden_effects_refuse() {
    let (source, machine) = fixture(false);
    for mutation in 0..10 {
        let mut wrong = source.clone();
        let instructions = &mut wrong
            .blocks
            .get_mut(&wrong.entry_block)
            .unwrap()
            .instructions;
        match mutation {
            0 => instructions[2].args[0] = Value(5),
            1 => {
                instructions[0].opcode = L::Iconst {
                    ty: Type::I64,
                    imm: 8,
                }
            }
            2 => instructions[1].args[0] = Value(1),
            3 => instructions[0].results[0] = Value(0),
            4 => instructions[2].args[0] = Value(999),
            5 => {
                instructions[2].opcode = L::Store {
                    ty: Type::I32,
                    align: Some(4),
                }
            }
            6 => {
                instructions[2].opcode = L::Store {
                    ty: Type::I64,
                    align: Some(16),
                }
            }
            7 => {
                instructions[2].opcode = L::Call {
                    name: "callback".into(),
                    binding: DirectCallBinding::Interposable,
                }
            }
            8 => {
                instructions.pop();
            }
            _ => {
                wrong.value_types.insert(Value(1), Type::F64);
            }
        }
        assert!(
            diagnostic_output_memory_obligation(&wrong, &machine).is_none(),
            "mutation={mutation}"
        );
    }
}

#[test]
fn output_store_aliasing_is_ordered_not_a_set_of_final_writes() {
    let (mut source, mut machine) = fixture(false);
    // Two writes to the same output address are legal; both traces must retain
    // their order. The final-memory query compares the last writer on each side.
    source
        .blocks
        .get_mut(&source.entry_block)
        .unwrap()
        .instructions[3]
        .opcode = L::Iconst {
        ty: Type::I64,
        imm: 0,
    };
    machine.insts[3].operands[2] = O::Imm(0);
    assert!(diagnostic_output_memory_obligation(&source, &machine).is_some());
    machine.insts[2].operands[0] = p(2);
    machine.insts[3].operands[0] = p(1);
    assert!(diagnostic_output_memory_obligation(&source, &machine).is_none());
}

#[test]
fn output_store_tracks_copies_pointer_offsets_and_full_width_constants() {
    let (source, mut machine) = fixture(false);
    machine.insts[2].operands[0] = p(9);
    machine
        .insts
        .insert(2, MachInst::new(M::MOVXrr, vec![p(9), p(1)]));
    machine.blocks[0].insts = (0..machine.insts.len())
        .map(|i| trust_cg_ir::InstId(i as u32))
        .collect();
    assert!(diagnostic_output_memory_obligation(&source, &machine).is_some());
    machine.insts[2].operands[1] = p(2);
    assert!(diagnostic_output_memory_obligation(&source, &machine).is_none());

    let (source, mut machine) = fixture(false);
    // Address computation is independently tracked, including destructive
    // updates of the output base after its first use.
    machine.insts[3].operands[2] = O::Imm(0);
    machine
        .insts
        .insert(3, MachInst::new(M::AddRI, vec![p(9), p(0), O::Imm(8)]));
    machine.insts[4].operands[1] = p(9);
    machine.blocks[0].insts = (0..machine.insts.len())
        .map(|i| trust_cg_ir::InstId(i as u32))
        .collect();
    assert!(diagnostic_output_memory_obligation(&source, &machine).is_some());
    machine.insts[3].operands[2] = O::Imm(16);
    assert!(diagnostic_output_memory_obligation(&source, &machine).is_none());

    let (mut source, mut machine) = fixture(false);
    let literal = 0xfedc_ba98_7654_3210_u64;
    let instructions = &mut source
        .blocks
        .get_mut(&source.entry_block)
        .unwrap()
        .instructions;
    instructions[2].args[0] = Value(20);
    instructions.insert(
        0,
        Instruction {
            opcode: L::Iconst {
                ty: Type::I64,
                imm: literal as i64,
            },
            args: vec![],
            results: vec![Value(20)],
        },
    );
    machine.insts[2].operands[0] = p(9);
    for half in (0..4).rev() {
        let op = if half == 0 { M::Movz } else { M::Movk };
        machine.insts.insert(
            2,
            MachInst::new(
                op,
                vec![
                    p(9),
                    O::Imm(((literal >> (16 * half)) & 0xffff) as i64),
                    O::Imm(16 * half),
                ],
            ),
        );
    }
    machine.blocks[0].insts = (0..machine.insts.len())
        .map(|i| trust_cg_ir::InstId(i as u32))
        .collect();
    assert!(diagnostic_output_memory_obligation(&source, &machine).is_some());
    machine.insts[5].operands[1] = O::Imm(0);
    assert!(diagnostic_output_memory_obligation(&source, &machine).is_none());
}

#[test]
fn output_store_gep_stride_and_offset_bounds_are_source_derived() {
    for (ty, stride) in [
        (Type::I8, 1),
        (Type::I16, 2),
        (Type::I32, 4),
        (Type::I64, 8),
    ] {
        let (mut source, machine) = fixture(false);
        let instructions = &mut source
            .blocks
            .get_mut(&source.entry_block)
            .unwrap()
            .instructions;
        for slot in 0..5 {
            instructions[slot * 3].opcode = L::Iconst {
                ty: Type::I64,
                imm: (slot * 8 / stride) as i64,
            };
            instructions[slot * 3 + 1].opcode = L::ArrayGep {
                elem_ty: ty.clone(),
            };
        }
        assert!(diagnostic_output_memory_obligation(&source, &machine).is_some());
        source
            .blocks
            .get_mut(&source.entry_block)
            .unwrap()
            .instructions[3]
            .opcode = L::Iconst {
            ty: Type::I64,
            imm: i64::MAX,
        };
        assert!(diagnostic_output_memory_obligation(&source, &machine).is_none());
    }
    for offset in [-8, 7, 4096] {
        let (mut source, machine) = fixture(false);
        source
            .blocks
            .get_mut(&source.entry_block)
            .unwrap()
            .instructions[3]
            .opcode = L::Iconst {
            ty: Type::I64,
            imm: offset,
        };
        assert!(diagnostic_output_memory_obligation(&source, &machine).is_none());
    }
}

#[test]
fn output_store_premises_exclude_wrap_misalignment_and_private_frame_aliases() {
    let (source, machine) = fixture(true);
    let proof = diagnostic_output_memory_obligation(&source, &machine).unwrap();
    let admitted = |sp: u64, output: u64| {
        let env = HashMap::from([("entry_sp".to_string(), sp), ("arg_0".to_string(), output)]);
        proof
            .preconditions
            .iter()
            .all(|p| p.try_eval(&env).unwrap() == crate::smt::EvalResult::Bool(true))
    };
    assert!(admitted(4096, 8192));
    assert!(admitted(4096, 4000));
    assert!(admitted(4096, 4096)); // caller-owned region starts above frame
    for (sp, output) in [
        (8, 8192),
        (4097, 8192),
        (4096, 8193),
        (4096, u64::MAX - 7),
        (4096, 4080),
        (4096, 4072),
        (4096, 4056),
    ] {
        assert!(!admitted(sp, output), "sp={sp} output={output}");
    }
}

#[test]
fn output_store_frame_and_instruction_ownership_remain_required() {
    let (source, machine) = fixture(false);
    for mutation in 0..5 {
        let mut wrong = machine.clone();
        match mutation {
            0 => wrong.insts[0].operands[3] = O::Imm(-32),
            1 => wrong.insts[0].operands[0] = p(19),
            2 => {
                let last = wrong.insts.len() - 2;
                wrong.insts[last].operands[3] = O::Imm(32);
            }
            3 => {
                let duplicate = wrong.blocks[0].insts[2];
                wrong.blocks[0].insts.insert(3, duplicate);
            }
            _ => {
                wrong.push_inst(MachInst::new(M::StrRI, vec![p(1), p(0), O::Imm(0)]));
            }
        }
        assert!(
            diagnostic_output_memory_obligation(&source, &wrong).is_none(),
            "mutation={mutation}"
        );
    }
}
