// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Repeatable rotated GCD loop through the real AArch64 pipeline. Source
//! omission credit is narrower than complete machine instruction coverage.

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::provenance::SourceInstId;
use trust_cg_ir::{AArch64Opcode, MachFunction};
use trust_cg_lower::function::{BasicBlock, Signature};
use trust_cg_lower::instructions::{Block, Instruction, IntCC, Opcode as O, Value};
use trust_cg_lower::{Function, Type};
use trust_cg_verify::aarch64_trap_guard::{TRAP_GUARD_REFUSED, account};
use trust_cg_verify::function_verifier::{
    FunctionVerificationPreconditionFailure, FunctionVerificationReport, FunctionVerifier,
    InstructionVerificationResult,
};
use trust_cg_verify::lowering_proof::VerificationConfig;
use trust_cg_verify::provenance_xcheck::{LirSourceIndex, ProvenanceXCheckMode};

fn inst(opcode: O, args: &[u32], results: &[u32]) -> Instruction {
    Instruction {
        opcode,
        args: args.iter().copied().map(Value).collect(),
        results: results.iter().copied().map(Value).collect(),
    }
}

fn rotated_gcd() -> Function {
    let mut f = Function::new(
        "omitted_remainder_trap",
        Signature {
            params: vec![Type::I64, Type::I64],
            returns: vec![],
        },
    );
    let blocks = [
        (
            0,
            vec![(Value(0), Type::I64), (Value(1), Type::I64)],
            vec![
                inst(O::Copy, &[0], &[67]),
                inst(O::Copy, &[1], &[69]),
                inst(O::Jump { dest: Block(10) }, &[], &[]),
            ],
        ),
        (
            10,
            vec![(Value(67), Type::I64), (Value(69), Type::I64)],
            vec![
                inst(O::Copy, &[69], &[70]),
                inst(
                    O::Switch {
                        cases: vec![(0, Block(12))],
                        default: Block(11),
                    },
                    &[70],
                    &[],
                ),
            ],
        ),
        (
            11,
            vec![],
            vec![
                inst(O::Copy, &[69], &[76]),
                inst(
                    O::Iconst {
                        ty: Type::I64,
                        imm: 0,
                    },
                    &[],
                    &[77],
                ),
                inst(O::Icmp { cond: IntCC::Equal }, &[76, 77], &[78]),
                inst(
                    O::Iconst {
                        ty: Type::B1,
                        imm: 0,
                    },
                    &[],
                    &[79],
                ),
                inst(O::Icmp { cond: IntCC::Equal }, &[78, 79], &[80]),
                inst(
                    O::Brif {
                        cond: Value(80),
                        then_dest: Block(14),
                        else_dest: Block(15),
                    },
                    &[80],
                    &[],
                ),
            ],
        ),
        // This reachable zero-exit trap is intentionally unrelated to the
        // contradictory panic edge. Its accounting refusal must survive.
        (12, vec![], vec![inst(O::Trap, &[], &[])]),
        (
            14,
            vec![],
            vec![
                inst(O::Urem, &[67, 76], &[83]),
                inst(O::Copy, &[69], &[84]),
                inst(O::Copy, &[83], &[85]),
                inst(O::Copy, &[84], &[67]),
                inst(O::Copy, &[85], &[69]),
                inst(O::Jump { dest: Block(10) }, &[], &[]),
            ],
        ),
        (15, vec![], vec![inst(O::Trap, &[], &[])]),
    ];
    f.blocks.clear();
    f.block_order.clear();
    for (id, params, instructions) in blocks {
        f.block_order.push(Block(id));
        f.blocks.insert(
            Block(id),
            BasicBlock {
                params,
                instructions,
                ..Default::default()
            },
        );
    }
    f
}

fn prepare(source: &Function) -> MachFunction {
    Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O2,
        verify: false,
        ..PipelineConfig::for_target("aarch64-unknown-linux-gnu")
    })
    .prepare_function_with_metrics(source, None)
    .expect("real rotated-loop pipeline")
    .0
}

fn verify(machine: &MachFunction, source: &Function) -> FunctionVerificationReport {
    FunctionVerifier::with_config(VerificationConfig::for_proof_promotion())
        .verify_with_lir_source_and_mode(machine, Some(source), ProvenanceXCheckMode::Enforce)
}

fn unaccounted(report: &FunctionVerificationReport) -> &[String] {
    match &report.precondition_failure {
        Some(FunctionVerificationPreconditionFailure::TrapGuardAccounting(failure)) => {
            assert!(failure.absent_windows.is_empty(), "{failure:?}");
            &failure.unaccounted_sources
        }
        None => &[],
        other => panic!("unexpected function prerequisite failure: {other:?}"),
    }
}

#[test]
fn rotated_gcd_omission_discharges_only_the_contradictory_plain_trap() {
    let source = rotated_gcd();
    let machine = prepare(&source);
    let indexed_only = account(
        &machine,
        Some(&LirSourceIndex::build(&source)),
        &VerificationConfig::for_proof_promotion(),
    )
    .expect_err("an index without retained edges cannot prove an omitted trap");
    assert!(
        indexed_only
            .unaccounted_sources
            .iter()
            .any(|s| s == "`Trap` at LIR (15, 0)")
    );
    let report = verify(&machine, &source);
    let missing = unaccounted(&report);
    assert!(
        !missing.iter().any(|s| s == "`Trap` at LIR (15, 0)"),
        "{report:?}"
    );
    let surviving = machine
        .block_order
        .iter()
        .flat_map(|block| &machine.blocks[block.0 as usize].insts)
        .find(|&&id| {
            machine.inst(id).opcode == AArch64Opcode::Brk
                && machine.inst_lowering_provenance(id).source_id()
                    == Some(SourceInstId {
                        block: 12,
                        index: 0,
                    })
        })
        .expect("reachable zero-exit BRK");
    let row = report
        .instructions
        .iter()
        .find(|row| row.inst_index == surviving.0 as usize)
        .expect("surviving BRK verdict");
    assert!(
        matches!(
            &row.result,
            InstructionVerificationResult::Unverified { reason }
                if reason.starts_with(TRAP_GUARD_REFUSED)
        ),
        "{row:?}"
    );
    assert!(!report.emitted_opcode_inventory().is_promotable());
}

#[test]
fn stale_switch_or_retest_cannot_reuse_the_pipeline_omission() {
    let original = rotated_gcd();
    let machine = prepare(&original);
    let edits: [fn(&mut Function); 4] = [
        |source| {
            source.blocks.get_mut(&Block(10)).unwrap().instructions[1].opcode = O::Switch {
                cases: vec![(1, Block(12))],
                default: Block(11),
            };
        },
        |source| {
            source.blocks.get_mut(&Block(11)).unwrap().instructions[4].opcode = O::Icmp {
                cond: IntCC::NotEqual,
            };
        },
        |source| {
            source.blocks.get_mut(&Block(11)).unwrap().instructions[0].args = vec![Value(67)];
        },
        |source| {
            source.blocks.get_mut(&Block(0)).unwrap().instructions[2].opcode =
                O::Jump { dest: Block(11) };
        },
    ];
    for edit in edits {
        let mut source = original.clone();
        edit(&mut source);
        let report = verify(&machine, &source);
        let missing = unaccounted(&report);
        assert!(
            missing.iter().any(|s| s == "`Trap` at LIR (15, 0)"),
            "{report:?}"
        );
        assert!(!report.emitted_opcode_inventory().is_promotable());
    }
}
