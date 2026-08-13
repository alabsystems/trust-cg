// overflow_mul_seed_no_over_elimination_regression.rs — over-elimination blocker regression (MUL, #29/#30)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! PERMANENT regression for the MUL overflow carrier's no-over-elimination guarantee — the mul mirror
//! of `overflow_seed_no_over_elimination_regression.rs`.
//!
//! A proof associated with the OUTER multiplication must never delete the unrelated INNER add's panic
//! check. Production uses `Proof::CarrierNoOverflow` to keep carrier selection separate from general
//! value proofs. Proof labels are also report-only until exact validator replay authority exists, so
//! the outer mul carrier must expand to its concrete `MUL/SMULH/ASR/CMP/B.EQ/BRK` runtime check.
//! An adversarial legacy `Proof::NoOverflow` seed must retain the same checks.

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::function::MachFunction;
use trust_cg_ir::inst::AArch64Opcode;
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::{OverflowOp, pack_overflow_tag};

use trust_cg_lower::function::{BasicBlock, Function as LirFunction, Signature as LirSignature};
use trust_cg_lower::instructions::{Block as LirBlock, Instruction, IntCC, Opcode, Value};
use trust_cg_lower::{Proof, ProofContext, Type as LirType};

/// VS condition-code encoding (V == 1), the signed-overflow branch the inner i128 idiom fuses to.
const VS_ENCODING: i64 = 0b0110;
/// EQ (Z == 1), used to skip the outer signed-mul trap when high == sign-extension(low).
const EQ_ENCODING: i64 = 0b0000;

fn inst(opcode: Opcode, args: Vec<Value>, results: Vec<Value>) -> Instruction {
    Instruction {
        opcode,
        args,
        results,
    }
}

fn sext_i64_to_i128(src: Value, dst: Value) -> Instruction {
    inst(
        Opcode::Sextend {
            from_ty: LirType::I64,
            to_ty: LirType::I128,
        },
        vec![src],
        vec![dst],
    )
}

#[derive(Clone, Copy)]
enum Seed {
    /// Production behaviour AFTER the fix: synthetic carrier-only seed. Binds the mul carrier WITHOUT
    /// leaking onto the inner add's defining ADDS.
    CarrierOnly,
    /// Adversarial legacy general proof. It is report-only without validator replay authority.
    LegacyGeneral,
}

/// Build `(a + b)` [inner panic add, UNRELATED] feeding `(sum_ab * c)` [OUTER proven MUL carrier]:
///
/// ```text
/// entry(a, b, c):                       ; INNER add `a + b`, a panic-on-overflow check.
///   sum_ab   = Iadd a, b                ;   i128-widened signed-overflow idiom -> ADDS + B.VS
///   sa,sb,wide,ssum,ovf ...             ;   (the widened check; branches to panic on overflow)
///   Brif ovf -> panic, cont
///
/// panic: Trap
///
/// cont:                                 ; OUTER mul `sum_ab * c`, PROVEN no-overflow (the carrier).
///   prod     = Imul sum_ab, c           ;   plain wrapping value op (never touched by elimination)
///   GuardOverflow{SignedMul,64} sum_ab, c   ; self-contained mul-overflow carrier (proven -> eliminated)
///   Return prod
/// ```
fn build(seed: Seed) -> (LirFunction, ProofContext) {
    let sig = LirSignature {
        params: vec![LirType::I64, LirType::I64, LirType::I64],
        returns: vec![LirType::I64],
    };
    let mut func = LirFunction::new("inner_panic_outer_proven_mul", sig);

    let entry = LirBlock(0);
    let panic = LirBlock(1);
    let cont = LirBlock(2);
    func.entry_block = entry;
    func.block_order = vec![entry, panic, cont];

    let a = Value(0);
    let b = Value(1);
    let c = Value(2);
    let sum_ab = Value(3);
    let sa = Value(4);
    let sb = Value(5);
    let wide = Value(6);
    let ssum = Value(7);
    let ovf = Value(8);
    let prod = Value(9);

    let entry_block = BasicBlock {
        params: vec![(a, LirType::I64), (b, LirType::I64), (c, LirType::I64)],
        instructions: vec![
            inst(Opcode::Iadd, vec![a, b], vec![sum_ab]),
            sext_i64_to_i128(a, sa),
            sext_i64_to_i128(b, sb),
            inst(Opcode::Iadd, vec![sa, sb], vec![wide]),
            sext_i64_to_i128(sum_ab, ssum),
            inst(
                Opcode::Icmp {
                    cond: IntCC::NotEqual,
                },
                vec![ssum, wide],
                vec![ovf],
            ),
            inst(
                Opcode::Brif {
                    cond: ovf,
                    then_dest: panic,
                    else_dest: cont,
                },
                vec![ovf],
                vec![],
            ),
        ],
        ..Default::default()
    };

    let panic_block = BasicBlock {
        params: vec![],
        instructions: vec![inst(Opcode::Trap, vec![], vec![])],
        ..Default::default()
    };

    // OUTER proven MUL carrier.
    let op_tag = pack_overflow_tag(OverflowOp::SignedMul, 64);
    let mut proof_ctx = ProofContext::default();

    let make_proof = |signed: bool| match seed {
        Seed::CarrierOnly => Proof::CarrierNoOverflow { signed },
        Seed::LegacyGeneral => Proof::NoOverflow { signed },
    };
    proof_ctx
        .value_proofs
        .insert(sum_ab, vec![make_proof(true)]);
    proof_ctx.value_proofs.insert(c, vec![make_proof(true)]);

    let obligation = proof_ctx.synthesize_discharged_obligation();

    let cont_block = BasicBlock {
        params: vec![],
        instructions: vec![
            inst(Opcode::Imul, vec![sum_ab, c], vec![prod]),
            inst(
                Opcode::GuardOverflow { op_tag, obligation },
                vec![sum_ab, c],
                vec![],
            ),
            inst(Opcode::Return, vec![prod], vec![]),
        ],
        ..Default::default()
    };

    func.blocks.insert(entry, entry_block);
    func.blocks.insert(panic, panic_block);
    func.blocks.insert(cont, cont_block);

    (func, proof_ctx)
}

fn prepare(func: &LirFunction, ctx: &ProofContext) -> MachFunction {
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O2,
        verify: false,
        ..PipelineConfig::default()
    });
    pipeline
        .prepare_function_with_metrics(func, Some(ctx))
        .map(|(prepared, _)| prepared)
        .expect("prepare inner-panic / outer-proven mul function")
}

fn count_opcode(func: &MachFunction, opcode: AArch64Opcode) -> usize {
    func.block_order
        .iter()
        .flat_map(|&block_id| func.block(block_id).insts.iter())
        .filter(|&&inst_id| func.inst(inst_id).opcode == opcode)
        .count()
}

fn count_bvs(func: &MachFunction) -> usize {
    count_bcond(func, VS_ENCODING)
}

fn count_bcond(func: &MachFunction, encoding: i64) -> usize {
    func.block_order
        .iter()
        .flat_map(|&block_id| func.block(block_id).insts.iter())
        .filter(|&&inst_id| {
            let inst = func.inst(inst_id);
            inst.opcode == AArch64Opcode::BCond
                && matches!(
                    inst.operands.first(),
                    Some(MachOperand::Imm(actual)) if *actual == encoding
                )
        })
        .count()
}

fn has_trap_overflow_exact(func: &MachFunction) -> bool {
    count_opcode(func, AArch64Opcode::TrapOverflowExact) > 0
}

/// Production behaviour: preserve the unrelated inner panic check and expand the outer carrier into
/// an executable runtime guard while exact validator replay authority is unavailable.
#[test]
fn carrier_only_seed_preserves_inner_panic_check_and_expands_mul_runtime_guard() {
    let (func, ctx) = build(Seed::CarrierOnly);
    let prepared = prepare(&func, &ctx);

    // (a) The INNER panic add's overflow check MUST survive.
    assert!(
        count_opcode(&prepared, AArch64Opcode::AddsRR) >= 1,
        "the inner panic add's flag-setting ADDS must be PRESERVED; a mul proof on the OUTER op \
         must never delete the INNER op's overflow check"
    );
    assert!(
        count_bvs(&prepared) >= 1,
        "the inner panic add's B.VS overflow-branch must be PRESERVED"
    );

    // (b) The outer carrier must be KEPT and expanded, not accidentally deleted.
    assert!(
        !has_trap_overflow_exact(&prepared),
        "TrapOverflowExact must not survive the mandatory expansion boundary"
    );
    assert!(
        count_opcode(&prepared, AArch64Opcode::Smulh) >= 1,
        "the signed-mul carrier must recompute the high product at runtime"
    );
    assert!(
        count_bcond(&prepared, EQ_ENCODING) >= 1
            && count_opcode(&prepared, AArch64Opcode::Brk) >= 1,
        "the signed-mul carrier must retain its B.EQ/BRK runtime overflow path"
    );
}

/// Fail-closed control: a legacy general proof label cannot authorize deleting either runtime check
/// without exact validator replay authority.
#[test]
fn legacy_general_seed_cannot_over_eliminate_mul_without_replay_authority() {
    let (carrier_func, carrier_ctx) = build(Seed::CarrierOnly);
    let carrier_only = prepare(&carrier_func, &carrier_ctx);
    let (legacy_func, legacy_ctx) = build(Seed::LegacyGeneral);
    let legacy = prepare(&legacy_func, &legacy_ctx);

    let carrier_only_adds = count_opcode(&carrier_only, AArch64Opcode::AddsRR);
    let legacy_adds = count_opcode(&legacy, AArch64Opcode::AddsRR);
    let carrier_only_bvs = count_bvs(&carrier_only);
    let legacy_bvs = count_bvs(&legacy);

    assert_eq!(
        (legacy_adds, legacy_bvs),
        (carrier_only_adds, carrier_only_bvs),
        "report-only legacy proof labels must not reduce the inner overflow check: \
         carrier_only(AddsRR={carrier_only_adds}, B.VS={carrier_only_bvs}) vs \
         legacy(AddsRR={legacy_adds}, B.VS={legacy_bvs})"
    );
    assert!(
        legacy_bvs >= 1,
        "legacy proof labels must keep the inner add's B.VS overflow branch"
    );
    assert!(
        count_opcode(&legacy, AArch64Opcode::Smulh) >= 1
            && count_bcond(&legacy, EQ_ENCODING) >= 1
            && count_opcode(&legacy, AArch64Opcode::Brk) >= 1,
        "legacy proof labels must not delete the outer mul runtime overflow guard"
    );
}
