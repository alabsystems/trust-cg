// overflow_seed_no_over_elimination_regression.rs — over-elimination blocker regression (auditor repro)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! PERMANENT regression for the overflow proof-seeding over-elimination BLOCKER.
//!
//! A proof associated with the OUTER operation must never delete the unrelated INNER panic check in
//! `(a + b).overflowing_add(c)`. Production uses `Proof::CarrierNoOverflow` to keep carrier selection
//! separate from general value proofs. In addition, production proof labels are report-only until
//! exact validator replay authority is available, so the outer carrier must remain as a concrete
//! runtime check rather than disappear merely because a label says it is discharged.
//!
//! This fixture drives the exact shape through the real O2 pipeline and pins both boundaries:
//! the inner `ADDS + B.VS` survives, and the outer `TrapOverflowExact` is expanded to an executable
//! `ADDS + B.VC + BRK` check. An adversarial legacy `Proof::NoOverflow` seed must produce no fewer
//! inner checks than the carrier-only seed while replay authority is unavailable.

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::function::MachFunction;
use trust_cg_ir::inst::AArch64Opcode;
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::{OverflowOp, pack_overflow_tag};

use trust_cg_lower::function::{BasicBlock, Function as LirFunction, Signature as LirSignature};
use trust_cg_lower::instructions::{Block as LirBlock, Instruction, IntCC, Opcode, Value};
use trust_cg_lower::{Proof, ProofContext, Type as LirType};

/// VS condition-code encoding (V == 1), the signed-overflow branch the i128 idiom fuses to.
const VS_ENCODING: i64 = 0b0110;
/// VC (V == 0), used to skip the outer signed-overflow trap when the recomputation is safe.
const VC_ENCODING: i64 = 0b0111;

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

/// How the fixture seeds the carrier's operand no-overflow proofs.
#[derive(Clone, Copy)]
enum Seed {
    /// Production behaviour AFTER the fix: synthetic carrier-only seed. Binds the carrier WITHOUT
    /// leaking onto the inner add's defining ADDS.
    CarrierOnly,
    /// Adversarial legacy `Proof::NoOverflow` seed. Without validator replay authority it is
    /// report-only and must not delete either runtime check.
    LegacyGeneral,
}

/// Build the auditor repro `(a + b).overflowing_add(c)` shape as LIR driven through the real pipeline:
///
/// ```text
/// entry(a, b, c):                       ; INNER add `a + b`, a panic-on-overflow check.
///   sum_ab   = Iadd a, b                ;   i128-widened signed-overflow idiom -> ADDS + B.VS
///   sa       = SExt(I64->I128) a
///   sb       = SExt(I64->I128) b
///   wide     = Iadd sa, sb
///   ssum     = SExt(I64->I128) sum_ab
///   ovf      = Icmp Ne(I128) ssum, wide
///   Brif ovf -> panic, cont            ;   overflow => panic; else continue
///
/// panic:                                ; the inner add's panic handler (trap).
///   Trap
///
/// cont:                                 ; OUTER add `sum_ab + c`, PROVEN no-overflow (the carrier).
///   sum      = Iadd sum_ab, c           ;   plain wrapping value op (never touched by elimination)
///   GuardOverflow{SignedAdd,64} sum_ab, c   ; self-contained overflow carrier (proven -> eliminated)
///   Return sum
/// ```
///
/// The `ProofContext` seeds a no-overflow proof on BOTH outer-carrier operands (`sum_ab`, `c`) and
/// synthesizes a Discharged obligation for the carrier (so the kernel authorizes eliminating it). The
/// `Seed` mode selects either the synthetic carrier-only production variant or the legacy general
/// proof used as a fail-closed adversarial control.
fn build(seed: Seed) -> (LirFunction, ProofContext) {
    let sig = LirSignature {
        params: vec![LirType::I64, LirType::I64, LirType::I64],
        returns: vec![LirType::I64],
    };
    let mut func = LirFunction::new("inner_panic_outer_proven_add", sig);

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
    let sum = Value(9);

    // Entry: the inner i128-widened signed-overflow idiom for `a + b` (fuses to ADDS + B.VS + B), with
    // the overflow boolean branching to the panic handler.
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

    // Panic handler for the inner add's overflow.
    let panic_block = BasicBlock {
        params: vec![],
        instructions: vec![inst(Opcode::Trap, vec![], vec![])],
        ..Default::default()
    };

    // Continuation: the OUTER proven add `sum_ab + c`, decoupled into a plain value op + a
    // self-contained overflow carrier.
    let op_tag = pack_overflow_tag(OverflowOp::SignedAdd, 64);
    let mut proof_ctx = ProofContext::default();

    // Seed the carrier's operand no-overflow proofs. `CarrierOnly` mirrors production; the legacy
    // general variant verifies that untrusted/report-only labels cannot delete runtime checks.
    let make_proof = |signed: bool| match seed {
        Seed::CarrierOnly => Proof::CarrierNoOverflow { signed },
        Seed::LegacyGeneral => Proof::NoOverflow { signed },
    };
    proof_ctx
        .value_proofs
        .insert(sum_ab, vec![make_proof(true)]);
    proof_ctx.value_proofs.insert(c, vec![make_proof(true)]);

    // Synthesize the carrier's bound obligation as Discharged so the kernel authorizes eliminating the
    // PROVEN outer carrier (the intended behaviour we must preserve alongside closing the leak).
    let obligation = proof_ctx.synthesize_discharged_obligation();

    let cont_block = BasicBlock {
        params: vec![],
        instructions: vec![
            inst(Opcode::Iadd, vec![sum_ab, c], vec![sum]),
            inst(
                Opcode::GuardOverflow { op_tag, obligation },
                vec![sum_ab, c],
                vec![],
            ),
            inst(Opcode::Return, vec![sum], vec![]),
        ],
        ..Default::default()
    };

    func.blocks.insert(entry, entry_block);
    func.blocks.insert(panic, panic_block);
    func.blocks.insert(cont, cont_block);

    (func, proof_ctx)
}

/// Prepare through the REAL pipeline at O2 with the kernel gate at its production default (ON).
fn prepare(func: &LirFunction, ctx: &ProofContext) -> MachFunction {
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O2,
        verify: false,
        ..PipelineConfig::default()
    });
    pipeline
        .prepare_function_with_metrics(func, Some(ctx))
        .map(|(prepared, _)| prepared)
        .expect("prepare inner-panic / outer-proven overflow function")
}

fn count_opcode(func: &MachFunction, opcode: AArch64Opcode) -> usize {
    func.block_order
        .iter()
        .flat_map(|&block_id| func.block(block_id).insts.iter())
        .filter(|&&inst_id| func.inst(inst_id).opcode == opcode)
        .count()
}

/// Count `B.VS` branches (BCond with the VS condition-code immediate) — the inner add's signed
/// overflow guard branch.
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

/// Whether an exact carrier improperly survives the mandatory post-RA expansion boundary.
fn has_trap_overflow_exact(func: &MachFunction) -> bool {
    count_opcode(func, AArch64Opcode::TrapOverflowExact) > 0
}

/// Production behaviour: preserve the unrelated inner panic check and keep the outer carrier as an
/// executable runtime check until exact validator replay authority exists.
#[test]
fn carrier_only_seed_preserves_inner_panic_check_and_expands_outer_runtime_guard() {
    let (func, ctx) = build(Seed::CarrierOnly);
    let prepared = prepare(&func, &ctx);

    // (a) The INNER panic add's overflow check MUST survive: its flag-setting ADDS and its B.VS branch
    //     are both present (the i128 idiom fused to ADDS + B.VS + B; neither was deleted).
    assert!(
        count_opcode(&prepared, AArch64Opcode::AddsRR) >= 1,
        "the inner panic add's flag-setting ADDS must be PRESERVED (not converted to ADD); \
         a proof on the OUTER op must never delete the INNER op's overflow check"
    );
    assert!(
        count_bvs(&prepared) >= 1,
        "the inner panic add's B.VS overflow-branch must be PRESERVED"
    );

    // (b) The outer carrier must be KEPT and expanded, not accidentally deleted. Exact-carrier
    //     expansion recomputes signed overflow and skips BRK on VC.
    assert!(
        !has_trap_overflow_exact(&prepared),
        "TrapOverflowExact must not survive the mandatory expansion boundary"
    );
    assert!(
        count_bcond(&prepared, VC_ENCODING) >= 1,
        "the outer signed-add carrier must expand to a B.VC skip branch"
    );
    assert!(
        count_opcode(&prepared, AArch64Opcode::Brk) >= 1,
        "the outer carrier must retain an executable BRK overflow path without replay authority"
    );
}

/// Fail-closed control: a legacy general label is report-only without validator replay and cannot
/// authorize deleting the inner panic check or the outer runtime guard.
#[test]
fn legacy_general_seed_cannot_over_eliminate_without_replay_authority() {
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
        "legacy proof labels must not delete the inner add's B.VS overflow branch"
    );
    assert!(
        count_bcond(&legacy, VC_ENCODING) >= 1 && count_opcode(&legacy, AArch64Opcode::Brk) >= 1,
        "legacy proof labels must not delete the outer runtime overflow guard"
    );
}
