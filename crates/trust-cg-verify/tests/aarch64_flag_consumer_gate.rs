// trust-cg-verify/tests/aarch64_flag_consumer_gate.rs — X-OPCODES-P3/P5.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The FCMP, CSET, CSEL, CSINC and CSNEG credits rest on words CAPTURED from
//! the encoder (`trust-cg-verify` cannot call it outside tests) and on the
//! per-instruction producer binding in the function verifier. This target ties
//! both to live code:
//!
//! * the captured words are re-derived from the live encoder, and a sweep of
//!   every register field and condition decodes back through the independent
//!   decoders;
//! * ENC-5 (`trust-cg-codegen`'s AArch64 decode check) runs the independent
//!   FP-compare decoder on every emitted FCMP word;
//! * TrustIR modules with integer and floating-point comparisons feeding CSET
//!   and selects are lowered by the real adapter and selector, and every
//!   emitted FCMP/CSET/CSEL row verifies against exactly the obligation of its
//!   reaching producer, width and condition;
//! * the coverage-gate rows accept with the real hook and refuse an injected
//!   failing one.
//!
//! Evidence is sampled/finite evaluation plus decoding; none of it is a formal
//! proof or a silicon differential (see `aarch64_nzcv_silicon_bridge`).

use trust_cg_codegen::aarch64::decode_check::A64DecodeCheck;
use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_codegen::decode_check::{DecodeCheck, DecodeCheckOutcome};
use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, PReg, SpecialReg};
use trust_cg_lower::abi::AArch64AbiVariant;

use trust_cg_lower::isel::InstructionSelector;
use trust_cg_verify::aarch64_csel_semantics::DecodedConditionalSelect;
use trust_cg_verify::aarch64_flag_consumer_proofs::{
    captured_flag_words, check_captured_flag_word, decode_fp_compare, flag_consumer_credit,
};
use trust_cg_verify::coverage_gate::{CoverageFinding, CoverageGate};
use trust_cg_verify::lowering_proof::VerificationConfig;
use trust_cg_verify::provenance_xcheck::ProvenanceXCheckMode;
use trust_cg_verify::{FunctionVerifier, InstructionOpcode, InstructionVerificationResult};
use trust_ir::{
    Block, BlockId, FCmpOp, FuncId, FuncTy, Function, ICmpOp, Inst, InstrNode, Module, Ty, ValueId,
};

// ---------------------------------------------------------------------------
// Captured words and the live encoder
// ---------------------------------------------------------------------------

#[test]
fn captured_words_are_what_the_live_encoder_emits_today() {
    let corpus = captured_flag_words();
    assert_eq!(corpus.len(), 3 * 2 * 14 + 2 * 14 + 2);
    for entry in &corpus {
        let word = encode_instruction(&entry.inst)
            .unwrap_or_else(|error| panic!("live encoder refused {:?}: {error:?}", entry.inst));
        assert_eq!(
            word, entry.word,
            "captured word for {:?} is stale: live {word:#010x}",
            entry.inst
        );
        check_captured_flag_word(entry).unwrap_or_else(|error| panic!("{error}"));
    }
}

fn gpr(width: u32, n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(if width == 32 { 32 + n } else { n }))
}

fn fpr(width: u32, n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(if width == 32 { 128 + n } else { 96 + n }))
}

fn zr(width: u32) -> MachOperand {
    MachOperand::Special(if width == 32 {
        SpecialReg::WZR
    } else {
        SpecialReg::XZR
    })
}

#[test]
fn live_sweep_decodes_back_through_the_independent_decoders() {
    let mut checked = 0;
    let registers: Vec<(u16, u8)> = (0..31u16).map(|n| (n, n as u8)).collect();
    for width in [32u32, 64] {
        for (opcode, op, o2) in [
            (AArch64Opcode::Csel, 0, 0),
            (AArch64Opcode::Csinc, 0, 1),
            (AArch64Opcode::Csneg, 1, 1),
        ] {
            for cond in 0..16i64 {
                for &(rd, rd_hw) in &registers {
                    for (rn, rn_hw) in [
                        (gpr(width, (rd + 7) % 31), ((rd + 7) % 31) as u8),
                        (zr(width), 31),
                    ] {
                        let rm = gpr(width, (rd + 19) % 31);
                        let inst = MachInst::new(
                            opcode,
                            vec![gpr(width, rd), rn, rm, MachOperand::Imm(cond)],
                        );
                        let word = encode_instruction(&inst).expect("encodable select");
                        let decoded = DecodedConditionalSelect::decode(word).expect("decodes");
                        assert_eq!(decoded.width().bits(), width);
                        assert_eq!(decoded.registers(), (rd_hw, rn_hw, ((rd + 19) % 31) as u8));
                        assert_eq!(i64::from(decoded.condition()), cond);
                        assert_eq!((word >> 30) & 1, op, "{opcode:?} op bit of {word:#010x}");
                        assert_eq!((word >> 10) & 1, o2);
                        checked += 1;
                    }
                }
            }
        }
        for cc in 0..14i64 {
            for &(rd, rd_hw) in &registers {
                let inst = MachInst::new(
                    AArch64Opcode::CSet,
                    vec![gpr(width, rd), MachOperand::Imm(cc)],
                );
                let word = encode_instruction(&inst).expect("encodable CSET");
                let decoded = DecodedConditionalSelect::decode(word).expect("decodes");
                assert_eq!(decoded.registers(), (rd_hw, 31, 31));
                assert_eq!(i64::from(decoded.condition()), cc ^ 1);
                checked += 1;
            }
        }
        for rn in 0..32u16 {
            for rm in [0u16, 1, 17, 31] {
                let inst = MachInst::new(AArch64Opcode::Fcmp, vec![fpr(width, rn), fpr(width, rm)]);
                let word = encode_instruction(&inst).expect("encodable FCMP");
                let decoded = decode_fp_compare(word).expect("decodes");
                assert_eq!(
                    (decoded.width, decoded.rn, decoded.rm),
                    (width, rn as u8, rm as u8)
                );
                assert!(!decoded.against_zero && !decoded.signaling);
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 2 * (3 * 16 * 31 * 2 + 14 * 31 + 32 * 4));
}

#[test]
fn per_compile_decode_check_runs_the_independent_fp_compare_decoder() {
    let enc5 =
        |inst: &MachInst, word: u32| A64DecodeCheck.check_one(inst, &word.to_le_bytes(), None);
    for width in [32u32, 64] {
        let inst = MachInst::new(AArch64Opcode::Fcmp, vec![fpr(width, 3), fpr(width, 9)]);
        let word = encode_instruction(&inst).expect("encodable FCMP");
        assert!(
            matches!(enc5(&inst, word), DecodeCheckOutcome::Match),
            "{inst:?}: {:?}",
            enc5(&inst, word)
        );
        // Wrong register, swapped operands, other precision, FCMPE and the
        // compare-with-zero form are mismatches, not matches or allowlists.
        for (label, bad) in [
            ("Rn", word ^ (1 << 5)),
            ("swap", (word & !0x001F_03E0) | (3 << 16) | (9 << 5)),
            ("ftype", word ^ (1 << 22)),
            ("FCMPE", word | (1 << 4)),
            ("zero", (word & !0x001F_0000) | (1 << 3)),
        ] {
            assert!(
                matches!(enc5(&inst, bad), DecodeCheckOutcome::Mismatch(_)),
                "{label}: {bad:#010x} must mismatch {inst:?}"
            );
        }
    }
    // A mixed-width intent is a mismatch whatever word accompanies it. A
    // half-precision intent (`FCMP H1, H2`, which an F16 `fcmp` lowers to) is
    // decoded by ENC-5's FP/SIMD slice since L10-P6: its word matches and a
    // corrupted one mismatches. That is emission redundancy only; the packed
    // NZCV obligations above model the S/D compares.
    let mixed = MachInst::new(AArch64Opcode::Fcmp, vec![fpr(32, 1), fpr(64, 2)]);
    assert!(matches!(
        enc5(&mixed, 0x1E22_2020),
        DecodeCheckOutcome::Mismatch(_)
    ));
    let half = MachInst::new(
        AArch64Opcode::Fcmp,
        vec![
            MachOperand::PReg(PReg::new(166)),
            MachOperand::PReg(PReg::new(167)),
        ],
    );
    assert_eq!(encode_instruction(&half).ok(), Some(0x1EE2_2020));
    assert!(matches!(
        enc5(&half, 0x1EE2_2020),
        DecodeCheckOutcome::Match
    ));
    for bad in [
        0x1EE2_2020 ^ (1 << 22),
        0x1EE2_2020 ^ (1 << 16),
        0x1EE2_2030,
    ] {
        assert!(matches!(enc5(&half, bad), DecodeCheckOutcome::Mismatch(_)));
    }
    // The encoder spells a GPR "FCMP" as a D-register compare; ENC-5 refuses
    // the malformed intent rather than counting it.
    let gpr_intent = MachInst::new(AArch64Opcode::Fcmp, vec![gpr(32, 1), gpr(32, 2)]);
    let word = encode_instruction(&gpr_intent).expect("the encoder does not refuse it");
    assert_eq!(decode_fp_compare(word).map(|decoded| decoded.width), Ok(64));
    assert!(matches!(
        enc5(&gpr_intent, word),
        DecodeCheckOutcome::Mismatch(_)
    ));
}

// ---------------------------------------------------------------------------
// Real selector output binds every flag consumer
// ---------------------------------------------------------------------------

fn v(id: u32) -> ValueId {
    ValueId::new(id)
}

fn module(params: Vec<Ty>, ret: Ty, body: Vec<InstrNode>, result: u32) -> Module {
    let mut module = Module::new("flag_consumer_fixture");
    let signature = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns: vec![ret],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let entry = BlockId::new(0);
    let mut function = Function::new(FuncId::new(0), "flags", signature, entry);
    let mut body = body;
    body.push(InstrNode::new(Inst::Return {
        values: vec![v(result)],
    }));
    function.blocks.push(Block {
        id: entry,
        params: params
            .into_iter()
            .enumerate()
            .map(|(index, ty)| (v(index as u32), ty))
            .collect(),
        body,
    });
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn lower(module: &Module) -> MachFunction {
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        module,
        &permit_unlicensed(),
    )
    .expect("adapter accepts");
    let mut selector = InstructionSelector::new(lir.name.clone(), lir.signature.clone());
    selector.set_abi_variant(AArch64AbiVariant::Darwin);
    selector.set_stack_slots(lir.stack_slots.clone());
    selector.seed_value_types(&lir.value_types);
    selector.seed_iconst_origins(
        lir.blocks
            .values()
            .map(|block| block.instructions.as_slice()),
    );
    selector.seed_function_value_use_counts(&lir);
    selector
        .lower_formal_arguments(&lir.signature, lir.entry_block)
        .expect("ABI lowers");
    for id in lir.layout_order() {
        let block = &lir.blocks[&id];
        selector
            .select_block_with_provenance(
                id,
                &block.instructions,
                &block.source_locs,
                &lir.trust_ir_origins[&id],
            )
            .expect("instructions select");
    }
    selector
        .finalize_with_eh_info(&lir.eh_info)
        .expect("no EH")
        .to_ir_func()
}

fn icmp_select(ty: Ty, op: ICmpOp) -> Module {
    module(
        vec![ty.clone(); 4],
        ty.clone(),
        vec![
            InstrNode::new(Inst::ICmp {
                op,
                ty: ty.clone(),
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(10)),
            InstrNode::new(Inst::Select {
                ty,
                cond: v(10),
                then_val: v(2),
                else_val: v(3),
            })
            .with_result(v(11)),
        ],
        11,
    )
}

fn fcmp_bool(ty: Ty, op: FCmpOp) -> Module {
    module(
        vec![ty.clone(); 2],
        Ty::Bool,
        vec![
            InstrNode::new(Inst::FCmp {
                op,
                ty,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(10)),
        ],
        10,
    )
}

fn fcmp_select(ty: Ty, op: FCmpOp, arm: Ty) -> Module {
    module(
        vec![ty.clone(), ty.clone(), arm.clone(), arm.clone()],
        arm.clone(),
        vec![
            InstrNode::new(Inst::FCmp {
                op,
                ty,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(10)),
            InstrNode::new(Inst::Select {
                ty: arm,
                cond: v(10),
                then_val: v(2),
                else_val: v(3),
            })
            .with_result(v(11)),
        ],
        11,
    )
}

/// Verify `machine` and return, per FCMP/CSET/CSEL-family row, the registry
/// query the row binds, lowercased (or the result as an `Err`). Since E0.2 a
/// bound row is refused as a registry name lookup naming exactly that query;
/// a `Verified` row, or any other refusal, is an `Err`.
fn flag_rows(machine: &MachFunction) -> Vec<(AArch64Opcode, Result<String, String>)> {
    let verifier = FunctionVerifier::with_config(VerificationConfig::with_sample_count(64));
    let report = verifier.verify_with_lir_source_and_mode(machine, None, ProvenanceXCheckMode::Off);
    report
        .instructions
        .iter()
        .filter_map(|row| {
            let InstructionOpcode::AArch64(opcode) = row.opcode else {
                return None;
            };
            if !matches!(
                opcode,
                AArch64Opcode::Fcmp
                    | AArch64Opcode::CSet
                    | AArch64Opcode::Csel
                    | AArch64Opcode::Csinc
                    | AArch64Opcode::Csneg
            ) {
                return None;
            }
            Some((
                opcode,
                match &row.result {
                    InstructionVerificationResult::Unverified { reason }
                        if reason.starts_with(
                            trust_cg_verify::function_verifier::REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT,
                        ) =>
                    {
                        let query = reason.split('`').nth(1).unwrap_or_else(|| {
                            panic!("a registry refusal names its query: {reason}")
                        });
                        Ok(query.to_lowercase())
                    }
                    other => Err(format!("{other:?}")),
                },
            ))
        })
        .collect()
}

#[test]
fn real_selector_integer_selects_bind_to_their_reaching_cmp() {
    use ICmpOp::*;
    let mut rows = 0;
    for ty in [Ty::I32, Ty::I64] {
        for op in [Eq, Ne, Slt, Sle, Sgt, Sge, Ult, Ule, Ugt, Uge] {
            let machine = lower(&icmp_select(ty.clone(), op));
            let bound = flag_rows(&machine);
            assert!(
                bound
                    .iter()
                    .any(|(opcode, _)| *opcode == AArch64Opcode::Csel),
                "{ty:?}/{op:?}: no CSEL in {machine:#?}"
            );
            for (opcode, result) in bound {
                let name = result
                    .unwrap_or_else(|reason| panic!("{ty:?}/{op:?}: {opcode:?} unbound: {reason}"));
                match opcode {
                    AArch64Opcode::Csel => assert!(
                        name.starts_with("a64 nzcv csel") && name.contains(" over cmp w"),
                        "{name}"
                    ),
                    AArch64Opcode::CSet => assert!(name.starts_with("icmp_"), "{name}"),
                    other => panic!("unexpected {other:?}"),
                }
                rows += 1;
            }
        }
    }
    assert!(rows >= 20);
}

#[test]
fn real_selector_fcmp_booleans_bind_fcmp_and_every_cset() {
    use FCmpOp::*;
    let mut rows = 0;
    for (ty, width) in [(Ty::F32, 32), (Ty::F64, 64)] {
        for op in [OEq, ONe, OLt, OLe, OGt, OGe, UEq, UNe, ULt, ULe, UGt, UGe] {
            let machine = lower(&fcmp_bool(ty.clone(), op));
            let bound = flag_rows(&machine);
            let csets = bound
                .iter()
                .filter(|(opcode, _)| *opcode == AArch64Opcode::CSet)
                .count();
            assert!(csets >= 1, "{ty:?}/{op:?}: {machine:#?}");
            for (opcode, result) in bound {
                let name = result
                    .unwrap_or_else(|reason| panic!("{ty:?}/{op:?}: {opcode:?} unbound: {reason}"));
                let prefix = match opcode {
                    AArch64Opcode::Fcmp => format!("a64 nzcv fcmp f{width} packed:"),
                    AArch64Opcode::CSet => format!("a64 nzcv fcmp f{width} -> cset "),
                    other => panic!("unexpected {other:?}"),
                };
                assert!(name.starts_with(&prefix), "{name}");
                rows += 1;
            }
        }
    }
    // 24 FCMPs plus at least one CSET each (two for ONE/UEQ).
    assert!(rows >= 48 + 4, "{rows}");
}

#[test]
fn real_selector_fcmp_selects_bind_their_select_family() {
    use FCmpOp::*;
    let mut rows = 0;
    for (ty, width) in [(Ty::F32, 32), (Ty::F64, 64)] {
        for arm in [Ty::I32, Ty::I64] {
            for op in [OEq, OLt, OGe, UNe, ULt, UGt] {
                let machine = lower(&fcmp_select(ty.clone(), op, arm.clone()));
                let bound = flag_rows(&machine);
                assert!(
                    bound
                        .iter()
                        .any(|(opcode, _)| *opcode == AArch64Opcode::Csel),
                    "{ty:?}/{arm:?}/{op:?}: no CSEL in {machine:#?}"
                );
                for (opcode, result) in bound {
                    let name = result.unwrap_or_else(|reason| {
                        panic!("{ty:?}/{arm:?}/{op:?}: {opcode:?} unbound: {reason}")
                    });
                    if opcode == AArch64Opcode::Csel {
                        assert!(
                            name.starts_with("a64 nzcv csel")
                                && (name.contains(&format!(" over fcmp f{width} "))
                                    || name.contains(" over cmp w")),
                            "{name}"
                        );
                    }
                    rows += 1;
                }
            }
        }
    }
    assert!(rows >= 24);
}

// ---------------------------------------------------------------------------
// Coverage-gate rows
// ---------------------------------------------------------------------------

#[test]
fn gate_rows_accept_with_the_real_hook_and_refuse_a_failing_one() {
    let gate = CoverageGate::with_config(VerificationConfig::with_sample_count(512));
    for opcode in [
        AArch64Opcode::Fcmp,
        AArch64Opcode::CSet,
        AArch64Opcode::Csel,
        AArch64Opcode::Csinc,
        AArch64Opcode::Csneg,
    ] {
        let row = gate
            .audit_aarch64_flag_consumer_with(opcode, &flag_consumer_credit)
            .expect("flag-consumer opcode");
        assert!(row.finding.is_none(), "{row:?}");
        assert!(row.note.contains("NOT a formal proof"), "{}", row.note);
        let refused = gate
            .audit_aarch64_flag_consumer_with(opcode, &|_| Err("injected".into()))
            .expect("flag-consumer opcode");
        assert!(
            matches!(
                refused.finding,
                Some(CoverageFinding::ProofNotDischarged { .. })
            ),
            "{refused:?}"
        );
    }
    assert!(
        gate.audit_aarch64_flag_consumer_with(AArch64Opcode::Csinv, &flag_consumer_credit)
            .is_none(),
        "CSINV is not a credited flag consumer"
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
