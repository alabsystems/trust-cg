// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Canonical source Boolean literals/copies and the width-neutral Boolean-only
//! frame domain. Concrete checks are regressions, not independent proof replay.

use super::{SourceBoundBody, raw_body};
use crate::lowering_proof::ProofObligation;
use crate::smt::{EvalEnv, EvalResult};
use crate::source_bound_frame::source_bound_frame;
use trust_cg_ir::function::Type as MachineType;
use trust_cg_ir::regs::PReg;
use trust_cg_ir::{AArch64Opcode as M, InstId, MachFunction, MachInst, MachOperand as O};
use trust_cg_lower::Type;
use trust_cg_lower::function::{BasicBlock, Function, Signature};
use trust_cg_lower::instructions::{Instruction, IntCC, Opcode as L, Value};

fn r(index: u16, bits: u32) -> O {
    O::PReg(PReg::new(index + if bits == 32 { 32 } else { 0 }))
}

fn copy(bits: u32) -> M {
    if bits == 32 { M::MOVWrr } else { M::MOVXrr }
}

fn ty(bits: u32) -> Type {
    if bits == 32 { Type::I32 } else { Type::I64 }
}

fn inst(opcode: L, args: &[u32], result: Option<u32>) -> Instruction {
    Instruction {
        opcode,
        args: args.iter().copied().map(Value).collect(),
        results: result.into_iter().map(Value).collect(),
    }
}

#[derive(Clone, Copy)]
struct SelectIds {
    inputs: [InstId; 2],
    arms: [InstId; 2],
    literal: InstId,
    selector_copy: InstId,
    cmp: InstId,
    select: InstId,
    stale_result: InstId,
    result: InstId,
}

/// Select a+1 or b-1, not a parameter identity. Cross-width transport of
/// literal 0/1 is already canonical in the affine machine frame model.
fn selector_fixture(
    bits: u32,
    literal: i64,
    selector: IntCC,
    carrier: u32,
) -> (Function, MachFunction, SelectIds) {
    let (_, mut machine) = crate::source_bound_alu::tests::fixture(bits, M::AddRR, r(1, bits));
    let integer = ty(bits);
    let mut source = Function::new(
        "raw_bool_literal_select",
        Signature {
            params: vec![integer.clone(); 2],
            returns: vec![integer.clone()],
        },
    );
    let params = vec![(Value(0), integer.clone()), (Value(1), integer.clone())];
    source.value_types.extend(params.iter().cloned());
    for value in [2, 3, 4, 7] {
        source.value_types.insert(Value(value), integer.clone());
    }
    for value in [5, 6] {
        source.value_types.insert(Value(value), Type::B1);
    }
    source.blocks.insert(
        source.entry_block,
        BasicBlock {
            params,
            instructions: vec![
                inst(
                    L::Iconst {
                        ty: integer,
                        imm: 1,
                    },
                    &[],
                    Some(2),
                ),
                inst(L::Iadd, &[0, 2], Some(3)),
                inst(L::Isub, &[1, 2], Some(4)),
                inst(
                    L::Iconst {
                        ty: Type::B1,
                        imm: literal,
                    },
                    &[],
                    Some(5),
                ),
                inst(L::Copy, &[5], Some(6)),
                inst(L::Select { cond: selector }, &[6, 3, 4], Some(7)),
                inst(L::Return, &[7], None),
            ],
            ..Default::default()
        },
    );
    machine.name.clone_from(&source.name);
    let inputs = [
        machine.push_inst(MachInst::new(copy(bits), vec![r(9, bits), r(0, bits)])),
        machine.push_inst(MachInst::new(copy(bits), vec![r(10, bits), r(1, bits)])),
    ];
    let arms = [
        machine.push_inst(MachInst::new(
            M::AddRI,
            vec![r(9, bits), r(9, bits), O::Imm(1)],
        )),
        machine.push_inst(MachInst::new(
            M::SubRI,
            vec![r(10, bits), r(10, bits), O::Imm(1)],
        )),
    ];
    let literal_inst = machine.push_inst(MachInst::new(
        M::Movz,
        vec![r(11, if carrier == 32 { 64 } else { 32 }), O::Imm(literal)],
    ));
    let selector_copy = machine.push_inst(MachInst::new(
        copy(carrier),
        vec![r(12, carrier), r(11, carrier)],
    ));
    machine.insts[2] = MachInst::new(M::CmpRI, vec![r(12, carrier), O::Imm(0)]);
    let select = machine.push_inst(MachInst::new(
        M::Csel,
        vec![
            r(13, bits),
            r(9, bits),
            r(10, bits),
            O::Imm(i64::from(selector == IntCC::NotEqual)),
        ],
    ));
    let stale_result = machine.push_inst(MachInst::new(
        M::Movz,
        vec![r(0, 64), O::Imm(1), O::Imm(32)],
    ));
    let result = machine.push_inst(MachInst::new(copy(bits), vec![r(0, bits), r(13, bits)]));
    machine.blocks[0].insts = vec![
        InstId(0),
        InstId(1),
        inputs[0],
        inputs[1],
        arms[0],
        arms[1],
        literal_inst,
        selector_copy,
        InstId(2),
        select,
        stale_result,
        result,
        InstId(3),
        InstId(4),
    ];
    (
        source,
        machine,
        SelectIds {
            inputs,
            arms,
            literal: literal_inst,
            selector_copy,
            cmp: InstId(2),
            select,
            stale_result,
            result,
        },
    )
}

#[derive(Clone, Copy)]
struct ReturnIds {
    selector_copy: InstId,
    stale_result: InstId,
    result: InstId,
}

/// No integer parameters or constants: both the existing affine frame and
/// raw owner choose their width-neutral I64 domain, while B1's return observes
/// the complete canonical X0. Live copies avoid an empty-credit raw body.
fn return_fixture(literal: i64, carrier: u32) -> (Function, MachFunction, ReturnIds) {
    let (_, mut machine) = crate::source_bound_alu::tests::fixture(64, M::AddRR, r(1, 64));
    let mut source = Function::new(
        "raw_bool_only_return",
        Signature {
            params: vec![],
            returns: vec![Type::B1],
        },
    );
    source.value_types.insert(Value(0), Type::B1);
    source.value_types.insert(Value(1), Type::B1);
    source.blocks.insert(
        source.entry_block,
        BasicBlock {
            instructions: vec![
                inst(
                    L::Iconst {
                        ty: Type::B1,
                        imm: literal,
                    },
                    &[],
                    Some(0),
                ),
                inst(L::Copy, &[0], Some(1)),
                inst(L::Return, &[1], None),
            ],
            ..Default::default()
        },
    );
    machine.name.clone_from(&source.name);
    machine.signature.params.clear();
    machine.signature.returns = vec![MachineType::B1];
    machine.insts[2] = MachInst::new(
        M::Movz,
        vec![r(9, if carrier == 32 { 64 } else { 32 }), O::Imm(literal)],
    );
    let selector_copy = machine.push_inst(MachInst::new(
        copy(carrier),
        vec![r(12, carrier), r(9, carrier)],
    ));
    let stale_result = machine.push_inst(MachInst::new(
        M::Movz,
        vec![r(0, 64), O::Imm(1), O::Imm(32)],
    ));
    let result = machine.push_inst(MachInst::new(
        copy(carrier),
        vec![r(0, carrier), r(12, carrier)],
    ));
    machine.blocks[0].insts = vec![
        InstId(0),
        InstId(1),
        InstId(2),
        selector_copy,
        stale_result,
        result,
        InstId(3),
        InstId(4),
    ];
    (
        source,
        machine,
        ReturnIds {
            selector_copy,
            stale_result,
            result,
        },
    )
}

fn raw(
    source: &Function,
    machine: &MachFunction,
) -> (ProofObligation, std::collections::HashSet<InstId>) {
    raw_body(
        source,
        machine,
        machine.blocks[0].insts.clone(),
        [InstId(0), InstId(1), InstId(3)],
    )
    .expect("bounded canonical Boolean raw model")
}

fn evaluate(obligation: &ProofObligation, a: u64, b: u64) -> (EvalResult, EvalResult) {
    let mut env = EvalEnv::default();
    env.insert("abi_x0".into(), a);
    env.insert("abi_x1".into(), b);
    (
        obligation.trust_ir_expr.eval(&env),
        obligation.aarch64_expr.eval(&env),
    )
}

#[test]
fn canonical_bool_literals_and_copies_select_nonidentity_integer_arms_at_both_widths() {
    let mut cases = 0;
    for bits in [32, 64] {
        for literal in [0, 1] {
            for selector in [IntCC::Equal, IntCC::NotEqual] {
                for carrier in [32, 64] {
                    let (source, machine, ids) = selector_fixture(bits, literal, selector, carrier);
                    let frame = source_bound_frame(&source, &machine)
                        .expect("canonical literal/copy selector frame");
                    let body = SourceBoundBody::bind(&frame)
                        .expect("nonidentity canonical literal selector");
                    assert_eq!(
                        body.category(),
                        crate::proof_database::ProofCategory::Arithmetic
                    );
                    assert!(!body.obligation().is_degenerate());
                    let live = [
                        ids.inputs[0],
                        ids.inputs[1],
                        ids.selector_copy,
                        ids.cmp,
                        ids.select,
                        ids.result,
                    ]
                    .into_iter()
                    .collect();
                    assert_eq!(raw(&source, &machine).1, live);
                    for id in [ids.literal, ids.arms[0], ids.arms[1], ids.stale_result] {
                        assert!(!body.credits(id));
                    }
                    for a in [
                        0,
                        1,
                        u32::MAX as u64,
                        1 << 32,
                        i64::MAX as u64,
                        1 << 63,
                        u64::MAX,
                    ] {
                        for b in [0, 1, u32::MAX as u64, (1 << 32) + 1, u64::MAX] {
                            let take_then = (literal == 1) ^ (selector == IntCC::Equal);
                            let want = if take_then {
                                a.wrapping_add(1)
                            } else {
                                b.wrapping_sub(1)
                            };
                            let want =
                                EvalResult::Bv(if bits == 32 { want as u32 as u64 } else { want });
                            assert_eq!(
                                evaluate(body.obligation(), a, b),
                                (want.clone(), want),
                                "i{bits}/literal{literal}/{selector:?}/carrier{carrier}/{a:#x}/{b:#x}"
                            );
                        }
                    }
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 16);
}

#[test]
fn boolean_only_constant_copy_returns_use_existing_neutral_domain_and_canonical_full_x0() {
    for literal in [0, 1] {
        for carrier in [32, 64] {
            let (source, machine, ids) = return_fixture(literal, carrier);
            let frame = source_bound_frame(&source, &machine)
                .expect("Boolean-only frame domain already supported");
            let body = SourceBoundBody::bind(&frame)
                .expect("raw neutral-domain Boolean literal/copy return");
            assert_eq!(
                body.category(),
                crate::proof_database::ProofCategory::Comparison
            );
            let obligation = body.obligation();
            assert!(!obligation.is_degenerate());
            assert!(obligation.inputs.is_empty());
            assert_eq!(obligation.trust_ir_expr.bv_width(), 64);
            assert_eq!(obligation.aarch64_expr.bv_width(), 64);
            let want = EvalResult::Bv(literal as u64);
            assert_eq!(
                evaluate(obligation, u64::MAX, u64::MAX),
                (want.clone(), want)
            );
            assert_eq!(
                raw(&source, &machine).1,
                [ids.selector_copy, ids.result].into_iter().collect()
            );
            assert!(!body.credits(ids.stale_result));
            assert!(
                !body.credits(InstId(2)),
                "constant row belongs to the separate constant owner"
            );
            let query = crate::serialize_to_smt2(obligation);
            assert!(query.contains("zero_extend 63"));
            assert!(
                query.contains("zero_extend 32"),
                "actual W writes clear X upper bits even in neutral I64 source domain"
            );
        }
    }
}

#[test]
fn canonical_literal_parameter_selections_remain_refused_as_source_identities() {
    for bits in [32, 64] {
        for literal in [0, 1] {
            for selector in [IntCC::Equal, IntCC::NotEqual] {
                let (mut source, mut machine, ids) = selector_fixture(bits, literal, selector, 32);
                source
                    .blocks
                    .get_mut(&source.entry_block)
                    .unwrap()
                    .instructions[5]
                    .args = vec![Value(6), Value(0), Value(1)];
                for id in ids.arms {
                    machine.insts[id.0 as usize] = MachInst::new(M::Nop, vec![]);
                }
                let frame = source_bound_frame(&source, &machine)
                    .expect("correct parameter identity frame");
                assert!(
                    SourceBoundBody::bind(&frame).is_none(),
                    "literal selector must not bypass source parameter-identity refusal"
                );
            }
        }
    }
}

#[test]
fn noncanonical_source_bool_literal_and_boolean_arithmetic_fail_closed() {
    for bits in [32, 64] {
        let (source, machine, _) = selector_fixture(bits, 0, IntCC::NotEqual, 32);
        for mutation in 0..3 {
            let mut wrong = source.clone();
            let block = wrong.blocks.get_mut(&wrong.entry_block).unwrap();
            match mutation {
                0 => {
                    block.instructions[3].opcode = L::Iconst {
                        ty: Type::B1,
                        imm: 2,
                    }
                }
                1 => block.instructions[4] = inst(L::Iadd, &[5, 5], Some(6)),
                _ => block.instructions[4] = inst(L::Icmp { cond: IntCC::Equal }, &[5, 5], Some(6)),
            }
            assert!(source_bound_frame(&wrong, &machine).is_err());
            assert!(
                raw_body(
                    &wrong,
                    &machine,
                    machine.blocks[0].insts.clone(),
                    [InstId(0), InstId(1), InstId(3)]
                )
                .is_none(),
                "malformed Boolean source case {mutation} is refusal, not semantic refutation credit"
            );
        }
    }
    for carrier in [32, 64] {
        let (mut source, machine, _) = return_fixture(1, carrier);
        source
            .blocks
            .get_mut(&source.entry_block)
            .unwrap()
            .instructions[0]
            .opcode = L::Iconst {
            ty: Type::B1,
            imm: 2,
        };
        assert!(source_bound_frame(&source, &machine).is_err());
        assert!(
            raw_body(
                &source,
                &machine,
                machine.blocks[0].insts.clone(),
                [InstId(0), InstId(1), InstId(3)]
            )
            .is_none()
        );
    }
}

#[test]
fn boolean_only_raw_residual_refutes_noncanonical_upper_x0_bits_after_return_copy() {
    for literal in [0, 1] {
        for carrier in [32, 64] {
            let (source, machine, _) = return_fixture(literal, carrier);
            let correct = raw(&source, &machine).0;
            let mut wrong = machine.clone();
            let high = wrong.push_inst(MachInst::new(
                M::Movz,
                vec![r(14, 64), O::Imm(1), O::Imm(32)],
            ));
            let corrupt =
                wrong.push_inst(MachInst::new(M::AddRR, vec![r(0, 64), r(0, 64), r(14, 64)]));
            let before_restore = wrong.blocks[0]
                .insts
                .iter()
                .position(|&id| id == InstId(3))
                .unwrap();
            wrong.blocks[0]
                .insts
                .splice(before_restore..before_restore, [high, corrupt]);
            assert!(source_bound_frame(&source, &wrong).is_err());
            let obligation = raw(&source, &wrong).0;
            assert!(!obligation.is_degenerate());
            assert_ne!(
                crate::serialize_to_smt2(&correct),
                crate::serialize_to_smt2(&obligation)
            );
            assert_eq!(
                evaluate(&obligation, 0, 0),
                (
                    EvalResult::Bv(literal as u64),
                    EvalResult::Bv((1 << 32) + literal as u64)
                ),
                "actual upper-bit corruption must refute raw canonical return, not merely cause frame refusal"
            );
            println!(
                "A64_RAW_BOOL_COUNTEREXAMPLE literal={literal} carrier={carrier} source={} machine={}",
                literal,
                (1u64 << 32) + literal as u64
            );
        }
    }
}

#[test]
fn boolean_only_raw_returns_require_positive_independent_ay_clean_replay() {
    use crate::function_request::FunctionDischargeContext;
    use crate::provenance_xcheck::ProvenanceXCheckMode;
    use crate::verify::VerificationResult;
    use crate::{FunctionVerifier, VerificationConfig};
    crate::env_lock::with_env_overrides(
        &[
            ("TCG_REFINE_SOLVER", "1"),
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            for literal in [0, 1] {
                for carrier in [32, 64] {
                    let (source, machine, _) = return_fixture(literal, carrier);
                    let frame = source_bound_frame(&source, &machine)
                        .expect("canonical Boolean-only frame");
                    let body = SourceBoundBody::bind(&frame).expect("raw Boolean-only owner");
                    let result = FunctionDischargeContext::new(&request).a64_body(&body);
                    assert!(
                        matches!(result, Some(VerificationResult::Valid)),
                        "required independent Boolean-only AY/Clean replay literal{literal}/carrier{carrier}: {result:?}; concrete evaluation is not proof evidence"
                    );
                }
            }
        },
    );
}
