// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Negative controls for exact Core source, both original arms, and actual
//! final A64 words. These semantic owners are not certificates or publication
//! authority. The separately retained native test remains explicitly Unchecked.

use super::diamond_tests::{CONDITIONS, LEVELS, TARGETS, prepare, source, translate};
use super::*;
use crate::pipeline::{OptLevel, Pipeline, PipelineConfig, PipelineError};
use trust_cg_ir::{AArch64Opcode as M, MachFunction, MachInst};
use trust_cg_lower::Function;
use trust_cg_verify::aarch64_affine_lowering::check_aarch64_trust_ir_affine_lowering;
use trust_ir::{Constant, ICmpOp, Inst, InstrNode, Module, ProofAnnotation, Ty, ValueId};

fn encoded(module: &Module, lir: &Function, machine: &MachFunction) -> Vec<u8> {
    let (code, fixups, sites) = encode_core_function(module, 0, lir, machine)
        .expect("original connected Core diamond must encode and check");
    assert!(fixups.is_empty() && sites.is_empty());
    assert!(check_aarch64_trust_ir_affine_bytes(module, 0, lir, &code).is_ok());
    code
}

fn invalid_source(
    module: &Module,
    lir: &Function,
    machine: &MachFunction,
    code: &[u8],
    label: &str,
) {
    assert!(
        matches!(
            check_aarch64_trust_ir_affine_lowering(module, 0, lir, machine),
            Err(TrustIrAffineLoweringError::InvalidTrustIr(_))
        ),
        "{label}: malformed original source must fail before target inspection"
    );
    assert!(
        matches!(
            check_aarch64_trust_ir_affine_bytes(module, 0, lir, code),
            Err(AffineByteError::Source(
                TrustIrAffineLoweringError::InvalidTrustIr(_)
            ))
        ),
        "{label}: malformed original source must not become unsupported-source credit"
    );
    assert!(matches!(
        check_core_bytes(module, 0, lir, code, &FixupList::new()),
        Err(CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. })
    ));
}

fn source_gap(module: &Module, lir: &Function, machine: &MachFunction, code: &[u8], reason: &str) {
    assert!(
        matches!(
            check_aarch64_trust_ir_affine_lowering(module, 0, lir, machine),
            Err(TrustIrAffineLoweringError::UnsupportedTrustIr(detail)) if detail.contains(reason)
        ),
        "original source-domain gap {reason} must remain explicit"
    );
    assert!(matches!(
        check_aarch64_trust_ir_affine_bytes(module, 0, lir, code),
        Err(AffineByteError::Source(TrustIrAffineLoweringError::UnsupportedTrustIr(detail)))
            if detail.contains(reason)
    ));
}

#[test]
fn sealed_core_diamond_rejects_correlated_lir_and_machine_substitution_before_optimization() {
    let mut controls = 0;
    for ty in [Ty::I32, Ty::I64] {
        for condition in CONDITIONS {
            let module = source(ty.clone(), condition);
            let lir = translate(&module);
            let (_, proofs) = trust_cg_lower::translate_function_with_license(
                &module.functions[0],
                &module,
                &crate::license_test_support::permit_unlicensed(),
            )
            .unwrap();
            for target in TARGETS {
                for level in LEVELS {
                    let original = prepare(target, &module, &lir, level);
                    let _code = encoded(&module, &lir, &original);
                    for arm in [1, 2] {
                        let mut wrong = lir.clone();
                        let block = wrong.block_order[arm];
                        let operation = wrong
                            .blocks
                            .get_mut(&block)
                            .unwrap()
                            .instructions
                            .iter_mut()
                            .find(|i| {
                                matches!(
                                    i.opcode,
                                    trust_cg_lower::instructions::Opcode::Iadd
                                        | trust_cg_lower::instructions::Opcode::Isub
                                )
                            })
                            .unwrap();
                        operation.opcode =
                            if operation.opcode == trust_cg_lower::instructions::Opcode::Iadd {
                                trust_cg_lower::instructions::Opcode::Isub
                            } else {
                                trust_cg_lower::instructions::Opcode::Iadd
                            };
                        // Actual ISel follows this corrupted LIR. Only the
                        // independently retained original Core prevents the
                        // correlated source/target substitution.
                        let result = Pipeline::new(PipelineConfig {
                            opt_level: level,
                            verify: false,
                            target_triple: target.into(),
                            ..Default::default()
                        })
                        .prepare_function_with_metrics_for_sealed_core(
                            &wrong,
                            Some(&proofs),
                            &module,
                            0,
                        );
                        assert!(
                            matches!(
                                result,
                                Err(PipelineError::AffineLoweringRejected {
                                    reason: TrustIrAffineLoweringError::TrustIrLirMismatch,
                                    ..
                                })
                            ),
                            "original Core i{ty:?}/{condition:?}/{target}/{level:?}/arm{arm} must reject correlated target: {result:?}"
                        );
                        controls += 1;
                    }
                }
            }
        }
    }
    assert_eq!(controls, 320);
}

#[test]
fn original_diamond_proof_context_and_guard_semantics_cannot_be_erased_by_lowering() {
    let mut contexts = 0;
    for ty in [Ty::I32, Ty::I64] {
        let module = source(ty.clone(), ICmpOp::Ult);
        let lir = translate(&module);
        let machine = prepare(TARGETS[0], &module, &lir, OptLevel::O0);
        let code = encoded(&module, &lir, &machine);
        for block in 0..4 {
            for node in 0..module.functions[0].blocks[block].body.len() {
                let mut changed = module.clone();
                changed.functions[0].blocks[block].body[node].proof_context =
                    Some(Default::default());
                invalid_source(
                    &changed,
                    &lir,
                    &machine,
                    &code,
                    "non-call proof context on original node",
                );
                contexts += 1;
            }
        }
        let mut guarded = module.clone();
        guarded.functions[0].blocks[0].body[0]
            .proofs
            .push(ProofAnnotation::InBounds);
        let (guard_lir, _) = trust_cg_lower::translate_function_with_license(
            &guarded.functions[0],
            &guarded,
            &crate::license_test_support::permit_unlicensed(),
        )
        .unwrap();
        assert!(
            guard_lir
                .blocks
                .values()
                .flat_map(|b| &b.instructions)
                .any(|i| matches!(
                    i.opcode,
                    trust_cg_lower::instructions::Opcode::GuardBoundsCheckDyn { .. }
                )),
            "the ordinary adapter retains the actual guard, not just metadata"
        );
        source_gap(&guarded, &lir, &machine, &code, "InBounds");
        // Claiming an unrelated proof annotation neither changes source
        // operational semantics nor supplies solver/replay authority.
        let mut hinted = module.clone();
        hinted.functions[0].blocks[0].body[1]
            .proofs
            .push(ProofAnnotation::BranchWeights(vec![1, 99]));
        let hinted_lir = translate(&hinted);
        let hinted_machine = prepare(TARGETS[1], &hinted, &hinted_lir, OptLevel::O2);
        let _ = encoded(&hinted, &hinted_lir, &hinted_machine);
    }
    assert_eq!(contexts, 22);
}

fn malformed_arm(module: &mut Module, arm: usize, mutation: usize) -> &'static str {
    let condition = module.functions[0].blocks[0].body[0].results[0];
    let body = &mut module.functions[0].blocks[arm].body;
    match mutation {
        0 => {
            let Inst::BinOp { lhs, .. } = &mut body[1].inst else {
                panic!("arithmetic arm")
            };
            *lhs = ValueId::new(99_999);
            "undefined arithmetic operand"
        }
        1 => {
            let Inst::BinOp { lhs, .. } = &mut body[1].inst else {
                panic!("arithmetic arm")
            };
            *lhs = condition;
            "Boolean used as integer operand"
        }
        2 => {
            let Inst::Const { value, .. } = &mut body[0].inst else {
                panic!("arm constant")
            };
            *value = Constant::Bool(true);
            "wrong literal carrier"
        }
        3 => {
            let Inst::Const { value, .. } = &mut body[0].inst else {
                panic!("arm constant")
            };
            *value = Constant::Int(i128::MAX);
            "out-of-range source literal"
        }
        4 => {
            body[1].results.clear();
            "missing arithmetic SSA result"
        }
        5 => {
            let Inst::Br { args, .. } = &mut body[3].inst else {
                panic!("arm merge edge")
            };
            args.clear();
            "missing merge argument"
        }
        6 => {
            let Inst::Br { args, .. } = &mut body[3].inst else {
                panic!("arm merge edge")
            };
            args.push(args[0]);
            "extra merge argument"
        }
        7 => {
            let Inst::Br { args, .. } = &mut body[3].inst else {
                panic!("arm merge edge")
            };
            args[0] = condition;
            "Boolean merge argument for integer join"
        }
        8 => {
            let duplicate = body[0].results[0];
            body[1].results[0] = duplicate;
            "duplicate SSA definition within arm"
        }
        _ => {
            body[3].results.push(ValueId::new(80_000));
            "SSA result on resultless arm terminator"
        }
    }
}

#[test]
fn original_core_diamond_validates_each_arm_ssa_types_and_merge_arguments() {
    let mut controls = 0;
    for ty in [Ty::I32, Ty::I64] {
        let module = source(ty, ICmpOp::Slt);
        let lir = translate(&module);
        let machine = prepare(TARGETS[0], &module, &lir, OptLevel::O0);
        let code = encoded(&module, &lir, &machine);
        for arm in [1, 2] {
            for mutation in 0..10 {
                let mut wrong = module.clone();
                let label = malformed_arm(&mut wrong, arm, mutation);
                invalid_source(&wrong, &lir, &machine, &code, label);
                controls += 1;
            }
        }
        let mut cross_arm = module.clone();
        cross_arm.functions[0].blocks[2].body[0].results[0] =
            module.functions[0].blocks[1].body[0].results[0];
        invalid_source(
            &cross_arm,
            &lir,
            &machine,
            &code,
            "duplicate SSA identity across disjoint arms",
        );
        controls += 1;
        let mut cross_use = module.clone();
        let from_other_arm = module.functions[0].blocks[1].body[1].results[0];
        let Inst::BinOp { lhs, .. } = &mut cross_use.functions[0].blocks[2].body[1].inst else {
            panic!("arm arithmetic")
        };
        *lhs = from_other_arm;
        invalid_source(
            &cross_use,
            &lir,
            &machine,
            &code,
            "use of value from non-dominating other arm",
        );
        controls += 1;
        let mut entry_args = module.clone();
        let argument = module.functions[0].blocks[0].params[0].0;
        let Inst::CondBr { then_args, .. } = &mut entry_args.functions[0].blocks[0].body[1].inst
        else {
            panic!("conditional entry edge")
        };
        then_args.push(argument);
        invalid_source(
            &entry_args,
            &lir,
            &machine,
            &code,
            "entry edge has extra arm argument",
        );
        controls += 1;
    }
    assert_eq!(controls, 46);
}

#[test]
fn constant_untaken_original_arm_still_requires_valid_ssa_type_edge_and_guard_contracts() {
    let mut controls = 0;
    for ty in [Ty::I32, Ty::I64] {
        for taken in [false, true] {
            let mut module = source(ty.clone(), ICmpOp::Ne);
            module.functions[0].blocks[0].body[0].inst = Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(taken),
            };
            let lir = translate(&module);
            let machine = prepare(TARGETS[0], &module, &lir, OptLevel::O0);
            let code = encoded(&module, &lir, &machine);
            let untaken = if taken { 2 } else { 1 };
            for mutation in 0..10 {
                let mut wrong = module.clone();
                let label = malformed_arm(&mut wrong, untaken, mutation);
                invalid_source(&wrong, &lir, &machine, &code, label);
                controls += 1;
            }
            let mut context = module.clone();
            context.functions[0].blocks[untaken].body[1].proof_context = Some(Default::default());
            invalid_source(
                &context,
                &lir,
                &machine,
                &code,
                "non-call proof context in constant-untaken arm",
            );
            controls += 1;
            let mut guarded = module.clone();
            let args = &module.functions[0].blocks[0].params;
            let mut guard = InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ult,
                ty: ty.clone(),
                lhs: args[0].0,
                rhs: args[1].0,
            })
            .with_result(ValueId::new(50_000));
            guard.proofs.push(ProofAnnotation::InBounds);
            guarded.functions[0].blocks[untaken].body.insert(0, guard);
            source_gap(&guarded, &lir, &machine, &code, "InBounds");
            controls += 1;
        }
    }
    assert_eq!(controls, 48);
}

fn words(code: &[u8]) -> Vec<(usize, u32)> {
    let (words, remainder) = code.as_chunks::<4>();
    assert!(remainder.is_empty(), "complete A64 instruction words");
    words
        .iter()
        .enumerate()
        .map(|(n, w)| (n * 4, u32::from_le_bytes(*w)))
        .collect()
}
fn only_word(code: &[u8], predicate: impl Fn(u32) -> bool) -> (usize, u32) {
    let found = words(code)
        .into_iter()
        .filter(|&(_, w)| predicate(w))
        .collect::<Vec<_>>();
    assert_eq!(
        found.len(),
        1,
        "one actual instruction is required: {found:#x?}"
    );
    found[0]
}
fn conditional(word: u32) -> bool {
    word & 0xff00_0010 == 0x5400_0000 || word & 0x7e00_0000 == 0x3400_0000
}
fn branch_target(offset: usize, word: u32) -> usize {
    let immediate = ((word >> 5) & 0x7ffff) as i32;
    let signed = (immediate << 13) >> 13;
    usize::try_from(offset as i64 + i64::from(signed) * 4).expect("original target inside code")
}
fn reject_code(module: &Module, lir: &Function, original: &[u8], changed: &[u8], label: &str) {
    assert_ne!(original, changed, "{label}: mutate actual bytes");
    let result = check_aarch64_trust_ir_affine_bytes(module, 0, lir, changed);
    assert!(
        matches!(
            result,
            Err(AffineByteError::InvalidBytes { .. }
                | AffineByteError::UnsupportedBytes { .. }
                | AffineByteError::ReturnMismatch)
        ),
        "{label}: supported Core/LIR must fail at target, not downgrade source coverage: {result:?}"
    );
    assert!(matches!(
        check_core_bytes(module, 0, lir, changed, &FixupList::new()),
        Err(CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. })
    ));
}
fn reject_word(
    module: &Module,
    lir: &Function,
    original: &[u8],
    offset: usize,
    word: u32,
    label: &str,
) {
    let mut changed = original.to_vec();
    changed[offset..offset + 4].copy_from_slice(&word.to_le_bytes());
    reject_code(module, lir, original, &changed, label);
}

#[test]
fn actual_encoded_diamond_words_bind_branches_both_arms_frame_and_complete_footer() {
    let mut cases = 0;
    let mut controls = 0;
    for ty in [Ty::I32, Ty::I64] {
        for condition in CONDITIONS {
            let module = source(ty.clone(), condition);
            let lir = translate(&module);
            for target in TARGETS {
                let machine = prepare(target, &module, &lir, OptLevel::O0);
                let code = encoded(&module, &lir, &machine);
                let (cmp_at, cmp) = only_word(&code, |w| w & 0x7fe0_fc1f == 0x6b00_001f);
                let lhs = (cmp >> 5) & 31;
                let rhs = (cmp >> 16) & 31;
                assert_ne!(lhs, rhs);
                reject_word(
                    &module,
                    &lir,
                    &code,
                    cmp_at,
                    (cmp & !(31 << 16)) | lhs << 16,
                    "actual compare operand",
                );
                reject_word(
                    &module,
                    &lir,
                    &code,
                    cmp_at,
                    cmp ^ (1 << 31),
                    "actual compare width",
                );
                reject_word(
                    &module,
                    &lir,
                    &code,
                    cmp_at,
                    0xd503_201f,
                    "missing reaching NZCV producer",
                );
                controls += 3;
                let (branch_at, branch) = only_word(&code, conditional);
                let sense_bit = if branch & 0xff00_0010 == 0x5400_0000 {
                    1
                } else {
                    1 << 24
                };
                reject_word(
                    &module,
                    &lir,
                    &code,
                    branch_at,
                    branch ^ sense_bit,
                    "actual branch sense",
                );
                reject_word(
                    &module,
                    &lir,
                    &code,
                    branch_at,
                    branch & !(0x7ffff << 5),
                    "self branch target",
                );
                let outside = ((code.len() - branch_at) / 4 + 1) as u32;
                reject_word(
                    &module,
                    &lir,
                    &code,
                    branch_at,
                    (branch & !(0x7ffff << 5)) | outside << 5,
                    "branch target outside exact allocation",
                );
                let target_at = branch_target(branch_at, branch);
                let fallthrough_at = branch_at + 4;
                let delta = ((target_at as i64 - fallthrough_at as i64) / 4) as u32 & 0x03ff_ffff;
                reject_word(
                    &module,
                    &lir,
                    &code,
                    fallthrough_at,
                    0x1400_0000 | delta,
                    "fallthrough routed to taken arm",
                );
                controls += 4;
                for subtract in [false, true] {
                    let (at, arithmetic) = only_word(&code, |w| {
                        let operation = if subtract { 0x5100_0000 } else { 0x1100_0000 };
                        let register = if subtract { 0x4b00_0000 } else { 0x0b00_0000 };
                        ((w & 0x7f00_0000 == operation) || (w & 0x7f20_0000 == register))
                            && (w >> 5) & 31 != 31
                            && w & 31 != 29
                    });
                    reject_word(
                        &module,
                        &lir,
                        &code,
                        at,
                        arithmetic ^ (1 << 30),
                        if subtract {
                            "actual else arithmetic arm"
                        } else {
                            "actual then arithmetic arm"
                        },
                    );
                    controls += 1;
                }
                let (save_at, save) = only_word(&code, |w| w & 0xffc0_0000 == 0xa980_0000);
                reject_word(&module, &lir, &code, save_at, save ^ 1, "saved frame pair");
                let (establish_at, _) = only_word(&code, |w| w == 0x9100_03fd);
                reject_word(
                    &module,
                    &lir,
                    &code,
                    establish_at,
                    0xd503_201f,
                    "frame establishment",
                );
                let (restore_at, restore) = only_word(&code, |w| w & 0xffc0_0000 == 0xa8c0_0000);
                reject_word(
                    &module,
                    &lir,
                    &code,
                    restore_at,
                    restore ^ 1,
                    "restored frame pair",
                );
                let (ret_at, ret) = only_word(&code, |w| w & 0xffff_fc1f == 0xd65f_0000);
                reject_word(
                    &module,
                    &lir,
                    &code,
                    ret_at,
                    ret ^ (1 << 5),
                    "actual return register",
                );
                controls += 4;
                let mut footer = code.clone();
                footer.extend_from_slice(&0xd503_201fu32.to_le_bytes());
                reject_code(
                    &module,
                    &lir,
                    &code,
                    &footer,
                    "unowned word after complete return footer",
                );
                controls += 1;
                let mut unsupported = code.clone();
                unsupported[cmp_at..cmp_at + 4].copy_from_slice(&0x9b02_7c20u32.to_le_bytes()); // MUL X0,X1,X2.
                assert!(
                    matches!(check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &unsupported),
                    Err(AffineByteError::UnsupportedBytes { offset, word: 0x9b02_7c20 }) if offset == cmp_at)
                );
                reject_code(
                    &module,
                    &lir,
                    &code,
                    &unsupported,
                    "unsupported target instruction is a typed hard refusal",
                );
                controls += 1;
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 40);
    assert_eq!(controls, 600);
}

#[test]
fn actual_encoded_overwriting_compare_replaces_nzcv_instead_of_reusing_source_flags() {
    let mut controls = 0;
    for ty in [Ty::I32, Ty::I64] {
        for condition in CONDITIONS {
            let module = source(ty.clone(), condition);
            let lir = translate(&module);
            for target in TARGETS {
                let original = prepare(target, &module, &lir, OptLevel::O0);
                let code = encoded(&module, &lir, &original);
                let mut changed = original.clone();
                let (block, at, cmp) = changed
                    .blocks
                    .iter()
                    .enumerate()
                    .find_map(|(b, block)| {
                        block
                            .insts
                            .iter()
                            .enumerate()
                            .find(|&(_, id)| changed.inst(*id).opcode == M::CmpRR)
                            .map(|(at, id)| (b, at, *id))
                    })
                    .unwrap();
                let lhs = changed.inst(cmp).operands[0].clone();
                let overwrite = changed.push_inst(MachInst::new(M::CmpRR, vec![lhs.clone(), lhs]));
                changed.blocks[block].insts.insert(at + 1, overwrite);
                let (wrong_code, fixups, sites) =
                    crate::pipeline::encode_function_with_fixups_and_sites(&changed).unwrap();
                assert!(fixups.is_empty() && sites.is_empty());
                assert_eq!(
                    words(&wrong_code)
                        .iter()
                        .filter(|&&(_, w)| w & 0x7fe0_fc1f == 0x6b00_001f)
                        .count(),
                    2
                );
                reject_code(
                    &module,
                    &lir,
                    &code,
                    &wrong_code,
                    "actual overwritten reaching NZCV",
                );
                controls += 1;
            }
        }
    }
    assert_eq!(controls, 40);
}

#[test]
fn supported_core_diamond_cannot_downgrade_through_unsupported_lir() {
    use trust_cg_lower::instructions::Opcode as L;
    for ty in [Ty::I32, Ty::I64] {
        let module = source(ty, ICmpOp::Slt);
        let lir = translate(&module);
        let machine = prepare(TARGETS[0], &module, &lir, OptLevel::O0);
        let code = encoded(&module, &lir, &machine);
        let mut wrong_lir = lir.clone();
        wrong_lir
            .blocks
            .values_mut()
            .flat_map(|b| &mut b.instructions)
            .find(|i| i.opcode == L::Iadd)
            .unwrap()
            .opcode = L::Imul;
        assert!(matches!(
            check_aarch64_trust_ir_affine_lowering(&module, 0, &wrong_lir, &machine),
            Err(TrustIrAffineLoweringError::Lowering(_))
        ));
        assert!(matches!(
            check_aarch64_trust_ir_affine_bytes(&module, 0, &wrong_lir, &code),
            Err(AffineByteError::Source(
                TrustIrAffineLoweringError::Lowering(_)
            ))
        ));
        assert!(matches!(
            check_core_bytes(&module, 0, &wrong_lir, &code, &FixupList::new()),
            Err(CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. })
        ));
    }
}

fn encoding_condition(condition: ICmpOp) -> u32 {
    match condition {
        ICmpOp::Eq => 0,
        ICmpOp::Ne => 1,
        ICmpOp::Slt => 11,
        ICmpOp::Sle => 13,
        ICmpOp::Sgt => 12,
        ICmpOp::Sge => 10,
        ICmpOp::Ult => 3,
        ICmpOp::Ule => 9,
        ICmpOp::Ugt => 8,
        ICmpOp::Uge => 2,
    }
}

/// Independent ISA vectors, not encoder output and not connected-runtime
/// credit. They exercise the public owner without any producer MachIR/stamp.
fn hand_words(bits: u32, condition: ICmpOp, route: usize) -> Vec<u8> {
    let cc = encoding_condition(condition);
    let sf = if bits == 64 { 1 << 31 } else { 0 };
    let mut instructions = vec![0xa9bf_7bfd, 0x9100_03fd, sf | 0x6b01_001f];
    if route == 0 {
        instructions.extend([0x5400_0000 | 2 << 5 | cc, 0x1400_0003]);
    } else {
        let carrier64 = route == 2 || route == 4;
        let zero = route == 3 || route == 4;
        let csf = if carrier64 { 1 << 31 } else { 0 };
        instructions.push(csf | 0x1a9f_07e9 | (cc ^ 1) << 12);
        instructions.push(csf | if zero { 0x3400_0089 } else { 0x3500_0049 });
        instructions.push(if zero { 0x1400_0001 } else { 0x1400_0003 });
    }
    instructions.extend([
        sf | 0x1100_0440, // ADD W/X0,W/X2,#1.
        0x1400_0003,
        sf | 0x5100_0460, // SUB W/X0,W/X3,#1.
        0x1400_0001,
        0xa8c1_7bfd,
        0xd65f_03c0,
    ]);
    instructions
        .into_iter()
        .flat_map(u32::to_le_bytes)
        .collect()
}

#[test]
fn independent_hand_words_cover_direct_and_materialized_diamond_routes_without_provenance() {
    let mut cases = 0;
    for (ty, bits) in [(Ty::I32, 32), (Ty::I64, 64)] {
        for condition in CONDITIONS {
            let module = source(ty.clone(), condition);
            let lir = translate(&module);
            for route in 0..5 {
                let code = hand_words(bits, condition, route);
                let checked = check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &code)
                    .unwrap_or_else(|error| {
                        panic!("independent words i{bits}/{condition:?}/route{route}: {error}")
                    });
                assert!(std::ptr::eq(checked.code(), code.as_slice()));
                assert!(std::ptr::eq(checked.module(), &module));
                assert_eq!(checked.statistics().machine_instructions, code.len() / 4);
                assert_eq!(checked.statistics().private_stack_bytes, 16);
                // Insert actual CMP a,a after CMP a,b and before its consumer.
                // Every relative branch and target shifts together, preserving
                // topology while independently changing reaching NZCV.
                let mut wrong = code.clone();
                let cmp_equal = if bits == 64 {
                    0xeb00_001fu32
                } else {
                    0x6b00_001fu32
                };
                wrong.splice(12..12, cmp_equal.to_le_bytes());
                reject_code(
                    &module,
                    &lir,
                    &code,
                    &wrong,
                    "independent word overwritten NZCV",
                );
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 100);
}

#[test]
fn original_diamond_source_node_budget_admits_256_declines_257_and_rejects_multiple_results() {
    for (ty, bits) in [(Ty::I32, 32), (Ty::I64, 64)] {
        let original = source(ty.clone(), ICmpOp::Eq);
        let lir = translate(&original);
        let machine = prepare(TARGETS[0], &original, &lir, OptLevel::O0);
        let code = hand_words(bits, ICmpOp::Eq, 0);
        let mut bounded = original.clone();
        let initial = bounded.functions[0]
            .blocks
            .iter()
            .map(|b| b.body.len())
            .sum::<usize>();
        assert_eq!(initial, 11);
        let dead = (0..256 - initial)
            .map(|n| {
                InstrNode::new(Inst::Const {
                    ty: ty.clone(),
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(100_000 + n as u32))
            })
            .collect::<Vec<_>>();
        let arm = &mut bounded.functions[0].blocks[1].body;
        arm.splice(arm.len() - 1..arm.len() - 1, dead);
        assert_eq!(
            bounded.functions[0]
                .blocks
                .iter()
                .map(|b| b.body.len())
                .sum::<usize>(),
            256
        );
        // This is a source-profile component control, not a claim that 256
        // nodes were compiled or executed. Its dead pure constants need no
        // large target: the independent small byte vector has the same result.
        let checked = check_aarch64_trust_ir_affine_bytes(&bounded, 0, &lir, &code)
            .expect("exact bounded original source remains admitted");
        assert_eq!(checked.statistics().trust_ir_instructions, 256);
        assert_eq!(checked.statistics().machine_instructions, 11);
        assert!(std::ptr::eq(checked.source(), &bounded.functions[0]));

        let mut excessive = bounded.clone();
        let arm = &mut excessive.functions[0].blocks[2].body;
        arm.insert(
            arm.len() - 1,
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(900_000)),
        );
        assert_eq!(
            excessive.functions[0]
                .blocks
                .iter()
                .map(|b| b.body.len())
                .sum::<usize>(),
            257
        );
        source_gap(&excessive, &lir, &machine, &code, "256 source instructions");

        // Multiple SSA outputs are malformed even below the resource bound;
        // they must not be disguised as unsupported source-domain coverage.
        for block in 0..4 {
            let mut malformed = bounded.clone();
            let node = &mut malformed.functions[0].blocks[block].body[0];
            while node.results.len() < 2 {
                node.results
                    .push(ValueId::new(950_000 + node.results.len() as u32));
            }
            invalid_source(
                &malformed,
                &lir,
                &machine,
                &code,
                "multiple scalar SSA results inside the 256-node bound",
            );
        }
    }
}

#[test]
fn original_diamond_arm_parameter_profile_is_distinct_from_malformed_edge_arity() {
    for ty in [Ty::I32, Ty::I64] {
        let module = source(ty.clone(), ICmpOp::Slt);
        let lir = translate(&module);
        let machine = prepare(TARGETS[0], &module, &lir, OptLevel::O0);
        let bits = if ty == Ty::I32 { 32 } else { 64 };
        let code = hand_words(bits, ICmpOp::Slt, 0);
        for arm in [1, 2] {
            let argument = module.functions[0].blocks[0].params[0].0;
            let mut parameterized = module.clone();
            parameterized.functions[0].blocks[arm].params =
                vec![(ValueId::new(800_000), ty.clone())];
            let Inst::CondBr {
                then_args,
                else_args,
                ..
            } = &mut parameterized.functions[0].blocks[0].body[1].inst
            else {
                panic!("entry conditional edge")
            };
            if arm == 1 {
                then_args.push(argument);
            } else {
                else_args.push(argument);
            }
            source_gap(&parameterized, &lir, &machine, &code, "arm parameters");

            let mut malformed = parameterized.clone();
            malformed.functions[0].blocks[arm].params.clear();
            invalid_source(
                &malformed,
                &lir,
                &machine,
                &code,
                "extra argument for an empty-parameter arm",
            );
            let mut missing = parameterized;
            let Inst::CondBr {
                then_args,
                else_args,
                ..
            } = &mut missing.functions[0].blocks[0].body[1].inst
            else {
                panic!("entry conditional edge")
            };
            if arm == 1 {
                then_args.clear();
            } else {
                else_args.clear();
            }
            invalid_source(
                &missing,
                &lir,
                &machine,
                &code,
                "missing argument for a parameterized arm",
            );

            let mut oversized = module.clone();
            oversized.functions[0].blocks[arm].params = (0..9)
                .map(|n| (ValueId::new(810_000 + n), ty.clone()))
                .collect();
            let Inst::CondBr {
                then_args,
                else_args,
                ..
            } = &mut oversized.functions[0].blocks[0].body[1].inst
            else {
                panic!("entry conditional edge")
            };
            if arm == 1 {
                *then_args = vec![argument; 9];
            } else {
                *else_args = vec![argument; 9];
            }
            source_gap(
                &oversized,
                &lir,
                &machine,
                &code,
                "exceeds eight block parameters",
            );
            // Poison the global SSA namespace as an ordering control: an
            // oversized parameter vector must be bounded before global
            // definition collection, rather than allocating/traversing it.
            oversized.functions[0].blocks[arm].params[0].0 = argument;
            source_gap(
                &oversized,
                &lir,
                &machine,
                &code,
                "exceeds eight block parameters",
            );
        }
    }
}

#[test]
fn i64_diamond_w_branch_requires_a_defined_canonical_boolean_not_an_incoming_integer() {
    let mut admitted = 0;
    let mut refusals = 0;
    // These are independent byte-owner controls. The existing constant-arm
    // test still uses actual sealed-Core preparation and requires Checked;
    // this component test must never substitute for that connected path.
    for condition in CONDITIONS {
        let module = source(Ty::I64, condition);
        let lir = translate(&module);
        for route in [1, 3] {
            let code = hand_words(64, condition, route); // CSET W9, then CBNZ/CBZ W9.
            assert!(check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &code).is_ok());
            let (at, branch) = only_word(&code, conditional);
            assert_eq!(branch >> 31, 0, "the actual branch reads W, not X");
            assert_eq!(branch & 31, 9);
            admitted += 1;
            for incoming in [0, 2] {
                // An I64 ABI input has an arbitrary upper half and is not a
                // canonical Boolean. CSET's unrelated W9 definition must not
                // license truncating/reinterpreting incoming X0 or X2 as Bool.
                reject_word(
                    &module,
                    &lir,
                    &code,
                    at,
                    (branch & !31) | incoming,
                    "I64 incoming integer is not a canonical W Boolean",
                );
                refusals += 1;
            }
            let mut undefined = code.clone();
            undefined[at..at + 4].copy_from_slice(&((branch & !31) | 10).to_le_bytes());
            assert!(
                matches!(check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &undefined),
                Err(AffineByteError::InvalidBytes { offset, .. }) if offset == at),
                "uninitialized W10 must fail at the actual branch read"
            );
            reject_code(
                &module,
                &lir,
                &code,
                &undefined,
                "undefined W Boolean branch operand",
            );
            refusals += 1;
        }
    }
    for taken in [false, true] {
        let mut module = source(Ty::I64, ICmpOp::Ne);
        module.functions[0].blocks[0].body[0].inst = Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(taken),
        };
        let lir = translate(&module);
        for route in [1, 3] {
            let mut code = hand_words(64, ICmpOp::Ne, route);
            // MOVZ W9,#0/#1 is a fully checked, canonical Boolean carrier.
            // It is not a claim about incoming parameter register contents.
            code[12..16].copy_from_slice(&(0x5280_0009u32 | u32::from(taken) << 5).to_le_bytes());
            assert!(
                check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &code).is_ok(),
                "canonical literal W Boolean in an I64-return diamond"
            );
            admitted += 1;
            let (at, branch) = only_word(&code, conditional);
            for incoming in [0, 2] {
                reject_word(
                    &module,
                    &lir,
                    &code,
                    at,
                    (branch & !31) | incoming,
                    "constant branch cannot confer Bool on an I64 input",
                );
                refusals += 1;
            }
            reject_word(
                &module,
                &lir,
                &code,
                at,
                (branch & !31) | 10,
                "constant branch cannot initialize W10",
            );
            refusals += 1;
        }
    }
    assert_eq!(admitted, 24);
    assert_eq!(refusals, 72);
}
