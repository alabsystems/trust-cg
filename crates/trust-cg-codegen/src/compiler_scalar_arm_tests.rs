// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! OD-102: ordinary original Core scalar nodes in both conditional arms.
//! The existing original-source, raw-ISel and actual-byte owners must genuinely
//! accept each fixture; unsupported preparation is never a positive outcome.
//! Native execution is explicitly Unchecked. These tests confer no replay,
//! row-proof, live-return credit or executable-publication authority.

use super::*;
use trust_ir::{InstrNode, ProofAnnotation, ValueId};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Variant {
    DeadBoolean,
    DeadComparisons,
    DeadSelect,
    LiveTrue,
    LiveFalse,
    LiveSameDynamic,
}

const VARIANTS: [Variant; 6] = [
    Variant::DeadBoolean,
    Variant::DeadComparisons,
    Variant::DeadSelect,
    Variant::LiveTrue,
    Variant::LiveFalse,
    Variant::LiveSameDynamic,
];

/// Every variant preserves `if outer(a,b) { c+1 } else { d-1 }`. The live
/// literal selects have genuinely distinct affine alternatives: the other
/// parameter plus seven, not a duplicate of the selected value. The live
/// dynamic select instead uses distinct SSA copies of the same affine value,
/// so its arm still normalizes flat under the existing scalar value domain.
fn scalar_source(ty: Ty, outer: ICmpOp, variant: Variant) -> Module {
    let mut builder = ModuleBuilder::new("original_core_scalar_arms");
    let signature = builder.add_func_type(vec![ty.clone(); 4], vec![ty.clone()]);
    let mut function = builder.function(SYMBOL, signature);
    let entry = function.create_block();
    let then_block = function.create_block();
    let else_block = function.create_block();
    let join = function.create_block();
    let args: Vec<_> = (0..4)
        .map(|_| function.add_block_param(entry, ty.clone()))
        .collect();
    let result = function.add_block_param(join, ty.clone());
    function.switch_to_block(entry);
    let predicate = function.icmp(outer, ty.clone(), args[0], args[1]);
    function.condbr(predicate, then_block, vec![], else_block, vec![]);
    for (block, take_then) in [(then_block, true), (else_block, false)] {
        function.switch_to_block(block);
        let selector = match variant {
            Variant::DeadBoolean => {
                let literal = function.bool_const(take_then);
                let _copy = function.copy(Ty::Bool, literal);
                None
            }
            Variant::DeadComparisons => {
                for comparison in CONDITIONS {
                    let predicate = function.icmp(comparison, ty.clone(), args[2], args[3]);
                    let _copy = function.copy(Ty::Bool, predicate);
                }
                None
            }
            Variant::DeadSelect | Variant::LiveSameDynamic => {
                let predicate = function.icmp(ICmpOp::Slt, ty.clone(), args[2], args[3]);
                let predicate = function.copy(Ty::Bool, predicate);
                if variant == Variant::DeadSelect {
                    let _dead = function.select(ty.clone(), predicate, args[2], args[3]);
                    None
                } else {
                    Some(predicate)
                }
            }
            Variant::LiveTrue | Variant::LiveFalse => {
                let predicate = function.bool_const(variant == Variant::LiveTrue);
                Some(function.copy(Ty::Bool, predicate))
            }
        };
        let one = function.iconst(ty.clone(), 1);
        let wanted = if take_then {
            function.add(ty.clone(), args[2], one)
        } else {
            function.sub(ty.clone(), args[3], one)
        };
        let wanted = function.copy(ty.clone(), wanted);
        let returned = match variant {
            Variant::LiveTrue | Variant::LiveFalse => {
                let seven = function.iconst(ty.clone(), 7);
                let alternative = function.add(ty.clone(), args[usize::from(take_then) + 2], seven);
                let (then_value, else_value) = if variant == Variant::LiveTrue {
                    (wanted, alternative)
                } else {
                    (alternative, wanted)
                };
                function.select(ty.clone(), selector.unwrap(), then_value, else_value)
            }
            Variant::LiveSameDynamic => {
                let then_value = function.copy(ty.clone(), wanted);
                let else_value = function.copy(ty.clone(), wanted);
                function.select(ty.clone(), selector.unwrap(), then_value, else_value)
            }
            _ => wanted,
        };
        function.br(join, vec![returned]);
    }
    function.switch_to_block(join);
    function.ret(vec![result]);
    function.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

fn returned(body: &[InstrNode]) -> ValueId {
    let Inst::Br { args, .. } = &body.last().unwrap().inst else {
        panic!("ordinary Core arm ends in merge edge");
    };
    let [value] = args.as_slice() else {
        panic!("one original Core merge argument");
    };
    *value
}

fn assert_original_inventory(module: &Module, variant: Variant) {
    assert_eq!(module.functions[0].blocks.len(), 4);
    for arm in [1, 2] {
        let body = &module.functions[0].blocks[arm].body;
        let comparisons: Vec<_> = body
            .iter()
            .filter_map(|node| match node.inst {
                Inst::ICmp { op, .. } => Some(op),
                _ => None,
            })
            .collect();
        let boolean_copies = body
            .iter()
            .filter(|node| matches!(&node.inst, Inst::Copy { ty: Ty::Bool, .. }))
            .count();
        match variant {
            Variant::DeadBoolean => {
                assert!(body.iter().any(|node| matches!(
                    &node.inst,
                    Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(_)
                    }
                )));
                assert_eq!(boolean_copies, 1);
            }
            Variant::DeadComparisons => {
                assert_eq!(comparisons, CONDITIONS);
                assert_eq!(boolean_copies, 10);
            }
            Variant::DeadSelect | Variant::LiveSameDynamic => {
                assert_eq!(comparisons, [ICmpOp::Slt]);
                assert_eq!(boolean_copies, 1);
            }
            Variant::LiveTrue | Variant::LiveFalse => {
                assert!(body.iter().any(|node| matches!(&node.inst, Inst::Const { ty: Ty::Bool, value: Constant::Bool(value) } if *value == (variant == Variant::LiveTrue))));
                assert_eq!(boolean_copies, 1);
            }
        }
        if variant != Variant::DeadBoolean && variant != Variant::DeadComparisons {
            let selects: Vec<_> = body
                .iter()
                .filter(|node| matches!(node.inst, Inst::Select { .. }))
                .collect();
            let [select] = selects.as_slice() else {
                panic!("one original integer select in each arm");
            };
            let Inst::Select {
                then_val, else_val, ..
            } = select.inst
            else {
                unreachable!()
            };
            assert_ne!(then_val, else_val, "distinct original SSA alternatives");
            if variant == Variant::DeadSelect {
                assert_ne!(
                    returned(body),
                    select.results[0],
                    "dead select does not become the return"
                );
            } else {
                assert_eq!(
                    returned(body),
                    select.results[0],
                    "live select feeds the merge directly"
                );
            }
            if variant == Variant::LiveSameDynamic {
                let copied = |id| {
                    let node = body.iter().find(|node| node.results == [id]).unwrap();
                    let Inst::Copy { operand, .. } = node.inst else {
                        panic!("same-value SSA copy");
                    };
                    operand
                };
                assert_eq!(copied(then_val), copied(else_val));
            }
        }
    }
}

fn encoded(module: &Module, lir: &Function, machine: &MachFunction) -> Vec<u8> {
    let frame = source_bound_frame(lir, machine).unwrap_or_else(|error| {
        panic!("both scalar arms must bind their source frame: {error:?}\n{lir:#?}\n{machine:#?}")
    });
    assert!(std::ptr::eq(frame.source(), lir));
    assert!(std::ptr::eq(frame.machine(), machine));
    let (bytes, fixups, sites) = encode_core_function(module, 0, lir, machine).unwrap();
    assert!(fixups.is_empty() && sites.is_empty());
    let checked = check_aarch64_trust_ir_affine_bytes(module, 0, lir, &bytes).unwrap();
    assert!(std::ptr::eq(checked.module(), module));
    assert!(std::ptr::eq(checked.source(), &module.functions[0]));
    assert!(std::ptr::eq(checked.lir(), lir));
    assert!(std::ptr::eq(checked.code(), bytes.as_slice()));
    let stats = checked.statistics();
    assert_eq!(
        stats.trust_ir_instructions,
        module.functions[0]
            .blocks
            .iter()
            .map(|block| block.body.len())
            .sum::<usize>()
    );
    assert_eq!(
        stats.lir_instructions,
        lir.blocks
            .values()
            .map(|block| block.instructions.len())
            .sum::<usize>()
    );
    assert_eq!(stats.machine_instructions, bytes.len() / 4);
    assert_eq!(stats.parameter_count, 4);
    assert_eq!(stats.private_stack_bytes, 16);
    bytes
}

#[test]
fn original_scalar_nodes_in_both_arms_reach_checked_preparation_and_actual_bytes() {
    let mut cases = 0;
    for variant in VARIANTS {
        for ty in [Ty::I32, Ty::I64] {
            for condition in CONDITIONS {
                let module = scalar_source(ty.clone(), condition, variant);
                assert_original_inventory(&module, variant);
                let lir = translate(&module);
                for target in TARGETS {
                    for level in LEVELS {
                        // No unsupported-source/target branch, ignore, or
                        // fallback can turn this required positive into pass.
                        let machine = prepare(target, &module, &lir, level);
                        let _ = encoded(&module, &lir, &machine);
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 960);
}

fn invalid_original(module: &Module, lir: &Function, bytes: &[u8], label: &str) {
    let refusal = check_aarch64_trust_ir_affine_bytes(module, 0, lir, bytes).unwrap_err();
    assert!(
        matches!(
            refusal,
            AffineByteError::Source(TrustIrAffineLoweringError::InvalidTrustIr(_))
        ),
        "{label}: malformed original node must not become a coverage gap: {refusal:?}"
    );
    assert!(
        matches!(
            check_core_bytes(module, 0, lir, bytes, &FixupList::new()),
            Err(CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. })
        ),
        "{label}: malformed original source must be a hard compiler error"
    );
}

fn source_profile(module: &Module, lir: &Function, bytes: &[u8], detail: &str) {
    let refusal = check_aarch64_trust_ir_affine_bytes(module, 0, lir, bytes).unwrap_err();
    assert!(
        matches!(refusal, AffineByteError::Source(TrustIrAffineLoweringError::UnsupportedTrustIr(ref reason)) if reason.contains(detail)),
        "original inherited source profile {detail}: {refusal:?}"
    );
}

fn mutate_invalid(module: &mut Module, arm: usize, mutation: usize) -> &'static str {
    let parameter = module.functions[0].blocks[0].params[0].0;
    let other_arm_bool = module.functions[0].blocks[3 - arm].body[1].results[0];
    let body = &mut module.functions[0].blocks[arm].body;
    let boolean = body[1].results[0];
    match mutation {
        0 => {
            let Inst::Const { value, .. } = &mut body[0].inst else {
                panic!("Boolean constant");
            };
            *value = Constant::Int(2);
            "noncanonical original Boolean literal carrier"
        }
        1..=3 => {
            let Inst::Copy { operand, .. } = &mut body[1].inst else {
                panic!("Boolean copy");
            };
            *operand = match mutation {
                1 => parameter,
                2 => ValueId::new(99_999),
                _ => other_arm_bool,
            };
            "wrong-type, undefined or other-arm Boolean copy operand"
        }
        4 => {
            body[0].results.clear();
            "missing original Boolean SSA result"
        }
        5 => {
            body[0].results.push(ValueId::new(90_000));
            "multiple original Boolean SSA results"
        }
        6 => {
            body[1].results[0] = body[0].results[0];
            "duplicate original same-arm Boolean SSA identity"
        }
        7 => {
            body[1].results[0] = other_arm_bool;
            "duplicate original Boolean SSA identity across arms"
        }
        8 => {
            let arithmetic = body
                .iter_mut()
                .find(|node| matches!(node.inst, Inst::BinOp { .. }))
                .unwrap();
            let Inst::BinOp { lhs, .. } = &mut arithmetic.inst else {
                unreachable!()
            };
            *lhs = boolean;
            "Boolean used as an integer arithmetic operand"
        }
        _ => {
            let Inst::Br { args, .. } = &mut body.last_mut().unwrap().inst else {
                panic!("merge edge");
            };
            args[0] = boolean;
            "Boolean used as the integer merge argument"
        }
    }
}

#[test]
fn original_boolean_nodes_keep_exact_carrier_type_arity_ssa_and_dominance_checks() {
    let mut controls = 0;
    for ty in [Ty::I32, Ty::I64] {
        let module = scalar_source(ty, ICmpOp::Ult, Variant::DeadBoolean);
        let lir = translate(&module);
        let machine = prepare(TARGETS[0], &module, &lir, OptLevel::O0);
        let bytes = encoded(&module, &lir, &machine);
        for arm in [1, 2] {
            for mutation in 0..10 {
                let mut changed = module.clone();
                let label = mutate_invalid(&mut changed, arm, mutation);
                invalid_original(&changed, &lir, &bytes, label);
                controls += 1;
            }
        }
    }
    assert_eq!(controls, 40);
}

#[test]
fn original_select_operands_and_dead_comparisons_remain_typed_and_guard_aware() {
    let mut controls = 0;
    for ty in [Ty::I32, Ty::I64] {
        for variant in [
            Variant::DeadSelect,
            Variant::LiveTrue,
            Variant::LiveFalse,
            Variant::LiveSameDynamic,
        ] {
            let module = scalar_source(ty.clone(), ICmpOp::Slt, variant);
            let lir = translate(&module);
            let machine = prepare(TARGETS[1], &module, &lir, OptLevel::O0);
            let bytes = encoded(&module, &lir, &machine);
            let integer = module.functions[0].blocks[0].params[0].0;
            for arm in [1, 2] {
                let body = &module.functions[0].blocks[arm].body;
                let site = body
                    .iter()
                    .position(|node| matches!(node.inst, Inst::Select { .. }))
                    .unwrap();
                let Inst::Select { cond, .. } = body[site].inst else {
                    unreachable!()
                };
                for mutation in 0..5 {
                    let mut changed = module.clone();
                    let node = &mut changed.functions[0].blocks[arm].body[site];
                    match mutation {
                        0 => {
                            let Inst::Select { cond, .. } = &mut node.inst else {
                                unreachable!()
                            };
                            *cond = integer;
                        }
                        1 => {
                            let Inst::Select { then_val, .. } = &mut node.inst else {
                                unreachable!()
                            };
                            *then_val = cond;
                        }
                        2 => {
                            let Inst::Select { else_val, .. } = &mut node.inst else {
                                unreachable!()
                            };
                            *else_val = ValueId::new(99_999);
                        }
                        3 => node.results.clear(),
                        _ => node.proof_context = Some(Default::default()),
                    }
                    invalid_original(
                        &changed,
                        &lir,
                        &bytes,
                        "original Select type/use/arity/context",
                    );
                    controls += 1;
                }
            }
        }
        let module = scalar_source(ty, ICmpOp::Ne, Variant::DeadComparisons);
        let lir = translate(&module);
        let machine = prepare(TARGETS[0], &module, &lir, OptLevel::O0);
        let bytes = encoded(&module, &lir, &machine);
        for arm in [1, 2] {
            let sites: Vec<_> = module.functions[0].blocks[arm]
                .body
                .iter()
                .enumerate()
                .filter(|(_, node)| matches!(node.inst, Inst::ICmp { .. }))
                .map(|(index, _)| index)
                .collect();
            assert_eq!(sites.len(), 10);
            for site in sites {
                let mut context = module.clone();
                context.functions[0].blocks[arm].body[site].proof_context =
                    Some(Default::default());
                invalid_original(
                    &context,
                    &lir,
                    &bytes,
                    "non-call proof context on each dead comparison",
                );
                let mut guarded = module.clone();
                guarded.functions[0].blocks[arm].body[site]
                    .proofs
                    .push(ProofAnnotation::InBounds);
                source_profile(&guarded, &lir, &bytes, "InBounds");
                controls += 2;
            }
        }
    }
    assert_eq!(controls, 160);
}

#[test]
fn constant_untaken_scalar_arm_does_not_hide_malformed_nodes_or_guard_semantics() {
    let mut controls = 0;
    for ty in [Ty::I32, Ty::I64] {
        for taken in [false, true] {
            let mut module = scalar_source(ty.clone(), ICmpOp::Ne, Variant::DeadBoolean);
            module.functions[0].blocks[0].body[0].inst = Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(taken),
            };
            let lir = translate(&module);
            let machine = prepare(TARGETS[0], &module, &lir, OptLevel::O0);
            let bytes = encoded(&module, &lir, &machine);
            let untaken = if taken { 2 } else { 1 };
            for mutation in 0..10 {
                let mut changed = module.clone();
                let label = mutate_invalid(&mut changed, untaken, mutation);
                invalid_original(&changed, &lir, &bytes, label);
                controls += 1;
            }
            let mut context = module.clone();
            context.functions[0].blocks[untaken].body[0].proof_context = Some(Default::default());
            invalid_original(
                &context,
                &lir,
                &bytes,
                "untaken Boolean constant proof context",
            );
            let args = &module.functions[0].blocks[0].params;
            let guard = InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ult,
                ty: ty.clone(),
                lhs: args[0].0,
                rhs: args[1].0,
            })
            .with_result(ValueId::new(70_000))
            .with_proof(ProofAnnotation::InBounds);
            let mut guarded = module.clone();
            guarded.functions[0].blocks[untaken].body.insert(0, guard);
            source_profile(&guarded, &lir, &bytes, "InBounds");
            controls += 2;
        }
    }
    assert_eq!(controls, 48);
}

#[test]
fn genuinely_nested_arm_returns_keep_the_existing_source_profile_refusal() {
    let mut controls = 0;
    for ty in [Ty::I32, Ty::I64] {
        let module = scalar_source(ty, ICmpOp::Slt, Variant::DeadSelect);
        let lir = translate(&module);
        let machine = prepare(TARGETS[0], &module, &lir, OptLevel::O0);
        let bytes = encoded(&module, &lir, &machine);
        for arm in [1, 2] {
            let body = &module.functions[0].blocks[arm].body;
            let selected = body
                .iter()
                .find(|node| matches!(node.inst, Inst::Select { .. }))
                .unwrap()
                .results[0];
            for constant_outer in [false, true] {
                let mut changed = module.clone();
                if constant_outer {
                    changed.functions[0].blocks[0].body[0].inst = Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(arm == 2),
                    };
                }
                let Inst::Br { args, .. } = &mut changed.functions[0].blocks[arm]
                    .body
                    .last_mut()
                    .unwrap()
                    .inst
                else {
                    panic!("merge edge");
                };
                args[0] = selected;
                source_profile(&changed, &lir, &bytes, "nested selection");
                controls += 1;
            }
        }
    }
    assert_eq!(controls, 8);
}

#[test]
fn admitted_scalar_arms_reject_new_effect_words_and_wrong_live_arithmetic() {
    let mut controls = 0;
    for ty in [Ty::I32, Ty::I64] {
        let module = scalar_source(ty, ICmpOp::Ult, Variant::DeadComparisons);
        let lir = translate(&module);
        let machine = prepare(TARGETS[1], &module, &lir, OptLevel::O0);
        let bytes = encoded(&module, &lir, &machine);
        let (words, remainder) = bytes.as_chunks::<4>();
        assert!(remainder.is_empty());
        let arithmetic: Vec<_> = words
            .iter()
            .enumerate()
            .filter_map(|(index, bytes)| {
                let word = u32::from_le_bytes(*bytes);
                (matches!(word & 0x7f800000, 0x11000000 | 0x51000000)
                    && word & 31 <= 17
                    && (word >> 5) & 31 <= 17)
                    .then_some((index * 4, word))
            })
            .collect();
        assert_eq!(
            arithmetic.len(),
            2,
            "one actual live arithmetic instruction per arm"
        );
        for (offset, word) in arithmetic {
            for replacement in [word | (1 << 29), 0xf9400000 | (word & 31)] {
                let mut changed = bytes.clone();
                changed[offset..offset + 4].copy_from_slice(&replacement.to_le_bytes());
                assert!(
                    matches!(
                        check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &changed),
                        Err(AffineByteError::UnsupportedBytes { .. })
                    ),
                    "new flags/memory effects are target refusals, not source-domain skips"
                );
                assert!(matches!(
                    check_core_bytes(&module, 0, &lir, &changed, &FixupList::new()),
                    Err(CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. })
                ));
                controls += 1;
            }
            let mut changed = bytes.clone();
            changed[offset..offset + 4].copy_from_slice(&(word ^ (1 << 30)).to_le_bytes());
            assert!(
                matches!(
                    check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &changed),
                    Err(AffineByteError::ReturnMismatch)
                ),
                "valid opposite arithmetic must actually change a live arm result"
            );
            controls += 1;
        }
    }
    assert_eq!(controls, 12);
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
mod native {
    use super::super::native::{boundaries, condition_holds, full_register_call};
    use super::*;
    use crate::compiler::{Compiler, CompilerConfig};
    use std::collections::HashMap;

    #[test]
    fn unchecked_mac_original_scalar_arms_execute_both_paths_and_ignore_i32_high_poison() {
        let mut compiled = 0;
        let mut calls = 0;
        for variant in VARIANTS {
            for (ty, bits) in [(Ty::I32, 32), (Ty::I64, 64)] {
                let mask = if bits == 32 {
                    u64::from(u32::MAX)
                } else {
                    u64::MAX
                };
                let sign = 1u64 << (bits - 1);
                let arms = [[0, 0], [mask, 0], [sign - 1, sign], [1, mask]];
                for outer in CONDITIONS {
                    let module = scalar_source(ty.clone(), outer, variant);
                    assert_original_inventory(&module, variant);
                    for level in LEVELS {
                        let compiler = Compiler::new(CompilerConfig {
                            opt_level: level,
                            emit_proofs: false,
                            enable_jit_fast_regalloc: false,
                            ..CompilerConfig::for_host_jit_unchecked()
                        })
                        .with_codegen_license(crate::license_test_support::permit_unlicensed());
                        assert!(compiler.config().jit_validation_mode().is_unchecked());
                        let result = compiler.compile_module_to_jit(&module, &HashMap::new()).unwrap_or_else(|error| panic!("UNCHECKED native {variant:?}/{ty:?}/{outer:?}/{level:?}: {error}"));
                        assert_eq!(result.metrics.function_count, 1);
                        assert!(!result.buffer.code_slice().is_empty());
                        let pointer = result.buffer.get_fn_ptr_bound(SYMBOL).unwrap();
                        // SAFETY: these signatures match the exact original
                        // homogeneous four-argument C-ABI module above. Both
                        // wrappers remain borrowed from the executable owner.
                        let narrow = if bits == 32 {
                            Some(unsafe {
                                result
                                    .buffer
                                    .get_fn_bound::<extern "C" fn(i32, i32, i32, i32) -> i32>(
                                        SYMBOL,
                                    )
                                    .unwrap()
                            })
                        } else {
                            None
                        };
                        // SAFETY: this wrapper matches the I64 module and
                        // stays borrowed until every call below completes.
                        let wide = if bits == 64 {
                            Some(unsafe {
                                result
                                    .buffer
                                    .get_fn_bound::<extern "C" fn(i64, i64, i64, i64) -> i64>(
                                        SYMBOL,
                                    )
                                    .unwrap()
                            })
                        } else {
                            None
                        };
                        let mut seen = [false; 2];
                        for a in boundaries(bits) {
                            for b in boundaries(bits) {
                                let take_then = condition_holds(outer, bits, a, b);
                                seen[usize::from(take_then)] = true;
                                for [c, d] in arms {
                                    let expected = if take_then {
                                        c.wrapping_add(1) & mask
                                    } else {
                                        d.wrapping_sub(1) & mask
                                    };
                                    let actual = if let Some(function) = &narrow {
                                        u64::from(function.as_ref()(
                                            a as i32, b as i32, c as i32, d as i32,
                                        ) as u32)
                                    } else {
                                        wide.as_ref().unwrap().as_ref()(
                                            a as i64, b as i64, c as i64, d as i64,
                                        ) as u64
                                    };
                                    assert_eq!(
                                        actual, expected,
                                        "typed {variant:?}/{ty:?}/{outer:?}/{level:?}, [{a:#x},{b:#x},{c:#x},{d:#x}]"
                                    );
                                    calls += 1;
                                    let poisons: &[[u64; 4]] = if bits == 32 {
                                        &[
                                            [
                                                0xffff_ffff_0000_0000,
                                                0,
                                                0xaaaa_aaaa_0000_0000,
                                                0x5555_5555_0000_0000,
                                            ],
                                            [
                                                0,
                                                0xffff_ffff_0000_0000,
                                                0x5555_5555_0000_0000,
                                                0xaaaa_aaaa_0000_0000,
                                            ],
                                        ]
                                    } else {
                                        &[[0; 4]]
                                    };
                                    for poison in poisons {
                                        let actual = full_register_call(
                                            pointer,
                                            [
                                                a | poison[0],
                                                b | poison[1],
                                                c | poison[2],
                                                d | poison[3],
                                            ],
                                        );
                                        assert_eq!(
                                            actual & mask,
                                            expected,
                                            "full register {variant:?}/{ty:?}/{outer:?}/{level:?}, poison={poison:#x?}, [{a:#x},{b:#x},{c:#x},{d:#x}]"
                                        );
                                        if bits == 32 {
                                            assert_eq!(
                                                actual >> 32,
                                                0,
                                                "these live W arithmetic returns zero X0's upper half"
                                            );
                                        }
                                        calls += 1;
                                    }
                                }
                            }
                        }
                        assert!(
                            seen.into_iter().all(|seen| seen),
                            "each source arm must execute"
                        );
                        compiled += 1;
                    }
                }
            }
        }
        assert_eq!(compiled, 480);
        assert_eq!(calls, 388_800);
    }
}
