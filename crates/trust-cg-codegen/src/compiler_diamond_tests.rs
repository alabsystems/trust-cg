// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Ordinary Core arithmetic diamonds through the adapter, sealed-Core machine
//! preparation and actual encoder. Native controls execute UNCERTIFIED bytes
//! on AArch64/macOS. Neither these checks nor frame construction discharge a
//! solver obligation. The independent Core and final-byte owners must accept
//! the original diamond and reject mutations of the real encoded words.

use super::*;
use crate::pipeline::{OptLevel, Pipeline, PipelineConfig, PreOptimizationAffineLowering};
use trust_cg_ir::{AArch64Opcode as M, InstId, MachFunction, MachOperand};
use trust_cg_lower::Function;
use trust_cg_verify::aarch64_affine_lowering::check_aarch64_trust_ir_affine_bytes;
use trust_cg_verify::source_bound_frame::{SourceBoundFrameRefusal, source_bound_frame};
use trust_ir::{Constant, ICmpOp, Inst, Module, Ty};
use trust_ir_build::ModuleBuilder;

#[path = "compiler_scalar_arm_tests.rs"]
mod scalar_arm_tests;

pub(super) const TARGETS: [&str; 2] = ["aarch64-unknown-linux-gnu", "aarch64-apple-darwin"];
pub(super) const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
pub(super) const CONDITIONS: [ICmpOp; 10] = [
    ICmpOp::Eq,
    ICmpOp::Ne,
    ICmpOp::Slt,
    ICmpOp::Sle,
    ICmpOp::Sgt,
    ICmpOp::Sge,
    ICmpOp::Ult,
    ICmpOp::Ule,
    ICmpOp::Ugt,
    ICmpOp::Uge,
];
const SYMBOL: &str = "arithmetic_diamond";

/// Four independent integer parameters prevent an arm, comparison, or merge
/// mutation from being hidden by accidental equal operands. The block argument
/// is an ordinary Core merge, not a hand-built LIR copy convention.
pub(super) fn source(ty: Ty, condition: ICmpOp) -> Module {
    let mut builder = ModuleBuilder::new("core_arithmetic_diamond");
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
    let condition = function.icmp(condition, ty.clone(), args[0], args[1]);
    function.condbr(condition, then_block, vec![], else_block, vec![]);
    function.switch_to_block(then_block);
    let one = function.iconst(ty.clone(), 1);
    let left = function.add(ty.clone(), args[2], one);
    let left = function.copy(ty.clone(), left);
    function.br(join, vec![left]);
    function.switch_to_block(else_block);
    let one = function.iconst(ty.clone(), 1);
    let right = function.sub(ty.clone(), args[3], one);
    let right = function.copy(ty, right);
    function.br(join, vec![right]);
    function.switch_to_block(join);
    function.ret(vec![result]);
    function.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

pub(super) fn translate(module: &Module) -> Function {
    trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .expect("ordinary Core diamond must translate")
    .0
}

pub(super) fn prepare(
    target: &str,
    module: &Module,
    lir: &Function,
    level: OptLevel,
) -> MachFunction {
    let (_, proof_context) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let (machine, metrics) = Pipeline::new(PipelineConfig {
        opt_level: level,
        verify: false,
        target_triple: target.into(),
        ..Default::default()
    })
    .prepare_function_with_metrics_for_sealed_core(lir, Some(&proof_context), module, 0)
    .unwrap_or_else(|error| panic!("diamond preparation {target}/{level:?}: {error}"));
    let Some(PreOptimizationAffineLowering::Checked(stats)) =
        metrics.pre_optimization_affine_lowering
    else {
        panic!(
            "original Core diamond must reach actual pre-optimization Checked: {target}/{level:?}"
        );
    };
    assert_eq!(
        stats.trust_ir_instructions,
        module.functions[0]
            .blocks
            .iter()
            .map(|b| b.body.len())
            .sum::<usize>()
    );
    assert_eq!(
        stats.lowering.source_instructions,
        lir.blocks
            .values()
            .map(|b| b.instructions.len())
            .sum::<usize>()
    );
    assert_eq!(stats.lowering.parameter_count, 4);
    assert!(stats.lowering.machine_instructions > 0);
    let integrity = metrics.pre_optimization_dataflow_integrity.unwrap();
    assert!(integrity.was_evaluated() && integrity.was_enforced());
    integrity
        .validate_pair(lir, &machine.name, true)
        .expect("enforced raw integrity remains bound to the exact retained LIR source");
    machine
}

fn frame_mismatch(lir: &Function, machine: &MachFunction, control: &str) {
    let refusal = match source_bound_frame(lir, machine) {
        Ok(_) => panic!("{control} must not bind its changed return/control semantics"),
        Err(refusal) => refusal,
    };
    assert!(
        matches!(refusal, SourceBoundFrameRefusal::Mismatch(_)),
        "{control} is a supported-source mismatch, not a coverage refusal: {refusal:?}\n{lir:#?}\n{machine:#?}"
    );
}

fn inverse(condition: ICmpOp) -> ICmpOp {
    match condition {
        ICmpOp::Eq => ICmpOp::Ne,
        ICmpOp::Ne => ICmpOp::Eq,
        ICmpOp::Slt => ICmpOp::Sge,
        ICmpOp::Sle => ICmpOp::Sgt,
        ICmpOp::Sgt => ICmpOp::Sle,
        ICmpOp::Sge => ICmpOp::Slt,
        ICmpOp::Ult => ICmpOp::Uge,
        ICmpOp::Ule => ICmpOp::Ugt,
        ICmpOp::Ugt => ICmpOp::Ule,
        ICmpOp::Uge => ICmpOp::Ult,
    }
}

#[test]
fn ordinary_core_arithmetic_diamonds_bind_both_arms_at_all_levels_and_targets() {
    use trust_cg_lower::instructions::Opcode as L;
    let mut cases = 0;
    for ty in [Ty::I32, Ty::I64] {
        for condition in CONDITIONS {
            let module = source(ty.clone(), condition);
            assert_eq!(module.functions[0].blocks.len(), 4);
            let lir = translate(&module);
            assert_eq!(lir.blocks.len(), 4);
            // A copy-only fixture would leave the new source admission blind.
            let instructions: Vec<_> = lir
                .blocks
                .values()
                .flat_map(|block| &block.instructions)
                .collect();
            assert_eq!(
                instructions.iter().filter(|i| i.opcode == L::Iadd).count(),
                1
            );
            assert_eq!(
                instructions.iter().filter(|i| i.opcode == L::Isub).count(),
                1
            );
            assert_eq!(
                instructions
                    .iter()
                    .filter(|i| matches!(i.opcode, L::Iconst { .. }))
                    .count(),
                2
            );
            for target in TARGETS {
                for level in LEVELS {
                    let machine = prepare(target, &module, &lir, level);
                    let frame = source_bound_frame(&lir, &machine).unwrap_or_else(|refusal| {
                        panic!(
                            "arithmetic diamond {ty:?}/{condition:?}/{target}/{level:?}: {refusal:?}\n{lir:#?}\n{machine:#?}"
                        )
                    });
                    assert!(std::ptr::eq(frame.source(), &lir));
                    assert!(std::ptr::eq(frame.machine(), &machine));
                    assert_ne!(frame.pair_instructions()[0], frame.pair_instructions()[1]);
                    let (bytes, fixups, sites) =
                        encode_core_function(&module, 0, &lir, &machine).unwrap();
                    assert!(!bytes.is_empty());
                    assert_eq!(bytes.len() % 4, 0);
                    assert!(fixups.is_empty() && sites.is_empty());
                    // The raw checked-triple owner ended before mutating
                    // optimization/allocation passes. Only its Checked metrics
                    // remain; final correspondence uses a fresh byte owner.
                    let checked_bytes =
                        check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &bytes)
                            .expect("original Core/LIR/final byte diamond correspondence");
                    assert!(std::ptr::eq(checked_bytes.module(), &module));
                    assert!(std::ptr::eq(checked_bytes.source(), &module.functions[0]));
                    assert!(std::ptr::eq(checked_bytes.lir(), &lir));
                    assert!(std::ptr::eq(checked_bytes.code(), bytes.as_slice()));
                    assert_eq!(checked_bytes.statistics().parameter_count, 4);
                    assert_eq!(
                        checked_bytes.statistics().machine_instructions,
                        bytes.len() / 4
                    );
                    assert_eq!(checked_bytes.statistics().private_stack_bytes, 16);
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 160);
}

#[test]
fn original_core_comparison_and_each_arithmetic_arm_are_observed_by_frame_binding() {
    let mut controls = 0;
    for ty in [Ty::I32, Ty::I64] {
        for condition in CONDITIONS {
            let module = source(ty.clone(), condition);
            let lir = translate(&module);
            for target in TARGETS {
                for level in [OptLevel::O0, OptLevel::O2] {
                    let machine = prepare(target, &module, &lir, level);
                    assert!(source_bound_frame(&lir, &machine).is_ok());
                    let mut changed = module.clone();
                    let comparison = changed.functions[0].blocks[0]
                        .body
                        .iter_mut()
                        .find_map(|node| match &mut node.inst {
                            Inst::ICmp { op, .. } => Some(op),
                            _ => None,
                        })
                        .unwrap();
                    *comparison = inverse(condition);
                    frame_mismatch(
                        &translate(&changed),
                        &machine,
                        "source comparison inversion",
                    );
                    controls += 1;
                    for arm in [1, 2] {
                        let mut changed = module.clone();
                        let value = changed.functions[0].blocks[arm]
                            .body
                            .iter_mut()
                            .find_map(|node| match &mut node.inst {
                                Inst::Const { value, .. } => Some(value),
                                _ => None,
                            })
                            .unwrap();
                        assert_eq!(*value, Constant::Int(1));
                        *value = Constant::Int(2);
                        frame_mismatch(
                            &translate(&changed),
                            &machine,
                            if arm == 1 {
                                "source true arm +2"
                            } else {
                                "source false arm -2"
                            },
                        );
                        controls += 1;
                    }
                }
            }
        }
    }
    assert_eq!(controls, 240);
}

/// Mutate the actual allocated instruction and check its independently bound
/// source frame. Encoding the changed machine must also change real words;
/// these are not metadata/provenance-only controls. The public byte checker
/// and sealed compiler wrapper must each reject the actual changed allocation.
fn encoded_machine_mismatch(
    module: &Module,
    lir: &Function,
    original: &[u8],
    machine: &MachFunction,
    control: &str,
) {
    frame_mismatch(lir, machine, control);
    let (changed, fixups, sites) = crate::pipeline::encode_function_with_fixups_and_sites(machine)
        .unwrap_or_else(|error| panic!("valid allocated {control} must encode: {error}"));
    assert!(fixups.is_empty() && sites.is_empty());
    assert_ne!(
        changed, original,
        "{control} must change the actual emitted words"
    );
    assert!(check_aarch64_trust_ir_affine_bytes(module, 0, lir, &changed).is_err());
    assert!(
        matches!(
            check_core_bytes(module, 0, lir, &changed, &fixups),
            Err(CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. })
        ),
        "{control}: sealed Core final-byte gate must reject"
    );
}

#[test]
fn allocated_diamond_comparison_branch_and_arithmetic_mutations_change_real_words() {
    let mut controls = 0;
    for ty in [Ty::I32, Ty::I64] {
        for condition in CONDITIONS {
            let module = source(ty.clone(), condition);
            let lir = translate(&module);
            for target in TARGETS {
                let machine = prepare(target, &module, &lir, OptLevel::O0);
                assert!(source_bound_frame(&lir, &machine).is_ok());
                let (original, fixups, sites) =
                    encode_core_function(&module, 0, &lir, &machine).unwrap();
                assert!(fixups.is_empty() && sites.is_empty());
                let live: Vec<InstId> = machine
                    .block_order
                    .iter()
                    .flat_map(|block| machine.block(*block).insts.iter().copied())
                    .collect();
                let cmp = live
                    .iter()
                    .copied()
                    .find(|id| machine.inst(*id).opcode == M::CmpRR)
                    .unwrap_or_else(|| panic!("actual source CMP at O0: {machine:#?}"));
                let mut changed = machine.clone();
                let lhs = changed.inst(cmp).operands[0].clone();
                assert_ne!(changed.inst(cmp).operands[1], lhs);
                changed.inst_mut(cmp).operands[1] = lhs;
                encoded_machine_mismatch(&module, &lir, &original, &changed, "CMP lhs,lhs");
                controls += 1;

                let branch = live
                    .iter()
                    .copied()
                    .find(|id| matches!(machine.inst(*id).opcode, M::BCond | M::Cbz | M::Cbnz))
                    .unwrap_or_else(|| panic!("actual conditional edge at O0: {machine:#?}"));
                let mut changed = machine.clone();
                let inst = changed.inst_mut(branch);
                match inst.opcode {
                    M::BCond => {
                        let MachOperand::Imm(cc) = &mut inst.operands[0] else {
                            panic!("actual B.cond condition");
                        };
                        assert!((0..=13).contains(cc));
                        *cc ^= 1;
                    }
                    M::Cbz => inst.opcode = M::Cbnz,
                    M::Cbnz => inst.opcode = M::Cbz,
                    _ => unreachable!(),
                }
                encoded_machine_mismatch(
                    &module,
                    &lir,
                    &original,
                    &changed,
                    "inverted machine edge",
                );
                controls += 1;

                for addition in [true, false] {
                    let arithmetic = live
                        .iter()
                        .copied()
                        .find(|id| {
                            let inst = machine.inst(*id);
                            matches!(inst.operands.get(1), Some(MachOperand::PReg(_)))
                                && if addition {
                                    matches!(inst.opcode, M::AddRR | M::AddRI)
                                } else {
                                    matches!(inst.opcode, M::SubRR | M::SubRI)
                                }
                        })
                        .unwrap_or_else(|| panic!("actual arithmetic on each arm: {machine:#?}"));
                    let mut changed = machine.clone();
                    let inst = changed.inst_mut(arithmetic);
                    inst.opcode = match inst.opcode {
                        M::AddRR => M::SubRR,
                        M::SubRR => M::AddRR,
                        M::AddRI => M::SubRI,
                        M::SubRI => M::AddRI,
                        _ => unreachable!(),
                    };
                    encoded_machine_mismatch(
                        &module,
                        &lir,
                        &original,
                        &changed,
                        if addition {
                            "true arm subtracts"
                        } else {
                            "false arm adds"
                        },
                    );
                    controls += 1;
                }
            }
        }
    }
    assert_eq!(controls, 160);
}

#[test]
fn diamond_final_byte_owner_binds_exact_source_and_rejects_corrupted_frame_words() {
    let module = source(Ty::I64, ICmpOp::Ne);
    let lir = translate(&module);
    let machine = prepare(TARGETS[1], &module, &lir, OptLevel::O0);
    let (bytes, fixups, _) = encode_core_function(&module, 0, &lir, &machine).unwrap();
    assert!(fixups.is_empty());
    assert!(check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &bytes).is_ok());
    let mut changed = bytes.clone();
    changed[0] ^= 1;
    assert_ne!(changed, bytes);
    assert!(check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &changed).is_err());
    assert!(matches!(
        check_core_bytes(&module, 0, &lir, &changed, &fixups),
        Err(CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. })
    ));
    assert!(matches!(
        check_aarch64_trust_ir_affine_bytes(&module, 1, &lir, &bytes),
        Err(AffineByteError::Source(
            TrustIrAffineLoweringError::InvalidTrustIr(_)
        ))
    ));
    let mut renamed = module.clone();
    renamed.functions[0].name = "another_diamond".into();
    assert!(matches!(
        check_aarch64_trust_ir_affine_bytes(&renamed, 0, &lir, &bytes),
        Err(AffineByteError::Source(
            TrustIrAffineLoweringError::TrustIrLirMismatch
        ))
    ));
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
mod native {
    use super::*;
    use crate::compiler::{Compiler, CompilerConfig};
    use crate::jit::JitPtr;
    use std::collections::HashMap;

    pub(super) fn condition_holds(condition: ICmpOp, bits: u32, a: u64, b: u64) -> bool {
        let mask = if bits == 32 {
            u64::from(u32::MAX)
        } else {
            u64::MAX
        };
        let (a, b) = (a & mask, b & mask);
        let (signed_a, signed_b) = if bits == 32 {
            (i64::from(a as i32), i64::from(b as i32))
        } else {
            (a as i64, b as i64)
        };
        match condition {
            ICmpOp::Eq => a == b,
            ICmpOp::Ne => a != b,
            ICmpOp::Slt => signed_a < signed_b,
            ICmpOp::Sle => signed_a <= signed_b,
            ICmpOp::Sgt => signed_a > signed_b,
            ICmpOp::Sge => signed_a >= signed_b,
            ICmpOp::Ult => a < b,
            ICmpOp::Ule => a <= b,
            ICmpOp::Ugt => a > b,
            ICmpOp::Uge => a >= b,
        }
    }

    pub(super) fn boundaries(bits: u32) -> [u64; 9] {
        let sign = 1u64 << (bits - 1);
        let mask = if bits == 32 {
            u64::from(u32::MAX)
        } else {
            u64::MAX
        };
        [0, 1, 2, 7, sign - 1, sign, sign + 1, mask - 1, mask]
    }

    /// A raw ABI probe supplies all four complete X-register carriers and
    /// observes X0. For I32 only their low halves belong to the source values;
    /// the distinct upper poisons must not affect comparison or arithmetic.
    /// The lifetime-bound pointer is never retained after its buffer is dropped.
    pub(super) fn full_register_call(pointer: JitPtr<'_>, arguments: [u64; 4]) -> u64 {
        let result;
        // SAFETY: this test owns a live executable AArch64/macOS buffer with
        // one C-ABI function taking four integer register parameters. BLR is a
        // real call, so C-ABI clobbers (including LR/NZCV) are declared and no
        // nostack/nomem promise is made. The callee has no external effects.
        unsafe {
            core::arch::asm!(
                "blr x16",
                in("x16") pointer.as_ptr(),
                inout("x0") arguments[0] => result,
                in("x1") arguments[1],
                in("x2") arguments[2],
                in("x3") arguments[3],
                clobber_abi("C"),
            );
        }
        result
    }

    #[test]
    fn unchecked_mac_native_arithmetic_diamonds_match_independent_wrapping_oracle() {
        let mut compiled = 0;
        let mut typed_calls = 0;
        let mut full_register_calls = 0;
        for (ty, bits) in [(Ty::I32, 32), (Ty::I64, 64)] {
            let mask = if bits == 32 {
                u64::from(u32::MAX)
            } else {
                u64::MAX
            };
            let sign = 1u64 << (bits - 1);
            let arm_inputs = [[0, 0], [mask, 0], [sign - 1, sign], [1, mask]];
            for condition in CONDITIONS {
                let module = source(ty.clone(), condition);
                for level in LEVELS {
                    let compiler = Compiler::new(CompilerConfig {
                        opt_level: level,
                        emit_proofs: false,
                        enable_jit_fast_regalloc: false,
                        ..CompilerConfig::for_host_jit_unchecked()
                    })
                    .with_codegen_license(crate::license_test_support::permit_unlicensed());
                    assert!(compiler.config().jit_validation_mode().is_unchecked());
                    let result = compiler
                        .compile_module_to_jit(&module, &HashMap::new())
                        .unwrap_or_else(|error| {
                            panic!(
                                "UNCERTIFIED native diamond {ty:?}/{condition:?}/{level:?}: {error}"
                            )
                        });
                    assert_eq!(result.metrics.function_count, 1);
                    assert!(!result.buffer.code_slice().is_empty());
                    let pointer = result.buffer.get_fn_ptr_bound(SYMBOL).unwrap();
                    // SAFETY: each signature exactly matches this module's
                    // four homogeneous I32/I64 C-ABI parameters and return.
                    // The wrappers remain borrowed from the live result buffer.
                    let narrow = if bits == 32 {
                        Some(unsafe {
                            result
                                .buffer
                                .get_fn_bound::<extern "C" fn(i32, i32, i32, i32) -> i32>(SYMBOL)
                                .unwrap()
                        })
                    } else {
                        None
                    };
                    // SAFETY: the I64 case has exactly the four-argument
                    // signature below, and this wrapper borrows its buffer.
                    let wide = if bits == 64 {
                        Some(unsafe {
                            result
                                .buffer
                                .get_fn_bound::<extern "C" fn(i64, i64, i64, i64) -> i64>(SYMBOL)
                                .unwrap()
                        })
                    } else {
                        None
                    };
                    let mut arms_seen = [0usize; 2];
                    for a in boundaries(bits) {
                        for b in boundaries(bits) {
                            let take_then = condition_holds(condition, bits, a, b);
                            arms_seen[usize::from(take_then)] += 1;
                            for [c, d] in arm_inputs {
                                let expected = if take_then {
                                    c.wrapping_add(1) & mask
                                } else {
                                    d.wrapping_sub(1) & mask
                                };
                                let typed = if let Some(function) = &narrow {
                                    u64::from(function.as_ref()(
                                        a as i32, b as i32, c as i32, d as i32,
                                    ) as u32)
                                } else {
                                    wide.as_ref().unwrap().as_ref()(
                                        a as i64, b as i64, c as i64, d as i64,
                                    ) as u64
                                };
                                assert_eq!(
                                    typed, expected,
                                    "typed {ty:?}/{condition:?}/{level:?} [{a:#x},{b:#x},{c:#x},{d:#x}]"
                                );
                                typed_calls += 1;
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
                                        "full-register {ty:?}/{condition:?}/{level:?}, poison={poison:#x?}, [{a:#x},{b:#x},{c:#x},{d:#x}]"
                                    );
                                    if bits == 32 {
                                        assert_eq!(
                                            actual >> 32,
                                            0,
                                            "these arithmetic W0 returns must zero the observed X0 upper half"
                                        );
                                    }
                                    full_register_calls += 1;
                                }
                            }
                        }
                    }
                    assert!(
                        arms_seen.iter().all(|count| *count > 0),
                        "both original source arms execute for every comparison: {arms_seen:?}"
                    );
                    compiled += 1;
                }
            }
        }
        assert_eq!(compiled, 80);
        assert_eq!(typed_calls, 25_920);
        assert_eq!(full_register_calls, 38_880);
    }
}
