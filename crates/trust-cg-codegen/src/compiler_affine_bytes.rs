// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Check the actual Core encoder output against its retained TrustIR and LIR.
//! This runs after all machine transformations, on the same byte allocation
//! subsequently consumed by the existing proof gate. Only the source may
//! determine unsupported coverage. No check here replaces proof promotion,
//! proves the Rust checker, or authorizes later mutation of the checked bytes.

use super::{CompileError, CoreAddressFreeMachineCompilationError};
use crate::macho::fixup::FixupList;
use crate::pipeline::{EncodedAarch64FixupSite, encode_function_with_fixups_and_sites};
use trust_cg_verify::aarch64_affine_lowering::{
    AffineByteError, TrustIrAffineLoweringError, check_aarch64_trust_ir_affine_bytes,
};

type EncodedFunction = (Vec<u8>, FixupList, Vec<EncodedAarch64FixupSite>);

#[cfg(test)]
#[path = "compiler_predicate_bytes_tests.rs"]
mod predicate_tests;

#[cfg(test)]
#[path = "compiler_select_bytes_tests.rs"]
mod select_tests;

#[cfg(test)]
#[path = "compiler_diamond_tests.rs"]
mod diamond_tests;

#[cfg(test)]
#[path = "compiler_core_diamond_controls.rs"]
mod core_diamond_controls;

#[cfg(all(test, target_arch = "aarch64", target_os = "macos"))]
#[path = "compiler_read_only_capture_tests.rs"]
mod read_only_capture_tests;

#[cfg(all(test, target_arch = "aarch64", target_os = "macos"))]
#[path = "compiler_scalar_action_capture_tests.rs"]
mod scalar_action_capture_tests;

#[cfg(all(test, target_arch = "aarch64", target_os = "macos"))]
#[path = "compiler_read_only_replay_tests.rs"]
mod read_only_replay_tests;

#[cfg(all(test, target_arch = "aarch64", target_os = "macos"))]
#[path = "compiler_scalar_action_replay_tests.rs"]
mod scalar_action_replay_tests;

pub(super) fn encode_core_function(
    module: &trust_ir::Module,
    ordinal: usize,
    lir: &trust_cg_lower::Function,
    machine: &trust_cg_ir::MachFunction,
) -> Result<EncodedFunction, CoreAddressFreeMachineCompilationError> {
    let encoded = encode_function_with_fixups_and_sites(machine).map_err(CompileError::Pipeline)?;
    check_core_bytes(module, ordinal, lir, &encoded.0, &encoded.1)?;
    Ok(encoded)
}

fn check_core_bytes(
    module: &trust_ir::Module,
    ordinal: usize,
    lir: &trust_cg_lower::Function,
    bytes: &[u8],
    fixups: &FixupList,
) -> Result<(), CoreAddressFreeMachineCompilationError> {
    match check_aarch64_trust_ir_affine_bytes(module, ordinal, lir, bytes) {
        Ok(_checked) => {
            // Even a currently matching word cannot be credited by this check
            // if a pending relocation can rewrite it after the comparison.
            if !fixups.is_empty() {
                return Err(
                    CoreAddressFreeMachineCompilationError::AffineBytesHaveFixups {
                        function: lir.name.clone(),
                        count: fixups.len(),
                    },
                );
            }
            Ok(())
        }
        Err(AffineByteError::Source(TrustIrAffineLoweringError::UnsupportedTrustIr(_))) => {
            // The raw Core check already records this same source-domain gap.
            // Broader programs retain all existing mandatory proof checks;
            // this uncredited branch does not provide a new certificate.
            Ok(())
        }
        Err(reason) => Err(
            CoreAddressFreeMachineCompilationError::AffineBytesRejected {
                function: lir.name.clone(),
                reason,
            },
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// This file's fixtures are hand-built and carry no codegen license
    /// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
    /// decision gate DG-73). Its lowerings state `Permit` explicitly, so none of
    /// them passes (or is refused) because the license silently refused it.
    fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
        trust_cg_lower::CodegenLicensePolicy::default()
            .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
    }

    use crate::macho::fixup::Fixup;
    use crate::pipeline::{OptLevel, Pipeline, PipelineConfig};
    use trust_cg_ir::{AArch64Opcode, MachFunction, MachOperand};
    use trust_cg_lower::Function;
    use trust_ir::{BinOp, Inst, Module, Ty};
    use trust_ir_build::ModuleBuilder;

    fn source(ty: Ty, op: BinOp) -> (Module, Function) {
        let mut builder = ModuleBuilder::new("final_core_bytes");
        let signature = builder.add_func_type(vec![ty.clone(); 2], vec![ty.clone()]);
        let mut function = builder.function("calculate", signature);
        let entry = function.create_block();
        let a = function.add_block_param(entry, ty.clone());
        let b = function.add_block_param(entry, ty.clone());
        function.switch_to_block(entry);
        let value = function.add(ty, a, b);
        function.ret(vec![value]);
        function.build();
        let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
        let Inst::BinOp { op: operation, .. } = &mut module.functions[0].blocks[0].body[0].inst
        else {
            panic!("binary source fixture");
        };
        *operation = op;
        let (lir, _) = trust_cg_lower::translate_function_with_license(
            &module.functions[0],
            &module,
            &permit_unlicensed(),
        )
        .unwrap();
        (module, lir)
    }

    fn prepare(module: &Module, lir: &Function, level: OptLevel) -> MachFunction {
        prepare_for("aarch64-unknown-linux-gnu", module, lir, level)
    }

    /// Exercise the frame theorem on both sealed-Core object targets. Linear
    /// leaves ordinarily omit their zero-storage frame, so these frame-specific
    /// fixtures request the FP/LR envelope explicitly.
    const SEALED_CORE_TRIPLES: [&str; 2] = ["aarch64-unknown-linux-gnu", "aarch64-apple-darwin"];

    fn prepare_for(triple: &str, module: &Module, lir: &Function, level: OptLevel) -> MachFunction {
        Pipeline::new(PipelineConfig {
            opt_level: level,
            verify: false,
            target_triple: triple.into(),
            aarch64_force_frame_pointers: true,
            ..Default::default()
        })
        .prepare_function_with_metrics_for_sealed_core(lir, None, module, 0)
        .unwrap()
        .0
    }

    #[test]
    fn generated_constant_leaf_frame_binds_its_complete_source() {
        let mut builder = ModuleBuilder::new("source_bound_leaf");
        let signature = builder.add_func_type(vec![], vec![Ty::I64]);
        let mut function = builder.function("answer", signature);
        let entry = function.create_block();
        function.switch_to_block(entry);
        let value = function.iconst(Ty::I64, 42);
        function.ret(vec![value]);
        function.build();
        let module = builder.build().expect("ModuleBuilder::build: test fixture");
        let (lir, _) = trust_cg_lower::translate_function_with_license(
            &module.functions[0],
            &module,
            &permit_unlicensed(),
        )
        .unwrap();
        for triple in SEALED_CORE_TRIPLES {
            for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                let machine = prepare_for(triple, &module, &lir, level);
                assert!(
                    trust_cg_verify::source_bound_frame::source_bound_frame(&lir, &machine).is_ok(),
                    "generated leaf for {triple} at {level:?}: {machine:#?}"
                );
            }
        }
    }

    #[test]
    fn generated_parameter_leaf_frames_bind_their_complete_source() {
        let mut failures = Vec::new();
        let mut cases = 0;
        for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
            let mut builder = ModuleBuilder::new("parameter_leaf");
            let signature = builder.add_func_type(vec![ty.clone()], vec![ty.clone()]);
            let mut function = builder.function("identity", signature);
            let entry = function.create_block();
            let value = function.add_block_param(entry, ty.clone());
            function.switch_to_block(entry);
            let value = function.copy(ty.clone(), value);
            function.ret(vec![value]);
            function.build();
            let module = builder.build().expect("ModuleBuilder::build: test fixture");
            let (lir, _) = trust_cg_lower::translate_function_with_license(
                &module.functions[0],
                &module,
                &permit_unlicensed(),
            )
            .unwrap();
            for (module, lir) in [
                (module, lir),
                source(ty.clone(), BinOp::Add),
                source(ty, BinOp::Sub),
            ] {
                for triple in SEALED_CORE_TRIPLES {
                    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                        cases += 1;
                        let machine = prepare_for(triple, &module, &lir, level);
                        if trust_cg_verify::source_bound_frame::source_bound_frame(&lir, &machine)
                            .is_err()
                        {
                            failures.push(format!(
                                "{} {:?} for {triple} at {level:?}: {:?}",
                                lir.name, lir.signature, machine.insts
                            ));
                        }
                    }
                }
            }
        }
        assert!(failures.is_empty(), "{}", failures.join("\n"));
        assert_eq!(cases, 96);
    }

    #[test]
    fn generated_linear_leaf_frames_bind_all_source_blocks() {
        for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
            let mut builder = ModuleBuilder::new("linear_leaf");
            let signature = builder.add_func_type(vec![ty.clone(); 2], vec![ty.clone()]);
            let mut function = builder.function("add_then_return", signature);
            let entry = function.create_block();
            let exit = function.create_block();
            let a = function.add_block_param(entry, ty.clone());
            let b = function.add_block_param(entry, ty.clone());
            function.switch_to_block(entry);
            let value = function.add(ty.clone(), a, b);
            let value = function.copy(ty, value);
            function.br(exit, vec![]);
            function.switch_to_block(exit);
            function.ret(vec![value]);
            function.build();
            let module = builder.build().expect("ModuleBuilder::build: test fixture");
            let (lir, _) = trust_cg_lower::translate_function_with_license(
                &module.functions[0],
                &module,
                &permit_unlicensed(),
            )
            .unwrap();
            assert_eq!(lir.blocks.len(), 2);
            for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                let machine = prepare(&module, &lir, level);
                assert!(
                    trust_cg_verify::source_bound_frame::source_bound_frame(&lir, &machine).is_ok(),
                    "linear leaf at {level:?}: {lir:#?}\n{machine:#?}"
                );
            }
        }
    }

    /// The mismatch classification must never fire on correct compiler
    /// output: every arithmetic shape of the source-bound JIT matrix binds
    /// (or is classified unsupported) at every level, never a mismatch.
    #[test]
    fn generated_arithmetic_matrix_never_classifies_as_mismatch() {
        use trust_cg_verify::source_bound_frame::{SourceBoundFrameRefusal, source_bound_frame};
        let mut bound = 0;
        for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
            for shape in [
                "add",
                "sub",
                "double",
                "add_small",
                "sub_small",
                "add_shifted",
                "sub_shifted",
                "add_negative",
                "sub_negative",
                "chain",
            ] {
                let mut builder = ModuleBuilder::new("arithmetic_matrix");
                let signature = builder.add_func_type(vec![ty.clone(); 2], vec![ty.clone()]);
                let mut function = builder.function("calculate", signature);
                let entry = function.create_block();
                let a = function.add_block_param(entry, ty.clone());
                let b = function.add_block_param(entry, ty.clone());
                function.switch_to_block(entry);
                let constant = |value: i128| match ty {
                    Ty::U32 => value as u32 as i128,
                    Ty::U64 => value as u64 as i128,
                    _ => value,
                };
                let result = match shape {
                    "add" => function.add(ty.clone(), a, b),
                    "sub" => function.sub(ty.clone(), a, b),
                    "double" => function.add(ty.clone(), a, a),
                    "chain" => {
                        let c = function.iconst(ty.clone(), 4096);
                        let d = function.iconst(ty.clone(), constant(-3));
                        let value = function.add(ty.clone(), a, c);
                        let value = function.sub(ty.clone(), value, b);
                        function.add(ty.clone(), value, d)
                    }
                    _ => {
                        let value = if shape.ends_with("small") {
                            4095
                        } else if shape.ends_with("shifted") {
                            4096
                        } else {
                            -1
                        };
                        let c = function.iconst(ty.clone(), constant(value));
                        if shape.starts_with("add") {
                            function.add(ty.clone(), a, c)
                        } else {
                            function.sub(ty.clone(), a, c)
                        }
                    }
                };
                function.ret(vec![result]);
                function.build();
                let module = builder.build().expect("ModuleBuilder::build: test fixture");
                let (lir, _) = trust_cg_lower::translate_function_with_license(
                    &module.functions[0],
                    &module,
                    &permit_unlicensed(),
                )
                .unwrap();
                for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                    let machine = prepare(&module, &lir, level);
                    match source_bound_frame(&lir, &machine) {
                        Ok(_) => bound += 1,
                        Err(SourceBoundFrameRefusal::Unsupported(_)) => {}
                        Err(SourceBoundFrameRefusal::Mismatch(mismatch)) => {
                            panic!("{ty:?}/{shape}/{level:?} misclassified: {mismatch}")
                        }
                    }
                }
            }
        }
        assert_eq!(bound, 160, "every matrix shape binds its complete source");
    }

    #[test]
    fn generated_diamond_leaf_frames_bind_both_source_arms() {
        use trust_ir::ICmpOp::*;
        let mut cases = 0;
        for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
            for comparison in [Eq, Ne, Slt, Sle, Sgt, Sge, Ult, Ule, Ugt, Uge] {
                let mut builder = ModuleBuilder::new("diamond_leaf");
                let signature = builder.add_func_type(vec![ty.clone(); 2], vec![ty.clone()]);
                let mut function = builder.function("choose_then_return", signature);
                let entry = function.create_block();
                let then_block = function.create_block();
                let else_block = function.create_block();
                let exit = function.create_block();
                let a = function.add_block_param(entry, ty.clone());
                let b = function.add_block_param(entry, ty.clone());
                let result = function.add_block_param(exit, ty.clone());
                function.switch_to_block(entry);
                let condition = function.icmp(comparison, ty.clone(), a, b);
                function.condbr(condition, then_block, vec![], else_block, vec![]);
                function.switch_to_block(then_block);
                let left = function.copy(ty.clone(), a);
                function.br(exit, vec![left]);
                function.switch_to_block(else_block);
                let right = function.copy(ty.clone(), b);
                function.br(exit, vec![right]);
                function.switch_to_block(exit);
                function.ret(vec![result]);
                function.build();
                let module = builder.build().expect("ModuleBuilder::build: test fixture");
                let (lir, _) = trust_cg_lower::translate_function_with_license(
                    &module.functions[0],
                    &module,
                    &permit_unlicensed(),
                )
                .unwrap();
                assert_eq!(lir.blocks.len(), 4);
                for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                    cases += 1;
                    let machine = prepare(&module, &lir, level);
                    assert!(
                        trust_cg_verify::source_bound_frame::source_bound_frame(&lir, &machine)
                            .is_ok(),
                        "diamond leaf {comparison:?} at {level:?}: {lir:#?}\n{machine:#?}"
                    );
                }
            }
        }
        assert_eq!(cases, 160);
    }

    #[test]
    fn linear_frame_offsets_match_actual_encoder_real_and_pseudo_nops() {
        use trust_cg_ir::function::{Signature, Type};
        use trust_cg_ir::regs::{SpecialReg, X0, X1, X29, X30};
        use trust_cg_ir::{InstFlags, InstId, MachInst};

        let (_, lir) = source(Ty::I64, BinOp::Add);
        for flags in [InstFlags::EMPTY, InstFlags::IS_PSEUDO] {
            let mut machine = MachFunction::new(
                lir.name.clone(),
                Signature::new(vec![Type::I64, Type::I64], vec![Type::I64]),
            );
            let pair = |offset| {
                vec![
                    MachOperand::PReg(X29),
                    MachOperand::PReg(X30),
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::Imm(offset),
                ]
            };
            for (opcode, operands) in [
                (AArch64Opcode::StpPreIndex, pair(-16)),
                (
                    AArch64Opcode::AddRI,
                    vec![
                        MachOperand::PReg(X29),
                        MachOperand::Special(SpecialReg::SP),
                        MachOperand::Imm(0),
                    ],
                ),
                (
                    AArch64Opcode::AddRR,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::PReg(X0),
                        MachOperand::PReg(X1),
                    ],
                ),
                (AArch64Opcode::LdpPostIndex, pair(16)),
                (AArch64Opcode::Ret, vec![MachOperand::PReg(X30)]),
            ] {
                let inst = MachInst::new(opcode, operands);
                // The I64 result is an ABI use of x0 even though RET encodes x30.
                let inst = if opcode == AArch64Opcode::Ret {
                    inst.with_implicit_uses(&[X0])
                } else {
                    inst
                };
                machine.push_inst(inst);
            }
            let body = machine.create_block();
            let exit = machine.create_block();
            machine.block_order = vec![machine.entry, exit, body];
            let mut nop = MachInst::new(AArch64Opcode::Nop, vec![]);
            nop.flags = flags;
            let nop = machine.push_inst(nop);
            let real_nop = flags == InstFlags::EMPTY;
            let offset = if real_nop { 4 } else { 3 };
            let enter = machine.push_inst(MachInst::new(
                AArch64Opcode::B,
                vec![MachOperand::Imm(offset)],
            ));
            let leave = machine.push_inst(MachInst::new(
                AArch64Opcode::B,
                vec![MachOperand::Imm(-offset)],
            ));
            machine.blocks[0].insts = vec![InstId(0), InstId(1), enter];
            machine.blocks[0].succs = vec![body];
            machine.blocks[body.0 as usize].insts = vec![InstId(2), leave];
            machine.blocks[body.0 as usize].preds = vec![machine.entry];
            machine.blocks[body.0 as usize].succs = vec![exit];
            machine.blocks[exit.0 as usize].insts = vec![nop, InstId(3), InstId(4)];
            machine.blocks[exit.0 as usize].preds = vec![body];
            assert!(
                trust_cg_verify::source_bound_frame::source_bound_frame(&lir, &machine).is_ok()
            );

            // Use the real encoder, not the binder's own word-count helper.
            let (bytes, fixups, _) = encode_function_with_fixups_and_sites(&machine).unwrap();
            assert!(fixups.is_empty());
            let words: Vec<u32> = bytes
                .as_chunks::<4>()
                .0
                .iter()
                .map(|word| u32::from_le_bytes(*word))
                .collect();
            let mut expected = vec![
                0xa9bf7bfd,
                0x910003fd,
                if real_nop { 0x14000004 } else { 0x14000003 },
            ];
            if real_nop {
                expected.push(0xd503201f);
            }
            expected.extend([
                0xa8c17bfd,
                0xd65f03c0,
                0x8b010000,
                if real_nop { 0x17fffffc } else { 0x17fffffd },
            ]);
            assert_eq!(words, expected);
            let branch_target = |at: usize| -> usize {
                assert_eq!(words[at] & 0xfc000000, 0x14000000);
                let displacement = ((words[at] << 6) as i32) >> 6;
                usize::try_from(at as i64 + i64::from(displacement)).unwrap()
            };
            assert_eq!(words[branch_target(2)], 0x8b010000);
            assert_eq!(branch_target(words.len() - 1), 3);

            let wrong = if real_nop { 3 } else { 4 };
            machine.insts[enter.0 as usize].operands[0] = MachOperand::Imm(wrong);
            machine.insts[leave.0 as usize].operands[0] = MachOperand::Imm(-wrong);
            // Both miscounted displacements land inside a block: a typed
            // branch-target mismatch, never an unsupported shape.
            assert!(matches!(
                trust_cg_verify::source_bound_frame::source_bound_frame(&lir, &machine),
                Err(trust_cg_verify::source_bound_frame::SourceBoundFrameRefusal::Mismatch(
                    trust_cg_verify::source_bound_frame::FrameBindingMismatch::BranchTarget {
                        defect: trust_cg_verify::source_bound_frame::BranchTargetDefect::NoBlockStart {
                            ..
                        },
                        ..
                    }
                ))
            ));
        }
    }

    #[test]
    fn actual_core_encoder_checks_complete_arithmetic_at_all_levels() {
        for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
            for op in [BinOp::Add, BinOp::Sub] {
                let (module, lir) = source(ty.clone(), op);
                for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                    let machine = prepare(&module, &lir, level);
                    let (code, fixups, sites) =
                        encode_core_function(&module, 0, &lir, &machine).unwrap();
                    assert!(!code.is_empty());
                    assert!(fixups.is_empty() && sites.is_empty());
                }
            }
        }
    }

    #[test]
    fn final_core_encoder_rejects_changed_machine_after_raw_source_check() {
        let (module, lir) = source(Ty::I64, BinOp::Add);
        let original = prepare(&module, &lir, OptLevel::O2);
        for replacement in [AArch64Opcode::SubRR, AArch64Opcode::MulRR] {
            let mut machine = original.clone();
            let instruction = machine
                .insts
                .iter_mut()
                .find(|i| i.opcode == AArch64Opcode::AddRR)
                .unwrap();
            instruction.opcode = replacement;
            assert!(matches!(
                encode_core_function(&module, 0, &lir, &machine),
                Err(CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. })
            ));
        }
        let mut machine = original;
        let instruction = machine
            .insts
            .iter_mut()
            .find(|i| i.opcode == AArch64Opcode::AddRR)
            .unwrap();
        instruction.operands[2] = instruction.operands[1].clone();
        assert!(matches!(
            encode_core_function(&module, 0, &lir, &machine),
            Err(
                CoreAddressFreeMachineCompilationError::AffineBytesRejected {
                    reason: AffineByteError::ReturnMismatch,
                    ..
                }
            )
        ));
    }

    #[test]
    fn final_core_encoder_rechecks_source_identity_and_lir_semantics() {
        let (mut module, mut lir) = source(Ty::I64, BinOp::Add);
        let machine = prepare(&module, &lir, OptLevel::O2);
        assert!(encode_core_function(&module, 1, &lir, &machine).is_err());
        lir.blocks.get_mut(&lir.entry_block).unwrap().instructions[0].opcode =
            trust_cg_lower::instructions::Opcode::Isub;
        assert!(matches!(
            encode_core_function(&module, 0, &lir, &machine),
            Err(CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. })
        ));
        module.functions[0].name = "different_source".into();
        module.functions[0].blocks.clear();
        assert!(matches!(
            encode_core_function(&module, 0, &lir, &machine),
            Err(CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. })
        ));
    }

    #[test]
    fn final_core_encoder_does_not_turn_unsupported_source_into_proof_authority() {
        let (module, lir) = source(Ty::I64, BinOp::Mul);
        let machine = prepare(&module, &lir, OptLevel::O2);
        let (code, _, _) = encode_core_function(&module, 0, &lir, &machine).unwrap();
        assert!(matches!(
            check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &code),
            Err(AffineByteError::Source(
                TrustIrAffineLoweringError::UnsupportedTrustIr(_)
            ))
        ));
        // The ordinary final FunctionVerifier and Core promotion gate still
        // decide evidence. This helper returns bytes, never a proof report.
    }

    #[test]
    fn final_core_encoder_binds_frame_save_restore_and_return() {
        let (module, lir) = source(Ty::I64, BinOp::Add);
        let original = prepare(&module, &lir, OptLevel::O2);
        let (original_code, _, _) = encode_core_function(&module, 0, &lir, &original).unwrap();
        for (opcode, operand, replacement) in [
            (AArch64Opcode::StpPreIndex, 3, MachOperand::Imm(-32)),
            (AArch64Opcode::LdpPostIndex, 3, MachOperand::Imm(32)),
            (
                AArch64Opcode::LdpPostIndex,
                1,
                MachOperand::PReg(trust_cg_ir::regs::X19),
            ),
        ] {
            let mut machine = original.clone();
            let instruction = machine
                .insts
                .iter_mut()
                .find(|i| i.opcode == opcode)
                .unwrap();
            let original_word =
                crate::aarch64::encode::encode_instruction(instruction).expect("frame word");
            instruction.operands[operand] = replacement;
            let corrupted_word =
                crate::aarch64::encode::encode_instruction(instruction).expect("frame word");
            // The final-stream frame dataflow net rejects the corrupted
            // save/restore on the MachIR stream before bytes exist.
            let error = encode_core_function(&module, 0, &lir, &machine)
                .expect_err("a corrupted frame save/restore must not encode");
            assert!(
                error.to_string().contains("[TCG-A64-SPILL-SLOT]"),
                "{opcode:?}: {error}"
            );
            // The source/byte boundary independently rejects the same word.
            let mut code = original_code.clone();
            let sites: Vec<usize> = code
                .as_chunks::<4>()
                .0
                .iter()
                .enumerate()
                .filter(|(_, word)| {
                    u32::from_le_bytes([word[0], word[1], word[2], word[3]]) == original_word
                })
                .map(|(index, _)| index * 4)
                .collect();
            assert_eq!(sites.len(), 1, "{opcode:?}: one frame word");
            code[sites[0]..sites[0] + 4].copy_from_slice(&corrupted_word.to_le_bytes());
            assert!(
                matches!(
                    check_core_bytes(&module, 0, &lir, &code, &FixupList::new()),
                    Err(CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. })
                ),
                "{opcode:?}"
            );
        }
        // Mutate the actual return word. A MachIR-only RET operand mutation
        // can already be rejected by the encoder's independent decode check;
        // it does not specifically exercise the new source/byte boundary.
        let (mut code, _, _) = encode_core_function(&module, 0, &lir, &original).unwrap();
        let end = code.len();
        code[end - 4..].copy_from_slice(&0xd65f0000_u32.to_le_bytes()); // RET X0
        assert!(matches!(
            check_core_bytes(&module, 0, &lir, &code, &FixupList::new()),
            Err(
                CoreAddressFreeMachineCompilationError::AffineBytesRejected {
                    reason: AffineByteError::InvalidBytes { .. },
                    ..
                }
            )
        ));
    }

    #[test]
    fn matching_core_bytes_cannot_carry_a_later_mutating_fixup() {
        let (module, lir) = source(Ty::I64, BinOp::Add);
        let machine = prepare(&module, &lir, OptLevel::O2);
        let (mut code, _, _) = encode_core_function(&module, 0, &lir, &machine).unwrap();
        for offset in [0, code.len() as u32, u32::MAX] {
            let mut fixups = FixupList::new();
            fixups.push(Fixup::branch_sym(offset, "unrelated".into()));
            assert!(matches!(
                check_core_bytes(&module, 0, &lir, &code, &fixups),
                Err(CoreAddressFreeMachineCompilationError::AffineBytesHaveFixups { count: 1, .. })
            ));
        }
        code[0] ^= 1;
        assert!(matches!(
            check_core_bytes(&module, 0, &lir, &code, &FixupList::new()),
            Err(CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. })
        ));
    }

    #[test]
    fn actual_core_encoder_binds_integer_select_operands_and_conditions() {
        use trust_ir::ICmpOp::*;
        for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
            for op in [Eq, Ne, Slt, Sle, Sgt, Sge, Ult, Ule, Ugt, Uge] {
                let mut builder = ModuleBuilder::new("final_core_select");
                let signature = builder.add_func_type(vec![ty.clone(); 4], vec![ty.clone()]);
                let mut function = builder.function("choose", signature);
                let entry = function.create_block();
                let args: Vec<_> = (0..4)
                    .map(|_| function.add_block_param(entry, ty.clone()))
                    .collect();
                function.switch_to_block(entry);
                let condition = function.icmp(op, ty.clone(), args[0], args[1]);
                let result = function.select(ty.clone(), condition, args[2], args[3]);
                function.ret(vec![result]);
                function.build();
                let module = builder.build().expect("ModuleBuilder::build: test fixture");
                let (lir, _) = trust_cg_lower::translate_function_with_license(
                    &module.functions[0],
                    &module,
                    &permit_unlicensed(),
                )
                .unwrap();
                for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                    let machine = prepare(&module, &lir, level);
                    let (code, _, _) = encode_core_function(&module, 0, &lir, &machine).unwrap();
                    let select = code
                        .as_chunks::<4>()
                        .0
                        .iter()
                        .position(|bytes| u32::from_le_bytes(*bytes) & 0x7fe00c00 == 0x1a800000)
                        .unwrap();
                    for bit in [5, 12, 16, 31] {
                        let mut changed = code.clone();
                        changed[select * 4 + bit / 8] ^= 1 << (bit % 8);
                        assert!(
                            matches!(
                                check_core_bytes(&module, 0, &lir, &changed, &FixupList::new()),
                                Err(
                                    CoreAddressFreeMachineCompilationError::AffineBytesRejected { .. }
                                )
                            ),
                            "{ty:?}/{op:?}/{level:?}/bit{bit}"
                        );
                    }
                }
            }
        }
    }
}
