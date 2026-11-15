// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Actual MRS-NZCV observation through the shared pass, pipeline and JIT.
//!
//! This is a raw-MachIR, compatibility/Unchecked native regression, not a
//! frontend refinement, independently checked theorem or caller certificate.
//! MRS-NZCV remains outside the decoded-value proof profile. The production
//! pipeline allocates the virtual registers; the JIT's bound callable lease
//! retains the executable image throughout every call. No custom emitter or
//! architectural interpreter is used.

#![cfg(all(target_arch = "aarch64", target_os = "macos"))]

use std::collections::HashMap;

use trust_cg_codegen::jit::{JitCompiler, JitConfig};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::aarch64_regs::X0;
use trust_cg_ir::{AArch64Opcode as O, MachFunction, MachInst, MachOperand as A};
use trust_cg_ir::{RegClass, Signature, Type, VReg};
use trust_cg_opt::and_cmp_fuse::AndCmpFuse;
use trust_cg_opt::pass_manager::MachinePass;

const ENTRY: &str = "observe_cmp_nzcv";
const NZCV_SYSREG: i64 = 0xDA10;
const CARRY: u64 = 1 << 29;

fn original(mask: u64) -> MachFunction {
    let mut function = MachFunction::new(
        ENTRY.into(),
        Signature::new(vec![Type::I64], vec![Type::I64]),
    );
    let argument = A::VReg(VReg::new(function.alloc_vreg(), RegClass::Gpr64));
    let masked = A::VReg(VReg::new(function.alloc_vreg(), RegClass::Gpr64));
    let flags = A::VReg(VReg::new(function.alloc_vreg(), RegClass::Gpr64));
    let block = function.entry;
    for instruction in [
        MachInst::new(O::Copy, vec![argument.clone(), A::PReg(X0)]),
        MachInst::new(
            O::AndRI,
            vec![masked.clone(), argument, A::Imm(mask as i64)],
        ),
        MachInst::new(O::CmpRI, vec![masked, A::Imm(0)]),
        MachInst::new(O::Mrs, vec![flags.clone(), A::Imm(NZCV_SYSREG)]),
        MachInst::new(O::Copy, vec![A::PReg(X0), flags]),
        MachInst::new(O::Ret, vec![]).with_implicit_uses(&[X0]),
    ] {
        let id = function.push_inst(instruction);
        function.append_inst(block, id);
    }
    function
}

/// The historical replacement is an explicit negative control, never a
/// production pass result or proof-accepted input. Keep stable arena IDs and
/// an inert tombstone for its removed AND so the ordinary pipeline owns it.
fn historical_tst_mutant(source: &MachFunction) -> MachFunction {
    let mut mutant = source.clone();
    let ids = mutant.block(mutant.entry).insts.clone();
    let and = ids[1];
    let compare = ids[2];
    assert_eq!(mutant.inst(and).opcode, O::AndRI);
    assert_eq!(mutant.inst(compare).opcode, O::CmpRI);
    let operands = mutant.inst(and).operands[1..].to_vec();
    *mutant.inst_mut(compare) = MachInst::new(O::Tst, operands);
    *mutant.inst_mut(and) = MachInst::new(O::Nop, vec![]);
    mutant.block_mut(mutant.entry).insts.retain(|&id| id != and);
    mutant
}

fn assert_pass_has_a_live_safe_twin(source: &MachFunction) {
    let mut safe = source.clone();
    let ids = safe.block(safe.entry).insts.clone();
    safe.block_mut(safe.entry)
        .insts
        .retain(|&id| id != ids[3] && id != ids[4]);
    for id in [ids[3], ids[4]] {
        *safe.inst_mut(id) = MachInst::new(O::Nop, vec![]);
    }
    assert!(
        AndCmpFuse.run(&mut safe),
        "the safe immediate arm must remain enabled"
    );
    assert!(
        safe.block(safe.entry)
            .insts
            .iter()
            .any(|&id| safe.inst(id).opcode == O::Tst)
    );
}

fn compile(mut function: MachFunction, opt_level: OptLevel) -> trust_cg_codegen::ExecutableBuffer {
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level,
        verify: false,
        target_triple: "aarch64-apple-darwin".into(),
        ..PipelineConfig::default()
    });
    pipeline
        .prepare_ir_function(&mut function)
        .unwrap_or_else(|error| panic!("{opt_level:?}: prepare: {error}"));
    assert!(
        function
            .block_order
            .iter()
            .flat_map(|&block| &function.block(block).insts)
            .any(|&id| {
                let instruction = function.inst(id);
                instruction.opcode == O::Mrs
                    && instruction.operands.get(1) == Some(&A::Imm(NZCV_SYSREG))
            })
    );
    let buffer = JitCompiler::new(JitConfig {
        opt_level,
        verify: false,
        ..JitConfig::default()
    })
    .compile_raw(&[function], &HashMap::new())
    .unwrap_or_else(|error| panic!("{opt_level:?}: raw JIT: {error}"));
    assert!(
        buffer.certificate(ENTRY).is_none(),
        "unchecked diagnostic mints no certificate"
    );
    buffer
}

#[test]
fn actual_mrs_nzcv_keeps_cmp_carry_across_pass_and_pipeline_o0_to_o3() {
    let inputs = [
        0,
        1,
        2,
        u64::MAX,
        1 << 63,
        (1 << 63) | 1,
        0xDEAD_BEEF_1234_5678,
    ];
    for mask in [1u64, 1 << 63] {
        let source = original(mask);
        assert_pass_has_a_live_safe_twin(&source);
        let mut optimized = source.clone();
        let before = format!("{optimized:?}");
        assert!(!AndCmpFuse.run(&mut optimized), "MRS makes NZCV observable");
        assert_eq!(format!("{optimized:?}"), before);
        let mutant = historical_tst_mutant(&source);
        for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let original_buffer = compile(source.clone(), level);
            let optimized_buffer = compile(optimized.clone(), level);
            let mutant_buffer = compile(mutant.clone(), level);
            // SAFETY: all three real Mach signatures are (i64)->i64, with the
            // same integer ABI as (u64)->u64. Each bound callable borrows its
            // live buffer, whose production JIT owns W^X publication.
            let original =
                unsafe { original_buffer.get_fn_bound::<extern "C" fn(u64) -> u64>(ENTRY) }
                    .expect("original entry");
            let optimized =
                unsafe { optimized_buffer.get_fn_bound::<extern "C" fn(u64) -> u64>(ENTRY) }
                    .expect("actual pass entry");
            let mutant = unsafe { mutant_buffer.get_fn_bound::<extern "C" fn(u64) -> u64>(ENTRY) }
                .expect("historical mutant entry");
            for input in inputs {
                let masked = input & mask;
                // CMP subtracts zero: no borrow (C=1), no overflow; N and Z
                // reflect the masked result. TST instead clears C and V.
                let expected = ((masked >> 63) << 31) | (u64::from(masked == 0) << 30) | CARRY;
                let original_flags = original.as_ref()(input);
                let optimized_flags = optimized.as_ref()(input);
                let mutant_flags = mutant.as_ref()(input);
                assert_eq!(
                    original_flags, expected,
                    "original {level:?}/{mask:#x}/{input:#x}"
                );
                assert_eq!(
                    optimized_flags, expected,
                    "pass {level:?}/{mask:#x}/{input:#x}"
                );
                assert_eq!(
                    mutant_flags,
                    expected & !CARRY,
                    "mutant {level:?}/{mask:#x}/{input:#x}"
                );
                assert_ne!(original_flags, mutant_flags);
            }
        }
    }
}
