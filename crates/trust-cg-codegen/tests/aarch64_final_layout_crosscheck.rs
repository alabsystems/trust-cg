// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Final-layout cross-check and proof-grade late-layout policy on real
//! pipeline output for both AArch64 object formats (Mach-O for
//! `aarch64-apple-darwin`, ELF for `aarch64-unknown-linux-gnu`).
//!
//! The pipeline-output controls are host-neutral. The JIT controls compile
//! and execute on an AArch64 host only; there they are required, never
//! skipped. Nothing here establishes proof of the late passes: it checks the
//! final words against offsets re-derived from the final layout, and that
//! proof-grade routes refuse ambient late-layout controls.

// Only the host-JIT module below (AArch64 hosts) compiles raw functions.
#[cfg(target_arch = "aarch64")]
use std::collections::HashMap;

use trust_cg_codegen::aarch64::layout_crosscheck::{LayoutCrossCheckError, check_final_layout};
use trust_cg_codegen::pipeline::{
    AARCH64_LATE_LAYOUT_CONTROLS, OptLevel, Pipeline, PipelineConfig, PipelineError,
    encode_function_with_fixups_and_blocks,
};
use trust_cg_ir::{AArch64Opcode, MachFunction, MachOperand};
use trust_ir::{ICmpOp, Module, Ty};
use trust_ir_build::ModuleBuilder;

const TRIPLES: [&str; 2] = ["aarch64-apple-darwin", "aarch64-unknown-linux-gnu"];

/// `sum_below(n)`: `t = 0; for i in 0..n { t = 3 * t + step(i) }` with
/// `step(i) = i`, or an external `observe(i)` call inside the loop so the
/// object also carries a Branch26 fixup. The recurrence keeps a real loop
/// (no closed form) for loop-head alignment to act on.
fn loop_module(observe: bool) -> Module {
    let mut builder = ModuleBuilder::new("final_layout");
    let signature = builder.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let observer = observe.then(|| builder.declare_function("observe", signature));
    let mut function = builder.function("sum_below", signature);
    let entry = function.create_block();
    let header = function.create_block();
    let body = function.create_block();
    let exit = function.create_block();
    let limit = function.add_block_param(entry, Ty::I64);
    let index = function.add_block_param(header, Ty::I64);
    let total = function.add_block_param(header, Ty::I64);
    let done = function.add_block_param(exit, Ty::I64);
    function.switch_to_block(entry);
    let zero = function.iconst(Ty::I64, 0);
    function.br(header, vec![zero, zero]);
    function.switch_to_block(header);
    let more = function.icmp(ICmpOp::Slt, Ty::I64, index, limit);
    function.condbr(more, body, vec![], exit, vec![total]);
    function.switch_to_block(body);
    let step = match observer {
        Some(observer) => function.call(observer, vec![index]),
        None => index,
    };
    let three = function.iconst(Ty::I64, 3);
    let scaled = function.mul(Ty::I64, total, three);
    let next_total = function.add(Ty::I64, scaled, step);
    let one = function.iconst(Ty::I64, 1);
    let next_index = function.add(Ty::I64, index, one);
    function.br(header, vec![next_index, next_total]);
    function.switch_to_block(exit);
    function.ret(vec![done]);
    function.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

fn prepare(triple: &str, observe: bool) -> MachFunction {
    let module = loop_module(observe);
    let function = module
        .functions
        .iter()
        .find(|function| function.name == "sum_below")
        .unwrap();
    let (lir, _) =
        trust_cg_lower::translate_function_with_license(function, &module, &permit_unlicensed())
            .unwrap();
    Pipeline::new(config(triple))
        .prepare_function(&lir)
        .unwrap()
}

fn config(triple: &str) -> PipelineConfig {
    PipelineConfig {
        opt_level: OptLevel::O2,
        target_triple: triple.to_owned(),
        verify: false,
        ..Default::default()
    }
}

/// Byte offsets of every emitted local branch with a resolved immediate.
fn branch_offsets(func: &MachFunction) -> Vec<usize> {
    let mut offsets = Vec::new();
    let mut offset = 0;
    for &block in &func.block_order {
        for &id in &func.block(block).insts {
            let inst = func.inst(id);
            if inst.is_pseudo() {
                continue;
            }
            let target = match inst.opcode {
                AArch64Opcode::B => inst.operands.first(),
                AArch64Opcode::BCond | AArch64Opcode::Cbz | AArch64Opcode::Cbnz => {
                    inst.operands.get(1)
                }
                AArch64Opcode::Tbz | AArch64Opcode::Tbnz => inst.operands.get(2),
                _ => None,
            };
            if matches!(target, Some(MachOperand::Imm(_))) {
                offsets.push(offset);
            }
            offset += 4;
        }
    }
    offsets
}

#[test]
fn pipeline_loop_output_matches_its_final_layout_on_both_formats() {
    // Loop-head alignment is opt-in (`TCG_LOOP_HEAD_ALIGN=1` outside the
    // bridge): the default layout is unpadded at the 4-byte placement, and the
    // opt-in pads the loop head and pins the function at 32 bytes. Both
    // layouts must satisfy the cross-check. The opt-in is visible only while
    // the function is prepared, so the proof-grade encodes below never see it.
    for triple in TRIPLES {
        for padded in [false, true] {
            let func = if padded {
                trust_cg_process_env::with_env_overrides(&[("TCG_LOOP_HEAD_ALIGN", "1")], || {
                    prepare(triple, true)
                })
            } else {
                prepare(triple, true)
            };
            check_pipeline_loop_output(triple, padded, &func);
        }
    }
}

fn check_pipeline_loop_output(triple: &str, padded: bool, func: &MachFunction) {
    let align_nops = func
        .block_order
        .iter()
        .flat_map(|block| func.block(*block).insts.iter())
        .filter(|id| func.inst(**id).opcode == AArch64Opcode::AlignNop)
        .count();
    if padded {
        assert_eq!(
            func.text_align_log2, 5,
            "{triple}: the opt-in pins the function"
        );
    } else {
        assert_eq!(
            func.text_align_log2, 2,
            "{triple}: default 4-byte placement"
        );
        assert_eq!(align_nops, 0, "{triple}: the default layout is unpadded");
    }
    let (code, fixups, blocks) = encode_function_with_fixups_and_blocks(func).unwrap();
    assert!(!branch_offsets(func).is_empty(), "{triple}");
    assert_eq!(fixups.len(), 1, "{triple}: one call relocation");
    // Pipeline output satisfies the stronger proof-grade CFG binding.
    check_final_layout(func, &code, Some(&fixups), &blocks, true).unwrap();
    // Both object writers consume the checked encode on both policies.
    for pipeline in [
        Pipeline::new(config(triple)),
        Pipeline::new(config(triple)).with_proof_grade_aarch64_publication(),
    ] {
        let object = pipeline.compile_module(std::slice::from_ref(func)).unwrap();
        let magic = &object[..4];
        if triple.contains("darwin") {
            assert_eq!(magic, [0xcf, 0xfa, 0xed, 0xfe], "{triple}: Mach-O");
        } else {
            assert_eq!(magic, [0x7f, b'E', b'L', b'F'], "{triple}: ELF");
        }
    }
}

/// A dense switch: its jump table follows the body and is addressed by ADR.
fn switch_function(triple: &str) -> MachFunction {
    let mut builder = ModuleBuilder::new("final_layout_switch");
    let signature = builder.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut function = builder.function("dense_switch", signature);
    let entry = function.create_block();
    let selector = function.add_block_param(entry, Ty::I64);
    let arms: Vec<_> = (0..6).map(|_| function.create_block()).collect();
    let default = function.create_block();
    function.switch_to_block(entry);
    let cases = arms
        .iter()
        .enumerate()
        .map(|(case, target)| trust_ir::SwitchCase {
            value: trust_ir::Constant::Int(case as i128),
            target: *target,
            args: vec![],
        })
        .collect();
    function.switch(selector, cases, default, vec![]);
    for (case, arm) in arms.iter().enumerate() {
        function.switch_to_block(*arm);
        let value = function.iconst(Ty::I64, 10 * case as i128 + 7);
        function.ret(vec![value]);
    }
    function.switch_to_block(default);
    let value = function.iconst(Ty::I64, -1);
    function.ret(vec![value]);
    function.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .unwrap();
    Pipeline::new(config(triple))
        .prepare_function(&lir)
        .unwrap()
}

#[test]
fn jump_tables_are_rederived_under_cfg_authority_on_both_formats() {
    for triple in TRIPLES {
        let func = switch_function(triple);
        assert_eq!(func.jump_tables.len(), 1, "{triple}: dense lowering");
        let (code, fixups, blocks) = encode_function_with_fixups_and_blocks(&func).unwrap();
        check_final_layout(&func, &code, Some(&fixups), &blocks, true).unwrap();
        let body: usize = func
            .block_order
            .iter()
            .flat_map(|block| &func.block(*block).insts)
            .filter(|id| !func.inst(**id).is_pseudo())
            .count()
            * 4;
        assert_eq!(code.len(), body + 4 * func.jump_tables[0].targets.len());
        // Every table entry is re-derived from the recomputed block starts.
        for entry in (body..code.len()).step_by(4) {
            let mut wrong = code.clone();
            wrong[entry] ^= 4;
            assert!(
                matches!(
                    check_final_layout(&func, &wrong, Some(&fixups), &blocks, false),
                    Err(LayoutCrossCheckError::JumpTableEntry { .. })
                ),
                "{triple}: entry at {entry}"
            );
        }
        let object = Pipeline::new(config(triple))
            .with_proof_grade_aarch64_publication()
            .compile_module(std::slice::from_ref(&func))
            .unwrap();
        assert!(!object.is_empty());
    }
}

#[test]
fn corrupted_words_offsets_and_fixups_fail_closed_on_both_formats() {
    for triple in TRIPLES {
        let func = prepare(triple, true);
        let (code, fixups, blocks) = encode_function_with_fixups_and_blocks(&func).unwrap();
        for at in branch_offsets(&func) {
            let mut wrong = code.clone();
            wrong[at] ^= 1 << 5;
            assert!(
                matches!(
                    check_final_layout(&func, &wrong, Some(&fixups), &blocks, false),
                    Err(LayoutCrossCheckError::Displacement { .. })
                ),
                "{triple}: branch at {at}"
            );
        }
        let call = fixups.iter().next().unwrap().offset as usize;
        let mut wrong = code.clone();
        wrong[call] |= 1;
        assert!(matches!(
            check_final_layout(&func, &wrong, Some(&fixups), &blocks, false),
            Err(LayoutCrossCheckError::FixupPlaceholder { .. })
        ));
        let none = trust_cg_codegen::macho::fixup::FixupList::new();
        assert!(matches!(
            check_final_layout(&func, &code, Some(&none), &blocks, false),
            Err(LayoutCrossCheckError::MissingFixup { .. })
        ));
        let mut moved = fixups.clone();
        moved.as_mut_slice()[0].offset += 4;
        assert!(check_final_layout(&func, &code, Some(&moved), &blocks, false).is_err());
        // Right site, kind and placeholder, but another callee.
        let mut retargeted = fixups.clone();
        retargeted.as_mut_slice()[0].target =
            trust_cg_codegen::macho::FixupTarget::NamedSymbol("not_observe".into());
        assert!(matches!(
            check_final_layout(&func, &code, Some(&retargeted), &blocks, false),
            Err(LayoutCrossCheckError::FixupSymbol { .. })
        ));
        for block in func.block_order.iter().skip(1) {
            let mut drifted = blocks.clone();
            *drifted.get_mut(block).unwrap() += 4;
            assert!(
                matches!(
                    check_final_layout(&func, &code, Some(&fixups), &drifted, false),
                    Err(LayoutCrossCheckError::BlockOffset { .. })
                ),
                "{triple}: block {block:?}"
            );
        }
        let mut long = code.clone();
        long.extend_from_slice(&0xd503_201fu32.to_le_bytes());
        assert!(matches!(
            check_final_layout(&func, &long, Some(&fixups), &blocks, false),
            Err(LayoutCrossCheckError::TrailingBytes { .. })
        ));
    }
}

#[test]
fn proof_grade_object_routes_refuse_every_late_layout_control() {
    for triple in TRIPLES {
        let func = prepare(triple, true);
        for control in AARCH64_LATE_LAYOUT_CONTROLS {
            trust_cg_process_env::with_env_overrides(&[(*control, "1")], || {
                // Ordinary routes keep the control, but it is not part of any
                // artifact identity: reuse is refused while it is visible.
                assert!(
                    trust_cg_codegen::artifact_reuse_permit().is_none(),
                    "{control}"
                );
                let refused = Pipeline::new(config(triple))
                    .with_proof_grade_aarch64_publication()
                    .compile_module(std::slice::from_ref(&func));
                assert!(
                    matches!(
                        &refused,
                        Err(PipelineError::AmbientLateLayoutControl { control: named, .. })
                            if named == control
                    ),
                    "{triple}: {control}: {refused:?}"
                );
                Pipeline::new(config(triple))
                    .compile_module(std::slice::from_ref(&func))
                    .unwrap();
            });
        }
    }
}

#[cfg(target_arch = "aarch64")]
fn expected(limit: i64) -> i64 {
    (0..limit).fold(0i64, |total, index| {
        total.wrapping_mul(3).wrapping_add(index)
    })
}

#[cfg(target_arch = "aarch64")]
mod host_jit {
    use super::*;
    use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitValidationMode};
    use trust_cg_codegen::jit::{JitCompiler, JitConfig, JitError};

    fn host_function() -> MachFunction {
        let triple = PipelineConfig::for_host_aarch64().target_triple;
        prepare(&triple, false)
    }

    #[test]
    fn raw_jit_executes_checked_layout_and_verifying_jit_refuses_controls() {
        let func = host_function();
        for verify in [false, true] {
            let buffer = JitCompiler::new(JitConfig {
                verify,
                ..Default::default()
            })
            .compile_raw(std::slice::from_ref(&func), &HashMap::new())
            .unwrap();
            let sum: extern "C" fn(i64) -> i64 = unsafe {
                buffer
                    .get_fn_bound("sum_below")
                    .expect("published symbol")
                    .into_inner()
            };
            for limit in [0, 1, 2, 10, 45] {
                assert_eq!(sum(limit), expected(limit), "verify={verify} n={limit}");
            }
        }
        trust_cg_process_env::with_env_overrides(&[("TCG_NO_POST_INDEX_LATE", "")], || {
            let refused = JitCompiler::new(JitConfig {
                verify: true,
                ..Default::default()
            })
            .compile_raw(std::slice::from_ref(&func), &HashMap::new());
            assert!(matches!(
                refused,
                Err(JitError::Pipeline(
                    PipelineError::AmbientLateLayoutControl {
                        control: "TCG_NO_POST_INDEX_LATE",
                        ..
                    }
                ))
            ));
            JitCompiler::new(JitConfig::default())
                .compile_raw(std::slice::from_ref(&func), &HashMap::new())
                .unwrap();
        });
    }

    #[test]
    fn verifying_compiler_jit_refuses_late_layout_controls() {
        let module = loop_module(false);
        trust_cg_process_env::with_env_overrides(&[("TCG_LOOP_ALIGN_MAX_SKIP", "4")], || {
            let verifying = Compiler::new(CompilerConfig {
                jit_validation_mode_override: Some(JitValidationMode::AlwaysVerify),
                ..CompilerConfig::for_host_jit()
            })
            .with_codegen_license(permit_unlicensed());
            let refused = verifying.compile_module_to_jit(&module, &HashMap::new());
            let message = refused
                .err()
                .map(|error| error.to_string())
                .unwrap_or_default();
            assert!(
                message.contains("[TCG-A64-LATE-LAYOUT-POLICY]")
                    && message.contains("TCG_LOOP_ALIGN_MAX_SKIP"),
                "{message}"
            );
            // The dev-only unchecked route keeps legacy switch semantics.
            let unchecked = Compiler::new(CompilerConfig::for_host_jit_unchecked())
                .with_codegen_license(permit_unlicensed())
                .compile_module_to_jit(&module, &HashMap::new())
                .unwrap();
            let sum: extern "C" fn(i64) -> i64 = unsafe {
                unchecked
                    .buffer
                    .get_fn_bound("sum_below")
                    .expect("published symbol")
                    .into_inner()
            };
            assert_eq!(sum(10), expected(10));
        });
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
