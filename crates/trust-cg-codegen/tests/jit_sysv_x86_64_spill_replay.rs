// x86-64 SysV host-JIT spill/replay coverage.
//
// Part of #L2: focused proof that the existing x86-native spill path executes
// high-pressure GPR and FPR code on SysV hosts without enabling generic
// live-range splitting.

#![cfg(all(target_arch = "x86_64", not(target_os = "windows")))]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::x86_64::{X86OutputFormat, X86Pipeline, X86PipelineConfig};
use trust_cg_lower::function::{BasicBlock, Function as LirFunction, Signature};
use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
use trust_cg_lower::types::Type;
use trust_cg_opt::OptLevel as X86OptLevel;
use trust_ir::Ty;
use trust_ir_build::ModuleBuilder;

const GPR_SPILL_REPLAY_LANES: usize = 32;
const FPR_SPILL_REPLAY_LANES: usize = 32;
const V128_SPILL_REPLAY_LANES: usize = 24;

fn host_jit_o0_compiler() -> Compiler {
    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = OptLevel::O0;
    Compiler::new(config)
}

fn host_jit_o0_x86_pipeline() -> X86Pipeline {
    X86Pipeline::new(X86PipelineConfig {
        opt_level: X86OptLevel::O0,
        output_format: X86OutputFormat::RawBytes,
        emit_frame: true,
        ..X86PipelineConfig::host_jit()
    })
}

fn single_lir_function(module: &trust_ir::Module) -> LirFunction {
    let mut functions =
        trust_cg_lower::translate_module(module).expect("spill replay module should lower to LIR");
    assert_eq!(functions.len(), 1);
    functions.remove(0).0
}

fn build_high_gpr_pressure_spill_replay_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_sysv_gpr_spill_replay");
    let ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
    let mut fb = mb.function("sysv_high_gpr_pressure_reduce", ty);
    let entry = fb.create_block();
    let input = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);

    let mut live_values = Vec::with_capacity(GPR_SPILL_REPLAY_LANES);
    for lane in 0..GPR_SPILL_REPLAY_LANES {
        let index = fb.iconst(Ty::I64, lane as i128);
        let addr = fb.gep(Ty::I64, input, vec![index]);
        let loaded = fb.load(Ty::I64, addr);
        let multiplier = fb.iconst(Ty::I64, ((lane as i64) % 7 + 2) as i128);
        let product = fb.mul(Ty::I64, loaded, multiplier);
        let bias = fb.iconst(Ty::I64, (lane as i64 * 13 - 29) as i128);
        live_values.push(fb.add(Ty::I64, product, bias));
    }

    let mut acc = fb.iconst(Ty::I64, 0);
    for value in live_values {
        acc = fb.add(Ty::I64, acc, value);
    }
    fb.ret(vec![acc]);
    fb.build();
    mb.build()
}

fn reference_high_gpr_pressure(input: &[i64]) -> i64 {
    input
        .iter()
        .take(GPR_SPILL_REPLAY_LANES)
        .enumerate()
        .map(|(lane, value)| value * ((lane as i64) % 7 + 2) + lane as i64 * 13 - 29)
        .sum()
}

fn build_high_fpr_pressure_spill_replay_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_sysv_fpr_spill_replay");
    let ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::F64]);
    let mut fb = mb.function("sysv_high_fpr_pressure_reduce", ty);
    let entry = fb.create_block();
    let input = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);

    let mut live_values = Vec::with_capacity(FPR_SPILL_REPLAY_LANES);
    for lane in 0..FPR_SPILL_REPLAY_LANES {
        let index = fb.iconst(Ty::I64, lane as i128);
        let addr = fb.gep(Ty::F64, input, vec![index]);
        let loaded = fb.load(Ty::F64, addr);
        let scale = fb.fconst(Ty::F64, (lane % 5) as f64 + 1.5);
        let product = fb.fmul(Ty::F64, loaded, scale);
        let bias = fb.fconst(Ty::F64, lane as f64 * 0.25 - 3.0);
        live_values.push(fb.fadd(Ty::F64, product, bias));
    }

    let mut acc = fb.fconst(Ty::F64, 0.0);
    for value in live_values {
        acc = fb.fadd(Ty::F64, acc, value);
    }
    fb.ret(vec![acc]);
    fb.build();
    mb.build()
}

fn reference_high_fpr_pressure(input: &[f64]) -> f64 {
    input
        .iter()
        .take(FPR_SPILL_REPLAY_LANES)
        .enumerate()
        .map(|(lane, value)| {
            let scale = (lane % 5) as f64 + 1.5;
            let bias = lane as f64 * 0.25 - 3.0;
            value * scale + bias
        })
        .sum()
}

fn build_high_v128_pressure_spill_replay_lir() -> LirFunction {
    let mut func = LirFunction::new(
        "sysv_high_v128_pressure_reduce",
        Signature {
            params: std::iter::repeat_n(Type::V128, V128_SPILL_REPLAY_LANES)
                .chain([Type::I64])
                .collect(),
            returns: vec![],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);

    let mut next_value = V128_SPILL_REPLAY_LANES as u32 + 1;
    let mut acc = Value(0);
    let mut instructions = Vec::new();
    for lane in 1..V128_SPILL_REPLAY_LANES {
        let result = Value(next_value);
        next_value += 1;
        instructions.push(Instruction {
            opcode: Opcode::Iadd,
            args: vec![acc, Value(lane as u32)],
            results: vec![result],
        });
        acc = result;
    }
    instructions.push(Instruction {
        opcode: Opcode::Store {
            ty: Type::V128,
            align: None,
        },
        args: vec![acc, Value(V128_SPILL_REPLAY_LANES as u32)],
        results: vec![],
    });
    instructions.push(Instruction {
        opcode: Opcode::Return,
        args: vec![],
        results: vec![],
    });

    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions,
            source_locs: vec![],
        },
    );
    func
}

#[test]
fn x86_64_sysv_jit_high_gpr_pressure_spill_replay_executes() {
    let module = build_high_gpr_pressure_spill_replay_module();
    let result = host_jit_o0_compiler()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("SysV x86-64 JIT should compile high-pressure GPR spill replay");

    let reduce: extern "C" fn(*const i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("sysv_high_gpr_pressure_reduce")
            .expect("sysv_high_gpr_pressure_reduce symbol")
            .into_inner()
    };

    let input: Vec<i64> = (0..GPR_SPILL_REPLAY_LANES)
        .map(|lane| (lane as i64 * 19) - 47)
        .collect();
    assert_eq!(reduce(input.as_ptr()), reference_high_gpr_pressure(&input));
}

#[test]
fn x86_64_sysv_ay_gpr_pressure_evidence_has_spill_canaries() {
    let module = build_high_gpr_pressure_spill_replay_module();
    let lir = single_lir_function(&module);
    let (code, evidence) = host_jit_o0_x86_pipeline()
        .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
        .expect("SysV x86-64 should compile high-pressure GPR evidence fixture");

    eprintln!("x86 ay GPR pressure evidence: {evidence:?}");
    assert!(!code.is_empty());
    assert!(evidence.spilled_vreg_count > 0, "{evidence:?}");
    assert_eq!(
        evidence.spill_stack_slot_count, evidence.spilled_vreg_count,
        "{evidence:?}"
    );
    assert!(evidence.spill_reload_count > 0, "{evidence:?}");
    assert!(evidence.spill_store_count > 0, "{evidence:?}");
    assert!(evidence.two_address_fixup_copy_count > 0, "{evidence:?}");
    assert!(evidence.callee_saved_gpr_save_count > 0, "{evidence:?}");
    assert!(evidence.instruction_count > 0, "{evidence:?}");
    assert!(evidence.code_size_bytes > 0, "{evidence:?}");
}

#[test]
fn x86_64_sysv_jit_high_fpr_pressure_spill_replay_executes() {
    let module = build_high_fpr_pressure_spill_replay_module();
    let result = host_jit_o0_compiler()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("SysV x86-64 JIT should compile high-pressure FPR spill replay");

    let reduce: extern "C" fn(*const f64) -> f64 = unsafe {
        result
            .buffer
            .get_fn_bound("sysv_high_fpr_pressure_reduce")
            .expect("sysv_high_fpr_pressure_reduce symbol")
            .into_inner()
    };

    let input: Vec<f64> = (0..FPR_SPILL_REPLAY_LANES)
        .map(|lane| lane as f64 * 0.5 - 6.25)
        .collect();
    let expected = reference_high_fpr_pressure(&input);
    let observed = reduce(input.as_ptr());
    assert!(
        (observed - expected).abs() <= 1.0e-9,
        "observed {observed}, expected {expected}"
    );
}

#[test]
fn x86_64_sysv_ay_v128_pressure_evidence_has_spill_canaries() {
    let lir = build_high_v128_pressure_spill_replay_lir();
    let (code, evidence) = host_jit_o0_x86_pipeline()
        .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
        .expect("SysV x86-64 should compile high-pressure V128 evidence fixture");

    eprintln!("x86 ay V128 pressure evidence: {evidence:?}");
    assert!(!code.is_empty());
    assert!(evidence.spilled_vreg_count > 0, "{evidence:?}");
    assert_eq!(
        evidence.spill_stack_slot_count, evidence.spilled_vreg_count,
        "{evidence:?}"
    );
    assert!(evidence.spill_reload_count > 0, "{evidence:?}");
    assert!(evidence.spill_store_count > 0, "{evidence:?}");
    assert!(evidence.two_address_fixup_copy_count > 0, "{evidence:?}");
    assert!(evidence.machine_code.paddd_count > 0, "{evidence:?}");
    assert!(evidence.machine_code.movdqu_load_count > 0, "{evidence:?}");
    assert!(evidence.machine_code.movdqu_store_count > 0, "{evidence:?}");
    assert!(evidence.instruction_count > 0, "{evidence:?}");
    assert!(evidence.code_size_bytes > 0, "{evidence:?}");
}
