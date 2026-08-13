#[cfg(target_arch = "x86_64")]
use std::collections::HashMap;

#[cfg(target_arch = "x86_64")]
use trust_cg_codegen::compiler::{CompileError, Compiler, CompilerConfig};
#[cfg(target_arch = "x86_64")]
use trust_cg_codegen::pipeline::OptLevel;
#[cfg(target_arch = "x86_64")]
use trust_cg_codegen::target::Target;
use trust_cg_codegen::x86_64::pipeline::X86RegAllocMode;
use trust_cg_codegen::x86_64::{
    X86OutputFormat, X86Pipeline, X86PipelineConfig, X86PipelineError, X86TargetFeature,
    X86TargetFeatures,
};
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_ir::x86_64_regs::{EAX, RAX, XMM0, XMM1, XMM2};
use trust_cg_lower::function::{BasicBlock, Function as LirFunction, Signature};
use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
use trust_cg_lower::types::Type;
use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst, X86ISelOperand};
use trust_ir::BinOp;
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, FuncTyId,
    Function as TrustIrFunction, ICmpOp, Inst, InstrNode, Module as TrustIrModule, Ty as TrustIrTy,
    ValueId,
};

#[test]
fn public_x86_target_feature_profiles_are_exported() {
    let generic = X86TargetFeatures::generic_x86_64();
    assert!(!generic.contains(X86TargetFeature::Popcnt));
    assert!(!generic.contains(X86TargetFeature::Sse41));
    assert!(!generic.contains(X86TargetFeature::Sse42));
    assert!(!generic.contains(X86TargetFeature::Avx));
    assert!(!generic.contains(X86TargetFeature::Avx2));
    assert_eq!(generic.metadata_feature_list(), "");

    let current = X86TargetFeatures::current();
    assert!(!current.contains(X86TargetFeature::Popcnt));
    assert!(current.contains(X86TargetFeature::Sse41));
    assert!(current.contains(X86TargetFeature::Sse42));
    assert!(!current.contains(X86TargetFeature::Avx));
    assert!(!current.contains(X86TargetFeature::Avx2));
    assert_eq!(current.metadata_feature_list(), "sse4.1,sse4.2");

    assert_eq!(X86PipelineConfig::generic_x86_64().target_features, generic);
    assert_eq!(X86PipelineConfig::current().target_features, current);
}

#[test]
fn public_x86_avx_feature_policy_is_distinct_and_explicit() {
    assert_eq!(X86TargetFeature::Popcnt.name(), "popcnt");
    assert_eq!(X86TargetFeature::Avx.name(), "avx");
    assert_eq!(X86TargetFeature::Avx2.name(), "avx2");

    let generic = X86TargetFeatures::generic_x86_64();
    let avx_only = generic.with_feature(X86TargetFeature::Avx);
    assert!(avx_only.contains(X86TargetFeature::Avx));
    assert!(!avx_only.contains(X86TargetFeature::Avx2));
    assert!(!avx_only.contains(X86TargetFeature::Popcnt));
    assert!(!avx_only.contains(X86TargetFeature::Sse41));
    assert_eq!(avx_only.metadata_feature_list(), "avx");

    let avx2_only = generic.with_feature(X86TargetFeature::Avx2);
    assert!(!avx2_only.contains(X86TargetFeature::Avx));
    assert!(avx2_only.contains(X86TargetFeature::Avx2));
    assert_eq!(avx2_only.metadata_feature_list(), "avx2");

    let mixed = generic
        .with_feature(X86TargetFeature::Popcnt)
        .with_feature(X86TargetFeature::Sse41)
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);
    assert_eq!(
        mixed.enabled_feature_names(),
        ["popcnt", "sse4.1", "avx", "avx2"]
    );
    assert_eq!(
        mixed
            .without_feature(X86TargetFeature::Avx)
            .metadata_feature_list(),
        "popcnt,sse4.1,avx2"
    );
}

#[cfg(target_arch = "x86_64")]
#[test]
fn host_x86_target_features_match_runtime_detection() {
    let host = X86TargetFeatures::host();
    assert_eq!(
        host.contains(X86TargetFeature::Popcnt),
        std::is_x86_feature_detected!("popcnt")
    );
    assert_eq!(
        host.contains(X86TargetFeature::Sse41),
        std::is_x86_feature_detected!("sse4.1")
    );
    assert_eq!(
        host.contains(X86TargetFeature::Sse42),
        std::is_x86_feature_detected!("sse4.2")
    );
    assert_eq!(
        host.contains(X86TargetFeature::Avx),
        std::is_x86_feature_detected!("avx")
    );
    assert_eq!(
        host.contains(X86TargetFeature::Avx2),
        std::is_x86_feature_detected!("avx2")
    );
    assert_eq!(
        host.enabled_feature_names().contains(&"avx"),
        std::is_x86_feature_detected!("avx")
    );
    assert_eq!(
        host.enabled_feature_names().contains(&"avx2"),
        std::is_x86_feature_detected!("avx2")
    );
    assert_eq!(X86PipelineConfig::host_jit().target_features, host);
}

fn generic_raw_pipeline() -> X86Pipeline {
    X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O0,
        output_format: X86OutputFormat::RawBytes,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Simplified,
        ..X86PipelineConfig::generic_x86_64()
    })
}

fn current_raw_pipeline() -> X86Pipeline {
    X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O0,
        output_format: X86OutputFormat::RawBytes,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Simplified,
        ..X86PipelineConfig::current()
    })
}

fn raw_pipeline_with_features(target_features: X86TargetFeatures) -> X86Pipeline {
    X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O0,
        output_format: X86OutputFormat::RawBytes,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Simplified,
        target_features,
        ..X86PipelineConfig::generic_x86_64()
    })
}

fn contains_popcnt_encoding(code: &[u8]) -> bool {
    code.iter().enumerate().any(|(idx, byte)| {
        if *byte != 0xf3 {
            return false;
        }
        let mut next = idx + 1;
        if code
            .get(next)
            .is_some_and(|byte| (0x40..=0x4f).contains(byte))
        {
            next += 1;
        }
        code.get(next) == Some(&0x0f) && code.get(next + 1) == Some(&0xb8)
    })
}

fn pressure_pipeline_with_features(target_features: X86TargetFeatures) -> X86Pipeline {
    X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O0,
        output_format: X86OutputFormat::RawBytes,
        emit_frame: true,
        regalloc_mode: X86RegAllocMode::Full(trust_cg_regalloc::AllocStrategy::Greedy),
        target_features,
        ..X86PipelineConfig::generic_x86_64()
    })
}

fn is_legacy_pmovmskb_modrm_byte(code: &[u8], idx: usize) -> bool {
    if idx < 3 || code.get(idx - 1) != Some(&0xD7) || code.get(idx - 2) != Some(&0x0F) {
        return false;
    }
    code.get(idx - 3) == Some(&0x66)
        || (idx >= 4 && (0x40..=0x4F).contains(&code[idx - 3]) && code.get(idx - 4) == Some(&0x66))
}

fn contains_vex_prefix_byte(code: &[u8]) -> bool {
    code.iter().enumerate().any(|(idx, byte)| match byte {
        0xC4 | 0xC5 if is_legacy_pmovmskb_modrm_byte(code, idx) => false,
        0xC4 => {
            let Some(vex_m) = code.get(idx + 1) else {
                return false;
            };
            matches!(vex_m & 0x1F, 0x01..=0x03) && code.get(idx + 3).is_some()
        }
        0xC5 => code.get(idx + 2).is_some(),
        _ => false,
    })
}

fn contains_sse2_opcode(code: &[u8], opcode: u8) -> bool {
    code.windows(3).any(|w| w == [0x66, 0x0F, opcode])
        || code.windows(4).any(|w| {
            w[0] == 0x66 && (0x40..=0x4F).contains(&w[1]) && w[2] == 0x0F && w[3] == opcode
        })
}

fn contains_imul_rr_opcode(code: &[u8]) -> bool {
    code.windows(2).any(|w| w == [0x0F, 0xAF])
        || code
            .windows(3)
            .any(|w| (0x40..=0x4F).contains(&w[0]) && w[1] == 0x0F && w[2] == 0xAF)
}

fn contains_packed_dword_shift_imm(code: &[u8], subopcode: u8, imm: u8) -> bool {
    code.windows(5).any(|w| {
        w[0] == 0x66
            && w[1] == 0x0F
            && w[2] == 0x72
            && ((w[3] >> 3) & 0x07) == subopcode
            && w[4] == imm
    }) || code.windows(6).any(|w| {
        w[0] == 0x66
            && (0x40..=0x4F).contains(&w[1])
            && w[2] == 0x0F
            && w[3] == 0x72
            && ((w[4] >> 3) & 0x07) == subopcode
            && w[5] == imm
    })
}

fn contains_any_packed_dword_shift_imm(code: &[u8]) -> bool {
    code.windows(4).any(|w| {
        w[0] == 0x66 && w[1] == 0x0F && w[2] == 0x72 && matches!((w[3] >> 3) & 0x07, 2 | 4 | 6)
    }) || code.windows(5).any(|w| {
        w[0] == 0x66
            && (0x40..=0x4F).contains(&w[1])
            && w[2] == 0x0F
            && w[3] == 0x72
            && matches!((w[4] >> 3) & 0x07, 2 | 4 | 6)
    })
}

fn contains_sse41_0f3a_opcode(code: &[u8], opcode: u8) -> bool {
    code.windows(4).any(|w| w == [0x66, 0x0F, 0x3A, opcode])
        || code.windows(5).any(|w| {
            w[0] == 0x66
                && (0x40..=0x4F).contains(&w[1])
                && w[2] == 0x0F
                && w[3] == 0x3A
                && w[4] == opcode
        })
}

fn contains_sse41_0f38_opcode(code: &[u8], opcode: u8) -> bool {
    code.windows(4).any(|w| w == [0x66, 0x0F, 0x38, opcode])
        || code.windows(5).any(|w| {
            w[0] == 0x66
                && (0x40..=0x4F).contains(&w[1])
                && w[2] == 0x0F
                && w[3] == 0x38
                && w[4] == opcode
        })
}

fn contains_pmulld_opcode(code: &[u8]) -> bool {
    contains_sse41_0f38_opcode(code, 0x40)
}

fn assert_no_vex_or_ymm_lowering(code: &[u8], label: &str) {
    assert!(
        !contains_vex_prefix_byte(code),
        "{label} must stay on legacy XMM/SSE encodings without VEX/YMM lowering: {code:02x?}"
    );
}

fn assert_no_scalar_lane_fallback(
    evidence: &trust_cg_codegen::x86_64::X86MachineCodeEvidence,
    label: &str,
) {
    assert_eq!(evidence.pinsrd_count, 0, "{label}: {evidence:?}");
    assert_eq!(evidence.pinsrq_count, 0, "{label}: {evidence:?}");
    assert_eq!(evidence.pextrd_count, 0, "{label}: {evidence:?}");
    assert_eq!(evidence.pextrq_count, 0, "{label}: {evidence:?}");
}

fn minimal_x86_isel_func(
    name: &str,
    opcode: X86Opcode,
    operands: Vec<X86ISelOperand>,
) -> X86ISelFunction {
    let mut func = X86ISelFunction::new(
        name.to_string(),
        Signature {
            params: vec![],
            returns: vec![],
        },
    );
    let entry = Block(0);
    func.ensure_block(entry);
    func.push_inst(entry, X86ISelInst::new(opcode, operands));
    func
}

fn assert_unsupported_feature(err: X86PipelineError, opcode: X86Opcode, feature: X86TargetFeature) {
    let message = err.to_string();
    assert!(
        message.contains(&format!("{opcode:?}")) && message.contains(feature.name()),
        "missing opcode/feature diagnostic for {opcode:?}/{}: {message}",
        feature.name()
    );
    match err {
        X86PipelineError::UnsupportedTargetFeature {
            opcode: actual_opcode,
            feature: actual_feature,
        } => {
            assert_eq!(actual_opcode, opcode);
            assert_eq!(actual_feature, feature);
        }
        other => panic!(
            "expected {opcode:?} to require {}, got {other:?}",
            feature.name()
        ),
    }
}

fn public_sse4_feature_gate_cases() -> Vec<(X86Opcode, Vec<X86ISelOperand>, X86TargetFeature)> {
    vec![
        (
            X86Opcode::Pinsrd,
            vec![
                X86ISelOperand::PReg(XMM0),
                X86ISelOperand::PReg(EAX),
                X86ISelOperand::Imm(0),
            ],
            X86TargetFeature::Sse41,
        ),
        (
            X86Opcode::Pextrd,
            vec![
                X86ISelOperand::PReg(EAX),
                X86ISelOperand::PReg(XMM0),
                X86ISelOperand::Imm(0),
            ],
            X86TargetFeature::Sse41,
        ),
        (
            X86Opcode::Pinsrq,
            vec![
                X86ISelOperand::PReg(XMM0),
                X86ISelOperand::PReg(RAX),
                X86ISelOperand::Imm(1),
            ],
            X86TargetFeature::Sse41,
        ),
        (
            X86Opcode::Pextrq,
            vec![
                X86ISelOperand::PReg(RAX),
                X86ISelOperand::PReg(XMM0),
                X86ISelOperand::Imm(1),
            ],
            X86TargetFeature::Sse41,
        ),
        (
            X86Opcode::Pmulld,
            vec![X86ISelOperand::PReg(XMM0), X86ISelOperand::PReg(XMM1)],
            X86TargetFeature::Sse41,
        ),
        (
            X86Opcode::Pcmpeqq,
            vec![X86ISelOperand::PReg(XMM0), X86ISelOperand::PReg(XMM1)],
            X86TargetFeature::Sse41,
        ),
        (
            X86Opcode::Ptest,
            vec![X86ISelOperand::PReg(XMM0), X86ISelOperand::PReg(XMM1)],
            X86TargetFeature::Sse41,
        ),
        (
            X86Opcode::Pblendvb,
            vec![X86ISelOperand::PReg(XMM1), X86ISelOperand::PReg(XMM2)],
            X86TargetFeature::Sse41,
        ),
        (
            X86Opcode::Pcmpgtq,
            vec![X86ISelOperand::PReg(XMM0), X86ISelOperand::PReg(XMM1)],
            X86TargetFeature::Sse42,
        ),
    ]
}

#[test]
fn generic_x86_64_rejects_all_sse4_opcodes_with_opcode_feature_diagnostics() {
    let pipeline = generic_raw_pipeline();

    for (opcode, operands, feature) in public_sse4_feature_gate_cases() {
        let func = minimal_x86_isel_func(
            &format!("generic_rejects_public_{opcode:?}"),
            opcode,
            operands,
        );
        let err = pipeline.compile_function(&func).unwrap_err();
        assert_unsupported_feature(err, opcode, feature);
    }
}

#[test]
fn generic_x86_64_rejects_sse4_from_public_module_pipeline_entry() {
    let pipeline = generic_raw_pipeline();
    let func = minimal_x86_isel_func(
        "generic_module_rejects_ptest",
        X86Opcode::Ptest,
        vec![X86ISelOperand::PReg(XMM0), X86ISelOperand::PReg(XMM1)],
    );

    let err = pipeline
        .compile_module(&[func])
        .expect_err("generic x86-64 module compilation must reject PTEST");
    assert_unsupported_feature(err, X86Opcode::Ptest, X86TargetFeature::Sse41);
}

#[test]
fn generic_x86_64_rejects_sse4_from_public_jit_fixup_pipeline_entry() {
    let pipeline = generic_raw_pipeline();
    let func = minimal_x86_isel_func(
        "generic_fixup_rejects_pcmpgtq",
        X86Opcode::Pcmpgtq,
        vec![X86ISelOperand::PReg(XMM0), X86ISelOperand::PReg(XMM1)],
    );

    let err = pipeline
        .compile_function_with_fixups(&func)
        .expect_err("generic x86-64 fixup compilation must reject PCMPGTQ");
    assert_unsupported_feature(err, X86Opcode::Pcmpgtq, X86TargetFeature::Sse42);
}

#[test]
fn generic_x86_64_rejects_pblendvb_from_public_function_pipeline_entry() {
    let pipeline = generic_raw_pipeline();
    let func = minimal_x86_isel_func(
        "generic_function_rejects_pblendvb",
        X86Opcode::Pblendvb,
        vec![X86ISelOperand::PReg(XMM1), X86ISelOperand::PReg(XMM2)],
    );

    let err = pipeline
        .compile_function(&func)
        .expect_err("generic x86-64 function compilation must reject PBLENDVB");
    assert_unsupported_feature(err, X86Opcode::Pblendvb, X86TargetFeature::Sse41);
}

#[test]
fn generic_x86_64_admits_v4i32_imul_without_sse4_pmulld() {
    let func = build_v128_i32_mul_store_lir("generic_v4i32_imul_sse2");
    let code = generic_raw_pipeline()
        .compile_trust_ir_function(&func)
        .expect("generic x86-64 LIR pipeline should scalarize v4i32 IMUL through SSE2");

    assert!(!code.is_empty());
    assert!(
        contains_sse2_opcode(&code, 0xF4),
        "generic v4i32 IMUL should use SSE2 PMULUDQ: {code:02x?}"
    );
    assert!(
        !contains_pmulld_opcode(&code),
        "generic v4i32 IMUL must not encode SSE4.1 PMULLD: {code:02x?}"
    );
    assert!(
        !code.windows(2).any(|bytes| bytes == [0x0F, 0xAF]),
        "generic v4i32 IMUL should not cross lanes through scalar GPR IMUL: {code:02x?}"
    );
}

#[test]
fn generic_x86_64_rejects_explicit_pmulld_from_public_function_pipeline_entry() {
    let pipeline = generic_raw_pipeline();
    let func = minimal_x86_isel_func(
        "generic_function_rejects_pmulld",
        X86Opcode::Pmulld,
        vec![X86ISelOperand::PReg(XMM0), X86ISelOperand::PReg(XMM1)],
    );

    let err = pipeline
        .compile_function(&func)
        .expect_err("generic x86-64 function compilation must reject explicit PMULLD");
    assert_unsupported_feature(err, X86Opcode::Pmulld, X86TargetFeature::Sse41);
}

#[test]
fn avx_feature_bits_are_inert_until_vex_lowering_exists() {
    let func = build_v128_i32_mul_store_lir("avx_inert_v4i32_mul");

    let generic = X86TargetFeatures::generic_x86_64();
    let generic_avx = generic
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);
    let generic_code = raw_pipeline_with_features(generic)
        .compile_trust_ir_function(&func)
        .expect("generic x86-64 vector lowering should compile");
    let generic_avx_code = raw_pipeline_with_features(generic_avx)
        .compile_trust_ir_function(&func)
        .expect("AVX policy bits must not enable a new generic lowering path");
    assert_eq!(
        generic_avx_code, generic_code,
        "AVX/AVX2 feature bits must be inert until VEX lowering exists"
    );
    assert!(
        !contains_vex_prefix_byte(&generic_avx_code),
        "generic AVX policy scaffolding must not emit VEX bytes: {generic_avx_code:02x?}"
    );

    let current = X86TargetFeatures::current();
    let current_avx = current
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);
    let current_code = raw_pipeline_with_features(current)
        .compile_trust_ir_function(&func)
        .expect("current x86-64 vector lowering should compile");
    let current_avx_code = raw_pipeline_with_features(current_avx)
        .compile_trust_ir_function(&func)
        .expect("AVX policy bits must not enable a new current lowering path");
    assert_eq!(
        current_avx_code, current_code,
        "AVX/AVX2 feature bits must not change current codegen before VEX lowering lands"
    );
    assert!(
        !contains_vex_prefix_byte(&current_avx_code),
        "current AVX policy scaffolding must not emit VEX bytes: {current_avx_code:02x?}"
    );
}

#[test]
fn generic_x86_64_ctpop_uses_baseline_fallback_and_popcnt_feature_uses_native_opcode() {
    let ctpop = build_ctpop_lir("ctpop_i64_feature_parity", Type::I64);
    let generic = X86TargetFeatures::generic_x86_64();
    let popcnt = generic.with_feature(X86TargetFeature::Popcnt);

    let (generic_code, generic_evidence) = raw_pipeline_with_features(generic)
        .compile_trust_ir_function_with_regalloc_pressure_evidence(&ctpop)
        .expect("generic x86-64 CtPop must compile via baseline fallback");
    assert_eq!(generic_evidence.machine_code.target_features, generic);
    assert_eq!(generic_evidence.machine_code.popcnt_count, 0);
    assert!(
        !contains_popcnt_encoding(&generic_code),
        "generic x86-64 CtPop must not encode POPCNT bytes: {generic_code:02x?}"
    );

    let (popcnt_code, popcnt_evidence) = raw_pipeline_with_features(popcnt)
        .compile_trust_ir_function_with_regalloc_pressure_evidence(&ctpop)
        .expect("popcnt-enabled x86-64 CtPop must compile");
    assert_eq!(popcnt_evidence.machine_code.target_features, popcnt);
    assert_eq!(popcnt_evidence.machine_code.popcnt_count, 1);
    assert!(
        contains_popcnt_encoding(&popcnt_code),
        "popcnt-enabled x86-64 CtPop should encode native POPCNT: {popcnt_code:02x?}"
    );
}

#[cfg(target_arch = "x86_64")]
#[test]
fn host_avx_feature_bits_are_runtime_detected_but_codegen_inert() {
    let func = build_v128_i32_mul_store_lir("host_avx_inert_v4i32_mul");
    let host = X86TargetFeatures::host();
    let host_without_avx = host
        .without_feature(X86TargetFeature::Avx)
        .without_feature(X86TargetFeature::Avx2);

    let host_code = raw_pipeline_with_features(host)
        .compile_trust_ir_function(&func)
        .expect("host x86-64 vector lowering should compile");
    let host_without_avx_code = raw_pipeline_with_features(host_without_avx)
        .compile_trust_ir_function(&func)
        .expect("host x86-64 vector lowering without AVX policy bits should compile");

    assert_eq!(
        host_code, host_without_avx_code,
        "runtime-detected AVX/AVX2 must not change codegen until VEX lowering lands"
    );
    assert!(
        !contains_vex_prefix_byte(&host_code),
        "host AVX policy scaffolding must not emit VEX bytes: {host_code:02x?}"
    );
}

#[test]
fn x86_v128_profile_evidence_matrix_distinguishes_sse2_sse4_and_inert_avx() {
    let generic = X86TargetFeatures::generic_x86_64();
    let current = X86TargetFeatures::current();
    let current_avx = current
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);

    let arith = build_v128_i32_mul_store_lir("profile_matrix_v4i32_mul");
    let (generic_arith_code, generic_arith) = raw_pipeline_with_features(generic)
        .compile_trust_ir_function_with_regalloc_pressure_evidence(&arith)
        .expect("generic x86_64 should scalarize v4i32 multiply through SSE2");
    let (current_arith_code, current_arith) = raw_pipeline_with_features(current)
        .compile_trust_ir_function_with_regalloc_pressure_evidence(&arith)
        .expect("current x86_64 should use SSE4.1 PMULLD for v4i32 multiply");
    let (current_avx_arith_code, current_avx_arith) = raw_pipeline_with_features(current_avx)
        .compile_trust_ir_function_with_regalloc_pressure_evidence(&arith)
        .expect("current+AVX policy bits must keep the legacy SSE lowering path");

    eprintln!(
        "x86 V128 profile arithmetic canary: generic={:?}, current={:?}, current_avx={:?}",
        generic_arith.machine_code, current_arith.machine_code, current_avx_arith.machine_code
    );
    assert_eq!(generic_arith.machine_code.target_features, generic);
    assert_eq!(current_arith.machine_code.target_features, current);
    assert_eq!(current_avx_arith.machine_code.target_features, current_avx);
    assert!(generic_arith.machine_code.pmuludq_count > 0);
    assert_eq!(generic_arith.machine_code.pmulld_count, 0);
    assert_eq!(current_arith.machine_code.pmulld_count, 1);
    assert_eq!(current_avx_arith.machine_code.pmulld_count, 1);
    assert_eq!(current_avx_arith_code, current_arith_code);
    assert_no_vex_or_ymm_lowering(&generic_arith_code, "generic v4i32 multiply");
    assert_no_vex_or_ymm_lowering(&current_avx_arith_code, "current+AVX v4i32 multiply");

    let generic_mask = build_v4i32_ne_mask_extract_lir("profile_matrix_v4i32_ne_mask");
    let (generic_mask_code, generic_mask_evidence) = raw_pipeline_with_features(generic)
        .compile_trust_ir_function_with_regalloc_pressure_evidence(&generic_mask)
        .expect("generic x86_64 should use SSE2 compare/mask extraction");
    eprintln!(
        "x86 V128 profile compare/mask generic canary: {:?}",
        generic_mask_evidence.machine_code
    );
    assert_eq!(generic_mask_evidence.machine_code.target_features, generic);
    assert!(generic_mask_evidence.machine_code.pcmpeqd_count >= 1);
    assert_eq!(generic_mask_evidence.machine_code.pmovmskb_count, 1);
    assert_eq!(generic_mask_evidence.machine_code.pcmpeqq_count, 0);
    assert_eq!(generic_mask_evidence.machine_code.pcmpgtq_count, 0);
    assert!(!generic_mask_code.is_empty());

    let current_mask =
        build_v2i64_bool_mask_extract_lir("profile_matrix_v2i64_slt_bool_extract", ICmpOp::Slt);
    let (current_mask_code, current_mask_evidence) = raw_pipeline_with_features(current)
        .compile_trust_ir_function_with_regalloc_pressure_evidence(&current_mask)
        .expect("current x86_64 should admit SSE4.2 v2i64 signed compare");
    let (current_avx_mask_code, current_avx_mask_evidence) =
        raw_pipeline_with_features(current_avx)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&current_mask)
            .expect("current+AVX policy bits must keep the legacy SSE4 compare path");
    eprintln!(
        "x86 V128 profile compare/mask current canary: current={:?}, current_avx={:?}",
        current_mask_evidence.machine_code, current_avx_mask_evidence.machine_code
    );
    assert_eq!(current_mask_evidence.machine_code.target_features, current);
    assert_eq!(
        current_avx_mask_evidence.machine_code.target_features,
        current_avx
    );
    assert_eq!(current_mask_evidence.machine_code.pcmpgtq_count, 1);
    assert_eq!(current_avx_mask_evidence.machine_code.pcmpgtq_count, 1);
    assert_eq!(current_avx_mask_code, current_mask_code);
    assert_no_vex_or_ymm_lowering(&current_avx_mask_code, "current+AVX v2i64 compare/mask");

    let branch = build_v4i32_mask_branch_lir("profile_matrix_v4i32_mask_branch");
    let (generic_branch_code, generic_branch_evidence) = raw_pipeline_with_features(generic)
        .compile_trust_ir_function_with_regalloc_pressure_evidence(&branch)
        .expect("generic x86_64 should expand V128 mask branches without PTEST");
    let (current_branch_code, current_branch_evidence) = raw_pipeline_with_features(current)
        .compile_trust_ir_function_with_regalloc_pressure_evidence(&branch)
        .expect("current x86_64 should use SSE4.1 PTEST for V128 mask branches");
    eprintln!(
        "x86 V128 profile select/branch canary: generic={:?}, current={:?}",
        generic_branch_evidence.machine_code, current_branch_evidence.machine_code
    );
    assert_eq!(
        generic_branch_evidence.machine_code.target_features,
        generic
    );
    assert_eq!(
        current_branch_evidence.machine_code.target_features,
        current
    );
    assert_eq!(generic_branch_evidence.machine_code.ptest_count, 0);
    assert!(generic_branch_evidence.machine_code.pmovmskb_count > 0);
    assert!(current_branch_evidence.machine_code.ptest_count > 0);
    assert_no_vex_or_ymm_lowering(&generic_branch_code, "generic v4i32 mask branch");
    assert_no_vex_or_ymm_lowering(&current_branch_code, "current v4i32 mask branch");
}

#[test]
fn x86_v128_memory_spill_profile_evidence_records_features_and_stays_legacy_sse() {
    let generic = X86TargetFeatures::generic_x86_64();
    let current_avx = X86TargetFeatures::current()
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);
    let spill = build_v128_profile_spill_lir("profile_matrix_v128_spill");

    for (label, features) in [("generic", generic), ("current_avx", current_avx)] {
        let (_code, evidence) = pressure_pipeline_with_features(features)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&spill)
            .unwrap_or_else(|err| panic!("{label} V128 spill canary should compile: {err}"));
        eprintln!("x86 V128 profile memory/spill canary {label}: {evidence:?}");
        assert_eq!(evidence.machine_code.target_features, features);
        assert!(evidence.spilled_vreg_count > 0, "{label}: {evidence:?}");
        assert!(evidence.spill_reload_count > 0, "{label}: {evidence:?}");
        assert!(evidence.spill_store_count > 0, "{label}: {evidence:?}");
        assert!(
            evidence.machine_code.movdqu_load_count > 0,
            "{label}: {evidence:?}"
        );
        assert!(
            evidence.machine_code.movdqu_store_count > 0,
            "{label}: {evidence:?}"
        );
        assert!(
            evidence.machine_code.paddd_count > 0,
            "{label}: {evidence:?}"
        );
        assert_eq!(
            evidence.machine_code.pmulld_count, 0,
            "{label}: {evidence:?}"
        );
        assert_eq!(
            evidence.machine_code.pblendvb_count, 0,
            "{label}: {evidence:?}"
        );
    }
}

#[test]
#[allow(clippy::type_complexity)] // Table rows bind opcode, encoding, and evidence counter.
fn x86_narrow_packed_spill_fold_pressure_evidence_uses_legacy_memory_rhs() {
    let cases: [(
        &str,
        Opcode,
        u8,
        fn(&trust_cg_codegen::x86_64::X86MachineCodeEvidence) -> usize,
    ); 4] = [
        (
            "profile_matrix_v16i8_paddb_spill_fold",
            Opcode::V16I8Add,
            0xFC,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.paddb_count,
        ),
        (
            "profile_matrix_v8i16_paddw_spill_fold",
            Opcode::V8I16Add,
            0xFD,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.paddw_count,
        ),
        (
            "profile_matrix_v16i8_psubb_spill_fold",
            Opcode::V16I8Sub,
            0xF8,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.psubb_count,
        ),
        (
            "profile_matrix_v8i16_psubw_spill_fold",
            Opcode::V8I16Sub,
            0xF9,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.psubw_count,
        ),
    ];
    for (name, opcode, sse2_opcode, count) in cases {
        let lir = build_v128_profile_spill_lir_with_opcode(name, opcode);
        let (code, evidence) = pressure_pipeline_with_features(X86TargetFeatures::generic_x86_64())
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} narrow packed pressure canary: {err}"));

        eprintln!("x86 narrow packed spill-fold pressure evidence {name}: {evidence:?}");
        assert!(
            contains_sse2_opcode(&code, sse2_opcode),
            "{name}: {code:02X?}"
        );
        assert_eq!(
            evidence.machine_code.target_features,
            X86TargetFeatures::generic_x86_64()
        );
        assert!(evidence.spilled_vreg_count > 0, "{name}: {evidence:?}");
        assert!(evidence.spill_reload_count > 0, "{name}: {evidence:?}");
        assert!(evidence.spill_store_count > 0, "{name}: {evidence:?}");
        assert_eq!(count(&evidence.machine_code), PROFILE_V128_SPILL_LANES - 1);
        assert!(
            evidence.machine_code.movdqu_load_count > 0,
            "{name}: {evidence:?}"
        );
        assert!(
            evidence.machine_code.movdqu_store_count > 0,
            "{name}: {evidence:?}"
        );
    }
}

#[test]
fn x86_narrow_bitwise_profile_canaries_stay_legacy_sse2_with_inert_avx() {
    let generic = X86TargetFeatures::generic_x86_64();
    let generic_avx = generic
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);
    let cases = [
        (
            "profile_matrix_v16i8_and_pand",
            v16i8_ty(),
            BinOp::And,
            0xDB,
        ),
        ("profile_matrix_v16i8_or_por", v16i8_ty(), BinOp::Or, 0xEB),
        (
            "profile_matrix_v16i8_xor_pxor",
            v16i8_ty(),
            BinOp::Xor,
            0xEF,
        ),
        (
            "profile_matrix_v8i16_and_pand",
            v8i16_ty(),
            BinOp::And,
            0xDB,
        ),
        ("profile_matrix_v8i16_or_por", v8i16_ty(), BinOp::Or, 0xEB),
        (
            "profile_matrix_v8i16_xor_pxor",
            v8i16_ty(),
            BinOp::Xor,
            0xEF,
        ),
    ];

    for (name, vector_ty, op, sse2_opcode) in cases {
        let lir = build_narrow_vector_bitwise_store_lir(name, vector_ty, op);
        let (generic_code, generic_evidence) = raw_pipeline_with_features(generic)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} generic narrow bitwise canary: {err}"));
        let (generic_avx_code, generic_avx_evidence) = raw_pipeline_with_features(generic_avx)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} generic+AVX narrow bitwise canary: {err}"));

        eprintln!(
            "x86 narrow bitwise profile canary {name}: generic={:?}, generic_avx={:?}",
            generic_evidence.machine_code, generic_avx_evidence.machine_code
        );
        assert_eq!(generic_evidence.machine_code.target_features, generic);
        assert_eq!(
            generic_avx_evidence.machine_code.target_features,
            generic_avx
        );
        assert_eq!(
            generic_avx_code, generic_code,
            "{name}: AVX/AVX2 feature bits must not change narrow bitwise codegen"
        );
        assert!(
            contains_sse2_opcode(&generic_code, sse2_opcode),
            "{name}: expected legacy SSE2 PAND/POR/PXOR opcode {sse2_opcode:#04x}: {generic_code:02x?}"
        );

        for (profile, evidence) in [
            ("generic", &generic_evidence),
            ("generic+avx", &generic_avx_evidence),
        ] {
            assert_eq!(
                evidence.machine_code.pand_count,
                usize::from(op == BinOp::And),
                "{name} {profile}: {:?}",
                evidence.machine_code
            );
            assert_eq!(
                evidence.machine_code.por_count,
                usize::from(op == BinOp::Or),
                "{name} {profile}: {:?}",
                evidence.machine_code
            );
            assert_eq!(
                evidence.machine_code.pxor_count,
                usize::from(op == BinOp::Xor),
                "{name} {profile}: {:?}",
                evidence.machine_code
            );
            assert_eq!(evidence.machine_code.pandn_count, 0, "{name} {profile}");
            assert_eq!(evidence.machine_code.pmovmskb_count, 0, "{name} {profile}");
            assert_eq!(evidence.machine_code.ptest_count, 0, "{name} {profile}");
            assert_eq!(evidence.machine_code.pblendvb_count, 0, "{name} {profile}");
            assert_eq!(
                evidence.machine_code.movd_to_xmm_count, 0,
                "{name} {profile}"
            );
            assert_eq!(
                evidence.machine_code.movq_to_xmm_count, 0,
                "{name} {profile}"
            );
            assert_no_scalar_lane_fallback(&evidence.machine_code, name);
        }

        for (profile, code) in [
            ("generic", &generic_code),
            ("generic+avx", &generic_avx_code),
        ] {
            assert_no_vex_or_ymm_lowering(code, &format!("{name} {profile}"));
            assert!(
                !contains_sse41_0f3a_opcode(code, 0x20)
                    && !contains_sse41_0f3a_opcode(code, 0x22)
                    && !contains_sse41_0f3a_opcode(code, 0x14)
                    && !contains_sse41_0f3a_opcode(code, 0x16)
                    && !contains_sse2_opcode(code, 0xC4)
                    && !contains_sse2_opcode(code, 0xC5),
                "{name} {profile}: must not use PINS*/PEXTR* scalar lane fallback: {code:02x?}"
            );
        }
    }
}

#[test]
#[allow(clippy::type_complexity)] // Table rows bind type, predicate, encoding, and evidence.
fn x86_narrow_compare_profile_canaries_stay_legacy_sse2_with_inert_avx() {
    let generic = X86TargetFeatures::generic_x86_64();
    let generic_avx = generic
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);
    let cases: [(
        &str,
        TrustIrTy,
        ICmpOp,
        u8,
        fn(&trust_cg_codegen::x86_64::X86MachineCodeEvidence) -> usize,
    ); 4] = [
        (
            "profile_matrix_v16i8_eq_pcmpeqb",
            v16i8_ty(),
            ICmpOp::Eq,
            0x74,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqb_count,
        ),
        (
            "profile_matrix_v16i8_ne_pcmpeqb",
            v16i8_ty(),
            ICmpOp::Ne,
            0x74,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqb_count,
        ),
        (
            "profile_matrix_v8i16_eq_pcmpeqw",
            v8i16_ty(),
            ICmpOp::Eq,
            0x75,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqw_count,
        ),
        (
            "profile_matrix_v8i16_ne_pcmpeqw",
            v8i16_ty(),
            ICmpOp::Ne,
            0x75,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqw_count,
        ),
    ];

    for (name, vector_ty, op, sse2_opcode, count) in cases {
        let lir = build_narrow_vector_icmp_store_lir(name, vector_ty, op);
        let (generic_code, generic_evidence) = raw_pipeline_with_features(generic)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} generic narrow compare canary: {err}"));
        let (generic_avx_code, generic_avx_evidence) = raw_pipeline_with_features(generic_avx)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} generic+AVX narrow compare canary: {err}"));

        eprintln!(
            "x86 narrow compare profile canary {name}: generic={:?}, generic_avx={:?}",
            generic_evidence.machine_code, generic_avx_evidence.machine_code
        );
        assert_eq!(generic_evidence.machine_code.target_features, generic);
        assert_eq!(
            generic_avx_evidence.machine_code.target_features,
            generic_avx
        );
        assert_eq!(
            generic_avx_code, generic_code,
            "{name}: AVX/AVX2 feature bits must not change codegen before VEX lowering lands"
        );
        assert!(
            contains_sse2_opcode(&generic_code, sse2_opcode),
            "{name}: expected legacy SSE2 PCMPEQB/PCMPEQW opcode {sse2_opcode:#04x}: {generic_code:02x?}"
        );
        assert_eq!(count(&generic_evidence.machine_code), 1, "{name}");
        assert_eq!(count(&generic_avx_evidence.machine_code), 1, "{name}");
        assert_eq!(generic_evidence.machine_code.pmovmskb_count, 0, "{name}");
        assert_eq!(generic_evidence.machine_code.ptest_count, 0, "{name}");
        assert_eq!(generic_evidence.machine_code.pcmpeqq_count, 0, "{name}");
        assert_eq!(generic_evidence.machine_code.pcmpgtq_count, 0, "{name}");
        if op == ICmpOp::Ne {
            assert_eq!(generic_evidence.machine_code.pcmpeqd_count, 1, "{name}");
            assert_eq!(generic_evidence.machine_code.pxor_count, 1, "{name}");
            assert!(
                contains_sse2_opcode(&generic_code, 0xEF),
                "{name}: expected legacy SSE2 PXOR for canonical Ne inversion: {generic_code:02x?}"
            );
        } else {
            assert_eq!(generic_evidence.machine_code.pcmpeqd_count, 0, "{name}");
            assert_eq!(generic_evidence.machine_code.pxor_count, 0, "{name}");
        }
        assert!(
            !generic_code.is_empty(),
            "{name}: legacy SSE2 mask_to_bits code should be nonempty"
        );
        assert!(
            !generic_avx_code.is_empty(),
            "{name}: generic+AVX mask_to_bits code should be nonempty"
        );
        assert_no_vex_or_ymm_lowering(&generic_code, name);
        assert_no_vex_or_ymm_lowering(&generic_avx_code, name);
    }
}

#[test]
#[allow(clippy::type_complexity)] // Table rows bind input/mask types and machine evidence.
fn x86_narrow_compare_mask_to_bits_canaries_use_pmovmskb_with_inert_avx() {
    let generic = X86TargetFeatures::generic_x86_64();
    let generic_avx = generic
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);
    let cases: [(
        &str,
        TrustIrTy,
        TrustIrTy,
        ICmpOp,
        u8,
        fn(&trust_cg_codegen::x86_64::X86MachineCodeEvidence) -> usize,
    ); 4] = [
        (
            "profile_matrix_v16i8_eq_mask_to_bits",
            v16i8_ty(),
            v16_bool_ty(),
            ICmpOp::Eq,
            0x74,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqb_count,
        ),
        (
            "profile_matrix_v16i8_ne_mask_to_bits",
            v16i8_ty(),
            v16_bool_ty(),
            ICmpOp::Ne,
            0x74,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqb_count,
        ),
        (
            "profile_matrix_v8i16_eq_mask_to_bits",
            v8i16_ty(),
            v8_bool_ty(),
            ICmpOp::Eq,
            0x75,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqw_count,
        ),
        (
            "profile_matrix_v8i16_ne_mask_to_bits",
            v8i16_ty(),
            v8_bool_ty(),
            ICmpOp::Ne,
            0x75,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqw_count,
        ),
    ];

    for (name, vector_ty, mask_ty, op, pcmpeq_opcode, count) in cases {
        let lir = build_narrow_vector_cmp_mask_to_bits_lir(name, vector_ty, mask_ty, op);
        let (generic_code, generic_evidence) = raw_pipeline_with_features(generic)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} generic mask_to_bits canary: {err}"));
        let (generic_avx_code, generic_avx_evidence) = raw_pipeline_with_features(generic_avx)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} generic+AVX mask_to_bits canary: {err}"));

        eprintln!(
            "x86 narrow compare mask_to_bits canary {name}: generic={:?}, generic_avx={:?}",
            generic_evidence.machine_code, generic_avx_evidence.machine_code
        );
        assert_eq!(generic_evidence.machine_code.target_features, generic);
        assert_eq!(
            generic_avx_evidence.machine_code.target_features,
            generic_avx
        );
        assert_eq!(
            generic_avx_code, generic_code,
            "{name}: AVX/AVX2 feature bits must not change narrow mask_to_bits codegen"
        );
        assert!(
            contains_sse2_opcode(&generic_code, pcmpeq_opcode),
            "{name}: expected legacy PCMPEQB/PCMPEQW opcode {pcmpeq_opcode:#04x}: {generic_code:02x?}"
        );
        assert!(
            contains_sse2_opcode(&generic_code, 0xD7),
            "{name}: expected legacy PMOVMSKB mask extraction: {generic_code:02x?}"
        );
        assert_eq!(count(&generic_evidence.machine_code), 1, "{name}");
        assert_eq!(count(&generic_avx_evidence.machine_code), 1, "{name}");
        assert_eq!(generic_evidence.machine_code.pmovmskb_count, 1, "{name}");
        assert_eq!(
            generic_avx_evidence.machine_code.pmovmskb_count, 1,
            "{name}"
        );
        assert_eq!(generic_evidence.machine_code.ptest_count, 0, "{name}");
        assert_eq!(generic_evidence.machine_code.pinsrd_count, 0, "{name}");
        assert_eq!(generic_evidence.machine_code.pinsrq_count, 0, "{name}");
        assert_eq!(generic_evidence.machine_code.pextrd_count, 0, "{name}");
        assert_eq!(generic_evidence.machine_code.pextrq_count, 0, "{name}");
        assert_eq!(generic_evidence.machine_code.pcmpeqq_count, 0, "{name}");
        assert_eq!(generic_evidence.machine_code.pcmpgtq_count, 0, "{name}");
        if op == ICmpOp::Ne {
            assert_eq!(generic_evidence.machine_code.pxor_count, 1, "{name}");
            assert!(
                generic_evidence.machine_code.pcmpeqd_count >= 1,
                "{name}: NotEqual should build an all-ones inverter with PCMPEQD"
            );
        } else {
            assert_eq!(generic_evidence.machine_code.pxor_count, 0, "{name}");
        }
        assert!(!generic_code.is_empty(), "{name}");
        assert!(!generic_avx_code.is_empty(), "{name}");
        assert_no_vex_or_ymm_lowering(&generic_code, name);
        assert_no_vex_or_ymm_lowering(&generic_avx_code, name);
    }
}

#[test]
fn x86_v4_v2_canonical_bool_constant_mask_to_bits_canaries_use_pmovmskb_with_inert_avx() {
    let generic = X86TargetFeatures::generic_x86_64();
    let generic_avx = generic
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);

    for (name, mask_ty, lanes, true_bits) in [
        (
            "profile_matrix_v4_bool_canonical_constant_mask_to_bits",
            v4_bool_ty(),
            4,
            0b1010,
        ),
        (
            "profile_matrix_v2_bool_canonical_constant_mask_to_bits",
            v2_bool_ty(),
            2,
            0b10,
        ),
    ] {
        let lir = build_bool_const_mask_to_bits_lir(name, mask_ty, lanes, true_bits);
        let (generic_code, generic_evidence) = raw_pipeline_with_features(generic)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| {
                panic!("{name} generic canonical bool mask_to_bits canary: {err}")
            });
        let (generic_avx_code, generic_avx_evidence) = raw_pipeline_with_features(generic_avx)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| {
                panic!("{name} generic+AVX canonical bool mask_to_bits canary: {err}")
            });

        eprintln!(
            "x86 V4/V2 canonical bool-constant mask_to_bits canary {name}: generic={:?}, generic_avx={:?}",
            generic_evidence.machine_code, generic_avx_evidence.machine_code
        );
        assert_eq!(generic_evidence.machine_code.target_features, generic);
        assert_eq!(
            generic_avx_evidence.machine_code.target_features,
            generic_avx
        );
        assert_eq!(
            generic_avx_code, generic_code,
            "{name}: AVX/AVX2 feature bits must not change V4/V2 bool mask_to_bits codegen"
        );
        assert_eq!(
            generic_evidence.machine_code.pmovmskb_count, 1,
            "{name}: canonical bool constants should compact through one PMOVMSKB"
        );
        assert_eq!(
            generic_avx_evidence.machine_code.pmovmskb_count, 1,
            "{name}: canonical bool constants should compact through one PMOVMSKB under AVX policy bits"
        );
        assert_eq!(generic_evidence.machine_code.ptest_count, 0, "{name}");
        assert_eq!(generic_evidence.machine_code.pblendvb_count, 0, "{name}");
        assert_no_scalar_lane_fallback(&generic_evidence.machine_code, name);
        assert_no_scalar_lane_fallback(&generic_avx_evidence.machine_code, name);
        assert!(
            contains_sse2_opcode(&generic_code, 0xD7),
            "{name}: expected legacy PMOVMSKB mask extraction: {generic_code:02x?}"
        );
        assert_no_vex_or_ymm_lowering(&generic_code, name);
        assert_no_vex_or_ymm_lowering(&generic_avx_code, name);
    }
}

#[test]
#[allow(clippy::type_complexity)] // Table rows bind predicate and paired evidence counters.
fn x86_narrow_signed_compare_profile_canaries_use_sse2_pcmpgt_with_inert_avx() {
    let generic = X86TargetFeatures::generic_x86_64();
    let generic_avx = generic
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);
    let cases: [(
        &str,
        TrustIrTy,
        ICmpOp,
        u8,
        fn(&trust_cg_codegen::x86_64::X86MachineCodeEvidence) -> usize,
        fn(&trust_cg_codegen::x86_64::X86MachineCodeEvidence) -> usize,
    ); 8] = [
        (
            "profile_matrix_v16i8_slt_pcmpgtb",
            v16i8_ty(),
            ICmpOp::Slt,
            0x64,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpgtb_count,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqb_count,
        ),
        (
            "profile_matrix_v16i8_sgt_pcmpgtb",
            v16i8_ty(),
            ICmpOp::Sgt,
            0x64,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpgtb_count,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqb_count,
        ),
        (
            "profile_matrix_v16i8_sle_pcmpgtb_pcmpeqb_por",
            v16i8_ty(),
            ICmpOp::Sle,
            0x64,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpgtb_count,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqb_count,
        ),
        (
            "profile_matrix_v16i8_sge_pcmpgtb_pcmpeqb_por",
            v16i8_ty(),
            ICmpOp::Sge,
            0x64,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpgtb_count,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqb_count,
        ),
        (
            "profile_matrix_v8i16_slt_pcmpgtw",
            v8i16_ty(),
            ICmpOp::Slt,
            0x65,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpgtw_count,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqw_count,
        ),
        (
            "profile_matrix_v8i16_sgt_pcmpgtw",
            v8i16_ty(),
            ICmpOp::Sgt,
            0x65,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpgtw_count,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqw_count,
        ),
        (
            "profile_matrix_v8i16_sle_pcmpgtw_pcmpeqw_por",
            v8i16_ty(),
            ICmpOp::Sle,
            0x65,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpgtw_count,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqw_count,
        ),
        (
            "profile_matrix_v8i16_sge_pcmpgtw_pcmpeqw_por",
            v8i16_ty(),
            ICmpOp::Sge,
            0x65,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpgtw_count,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqw_count,
        ),
    ];

    for (name, vector_ty, op, pcmpgt_opcode, pcmpgt_count, pcmpeq_count) in cases {
        let lir = build_narrow_vector_icmp_store_lir(name, vector_ty, op);
        let (generic_code, generic_evidence) = raw_pipeline_with_features(generic)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} generic narrow signed compare canary: {err}"));
        let (generic_avx_code, generic_avx_evidence) = raw_pipeline_with_features(generic_avx)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} generic+AVX narrow signed compare canary: {err}"));

        eprintln!(
            "x86 narrow signed compare profile canary {name}: generic={:?}, generic_avx={:?}",
            generic_evidence.machine_code, generic_avx_evidence.machine_code
        );
        assert_eq!(generic_evidence.machine_code.target_features, generic);
        assert_eq!(
            generic_avx_evidence.machine_code.target_features,
            generic_avx
        );
        assert_eq!(
            generic_avx_code, generic_code,
            "{name}: AVX/AVX2 feature bits must remain inert for legacy SSE2 narrow compares"
        );
        assert!(
            contains_sse2_opcode(&generic_code, pcmpgt_opcode),
            "{name}: expected legacy SSE2 PCMPGTB/PCMPGTW opcode {pcmpgt_opcode:#04x}: {generic_code:02x?}"
        );
        assert_eq!(pcmpgt_count(&generic_evidence.machine_code), 1, "{name}");
        assert_eq!(
            pcmpgt_count(&generic_avx_evidence.machine_code),
            1,
            "{name}"
        );
        assert_eq!(generic_evidence.machine_code.pmovmskb_count, 0, "{name}");
        assert_eq!(generic_evidence.machine_code.ptest_count, 0, "{name}");
        assert_eq!(generic_evidence.machine_code.pcmpeqq_count, 0, "{name}");
        assert_eq!(generic_evidence.machine_code.pcmpgtq_count, 0, "{name}");
        if matches!(op, ICmpOp::Sle | ICmpOp::Sge) {
            assert_eq!(pcmpeq_count(&generic_evidence.machine_code), 1, "{name}");
            assert_eq!(generic_evidence.machine_code.por_count, 1, "{name}");
            assert!(
                contains_sse2_opcode(&generic_code, 0xEB),
                "{name}: expected legacy SSE2 POR for inclusive signed compare mask: {generic_code:02x?}"
            );
        } else {
            assert_eq!(pcmpeq_count(&generic_evidence.machine_code), 0, "{name}");
            assert_eq!(generic_evidence.machine_code.por_count, 0, "{name}");
        }
        assert_no_vex_or_ymm_lowering(&generic_code, name);
        assert_no_vex_or_ymm_lowering(&generic_avx_code, name);
    }
}

#[test]
#[allow(clippy::type_complexity)] // Table rows bind select profiles to machine evidence.
fn x86_narrow_compare_vector_select_canaries_use_profiled_v128_bool_select() {
    let generic = X86TargetFeatures::generic_x86_64();
    let generic_avx = generic
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);
    let sse41 = generic.with_feature(X86TargetFeature::Sse41);
    let sse41_avx = sse41
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);
    let cases: [(
        &str,
        TrustIrTy,
        ICmpOp,
        u8,
        fn(&trust_cg_codegen::x86_64::X86MachineCodeEvidence) -> usize,
    ); 6] = [
        (
            "profile_matrix_v16i8_eq_select",
            v16i8_ty(),
            ICmpOp::Eq,
            0x74,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqb_count,
        ),
        (
            "profile_matrix_v16i8_ne_select",
            v16i8_ty(),
            ICmpOp::Ne,
            0x74,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqb_count,
        ),
        (
            "profile_matrix_v16i8_slt_select",
            v16i8_ty(),
            ICmpOp::Slt,
            0x64,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpgtb_count,
        ),
        (
            "profile_matrix_v8i16_eq_select",
            v8i16_ty(),
            ICmpOp::Eq,
            0x75,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqw_count,
        ),
        (
            "profile_matrix_v8i16_ne_select",
            v8i16_ty(),
            ICmpOp::Ne,
            0x75,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpeqw_count,
        ),
        (
            "profile_matrix_v8i16_slt_select",
            v8i16_ty(),
            ICmpOp::Slt,
            0x65,
            |e: &trust_cg_codegen::x86_64::X86MachineCodeEvidence| e.pcmpgtw_count,
        ),
    ];

    for (name, vector_ty, op, compare_opcode, compare_count) in cases {
        let lir = build_narrow_vector_cmp_select_store_lir(name, vector_ty, op);
        let (generic_code, generic_evidence) = raw_pipeline_with_features(generic)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} generic narrow select canary: {err}"));
        let (generic_avx_code, generic_avx_evidence) = raw_pipeline_with_features(generic_avx)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} generic+AVX narrow select canary: {err}"));
        let (sse41_code, sse41_evidence) = raw_pipeline_with_features(sse41)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} SSE4.1 narrow select canary: {err}"));
        let (sse41_avx_code, sse41_avx_evidence) = raw_pipeline_with_features(sse41_avx)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} SSE4.1+AVX narrow select canary: {err}"));

        eprintln!(
            "x86 narrow compare vector-select canary {name}: generic={:?}, generic_avx={:?}, sse41={:?}, sse41_avx={:?}",
            generic_evidence.machine_code,
            generic_avx_evidence.machine_code,
            sse41_evidence.machine_code,
            sse41_avx_evidence.machine_code
        );
        assert_eq!(generic_evidence.machine_code.target_features, generic);
        assert_eq!(
            generic_avx_evidence.machine_code.target_features,
            generic_avx
        );
        assert_eq!(sse41_evidence.machine_code.target_features, sse41);
        assert_eq!(sse41_avx_evidence.machine_code.target_features, sse41_avx);
        assert_eq!(
            generic_avx_code, generic_code,
            "{name}: generic AVX/AVX2 bits must not change SSE2 narrow select lowering"
        );
        assert_eq!(
            sse41_avx_code, sse41_code,
            "{name}: SSE4.1 AVX/AVX2 bits must not change legacy XMM narrow select lowering"
        );
        assert!(
            contains_sse2_opcode(&generic_code, compare_opcode),
            "{name}: expected legacy SSE2 narrow compare opcode {compare_opcode:#04x}: {generic_code:02x?}"
        );
        assert_eq!(compare_count(&generic_evidence.machine_code), 1, "{name}");
        assert_eq!(
            compare_count(&generic_avx_evidence.machine_code),
            1,
            "{name}"
        );
        assert_eq!(compare_count(&sse41_evidence.machine_code), 1, "{name}");
        assert_eq!(compare_count(&sse41_avx_evidence.machine_code), 1, "{name}");

        assert_eq!(generic_evidence.machine_code.pand_count, 1, "{name}");
        assert_eq!(generic_evidence.machine_code.pandn_count, 1, "{name}");
        assert_eq!(generic_evidence.machine_code.por_count, 1, "{name}");
        assert_eq!(generic_evidence.machine_code.pblendvb_count, 0, "{name}");
        assert_eq!(generic_avx_evidence.machine_code.pand_count, 1, "{name}");
        assert_eq!(generic_avx_evidence.machine_code.pandn_count, 1, "{name}");
        assert_eq!(generic_avx_evidence.machine_code.por_count, 1, "{name}");
        assert_eq!(
            generic_avx_evidence.machine_code.pblendvb_count, 0,
            "{name}"
        );
        assert_eq!(sse41_evidence.machine_code.pblendvb_count, 1, "{name}");
        assert_eq!(sse41_evidence.machine_code.pand_count, 0, "{name}");
        assert_eq!(sse41_evidence.machine_code.pandn_count, 0, "{name}");
        assert_eq!(sse41_evidence.machine_code.por_count, 0, "{name}");
        assert_eq!(sse41_avx_evidence.machine_code.pblendvb_count, 1, "{name}");
        assert_eq!(sse41_avx_evidence.machine_code.pand_count, 0, "{name}");
        assert_eq!(sse41_avx_evidence.machine_code.pandn_count, 0, "{name}");
        assert_eq!(sse41_avx_evidence.machine_code.por_count, 0, "{name}");
        assert!(
            contains_sse41_0f38_opcode(&sse41_code, 0x10),
            "{name}: SSE4.1 profile should encode legacy PBLENDVB: {sse41_code:02x?}"
        );
        assert_eq!(generic_evidence.machine_code.pmovmskb_count, 0, "{name}");
        assert_eq!(sse41_evidence.machine_code.pmovmskb_count, 0, "{name}");
        assert_eq!(generic_evidence.machine_code.ptest_count, 0, "{name}");
        assert_eq!(sse41_evidence.machine_code.ptest_count, 0, "{name}");
        assert_eq!(generic_evidence.machine_code.pcmpeqq_count, 0, "{name}");
        assert_eq!(generic_evidence.machine_code.pcmpgtq_count, 0, "{name}");
        assert_no_vex_or_ymm_lowering(&generic_code, name);
        assert_no_vex_or_ymm_lowering(&generic_avx_code, name);
        assert_no_vex_or_ymm_lowering(&sse41_code, name);
        assert_no_vex_or_ymm_lowering(&sse41_avx_code, name);
    }
}

#[test]
fn x86_v4_v2_compare_vector_select_profile_canaries_cover_v4i32() {
    let generic = X86TargetFeatures::generic_x86_64();
    let generic_avx = generic
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);
    let sse41 = generic.with_feature(X86TargetFeature::Sse41);
    let sse41_avx = sse41
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);

    for (name, op, compare_opcode) in [
        ("profile_matrix_v4i32_eq_select", ICmpOp::Eq, 0x76),
        ("profile_matrix_v4i32_ne_select", ICmpOp::Ne, 0x76),
        ("profile_matrix_v4i32_slt_select", ICmpOp::Slt, 0x66),
    ] {
        let lir = build_narrow_vector_cmp_select_store_lir(name, v4i32_ty(), op);
        let (generic_code, generic_evidence) = raw_pipeline_with_features(generic)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} generic v4i32 select canary: {err}"));
        let (generic_avx_code, generic_avx_evidence) = raw_pipeline_with_features(generic_avx)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} generic+AVX v4i32 select canary: {err}"));
        let (sse41_code, sse41_evidence) = raw_pipeline_with_features(sse41)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} SSE4.1 v4i32 select canary: {err}"));
        let (sse41_avx_code, sse41_avx_evidence) = raw_pipeline_with_features(sse41_avx)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} SSE4.1+AVX v4i32 select canary: {err}"));

        eprintln!(
            "x86 V4/V2 compare vector-select canary {name}: generic={:?}, generic_avx={:?}, sse41={:?}, sse41_avx={:?}",
            generic_evidence.machine_code,
            generic_avx_evidence.machine_code,
            sse41_evidence.machine_code,
            sse41_avx_evidence.machine_code
        );
        assert_eq!(generic_evidence.machine_code.target_features, generic);
        assert_eq!(
            generic_avx_evidence.machine_code.target_features,
            generic_avx
        );
        assert_eq!(sse41_evidence.machine_code.target_features, sse41);
        assert_eq!(sse41_avx_evidence.machine_code.target_features, sse41_avx);
        assert_eq!(
            generic_avx_code, generic_code,
            "{name}: AVX/AVX2 bits must not change generic V4I32 select lowering"
        );
        assert_eq!(
            sse41_avx_code, sse41_code,
            "{name}: AVX/AVX2 bits must not change SSE4.1 V4I32 select lowering"
        );
        assert!(
            contains_sse2_opcode(&generic_code, compare_opcode),
            "{name}: expected legacy V4I32 compare opcode {compare_opcode:#04x}: {generic_code:02x?}"
        );
        match op {
            ICmpOp::Eq => {
                assert_eq!(generic_evidence.machine_code.pcmpeqd_count, 1, "{name}");
                assert_eq!(generic_evidence.machine_code.pcmpgtd_count, 0, "{name}");
                assert_eq!(generic_evidence.machine_code.pxor_count, 0, "{name}");
            }
            ICmpOp::Ne => {
                assert!(
                    generic_evidence.machine_code.pcmpeqd_count >= 2,
                    "{name}: NotEqual should compare lanes and materialize an all-ones inverter"
                );
                assert_eq!(generic_evidence.machine_code.pcmpgtd_count, 0, "{name}");
                assert_eq!(generic_evidence.machine_code.pxor_count, 1, "{name}");
            }
            ICmpOp::Slt => {
                assert_eq!(generic_evidence.machine_code.pcmpgtd_count, 1, "{name}");
                assert_eq!(generic_evidence.machine_code.pxor_count, 0, "{name}");
            }
            _ => unreachable!("v4i32 select canary predicates are fixed"),
        }

        assert_eq!(generic_evidence.machine_code.pand_count, 1, "{name}");
        assert_eq!(generic_evidence.machine_code.pandn_count, 1, "{name}");
        assert_eq!(generic_evidence.machine_code.por_count, 1, "{name}");
        assert_eq!(generic_evidence.machine_code.pblendvb_count, 0, "{name}");
        assert_eq!(generic_avx_evidence.machine_code.pand_count, 1, "{name}");
        assert_eq!(generic_avx_evidence.machine_code.pandn_count, 1, "{name}");
        assert_eq!(generic_avx_evidence.machine_code.por_count, 1, "{name}");
        assert_eq!(
            generic_avx_evidence.machine_code.pblendvb_count, 0,
            "{name}"
        );
        assert_eq!(sse41_evidence.machine_code.pblendvb_count, 1, "{name}");
        assert_eq!(sse41_evidence.machine_code.pand_count, 0, "{name}");
        assert_eq!(sse41_evidence.machine_code.pandn_count, 0, "{name}");
        assert_eq!(sse41_evidence.machine_code.por_count, 0, "{name}");
        assert_eq!(sse41_avx_evidence.machine_code.pblendvb_count, 1, "{name}");
        assert_eq!(sse41_avx_evidence.machine_code.pand_count, 0, "{name}");
        assert_eq!(sse41_avx_evidence.machine_code.pandn_count, 0, "{name}");
        assert_eq!(sse41_avx_evidence.machine_code.por_count, 0, "{name}");
        assert!(
            contains_sse41_0f38_opcode(&sse41_code, 0x10),
            "{name}: SSE4.1 profile should encode legacy PBLENDVB: {sse41_code:02x?}"
        );
        for (profile, evidence) in [
            ("generic", &generic_evidence),
            ("generic+avx", &generic_avx_evidence),
            ("sse4.1", &sse41_evidence),
            ("sse4.1+avx", &sse41_avx_evidence),
        ] {
            assert_eq!(evidence.machine_code.pmovmskb_count, 0, "{name} {profile}");
            assert_eq!(evidence.machine_code.ptest_count, 0, "{name} {profile}");
            assert_eq!(evidence.machine_code.pcmpeqq_count, 0, "{name} {profile}");
            assert_eq!(evidence.machine_code.pcmpgtq_count, 0, "{name} {profile}");
            assert_no_scalar_lane_fallback(&evidence.machine_code, name);
        }
        assert_no_vex_or_ymm_lowering(&generic_code, name);
        assert_no_vex_or_ymm_lowering(&generic_avx_code, name);
        assert_no_vex_or_ymm_lowering(&sse41_code, name);
        assert_no_vex_or_ymm_lowering(&sse41_avx_code, name);
    }
}

#[test]
fn x86_v4_v2_compare_vector_select_profile_canaries_cover_v2i64() {
    let generic = X86TargetFeatures::generic_x86_64();
    let generic_avx = generic
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);
    let sse41 = generic.with_feature(X86TargetFeature::Sse41);
    let sse41_avx = sse41
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);
    let sse42 = sse41.with_feature(X86TargetFeature::Sse42);
    let sse42_avx = sse42
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);

    for (name, op, expect_pxor) in [
        ("profile_matrix_v2i64_eq_select", ICmpOp::Eq, false),
        ("profile_matrix_v2i64_ne_select", ICmpOp::Ne, true),
    ] {
        let lir = build_narrow_vector_cmp_select_store_lir(name, v2i64_ty(), op);
        let err = raw_pipeline_with_features(generic)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .expect_err("generic x86-64 must reject V2I64 Eq/Ne vector selects");
        assert_unsupported_feature(err, X86Opcode::Pcmpeqq, X86TargetFeature::Sse41);
        let err = raw_pipeline_with_features(generic_avx)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .expect_err("generic+AVX x86-64 must not make V2I64 Eq/Ne selects legal");
        assert_unsupported_feature(err, X86Opcode::Pcmpeqq, X86TargetFeature::Sse41);

        let (sse41_code, sse41_evidence) = raw_pipeline_with_features(sse41)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} SSE4.1 v2i64 select canary: {err}"));
        let (sse41_avx_code, sse41_avx_evidence) = raw_pipeline_with_features(sse41_avx)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} SSE4.1+AVX v2i64 select canary: {err}"));

        eprintln!(
            "x86 V2I64 Eq/Ne vector-select canary {name}: sse41={:?}, sse41_avx={:?}",
            sse41_evidence.machine_code, sse41_avx_evidence.machine_code
        );
        assert_eq!(sse41_evidence.machine_code.target_features, sse41);
        assert_eq!(sse41_avx_evidence.machine_code.target_features, sse41_avx);
        assert_eq!(
            sse41_avx_code, sse41_code,
            "{name}: AVX/AVX2 bits must not change SSE4.1 V2I64 select lowering"
        );
        assert_eq!(sse41_evidence.machine_code.pcmpeqq_count, 1, "{name}");
        assert_eq!(sse41_evidence.machine_code.pcmpgtq_count, 0, "{name}");
        assert_eq!(
            sse41_evidence.machine_code.pxor_count,
            usize::from(expect_pxor),
            "{name}"
        );
        assert_eq!(sse41_evidence.machine_code.pblendvb_count, 1, "{name}");
        assert_eq!(sse41_evidence.machine_code.pand_count, 0, "{name}");
        assert_eq!(sse41_evidence.machine_code.pandn_count, 0, "{name}");
        assert_eq!(sse41_evidence.machine_code.por_count, 0, "{name}");
        assert_eq!(sse41_evidence.machine_code.pmovmskb_count, 0, "{name}");
        assert_eq!(sse41_evidence.machine_code.ptest_count, 0, "{name}");
        assert_no_scalar_lane_fallback(&sse41_evidence.machine_code, name);
        assert_no_scalar_lane_fallback(&sse41_avx_evidence.machine_code, name);
        assert!(
            contains_sse41_0f38_opcode(&sse41_code, 0x29),
            "{name}: SSE4.1 profile should encode legacy PCMPEQQ: {sse41_code:02x?}"
        );
        assert!(
            contains_sse41_0f38_opcode(&sse41_code, 0x10),
            "{name}: SSE4.1 profile should encode legacy PBLENDVB: {sse41_code:02x?}"
        );
        assert_no_vex_or_ymm_lowering(&sse41_code, name);
        assert_no_vex_or_ymm_lowering(&sse41_avx_code, name);
    }

    for (name, op, expect_pcmpeqq, expect_por) in [
        ("profile_matrix_v2i64_slt_select", ICmpOp::Slt, 0, 0),
        ("profile_matrix_v2i64_sle_select", ICmpOp::Sle, 1, 1),
        ("profile_matrix_v2i64_sgt_select", ICmpOp::Sgt, 0, 0),
        ("profile_matrix_v2i64_sge_select", ICmpOp::Sge, 1, 1),
    ] {
        let lir = build_narrow_vector_cmp_select_store_lir(name, v2i64_ty(), op);
        let err = raw_pipeline_with_features(generic)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .expect_err("generic x86-64 must reject V2I64 signed vector selects");
        assert_unsupported_feature(err, X86Opcode::Pcmpgtq, X86TargetFeature::Sse42);
        let err = raw_pipeline_with_features(sse41)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .expect_err("SSE4.1-only x86-64 must reject V2I64 signed vector selects");
        assert_unsupported_feature(err, X86Opcode::Pcmpgtq, X86TargetFeature::Sse42);

        let (sse42_code, sse42_evidence) = raw_pipeline_with_features(sse42)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} SSE4.2 v2i64 select canary: {err}"));
        let (sse42_avx_code, sse42_avx_evidence) = raw_pipeline_with_features(sse42_avx)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} SSE4.2+AVX v2i64 select canary: {err}"));

        eprintln!(
            "x86 V2I64 signed vector-select canary {name}: sse42={:?}, sse42_avx={:?}",
            sse42_evidence.machine_code, sse42_avx_evidence.machine_code
        );
        assert_eq!(sse42_evidence.machine_code.target_features, sse42);
        assert_eq!(sse42_avx_evidence.machine_code.target_features, sse42_avx);
        assert_eq!(
            sse42_avx_code, sse42_code,
            "{name}: AVX/AVX2 bits must not change SSE4.2 V2I64 select lowering"
        );
        assert_eq!(sse42_evidence.machine_code.pcmpgtq_count, 1, "{name}");
        assert_eq!(
            sse42_evidence.machine_code.pcmpeqq_count, expect_pcmpeqq,
            "{name}"
        );
        assert_eq!(sse42_evidence.machine_code.por_count, expect_por, "{name}");
        assert_eq!(sse42_evidence.machine_code.pxor_count, 0, "{name}");
        assert_eq!(sse42_evidence.machine_code.pblendvb_count, 1, "{name}");
        assert_eq!(sse42_evidence.machine_code.pand_count, 0, "{name}");
        assert_eq!(sse42_evidence.machine_code.pandn_count, 0, "{name}");
        assert_eq!(sse42_evidence.machine_code.pmovmskb_count, 0, "{name}");
        assert_eq!(sse42_evidence.machine_code.ptest_count, 0, "{name}");
        assert_no_scalar_lane_fallback(&sse42_evidence.machine_code, name);
        assert_no_scalar_lane_fallback(&sse42_avx_evidence.machine_code, name);
        assert!(
            contains_sse41_0f38_opcode(&sse42_code, 0x37),
            "{name}: SSE4.2 profile should encode legacy PCMPGTQ: {sse42_code:02x?}"
        );
        assert!(
            contains_sse41_0f38_opcode(&sse42_code, 0x10),
            "{name}: SSE4.2 profile should encode legacy PBLENDVB: {sse42_code:02x?}"
        );
        assert_no_vex_or_ymm_lowering(&sse42_code, name);
        assert_no_vex_or_ymm_lowering(&sse42_avx_code, name);
    }
}

#[test]
fn x86_v4_v2_v2i64_compare_mask_to_bits_profile_canaries_cover_all_predicates() {
    let generic = X86TargetFeatures::generic_x86_64();
    let generic_avx = generic
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);
    let sse41 = generic.with_feature(X86TargetFeature::Sse41);
    let sse41_avx = sse41
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);
    let sse42 = sse41.with_feature(X86TargetFeature::Sse42);
    let sse42_avx = sse42
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);

    for (name, op, expect_pxor) in [
        ("profile_matrix_v2i64_eq_mask_to_bits", ICmpOp::Eq, 0),
        ("profile_matrix_v2i64_ne_mask_to_bits", ICmpOp::Ne, 1),
    ] {
        let lir = build_narrow_vector_cmp_mask_to_bits_lir(name, v2i64_ty(), v2_bool_ty(), op);
        let err = raw_pipeline_with_features(generic)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .expect_err("generic x86-64 must reject V2I64 Eq/Ne mask_to_bits");
        assert_unsupported_feature(err, X86Opcode::Pcmpeqq, X86TargetFeature::Sse41);
        let err = raw_pipeline_with_features(generic_avx)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .expect_err("generic+AVX x86-64 must not make V2I64 Eq/Ne mask_to_bits legal");
        assert_unsupported_feature(err, X86Opcode::Pcmpeqq, X86TargetFeature::Sse41);

        let (sse41_code, sse41_evidence) = raw_pipeline_with_features(sse41)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} SSE4.1 v2i64 mask_to_bits canary: {err}"));
        let (sse41_avx_code, sse41_avx_evidence) = raw_pipeline_with_features(sse41_avx)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} SSE4.1+AVX v2i64 mask_to_bits canary: {err}"));

        eprintln!(
            "x86 V2I64 Eq/Ne mask_to_bits canary {name}: sse41={:?}, sse41_avx={:?}",
            sse41_evidence.machine_code, sse41_avx_evidence.machine_code
        );
        assert_eq!(sse41_evidence.machine_code.target_features, sse41);
        assert_eq!(sse41_avx_evidence.machine_code.target_features, sse41_avx);
        assert_eq!(
            sse41_avx_code, sse41_code,
            "{name}: AVX/AVX2 bits must not change SSE4.1 V2I64 mask_to_bits lowering"
        );
        assert_eq!(sse41_evidence.machine_code.pcmpeqq_count, 1, "{name}");
        assert_eq!(sse41_evidence.machine_code.pcmpgtq_count, 0, "{name}");
        assert_eq!(sse41_evidence.machine_code.por_count, 0, "{name}");
        assert_eq!(
            sse41_evidence.machine_code.pxor_count, expect_pxor,
            "{name}"
        );
        assert_eq!(sse41_evidence.machine_code.pmovmskb_count, 1, "{name}");
        assert_eq!(sse41_avx_evidence.machine_code.pmovmskb_count, 1, "{name}");
        assert_eq!(sse41_evidence.machine_code.pblendvb_count, 0, "{name}");
        assert_eq!(sse41_evidence.machine_code.ptest_count, 0, "{name}");
        assert_no_scalar_lane_fallback(&sse41_evidence.machine_code, name);
        assert_no_scalar_lane_fallback(&sse41_avx_evidence.machine_code, name);
        assert!(
            contains_sse41_0f38_opcode(&sse41_code, 0x29),
            "{name}: SSE4.1 profile should encode legacy PCMPEQQ: {sse41_code:02x?}"
        );
        assert!(
            contains_sse2_opcode(&sse41_code, 0xD7),
            "{name}: expected legacy PMOVMSKB mask extraction: {sse41_code:02x?}"
        );
        assert_no_vex_or_ymm_lowering(&sse41_code, name);
        assert_no_vex_or_ymm_lowering(&sse41_avx_code, name);
    }

    for (name, op, expect_pcmpeqq, expect_por) in [
        ("profile_matrix_v2i64_slt_mask_to_bits", ICmpOp::Slt, 0, 0),
        ("profile_matrix_v2i64_sle_mask_to_bits", ICmpOp::Sle, 1, 1),
        ("profile_matrix_v2i64_sgt_mask_to_bits", ICmpOp::Sgt, 0, 0),
        ("profile_matrix_v2i64_sge_mask_to_bits", ICmpOp::Sge, 1, 1),
    ] {
        let lir = build_narrow_vector_cmp_mask_to_bits_lir(name, v2i64_ty(), v2_bool_ty(), op);
        let err = raw_pipeline_with_features(generic)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .expect_err("generic x86-64 must reject V2I64 signed mask_to_bits");
        assert_unsupported_feature(err, X86Opcode::Pcmpgtq, X86TargetFeature::Sse42);
        let err = raw_pipeline_with_features(sse41)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .expect_err("SSE4.1-only x86-64 must reject V2I64 signed mask_to_bits");
        assert_unsupported_feature(err, X86Opcode::Pcmpgtq, X86TargetFeature::Sse42);

        let (sse42_code, sse42_evidence) = raw_pipeline_with_features(sse42)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} SSE4.2 v2i64 mask_to_bits canary: {err}"));
        let (sse42_avx_code, sse42_avx_evidence) = raw_pipeline_with_features(sse42_avx)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} SSE4.2+AVX v2i64 mask_to_bits canary: {err}"));

        eprintln!(
            "x86 V2I64 signed mask_to_bits canary {name}: sse42={:?}, sse42_avx={:?}",
            sse42_evidence.machine_code, sse42_avx_evidence.machine_code
        );
        assert_eq!(sse42_evidence.machine_code.target_features, sse42);
        assert_eq!(sse42_avx_evidence.machine_code.target_features, sse42_avx);
        assert_eq!(
            sse42_avx_code, sse42_code,
            "{name}: AVX/AVX2 bits must not change SSE4.2 V2I64 mask_to_bits lowering"
        );
        assert_eq!(sse42_evidence.machine_code.pcmpgtq_count, 1, "{name}");
        assert_eq!(
            sse42_evidence.machine_code.pcmpeqq_count, expect_pcmpeqq,
            "{name}"
        );
        assert_eq!(sse42_evidence.machine_code.por_count, expect_por, "{name}");
        assert_eq!(sse42_evidence.machine_code.pxor_count, 0, "{name}");
        assert_eq!(sse42_evidence.machine_code.pmovmskb_count, 1, "{name}");
        assert_eq!(sse42_avx_evidence.machine_code.pmovmskb_count, 1, "{name}");
        assert_eq!(sse42_evidence.machine_code.pblendvb_count, 0, "{name}");
        assert_eq!(sse42_evidence.machine_code.ptest_count, 0, "{name}");
        assert_no_scalar_lane_fallback(&sse42_evidence.machine_code, name);
        assert_no_scalar_lane_fallback(&sse42_avx_evidence.machine_code, name);
        assert!(
            contains_sse41_0f38_opcode(&sse42_code, 0x37),
            "{name}: SSE4.2 profile should encode legacy PCMPGTQ: {sse42_code:02x?}"
        );
        assert!(
            contains_sse2_opcode(&sse42_code, 0xD7),
            "{name}: expected legacy PMOVMSKB mask extraction: {sse42_code:02x?}"
        );
        assert_no_vex_or_ymm_lowering(&sse42_code, name);
        assert_no_vex_or_ymm_lowering(&sse42_avx_code, name);
    }
}

#[test]
fn x86_canonical_bool_constant_select_profile_canaries_use_profiled_v128_bool_select() {
    let generic = X86TargetFeatures::generic_x86_64();
    let generic_avx = generic
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);
    let sse41 = generic.with_feature(X86TargetFeature::Sse41);
    let sse41_avx = sse41
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);

    for (name, vector_ty, mask_ty, lanes, true_bits) in [
        (
            "profile_matrix_v16i8_canonical_bool_constant_select",
            v16i8_ty(),
            v16_bool_ty(),
            16,
            0xCA69,
        ),
        (
            "profile_matrix_v8i16_canonical_bool_constant_select",
            v8i16_ty(),
            v8_bool_ty(),
            8,
            0x96,
        ),
    ] {
        let lir =
            build_narrow_bool_const_select_store_lir(name, vector_ty, mask_ty, lanes, true_bits);
        let (generic_code, generic_evidence) = pressure_pipeline_with_features(generic)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} generic bool-constant select canary: {err}"));
        let (generic_avx_code, generic_avx_evidence) = pressure_pipeline_with_features(generic_avx)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} generic+AVX bool-constant select canary: {err}"));
        let (sse41_code, sse41_evidence) = pressure_pipeline_with_features(sse41)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} SSE4.1 bool-constant select canary: {err}"));
        let (sse41_avx_code, sse41_avx_evidence) = pressure_pipeline_with_features(sse41_avx)
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
            .unwrap_or_else(|err| panic!("{name} SSE4.1+AVX bool-constant select canary: {err}"));

        eprintln!(
            "x86 canonical bool-constant vector-select canary {name}: generic={:?}, generic_avx={:?}, sse41={:?}, sse41_avx={:?}",
            generic_evidence.machine_code,
            generic_avx_evidence.machine_code,
            sse41_evidence.machine_code,
            sse41_avx_evidence.machine_code
        );
        assert_eq!(generic_evidence.machine_code.target_features, generic);
        assert_eq!(
            generic_avx_evidence.machine_code.target_features,
            generic_avx
        );
        assert_eq!(sse41_evidence.machine_code.target_features, sse41);
        assert_eq!(sse41_avx_evidence.machine_code.target_features, sse41_avx);
        assert_eq!(
            generic_avx_code, generic_code,
            "{name}: AVX/AVX2 bits must not change generic SSE2 bool-constant select lowering"
        );
        assert_eq!(
            sse41_avx_code, sse41_code,
            "{name}: AVX/AVX2 bits must not change SSE4.1 bool-constant select lowering"
        );

        assert_eq!(generic_evidence.machine_code.pand_count, 1, "{name}");
        assert_eq!(generic_evidence.machine_code.pandn_count, 1, "{name}");
        assert_eq!(generic_evidence.machine_code.por_count, 1, "{name}");
        assert_eq!(generic_evidence.machine_code.pblendvb_count, 0, "{name}");
        assert_eq!(generic_avx_evidence.machine_code.pand_count, 1, "{name}");
        assert_eq!(generic_avx_evidence.machine_code.pandn_count, 1, "{name}");
        assert_eq!(generic_avx_evidence.machine_code.por_count, 1, "{name}");
        assert_eq!(
            generic_avx_evidence.machine_code.pblendvb_count, 0,
            "{name}"
        );
        assert_eq!(sse41_evidence.machine_code.pblendvb_count, 1, "{name}");
        assert_eq!(sse41_evidence.machine_code.pand_count, 0, "{name}");
        assert_eq!(sse41_evidence.machine_code.pandn_count, 0, "{name}");
        assert_eq!(sse41_evidence.machine_code.por_count, 0, "{name}");
        assert_eq!(sse41_avx_evidence.machine_code.pblendvb_count, 1, "{name}");
        assert_eq!(sse41_avx_evidence.machine_code.pand_count, 0, "{name}");
        assert_eq!(sse41_avx_evidence.machine_code.pandn_count, 0, "{name}");
        assert_eq!(sse41_avx_evidence.machine_code.por_count, 0, "{name}");

        assert!(
            contains_sse2_opcode(&generic_code, 0xDB)
                && contains_sse2_opcode(&generic_code, 0xDF)
                && contains_sse2_opcode(&generic_code, 0xEB),
            "{name}: generic profile should encode legacy PAND/PANDN/POR: {generic_code:02x?}"
        );
        assert!(
            contains_sse41_0f38_opcode(&sse41_code, 0x10),
            "{name}: SSE4.1 profile should encode legacy PBLENDVB: {sse41_code:02x?}"
        );

        for (profile, evidence) in [
            ("generic", &generic_evidence),
            ("generic+avx", &generic_avx_evidence),
            ("sse4.1", &sse41_evidence),
            ("sse4.1+avx", &sse41_avx_evidence),
        ] {
            assert_eq!(
                evidence.machine_code.pmovmskb_count, 0,
                "{name} {profile}: bool-constant select must not extract masks"
            );
            assert_eq!(
                evidence.machine_code.ptest_count, 0,
                "{name} {profile}: bool-constant select must not route through PTEST"
            );
            assert_eq!(
                evidence.machine_code.pcmpeqb_count, 0,
                "{name} {profile}: bool-constant select must not rebuild byte compare masks"
            );
            assert_eq!(
                evidence.machine_code.pcmpeqw_count, 0,
                "{name} {profile}: bool-constant select must not rebuild word compare masks"
            );
            assert_eq!(
                evidence.machine_code.pcmpgtb_count, 0,
                "{name} {profile}: bool-constant select must not rebuild byte signed compare masks"
            );
            assert_eq!(
                evidence.machine_code.pcmpgtw_count, 0,
                "{name} {profile}: bool-constant select must not rebuild word signed compare masks"
            );
            assert_eq!(evidence.machine_code.pinsrd_count, 0, "{name} {profile}");
            assert_eq!(evidence.machine_code.pinsrq_count, 0, "{name} {profile}");
            assert_eq!(evidence.machine_code.pextrd_count, 0, "{name} {profile}");
            assert_eq!(evidence.machine_code.pextrq_count, 0, "{name} {profile}");
            assert_eq!(
                evidence.machine_code.movd_to_xmm_count, 0,
                "{name} {profile}"
            );
            assert_eq!(
                evidence.machine_code.movq_to_xmm_count, 0,
                "{name} {profile}"
            );
        }

        assert_no_vex_or_ymm_lowering(&generic_code, name);
        assert_no_vex_or_ymm_lowering(&generic_avx_code, name);
        assert_no_vex_or_ymm_lowering(&sse41_code, name);
        assert_no_vex_or_ymm_lowering(&sse41_avx_code, name);
    }
}

#[cfg(target_arch = "x86_64")]
#[test]
fn host_profile_v128_sse4_canaries_record_runtime_features_or_fail_closed() {
    let host = X86TargetFeatures::host();
    let eq = build_v2i64_bool_mask_extract_lir("host_profile_v2i64_eq_bool_extract", ICmpOp::Eq);
    let eq_result = raw_pipeline_with_features(host)
        .compile_trust_ir_function_with_regalloc_pressure_evidence(&eq);
    if host.contains(X86TargetFeature::Sse41) {
        let (code, evidence) = eq_result.expect("SSE4.1 host should admit PCMPEQQ");
        eprintln!(
            "x86 host V128 eq profile canary: {:?}",
            evidence.machine_code
        );
        assert_eq!(evidence.machine_code.target_features, host);
        assert_eq!(evidence.machine_code.pcmpeqq_count, 1);
        assert_no_vex_or_ymm_lowering(&code, "host v2i64 equality compare");
    } else {
        let err = eq_result.expect_err("host without SSE4.1 must reject PCMPEQQ");
        assert_unsupported_feature(err, X86Opcode::Pcmpeqq, X86TargetFeature::Sse41);
    }

    let slt = build_v2i64_bool_mask_extract_lir("host_profile_v2i64_slt_bool_extract", ICmpOp::Slt);
    let slt_result = raw_pipeline_with_features(host)
        .compile_trust_ir_function_with_regalloc_pressure_evidence(&slt);
    if host.contains(X86TargetFeature::Sse42) {
        let (code, evidence) = slt_result.expect("SSE4.2 host should admit PCMPGTQ");
        eprintln!(
            "x86 host V128 signed-compare profile canary: {:?}",
            evidence.machine_code
        );
        assert_eq!(evidence.machine_code.target_features, host);
        assert_eq!(evidence.machine_code.pcmpgtq_count, 1);
        assert_no_vex_or_ymm_lowering(&code, "host v2i64 signed compare");
    } else {
        let err = slt_result.expect_err("host without SSE4.2 must reject PCMPGTQ");
        assert_unsupported_feature(err, X86Opcode::Pcmpgtq, X86TargetFeature::Sse42);
    }
}

#[test]
fn current_x86_64_public_module_pipeline_admits_chc_sse4_opcodes() {
    let pipeline = current_raw_pipeline();
    let funcs: Vec<_> = public_sse4_feature_gate_cases()
        .into_iter()
        .map(|(opcode, operands, _)| {
            minimal_x86_isel_func(&format!("current_admits_{opcode:?}"), opcode, operands)
        })
        .collect();

    let code = pipeline
        .compile_module(&funcs)
        .expect("current x86-64 module pipeline must admit CHC SSE4 opcodes");
    assert!(!code.is_empty());
}

#[test]
fn explicit_feature_profiles_admit_sse4_opcodes_only_when_bit_is_present() {
    let sse41_pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O0,
        output_format: X86OutputFormat::RawBytes,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Simplified,
        target_features: X86TargetFeatures::generic_x86_64().with_feature(X86TargetFeature::Sse41),
        ..X86PipelineConfig::generic_x86_64()
    });
    let sse42_pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O0,
        output_format: X86OutputFormat::RawBytes,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Simplified,
        target_features: X86TargetFeatures::generic_x86_64().with_feature(X86TargetFeature::Sse42),
        ..X86PipelineConfig::generic_x86_64()
    });

    for (opcode, operands, feature) in public_sse4_feature_gate_cases() {
        let func = minimal_x86_isel_func(
            &format!("explicit_feature_profile_{opcode:?}"),
            opcode,
            operands,
        );
        match feature {
            X86TargetFeature::Sse41 => {
                sse41_pipeline
                    .compile_function(&func)
                    .unwrap_or_else(|err| panic!("SSE4.1 profile should admit {opcode:?}: {err}"));
                let err = sse42_pipeline
                    .compile_function(&func)
                    .expect_err("SSE4.2-only profile must reject SSE4.1 opcode");
                assert_unsupported_feature(err, opcode, X86TargetFeature::Sse41);
            }
            X86TargetFeature::Sse42 => {
                sse42_pipeline
                    .compile_function(&func)
                    .unwrap_or_else(|err| panic!("SSE4.2 profile should admit {opcode:?}: {err}"));
                let err = sse41_pipeline
                    .compile_function(&func)
                    .expect_err("SSE4.1-only profile must reject SSE4.2 opcode");
                assert_unsupported_feature(err, opcode, X86TargetFeature::Sse42);
            }
            X86TargetFeature::Popcnt | X86TargetFeature::Avx | X86TargetFeature::Avx2 => {
                unreachable!("SSE4 gate cases must not carry non-SSE4 features")
            }
        }
    }
}

fn build_v128_i32_mul_store_lir(name: &str) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![Type::I64, Type::I64, Type::I64],
            returns: vec![],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(0)],
                    results: vec![Value(3)],
                },
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(1)],
                    results: vec![Value(4)],
                },
                Instruction {
                    opcode: Opcode::Imul,
                    args: vec![Value(3), Value(4)],
                    results: vec![Value(5)],
                },
                Instruction {
                    opcode: Opcode::Store {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(5), Value(2)],
                    results: vec![],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

const PROFILE_V128_SPILL_LANES: usize = 24;

fn build_v128_profile_spill_lir(name: &str) -> LirFunction {
    build_v128_profile_spill_lir_with_opcode(name, Opcode::Iadd)
}

fn build_ctpop_lir(name: &str, ty: Type) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![ty.clone()],
            returns: vec![ty],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::CtPop,
                    args: vec![Value(0)],
                    results: vec![Value(1)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(1)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn build_v128_profile_spill_lir_with_opcode(name: &str, opcode: Opcode) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: std::iter::repeat_n(Type::V128, PROFILE_V128_SPILL_LANES)
                .chain([Type::I64])
                .collect(),
            returns: vec![],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);

    let mut acc = Value(0);
    let mut instructions = Vec::new();
    for (next_value, lane) in
        (PROFILE_V128_SPILL_LANES as u32 + 1..).zip(1..PROFILE_V128_SPILL_LANES)
    {
        let result = Value(next_value);
        instructions.push(Instruction {
            opcode: opcode.clone(),
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
        args: vec![acc, Value(PROFILE_V128_SPILL_LANES as u32)],
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

fn build_v4i32_extract_lir(name: &str, lane: u8) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![Type::I64],
            returns: vec![Type::I32],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(0)],
                    results: vec![Value(1)],
                },
                Instruction {
                    opcode: Opcode::V4I32ExtractLane { lane },
                    args: vec![Value(1)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(2)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn build_v2i64_extract_lir(name: &str, lane: u8) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![Type::I64],
            returns: vec![Type::I64],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(0)],
                    results: vec![Value(1)],
                },
                Instruction {
                    opcode: Opcode::V2I64ExtractLane { lane },
                    args: vec![Value(1)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(2)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn build_v2i64_bool_mask_extract_lir(name: &str, op: ICmpOp) -> LirFunction {
    let v2i64 = v2i64_ty();
    let mut module = TrustIrModule::new(format!("{name}_module"));
    add_trust_ir_function(
        &mut module,
        9200,
        name,
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr], vec![TrustIrTy::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr), (v(1), TrustIrTy::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v2i64.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: v2i64.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: v2i64,
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_cg_lower::bitfield_dialect::v2i64_bool_mask_extract(
                        v(12),
                        TrustIrTy::I32,
                    ),
                )))
                .with_result(v(13)),
                InstrNode::new(Inst::Return {
                    values: vec![v(13)],
                }),
            ],
        }],
    );

    let mut translated =
        trust_cg_lower::translate_module(&module).expect("feature-test module must translate");
    assert_eq!(translated.len(), 1);
    translated.pop().expect("translated function").0
}

fn build_v4i32_ne_mask_extract_lir(name: &str) -> LirFunction {
    let v4i32 = v4i32_ty();
    let mut module = TrustIrModule::new(format!("{name}_module"));
    add_trust_ir_function(
        &mut module,
        9202,
        name,
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr], vec![TrustIrTy::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr), (v(1), TrustIrTy::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v4i32.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: v4i32.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ne,
                    ty: v4i32.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Const {
                    ty: v4i32.clone(),
                    value: v4i32_const([-1, -1, -1, -1]),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Const {
                    ty: v4i32.clone(),
                    value: v4i32_const([0, 0, 0, 0]),
                })
                .with_result(v(14)),
                InstrNode::new(Inst::Select {
                    ty: v4i32.clone(),
                    cond: v(12),
                    then_val: v(13),
                    else_val: v(14),
                })
                .with_result(v(15)),
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_cg_lower::bitfield_dialect::v4i32_mask_extract(v(15)),
                )))
                .with_result(v(16)),
                InstrNode::new(Inst::Return {
                    values: vec![v(16)],
                }),
            ],
        }],
    );

    let mut translated =
        trust_cg_lower::translate_module(&module).expect("feature-test module must translate");
    assert_eq!(translated.len(), 1);
    translated.pop().expect("translated function").0
}

fn build_narrow_vector_icmp_store_lir(name: &str, vector_ty: TrustIrTy, op: ICmpOp) -> LirFunction {
    let mut module = TrustIrModule::new(format!("{name}_module"));
    add_trust_ir_function(
        &mut module,
        9206,
        name,
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr, TrustIrTy::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), TrustIrTy::Ptr),
                (v(1), TrustIrTy::Ptr),
                (v(2), TrustIrTy::Ptr),
            ],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: vector_ty.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Store {
                    ty: vector_ty,
                    ptr: v(2),
                    value: v(12),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    let mut translated =
        trust_cg_lower::translate_module(&module).expect("feature-test narrow ICmp module");
    assert_eq!(translated.len(), 1);
    translated.pop().expect("translated function").0
}

fn build_narrow_vector_bitwise_store_lir(
    name: &str,
    vector_ty: TrustIrTy,
    op: BinOp,
) -> LirFunction {
    let mut module = TrustIrModule::new(format!("{name}_module"));
    add_trust_ir_function(
        &mut module,
        9211,
        name,
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr, TrustIrTy::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), TrustIrTy::Ptr),
                (v(1), TrustIrTy::Ptr),
                (v(2), TrustIrTy::Ptr),
            ],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::BinOp {
                    op,
                    ty: vector_ty.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Store {
                    ty: vector_ty,
                    ptr: v(2),
                    value: v(12),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    let mut translated =
        trust_cg_lower::translate_module(&module).expect("feature-test narrow bitwise module");
    assert_eq!(translated.len(), 1);
    translated.pop().expect("translated function").0
}

fn build_narrow_vector_cmp_mask_to_bits_lir(
    name: &str,
    vector_ty: TrustIrTy,
    mask_ty: TrustIrTy,
    op: ICmpOp,
) -> LirFunction {
    let mut module = TrustIrModule::new(format!("{name}_module"));
    add_trust_ir_function(
        &mut module,
        9207,
        name,
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr], vec![TrustIrTy::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr), (v(1), TrustIrTy::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: vector_ty,
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::mask_to_bits(mask_ty, v(12), TrustIrTy::I32),
                )))
                .with_result(v(13)),
                InstrNode::new(Inst::Return {
                    values: vec![v(13)],
                }),
            ],
        }],
    );

    let mut translated =
        trust_cg_lower::translate_module(&module).expect("feature-test narrow mask_to_bits module");
    assert_eq!(translated.len(), 1);
    translated.pop().expect("translated function").0
}

fn build_bool_const_mask_to_bits_lir(
    name: &str,
    mask_ty: TrustIrTy,
    lanes: usize,
    true_bits: u32,
) -> LirFunction {
    let mut module = TrustIrModule::new(format!("{name}_module"));
    add_trust_ir_function(
        &mut module,
        9210,
        name,
        func_ty(vec![], vec![TrustIrTy::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: mask_ty.clone(),
                    value: bool_mask_const_from_bits(lanes, true_bits),
                })
                .with_result(v(10)),
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::mask_to_bits(mask_ty, v(10), TrustIrTy::I32),
                )))
                .with_result(v(11)),
                InstrNode::new(Inst::Return {
                    values: vec![v(11)],
                }),
            ],
        }],
    );

    let mut translated =
        trust_cg_lower::translate_module(&module).expect("feature-test bool mask_to_bits module");
    assert_eq!(translated.len(), 1);
    translated.pop().expect("translated function").0
}

fn build_narrow_vector_cmp_select_store_lir(
    name: &str,
    vector_ty: TrustIrTy,
    op: ICmpOp,
) -> LirFunction {
    let mut module = TrustIrModule::new(format!("{name}_module"));
    add_trust_ir_function(
        &mut module,
        9208,
        name,
        func_ty(
            vec![
                TrustIrTy::Ptr,
                TrustIrTy::Ptr,
                TrustIrTy::Ptr,
                TrustIrTy::Ptr,
            ],
            vec![],
        ),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), TrustIrTy::Ptr),
                (v(1), TrustIrTy::Ptr),
                (v(2), TrustIrTy::Ptr),
                (v(3), TrustIrTy::Ptr),
            ],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(2),
                    align: None,
                    volatile: false,
                })
                .with_result(v(12)),
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: vector_ty.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Select {
                    ty: vector_ty.clone(),
                    cond: v(13),
                    then_val: v(10),
                    else_val: v(12),
                })
                .with_result(v(14)),
                InstrNode::new(Inst::Store {
                    ty: vector_ty,
                    ptr: v(3),
                    value: v(14),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    let mut translated =
        trust_cg_lower::translate_module(&module).expect("feature-test narrow select module");
    assert_eq!(translated.len(), 1);
    translated.pop().expect("translated function").0
}

fn build_narrow_bool_const_select_store_lir(
    name: &str,
    vector_ty: TrustIrTy,
    mask_ty: TrustIrTy,
    lanes: usize,
    true_bits: u32,
) -> LirFunction {
    let mut module = TrustIrModule::new(format!("{name}_module"));
    add_trust_ir_function(
        &mut module,
        9209,
        name,
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr, TrustIrTy::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), TrustIrTy::Ptr),
                (v(1), TrustIrTy::Ptr),
                (v(2), TrustIrTy::Ptr),
            ],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::Const {
                    ty: mask_ty,
                    value: bool_mask_const_from_bits(lanes, true_bits),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Select {
                    ty: vector_ty.clone(),
                    cond: v(12),
                    then_val: v(10),
                    else_val: v(11),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Store {
                    ty: vector_ty,
                    ptr: v(2),
                    value: v(13),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    let mut translated = trust_cg_lower::translate_module(&module)
        .expect("feature-test bool-constant select module");
    assert_eq!(translated.len(), 1);
    translated.pop().expect("translated function").0
}

fn build_v4i32_mask_branch_lir(name: &str) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![Type::I64, Type::I64],
            returns: vec![Type::I64],
        },
    );
    let entry = Block(0);
    let then_block = Block(1);
    let else_block = Block(2);
    func.entry_block = entry;
    func.block_order = vec![entry, then_block, else_block];
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(0)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(1)],
                    results: vec![Value(3)],
                },
                Instruction {
                    opcode: Opcode::Icmp {
                        cond: trust_cg_lower::instructions::IntCC::Equal,
                    },
                    args: vec![Value(2), Value(3)],
                    results: vec![Value(4)],
                },
                Instruction {
                    opcode: Opcode::Brif {
                        cond: Value(4),
                        then_dest: then_block,
                        else_dest: else_block,
                    },
                    args: vec![Value(4)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func.blocks.insert(
        then_block,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Iconst {
                        ty: Type::I64,
                        imm: 1,
                    },
                    args: vec![],
                    results: vec![Value(5)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(5)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func.blocks.insert(
        else_block,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Iconst {
                        ty: Type::I64,
                        imm: 0,
                    },
                    args: vec![],
                    results: vec![Value(6)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(6)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn build_v4i32_mask_scalar_select_lir(name: &str) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![Type::I64, Type::I64],
            returns: vec![Type::I64],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(0)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(1)],
                    results: vec![Value(3)],
                },
                Instruction {
                    opcode: Opcode::Icmp {
                        cond: trust_cg_lower::instructions::IntCC::Equal,
                    },
                    args: vec![Value(2), Value(3)],
                    results: vec![Value(4)],
                },
                Instruction {
                    opcode: Opcode::Iconst {
                        ty: Type::I64,
                        imm: 7,
                    },
                    args: vec![],
                    results: vec![Value(5)],
                },
                Instruction {
                    opcode: Opcode::Iconst {
                        ty: Type::I64,
                        imm: 9,
                    },
                    args: vec![],
                    results: vec![Value(6)],
                },
                Instruction {
                    opcode: Opcode::Select {
                        cond: trust_cg_lower::instructions::IntCC::NotEqual,
                    },
                    args: vec![Value(4), Value(5), Value(6)],
                    results: vec![Value(7)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(7)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn build_raw_v2i64_mask_extract_lir(name: &str) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![Type::I64],
            returns: vec![Type::I32],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(0)],
                    results: vec![Value(1)],
                },
                Instruction {
                    opcode: Opcode::V2I64MaskExtract {
                        result_ty: Type::I32,
                    },
                    args: vec![Value(1)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(2)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn build_v2i64_const_store_lir(name: &str, lanes: [i128; 2]) -> LirFunction {
    let v2i64 = v2i64_ty();
    let mut module = TrustIrModule::new(format!("{name}_module"));
    add_trust_ir_function(
        &mut module,
        9201,
        name,
        func_ty(vec![TrustIrTy::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: v2i64.clone(),
                    value: Constant::Vector(
                        lanes.into_iter().map(Constant::Int).collect::<Vec<_>>(),
                    ),
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Store {
                    ty: v2i64,
                    ptr: v(0),
                    value: v(10),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    let mut translated = trust_cg_lower::translate_module(&module)
        .expect("feature-test const module must translate");
    assert_eq!(translated.len(), 1);
    translated.pop().expect("translated function").0
}

fn build_v4i32_pack_store_lir(name: &str) -> LirFunction {
    let v4i32 = v4i32_ty();
    let mut module = TrustIrModule::new(format!("{name}_module"));
    add_trust_ir_function(
        &mut module,
        9203,
        name,
        func_ty(
            vec![
                TrustIrTy::Ptr,
                TrustIrTy::I32,
                TrustIrTy::I32,
                TrustIrTy::I32,
                TrustIrTy::I32,
            ],
            vec![],
        ),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), TrustIrTy::Ptr),
                (v(1), TrustIrTy::I32),
                (v(2), TrustIrTy::I32),
                (v(3), TrustIrTy::I32),
                (v(4), TrustIrTy::I32),
            ],
            body: vec![
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::pack_lanes(v4i32.clone(), [v(1), v(2), v(3), v(4)]),
                )))
                .with_result(v(10)),
                InstrNode::new(Inst::Store {
                    ty: v4i32,
                    ptr: v(0),
                    value: v(10),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    let mut translated =
        trust_cg_lower::translate_module(&module).expect("feature-test pack module must translate");
    assert_eq!(translated.len(), 1);
    translated.pop().expect("translated function").0
}

fn build_v4i32_zero_insert_store_lir(name: &str, lane: i128) -> LirFunction {
    let v4i32 = v4i32_ty();
    let mut module = TrustIrModule::new(format!("{name}_module"));
    add_trust_ir_function(
        &mut module,
        9204,
        name,
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::I32], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr), (v(1), TrustIrTy::I32)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: TrustIrTy::I64,
                    value: Constant::Int(lane),
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Const {
                    ty: v4i32.clone(),
                    value: v4i32_const([0, 0, 0, 0]),
                })
                .with_result(v(11)),
                InstrNode::new(Inst::InsertElement {
                    ty: v4i32.clone(),
                    array: v(11),
                    index: v(10),
                    value: v(1),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Store {
                    ty: v4i32,
                    ptr: v(0),
                    value: v(12),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    let mut translated = trust_cg_lower::translate_module(&module)
        .expect("feature-test zero v4i32 insert module must translate");
    assert_eq!(translated.len(), 1);
    translated.pop().expect("translated function").0
}

fn build_v2i64_zero_insert_store_lir(name: &str) -> LirFunction {
    let v2i64 = v2i64_ty();
    let mut module = TrustIrModule::new(format!("{name}_module"));
    add_trust_ir_function(
        &mut module,
        9205,
        name,
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::I64], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr), (v(1), TrustIrTy::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: TrustIrTy::I64,
                    value: Constant::Int(1),
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Const {
                    ty: v2i64.clone(),
                    value: Constant::Vector(vec![Constant::Int(0), Constant::Int(0)]),
                })
                .with_result(v(11)),
                InstrNode::new(Inst::InsertElement {
                    ty: v2i64.clone(),
                    array: v(11),
                    index: v(10),
                    value: v(1),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Store {
                    ty: v2i64,
                    ptr: v(0),
                    value: v(12),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    let mut translated = trust_cg_lower::translate_module(&module)
        .expect("feature-test zero v2i64 insert module must translate");
    assert_eq!(translated.len(), 1);
    translated.pop().expect("translated function").0
}

fn build_v2i64_nonzero_insert_store_lir(name: &str, lane: u8) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![Type::I64, Type::I64, Type::I64],
            returns: vec![],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(1)],
                    results: vec![Value(3)],
                },
                Instruction {
                    opcode: Opcode::V2I64InsertLane { lane },
                    args: vec![Value(3), Value(2)],
                    results: vec![Value(4)],
                },
                Instruction {
                    opcode: Opcode::Store {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(4), Value(0)],
                    results: vec![],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn build_v4i32_nonzero_insert_store_lir(name: &str, lane: u8) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![Type::I64, Type::I64, Type::I32],
            returns: vec![],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(1)],
                    results: vec![Value(3)],
                },
                Instruction {
                    opcode: Opcode::V4I32InsertLane { lane },
                    args: vec![Value(3), Value(2)],
                    results: vec![Value(4)],
                },
                Instruction {
                    opcode: Opcode::Store {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(4), Value(0)],
                    results: vec![],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn build_v4i32_lane_shift_lir(name: &str, opcode: Opcode) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![Type::I64, Type::I64, Type::I64],
            returns: vec![],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(0)],
                    results: vec![Value(3)],
                },
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(1)],
                    results: vec![Value(4)],
                },
                Instruction {
                    opcode,
                    args: vec![Value(3), Value(4)],
                    results: vec![Value(5)],
                },
                Instruction {
                    opcode: Opcode::Store {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(5), Value(2)],
                    results: vec![],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn build_v4i32_uniform_const_shift_lir(name: &str, op: BinOp, count: i128) -> LirFunction {
    let v4i32 = v4i32_ty();
    let mut module = TrustIrModule::new(format!("{name}_module"));
    add_trust_ir_function(
        &mut module,
        9212,
        name,
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr), (v(1), TrustIrTy::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v4i32.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Const {
                    ty: TrustIrTy::I32,
                    value: Constant::Int(count),
                })
                .with_result(v(11)),
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::pack_lanes(
                        v4i32.clone(),
                        [v(11), v(11), v(11), v(11)],
                    ),
                )))
                .with_result(v(12)),
                InstrNode::new(Inst::BinOp {
                    op,
                    ty: v4i32.clone(),
                    lhs: v(10),
                    rhs: v(12),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Store {
                    ty: v4i32,
                    ptr: v(1),
                    value: v(13),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    let mut translated = trust_cg_lower::translate_module(&module)
        .expect("feature-test uniform v4i32 shift module must translate");
    assert_eq!(translated.len(), 1);
    translated.pop().expect("translated function").0
}

fn build_v2i64_binop_store_lir(name: &str, opcode: Opcode) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![Type::I64, Type::I64, Type::I64],
            returns: vec![],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(0)],
                    results: vec![Value(3)],
                },
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(1)],
                    results: vec![Value(4)],
                },
                Instruction {
                    opcode,
                    args: vec![Value(3), Value(4)],
                    results: vec![Value(5)],
                },
                Instruction {
                    opcode: Opcode::Store {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(5), Value(2)],
                    results: vec![],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

#[test]
fn generic_x86_64_rejects_v2i64_bool_mask_extract_compare_features() {
    let eq_err = generic_raw_pipeline()
        .compile_trust_ir_function(&build_v2i64_bool_mask_extract_lir(
            "generic_v2i64_bool_extract_eq",
            ICmpOp::Eq,
        ))
        .expect_err("generic x86-64 must reject v2i64 eq compare before bool mask extraction");
    assert_unsupported_feature(eq_err, X86Opcode::Pcmpeqq, X86TargetFeature::Sse41);

    let slt_err = generic_raw_pipeline()
        .compile_trust_ir_function(&build_v2i64_bool_mask_extract_lir(
            "generic_v2i64_bool_extract_slt",
            ICmpOp::Slt,
        ))
        .expect_err("generic x86-64 must reject v2i64 slt compare before bool mask extraction");
    assert_unsupported_feature(slt_err, X86Opcode::Pcmpgtq, X86TargetFeature::Sse42);
}

#[test]
fn generic_x86_64_admits_v2i64_unsigned_bool_mask_extract_without_sse4_compare() {
    let (code, evidence) = generic_raw_pipeline()
        .compile_trust_ir_function_with_regalloc_pressure_evidence(
            &build_v2i64_bool_mask_extract_lir("generic_v2i64_bool_extract_ult", ICmpOp::Ult),
        )
        .expect("generic x86-64 should lower unsigned v2i64 compare through SSE2 dword halves");

    assert!(!code.is_empty());
    assert_eq!(
        evidence.machine_code.target_features,
        X86TargetFeatures::generic_x86_64()
    );
    assert_eq!(evidence.machine_code.pcmpgtq_count, 0);
    assert_eq!(evidence.machine_code.pcmpeqq_count, 0);
    assert_eq!(evidence.machine_code.pcmpgtd_count, 1);
    assert_eq!(evidence.machine_code.pcmpeqd_count, 1);
    assert_eq!(evidence.machine_code.pxor_count, 2);
    assert_eq!(evidence.machine_code.pmovmskb_count, 1);
    assert_no_scalar_lane_fallback(&evidence.machine_code, "generic v2i64 unsigned compare");
}

#[test]
fn generic_x86_64_admits_raw_v2i64_mask_extract_without_sse4_compare() {
    let code = generic_raw_pipeline()
        .compile_trust_ir_function(&build_raw_v2i64_mask_extract_lir(
            "generic_raw_v2i64_mask_extract",
        ))
        .expect("raw v2i64 mask extract expands through generic-legal PMOVMSKB");
    assert!(!code.is_empty());
}

#[test]
fn generic_x86_64_admits_v4i32_ne_mask_extract_without_sse4() {
    let code = generic_raw_pipeline()
        .compile_trust_ir_function(&build_v4i32_ne_mask_extract_lir(
            "generic_v4i32_ne_mask_extract",
        ))
        .expect("generic x86-64 should admit SSE2-only v4i32 NotEqual mask extraction");
    assert!(!code.is_empty());
}

#[test]
fn generic_x86_64_admits_v4i32_mask_branch_without_sse4_ptest() {
    let code = generic_raw_pipeline()
        .compile_trust_ir_function(&build_v4i32_mask_branch_lir("generic_v4i32_mask_branch"))
        .expect("generic x86-64 should expand lowered V128 mask branch PTEST self-test");
    assert!(!code.is_empty());
}

#[test]
fn generic_x86_64_admits_v4i32_mask_scalar_select_without_sse4_ptest() {
    let code = generic_raw_pipeline()
        .compile_trust_ir_function(&build_v4i32_mask_scalar_select_lir(
            "generic_v4i32_mask_scalar_select",
        ))
        .expect("generic x86-64 should expand lowered V128 mask select PTEST self-test");
    assert!(!code.is_empty());
}

#[test]
fn generic_x86_64_admits_lane_zero_vector_extracts_without_sse4() {
    let v4_code = generic_raw_pipeline()
        .compile_trust_ir_function(&build_v4i32_extract_lir(
            "generic_v4i32_lane_zero_extract",
            0,
        ))
        .expect("v4i32 lane-zero extract should lower through SSE2 MOVD");
    assert!(!v4_code.is_empty());

    let v2_code = generic_raw_pipeline()
        .compile_trust_ir_function(&build_v2i64_extract_lir(
            "generic_v2i64_lane_zero_extract",
            0,
        ))
        .expect("v2i64 lane-zero extract should lower through SSE2 MOVQ");
    assert!(!v2_code.is_empty());
}

#[test]
fn generic_x86_64_admits_nonzero_vector_extracts_without_sse4() {
    for lane in 1..=3 {
        let code = generic_raw_pipeline()
            .compile_trust_ir_function(&build_v4i32_extract_lir(
                &format!("generic_v4i32_lane_{lane}_extract_sse2"),
                lane,
            ))
            .unwrap_or_else(|err| {
                panic!("v4i32 lane-{lane} extract should lower through SSE2 PSHUFD+MOVD: {err}")
            });
        assert!(!code.is_empty(), "lane {lane}");
    }

    let v2_code = generic_raw_pipeline()
        .compile_trust_ir_function(&build_v2i64_extract_lir(
            "generic_v2i64_lane_one_extract_sse2",
            1,
        ))
        .expect("v2i64 lane-one extract should lower through SSE2 PSHUFD+MOVQ");
    assert!(!v2_code.is_empty());
}

#[test]
fn generic_x86_64_admits_v2i64_repeated_constants_without_sse4() {
    for (name, lanes) in [
        ("generic_v2i64_all_ones_const", [-1, -1]),
        ("generic_v2i64_repeated_42_const", [42, 42]),
        (
            "generic_v2i64_repeated_min_const",
            [i64::MIN as i128, i64::MIN as i128],
        ),
    ] {
        let code = generic_raw_pipeline()
            .compile_trust_ir_function(&build_v2i64_const_store_lir(name, lanes))
            .unwrap_or_else(|err| {
                panic!("generic x86-64 should admit SSE2-only repeated const {name}: {err}")
            });
        assert!(!code.is_empty(), "{name}");
    }
}

#[test]
fn generic_x86_64_admits_v4i32_distinct_pack_without_sse4_pinsrd() {
    let code = generic_raw_pipeline()
        .compile_trust_ir_function(&build_v4i32_pack_store_lir(
            "generic_v4i32_distinct_pack_sse2",
        ))
        .expect("generic x86-64 should lower distinct v4i32 packs through SSE2 unpack ops");
    assert!(!code.is_empty());
}

#[test]
fn generic_x86_64_admits_unequal_v2i64_constants_without_sse4_pinsrq() {
    let code = generic_raw_pipeline()
        .compile_trust_ir_function(&build_v2i64_const_store_lir(
            "generic_v2i64_unequal_const_sse2",
            [i64::MIN as i128, 42],
        ))
        .expect("generic x86-64 should lower unequal v2i64 constants through SSE2 unpack ops");
    assert!(!code.is_empty());
}

#[test]
fn generic_x86_64_admits_zero_base_nonzero_vector_inserts_without_sse4() {
    for lane in 1..=3 {
        let code = generic_raw_pipeline()
            .compile_trust_ir_function(&build_v4i32_zero_insert_store_lir(
                &format!("generic_v4i32_zero_lane_{lane}_insert_sse2"),
                lane,
            ))
            .unwrap_or_else(|err| {
                panic!("generic x86-64 should admit zero-base v4i32 lane-{lane} insert: {err}")
            });
        assert!(!code.is_empty(), "v4i32 lane {lane}");
    }

    let code = generic_raw_pipeline()
        .compile_trust_ir_function(&build_v2i64_zero_insert_store_lir(
            "generic_v2i64_zero_lane_one_insert_sse2",
        ))
        .expect("generic x86-64 should admit zero-base v2i64 lane-one insert");
    assert!(!code.is_empty());
}

#[test]
fn generic_x86_64_admits_nonzero_base_v2i64_inserts_without_sse4() {
    for lane in 0..=1 {
        let code = generic_raw_pipeline()
            .compile_trust_ir_function(&build_v2i64_nonzero_insert_store_lir(
                &format!("generic_v2i64_nonzero_lane_{lane}_insert_sse2"),
                lane,
            ))
            .unwrap_or_else(|err| {
                panic!("generic x86-64 should admit nonzero-base v2i64 lane-{lane} insert: {err}")
            });
        assert!(!code.is_empty(), "v2i64 lane {lane}");
    }
}

#[test]
fn generic_x86_64_admits_nonzero_base_v4i32_inserts_without_sse4() {
    for lane in 0..=3 {
        let code = generic_raw_pipeline()
            .compile_trust_ir_function(&build_v4i32_nonzero_insert_store_lir(
                &format!("generic_v4i32_nonzero_lane_{lane}_insert_sse2"),
                lane,
            ))
            .unwrap_or_else(|err| {
                panic!("generic x86-64 should admit nonzero-base v4i32 lane-{lane} insert: {err}")
            });
        assert!(!code.is_empty(), "v4i32 lane {lane}");
    }
}

#[test]
fn generic_x86_64_admits_v4i32_lane_shifts_without_sse4_pinsrd() {
    for (name, opcode) in [
        ("ishl", Opcode::Ishl),
        ("ushr", Opcode::Ushr),
        ("sshr", Opcode::Sshr),
    ] {
        let code = generic_raw_pipeline()
            .compile_trust_ir_function(&build_v4i32_lane_shift_lir(
                &format!("generic_v4i32_lane_shift_{name}_sse2"),
                opcode,
            ))
            .unwrap_or_else(|err| {
                panic!("generic x86-64 should admit v4i32 lane-wise {name} shifts: {err}")
            });
        assert!(!code.is_empty(), "{name}");
        assert!(
            contains_sse2_opcode(&code, 0x62),
            "generic x86-64 v4i32 {name} shift should reassemble dword pairs with PUNPCKLDQ: {code:02x?}"
        );
        assert!(
            contains_sse2_opcode(&code, 0x6C),
            "generic x86-64 v4i32 {name} shift should join dword pairs with PUNPCKLQDQ: {code:02x?}"
        );
        assert!(
            !contains_sse41_0f3a_opcode(&code, 0x22),
            "generic x86-64 v4i32 {name} shift should not require SSE4.1 PINSRD: {code:02x?}"
        );
        assert!(
            !contains_sse41_0f3a_opcode(&code, 0x16),
            "generic x86-64 v4i32 {name} shift should not require SSE4.1 PEXTRD: {code:02x?}"
        );
        assert!(
            code.contains(&0xD3),
            "generic x86-64 v4i32 lane-wise {name} shift should preserve variable-count scalar fallback: {code:02x?}"
        );
        assert!(
            !contains_any_packed_dword_shift_imm(&code),
            "generic x86-64 v4i32 lane-wise {name} shift must not use a uniform packed immediate shift: {code:02x?}"
        );
    }
}

#[test]
fn x86_v4i32_uniform_const_shifts_use_sse2_immediates_across_profiles() {
    let profiles = [
        ("generic", X86TargetFeatures::generic_x86_64()),
        ("current", X86TargetFeatures::current()),
        (
            "current_avx",
            X86TargetFeatures::current()
                .with_feature(X86TargetFeature::Avx)
                .with_feature(X86TargetFeature::Avx2),
        ),
    ];
    let cases = [
        ("ishl", BinOp::Shl, 6),
        ("ushr", BinOp::LShr, 2),
        ("sshr", BinOp::AShr, 4),
    ];

    for (profile_name, features) in profiles {
        for count in [0, 1, 7, 31] {
            for (op_name, op, subopcode) in &cases {
                let func = build_v4i32_uniform_const_shift_lir(
                    &format!("profile_{profile_name}_v4i32_uniform_{op_name}_{count}"),
                    *op,
                    count,
                );
                let (code, evidence) = raw_pipeline_with_features(features)
                    .compile_trust_ir_function_with_regalloc_pressure_evidence(&func)
                    .unwrap_or_else(|err| {
                        panic!(
                            "{profile_name} v4i32 uniform {op_name} {count} should compile: {err}"
                        )
                    });
                eprintln!(
                    "x86 uniform v4i32 shift canary profile={profile_name} op={op_name} count={count}: {:?}",
                    evidence.machine_code
                );
                assert_eq!(evidence.machine_code.target_features, features);
                assert!(
                    contains_packed_dword_shift_imm(&code, *subopcode, count as u8),
                    "{profile_name} v4i32 uniform {op_name} {count} should encode 66 0F 72 /{subopcode} ib: {code:02X?}"
                );
                assert!(
                    !code.contains(&0xD3),
                    "{profile_name} v4i32 uniform {op_name} {count} should not use scalar D3 shifts: {code:02X?}"
                );
                assert_eq!(
                    evidence.machine_code.movd_to_xmm_count, 0,
                    "{profile_name} v4i32 uniform {op_name} {count} should not materialize scalar dword lanes through MOVD: {:?}",
                    evidence.machine_code
                );
                assert_eq!(
                    evidence.machine_code.punpckldq_count, 0,
                    "{profile_name} v4i32 uniform {op_name} {count} should not reassemble dword pairs with PUNPCKLDQ: {:?}",
                    evidence.machine_code
                );
                assert_eq!(
                    evidence.machine_code.punpcklqdq_count, 0,
                    "{profile_name} v4i32 uniform {op_name} {count} should not reassemble qword pairs with PUNPCKLQDQ: {:?}",
                    evidence.machine_code
                );
                assert_no_vex_or_ymm_lowering(
                    &code,
                    &format!("{profile_name} v4i32 uniform {op_name} {count}"),
                );
            }
        }
    }
}

#[test]
fn generic_x86_64_admits_v2i64_add_sub_without_sse4() {
    for (name, opcode, expected_byte, mnemonic) in [
        (
            "generic_v2i64_add_paddq_sse2",
            Opcode::V2I64Add,
            0xD4,
            "PADDQ",
        ),
        (
            "generic_v2i64_sub_psubq_sse2",
            Opcode::V2I64Sub,
            0xFB,
            "PSUBQ",
        ),
    ] {
        let code = generic_raw_pipeline()
            .compile_trust_ir_function(&build_v2i64_binop_store_lir(name, opcode))
            .unwrap_or_else(|err| {
                panic!("generic x86-64 should admit {mnemonic} as an SSE2 v2i64 op: {err}")
            });
        assert!(
            contains_sse2_opcode(&code, expected_byte),
            "generic x86-64 should encode native {mnemonic} bytes, code={code:02X?}"
        );
    }
}

#[test]
fn generic_x86_64_admits_v2i64_mul_without_sse4_or_avx() {
    let code = generic_raw_pipeline()
        .compile_trust_ir_function(&build_v2i64_binop_store_lir(
            "generic_v2i64_mul_scalarized",
            Opcode::V2I64Mul,
        ))
        .unwrap_or_else(|err| {
            panic!("generic x86-64 should admit V2I64Mul through scalar lane multiply: {err}")
        });
    assert!(
        contains_imul_rr_opcode(&code),
        "generic x86-64 V2I64Mul should encode scalar IMUL lanes, code={code:02X?}"
    );
    assert!(
        contains_sse2_opcode(&code, 0x6C),
        "generic x86-64 V2I64Mul should repack with PUNPCKLQDQ, code={code:02X?}"
    );
    assert!(
        !contains_sse2_opcode(&code, 0xF4),
        "generic x86-64 V2I64Mul must not use PMULUDQ as a fake i64 multiply: {code:02X?}"
    );
    assert!(
        !contains_vex_prefix_byte(&code),
        "generic x86-64 V2I64Mul must not require AVX/VEX/YMM encoding: {code:02X?}"
    );
}

#[test]
fn generic_x86_64_admits_narrow_i8_i16_add_sub_mul_without_sse4_or_avx() {
    for (name, opcode, expected_byte, mnemonic) in [
        (
            "generic_v16i8_add_paddb_sse2",
            Opcode::V16I8Add,
            0xFC,
            "PADDB",
        ),
        (
            "generic_v16i8_sub_psubb_sse2",
            Opcode::V16I8Sub,
            0xF8,
            "PSUBB",
        ),
        (
            "generic_v16i8_mul_packuswb_sse2",
            Opcode::V16I8Mul,
            0x67,
            "PACKUSWB",
        ),
        (
            "generic_v8i16_add_paddw_sse2",
            Opcode::V8I16Add,
            0xFD,
            "PADDW",
        ),
        (
            "generic_v8i16_sub_psubw_sse2",
            Opcode::V8I16Sub,
            0xF9,
            "PSUBW",
        ),
    ] {
        let code = generic_raw_pipeline()
            .compile_trust_ir_function(&build_v2i64_binop_store_lir(name, opcode))
            .unwrap_or_else(|err| {
                panic!("generic x86-64 should admit {mnemonic} as an SSE2 narrow vector op: {err}")
            });
        assert!(
            contains_sse2_opcode(&code, expected_byte),
            "generic x86-64 should encode native {mnemonic} bytes, code={code:02X?}"
        );
        assert!(
            !contains_vex_prefix_byte(&code),
            "generic x86-64 {mnemonic} must not require AVX/VEX/YMM encoding: {code:02X?}"
        );
    }
}

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn f(n: u32) -> FuncId {
    FuncId::new(n)
}

fn func_ty(params: Vec<TrustIrTy>, returns: Vec<TrustIrTy>) -> FuncTy {
    FuncTy {
        params,
        returns,
        is_vararg: false,
    }
}

fn add_trust_ir_function(
    module: &mut TrustIrModule,
    func_id: u32,
    name: &str,
    ty: FuncTy,
    blocks: Vec<TrustIrBlock>,
) {
    let entry = blocks.first().expect("test function must have a block").id;
    let func_ty_id: FuncTyId = module.add_func_type(ty);
    let mut func = TrustIrFunction::new(f(func_id), name, func_ty_id, entry);
    func.blocks = blocks;
    module.add_function(func);
}

fn v2i64_ty() -> TrustIrTy {
    TrustIrTy::Vector(Box::new(TrustIrTy::I64), 2)
}

fn v4i32_ty() -> TrustIrTy {
    TrustIrTy::Vector(Box::new(TrustIrTy::I32), 4)
}

fn v16i8_ty() -> TrustIrTy {
    TrustIrTy::Vector(Box::new(TrustIrTy::I8), 16)
}

fn v8i16_ty() -> TrustIrTy {
    TrustIrTy::Vector(Box::new(TrustIrTy::I16), 8)
}

fn v4_bool_ty() -> TrustIrTy {
    TrustIrTy::Vector(Box::new(TrustIrTy::Bool), 4)
}

fn v2_bool_ty() -> TrustIrTy {
    TrustIrTy::Vector(Box::new(TrustIrTy::Bool), 2)
}

fn v16_bool_ty() -> TrustIrTy {
    TrustIrTy::Vector(Box::new(TrustIrTy::Bool), 16)
}

fn v8_bool_ty() -> TrustIrTy {
    TrustIrTy::Vector(Box::new(TrustIrTy::Bool), 8)
}

fn v4i32_const(values: [i128; 4]) -> Constant {
    Constant::Vector(values.into_iter().map(Constant::Int).collect())
}

fn bool_mask_const_from_bits(lanes: usize, true_bits: u32) -> Constant {
    Constant::Vector(
        (0..lanes)
            .map(|lane| Constant::Bool((true_bits & (1_u32 << lane)) != 0))
            .collect(),
    )
}

#[cfg(target_arch = "x86_64")]
fn build_chc_sse4_public_jit_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("x86_feature_chc_sse4_public_jit".to_string());

    let v2i64 = v2i64_ty();
    add_trust_ir_function(
        &mut module,
        9100,
        "feature_chc_v2i64_slt_select",
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr], vec![TrustIrTy::Ptr]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr), (v(1), TrustIrTy::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v2i64.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: v2i64.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Slt,
                    ty: v2i64,
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Select {
                    ty: TrustIrTy::Ptr,
                    cond: v(12),
                    then_val: v(0),
                    else_val: v(1),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Return {
                    values: vec![v(13)],
                }),
            ],
        }],
    );

    let v4i32 = v4i32_ty();
    add_trust_ir_function(
        &mut module,
        9101,
        "feature_chc_v4i32_mul_mask",
        func_ty(vec![], vec![TrustIrTy::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: v4i32.clone(),
                    value: v4i32_const([1, 2, 3, 4]),
                })
                .with_result(v(20)),
                InstrNode::new(Inst::Const {
                    ty: v4i32.clone(),
                    value: v4i32_const([5, 6, 7, 8]),
                })
                .with_result(v(21)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Mul,
                    ty: v4i32.clone(),
                    lhs: v(20),
                    rhs: v(21),
                })
                .with_result(v(22)),
                InstrNode::new(Inst::Const {
                    ty: TrustIrTy::I64,
                    value: Constant::Int(0),
                })
                .with_result(v(23)),
                InstrNode::new(Inst::ExtractElement {
                    ty: TrustIrTy::I32,
                    array: v(22),
                    index: v(23),
                })
                .with_result(v(24)),
                InstrNode::new(Inst::Return {
                    values: vec![v(24)],
                }),
            ],
        }],
    );

    module
}

#[cfg(target_arch = "x86_64")]
fn build_unsupported_vector_shape_public_jit_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("x86_rejects_unsupported_vector_shape".to_string());
    let v4i64 = TrustIrTy::Vector(Box::new(TrustIrTy::I64), 4);
    add_trust_ir_function(
        &mut module,
        9102,
        "unsupported_v4i64_add",
        func_ty(vec![], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: v4i64.clone(),
                    value: Constant::Vector(vec![
                        Constant::Int(1),
                        Constant::Int(2),
                        Constant::Int(3),
                        Constant::Int(4),
                    ]),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Const {
                    ty: v4i64.clone(),
                    value: Constant::Vector(vec![
                        Constant::Int(4),
                        Constant::Int(3),
                        Constant::Int(2),
                        Constant::Int(1),
                    ]),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: v4i64,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    module
}

#[cfg(target_arch = "x86_64")]
#[test]
fn public_x86_jit_rejects_unsupported_vector_shapes_fail_closed() {
    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = OptLevel::O0;
    config.parallel = false;

    let err = Compiler::new(config)
        .compile_module_to_jit(
            &build_unsupported_vector_shape_public_jit_module(),
            &HashMap::new(),
        )
        .expect_err("public x86 JIT pipeline must reject unsupported vector shapes");

    let CompileError::Adapter(trust_cg_lower::AdapterError::UnsupportedType(message)) = err else {
        panic!("expected public x86 adapter rejection for unsupported vector shape, got {err:?}");
    };
    assert!(
        message.contains("unsupported vector shape")
            || message.contains("only 128-bit fixed vectors are lowered today"),
        "unsupported vector diagnostic should name the closed contract, got: {message}"
    );
}

#[cfg(target_arch = "x86_64")]
#[test]
fn default_host_jit_uses_detected_features_for_chc_sse4_helpers() {
    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = OptLevel::O0;
    config.parallel = false;

    let host = X86TargetFeatures::host();
    let result = Compiler::new(config)
        .compile_module_to_jit(&build_chc_sse4_public_jit_module(), &HashMap::new());

    if !host.contains(X86TargetFeature::Sse41) || !host.contains(X86TargetFeature::Sse42) {
        result.expect_err("host JIT must fail closed when CHC SSE4 helpers are unsupported");
        return;
    }

    let result = result.expect("host JIT with detected SSE4 support must admit CHC SSE4 helpers");

    assert_eq!(result.metrics.function_count, 2);
    assert!(result.metrics.code_size_bytes > 0);
    assert!(
        result
            .buffer
            .get_fn_ptr_bound("feature_chc_v2i64_slt_select")
            .is_some()
    );
    assert!(
        result
            .buffer
            .get_fn_ptr_bound("feature_chc_v4i32_mul_mask")
            .is_some()
    );
}

#[cfg(target_arch = "x86_64")]
#[test]
fn public_x86_aot_compiler_uses_current_sse4_feature_profile() {
    let config = CompilerConfig {
        opt_level: OptLevel::O0,
        target: Target::X86_64,
        parallel: false,
        ..CompilerConfig::default()
    };

    let result = Compiler::new(config)
        .compile(&build_chc_sse4_public_jit_module())
        .expect("public x86 AOT compiler should use the current SSE4-capable profile");

    assert_eq!(result.metrics.function_count, 2);
    assert!(result.metrics.code_size_bytes > 0);
    assert!(!result.object_code.is_empty());
}
