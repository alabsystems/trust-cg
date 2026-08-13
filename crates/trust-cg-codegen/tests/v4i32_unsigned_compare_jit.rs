#![cfg(all(target_arch = "x86_64", unix))]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{
    Compiler, CompilerConfig, FunctionQualityMetrics, JitCompilationResult,
};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::x86_64::{
    X86OutputFormat, X86Pipeline, X86PipelineConfig, X86TargetFeature, X86TargetFeatures,
};
use trust_cg_lower::function::Function as LirFunction;
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, FuncTyId,
    Function as TrustIrFunction, ICmpOp, Inst, InstrNode, Module as TrustIrModule, Ty as TrustIrTy,
    ValueId,
};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn f(n: u32) -> FuncId {
    FuncId::new(n)
}

fn v4i32_ty() -> TrustIrTy {
    TrustIrTy::Vector(Box::new(TrustIrTy::I32), 4)
}

fn func_ty(params: Vec<TrustIrTy>, returns: Vec<TrustIrTy>) -> FuncTy {
    FuncTy {
        params,
        returns,
        is_vararg: false,
    }
}

fn v4i32_mask_const(value: i128) -> Constant {
    Constant::Vector(vec![
        Constant::Int(value),
        Constant::Int(value),
        Constant::Int(value),
        Constant::Int(value),
    ])
}

fn add_unsigned_cmp_mask_extract_function(
    module: &mut TrustIrModule,
    func_id: u32,
    name: &str,
    op: ICmpOp,
) {
    let v4i32 = v4i32_ty();
    let ty = func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr], vec![TrustIrTy::I32]);
    let func_ty_id: FuncTyId = module.add_func_type(ty);
    let mut func = TrustIrFunction::new(f(func_id), name, func_ty_id, b(0));
    func.blocks = vec![TrustIrBlock {
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
                op,
                ty: v4i32.clone(),
                lhs: v(10),
                rhs: v(11),
            })
            .with_result(v(12)),
            InstrNode::new(Inst::Const {
                ty: v4i32.clone(),
                value: v4i32_mask_const(-1),
            })
            .with_result(v(13)),
            InstrNode::new(Inst::Const {
                ty: v4i32.clone(),
                value: v4i32_mask_const(0),
            })
            .with_result(v(14)),
            InstrNode::new(Inst::Select {
                ty: v4i32,
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
    }];
    module.add_function(func);
}

fn unsigned_cmp_cases() -> [(&'static str, ICmpOp); 4] {
    [
        ("ult", ICmpOp::Ult),
        ("ule", ICmpOp::Ule),
        ("ugt", ICmpOp::Ugt),
        ("uge", ICmpOp::Uge),
    ]
}

fn build_unsigned_cmp_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("v4i32_unsigned_cmp_mask_extract_module");
    for (idx, (suffix, op)) in unsigned_cmp_cases().into_iter().enumerate() {
        add_unsigned_cmp_mask_extract_function(
            &mut module,
            9400 + idx as u32,
            &format!("v4i32_unsigned_{suffix}_mask_bits"),
            op,
        );
    }
    module
}

fn build_single_unsigned_cmp_module(name: &str, op: ICmpOp) -> TrustIrModule {
    let mut module = TrustIrModule::new(format!("{name}_module"));
    add_unsigned_cmp_mask_extract_function(&mut module, 9410, name, op);
    module
}

fn host_jit_o0_compiler() -> Compiler {
    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = OptLevel::O0;
    Compiler::new(config)
}

fn metrics_for<'a>(result: &'a JitCompilationResult, name: &str) -> &'a FunctionQualityMetrics {
    result
        .per_function_metrics
        .iter()
        .find(|metrics| metrics.name == name)
        .unwrap_or_else(|| panic!("{name} per-function metrics should be present"))
}

fn single_translated_lir_function(module: &TrustIrModule) -> LirFunction {
    let mut translated =
        trust_cg_lower::translate_module(module).expect("test module must translate to LIR");
    assert_eq!(
        translated.len(),
        1,
        "test module should contain one function"
    );
    translated.pop().expect("translated function").0
}

fn raw_pipeline_with_features(target_features: X86TargetFeatures) -> X86Pipeline {
    X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O0,
        emit_frame: true,
        output_format: X86OutputFormat::RawBytes,
        target_features,
        ..X86PipelineConfig::generic_x86_64()
    })
}

fn compile_lir_raw_with_features(func: &LirFunction, features: X86TargetFeatures) -> Vec<u8> {
    raw_pipeline_with_features(features)
        .compile_trust_ir_function(func)
        .expect("unsigned v4i32 compare canary should compile")
}

fn is_expected_legacy_sse_modrm_byte(code: &[u8], idx: usize) -> bool {
    fn is_expected_sse_opcode(byte: u8) -> bool {
        matches!(byte, 0x66 | 0x6E | 0x6F | 0x70 | 0x76 | 0xD7 | 0xEB | 0xEF)
    }

    if idx >= 3
        && code.get(idx - 2) == Some(&0x0F)
        && code.get(idx - 3) == Some(&0x66)
        && code
            .get(idx - 1)
            .copied()
            .is_some_and(is_expected_sse_opcode)
    {
        return true;
    }

    idx >= 4
        && code.get(idx - 2) == Some(&0x0F)
        && (0x40..=0x4F).contains(&code[idx - 3])
        && code.get(idx - 4) == Some(&0x66)
        && code
            .get(idx - 1)
            .copied()
            .is_some_and(is_expected_sse_opcode)
}

fn contains_vex_prefix_byte(code: &[u8]) -> bool {
    code.iter().enumerate().any(|(idx, byte)| match byte {
        0xC4 | 0xC5 if is_expected_legacy_sse_modrm_byte(code, idx) => false,
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

fn assert_legacy_unsigned_compare_code_shape(code: &[u8], op: ICmpOp, name: &str) {
    assert!(
        contains_sse2_opcode(code, 0x6E),
        "{name}: expected MOVD sign-bit seed: {code:02X?}"
    );
    assert!(
        contains_sse2_opcode(code, 0x70),
        "{name}: expected PSHUFD sign-bit splat: {code:02X?}"
    );
    assert!(
        contains_sse2_opcode(code, 0xEF),
        "{name}: expected PXOR sign-bit bias: {code:02X?}"
    );
    assert!(
        contains_sse2_opcode(code, 0x66),
        "{name}: expected PCMPGTD signed dword compare: {code:02X?}"
    );
    if matches!(op, ICmpOp::Ule | ICmpOp::Uge) {
        assert!(
            contains_sse2_opcode(code, 0x76),
            "{name}: inclusive unsigned compare should use PCMPEQD: {code:02X?}"
        );
        assert!(
            contains_sse2_opcode(code, 0xEB),
            "{name}: inclusive unsigned compare should OR equality with POR: {code:02X?}"
        );
    }
    assert!(
        !contains_sse41_0f3a_opcode(code, 0x22),
        "{name}: unsigned compare must not use PINSRD: {code:02X?}"
    );
    assert!(
        !contains_sse41_0f3a_opcode(code, 0x16),
        "{name}: unsigned compare must not use PEXTRD: {code:02X?}"
    );
    assert!(
        !contains_vex_prefix_byte(code),
        "{name}: unsigned compare must stay legacy SSE/XMM without VEX/YMM: {code:02X?}"
    );
}

fn unsigned_cmp_matches(op: ICmpOp, lhs: i32, rhs: i32) -> bool {
    let lhs = lhs as u32;
    let rhs = rhs as u32;
    match op {
        ICmpOp::Ult => lhs < rhs,
        ICmpOp::Ule => lhs <= rhs,
        ICmpOp::Ugt => lhs > rhs,
        ICmpOp::Uge => lhs >= rhs,
        other => panic!("unexpected unsigned v4i32 predicate {other:?}"),
    }
}

fn expected_unsigned_lane_bits(op: ICmpOp, lhs: [i32; 4], rhs: [i32; 4]) -> u32 {
    lhs.into_iter()
        .zip(rhs)
        .enumerate()
        .fold(0, |mask, (lane, (lhs, rhs))| {
            if unsigned_cmp_matches(op, lhs, rhs) {
                mask | (1 << lane)
            } else {
                mask
            }
        })
}

#[test]
fn x86_v4i32_unsigned_host_jit_boundary_masks_cover_u32_edges() {
    let module = build_unsigned_cmp_module();
    let result = host_jit_o0_compiler()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("host JIT should compile unsigned v4i32 compare canaries");

    for (suffix, op) in unsigned_cmp_cases() {
        let name = format!("v4i32_unsigned_{suffix}_mask_bits");
        let metrics = metrics_for(&result, &name);
        assert_eq!(
            metrics.x86_machine_code.movd_to_xmm_count, 1,
            "{name}: should seed one sign-bit splat through MOVD"
        );
        assert_eq!(
            metrics.x86_machine_code.pshufd_count, 1,
            "{name}: should splat the sign-bit seed with PSHUFD"
        );
        assert_eq!(
            metrics.x86_machine_code.pxor_count, 2,
            "{name}: should bias both operands with PXOR"
        );
        assert_eq!(
            metrics.x86_machine_code.pcmpgtd_count, 1,
            "{name}: should reuse signed PCMPGTD for unsigned compare"
        );
        assert_eq!(
            metrics.x86_machine_code.pcmpeqd_count,
            usize::from(matches!(op, ICmpOp::Ule | ICmpOp::Uge)),
            "{name}: inclusive predicates should add equality only"
        );
        assert_eq!(
            metrics.x86_machine_code.por_count,
            usize::from(matches!(op, ICmpOp::Ule | ICmpOp::Uge)),
            "{name}: inclusive predicates should merge equality with POR"
        );
        assert_eq!(
            metrics.x86_machine_code.pmovmskb_count, 1,
            "{name}: mask extraction should cross the host/JIT boundary with PMOVMSKB"
        );
        assert_eq!(
            metrics.x86_machine_code.pinsrd_count, 0,
            "{name}: must not rebuild lanes with PINSRD"
        );
        assert_eq!(
            metrics.x86_machine_code.pextrd_count, 0,
            "{name}: must not scalarize lanes with PEXTRD"
        );

        let run: extern "C" fn(*const i32, *const i32) -> u32 = unsafe {
            result
                .buffer
                .get_fn_bound(&name)
                .unwrap_or_else(|| panic!("{name} symbol must be present"))
                .into_inner()
        };

        for (lhs, rhs) in [
            ([0, i32::MAX, i32::MIN, -1], [-1, i32::MIN, i32::MAX, 0]),
            ([0, i32::MAX, i32::MIN, -1], [0, i32::MAX, i32::MIN, -1]),
            ([-1, i32::MIN, i32::MAX, 0], [0, i32::MAX, i32::MIN, -1]),
        ] {
            let actual = run(lhs.as_ptr(), rhs.as_ptr());
            let expected = expected_unsigned_lane_bits(op, lhs, rhs);
            assert_eq!(
                actual, expected,
                "{name} lhs={lhs:?} rhs={rhs:?} should return bitN for laneN"
            );
        }
    }
}

#[test]
fn x86_v4i32_unsigned_compare_avx_feature_bits_are_inert() {
    let generic = X86TargetFeatures::generic_x86_64();
    let avx_avx2 = generic
        .with_feature(X86TargetFeature::Avx)
        .with_feature(X86TargetFeature::Avx2);

    for (suffix, op) in unsigned_cmp_cases() {
        let name = format!("v4i32_unsigned_{suffix}_avx_inert");
        let module = build_single_unsigned_cmp_module(&name, op);
        let lir = single_translated_lir_function(&module);
        let generic_code = compile_lir_raw_with_features(&lir, generic);
        let avx_code = compile_lir_raw_with_features(&lir, avx_avx2);

        assert_eq!(
            avx_code, generic_code,
            "{name}: enabling AVX/AVX2 must not change the legacy SSE2/XMM lowering"
        );
        assert_legacy_unsigned_compare_code_shape(&generic_code, op, &name);
        assert_legacy_unsigned_compare_code_shape(&avx_code, op, &name);
    }
}
