#![cfg(all(target_arch = "x86_64", unix))]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{
    Compiler, CompilerConfig, FunctionQualityMetrics, JitCompilationResult,
};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, FuncTyId,
    Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, Ty as TrustIrTy,
    ValueId,
};

const SHIFT_COUNTS: [i128; 7] = [0, 1, 7, 8, 15, 16, 31];

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

fn shift_cases() -> [(&'static str, BinOp, u8); 3] {
    [
        ("shl", BinOp::Shl, 6),
        ("lshr", BinOp::LShr, 2),
        ("ashr", BinOp::AShr, 4),
    ]
}

fn add_v4i32_uniform_const_shift_function(
    module: &mut TrustIrModule,
    func_id: u32,
    name: &str,
    op: BinOp,
    count: i128,
) {
    let v4i32 = v4i32_ty();
    let func_ty_id: FuncTyId =
        module.add_func_type(func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr], vec![]));
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
            InstrNode::new(Inst::Const {
                ty: TrustIrTy::I32,
                value: Constant::Int(count),
            })
            .with_result(v(11)),
            InstrNode::new(Inst::DialectOp(Box::new(
                trust_ir::dialect::vector::pack_lanes(v4i32.clone(), [v(11), v(11), v(11), v(11)]),
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
    }];
    module.add_function(func);
}

fn build_v4i32_uniform_const_shift_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("x86_64_sse2_dword_shifts");
    let mut func_id = 112_600;

    for (suffix, op, _) in shift_cases() {
        for count in SHIFT_COUNTS {
            let name = format!("v4i32_{suffix}_imm_{count}");
            add_v4i32_uniform_const_shift_function(&mut module, func_id, &name, op.clone(), count);
            func_id += 1;
        }
    }

    module
}

fn host_jit_o0_compiler() -> Compiler {
    // JIT-5: SSE2 packed dword-shift opcodes are not yet cert-covered, so under
    // the new x86 default (CachedVerified) this codegen test would correctly
    // fail closed. It exercises raw SSE2 encoding, so it opts into the dev-only
    // Unchecked mode explicitly.
    let mut config = CompilerConfig::for_host_jit_unchecked();
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

fn jit_symbol_code_bytes<'a>(result: &'a JitCompilationResult, name: &str) -> &'a [u8] {
    let metrics = metrics_for(result, name);
    let ptr = result
        .buffer
        .get_fn_ptr_bound(name)
        .unwrap_or_else(|| panic!("{name} symbol must be present"))
        .as_ptr();
    unsafe { core::slice::from_raw_parts(ptr, metrics.code_size_bytes) }
}

fn assert_metrics_code_size_matches_replay(result: &JitCompilationResult, name: &str) {
    let metrics = metrics_for(result, name);
    let replay = result.buffer.replay_report_metadata();
    let symbol = replay
        .symbols
        .iter()
        .find(|symbol| symbol.name == name)
        .unwrap_or_else(|| panic!("{name} replay symbol should be present"));
    let symbol_size = usize::try_from(symbol.range.end_offset - symbol.range.start_offset)
        .expect("symbol range should fit usize");

    assert!(
        metrics.code_size_bytes > 0,
        "{name} should expose nonzero per-symbol code bytes"
    );
    assert_eq!(
        metrics.code_size_bytes, symbol_size,
        "{name} code_size_bytes should match replay symbol range"
    );
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

fn is_legacy_pmovmskb_modrm_byte(code: &[u8], idx: usize) -> bool {
    if idx < 3 || code.get(idx - 1) != Some(&0xD7) || code.get(idx - 2) != Some(&0x0F) {
        return false;
    }
    code.get(idx - 3) == Some(&0x66)
        || (idx >= 4 && (0x40..=0x4F).contains(&code[idx - 3]) && code.get(idx - 4) == Some(&0x66))
}

fn contains_vex_instruction_prefix(code: &[u8]) -> bool {
    code.iter().enumerate().any(|(idx, byte)| match byte {
        0xC4 if !is_legacy_pmovmskb_modrm_byte(code, idx) => {
            let Some(vex_m) = code.get(idx + 1) else {
                return false;
            };
            matches!(vex_m & 0x1F, 0x01..=0x03) && code.get(idx + 3).is_some()
        }
        0xC5 if !is_legacy_pmovmskb_modrm_byte(code, idx) => code.get(idx + 2).is_some(),
        _ => false,
    })
}

fn contains_scalar_shift_group_instruction(code: &[u8]) -> bool {
    code.windows(2).any(|w| {
        matches!(w[0], 0xC1 | 0xD1 | 0xD3)
            && (w[1] & 0xC0) == 0xC0
            && matches!((w[1] >> 3) & 0x07, 4 | 5 | 7)
    })
}

fn assert_no_scalar_or_lane_rebuild(code: &[u8], metrics: &FunctionQualityMetrics, name: &str) {
    assert!(
        !contains_scalar_shift_group_instruction(code),
        "{name}: should not use scalar shift encodings: {code:02X?}"
    );
    assert!(
        !contains_sse2_opcode(code, 0x6E),
        "{name}: should not materialize lanes with MOVD-to-XMM: {code:02X?}"
    );
    assert!(
        !contains_sse2_opcode(code, 0x7E),
        "{name}: should not scalarize lanes with MOVD-from-XMM: {code:02X?}"
    );
    assert!(
        !contains_sse2_opcode(code, 0x62),
        "{name}: should not rebuild lanes with PUNPCKLDQ: {code:02X?}"
    );
    assert!(
        !contains_sse2_opcode(code, 0x6C),
        "{name}: should not rebuild lanes with PUNPCKLQDQ: {code:02X?}"
    );
    assert!(
        !contains_sse41_0f3a_opcode(code, 0x22),
        "{name}: should not rebuild lanes with PINSRD: {code:02X?}"
    );
    assert!(
        !contains_sse41_0f3a_opcode(code, 0x16),
        "{name}: should not extract lanes with PEXTRD: {code:02X?}"
    );
    assert!(
        !contains_vex_instruction_prefix(code),
        "{name}: should stay on legacy SSE2/XMM encodings without VEX/YMM lowering: {code:02X?}"
    );

    assert_eq!(
        metrics.x86_machine_code.movd_to_xmm_count, 0,
        "{name}: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.punpckldq_count, 0,
        "{name}: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.punpcklqdq_count, 0,
        "{name}: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.pinsrd_count, 0,
        "{name}: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.pextrd_count, 0,
        "{name}: {:?}",
        metrics.x86_machine_code
    );
}

fn expected_shift_lane(op: &str, value: i32, count: i128) -> i32 {
    let count = u32::try_from(count).expect("test count should fit u32");
    match op {
        "shl" => value.wrapping_shl(count),
        "lshr" => ((value as u32) >> count) as i32,
        "ashr" => value >> count,
        other => panic!("unexpected shift op {other}"),
    }
}

#[test]
fn x86_v4i32_immediate_dword_shifts_use_sse2_host_jit() {
    let module = build_v4i32_uniform_const_shift_module();
    let result = host_jit_o0_compiler()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("x86-64 host JIT should compile packed dword shift canaries");
    let lhs = [1i32, -1, i32::MIN, 0x4000_0001];

    for (suffix, _, subopcode) in shift_cases() {
        for count in SHIFT_COUNTS {
            let name = format!("v4i32_{suffix}_imm_{count}");
            assert_metrics_code_size_matches_replay(&result, &name);
            let metrics = metrics_for(&result, &name);
            let code = jit_symbol_code_bytes(&result, &name);

            assert!(
                contains_packed_dword_shift_imm(code, subopcode, count as u8),
                "{name}: should encode 66 0F 72 /{subopcode} {count:#04x}: {code:02X?}"
            );
            assert_no_scalar_or_lane_rebuild(code, metrics, &name);

            let run: extern "C" fn(*const i32, *mut i32) = unsafe {
                result
                    .buffer
                    .get_fn_bound(&name)
                    .unwrap_or_else(|| panic!("{name} symbol must be present"))
                    .into_inner()
            };
            let mut output = [0i32; 4];
            run(lhs.as_ptr(), output.as_mut_ptr());

            let expected =
                core::array::from_fn(|lane| expected_shift_lane(suffix, lhs[lane], count));
            assert_eq!(
                output, expected,
                "{name}: should shift every i32 lane by immediate count {count}"
            );
        }
    }
}
