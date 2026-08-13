// trust-cg-codegen/tests/panic_fuzz_compile_x86_64.rs
// Property-based panic-fuzz harness for the x86-64 compile pipeline.
//
// Part of #L14: first production slice toward x86 live-range split replay
// and fuzz proof.
//
// Contract under test: for generated x86-64 ISel functions, `X86Pipeline`
// must either return `Ok(..)` or a typed error. It must not panic while
// compiling integer chains, high GPR pressure that exercises x86 spill replay,
// or FP constant-pool shapes.
//
// Run:
//   cargo test -p trust-cg-codegen --test panic_fuzz_compile_x86_64
// Increase case count via env:
//   PROPTEST_CASES=100000 cargo test -p trust-cg-codegen --test panic_fuzz_compile_x86_64

use std::panic;

#[cfg(target_arch = "x86_64")]
use std::collections::HashMap;

use proptest::prelude::*;
#[cfg(target_arch = "x86_64")]
use trust_cg_codegen::Compiler;
#[cfg(target_arch = "x86_64")]
use trust_cg_codegen::compiler::CompilerConfig;
#[cfg(target_arch = "x86_64")]
use trust_cg_codegen::pipeline::OptLevel as CompilerOptLevel;
use trust_cg_codegen::x86_64::pipeline::X86RegAllocMode;
use trust_cg_codegen::x86_64::{
    X86OutputFormat, X86Pipeline, X86PipelineConfig, X86PipelineError, X86TargetFeature,
    X86TargetFeatures,
};
use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_ir::x86_64_regs;
use trust_cg_lower::function::Signature;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::types::Type;
use trust_cg_lower::x86_64_isel::{
    X86ISelConstPoolEntry, X86ISelFunction, X86ISelInst, X86ISelOperand,
};
use trust_cg_opt::OptLevel as X86OptLevel;
#[cfg(target_arch = "x86_64")]
use trust_ir::Ty;
#[cfg(target_arch = "x86_64")]
use trust_ir_build::ModuleBuilder;

#[derive(Debug, Clone, Copy)]
enum IntOp {
    Add,
    Sub,
    Xor,
    And,
    Or,
}

impl IntOp {
    fn opcode(self) -> X86Opcode {
        match self {
            Self::Add => X86Opcode::AddRR,
            Self::Sub => X86Opcode::SubRR,
            Self::Xor => X86Opcode::XorRR,
            Self::And => X86Opcode::AndRR,
            Self::Or => X86Opcode::OrRR,
        }
    }
}

#[derive(Debug, Clone)]
enum X86Shape {
    IntChain {
        immediates: Vec<i64>,
        ops: Vec<IntOp>,
    },
    SpillPressure {
        live_values: u8,
    },
    FpConstPool {
        f32_bits: u32,
        f64_bits: u64,
        duplicate_f32: bool,
    },
}

fn int_op_strategy() -> impl Strategy<Value = IntOp> {
    prop_oneof![
        Just(IntOp::Add),
        Just(IntOp::Sub),
        Just(IntOp::Xor),
        Just(IntOp::And),
        Just(IntOp::Or),
    ]
}

fn shape_strategy() -> impl Strategy<Value = X86Shape> {
    prop_oneof![
        (
            prop::collection::vec(-4096i64..=4096i64, 0..=16),
            prop::collection::vec(int_op_strategy(), 0..=16),
        )
            .prop_map(|(immediates, ops)| X86Shape::IntChain { immediates, ops }),
        (1u8..=32u8).prop_map(|live_values| X86Shape::SpillPressure { live_values }),
        (any::<u32>(), any::<u64>(), any::<bool>()).prop_map(
            |(f32_bits, f64_bits, duplicate_f32)| X86Shape::FpConstPool {
                f32_bits,
                f64_bits,
                duplicate_f32,
            },
        ),
    ]
}

fn opt_level_strategy() -> impl Strategy<Value = X86OptLevel> {
    prop_oneof![
        Just(X86OptLevel::O0),
        Just(X86OptLevel::O1),
        Just(X86OptLevel::O2),
        Just(X86OptLevel::O3),
    ]
}

fn minimal_func(name: &str, returns: Vec<Type>) -> X86ISelFunction {
    let sig = Signature {
        params: vec![],
        returns,
    };
    let mut func = X86ISelFunction::new(name.to_string(), sig);
    func.ensure_block(Block(0));
    func
}

fn push_vreg_imm(func: &mut X86ISelFunction, next_vreg: &mut u32, value: i64) -> VReg {
    let vreg = VReg::new(*next_vreg, RegClass::Gpr64);
    *next_vreg += 1;
    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![X86ISelOperand::VReg(vreg), X86ISelOperand::Imm(value)],
        ),
    );
    vreg
}

fn build_int_chain(immediates: &[i64], ops: &[IntOp]) -> X86ISelFunction {
    let mut func = minimal_func("panic_fuzz_x86_int_chain", vec![Type::I64]);
    let mut next_vreg = 0;
    let mut acc = push_vreg_imm(&mut func, &mut next_vreg, 0);

    for (idx, imm) in immediates.iter().enumerate() {
        let rhs = push_vreg_imm(&mut func, &mut next_vreg, *imm);
        let dst = VReg::new(next_vreg, RegClass::Gpr64);
        next_vreg += 1;
        let op = ops.get(idx).copied().unwrap_or(IntOp::Add);
        func.push_inst(
            Block(0),
            X86ISelInst::new(
                op.opcode(),
                vec![
                    X86ISelOperand::VReg(dst),
                    X86ISelOperand::VReg(acc),
                    X86ISelOperand::VReg(rhs),
                ],
            ),
        );
        acc = dst;
    }

    func.next_vreg = next_vreg;
    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![
                X86ISelOperand::PReg(x86_64_regs::RAX),
                X86ISelOperand::VReg(acc),
            ],
        ),
    );
    func.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));
    func
}

fn build_spill_pressure(live_values: u8) -> X86ISelFunction {
    let live_values = u32::from(live_values.max(1));
    let mut func = minimal_func("panic_fuzz_x86_spill_pressure", vec![Type::I64]);

    for id in 0..live_values {
        func.push_inst(
            Block(0),
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![
                    X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64)),
                    X86ISelOperand::Imm(i64::from(id) * 17 - 101),
                ],
            ),
        );
    }

    for id in 1..live_values {
        func.push_inst(
            Block(0),
            X86ISelInst::new(
                X86Opcode::AddRR,
                vec![
                    X86ISelOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                    X86ISelOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                    X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64)),
                ],
            ),
        );
    }

    func.next_vreg = live_values;
    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![
                X86ISelOperand::PReg(x86_64_regs::RAX),
                X86ISelOperand::VReg(VReg::new(0, RegClass::Gpr64)),
            ],
        ),
    );
    func.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));
    func
}

fn build_fp_const_pool(f32_bits: u32, f64_bits: u64, duplicate_f32: bool) -> X86ISelFunction {
    let mut func = minimal_func("panic_fuzz_x86_fp_const_pool", vec![Type::F64]);
    let f32_index = func.const_pool_entries.len();
    func.const_pool_entries.push(X86ISelConstPoolEntry {
        data: f32_bits.to_le_bytes().to_vec(),
        align: 4,
    });
    if duplicate_f32 {
        func.const_pool_entries.push(X86ISelConstPoolEntry {
            data: f32_bits.to_le_bytes().to_vec(),
            align: 4,
        });
    }
    let f64_index = func.const_pool_entries.len();
    func.const_pool_entries.push(X86ISelConstPoolEntry {
        data: f64_bits.to_le_bytes().to_vec(),
        align: 8,
    });

    let f32_tmp = VReg::new(0, RegClass::Fpr32);
    let f64_ret = VReg::new(1, RegClass::Fpr64);
    func.next_vreg = 2;
    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::MovssRipRel,
            vec![
                X86ISelOperand::VReg(f32_tmp),
                X86ISelOperand::ConstPoolEntry(f32_index),
            ],
        ),
    );
    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::MovsdRipRel,
            vec![
                X86ISelOperand::VReg(f64_ret),
                X86ISelOperand::ConstPoolEntry(f64_index),
            ],
        ),
    );
    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::MovsdRR,
            vec![
                X86ISelOperand::PReg(x86_64_regs::XMM0),
                X86ISelOperand::VReg(f64_ret),
            ],
        ),
    );
    func.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));
    func
}

fn materialise(shape: &X86Shape) -> X86ISelFunction {
    match shape {
        X86Shape::IntChain { immediates, ops } => build_int_chain(immediates, ops),
        X86Shape::SpillPressure { live_values } => build_spill_pressure(*live_values),
        X86Shape::FpConstPool {
            f32_bits,
            f64_bits,
            duplicate_f32,
        } => build_fp_const_pool(*f32_bits, *f64_bits, *duplicate_f32),
    }
}

fn panic_payload_to_string(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<&'static str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "<non-string panic payload>".to_string()
    }
}

fn assert_x86_pipeline_no_panic(func: X86ISelFunction, opt_level: X86OptLevel) {
    let name = func.name.clone();
    let result = panic::catch_unwind(panic::AssertUnwindSafe(move || {
        let pipeline = X86Pipeline::new(X86PipelineConfig {
            opt_level,
            output_format: X86OutputFormat::RawBytes,
            emit_frame: true,
            ..X86PipelineConfig::default()
        });
        let _ = pipeline.compile_function(&func);
    }));
    if let Err(payload) = result {
        panic!(
            "x86-64 pipeline panicked on function '{name}' at {opt_level:?}: {}",
            panic_payload_to_string(payload.as_ref())
        );
    }
}

#[test]
fn x86_generic_sse4_feature_gate_returns_typed_error_without_panic() {
    let result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        let pipeline = X86Pipeline::new(X86PipelineConfig {
            opt_level: X86OptLevel::O0,
            output_format: X86OutputFormat::RawBytes,
            emit_frame: false,
            regalloc_mode: X86RegAllocMode::Simplified,
            target_features: X86TargetFeatures::generic_x86_64(),
            ..X86PipelineConfig::generic_x86_64()
        });
        let mut func = minimal_func("panic_fuzz_generic_rejects_pcmpgtq", vec![]);
        func.push_inst(
            Block(0),
            X86ISelInst::new(
                X86Opcode::Pcmpgtq,
                vec![
                    X86ISelOperand::PReg(x86_64_regs::XMM0),
                    X86ISelOperand::PReg(x86_64_regs::XMM1),
                ],
            ),
        );

        pipeline
            .compile_function(&func)
            .expect_err("generic x86-64 must reject SSE4.2 PCMPGTQ before emission")
    }));

    let err = result.unwrap_or_else(|payload| {
        panic!(
            "generic x86-64 SSE4 feature gate panicked: {}",
            panic_payload_to_string(payload.as_ref())
        )
    });
    let message = err.to_string();
    assert!(
        message.contains("Pcmpgtq") && message.contains("sse4.2"),
        "diagnostic must include opcode and required feature, got: {message}"
    );
    match err {
        X86PipelineError::UnsupportedTargetFeature { opcode, feature } => {
            assert_eq!(opcode, X86Opcode::Pcmpgtq);
            assert_eq!(feature, X86TargetFeature::Sse42);
        }
        other => panic!("expected unsupported target feature error, got {other:?}"),
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(64),
        max_shrink_iters: 200,
        .. ProptestConfig::default()
    })]

    #[test]
    fn x86_pipeline_compile_never_panics(
        shape in shape_strategy(),
        opt_level in opt_level_strategy(),
    ) {
        assert_x86_pipeline_no_panic(materialise(&shape), opt_level);
    }
}

#[cfg(target_arch = "x86_64")]
fn assert_host_jit_no_panic(module: trust_ir::Module, label: &'static str) {
    let result = panic::catch_unwind(panic::AssertUnwindSafe(move || {
        let mut config = CompilerConfig::for_host_jit();
        config.opt_level = CompilerOptLevel::O0;
        let _ = Compiler::new(config).compile_module_to_jit(&module, &HashMap::new());
    }));
    if let Err(payload) = result {
        panic!(
            "x86-64 host JIT panicked on {label}: {}",
            panic_payload_to_string(payload.as_ref())
        );
    }
}

#[cfg(target_arch = "x86_64")]
#[test]
fn x86_host_jit_spill_pressure_shape_never_panics() {
    let mut mb = ModuleBuilder::new("panic_fuzz_x86_host_jit_spill");
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("jit_spill_pressure", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);

    let mut live = Vec::new();
    for lane in 0..28 {
        live.push(fb.iconst(Ty::I64, i128::from(lane * 13 - 77)));
    }
    let mut acc = fb.iconst(Ty::I64, 0);
    for value in live {
        acc = fb.add(Ty::I64, acc, value);
    }
    fb.ret(vec![acc]);
    fb.build();

    assert_host_jit_no_panic(mb.build(), "spill-pressure");
}

#[cfg(target_arch = "x86_64")]
#[test]
fn x86_host_jit_fp_constant_pool_shape_never_panics() {
    let mut mb = ModuleBuilder::new("panic_fuzz_x86_host_jit_fp");
    let ty = mb.add_func_type(vec![], vec![Ty::F64]);
    let mut fb = mb.function("jit_fp_const_pool", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);

    let mut acc = fb.fconst(Ty::F64, -0.0);
    for i in 0..16 {
        let value = fb.fconst(Ty::F64, f64::from(i) + 0.25);
        acc = fb.fadd(Ty::F64, acc, value);
    }
    fb.ret(vec![acc]);
    fb.build();

    assert_host_jit_no_panic(mb.build(), "fp-constant-pool");
}
