// trust-cg-codegen/tests/e2e_aarch64_f16_fcvt.rs - CG-compiled half-precision FCVT against the hardware instruction
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Native execution control for the four half-precision conversions
//! (X-OPCODES-P7): `f16 -> f32`, `f16 -> f64`, `f32 -> f16`, `f64 -> f16`.
//!
//! Each conversion is compiled by the production `Compiler` for the host
//! triple (the generic Linux GNU profile on Linux, which admits no FEAT_FP16,
//! and the Apple profile on macOS) as `load; fpext|fptrunc; store`, linked with
//! a C driver and run. The driver computes the reference with the hardware
//! `FCVT` instruction itself (inline assembly, independent of any C compiler's
//! `_Float16` support) and records both results; the test then requires, bit
//! for bit including signed zeros and NaN payloads:
//!
//! * CG-compiled result == hardware `FCVT` result, and
//! * hardware result == both sides of the coverage-gate obligation — the IEEE
//!   `convertFormat` intent (`aarch64_fcvt_half::ieee_convert_format`) and the
//!   Arm `FPConvert` transcription of the decoded word (`arm_fpconvert`) — and
//!   the silicon-validated integer bit model (`fp_bitmodel`).
//!
//! Inputs: every binary16 for the widening forms (exhaustive); for the rounded
//! forms, every binary16 value re-expressed in the source format, the exact
//! midpoint (tie) between every pair of neighbouring binary16 values and one
//! source ulp either side of it, the structured boundary battery (overflow
//! and underflow thresholds, source denormals, quiet and signaling NaNs with
//! payload bits kept and dropped) and a fixed pseudo-random sample.
//!
//! This is finite execution on one CPU under the process-default FPCR: a
//! differential control, not a proof. It runs natively on AArch64 macOS and
//! AArch64 Linux GNU; elsewhere only the object-level control compiles.

use std::fs;
use std::path::Path;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_verify::aarch64_fcvt_half::{
    HalfConversion, arm_fpconvert, half_conversion_battery, ieee_convert_format,
};
use trust_cg_verify::fp_bitmodel;
use trust_cg_verify::smt::{EvalEnv, EvalResult, SmtExpr};
use trust_ir::{
    Block, BlockId, CastOp, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};

#[path = "common/native_host.rs"]
mod native_host;

/// (conversion, CG symbol, source type, destination type, cast).
const CONVERSIONS: [(HalfConversion, &str); 4] = [
    (HalfConversion::HalfToSingle, "cg_fcvt_h_to_s"),
    (HalfConversion::HalfToDouble, "cg_fcvt_h_to_d"),
    (HalfConversion::SingleToHalf, "cg_fcvt_s_to_h"),
    (HalfConversion::DoubleToHalf, "cg_fcvt_d_to_h"),
];

fn ty(bits: u32) -> Ty {
    match bits {
        16 => Ty::F16,
        32 => Ty::F32,
        _ => Ty::F64,
    }
}

/// `fn name(src: *const S, dst: *mut D) { *dst = cast(*src) }`.
fn build_module() -> Module {
    let mut module = Module::new("f16_fcvt");
    for (index, (conv, name)) in CONVERSIONS.iter().enumerate() {
        let (src, dst) = (ty(conv.source().bits()), ty(conv.destination().bits()));
        let signature = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::Ptr],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function =
            Function::new(FuncId::new(index as u32), *name, signature, BlockId::new(0));
        function.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::Ptr), (ValueId::new(1), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: src.clone(),
                    ptr: ValueId::new(0),
                    volatile: false,
                    align: Some(u64::from(conv.source().bits() / 8)),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::Cast {
                    op: if conv.widens() {
                        CastOp::FPExt
                    } else {
                        CastOp::FPTrunc
                    },
                    src_ty: src,
                    dst_ty: dst.clone(),
                    operand: ValueId::new(2),
                })
                .with_result(ValueId::new(3)),
                InstrNode::new(Inst::Store {
                    ty: dst,
                    ptr: ValueId::new(1),
                    value: ValueId::new(3),
                    volatile: false,
                    align: Some(u64::from(conv.destination().bits() / 8)),
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }];
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
    }
    module
}

fn compile(triple: &str, opt_level: OptLevel) -> Vec<u8> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&build_module())
    .unwrap_or_else(|error| panic!("{triple} {opt_level:?}: {error}"))
    .object_code
}

/// `FCVT <dst>, <src>` word pattern (register fields masked).
fn is_fcvt(word: u32, conv: HalfConversion) -> bool {
    let code = |bits: u32| match bits {
        32 => 0b00,
        64 => 0b01,
        _ => 0b11,
    };
    let (ftype, opc) = (code(conv.source().bits()), code(conv.destination().bits()));
    word & 0xFFFF_FC00 == 0x1E22_4000 | (ftype << 22) | (opc << 15)
}

/// The generic Linux GNU profile admits no FEAT_FP16, yet all four
/// conversions compile: FCVT between H and S/D is base floating point. Each
/// object carries the exact FCVT form of each conversion (ENC-5 accepted
/// every emitted word, including the decoded-word FCVT obligation). Runs on
/// every host.
#[test]
fn generic_linux_object_carries_each_fcvt_form_without_fp16() {
    for opt in [OptLevel::O0, OptLevel::O2] {
        let object = compile("aarch64-unknown-linux-gnu", opt);
        native_host::assert_elf_aarch64_object(&object);
        let words = native_host::text_words(&object);
        for (conv, name) in CONVERSIONS {
            let count = words.iter().filter(|&&word| is_fcvt(word, conv)).count();
            assert_eq!(count, 1, "{opt:?} {name}: FCVT {conv:?} words in .text");
        }
    }
}

/// Source inputs for `conv`.
fn inputs(conv: HalfConversion) -> Vec<u64> {
    if conv.widens() {
        return (0..=u16::MAX).map(u64::from).collect();
    }
    let widen = |h: u64| match conv {
        HalfConversion::SingleToHalf => fp_bitmodel::fcvt_h_to_s(h),
        _ => fp_bitmodel::fcvt_h_to_d(h),
    };
    let sign = 1u64 << (conv.source().bits() - 1);
    let mut out = half_conversion_battery(conv);
    for h in 0..0x7C00u64 {
        let exact = widen(h);
        let next = widen(h + 1);
        // Between two same-signed values the bit patterns are monotone and
        // their average is the value midpoint (see half_conversion_battery).
        let mid = if h == 0x7BFF {
            exact + ((widen(0x7BFF) - widen(0x7BFE)) / 2)
        } else {
            (exact + next) / 2
        };
        for value in [exact, mid, mid - 1, mid + 1] {
            out.push(value);
            out.push(value | sign);
        }
    }
    let mut state = 0x5EED_F16Cu64;
    for _ in 0..50_000 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        out.push(if conv.source().bits() == 32 {
            state & 0xFFFF_FFFF
        } else {
            state
        });
    }
    out.sort_unstable();
    out.dedup();
    out
}

const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern void cg_fcvt_h_to_s(const uint16_t *, uint32_t *);
extern void cg_fcvt_h_to_d(const uint16_t *, uint64_t *);
extern void cg_fcvt_s_to_h(const uint32_t *, uint16_t *);
extern void cg_fcvt_d_to_h(const uint64_t *, uint16_t *);

/* The hardware reference: the FCVT instruction itself. The source bits
   travel in a D register; %h/%s/%d name its views. A scalar FP write zeroes
   the rest of the vector register, so the D view of the result is the
   zero-extended destination. */
static uint64_t hw(int kind, uint64_t x) {
    double in, out;
    uint64_t r;
    memcpy(&in, &x, 8);
    switch (kind) {
    case 0: __asm__ volatile("fcvt %s0, %h1" : "=w"(out) : "w"(in)); break;
    case 1: __asm__ volatile("fcvt %d0, %h1" : "=w"(out) : "w"(in)); break;
    case 2: __asm__ volatile("fcvt %h0, %s1" : "=w"(out) : "w"(in)); break;
    default: __asm__ volatile("fcvt %h0, %d1" : "=w"(out) : "w"(in)); break;
    }
    memcpy(&r, &out, 8);
    return r;
}

static uint64_t cg(int kind, uint64_t x) {
    switch (kind) {
    case 0: { uint16_t s = (uint16_t)x; uint32_t d = 0xA5A5A5A5u; cg_fcvt_h_to_s(&s, &d); return d; }
    case 1: { uint16_t s = (uint16_t)x; uint64_t d = 0xA5A5A5A5A5A5A5A5ull; cg_fcvt_h_to_d(&s, &d); return d; }
    case 2: { uint32_t s = (uint32_t)x; uint16_t d = 0xA5A5; cg_fcvt_s_to_h(&s, &d); return d; }
    default: { uint64_t s = x; uint16_t d = 0xA5A5; cg_fcvt_d_to_h(&s, &d); return d; }
    }
}

int main(int argc, char **argv) {
    if (argc != 4) return 90;
    int kind = atoi(argv[1]);
    FILE *in = fopen(argv[2], "rb");
    FILE *out = fopen(argv[3], "wb");
    if (!in || !out) return 91;
    uint64_t x;
    unsigned long n = 0;
    while (fread(&x, 8, 1, in) == 1) {
        uint64_t pair[2] = { cg(kind, x), hw(kind, x) };
        if (fwrite(pair, 8, 2, out) != 2) return 92;
        n++;
    }
    fclose(in);
    fclose(out);
    printf("%lu\n", n);
    return 0;
}
"#;

#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
fn link(dir: &Path, object: &[u8]) -> std::path::PathBuf {
    let object_path = dir.join("fcvt.o");
    let driver_path = dir.join("driver.c");
    let exe = dir.join("fcvt_driver");
    fs::write(&object_path, object).unwrap();
    fs::write(&driver_path, DRIVER).unwrap();
    let output = Command::new(native_host::C_COMPILER)
        .arg("-O0")
        .arg(&driver_path)
        .arg(&object_path)
        .args(native_host::link_hardening_args())
        .arg("-o")
        .arg(&exe)
        .output()
        .expect("run the host C compiler");
    assert!(
        output.status.success(),
        "link failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    exe
}

#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
fn evaluate(expr: &SmtExpr, x: u64) -> u64 {
    let mut env = EvalEnv::default();
    env.insert("x".to_string(), x);
    match expr.try_eval(&env).expect("intent evaluates") {
        EvalResult::Bv(bits) => bits,
        other => panic!("unexpected {other:?}"),
    }
}

#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
fn bitmodel(conv: HalfConversion, x: u64) -> u64 {
    match conv {
        HalfConversion::HalfToSingle => fp_bitmodel::fcvt_h_to_s(x),
        HalfConversion::HalfToDouble => fp_bitmodel::fcvt_h_to_d(x),
        HalfConversion::SingleToHalf => fp_bitmodel::fcvt_s_to_h(x),
        HalfConversion::DoubleToHalf => fp_bitmodel::fcvt_d_to_h(x),
    }
}

/// CG-compiled conversions agree with the hardware FCVT instruction, and the
/// hardware agrees with the obligation's IEEE intent and the bit model, on
/// every input of [`inputs`], at O0 and O2.
#[cfg_attr(
    any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    ),
    test
)]
#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
fn cg_compiled_fcvt_matches_the_hardware_instruction_bit_for_bit() {
    let dir = std::env::temp_dir().join(format!("trust_cg_f16_fcvt_{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let mut compared = 0usize;
    let mut ties = 0usize;
    let mut nan_payloads = 0usize;
    for opt in [OptLevel::O0, OptLevel::O2] {
        let exe = link(&dir, &compile(native_host::TRIPLE, opt));
        for (kind, (conv, name)) in CONVERSIONS.iter().enumerate() {
            let values = inputs(*conv);
            let input_path = dir.join(format!("{name}.in"));
            let output_path = dir.join(format!("{name}.out"));
            let bytes: Vec<u8> = values.iter().flat_map(|x| x.to_le_bytes()).collect();
            fs::write(&input_path, bytes).unwrap();
            let run = Command::new(&exe)
                .arg(kind.to_string())
                .arg(&input_path)
                .arg(&output_path)
                .output()
                .expect("run the driver");
            assert!(
                run.status.success(),
                "{name} {opt:?}: driver {:?}",
                run.status
            );
            let results = fs::read(&output_path).unwrap();
            assert_eq!(results.len(), values.len() * 16, "{name} {opt:?}");
            let var = SmtExpr::var("x", conv.source().bits());
            let intent = ieee_convert_format(*conv, &var);
            let machine = arm_fpconvert(*conv, &var);
            let dst_mask = if conv.destination().bits() == 64 {
                u64::MAX
            } else {
                (1u64 << conv.destination().bits()) - 1
            };
            for (index, &x) in values.iter().enumerate() {
                let pair = &results[index * 16..][..16];
                let cg = u64::from_le_bytes(pair[..8].try_into().unwrap());
                let hw = u64::from_le_bytes(pair[8..].try_into().unwrap());
                assert_eq!(
                    hw & !dst_mask,
                    0,
                    "{name}: the hardware scalar write left upper bits for {x:#x}"
                );
                assert_eq!(
                    cg, hw,
                    "{name} {opt:?}: CG-compiled {cg:#x} vs hardware FCVT {hw:#x} for {x:#x}"
                );
                if opt == OptLevel::O0 {
                    assert_eq!(
                        evaluate(&intent, x),
                        hw,
                        "{name}: IEEE intent vs hardware FCVT for {x:#x}"
                    );
                    assert_eq!(
                        evaluate(&machine, x),
                        hw,
                        "{name}: Arm FPConvert transcription vs hardware FCVT for {x:#x}"
                    );
                    assert_eq!(bitmodel(*conv, x), hw, "{name}: bit model for {x:#x}");
                    let src = conv.source();
                    let frac = x & ((1u64 << src.frac_bits()) - 1);
                    let exp = (x >> src.frac_bits()) & ((1u64 << src.exp_bits()) - 1);
                    if exp == (1u64 << src.exp_bits()) - 1 && frac != 0 {
                        nan_payloads += 1;
                    }
                    if !conv.widens()
                        && x & ((1u64 << (src.frac_bits() - 10)) - 1)
                            == 1u64 << (src.frac_bits() - 11)
                    {
                        ties += 1;
                    }
                }
                compared += 1;
            }
        }
    }
    let _ = fs::remove_dir_all(&dir);
    eprintln!(
        "half-precision FCVT on {}: {compared} CG-vs-hardware comparisons, {ties} exact ties, \
         {nan_payloads} NaN inputs",
        native_host::HOST
    );
    assert!(
        ties > 100_000,
        "the rounded forms must reach exact ties: {ties}"
    );
    assert!(nan_payloads > 2_000, "NaN payloads: {nan_payloads}");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
