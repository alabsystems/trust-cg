// trust-cg-codegen - an inlined narrow return keeps its declared width
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A call result keeps the callee's declared return type when the shared LIR
//! inliner (`trust-cg-opt/src/ir_inline.rs`) splices the callee body.
//!
//! The adapter materializes the Apple arm64 return extension: a callee whose
//! trust-ir return type is `i8`/`u8`/`i16`/`u16` returns a `Sextend`/`Uextend`
//! of that value to `I32` (`translate_return`). The `Return` operand is
//! therefore an `I32` value while the call result is the narrow type, and
//! instruction selection types a `Copy` result from its source. Both inliner
//! tiers narrow such an operand with a `Trunc` before the `Copy` that defines
//! the result (`ReturnWiring::Narrow`). A splice that copies the `I32` operand
//! directly gives the caller an `I32` where its own operations are `I8`/`I16`,
//! which these rows detect:
//!
//! * a signed comparison of the result against a narrow caller value
//!   decided on the 32-bit register answers wrong;
//! * a bitwise operation of the result with a narrow caller value is refused
//!   by instruction selection (`Logic lhs=I32 rhs=I8`).
//!
//! Every row compiles one module at O2 and O3, runs it, and compares with a
//! plain Rust model of the same function (which the trust-ir reference
//! interpreter agrees with). The callee is a one-block pure leaf, the shape the
//! straight-line tier admits. Kill switch: `TRUST_CG_DISABLE_PASSES=irinline`
//! (no splice, so the rows do not exercise the wiring). The rows are bounded
//! host executions; they are tests, not a proof.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, CastOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

type Entry = extern "C" fn(u64, u64, u64) -> u64;

/// `module` compiled for the AArch64 JIT at `opt_level`, or the refusal.
fn jit(module: &trust_ir::Module, opt_level: OptLevel) -> Result<JitCompilationResult, String> {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &HashMap::new())
        .map_err(|error| error.to_string())
}

/// What the caller does with the narrow call result `r` and `c` narrowed to
/// the same type.
#[derive(Clone, Copy, Debug)]
enum Use {
    /// `(r <s c) as u64`.
    SignedLess,
    /// `zext(r ^ c)`.
    Xor,
}

/// `g(x, y) -> narrow = trunc(x * 3 + y)`; `f(a, b, c) = use(g(a, b), trunc(c))`.
fn build(narrow: Ty, use_: Use) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_irinline_narrow_return_type");
    let gty = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![narrow.clone()]);
    let g = {
        let mut fb = mb.function("g", gty);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::U64);
        let y = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let three = fb.iconst(Ty::U64, 3);
        let x3 = fb.binop(BinOp::Mul, Ty::U64, x, three);
        let sum = fb.binop(BinOp::Add, Ty::U64, x3, y);
        let r = fb.cast(CastOp::Trunc, Ty::U64, narrow.clone(), sum);
        fb.ret(vec![r]);
        fb.build()
    };
    let fty = mb.add_func_type(vec![Ty::U64; 3], vec![Ty::U64]);
    let mut fb = mb.function("f", fty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::U64);
    let b = fb.add_block_param(entry, Ty::U64);
    let c = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let r = fb.call(g, vec![a, b]);
    let k = fb.cast(CastOp::Trunc, Ty::U64, narrow.clone(), c);
    let out = match use_ {
        Use::SignedLess => {
            let less = fb.icmp(ICmpOp::Slt, narrow.clone(), r, k);
            fb.cast(CastOp::ZExt, Ty::Bool, Ty::U64, less)
        }
        Use::Xor => {
            let x = fb.binop(BinOp::Xor, narrow.clone(), r, k);
            fb.cast(CastOp::ZExt, narrow.clone(), Ty::U64, x)
        }
    };
    fb.ret(vec![out]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Plain Rust model of `f` for a narrow type of `bits` (8 or 16).
fn model(bits: u32, use_: Use, a: u64, b: u64, c: u64) -> u64 {
    let r = a.wrapping_mul(3).wrapping_add(b);
    let mask = (1u64 << bits) - 1;
    let sext = |v: u64| -> i64 { ((v << (64 - bits)) as i64) >> (64 - bits) };
    match use_ {
        Use::SignedLess => u64::from(sext(r) < sext(c)),
        Use::Xor => (r ^ c) & mask,
    }
}

const INPUTS: [[u64; 3]; 8] = [
    [42, 3, 128],
    [0, 0x7f, 0x80],
    [42, 3, 0x81],
    [0x5555, 0x2a, 0x8000],
    [10_922, 2, 0x8001],
    [1, 2, 3],
    [0xffff_ffff, 1, 0xfe],
    [7, 0x80, 0x7fff],
];

fn run(narrow: Ty, bits: u32, use_: Use) -> Vec<String> {
    let module = build(narrow.clone(), use_);
    let mut failures = Vec::new();
    for level in [OptLevel::O2, OptLevel::O3] {
        let compiled = match jit(&module, level) {
            Ok(compiled) => compiled,
            Err(error) => {
                failures.push(format!("{narrow:?} {use_:?} {level:?}: refused: {error}"));
                continue;
            }
        };
        let f = unsafe { compiled.buffer.get_fn_bound::<Entry>("f") }.expect("f symbol");
        for [a, b, c] in INPUTS {
            let want = model(bits, use_, a, b, c);
            let got = f.as_ref()(a, b, c);
            if got != want {
                failures.push(format!(
                    "{narrow:?} {use_:?} {level:?} f({a:#x}, {b:#x}, {c:#x}) = {got:#x}, want {want:#x}"
                ));
            }
        }
    }
    failures
}

/// `(g(a, b) <s c)` with `g` returning `i8`: `f(42, 3, 128)` is
/// `-127 <s -128`, false; a result typed as its 32-bit extension answers true.
#[test]
fn signed_compare_of_inlined_i8_return() {
    let failures = run(Ty::I8, 8, Use::SignedLess);
    assert!(failures.is_empty(), "\n  {}", failures.join("\n  "));
}

/// The `i16` twin of [`signed_compare_of_inlined_i8_return`].
#[test]
fn signed_compare_of_inlined_i16_return() {
    let failures = run(Ty::I16, 16, Use::SignedLess);
    assert!(failures.is_empty(), "\n  {}", failures.join("\n  "));
}

/// `g(a, b) ^ c` with `g` returning `u8`: a result typed `I32` makes
/// instruction selection refuse this valid module at O2/O3
/// (`Logic lhs=I32 rhs=I8`).
#[test]
fn xor_of_inlined_u8_return() {
    let failures = run(Ty::U8, 8, Use::Xor);
    assert!(failures.is_empty(), "\n  {}", failures.join("\n  "));
}

/// The `u16` twin of [`xor_of_inlined_u8_return`].
#[test]
fn xor_of_inlined_u16_return() {
    let failures = run(Ty::U16, 16, Use::Xor);
    assert!(failures.is_empty(), "\n  {}", failures.join("\n  "));
}

/// The plain Rust model agrees with the trust-ir reference interpreter on
/// every row, so a failing row is the compiled code's disagreement.
#[test]
fn model_matches_reference_interpreter() {
    for (narrow, bits) in [(Ty::I8, 8), (Ty::I16, 16), (Ty::U8, 8), (Ty::U16, 16)] {
        for use_ in [Use::SignedLess, Use::Xor] {
            let module = build(narrow.clone(), use_);
            let interp = trust_ir::Interpreter::with_module(&module);
            let f = module.functions.iter().find(|f| f.name == "f").expect("f");
            for [a, b, c] in INPUTS {
                let args: Vec<_> = [a, b, c]
                    .iter()
                    .map(|v| trust_ir::InterpretValue::int(Ty::U64, i128::from(*v)).expect("u64"))
                    .collect();
                let out = interp.execute_function(f, args).expect("interpreter run");
                let got = out.returns[0].as_int().expect("int").raw as u64;
                assert_eq!(
                    got,
                    model(bits, use_, a, b, c),
                    "{narrow:?} {use_:?} ({a}, {b}, {c})"
                );
            }
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
