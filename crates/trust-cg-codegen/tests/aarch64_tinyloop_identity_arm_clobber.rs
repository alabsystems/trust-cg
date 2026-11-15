// trust-cg-codegen - tiny-loop-diamond must not hoist a write the identity arm reads
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A loop-resident diamond whose compute arm writes two loop-carried
//! registers, run through the JIT at O0/O2/O3 and compared with the trust-ir
//! reference interpreter.
//!
//! ```text
//! cell = 0; acc = seed*3 + 1; s = seed | 1
//! H(acc, s): i = *cell; if i >= n { return s }
//! X:         *cell = i + 1; s4 = xorshift(s); if s4 & 6 == 2 { A } else { B }
//! A:         H(acc + 77, s4)
//! B:         H(acc, acc)
//! ```
//!
//! After cfg-simplify the arms are
//! `A: [AddRI t, acc, #77; MovR acc, t; MovR s, s4; B H]` and
//! `B: [MovR s, acc; B H]`, and the condition flows from the xorshift
//! recurrence, so `tiny-loop-diamond` matches the diamond with merge register
//! `s`. Converting it would hoist A's non-final instructions, `AddRI t, acc,
//! #77` AND the loop-carried write-back `MovR acc, t`, above `Csel s, s4, acc,
//! eq`:
//!
//! * the identity operand of the `Csel` would read `acc` after the hoisted
//!   write, so the B path would store `acc + 77` into `s` instead of `acc`;
//! * `acc` itself would advance by 77 on every iteration, not only on A's.
//!
//! `acc` is read only inside the two arms, so a guard that scans only the
//! blocks outside them admits the hoist. The invariant this row
//! pins: an instruction hoisted out of an arm defines only registers no other
//! path reads, neither the other arm (its identity source), the merge `Csel`,
//! nor any later iteration. `if_convert::arm_defs_observable` therefore also
//! counts a read in the other arm, and a read inside the compute arm that no
//! earlier instruction of that arm writes, and the pass declines this diamond.
//! The rows are bounded host executions; they are tests, not a proof.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, FuncId, ICmpOp, InterpretOptions, InterpretValue, Interpreter, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "tiny_loop_identity_clobber";
const PASS: &str = "tiny-loop-diamond";
const TRIPLE: &str = if cfg!(target_os = "linux") {
    "aarch64-unknown-linux-gnu"
} else {
    "aarch64-apple-darwin"
};

type Kernel = extern "C" fn(u64, u64) -> u64;

/// The module of the doc comment: `(seed, n) -> s`.
fn module() -> (trust_ir::Module, FuncId) {
    let mut mb = ModuleBuilder::new("aarch64_tinyloop_identity_arm_clobber");
    let ty = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function(ENTRY, ty);
    let entry = fb.create_block();
    let seed = fb.add_block_param(entry, Ty::U64);
    let n = fb.add_block_param(entry, Ty::U64);
    let h = fb.create_block();
    let acc = fb.add_block_param(h, Ty::U64);
    let s = fb.add_block_param(h, Ty::U64);
    let x = fb.create_block();
    let a = fb.create_block();
    let b = fb.create_block();
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    let cell = fb.alloca(Ty::U64);
    let zero = fb.iconst(Ty::U64, 0);
    fb.store(Ty::U64, cell, zero);
    let three = fb.iconst(Ty::U64, 3);
    let one = fb.iconst(Ty::U64, 1);
    let scaled = fb.binop(BinOp::Mul, Ty::U64, seed, three);
    let acc0 = fb.binop(BinOp::Add, Ty::U64, scaled, one);
    let s0 = fb.binop(BinOp::Or, Ty::U64, seed, one);
    fb.br(h, vec![acc0, s0]);

    fb.switch_to_block(h);
    let i = fb.load(Ty::U64, cell);
    let go = fb.icmp(ICmpOp::Ult, Ty::U64, i, n);
    fb.condbr(go, x, vec![], exit, vec![]);

    fb.switch_to_block(x);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    fb.store(Ty::U64, cell, next);
    let k13 = fb.iconst(Ty::U64, 13);
    let k7 = fb.iconst(Ty::U64, 7);
    let k17 = fb.iconst(Ty::U64, 17);
    let t1 = fb.binop(BinOp::Shl, Ty::U64, s, k13);
    let s2 = fb.binop(BinOp::Xor, Ty::U64, s, t1);
    let t2 = fb.binop(BinOp::LShr, Ty::U64, s2, k7);
    let s3 = fb.binop(BinOp::Xor, Ty::U64, s2, t2);
    let t3 = fb.binop(BinOp::Shl, Ty::U64, s3, k17);
    let s4 = fb.binop(BinOp::Xor, Ty::U64, s3, t3);
    let six = fb.iconst(Ty::U64, 6);
    let two = fb.iconst(Ty::U64, 2);
    let low = fb.binop(BinOp::And, Ty::U64, s4, six);
    let take_a = fb.icmp(ICmpOp::Eq, Ty::U64, low, two);
    fb.condbr(take_a, a, vec![], b, vec![]);

    fb.switch_to_block(a);
    let k77 = fb.iconst(Ty::U64, 77);
    let acc2 = fb.binop(BinOp::Add, Ty::U64, acc, k77);
    fb.br(h, vec![acc2, s4]);

    fb.switch_to_block(b);
    fb.br(h, vec![acc, acc]);

    fb.switch_to_block(exit);
    fb.ret(vec![s]);
    let fid = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), fid)
}

/// The interpreter's result for `(seed, n)`.
fn reference(module: &trust_ir::Module, fid: FuncId, seed: u64, n: u64) -> u64 {
    let args: Vec<InterpretValue> = [seed, n]
        .iter()
        .map(|&v| InterpretValue::int(Ty::U64, i128::from(v)).expect("u64 argument"))
        .collect();
    let out = Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 10_000_000,
            ..Default::default()
        })
        .execute_func(fid, args)
        .expect("interpreter");
    out.returns[0].as_int().expect("int").as_unsigned() as u64
}

/// The same program in plain Rust, a second oracle for the interpreter.
fn model(seed: u64, n: u64) -> u64 {
    let (mut acc, mut s) = (seed.wrapping_mul(3).wrapping_add(1), seed | 1);
    for _ in 0..n {
        let s2 = s ^ (s << 13);
        let s3 = s2 ^ (s2 >> 7);
        let s4 = s3 ^ (s3 << 17);
        if s4 & 6 == 2 {
            acc = acc.wrapping_add(77);
            s = s4;
        } else {
            s = acc;
        }
    }
    s
}

/// How many times `pass` changed the function at `opt_level`. The disable list
/// is explicitly empty, but `tiny-loop-diamond` also reads the ambient
/// `TRUST_CG_DISABLE_PASSES` itself, so this count is 0 under `tinyloop`.
fn pass_changes(module: &trust_ir::Module, opt_level: OptLevel, pass: &str) -> u32 {
    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect("lowering");
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level,
        target_triple: TRIPLE.into(),
        disabled_passes_override: Some(String::new()),
        ..PipelineConfig::default()
    });
    let mut changes = 0;
    for (function, _) in &lowered {
        let (_, metrics) = pipeline
            .prepare_function_with_metrics(function, None)
            .expect("prepare");
        for (name, count) in &metrics.optimization_pass_changes {
            if name == pass {
                changes += count;
            }
        }
    }
    changes
}

fn jit(module: &trust_ir::Module, opt_level: OptLevel) -> JitCompilationResult {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
}

const ROWS: [(u64, u64); 6] = [(1, 0), (1, 1), (1, 5), (12345, 40), (99, 200), (7, 1000)];

#[test]
fn the_interpreter_and_the_rust_model_agree() {
    let (module, fid) = module();
    for (seed, n) in ROWS {
        assert_eq!(
            reference(&module, fid, seed, n),
            model(seed, n),
            "seed = {seed}, n = {n}"
        );
    }
}

/// The pass matches this diamond (its condition flows from the xorshift
/// recurrence) and must decline it: both arms read `acc`, which the compute
/// arm's hoistable `MovR acc, t` writes.
#[test]
fn tiny_loop_diamond_declines_the_two_write_compute_arm() {
    let (module, _) = module();
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        assert_eq!(
            pass_changes(&module, opt_level, PASS),
            0,
            "{opt_level:?}: {PASS} hoisted a write the identity arm reads"
        );
    }
}

#[test]
fn the_identity_arm_reads_the_loop_carried_value_not_the_hoisted_write() {
    let (module, fid) = module();
    let mut failures = Vec::new();
    for opt_level in [OptLevel::O0, OptLevel::O2, OptLevel::O3] {
        let result = jit(&module, opt_level);
        // SAFETY: the signature matches the trust-ir type (u64, u64) -> u64 and
        // `result` outlives the call.
        let entry = unsafe { result.buffer.get_fn_bound::<Kernel>(ENTRY) }.expect("entry symbol");
        for (seed, n) in ROWS {
            let want = reference(&module, fid, seed, n);
            let got = entry.as_ref()(seed, n);
            if got != want {
                failures.push(format!(
                    "{opt_level:?}: seed = {seed}, n = {n}: got {got}, want {want}"
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
