// trust-cg-codegen - a loop header's jump-table bound stays in its dispatch block
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A loop whose HEADER dispatches through a five-entry jump table whose
//! default leaves the loop, run through the JIT at O0-O3 and compared with a
//! plain Rust model.
//!
//! ```text
//! i = 0; acc = 0
//! loop {
//!     x = a[i]
//!     acc = match x { 0..=4 => acc * 7 + (x * 11 + 10), _ => return x + 1_000_000 }
//!     i += 1
//!     if i >= n { return acc }
//! }
//! ```
//!
//! This is the shape of a coroutine's resume loop (`yield 10; yield 20; 30`
//! has the five states 0..=4, and a state past the table panics). The header
//! lowers to `CMP x, #4; B.HI bad; ADR; LDRSW; ADD; BR`, and `CMP #4; B.HI
//! <outside the loop>` also looks like a constant-trip exit guard.
//! `const-trip-guard-normalize` (trust-cg-opt `scalar_unroll`) rewrote it to
//! `CMP x, x9` with `MOVZ x9, #4` hoisted into the preheader. The per-compile
//! switch binder (`trust_cg_verify::aarch64_switch_binding`) binds a table
//! bound only to an immediate or a move-wide chain inside the dispatch block,
//! so the compile failed closed at O2 and O3 with `[TCG-A64-SWITCH-BIND]
//! ... jump-table bounds constant constant register x9 is not materialized by
//! a move-wide chain: no producer in the block` (the bridge's
//! `coroutine_generator_linux` twin, 2026-10-24). The normalizer now declines
//! a header that dispatches through a jump table, and the binder is unchanged.
//!
//! The invariant this row pins: a jump-table dispatch header keeps its bound
//! as an immediate compare in the dispatch block at every level, the compile
//! binds, and the executed results equal the model, including the first index
//! past the table (5). The rows are bounded host executions; they are tests,
//! not a proof.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_cg_ir::AArch64Opcode;
use trust_ir::{BinOp, Constant, ICmpOp, SwitchCase, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "jump_table_loop_header";
const PASS: &str = "const-trip-guard-normalize";
const TRIPLE: &str = if cfg!(target_os = "linux") {
    "aarch64-unknown-linux-gnu"
} else {
    "aarch64-apple-darwin"
};
const STATES: u64 = 5;
const BAD_BIAS: u64 = 1_000_000;
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

type Kernel = extern "C" fn(*const u64, u64) -> u64;

/// The module of the doc comment: `(a, n) -> u64`, `n >= 1`.
fn module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_jump_table_loop_header_bound");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function(ENTRY, ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, Ty::U64);
    let header = fb.create_block();
    let i = fb.add_block_param(header, Ty::U64);
    let acc = fb.add_block_param(header, Ty::U64);
    let arms: Vec<_> = (0..STATES).map(|_| fb.create_block()).collect();
    let join = fb.create_block();
    let next = fb.add_block_param(join, Ty::U64);
    let bad = fb.create_block();
    let done = fb.create_block();
    let result = fb.add_block_param(done, Ty::U64);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(header, vec![zero, zero]);

    fb.switch_to_block(header);
    let slot = fb.gep(Ty::U64, a, vec![i]);
    let x = fb.load(Ty::U64, slot);
    let table: Vec<SwitchCase> = (0..STATES as usize)
        .map(|state| SwitchCase {
            value: Constant::Int(state as i128),
            target: arms[state],
            args: vec![acc],
        })
        .collect();
    fb.switch(x, table, bad, vec![x]);

    for (state, &block) in arms.iter().enumerate() {
        fb.switch_to_block(block);
        let carried = fb.add_block_param(block, Ty::U64);
        let seven = fb.iconst(Ty::U64, 7);
        let scaled = fb.binop(BinOp::Mul, Ty::U64, carried, seven);
        let value = fb.iconst(Ty::U64, state as i128 * 11 + 10);
        let sum = fb.binop(BinOp::Add, Ty::U64, scaled, value);
        fb.br(join, vec![sum]);
    }

    fb.switch_to_block(join);
    let one = fb.iconst(Ty::U64, 1);
    let step = fb.binop(BinOp::Add, Ty::U64, i, one);
    let stop = fb.icmp(ICmpOp::Uge, Ty::U64, step, n);
    fb.condbr(stop, done, vec![next], header, vec![step, next]);

    fb.switch_to_block(bad);
    let selector = fb.add_block_param(bad, Ty::U64);
    let bias = fb.iconst(Ty::U64, BAD_BIAS as i128);
    let flagged = fb.binop(BinOp::Add, Ty::U64, selector, bias);
    fb.ret(vec![flagged]);

    fb.switch_to_block(done);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The same program in plain Rust.
fn model(a: &[u64]) -> u64 {
    let mut acc = 0u64;
    for &x in a {
        if x >= STATES {
            return x.wrapping_add(BAD_BIAS);
        }
        acc = acc.wrapping_mul(7).wrapping_add(x * 11 + 10);
    }
    acc
}

/// Every row is non-empty (the loop is do-while). The resume sequence
/// 0, 3, 4, every state, long runs, and selectors past the table: 5 (the first
/// index a bound off by one would admit), a large value and `u64::MAX`.
fn rows() -> Vec<Vec<u64>> {
    vec![
        vec![0, 3, 4],
        vec![0, 1, 2, 3, 4],
        vec![4; 9],
        vec![3, 0, 2, 1, 4, 0, 4, 3, 2, 1, 0],
        vec![5],
        vec![0, 3, 5, 4],
        vec![4, 4, 1000],
        vec![2, u64::MAX],
    ]
}

fn jit(module: &trust_ir::Module, opt_level: OptLevel) -> JitCompilationResult {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
}

/// The prepared (post-pipeline) machine function, and how many times `PASS`
/// changed it, with an explicit empty disable list so the ambient
/// `TRUST_CG_DISABLE_PASSES` cannot hide the pass.
fn prepared(module: &trust_ir::Module, opt_level: OptLevel) -> (trust_cg_ir::MachFunction, u32) {
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
    let (function, _) = lowered
        .iter()
        .find(|(function, _)| function.name == ENTRY)
        .expect("the entry function is lowered");
    let (func, metrics) = pipeline
        .prepare_function_with_metrics(function, None)
        .unwrap_or_else(|error| panic!("{opt_level:?}: prepare: {error}"));
    let changes = metrics
        .optimization_pass_changes
        .iter()
        .filter(|(name, _)| name == PASS)
        .map(|(_, count)| *count)
        .sum();
    (func, changes)
}

/// At every level the switch is a jump table, every block that addresses it
/// compares against an immediate in the same block, and the normalizer never
/// rewrote the dispatch header.
#[test]
fn the_dispatch_header_keeps_its_bound_in_the_dispatch_block() {
    let module = module();
    for opt_level in LEVELS {
        let (func, changes) = prepared(&module, opt_level);
        assert_eq!(
            changes, 0,
            "{opt_level:?}: {PASS} rewrote the jump-table dispatch header"
        );
        assert_eq!(
            func.jump_tables.len(),
            1,
            "{opt_level:?}: the five-state switch must lower to one jump table"
        );
        let dispatch: Vec<_> = func
            .block_order
            .iter()
            .copied()
            .filter(|&block| {
                func.block(block).insts.iter().any(|&id| {
                    func.inst(id)
                        .operands
                        .iter()
                        .any(|op| op.as_jump_table_index().is_some())
                })
            })
            .collect();
        assert_eq!(dispatch.len(), 1, "{opt_level:?}: one dispatch block");
        let opcodes: Vec<AArch64Opcode> = func
            .block(dispatch[0])
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect();
        assert!(
            opcodes.contains(&AArch64Opcode::CmpRI) && !opcodes.contains(&AArch64Opcode::CmpRR),
            "{opt_level:?}: the bound must stay an immediate compare in the dispatch block: {opcodes:?}"
        );
    }
}

/// The compile binds at every level (a refusal panics in `jit`) and every row
/// equals the model.
#[test]
fn every_level_compiles_and_matches_the_model() {
    let module = module();
    let mut failures = Vec::new();
    for opt_level in LEVELS {
        let result = jit(&module, opt_level);
        // SAFETY: the signature matches the trust-ir type (ptr, u64) -> u64
        // and `result` outlives every call.
        let entry = unsafe { result.buffer.get_fn_bound::<Kernel>(ENTRY) }.expect("entry symbol");
        for row in rows() {
            let want = model(&row);
            let got = entry.as_ref()(row.as_ptr(), row.len() as u64);
            if got != want {
                failures.push(format!("{opt_level:?}: {row:?}: got {got}, want {want}"));
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
