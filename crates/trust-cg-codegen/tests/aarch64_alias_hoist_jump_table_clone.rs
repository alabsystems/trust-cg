// trust-cg-codegen - alias-hoist must not clone a jump-table dispatch
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A do-while loop that reads an invariant `*p`, dispatches through a dense
//! `switch` (lowered to a jump table) and stores into `a[i]`, run through the
//! JIT at O0/O2/O3 and compared with a plain Rust model.
//!
//! ```text
//! i = 0
//! loop {
//!     x = *p
//!     v = match i & 3 { 0 => 10, 1 => 21, 2 => 32, 3 => 43 }   // jump table
//!     a[i] = x + v
//!     i += 1
//!     if i >= n { break }
//! }
//! ```
//!
//! `alias-hoist` versions this loop on a run-time check that the store range
//! `a[0..n)` misses `*p`: the fast version is a clone of the body with the
//! load hoisted. `clone_body` rewrites every `MachOperand::Block` of the
//! cloned instructions, but the dispatch is `Adr t, JumpTableIndex(k);
//! LdrswRO; AddRR; Br`, whose targets live in `MachFunction::jump_tables[k]`.
//! A clone would share that table, so the fast version's dispatch would land
//! in the ORIGINAL loop's case blocks, which still reload `*p` and branch back
//! into the original loop. Before the fix O2/O3 stored 6187475906 into `a[0]`
//! where the source stores 1010.
//!
//! The invariant this row pins: a cloned loop version dispatches only into its
//! own blocks, through every block-addressing form (branch operands AND
//! jump-table entries). The pass reproduces only `Block`-operand edges, so it
//! declines a body that reads a jump table or has an out-edge no operand
//! names (`mach_util::clone_reproduces_out_edges`). The rows are bounded host
//! executions; they are tests, not a proof.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, Constant, ICmpOp, SwitchCase, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "alias_hoist_jump_table";
const PASS: &str = "alias-hoist";
const TRIPLE: &str = if cfg!(target_os = "linux") {
    "aarch64-unknown-linux-gnu"
} else {
    "aarch64-apple-darwin"
};
/// Elements of the stored array; every row's `n` stays below it.
const LEN: usize = 16;
/// Index of `a` that `p` points at in the aliasing rows.
const ALIASED: usize = 2;
/// `*p` in the rows where `p` points outside `a`.
const OUTSIDE: u64 = 1000;

type Kernel = extern "C" fn(*mut u64, *const u64, u64);

/// The module of the doc comment: `(a, p, n)`. With `switch == false` the loop
/// computes `v = (i & 3) * 11 + 10` directly and stores it: the same loop
/// without a jump table.
fn module_with(switch: bool) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_alias_hoist_jump_table_clone");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::U64], vec![]);
    let mut fb = mb.function(ENTRY, ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let p = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, Ty::U64);
    let header = fb.create_block();
    let i = fb.add_block_param(header, Ty::U64);
    let cases: Vec<_> = if switch {
        (0..4).map(|_| fb.create_block()).collect()
    } else {
        Vec::new()
    };
    let join = fb.create_block();
    let v = fb.add_block_param(join, Ty::U64);
    let done = fb.create_block();

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(header, vec![zero]);

    fb.switch_to_block(header);
    let x = fb.load(Ty::U64, p);
    let three = fb.iconst(Ty::U64, 3);
    let sel = fb.binop(BinOp::And, Ty::U64, i, three);
    if switch {
        let table: Vec<SwitchCase> = (0..4)
            .map(|case| SwitchCase {
                value: Constant::Int(case as i128),
                target: cases[case],
                args: vec![x],
            })
            .collect();
        fb.switch(sel, table, cases[0], vec![x]);
    } else {
        let eleven = fb.iconst(Ty::U64, 11);
        let ten = fb.iconst(Ty::U64, 10);
        let scaled = fb.binop(BinOp::Mul, Ty::U64, sel, eleven);
        let value = fb.binop(BinOp::Add, Ty::U64, scaled, ten);
        let sum = fb.binop(BinOp::Add, Ty::U64, x, value);
        fb.br(join, vec![sum]);
    }
    for (case, &block) in cases.iter().enumerate() {
        fb.switch_to_block(block);
        let loaded = fb.add_block_param(block, Ty::U64);
        let value = fb.iconst(Ty::U64, case as i128 * 11 + 10);
        let sum = fb.binop(BinOp::Add, Ty::U64, loaded, value);
        fb.br(join, vec![sum]);
    }

    fb.switch_to_block(join);
    let slot = fb.gep(Ty::U64, a, vec![i]);
    fb.store(Ty::U64, slot, v);
    let one = fb.iconst(Ty::U64, 1);
    let step = fb.binop(BinOp::Add, Ty::U64, i, one);
    let stop = fb.icmp(ICmpOp::Uge, Ty::U64, step, n);
    fb.condbr(stop, done, vec![], header, vec![step]);

    fb.switch_to_block(done);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The same program in plain Rust. `p` is `Some(k)` when it points at `a[k]`,
/// `None` when it points at a cell holding [`OUTSIDE`].
fn model(a: &mut [u64; LEN], p: Option<usize>, n: u64) {
    let mut i = 0u64;
    loop {
        let x = p.map_or(OUTSIDE, |k| a[k]);
        let v = (i & 3) * 11 + 10;
        a[i as usize] = x.wrapping_add(v);
        i += 1;
        if i >= n {
            break;
        }
    }
}

/// How many times `pass` changed the function at `opt_level`, with an explicit
/// empty disable list so the ambient `TRUST_CG_DISABLE_PASSES` cannot hide it.
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

/// `(p aliases a[ALIASED], n)`. The non-aliasing rows take the fast clone;
/// the aliasing rows fail the disjointness check and run the original loop.
const ROWS: [(bool, u64); 6] = [
    (false, 1),
    (false, 5),
    (false, 9),
    (true, 1),
    (true, 6),
    (true, 12),
];

/// Run every row through `module` at each level against [`model`].
fn failures_at(module: &trust_ir::Module, levels: &[OptLevel]) -> Vec<String> {
    let mut failures = Vec::new();
    for &opt_level in levels {
        let result = jit(module, opt_level);
        // SAFETY: the signature matches the trust-ir type (ptr, ptr, u64) -> ()
        // and `result` outlives every call.
        let entry = unsafe { result.buffer.get_fn_bound::<Kernel>(ENTRY) }.expect("entry symbol");
        for (aliased, n) in ROWS {
            let mut a = [0u64; LEN];
            let outside = [OUTSIDE];
            if aliased {
                a[ALIASED] = 500;
            }
            let mut want = a;
            model(&mut want, aliased.then_some(ALIASED), n);
            let base = a.as_mut_ptr();
            let p: *const u64 = if aliased {
                base.wrapping_add(ALIASED)
            } else {
                outside.as_ptr()
            };
            entry.as_ref()(base, p, n);
            if a != want {
                failures.push(format!(
                    "{opt_level:?}: aliased = {aliased}, n = {n}: got {:?}, want {:?}",
                    &a[..n as usize],
                    &want[..n as usize]
                ));
            }
        }
    }
    failures
}

/// The loop is versionable (one invariant load, one counted store), and the
/// pass must decline it: its body dispatches through a jump table.
#[test]
fn alias_hoist_declines_the_jump_table_loop() {
    let module = module_with(true);
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        let changes = pass_changes(&module, opt_level, PASS);
        assert_eq!(
            changes, 0,
            "{opt_level:?}: {PASS} cloned a jump-table dispatch ({changes} changes)"
        );
    }
}

/// Positive control: the same loop without the jump table is still versioned,
/// and both versions compute the source's result.
#[test]
fn alias_hoist_versions_the_jump_table_free_twin() {
    let module = module_with(false);
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        assert!(
            pass_changes(&module, opt_level, PASS) > 0,
            "{opt_level:?}: {PASS} must version the twin"
        );
    }
    let failures = failures_at(&module, &[OptLevel::O0, OptLevel::O2, OptLevel::O3]);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn the_fast_version_dispatches_into_its_own_case_blocks() {
    let failures = failures_at(
        &module_with(true),
        &[OptLevel::O0, OptLevel::O2, OptLevel::O3],
    );
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
