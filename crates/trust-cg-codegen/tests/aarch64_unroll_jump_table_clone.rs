// trust-cg-codegen - loop-unroll must not clone a jump-table dispatch
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Two multi-block loops whose header dispatches through a dense `switch`
//! (lowered to a jump table), one per multi-block full-unroll tier of
//! `loop-unroll`, run through the JIT at O0/O2/O3 against plain Rust models.
//!
//! Bounded early exit (`analyze_bounded_early_exit_loop`):
//!
//! ```text
//! for j in 1..=8 {
//!     out[j] = match (j + base[0]) & 3 { 0 => 10, 1 => 21, 2 => 32, 3 => 43 };
//!     if base[j] == key { break }        // exit written (j != 8) & (base[j] != key)
//! }
//! ```
//!
//! Diamond body with a constant trip (`analyze_diamond_const_trip_loop`):
//!
//! ```text
//! for i in 0..8 {
//!     out[i] = match (i + base[0]) & 3 { 0 | 2 => 10, 1 | 3 => 21 };
//! }
//! ```
//!
//! Both tiers clone the body once per extra iteration with
//! `clone_inst_remap`, which rewrites `MachOperand::Block` operands, and wire
//! each clone's edges from those operands. The dispatch is `Adr t,
//! JumpTableIndex(k); LdrswRO; AddRR; Br`, whose targets live in
//! `MachFunction::jump_tables[k]`: every clone shares the table and
//! dispatches into iteration 1's case blocks, whose join branches back into
//! iteration 2. Before the fix the bounded-early-exit kernel never returned at
//! O2/O3 (the source runs at most 8 trips).
//!
//! The invariant these rows pin: a cloned iteration dispatches only into its
//! own blocks, through every block-addressing form (branch operands AND
//! jump-table entries). The tiers reproduce only `Block`-operand edges, so they
//! decline a body that reads a jump table or has an out-edge no operand names
//! (`mach_util::clone_reproduces_out_edges`). Each kernel call runs on its
//! own thread with a deadline, so a non-terminating build fails the row
//! instead of hanging the test. The rows are bounded host executions; they are
//! tests, not a proof.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::mpsc;
use std::time::Duration;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, Constant, ICmpOp, SwitchCase, Ty};
use trust_ir_build::ModuleBuilder;

const PASS: &str = "loop-unroll";
const TRIPLE: &str = if cfg!(target_os = "linux") {
    "aarch64-unknown-linux-gnu"
} else {
    "aarch64-apple-darwin"
};
const LEVELS: [OptLevel; 3] = [OptLevel::O0, OptLevel::O2, OptLevel::O3];
/// How long one kernel call may run. The kernels run at most 8 trips.
const CALL_DEADLINE: Duration = Duration::from_secs(5);
/// Elements of `base` and `out`.
const LEN: usize = 9;

const BEE_ENTRY: &str = "bounded_early_exit_jump_table";
const DIAMOND_ENTRY: &str = "diamond_jump_table";

type BeeKernel = extern "C" fn(*const u64, *mut u64, u64);
type DiamondKernel = extern "C" fn(*const u64, *mut u64);

/// The bounded-early-exit kernel `(base, out, key)`. With `switch == false`
/// the header computes `(sel * 11) + 10` directly: the same loop without a
/// jump table.
fn bee_module(switch: bool) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_unroll_jump_table_clone_bee");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::U64], vec![]);
    let mut fb = mb.function(BEE_ENTRY, ty);
    let entry = fb.create_block();
    let base = fb.add_block_param(entry, Ty::Ptr);
    let out = fb.add_block_param(entry, Ty::Ptr);
    let key = fb.add_block_param(entry, Ty::U64);
    let header = fb.create_block();
    let i = fb.add_block_param(header, Ty::U64);
    let cases: Vec<_> = if switch {
        (0..4).map(|_| fb.create_block()).collect()
    } else {
        Vec::new()
    };
    let test = fb.create_block();
    let v = fb.add_block_param(test, Ty::U64);
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(header, vec![zero]);

    fb.switch_to_block(header);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    let k = fb.load(Ty::U64, base);
    let mix = fb.binop(BinOp::Add, Ty::U64, next, k);
    let three = fb.iconst(Ty::U64, 3);
    let sel = fb.binop(BinOp::And, Ty::U64, mix, three);
    if switch {
        let table: Vec<SwitchCase> = (0..4)
            .map(|case| SwitchCase {
                value: Constant::Int(case as i128),
                target: cases[case],
                args: vec![],
            })
            .collect();
        fb.switch(sel, table, cases[0], vec![]);
    } else {
        let eleven = fb.iconst(Ty::U64, 11);
        let ten = fb.iconst(Ty::U64, 10);
        let scaled = fb.binop(BinOp::Mul, Ty::U64, sel, eleven);
        let value = fb.binop(BinOp::Add, Ty::U64, scaled, ten);
        fb.br(test, vec![value]);
    }
    for (case, &block) in cases.iter().enumerate() {
        fb.switch_to_block(block);
        let value = fb.iconst(Ty::U64, case as i128 * 11 + 10);
        fb.br(test, vec![value]);
    }

    fb.switch_to_block(test);
    let out_slot = fb.gep(Ty::U64, out, vec![next]);
    fb.store(Ty::U64, out_slot, v);
    let base_slot = fb.gep(Ty::U64, base, vec![next]);
    let value = fb.load(Ty::U64, base_slot);
    let eight = fb.iconst(Ty::U64, 8);
    let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, eight);
    let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, value, key);
    let more = fb.binop(BinOp::BAnd, Ty::Bool, trip, not_found);
    fb.condbr(more, header, vec![next], exit, vec![]);

    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn bee_model(base: &[u64; LEN], out: &mut [u64; LEN], key: u64) {
    for j in 1..=8u64 {
        let sel = (j + base[0]) & 3;
        out[j as usize] = sel * 11 + 10;
        if base[j as usize] == key {
            break;
        }
    }
}

/// The diamond kernel `(base, out)`. With `switch == true` the header
/// dispatches through a four-entry jump table over two case blocks; with
/// `switch == false` it branches on `sel & 1` to the same two blocks: the same
/// diamond without a jump table.
fn diamond_module(switch: bool) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_unroll_jump_table_clone_diamond");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr], vec![]);
    let mut fb = mb.function(DIAMOND_ENTRY, ty);
    let entry = fb.create_block();
    let base = fb.add_block_param(entry, Ty::Ptr);
    let out = fb.add_block_param(entry, Ty::Ptr);
    let header = fb.create_block();
    let i = fb.add_block_param(header, Ty::U64);
    let even = fb.create_block();
    let odd = fb.create_block();
    let join = fb.create_block();
    let v = fb.add_block_param(join, Ty::U64);
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(header, vec![zero]);

    fb.switch_to_block(header);
    let k = fb.load(Ty::U64, base);
    let mix = fb.binop(BinOp::Add, Ty::U64, i, k);
    let three = fb.iconst(Ty::U64, 3);
    let sel = fb.binop(BinOp::And, Ty::U64, mix, three);
    if switch {
        let table: Vec<SwitchCase> = (0..4)
            .map(|case| SwitchCase {
                value: Constant::Int(case as i128),
                target: if case % 2 == 0 { even } else { odd },
                args: vec![],
            })
            .collect();
        fb.switch(sel, table, even, vec![]);
    } else {
        let one = fb.iconst(Ty::U64, 1);
        let low = fb.binop(BinOp::And, Ty::U64, sel, one);
        let zero = fb.iconst(Ty::U64, 0);
        let is_even = fb.icmp(ICmpOp::Eq, Ty::U64, low, zero);
        fb.condbr(is_even, even, vec![], odd, vec![]);
    }

    fb.switch_to_block(even);
    let ten = fb.iconst(Ty::U64, 10);
    fb.br(join, vec![ten]);

    fb.switch_to_block(odd);
    let twenty_one = fb.iconst(Ty::U64, 21);
    fb.br(join, vec![twenty_one]);

    fb.switch_to_block(join);
    let slot = fb.gep(Ty::U64, out, vec![i]);
    fb.store(Ty::U64, slot, v);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    let eight = fb.iconst(Ty::U64, 8);
    let more = fb.icmp(ICmpOp::Ult, Ty::U64, next, eight);
    // An unused constant between the compare and the branch keeps instruction
    // selection from fusing them into `Cmp; BCond`: the trip test stays in its
    // `Cmp; CSet; CmpRI #0; BCond; B` dialect, the one the diamond tier
    // recognizes. LICM hoists the constant out of the loop before the unroller
    // runs, so the five control instructions end the block contiguously.
    let _spacer = fb.iconst(Ty::U64, 0x5a5a);
    fb.condbr(more, header, vec![next], exit, vec![]);

    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn diamond_model(base: &[u64; LEN], out: &mut [u64; LEN]) {
    for i in 0..8u64 {
        let sel = (i + base[0]) & 3;
        out[i as usize] = if sel & 1 == 0 { 10 } else { 21 };
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

/// Run `call` on its own thread; `None` when it has not returned by
/// [`CALL_DEADLINE`]. The thread owns every buffer the kernel writes.
fn call_with_deadline<T: Send + 'static>(call: impl FnOnce() -> T + Send + 'static) -> Option<T> {
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(call());
    });
    rx.recv_timeout(CALL_DEADLINE).ok()
}

/// `(base[0], key)`; `base[j] = 10 + j` otherwise, so `key` in `11..=18`
/// stops the loop at `j = key - 10` and any other key runs all 8 trips.
const BEE_ROWS: [(u64, u64); 5] = [(0, 13), (1, 11), (2, 17), (3, 99), (5, 18)];

/// `base[0]` for the diamond rows.
const DIAMOND_ROWS: [u64; 4] = [0, 1, 2, 7];

fn bee_failures(module: &trust_ir::Module, levels: &[OptLevel]) -> Vec<String> {
    let mut failures = Vec::new();
    for &opt_level in levels {
        let result = jit(module, opt_level);
        let entry = result
            .buffer
            .get_fn_ptr_bound(BEE_ENTRY)
            .expect("entry symbol")
            .as_ptr() as usize;
        for (b0, key) in BEE_ROWS {
            let mut base: [u64; LEN] = std::array::from_fn(|j| 10 + j as u64);
            base[0] = b0;
            let mut want = [0u64; LEN];
            bee_model(&base, &mut want, key);
            let got = call_with_deadline(move || {
                let mut out = [0u64; LEN];
                // SAFETY: `entry` is the JIT entry of a (ptr, ptr, u64) -> ()
                // function, and both buffers outlive the call.
                let kernel: BeeKernel = unsafe { std::mem::transmute(entry) };
                kernel(base.as_ptr(), out.as_mut_ptr(), key);
                out
            });
            match got {
                Some(out) if out == want => {}
                Some(out) => failures.push(format!(
                    "{opt_level:?}: base[0] = {b0}, key = {key}: got {out:?}, want {want:?}"
                )),
                None => {
                    failures.push(format!(
                        "{opt_level:?}: base[0] = {b0}, key = {key}: did not return within \
                         {CALL_DEADLINE:?} (want {want:?})"
                    ));
                    // The spinning thread still executes the JIT code.
                    std::mem::forget(result);
                    break;
                }
            }
        }
    }
    failures
}

fn diamond_failures(module: &trust_ir::Module, levels: &[OptLevel]) -> Vec<String> {
    let mut failures = Vec::new();
    for &opt_level in levels {
        let result = jit(module, opt_level);
        let entry = result
            .buffer
            .get_fn_ptr_bound(DIAMOND_ENTRY)
            .expect("entry symbol")
            .as_ptr() as usize;
        for b0 in DIAMOND_ROWS {
            let mut base = [0u64; LEN];
            base[0] = b0;
            let mut want = [0u64; LEN];
            diamond_model(&base, &mut want);
            let got = call_with_deadline(move || {
                let mut out = [0u64; LEN];
                // SAFETY: `entry` is the JIT entry of a (ptr, ptr) -> ()
                // function, and both buffers outlive the call.
                let kernel: DiamondKernel = unsafe { std::mem::transmute(entry) };
                kernel(base.as_ptr(), out.as_mut_ptr());
                out
            });
            match got {
                Some(out) if out == want => {}
                Some(out) => failures.push(format!(
                    "{opt_level:?}: base[0] = {b0}: got {out:?}, want {want:?}"
                )),
                None => {
                    failures.push(format!(
                        "{opt_level:?}: base[0] = {b0}: did not return within \
                         {CALL_DEADLINE:?} (want {want:?})"
                    ));
                    // The spinning thread still executes the JIT code.
                    std::mem::forget(result);
                    break;
                }
            }
        }
    }
    failures
}

/// The bounded-early-exit tier recognizes this loop shape, and must decline
/// it: its header dispatches through a jump table.
#[test]
fn bounded_early_exit_unroll_declines_the_jump_table_loop() {
    let module = bee_module(true);
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        let changes = pass_changes(&module, opt_level, PASS);
        assert_eq!(
            changes, 0,
            "{opt_level:?}: {PASS} cloned a jump-table dispatch ({changes} changes)"
        );
    }
}

/// Positive control: the same loop without the jump table is still fully
/// unrolled, and the unrolled code computes the source's result.
#[test]
fn bounded_early_exit_unroll_takes_the_jump_table_free_twin() {
    let module = bee_module(false);
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        assert!(
            pass_changes(&module, opt_level, PASS) > 0,
            "{opt_level:?}: {PASS} must unroll the twin"
        );
    }
    let failures = bee_failures(&module, &LEVELS);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn bounded_early_exit_clones_dispatch_into_their_own_case_blocks() {
    let failures = bee_failures(&bee_module(true), &LEVELS);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The diamond tier recognizes this loop shape, and must decline it: its
/// header dispatches through a jump table.
#[test]
fn diamond_unroll_declines_the_jump_table_loop() {
    let module = diamond_module(true);
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        let changes = pass_changes(&module, opt_level, PASS);
        assert_eq!(
            changes, 0,
            "{opt_level:?}: {PASS} cloned a jump-table dispatch ({changes} changes)"
        );
    }
}

/// Positive control: the same diamond without the jump table is still fully
/// unrolled, and the unrolled code computes the source's result.
#[test]
fn diamond_unroll_takes_the_jump_table_free_twin() {
    let module = diamond_module(false);
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        assert!(
            pass_changes(&module, opt_level, PASS) > 0,
            "{opt_level:?}: {PASS} must unroll the twin"
        );
    }
    let failures = diamond_failures(&module, &LEVELS);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn diamond_clones_dispatch_into_their_own_case_blocks() {
    let failures = diamond_failures(&diamond_module(true), &LEVELS);
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
