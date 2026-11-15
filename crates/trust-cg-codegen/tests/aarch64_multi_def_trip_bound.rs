// trust-cg-codegen - constant trip bounds against a register with several constant definitions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Compile-time loop bounds read from a bound register written with
//! different constants on different paths.
//!
//! The invariant these rows pin: a register written with different constants
//! on different paths is not one constant. Machine IR is not SSA, and
//! `effects::build_reaching_def_map` keeps one definition per vreg, the
//! layout-last one; a resolver that reads it takes that definition's value on
//! every path. `mach_util::const_value` and the pass-local resolvers (which
//! delegate to `mach_util::copied_const`) give a register a constant only
//! when EVERY definition of it writes that constant, and `alias-hoist` reads
//! a constant bound as the ONE definition reaching its use
//! (`crate::reaching_const`), so the multi-def rows below are refused rather
//! than read as their layout-last value.
//!
//! Each pass sizes its fast path from a constant loop bound (a trip count, a
//! checked length, a low bound, or the store range a hoisted load must not
//! alias) and accepts a bound REGISTER it resolves to a constant. The
//! register here is the stop value of an early-exit search that O2/O3 unroll
//! fully, one `Movz r, #k` per exit edge. The shapes, one module per pass:
//!
//! * an ascending stepped search (`j = step, 2*step, ..., limit*step`, stop
//!   when `j == sel`), the layout-last def `#limit*step`: the loop bound of
//!   `bitrev`, `bytesum`, `iota_fill`, `predsum_chain` and
//!   `swap_range_guard`, and the checked length of `mac_row_unroll`;
//! * a descending search (`j = start-1, ..., stop`), the layout-last def
//!   `#stop`: the low bound of a reverse map (`map_reverse`) and the loop
//!   bound of a hoisted load's store range (`alias_hoist`, which also takes
//!   the bound from a diamond phi of two constants and from a constant an
//!   outer loop carries).
//!
//! The `TRUST_CG_DISABLE_PASSES` key a module names cleared the mismatch a
//! layout-last read produced. Every row JIT-runs at O2 and O3 and compares
//! with a plain Rust model of the same program. A test's doc names what a
//! resolver that reads the layout-last definition does with its shape: the
//! misreading the row pins against. The rows are bounded host executions;
//! they are tests, not a proof.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, BlockId, ICmpOp, Ty, ValueId};
use trust_ir_build::FunctionBuilder;

/// The host triple the metrics pipeline prepares for.
const TRIPLE: &str = if cfg!(target_os = "linux") {
    "aarch64-unknown-linux-gnu"
} else {
    "aarch64-apple-darwin"
};

/// How many times `pass` changed the function at `opt_level`, through the
/// public pipeline with an explicit empty disable list (so the ambient
/// `TRUST_CG_DISABLE_PASSES` cannot hide a firing).
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

/// `module` compiled for the AArch64 JIT at `opt_level`, or the refusal.
fn jit(module: &trust_ir::Module, opt_level: OptLevel) -> Result<JitCompilationResult, String> {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &HashMap::new())
        .map_err(|error| error.to_string())
}

/// Where `j = 0; loop { j += step; if j == limit*step || j == sel { break } }`
/// stops for `sel`. Fully unrolled, the search writes one `Movz r, #j` per
/// exit edge, `#limit*step` laid out last.
fn stepped_search_stop(limit: u64, step: u64, sel: u64) -> u64 {
    let mut j = 0u64;
    loop {
        j += step;
        if j == limit * step || j == sel {
            return j;
        }
    }
}

/// Where `j = start; loop { j -= 1; if j == stop || j == sel { break } }`
/// stops for `sel`.
fn descending_search_stop(start: u64, stop: u64, sel: u64) -> u64 {
    let mut j = start;
    loop {
        j -= 1;
        if j == stop || j == sel {
            return j;
        }
    }
}

/// Emits `j = start; loop { j -= 1; if j == stop || j == sel { break } }`
/// from the current block and branches to `target` with `[j]`. Fully
/// unrolled at O2/O3, it writes one `Movz r, #j` per exit edge, `#stop` laid
/// out last.
fn emit_descending_search(
    fb: &mut FunctionBuilder<'_>,
    sel: ValueId,
    start: u64,
    stop: u64,
    target: BlockId,
) {
    let search = fb.create_block();
    let j = fb.add_block_param(search, Ty::U64);
    let search_test = fb.create_block();
    let first = fb.iconst(Ty::U64, i128::from(start));
    fb.br(search, vec![first]);
    fb.switch_to_block(search);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.sub(Ty::U64, j, one);
    fb.br(search_test, vec![]);
    fb.switch_to_block(search_test);
    let last = fb.iconst(Ty::U64, i128::from(stop));
    let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, last);
    let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, sel);
    let more = fb.binop(BinOp::And, Ty::Bool, trip, not_found);
    fb.condbr(more, search, vec![next], target, vec![next]);
}

/// Fails the test with every collected mismatch.
fn assert_no_failures(failures: &[String]) {
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

mod alias_hoist {
    //! `i = 0; loop { a[i] = 7; *out = *p; i += 1; if i >= r { break } }`, run
    //! through the JIT at O2 and O3.
    //!
    //! The alias-versioned load hoist (`alias-hoist`) sizes the loop's store range
    //! as `[a, a + 8*bound)` from the exit compare `cmp step, r`. A register `r`
    //! with more than one definition is not taken as a run-time bound; it fell
    //! through to `resolve_const_vreg`, which read
    //! `build_reaching_def_map_by_vreg` (LAST-WINS) and returned the layout-last
    //! constant. When that constant is smaller than the value `r` really holds,
    //! the store range is under-approximated, a `p` inside the real range clears
    //! the disjointness check, and the fast clone loads `*p` before the loop
    //! stores it.
    //!
    //! `r` is made multi-def three ways: a phi of constants through a diamond
    //! (`sel != 0 ? 6 : 2`, the `2` arm laid out last), a fully unrolled
    //! descending early-exit search (`j = 8, 7, ..., 1`, stop when `j == sel`),
    //! whose layout-last exit edge writes `#1`, and a register an enclosing loop
    //! carries (6 on entry, 2 from its latch, which is laid out last). `*out` must
    //! be 7 exactly when `p` is one of the stored elements.
    //! `TRUST_CG_DISABLE_PASSES=aliashoist` clears the mismatch.
    //!
    //! Current state: `alias-hoist` reads the start and a constant
    //! bound as the ONE definition reaching their use (`crate::reaching_const`,
    //! through copies), so a register two definitions reach is not a counted
    //! bound or start; the rows still pin the result.

    use super::*;
    use trust_ir::{BlockId, ICmpOp, Ty, ValueId};
    use trust_ir_build::{FunctionBuilder, ModuleBuilder};

    const PASS: &str = "alias-hoist";
    /// Where the descending search starts (its first value is `START - 1`).
    const START: u64 = 9;
    /// The enclosing loop's bound on its first pass and on every later pass.
    const OUTER_FIRST: u64 = 6;
    const OUTER_THEN: u64 = 2;

    type Kernel = extern "C" fn(*mut u64, *const u64, *mut u64, u64);

    /// How the loop bound `r` is produced from `sel`.
    #[derive(Clone, Copy, Debug)]
    enum Bound {
        /// `sel != 0 ? taken : fallthrough`, merged into one block parameter; the
        /// `fallthrough` arm is created (and laid out) last.
        Diamond { taken: u64, fallthrough: u64 },
        /// `j = START; loop { j -= 1; if j == 1 || j == sel { break } }`, fully
        /// unrolled at O2/O3 into one `Movz r, #j` per exit edge, `#1` last.
        DescendingSearch,
    }

    impl Bound {
        fn value(self, sel: u64) -> u64 {
            match self {
                Bound::Diamond { taken, fallthrough } => {
                    if sel != 0 {
                        taken
                    } else {
                        fallthrough
                    }
                }
                Bound::DescendingSearch => descending_search_stop(START, 1, sel),
            }
        }

        fn sels(self) -> Vec<u64> {
            match self {
                Bound::Diamond { .. } => vec![0, 1],
                Bound::DescendingSearch => (0..=START).collect(),
            }
        }

        /// Emits the producer from the current block and branches to `target`
        /// with `[r]`.
        fn emit(self, fb: &mut FunctionBuilder<'_>, sel: ValueId, target: BlockId) {
            match self {
                Bound::Diamond { taken, fallthrough } => {
                    let then_block = fb.create_block();
                    let else_block = fb.create_block();
                    let zero = fb.iconst(Ty::U64, 0);
                    let nonzero = fb.icmp(ICmpOp::Ne, Ty::U64, sel, zero);
                    fb.condbr(nonzero, then_block, vec![], else_block, vec![]);
                    fb.switch_to_block(then_block);
                    let value = fb.iconst(Ty::U64, i128::from(taken));
                    fb.br(target, vec![value]);
                    fb.switch_to_block(else_block);
                    let value = fb.iconst(Ty::U64, i128::from(fallthrough));
                    fb.br(target, vec![value]);
                }
                Bound::DescendingSearch => emit_descending_search(fb, sel, START, 1, target),
            }
        }
    }

    /// `fn(a: *mut u64, p: *const u64, out: *mut u64, sel: u64)`:
    ///
    /// ```text
    /// r = bound(sel)
    /// i = 0; loop { a[i] = 7; *out = *p; i += 1; if i >= r { break } }
    /// ```
    fn build_module(name: &str, bound: Bound) -> trust_ir::Module {
        let mut mb = ModuleBuilder::new(name);
        let fty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::U64], vec![]);
        let mut fb = mb.function(name, fty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::Ptr);
        let p = fb.add_block_param(entry, Ty::Ptr);
        let out = fb.add_block_param(entry, Ty::Ptr);
        let sel = fb.add_block_param(entry, Ty::U64);
        let pre = fb.create_block();
        let r = fb.add_block_param(pre, Ty::U64);
        let header = fb.create_block();
        let i = fb.add_block_param(header, Ty::U64);
        let done = fb.create_block();

        fb.switch_to_block(entry);
        bound.emit(&mut fb, sel, pre);

        fb.switch_to_block(pre);
        let zero = fb.iconst(Ty::U64, 0);
        fb.br(header, vec![zero]);

        fb.switch_to_block(header);
        let slot = fb.gep(Ty::U64, a, vec![i]);
        let seven = fb.iconst(Ty::U64, 7);
        fb.store(Ty::U64, slot, seven);
        let value = fb.load(Ty::U64, p);
        fb.store(Ty::U64, out, value);
        let one = fb.iconst(Ty::U64, 1);
        let step = fb.add(Ty::U64, i, one);
        let stop = fb.icmp(ICmpOp::Uge, Ty::U64, step, r);
        fb.condbr(stop, done, vec![], header, vec![step]);

        fb.switch_to_block(done);
        fb.ret(vec![]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// `fn(a: *mut u64, p: *const u64, out: *mut u64, passes: u64)` with the
    /// bound carried by an enclosing loop:
    ///
    /// ```text
    /// t = 0; r = FIRST
    /// while t <u passes {
    ///     i = 0; loop { a[i] = 7; *out = *p; i += 1; if i >= r { break } }
    ///     t += 1; r = THEN
    /// }
    /// ```
    fn build_outer_carried_module(name: &str) -> trust_ir::Module {
        let mut mb = ModuleBuilder::new(name);
        let fty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::U64], vec![]);
        let mut fb = mb.function(name, fty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::Ptr);
        let p = fb.add_block_param(entry, Ty::Ptr);
        let out = fb.add_block_param(entry, Ty::Ptr);
        let passes = fb.add_block_param(entry, Ty::U64);
        let outer = fb.create_block();
        let t = fb.add_block_param(outer, Ty::U64);
        let r = fb.add_block_param(outer, Ty::U64);
        let pre = fb.create_block();
        let header = fb.create_block();
        let i = fb.add_block_param(header, Ty::U64);
        let outer_latch = fb.create_block();
        let done = fb.create_block();

        fb.switch_to_block(entry);
        let t0 = fb.iconst(Ty::U64, 0);
        let first = fb.iconst(Ty::U64, i128::from(OUTER_FIRST));
        fb.br(outer, vec![t0, first]);

        fb.switch_to_block(outer);
        let more = fb.icmp(ICmpOp::Ult, Ty::U64, t, passes);
        fb.condbr(more, pre, vec![], done, vec![]);

        fb.switch_to_block(pre);
        let zero = fb.iconst(Ty::U64, 0);
        fb.br(header, vec![zero]);

        fb.switch_to_block(header);
        let slot = fb.gep(Ty::U64, a, vec![i]);
        let seven = fb.iconst(Ty::U64, 7);
        fb.store(Ty::U64, slot, seven);
        let value = fb.load(Ty::U64, p);
        fb.store(Ty::U64, out, value);
        let one = fb.iconst(Ty::U64, 1);
        let step = fb.add(Ty::U64, i, one);
        let stop = fb.icmp(ICmpOp::Uge, Ty::U64, step, r);
        fb.condbr(stop, outer_latch, vec![], header, vec![step]);

        fb.switch_to_block(outer_latch);
        let t_one = fb.iconst(Ty::U64, 1);
        let t_next = fb.add(Ty::U64, t, t_one);
        let then = fb.iconst(Ty::U64, i128::from(OUTER_THEN));
        fb.br(outer, vec![t_next, then]);

        fb.switch_to_block(done);
        fb.ret(vec![]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// `*out` after `passes` runs of the outer-carried kernel with `p = a + k`.
    fn outer_carried_model(passes: u64, k: u64) -> u64 {
        let mut a = [0u64; 16];
        let mut out = u64::MAX;
        let mut r = OUTER_FIRST;
        for _ in 0..passes {
            let mut i = 0u64;
            loop {
                a[i as usize] = 7;
                out = a[k as usize];
                i += 1;
                if i >= r {
                    break;
                }
            }
            r = OUTER_THEN;
        }
        out
    }

    /// Every `sel` and every `p = a + k` (`k < 8`) at O2 and O3. Returns the
    /// failures as text.
    fn probe(name: &str, bound: Bound) -> Vec<String> {
        let module = build_module(name, bound);
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let fired = pass_changes(&module, opt_level, PASS);
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{name} {opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the entry's trust-ir signature is (ptr, ptr, ptr, u64) ->
            // (), matching `Kernel`, and `result` outlives every call.
            let entry =
                unsafe { result.buffer.get_fn_bound::<Kernel>(name) }.expect("entry symbol");
            for sel in bound.sels() {
                let r = bound.value(sel);
                // The body runs once whatever `r` is, then while `i < r`.
                let trips = r.max(1);
                for k in 0..8usize {
                    let mut a = [0u64; 16];
                    let mut out = u64::MAX;
                    let base = a.as_mut_ptr();
                    // SAFETY: every bound above stores at most `a[0..8]` and
                    // `k < 8`, so every access stays inside `a` and `out`.
                    entry.as_ref()(base, unsafe { base.add(k) }, &mut out, sel);
                    let expected = if (k as u64) < trips { 7 } else { 0 };
                    if out != expected {
                        failures.push(format!(
                            "{name} {opt_level:?} sel={sel} r={r} p=a+{k}: *out = {out}, \
                         expected {expected} ({PASS} changes: {fired})"
                        ));
                    }
                }
            }
        }
        failures
    }

    /// The last iteration loads `*p` after the loop stored `a[0..r)`, so `*out`
    /// is 7 whenever `p` points into that range. A bound register resolved to
    /// its layout-last constant (2 for the diamond, 1 for the search) shrinks the
    /// store range the hoist checks, and the hoisted load then reads the value
    /// `*p` had before the loop.
    #[test]
    fn hoisted_load_against_a_multi_def_register_bound_sees_the_loop_stores() {
        let mut failures = Vec::new();
        for (name, bound) in [
            (
                "alias_hoist_rbound_diamond",
                Bound::Diamond {
                    taken: 6,
                    fallthrough: 2,
                },
            ),
            ("alias_hoist_rbound_search", Bound::DescendingSearch),
        ] {
            failures.extend(probe(name, bound));
        }
        assert_no_failures(&failures);
    }

    /// The bound an enclosing loop carries is 6 on the first pass and 2 after it;
    /// its layout-last definition (the outer latch's 2) sizes the store range the
    /// hoist checks, so on the first pass a `p` in `a[2..6)` is loaded before the
    /// inner loop stores it.
    #[test]
    fn hoisted_load_against_an_outer_loop_carried_bound_sees_the_loop_stores() {
        let name = "alias_hoist_rbound_outer_carried";
        let module = build_outer_carried_module(name);
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let fired = pass_changes(&module, opt_level, PASS);
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the entry's trust-ir signature is (ptr, ptr, ptr, u64) ->
            // (), matching `Kernel`, and `result` outlives every call.
            let entry =
                unsafe { result.buffer.get_fn_bound::<Kernel>(name) }.expect("entry symbol");
            for passes in 1..=3u64 {
                for k in 0..8u64 {
                    let mut a = [0u64; 16];
                    let mut out = u64::MAX;
                    let base = a.as_mut_ptr();
                    // SAFETY: every pass stores at most `a[0..6]` and `k < 8`, so
                    // every access stays inside `a` and `out`.
                    entry.as_ref()(base, unsafe { base.add(k as usize) }, &mut out, passes);
                    let expected = outer_carried_model(passes, k);
                    if out != expected {
                        failures.push(format!(
                            "{opt_level:?} passes={passes} p=a+{k}: *out = {out}, expected \
                         {expected} ({PASS} changes: {fired})"
                        ));
                    }
                }
            }
        }
        assert_no_failures(&failures);
    }
}

mod mac_row_unroll {
    //! `mac-row-unroll` 4x-unrolls the bounds-checked AXPY row
    //! `while j <u N { c[i*N+j] += aik * b[k*N+j]; j += 1 }` behind hoisted
    //! `cidx <u L-3` / `bidx <u L-3` guards, where `L` is the array length every
    //! bounds check compares against. `bounds_check_in` reads `L` from a
    //! `CmpRR(idx, Lreg)` check; its pass-local `const_value` read
    //! the last-wins def map, so a length register with several constant
    //! definitions resolved to its layout-last one. The guards then use that
    //! constant, and the fast path runs four unchecked MACs past the length the
    //! scalar checks enforce.
    //!
    //! These tests JIT-run, at O2 and O3, the row loop with its checked length in
    //! the register a fully unrolled early-exit search left (`j = 10, 20, ..., 80`,
    //! stop when `j == sel`): one `Movz L, #j` per unrolled exit edge, the
    //! layout-last being `#80`. A failing check returns `u64::MAX` after the
    //! stores the earlier iterations made. The return value and the whole `c`
    //! buffer are compared with a plain Rust model.
    //! `TRUST_CG_DISABLE_PASSES=mac_row_unroll` clears the mismatch.

    use super::*;
    use trust_ir::{BinOp, ICmpOp, Ty};
    use trust_ir_build::ModuleBuilder;

    const PASS: &str = "mac-row-unroll";
    /// Row length (the loop's constant trip `N`).
    const N: u64 = 8;
    /// Unrolled search steps; small enough for O2/O3 to unroll the search fully.
    const LIMIT: u64 = 8;
    /// Search stride; distinct from `N` so no length constant coincides with it.
    const STEP: u64 = 10;
    const ABORTED: u64 = u64::MAX;
    const AIK: u64 = 5;
    const BUF: usize = 128;

    type Kernel = extern "C" fn(*mut i64, *const i64, u64, u64, u64, u64) -> u64;

    /// `fn(c: *mut i64, b: *const i64, i: u64, k: u64, aik: u64, sel: u64) -> u64`:
    ///
    /// ```text
    /// j = 0; loop { j += STEP; if j == LIMIT*STEP || j == sel { break } }   // L = j
    /// j = 0
    /// while j <u N {
    ///     cidx = i*N + j; if !(cidx <u L) { return ABORTED }
    ///     bidx = k*N + j; if !(bidx <u L) { return ABORTED }
    ///     c[cidx] = aik * b[bidx] + c[cidx]; j += 1
    /// }
    /// return 0
    /// ```
    fn build_module(name: &str) -> trust_ir::Module {
        let mut mb = ModuleBuilder::new(name);
        let fty = mb.add_func_type(
            vec![Ty::Ptr, Ty::Ptr, Ty::U64, Ty::U64, Ty::U64, Ty::U64],
            vec![Ty::U64],
        );
        let mut fb = mb.function(name, fty);
        let entry = fb.create_block();
        let c = fb.add_block_param(entry, Ty::Ptr);
        let b = fb.add_block_param(entry, Ty::Ptr);
        let i = fb.add_block_param(entry, Ty::U64);
        let k = fb.add_block_param(entry, Ty::U64);
        let aik = fb.add_block_param(entry, Ty::U64);
        let sel = fb.add_block_param(entry, Ty::U64);
        let search = fb.create_block();
        let s = fb.add_block_param(search, Ty::U64);
        let search_test = fb.create_block();
        let pre = fb.create_block();
        let len = fb.add_block_param(pre, Ty::U64);
        let header = fb.create_block();
        let j = fb.add_block_param(header, Ty::U64);
        let exit = fb.create_block();
        let check_c = fb.create_block();
        let check_b = fb.create_block();
        let body = fb.create_block();
        let abort = fb.create_block();

        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::U64, 0);
        fb.br(search, vec![zero]);

        fb.switch_to_block(search);
        let stride = fb.iconst(Ty::U64, i128::from(STEP));
        let next = fb.add(Ty::U64, s, stride);
        fb.br(search_test, vec![]);

        fb.switch_to_block(search_test);
        let last = fb.iconst(Ty::U64, i128::from(LIMIT * STEP));
        let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, last);
        let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, sel);
        let more = fb.binop(BinOp::And, Ty::Bool, trip, not_found);
        fb.condbr(more, search, vec![next], pre, vec![next]);

        fb.switch_to_block(pre);
        let j0 = fb.iconst(Ty::U64, 0);
        fb.br(header, vec![j0]);

        fb.switch_to_block(header);
        let row = fb.iconst(Ty::U64, i128::from(N));
        let go = fb.icmp(ICmpOp::Ult, Ty::U64, j, row);
        fb.condbr(go, check_c, vec![], exit, vec![]);

        fb.switch_to_block(exit);
        let ok = fb.iconst(Ty::U64, 0);
        fb.ret(vec![ok]);

        fb.switch_to_block(check_c);
        let row_c = fb.iconst(Ty::U64, i128::from(N));
        let c_row = fb.mul(Ty::U64, i, row_c);
        let cidx = fb.add(Ty::U64, c_row, j);
        let c_in = fb.icmp(ICmpOp::Ult, Ty::U64, cidx, len);
        fb.condbr(c_in, check_b, vec![], abort, vec![]);

        fb.switch_to_block(check_b);
        let row_b = fb.iconst(Ty::U64, i128::from(N));
        let b_row = fb.mul(Ty::U64, k, row_b);
        let bidx = fb.add(Ty::U64, b_row, j);
        let b_in = fb.icmp(ICmpOp::Ult, Ty::U64, bidx, len);
        fb.condbr(b_in, body, vec![], abort, vec![]);

        fb.switch_to_block(body);
        let c_addr = fb.gep(Ty::I64, c, vec![cidx]);
        let c_val = fb.load(Ty::I64, c_addr);
        let b_addr = fb.gep(Ty::I64, b, vec![bidx]);
        let b_val = fb.load(Ty::I64, b_addr);
        let product = fb.mul(Ty::U64, aik, b_val);
        let mac = fb.add(Ty::U64, product, c_val);
        let store_addr = fb.gep(Ty::I64, c, vec![cidx]);
        fb.store(Ty::I64, store_addr, mac);
        let one = fb.iconst(Ty::U64, 1);
        let j_next = fb.add(Ty::U64, j, one);
        fb.br(header, vec![j_next]);

        fb.switch_to_block(abort);
        let aborted = fb.iconst(Ty::U64, i128::from(ABORTED));
        fb.ret(vec![aborted]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// Plain-Rust model of the row loop; returns the function's result.
    fn model(c: &mut [i64], b: &[i64], i: u64, k: u64, len: u64) -> u64 {
        for j in 0..N {
            let cidx = i * N + j;
            if cidx >= len {
                return ABORTED;
            }
            let bidx = k * N + j;
            if bidx >= len {
                return ABORTED;
            }
            let cidx = cidx as usize;
            c[cidx] = (AIK as i64)
                .wrapping_mul(b[bidx as usize])
                .wrapping_add(c[cidx]);
        }
        0
    }

    /// A row whose index range crosses the checked length `L` must abort at the
    /// first out-of-range index, after the in-range MACs, where `L` is the
    /// register the unrolled search left: `sel` on every early-exit path and 80
    /// only on the path that runs the search out. Resolving `L` to its
    /// layout-last `#80` lets the 4x fast path run the whole row unchecked.
    #[test]
    fn mac_row_against_a_multi_def_checked_length_aborts_at_the_real_length() {
        let name = "mac_row_unroll_rlength";
        let module = build_module(name);
        let b: Vec<i64> = (0..BUF as i64).map(|x| x * 3 + 1).collect();
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let fired = pass_changes(&module, opt_level, PASS);
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the entry's trust-ir signature is (ptr, ptr, u64, u64, u64,
            // u64) -> u64, matching `Kernel`; every row below indexes at most
            // `8*7 + 7 < BUF`, and `result` outlives every call.
            let entry =
                unsafe { result.buffer.get_fn_bound::<Kernel>(name) }.expect("entry symbol");
            for sel in (0..=LIMIT + 1).map(|k| k * STEP).chain([1]) {
                let len = stepped_search_stop(LIMIT, STEP, sel);
                for (i, k) in [(0u64, 0u64), (1, 2), (2, 1), (3, 0), (0, 5), (7, 7)] {
                    let mut got_c: Vec<i64> = (0..BUF as i64).map(|x| 1000 + x).collect();
                    let mut want_c = got_c.clone();
                    let got = entry.as_ref()(got_c.as_mut_ptr(), b.as_ptr(), i, k, AIK, sel);
                    let want = model(&mut want_c, &b, i, k, len);
                    if got != want || got_c != want_c {
                        let at = (0..BUF).find(|&x| got_c[x] != want_c[x]);
                        failures.push(format!(
                            "{opt_level:?} sel={sel} L={len} i={i} k={k}: returned {got:#x}, \
                         expected {want:#x}; first differing c index {at:?} \
                         ({PASS} changes: {fired})"
                        ));
                    }
                }
            }
        }
        assert_no_failures(&failures);
    }
}

mod bitrev {
    //! `neon-bitrev` vectorizes `for i in 0..N { out[i] = a[i].reverse_bits() }`
    //! over two local `[u8; _]` arrays and requires one compile-time `N`: every
    //! `iv`-relative `CmpRR(iv, Nreg)` contributes the pass-local
    //! `const_value(Nreg)`. `const_value` read the last-wins def map, so a
    //! register with several constant definitions resolved to its layout-last
    //! one, and the vector loop then stored 64-byte blocks up to that constant.
    //!
    //! These tests JIT-run, at O2 and O3, a function that copies a caller buffer
    //! into a local array, bit-reverses its first `r` bytes into a zeroed local
    //! array and copies that array back out, with `r` the register a fully
    //! unrolled early-exit search left (`j = STEP, 2*STEP, ..., LIMIT*STEP`, stop
    //! when `j == sel`): one `Movz r, #j` per unrolled exit edge, the layout-last
    //! being `#LIMIT*STEP`. The output is compared with a plain Rust model.
    //! `TRUST_CG_DISABLE_PASSES=neon_bitrev` clears the mismatch.

    use super::*;
    use trust_ir::{BinOp, ICmpOp, Ty, ValueId};
    use trust_ir_build::ModuleBuilder;

    const PASS: &str = "neon-bitrev";
    /// Local array length; every search value is at most this.
    const LEN: u64 = 256;
    /// `sel` value that branches straight to the copy-out. The bit-reverse
    /// loop's exit then has a second predecessor, which keeps `loop-latch-layout`
    /// from rotating it into a do-while that the pass does not match.
    const SKIP: u64 = 0xFFFF;

    /// `fn(src: *const u8, out: *mut u8, sel: u64, _: u64)`:
    ///
    /// ```text
    /// a, o: [u8; LEN]; for k in 0..LEN { a[k] = src[k]; o[k] = 0 }
    /// if sel != SKIP {
    ///     j = 0; loop { j += step; if j == limit*step || j == sel { break } }   // r = j
    ///     for i in 0..r (i <u r) { o[i] = reverse8(a[i]) }   // the bitmanip ladder
    /// }
    /// for k in 0..LEN { out[k] = o[k] }
    /// ```
    fn build_module(name: &str, limit: u64, step: u64) -> trust_ir::Module {
        let mut mb = ModuleBuilder::new(name);
        let u8_ty = mb.add_type(Ty::U8);
        let array = Ty::Array(u8_ty, LEN);
        let fty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::U64, Ty::U64], vec![]);
        let mut fb = mb.function(name, fty);
        let entry = fb.create_block();
        let src = fb.add_block_param(entry, Ty::Ptr);
        let out = fb.add_block_param(entry, Ty::Ptr);
        let sel = fb.add_block_param(entry, Ty::U64);
        let _unused = fb.add_block_param(entry, Ty::U64);
        let fill = fb.create_block();
        let k0 = fb.add_block_param(fill, Ty::U64);
        let fill_body = fb.create_block();
        let filled = fb.create_block();
        let search_entry = fb.create_block();
        let search = fb.create_block();
        let j = fb.add_block_param(search, Ty::U64);
        let search_test = fb.create_block();
        let pre = fb.create_block();
        let r = fb.add_block_param(pre, Ty::U64);
        let header = fb.create_block();
        let iv = fb.add_block_param(header, Ty::U64);
        let body = fb.create_block();
        let done = fb.create_block();
        let drain = fb.create_block();
        let k2 = fb.add_block_param(drain, Ty::U64);
        let drain_body = fb.create_block();
        let finish = fb.create_block();

        fb.switch_to_block(entry);
        let a = fb.alloca(array.clone());
        let o = fb.alloca(array);
        let zero = fb.iconst(Ty::U64, 0);
        fb.br(fill, vec![zero]);

        fb.switch_to_block(fill);
        let len = fb.iconst(Ty::U64, i128::from(LEN));
        let more_fill = fb.icmp(ICmpOp::Ult, Ty::U64, k0, len);
        fb.condbr(more_fill, fill_body, vec![], filled, vec![]);

        fb.switch_to_block(fill_body);
        let src_addr = fb.gep(Ty::U8, src, vec![k0]);
        let byte = fb.load(Ty::U8, src_addr);
        let a_addr = fb.gep(Ty::U8, a, vec![k0]);
        fb.store(Ty::U8, a_addr, byte);
        let o_addr = fb.gep(Ty::U8, o, vec![k0]);
        let zero_byte = fb.iconst(Ty::U8, 0);
        fb.store(Ty::U8, o_addr, zero_byte);
        let one = fb.iconst(Ty::U64, 1);
        let k0_next = fb.add(Ty::U64, k0, one);
        fb.br(fill, vec![k0_next]);

        fb.switch_to_block(filled);
        let skip = fb.iconst(Ty::U64, i128::from(SKIP));
        let is_skip = fb.icmp(ICmpOp::Eq, Ty::U64, sel, skip);
        fb.condbr(is_skip, done, vec![], search_entry, vec![]);

        fb.switch_to_block(search_entry);
        let j0 = fb.iconst(Ty::U64, 0);
        fb.br(search, vec![j0]);

        fb.switch_to_block(search);
        let stride = fb.iconst(Ty::U64, i128::from(step));
        let next = fb.add(Ty::U64, j, stride);
        fb.br(search_test, vec![]);

        fb.switch_to_block(search_test);
        let last = fb.iconst(Ty::U64, i128::from(limit * step));
        let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, last);
        let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, sel);
        let more = fb.binop(BinOp::And, Ty::Bool, trip, not_found);
        fb.condbr(more, search, vec![next], pre, vec![next]);

        fb.switch_to_block(pre);
        let i0 = fb.iconst(Ty::U64, 0);
        fb.br(header, vec![i0]);

        fb.switch_to_block(header);
        let go = fb.icmp(ICmpOp::Ult, Ty::U64, iv, r);
        fb.condbr(go, body, vec![], done, vec![]);

        // `reverse8` as the bridge's `bitmanip_reverse_bits(n=8)` ladder: bit `b`
        // isolated with `& (1 << b)` and moved to bit `7 - b`, OR-combined.
        fb.switch_to_block(body);
        let load_addr = fb.gep(Ty::U8, a, vec![iv]);
        let loaded = fb.load(Ty::U8, load_addr);
        let wide = fb.zext(Ty::U8, Ty::U64, loaded);
        let mut reversed: Option<ValueId> = None;
        for bit in 0..8i64 {
            let mask = fb.iconst(Ty::U64, i128::from(1i64 << bit));
            let isolated = fb.binop(BinOp::And, Ty::U64, wide, mask);
            let placed = if bit < 4 {
                let shift = fb.iconst(Ty::U64, i128::from(7 - 2 * bit));
                fb.binop(BinOp::Shl, Ty::U64, isolated, shift)
            } else {
                let shift = fb.iconst(Ty::U64, i128::from(2 * bit - 7));
                fb.binop(BinOp::LShr, Ty::U64, isolated, shift)
            };
            reversed = Some(match reversed {
                None => placed,
                Some(prev) => fb.binop(BinOp::Or, Ty::U64, prev, placed),
            });
        }
        let narrow = fb.trunc(Ty::U64, Ty::U8, reversed.expect("eight ladder terms"));
        let store_addr = fb.gep(Ty::U8, o, vec![iv]);
        fb.store(Ty::U8, store_addr, narrow);
        let step_one = fb.iconst(Ty::U64, 1);
        let iv_next = fb.add(Ty::U64, iv, step_one);
        fb.br(header, vec![iv_next]);

        fb.switch_to_block(done);
        let k2_start = fb.iconst(Ty::U64, 0);
        fb.br(drain, vec![k2_start]);

        fb.switch_to_block(drain);
        let len2 = fb.iconst(Ty::U64, i128::from(LEN));
        let more_drain = fb.icmp(ICmpOp::Ult, Ty::U64, k2, len2);
        fb.condbr(more_drain, drain_body, vec![], finish, vec![]);

        fb.switch_to_block(drain_body);
        let o_read = fb.gep(Ty::U8, o, vec![k2]);
        let value = fb.load(Ty::U8, o_read);
        let out_addr = fb.gep(Ty::U8, out, vec![k2]);
        fb.store(Ty::U8, out_addr, value);
        let one2 = fb.iconst(Ty::U64, 1);
        let k2_next = fb.add(Ty::U64, k2, one2);
        fb.br(drain, vec![k2_next]);

        fb.switch_to_block(finish);
        fb.ret(vec![]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// Every `sel` that stops the search at each step, one that runs it out and
    /// `SKIP`, at O2 and O3. Returns the failures as text.
    fn probe(name: &str, limit: u64, step: u64) -> Vec<String> {
        let module = build_module(name, limit, step);
        let src: Vec<u8> = (0..LEN as u32)
            .map(|i| (i.wrapping_mul(73) ^ 0x3c) as u8)
            .collect();
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let fired = pass_changes(&module, opt_level, PASS);
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{name} {opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the entry's trust-ir signature is (ptr, ptr, u64, u64) ->
            // (), both buffers hold `LEN` bytes, and `result` outlives every call
            // through `entry`.
            let entry = unsafe {
                result
                    .buffer
                    .get_fn_bound::<extern "C" fn(*const u8, *mut u8, u64, u64)>(name)
            }
            .expect("entry symbol");
            for sel in (0..=limit + 1).map(|k| k * step).chain([1, SKIP]) {
                let r = if sel == SKIP {
                    0
                } else {
                    stepped_search_stop(limit, step, sel) as usize
                };
                let mut got = vec![0xEEu8; LEN as usize];
                entry.as_ref()(src.as_ptr(), got.as_mut_ptr(), sel, 0);
                let mut want = vec![0u8; LEN as usize];
                for (slot, byte) in want.iter_mut().zip(&src).take(r) {
                    *slot = byte.reverse_bits();
                }
                if let Some(at) = (0..LEN as usize).find(|&i| got[i] != want[i]) {
                    failures.push(format!(
                        "{name} {opt_level:?} sel={sel} r={r}: out[{at}] = {:#x}, expected {:#x} \
                     ({PASS} changes: {fired})",
                        got[at], want[at]
                    ));
                }
            }
        }
        failures
    }

    /// The bit-reverse stores exactly `o[0..r)`, where `r` is the register the
    /// unrolled search left: `sel` on every early-exit path and `limit*step` only
    /// on the path that runs the search out. Resolving `r` through the last-wins
    /// def map makes the bound the constant `limit*step`, and the vector loop then
    /// stores whole 64-byte blocks past the real `r`.
    #[test]
    fn bit_reverse_against_a_multi_def_register_bound_stores_only_the_real_range() {
        let mut failures = Vec::new();
        for (name, limit, step) in [
            ("bitrev_rbound_l8_s32", 8u64, 32u64),
            ("bitrev_rbound_l16_s16", 16, 16),
        ] {
            failures.extend(probe(name, limit, step));
        }
        assert_no_failures(&failures);
    }
}

mod bytesum {
    //! `neon-bytesum` vectorizes `acc: u64 += a_u8[i] as u64` over `i <u N` and
    //! requires every `iv`-relative guard to agree on ONE compile-time `N`. A
    //! `CmpRR(iv, Nreg)` guard contributes the pass-local `const_value(Nreg)`
    //! (the `record` loop in `recognize`, and `recognize_chain_guard`'s
    //! `const_cmp` on the forward-chain walk). `const_value` read the last-wins
    //! def map, so a register with several constant definitions resolved to its
    //! layout-last one, and the vector loop's main bound `N - (W-1)` was then a
    //! constant that ignored the real register value.
    //!
    //! These tests JIT-run, at O2 and O3, a byte sum whose loop bound is the
    //! register a fully unrolled early-exit search left (`j = STEP, 2*STEP, ...,
    //! LIMIT*STEP`, stop when `j == sel`): one `Movz r, #k` per unrolled exit
    //! edge, the layout-last being `#LIMIT*STEP`. A bounds check `i <u LEN`
    //! (`LEN == LIMIT*STEP`, never taken) makes the loop the 3-block chain the pass
    //! matches and supplies the agreeing immediate. The result is compared with a
    //! plain Rust model. `TRUST_CG_DISABLE_PASSES=neon_bytesum` clears the
    //! mismatch.

    use super::*;
    use trust_ir::{BinOp, ICmpOp, Ty};
    use trust_ir_build::ModuleBuilder;

    const PASS: &str = "neon-bytesum";
    /// Returned when the (never failing) bounds check fails.
    const TRAPPED: u64 = 0xBAD;

    /// `fn(p: *const u8, sel: u64, _: u64, _: u64) -> u64`:
    ///
    /// ```text
    /// j = 0; loop { j += step; if j == limit*step || j == sel { break } }   // r = j
    /// acc = 0; i = 0
    /// while i <u r {
    ///     if !(i <u limit*step) { return TRAPPED }
    ///     acc += a[i] as u64; i += 1
    /// }
    /// return acc
    /// ```
    fn build_module(name: &str, limit: u64, step: u64) -> trust_ir::Module {
        let len = limit * step;
        let mut mb = ModuleBuilder::new(name);
        let fty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]);
        let mut fb = mb.function(name, fty);
        let entry = fb.create_block();
        let p = fb.add_block_param(entry, Ty::Ptr);
        let sel = fb.add_block_param(entry, Ty::U64);
        let _unused_a = fb.add_block_param(entry, Ty::U64);
        let _unused_b = fb.add_block_param(entry, Ty::U64);
        let search = fb.create_block();
        let j = fb.add_block_param(search, Ty::U64);
        let search_test = fb.create_block();
        let pre = fb.create_block();
        let r = fb.add_block_param(pre, Ty::U64);
        let header = fb.create_block();
        let iv = fb.add_block_param(header, Ty::U64);
        let acc = fb.add_block_param(header, Ty::U64);
        let exit = fb.create_block();
        let exit_acc = fb.add_block_param(exit, Ty::U64);
        let check = fb.create_block();
        let trap = fb.create_block();
        let body = fb.create_block();

        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::U64, 0);
        fb.br(search, vec![zero]);

        fb.switch_to_block(search);
        let stride = fb.iconst(Ty::U64, i128::from(step));
        let next = fb.add(Ty::U64, j, stride);
        fb.br(search_test, vec![]);

        fb.switch_to_block(search_test);
        let last = fb.iconst(Ty::U64, i128::from(len));
        let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, last);
        let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, sel);
        let more = fb.binop(BinOp::And, Ty::Bool, trip, not_found);
        fb.condbr(more, search, vec![next], pre, vec![next]);

        fb.switch_to_block(pre);
        let i0 = fb.iconst(Ty::U64, 0);
        let seed = fb.iconst(Ty::U64, 0);
        fb.br(header, vec![i0, seed]);

        fb.switch_to_block(header);
        let go = fb.icmp(ICmpOp::Ult, Ty::U64, iv, r);
        fb.condbr(go, check, vec![], exit, vec![acc]);

        fb.switch_to_block(exit);
        fb.ret(vec![exit_acc]);

        fb.switch_to_block(check);
        let bound = fb.iconst(Ty::U64, i128::from(len));
        let in_bounds = fb.icmp(ICmpOp::Ult, Ty::U64, iv, bound);
        fb.condbr(in_bounds, body, vec![], trap, vec![]);

        fb.switch_to_block(trap);
        let trapped = fb.iconst(Ty::U64, i128::from(TRAPPED));
        fb.ret(vec![trapped]);

        fb.switch_to_block(body);
        let addr = fb.gep(Ty::U8, p, vec![iv]);
        let byte = fb.load(Ty::U8, addr);
        let wide = fb.zext(Ty::U8, Ty::U64, byte);
        let acc_next = fb.add(Ty::U64, acc, wide);
        let one = fb.iconst(Ty::U64, 1);
        let iv_next = fb.add(Ty::U64, iv, one);
        fb.br(header, vec![iv_next, acc_next]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// Every `sel` that stops the search at each step and one that runs it out,
    /// at O2 and O3. Returns the failures as text.
    fn probe(name: &str, limit: u64, step: u64) -> Vec<String> {
        let module = build_module(name, limit, step);
        let data: Vec<u8> = (0..1024u32)
            .map(|i| (i.wrapping_mul(37) ^ 0x5a) as u8)
            .collect();
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let fired = pass_changes(&module, opt_level, PASS);
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{name} {opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the entry's trust-ir signature is (ptr, u64, u64, u64) ->
            // u64, `data` covers every index the loop reads, and `result` outlives
            // every call through `entry`.
            let entry = unsafe {
                result
                    .buffer
                    .get_fn_bound::<extern "C" fn(*const u8, u64, u64, u64) -> u64>(name)
            }
            .expect("entry symbol");
            for sel in (0..=limit + 1).map(|k| k * step).chain([1]) {
                let r = stepped_search_stop(limit, step, sel);
                let expected: u64 = data[..r as usize].iter().map(|&b| u64::from(b)).sum();
                let got = entry.as_ref()(data.as_ptr(), sel, 0, 0);
                if got != expected {
                    failures.push(format!(
                        "{name} {opt_level:?} sel={sel} r={r}: got {got}, expected {expected} \
                     ({PASS} changes: {fired})"
                    ));
                }
            }
        }
        failures
    }

    /// The sum covers exactly `a[0..r)`, where `r` is the register the unrolled
    /// search left: `sel` on every early-exit path and `limit*step` only on the
    /// path that runs the search out. Resolving `r` through the last-wins def map
    /// makes the bound the constant `limit*step`, and the vector loop then sums
    /// whole 128-byte blocks past the real `r`.
    #[test]
    fn byte_sum_against_a_multi_def_register_bound_sums_only_the_real_range() {
        let mut failures = Vec::new();
        for (name, limit, step) in [
            ("bytesum_rbound_l8_s40", 8u64, 40u64),
            ("bytesum_rbound_l16_s16", 16, 16),
        ] {
            failures.extend(probe(name, limit, step));
        }
        assert_no_failures(&failures);
    }
}

mod iota_fill {
    //! `neon-iota-fill` vectorizes `for i in 0..bound { p[i] = trunc32(i) + inv }`.
    //! `recognize_native_test` turns a header bound REGISTER into
    //! `Bound::Const(n)` when the pass-local `const_value` resolves it, and a
    //! constant bound gets a compile-time main bound `n - 15` with no run-time
    //! check. `const_value` read the last-wins def map
    //! (`crate::effects::build_reaching_def_map`), so a register with several
    //! constant definitions resolved to its layout-last one.
    //!
    //! These tests JIT-run, at O2 and O3, a fill whose bound is the register a
    //! fully unrolled early-exit search left (`j = 1..=LIMIT`, stop when
    //! `j == sel`): one `Movz r, #k` per unrolled exit edge, the layout-last being
    //! `#LIMIT`. The result is compared with a plain Rust model; the fill must
    //! store exactly `p[0..r)` and leave the rest of the buffer untouched.
    //! `TRUST_CG_DISABLE_PASSES=neon_iota_fill` clears the mismatch.

    use super::*;
    use trust_ir::{BinOp, ICmpOp, Ty};
    use trust_ir_build::ModuleBuilder;

    const PASS: &str = "neon-iota-fill";
    /// The search's last value: small enough for O2/O3 to unroll the search fully,
    /// and at least the pass's 16-element block.
    const LIMIT: u64 = 16;
    /// `sel` value that branches from the entry straight to the loop exit. The
    /// exit's second predecessor keeps `loop-latch-layout` from rotating the fill
    /// loop into a do-while that the pass does not match.
    const SKIP: u64 = 0xFFFF;
    const LEN: usize = 64;
    const SENTINEL: u32 = 0xDEAD_BEEF;
    const INV: u64 = 0x100;

    /// `fn(p: *mut u32, sel: u64, inv: u64, _: u64)`:
    ///
    /// ```text
    /// if sel == SKIP { return }
    /// j = 0; loop { j += 1; if j == LIMIT || j == sel { break } }   // r = j
    /// i = 0; while i <u r { p[i] = trunc32(i) + trunc32(inv); i += 1 }
    /// ```
    fn build_module(name: &str) -> trust_ir::Module {
        let mut mb = ModuleBuilder::new(name);
        let fty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::U64, Ty::U64], vec![]);
        let mut fb = mb.function(name, fty);
        let entry = fb.create_block();
        let p = fb.add_block_param(entry, Ty::Ptr);
        let sel = fb.add_block_param(entry, Ty::U64);
        let inv = fb.add_block_param(entry, Ty::U64);
        let _unused = fb.add_block_param(entry, Ty::U64);
        let search = fb.create_block();
        let j = fb.add_block_param(search, Ty::U64);
        let search_test = fb.create_block();
        let pre = fb.create_block();
        let r = fb.add_block_param(pre, Ty::U64);
        let inv_pre = fb.add_block_param(pre, Ty::U32);
        let header = fb.create_block();
        let iv = fb.add_block_param(header, Ty::U64);
        let exit = fb.create_block();
        let body = fb.create_block();

        fb.switch_to_block(entry);
        let inv32 = fb.trunc(Ty::U64, Ty::U32, inv);
        let skip = fb.iconst(Ty::U64, i128::from(SKIP));
        let is_skip = fb.icmp(ICmpOp::Eq, Ty::U64, sel, skip);
        let zero = fb.iconst(Ty::U64, 0);
        let search_entry = fb.create_block();
        fb.condbr(is_skip, exit, vec![], search_entry, vec![]);

        fb.switch_to_block(search_entry);
        fb.br(search, vec![zero]);

        fb.switch_to_block(search);
        let one = fb.iconst(Ty::U64, 1);
        let next = fb.add(Ty::U64, j, one);
        fb.br(search_test, vec![]);

        fb.switch_to_block(search_test);
        let lim = fb.iconst(Ty::U64, i128::from(LIMIT));
        let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, lim);
        let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, sel);
        let more = fb.binop(BinOp::And, Ty::Bool, trip, not_found);
        fb.condbr(more, search, vec![next], pre, vec![next, inv32]);

        fb.switch_to_block(pre);
        let i0 = fb.iconst(Ty::U64, 0);
        fb.br(header, vec![i0]);

        fb.switch_to_block(header);
        let go = fb.icmp(ICmpOp::Ult, Ty::U64, iv, r);
        fb.condbr(go, body, vec![], exit, vec![]);

        fb.switch_to_block(exit);
        fb.ret(vec![]);

        fb.switch_to_block(body);
        let low = fb.trunc(Ty::U64, Ty::U32, iv);
        let value = fb.add(Ty::U32, low, inv_pre);
        let addr = fb.gep(Ty::U32, p, vec![iv]);
        fb.store(Ty::U32, addr, value);
        let step = fb.iconst(Ty::U64, 1);
        let iv_next = fb.add(Ty::U64, iv, step);
        fb.br(header, vec![iv_next]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// Plain-Rust model of the whole function over a `LEN`-element buffer.
    fn model(sel: u64) -> Vec<u32> {
        let mut out = vec![SENTINEL; LEN];
        if sel == SKIP {
            return out;
        }
        let r = stepped_search_stop(LIMIT, 1, sel) as usize;
        for (i, slot) in out.iter_mut().enumerate().take(r) {
            *slot = (i as u32).wrapping_add(INV as u32);
        }
        out
    }

    /// The fill stores exactly `p[0..r)` for every `sel`, where `r` is the
    /// register the unrolled search left: `sel` on every early-exit path and
    /// `LIMIT` only on the path that runs the search out. Resolving `r` through
    /// the last-wins def map makes the bound the constant `LIMIT`, and the vector
    /// block then stores all 16 lanes whatever the real `r` is.
    #[test]
    fn iota_fill_against_a_multi_def_register_bound_stores_only_the_real_range() {
        let name = "iota_fill_rbound";
        let module = build_module(name);
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let fired = pass_changes(&module, opt_level, PASS);
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the entry's trust-ir signature is (ptr, u64, u64, u64) -> (),
            // and `result` outlives every call through `entry`.
            let entry = unsafe {
                result
                    .buffer
                    .get_fn_bound::<extern "C" fn(*mut u32, u64, u64, u64)>(name)
            }
            .expect("entry symbol");
            for sel in (0..=LIMIT + 1).chain([SKIP]) {
                let mut got = vec![SENTINEL; LEN];
                entry.as_ref()(got.as_mut_ptr(), sel, INV, 0);
                let want = model(sel);
                if let Some(at) = (0..LEN).find(|&i| got[i] != want[i]) {
                    failures.push(format!(
                        "{opt_level:?} sel={sel} r={}: p[{at}] = {:#x}, expected {:#x} \
                     ({PASS} changes: {fired})",
                        if sel == SKIP {
                            0
                        } else {
                            stepped_search_stop(LIMIT, 1, sel)
                        },
                        got[at],
                        want[at]
                    ));
                }
            }
        }
        assert_no_failures(&failures);
    }
}

mod map_reverse {
    //! `neon-map` vectorizes descending element-wise map loops only when their low
    //! end is index 0, and decides that from a constant on the exit compare:
    //!
    //! * the ROTATED reverse shape (`recognize_rotated_reverse_header_exit`)
    //!   requires `cmp iv, 1; b.gt <latch>`, accepting a register RHS when
    //!   `mach_util::const_value` resolves it to 1;
    //! * the NATIVE reverse shape (`recognize_two_block`) requires
    //!   `cmp iv, z; b.ge <header>` in the latch, accepting a register `z` when
    //!   `const_value` resolves it to 0.
    //!
    //! `const_value` read the last-wins def map, so a register with several
    //! constant definitions resolved to its layout-last one. These tests JIT-run,
    //! at O2 and O3, both reverse shapes with the low bound in the register a fully
    //! unrolled descending early-exit search left (`j = 7, 6, ..., stop`, stop when
    //! `j == sel`): one `Movz r, #j` per exit edge, the layout-last being `#stop`
    //! (1 or 0). The vector loop then covers the elements below the real bound.
    //! Results are compared with a plain Rust model.
    //! `TRUST_CG_DISABLE_PASSES=neon_map` clears the mismatch.

    use super::*;
    use trust_ir::{ICmpOp, Ty};
    use trust_ir_build::ModuleBuilder;

    const PASS: &str = "neon-map";
    /// Where the descending search starts (its first value is `START - 1`).
    const START: u64 = 8;
    const LEN: usize = 128;
    const COUNTS: [u64; 8] = [0, 1, 2, 5, 17, 40, 64, 100];

    type Kernel = extern "C" fn(*const u8, *mut u8, u64, u64);

    /// ROTATED reverse, `fn(x: *const i32, y: *mut i32, n: u64, sel: u64)`:
    ///
    /// ```text
    /// r = search(sel, stop = 1)
    /// if n == 0 { return }
    /// iv = n; loop { y[iv-1] = x[iv-1] + 5; if iv >s r { iv -= 1 } else { break } }
    /// ```
    fn rotated_reverse_module(name: &str) -> trust_ir::Module {
        let mut mb = ModuleBuilder::new(name);
        let fty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::U64, Ty::U64], vec![]);
        let mut fb = mb.function(name, fty);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::Ptr);
        let y = fb.add_block_param(entry, Ty::Ptr);
        let n = fb.add_block_param(entry, Ty::U64);
        let sel = fb.add_block_param(entry, Ty::U64);
        let pre = fb.create_block();
        let r = fb.add_block_param(pre, Ty::U64);
        let guard = fb.create_block();
        let header = fb.create_block();
        let iv = fb.add_block_param(header, Ty::U64);
        let exit = fb.create_block();

        fb.switch_to_block(entry);
        emit_descending_search(&mut fb, sel, START, 1, pre);

        fb.switch_to_block(pre);
        let zero = fb.iconst(Ty::U64, 0);
        let empty = fb.icmp(ICmpOp::Eq, Ty::U64, n, zero);
        fb.condbr(empty, exit, vec![], guard, vec![]);

        fb.switch_to_block(guard);
        fb.br(header, vec![n]);

        fb.switch_to_block(header);
        let one = fb.iconst(Ty::U64, 1);
        let idx = fb.sub(Ty::U64, iv, one);
        let xa = fb.gep(Ty::I32, x, vec![idx]);
        let xv = fb.load(Ty::I32, xa);
        let five = fb.iconst(Ty::I32, 5);
        let yv = fb.add(Ty::I32, xv, five);
        let ya = fb.gep(Ty::I32, y, vec![idx]);
        fb.store(Ty::I32, ya, yv);
        let more = fb.icmp(ICmpOp::Sgt, Ty::U64, iv, r);
        fb.condbr(more, header, vec![idx], exit, vec![]);

        fb.switch_to_block(exit);
        fb.ret(vec![]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// NATIVE reverse (top-tested, in place), `fn(_: *const i64, a: *mut i64, n:
    /// u64, sel: u64)`:
    ///
    /// ```text
    /// z = search(sel, stop = 0)
    /// iv = n; while iv >=s z { a[iv] = a[iv] + 5; iv -= 1 }
    /// ```
    ///
    /// `loop-latch-layout` rotates it into the do-while whose latch holds
    /// `cmp iv, z; b.ge <header>`, the NATIVE reverse shape.
    fn native_reverse_module(name: &str) -> trust_ir::Module {
        let mut mb = ModuleBuilder::new(name);
        let fty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::U64, Ty::U64], vec![]);
        let mut fb = mb.function(name, fty);
        let entry = fb.create_block();
        let _unused = fb.add_block_param(entry, Ty::Ptr);
        let a = fb.add_block_param(entry, Ty::Ptr);
        let n = fb.add_block_param(entry, Ty::U64);
        let sel = fb.add_block_param(entry, Ty::U64);
        let pre = fb.create_block();
        let z = fb.add_block_param(pre, Ty::U64);
        let header = fb.create_block();
        let iv = fb.add_block_param(header, Ty::U64);
        let body = fb.create_block();
        let exit = fb.create_block();

        fb.switch_to_block(entry);
        emit_descending_search(&mut fb, sel, START, 0, pre);

        fb.switch_to_block(pre);
        fb.br(header, vec![n]);

        fb.switch_to_block(header);
        let go = fb.icmp(ICmpOp::Sge, Ty::U64, iv, z);
        fb.condbr(go, body, vec![], exit, vec![]);

        fb.switch_to_block(body);
        let addr = fb.gep(Ty::I64, a, vec![iv]);
        let value = fb.load(Ty::I64, addr);
        let five = fb.iconst(Ty::I64, 5);
        let bumped = fb.add(Ty::I64, value, five);
        let store_addr = fb.gep(Ty::I64, a, vec![iv]);
        fb.store(Ty::I64, store_addr, bumped);
        let one = fb.iconst(Ty::U64, 1);
        let iv_next = fb.sub(Ty::U64, iv, one);
        fb.br(header, vec![iv_next]);

        fb.switch_to_block(exit);
        fb.ret(vec![]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// The first index where `got` and `want` differ.
    fn first_diff<T: PartialEq>(got: &[T], want: &[T]) -> Option<usize> {
        (0..got.len()).find(|&i| got[i] != want[i])
    }

    /// The rotated reverse loop writes `y[n-1]` down to `y[r-1]` (the last body
    /// runs at `iv == r`), where `r` is the register the unrolled search left:
    /// `sel` on every early-exit path and 1 only on the path that runs the search
    /// out. Resolving `r` to its layout-last `#1` makes the vector loop cover
    /// `y[0..n)` whatever the real `r` is.
    #[test]
    fn rotated_reverse_map_against_a_multi_def_low_bound_stops_at_the_real_bound() {
        let name = "neon_map_rotated_reverse_rbound";
        let module = rotated_reverse_module(name);
        let xs: Vec<i32> = (0..LEN as i32).map(|i| i * 1000 + 3).collect();
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let fired = pass_changes(&module, opt_level, PASS);
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the entry's trust-ir signature is (ptr, ptr, u64, u64) ->
            // (), matching `Kernel`; every `n` below is at most `LEN`, and
            // `result` outlives every call.
            let entry =
                unsafe { result.buffer.get_fn_bound::<Kernel>(name) }.expect("entry symbol");
            for sel in 0..=START {
                let r = descending_search_stop(START, 1, sel);
                for n in COUNTS {
                    let mut got = vec![-1i32; LEN];
                    entry.as_ref()(xs.as_ptr().cast(), got.as_mut_ptr().cast(), n, sel);
                    let mut want = vec![-1i32; LEN];
                    if n != 0 {
                        let mut iv = n;
                        loop {
                            want[(iv - 1) as usize] = xs[(iv - 1) as usize] + 5;
                            if (iv as i64) > (r as i64) {
                                iv -= 1;
                            } else {
                                break;
                            }
                        }
                    }
                    if let Some(at) = first_diff(&got, &want) {
                        failures.push(format!(
                            "{opt_level:?} sel={sel} r={r} n={n}: y[{at}] = {}, expected {} \
                         ({PASS} changes: {fired})",
                            got[at], want[at]
                        ));
                    }
                }
            }
        }
        assert_no_failures(&failures);
    }

    /// The native reverse loop updates `a[n]` down to `a[z]`, where `z` is the
    /// register the unrolled search left: `sel` on every early-exit path and 0
    /// only on the path that runs the search out. Resolving `z` to its
    /// layout-last `#0` makes the vector loop update `a[0..z)` too.
    #[test]
    fn native_reverse_map_against_a_multi_def_low_bound_stops_at_the_real_bound() {
        let name = "neon_map_native_reverse_rbound";
        let module = native_reverse_module(name);
        let initial: Vec<i64> = (0..LEN as i64).map(|i| i * 1000 + 3).collect();
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let fired = pass_changes(&module, opt_level, PASS);
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the entry's trust-ir signature is (ptr, ptr, u64, u64) ->
            // (), matching `Kernel`; every `n` below is below `LEN`, and `result`
            // outlives every call.
            let entry =
                unsafe { result.buffer.get_fn_bound::<Kernel>(name) }.expect("entry symbol");
            for sel in 0..=START {
                let z = descending_search_stop(START, 0, sel);
                for n in COUNTS {
                    let mut got = initial.clone();
                    entry.as_ref()(initial.as_ptr().cast(), got.as_mut_ptr().cast(), n, sel);
                    let mut want = initial.clone();
                    let mut iv = n as i64;
                    while iv >= z as i64 {
                        want[iv as usize] += 5;
                        iv -= 1;
                    }
                    if let Some(at) = first_diff(&got, &want) {
                        failures.push(format!(
                            "{opt_level:?} sel={sel} z={z} n={n}: a[{at}] = {}, expected {} \
                         ({PASS} changes: {fired})",
                            got[at], want[at]
                        ));
                    }
                }
            }
        }
        assert_no_failures(&failures);
    }
}

mod predsum_chain {
    //! `neon-predsum`'s forward-chain path (`PredSumChainRecognized`) vectorizes
    //! `while i <u N { if a[i] > t { s += a[i] } ; i += 1 }` and requires `N` to be
    //! a compile-time constant: `apply_chain` materializes `main_bound = N - (W-1)`
    //! with no run-time check. A header bound REGISTER (`ChainBound::Reg`) is
    //! accepted when `mach_util::const_value` resolves it, and `const_value` read
    //! the last-wins def map, so a register with several constant definitions
    //! resolved to its layout-last one.
    //!
    //! These tests JIT-run, at O2 and O3, the chain loop with its bound in the
    //! register a fully unrolled early-exit search left (`j = 2, 4, ..., 32`, stop
    //! when `j == sel`): one `Movz r, #j` per unrolled exit edge, the layout-last
    //! being `#32`. The sum is compared with a plain Rust model.
    //! `TRUST_CG_DISABLE_PASSES=neon_predsum` clears the mismatch.

    use super::*;
    use trust_ir::{BinOp, ICmpOp, Ty};
    use trust_ir_build::ModuleBuilder;

    const PASS: &str = "neon-predsum";
    /// Unrolled search steps; small enough for O2/O3 to unroll the search fully.
    const LIMIT: u64 = 16;
    /// Search stride: the layout-last bound `LIMIT * STEP = 32` covers a whole
    /// vector block.
    const STEP: u64 = 2;
    const THRESHOLD: i32 = 10;

    /// `fn(p: *const i32, sel: u64, t: u64, _: u64) -> u64`:
    ///
    /// ```text
    /// j = 0; loop { j += STEP; if j == LIMIT*STEP || j == sel { break } }   // r = j
    /// s: i32 = 0; i = 0
    /// while i <u r { if p[i] >s t { s += p[i] }; i += 1 }
    /// return zext(s)
    /// ```
    fn build_module(name: &str) -> trust_ir::Module {
        let mut mb = ModuleBuilder::new(name);
        let fty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]);
        let mut fb = mb.function(name, fty);
        let entry = fb.create_block();
        let p = fb.add_block_param(entry, Ty::Ptr);
        let sel = fb.add_block_param(entry, Ty::U64);
        let t_arg = fb.add_block_param(entry, Ty::U64);
        let _unused = fb.add_block_param(entry, Ty::U64);
        let search = fb.create_block();
        let j = fb.add_block_param(search, Ty::U64);
        let search_test = fb.create_block();
        let pre = fb.create_block();
        let r = fb.add_block_param(pre, Ty::U64);
        let t = fb.add_block_param(pre, Ty::I32);
        let header = fb.create_block();
        let iv = fb.add_block_param(header, Ty::U64);
        let acc = fb.add_block_param(header, Ty::I32);
        let exit = fb.create_block();
        let exit_acc = fb.add_block_param(exit, Ty::I32);
        let compare = fb.create_block();
        let then_block = fb.create_block();
        let latch = fb.create_block();
        let joined = fb.add_block_param(latch, Ty::I32);

        fb.switch_to_block(entry);
        let t32 = fb.trunc(Ty::U64, Ty::I32, t_arg);
        let zero = fb.iconst(Ty::U64, 0);
        fb.br(search, vec![zero]);

        fb.switch_to_block(search);
        let stride = fb.iconst(Ty::U64, i128::from(STEP));
        let next = fb.add(Ty::U64, j, stride);
        fb.br(search_test, vec![]);

        fb.switch_to_block(search_test);
        let last = fb.iconst(Ty::U64, i128::from(LIMIT * STEP));
        let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, last);
        let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, sel);
        let more = fb.binop(BinOp::And, Ty::Bool, trip, not_found);
        fb.condbr(more, search, vec![next], pre, vec![next, t32]);

        fb.switch_to_block(pre);
        let i0 = fb.iconst(Ty::U64, 0);
        let seed = fb.iconst(Ty::I32, 0);
        fb.br(header, vec![i0, seed]);

        fb.switch_to_block(header);
        let go = fb.icmp(ICmpOp::Ult, Ty::U64, iv, r);
        fb.condbr(go, compare, vec![], exit, vec![acc]);

        fb.switch_to_block(exit);
        let wide = fb.zext(Ty::I32, Ty::U64, exit_acc);
        fb.ret(vec![wide]);

        fb.switch_to_block(compare);
        let addr = fb.gep(Ty::I32, p, vec![iv]);
        let value = fb.load(Ty::I32, addr);
        let above = fb.icmp(ICmpOp::Sgt, Ty::I32, value, t);
        fb.condbr(above, then_block, vec![], latch, vec![acc]);

        fb.switch_to_block(then_block);
        let reload_addr = fb.gep(Ty::I32, p, vec![iv]);
        let reload = fb.load(Ty::I32, reload_addr);
        let added = fb.add(Ty::I32, acc, reload);
        fb.br(latch, vec![added]);

        fb.switch_to_block(latch);
        let one = fb.iconst(Ty::U64, 1);
        let iv_next = fb.add(Ty::U64, iv, one);
        fb.br(header, vec![iv_next, joined]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// The conditional sum covers exactly `p[0..r)`, where `r` is the register
    /// the unrolled search left: `sel` on every early-exit path and 32 only on the
    /// path that runs the search out. Resolving `r` through the last-wins def map
    /// makes the chain bound the constant 32, and the vector loop then sums a
    /// whole block past the real `r`.
    #[test]
    fn predicated_sum_chain_against_a_multi_def_register_bound_sums_only_the_real_range() {
        let name = "predsum_chain_rbound";
        let module = build_module(name);
        let data: Vec<i32> = (0..128i32)
            .map(|i| if i % 3 == 0 { -(i + 1) } else { i * 7 + 1 })
            .collect();
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let fired = pass_changes(&module, opt_level, PASS);
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the entry's trust-ir signature is (ptr, u64, u64, u64) ->
            // u64, `data` covers every index the loop reads, and `result` outlives
            // every call through `entry`.
            let entry = unsafe {
                result
                    .buffer
                    .get_fn_bound::<extern "C" fn(*const i32, u64, u64, u64) -> u64>(name)
            }
            .expect("entry symbol");
            for sel in (0..=LIMIT + 1).map(|k| k * STEP).chain([1]) {
                let r = stepped_search_stop(LIMIT, STEP, sel) as usize;
                let sum = data[..r]
                    .iter()
                    .filter(|&&v| v > THRESHOLD)
                    .fold(0i32, |acc, &v| acc.wrapping_add(v));
                let expected = u64::from(sum as u32);
                let got = entry.as_ref()(data.as_ptr(), sel, THRESHOLD as u64, 0);
                if got != expected {
                    failures.push(format!(
                        "{opt_level:?} sel={sel} r={r}: got {got}, expected {expected} \
                     ({PASS} changes: {fired})"
                    ));
                }
            }
        }
        assert_no_failures(&failures);
    }
}

mod swap_range_guard {
    //! `swap-range-guard` splices a guarded fast path in front of the
    //! bounds-checked crosswise swap loop
    //! `while x <u C { swap(a[y*S+x], a[x*S+y]) }` (four `idx <u K` checks), and
    //! the fast path runs exactly `C - x0` iterations with no checks.
    //! `recognize_header` reads `C` from `CmpRR(x, Creg)`; its pass-local
    //! `const_value` stripped copies only through single-def registers and
    //! then read the last-wins def map, so a bound register with several constant
    //! definitions resolved to its layout-last one.
    //!
    //! These tests JIT-run, at O2 and O3, the swap loop with its bound in the
    //! register a fully unrolled early-exit search left (`j = 1..=8`, stop when
    //! `j == sel`): one `Movz C, #j` per unrolled exit edge, the layout-last being
    //! `#8`. The return value and the whole array are compared with a plain Rust
    //! model. `TRUST_CG_DISABLE_PASSES=swap_range_guard` clears the mismatch.

    use super::*;
    use trust_ir::{BinOp, ICmpOp, Ty};
    use trust_ir_build::{FunctionBuilder, ModuleBuilder};

    const PASS: &str = "swap-range-guard";
    /// The search's last value; small enough for O2/O3 to unroll it fully.
    const LIMIT: u64 = 8;
    /// Row stride `S` and checked length `K` of the 8x8 matrix.
    const S: u64 = 8;
    const K: u64 = 64;
    const ABORTED: u64 = u64::MAX;
    const BUF: usize = 80;

    type Kernel = extern "C" fn(*mut i32, u64, u64, u64) -> u64;

    /// `fn(a: *mut i32, y: u64, x0: u64, sel: u64) -> u64`:
    ///
    /// ```text
    /// j = 0; loop { j += 1; if j == LIMIT || j == sel { break } }   // C = j
    /// x = x0
    /// while x <u C {
    ///     i1 = y*S + x;  if !(i1 <u K) { return ABORTED }; t1 = a[i1]
    ///     i2 = x*S + y;  if !(i2 <u K) { return ABORTED }; t2 = a[i2]
    ///     i1 = x + S*y;  if !(i1 <u K) { return ABORTED }; a[i1] = t2
    ///     i2 = y + S*x;  if !(i2 <u K) { return ABORTED }; a[i2] = t1
    ///     x += 1
    /// }
    /// return 0
    /// ```
    ///
    /// The recomputed indices are spelled with swapped operands so they survive
    /// CSE as the bridge's literal recomputations do.
    fn build_module(name: &str) -> trust_ir::Module {
        let mut mb = ModuleBuilder::new(name);
        let fty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]);
        let mut fb = mb.function(name, fty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::Ptr);
        let y = fb.add_block_param(entry, Ty::U64);
        let x0 = fb.add_block_param(entry, Ty::U64);
        let sel = fb.add_block_param(entry, Ty::U64);
        let search = fb.create_block();
        let j = fb.add_block_param(search, Ty::U64);
        let search_test = fb.create_block();
        let pre = fb.create_block();
        let bound = fb.add_block_param(pre, Ty::U64);
        let header = fb.create_block();
        let x = fb.add_block_param(header, Ty::U64);
        let exit = fb.create_block();
        let load_first = fb.create_block();
        let load_second = fb.create_block();
        let store_first = fb.create_block();
        let store_second = fb.create_block();
        let latch = fb.create_block();
        let abort = fb.create_block();
        let stride = |fb: &mut FunctionBuilder<'_>| fb.iconst(Ty::U64, i128::from(S));
        let length = |fb: &mut FunctionBuilder<'_>| fb.iconst(Ty::U64, i128::from(K));

        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::U64, 0);
        fb.br(search, vec![zero]);

        fb.switch_to_block(search);
        let one = fb.iconst(Ty::U64, 1);
        let next = fb.add(Ty::U64, j, one);
        fb.br(search_test, vec![]);

        fb.switch_to_block(search_test);
        let last = fb.iconst(Ty::U64, i128::from(LIMIT));
        let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, last);
        let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, sel);
        let more = fb.binop(BinOp::And, Ty::Bool, trip, not_found);
        fb.condbr(more, search, vec![next], pre, vec![next]);

        fb.switch_to_block(pre);
        fb.br(header, vec![x0]);

        fb.switch_to_block(header);
        let go = fb.icmp(ICmpOp::Ult, Ty::U64, x, bound);
        fb.condbr(go, load_first, vec![], exit, vec![]);

        fb.switch_to_block(exit);
        let ok = fb.iconst(Ty::U64, 0);
        fb.ret(vec![ok]);

        fb.switch_to_block(load_first);
        let s1 = stride(&mut fb);
        let ys = fb.mul(Ty::U64, y, s1);
        let i1 = fb.add(Ty::U64, ys, x);
        let k1 = length(&mut fb);
        let ok1 = fb.icmp(ICmpOp::Ult, Ty::U64, i1, k1);
        fb.condbr(ok1, load_second, vec![], abort, vec![]);

        fb.switch_to_block(load_second);
        let a1 = fb.gep(Ty::I32, a, vec![i1]);
        let t1 = fb.load(Ty::I32, a1);
        let s2 = stride(&mut fb);
        let xs = fb.mul(Ty::U64, x, s2);
        let i2 = fb.add(Ty::U64, xs, y);
        let k2 = length(&mut fb);
        let ok2 = fb.icmp(ICmpOp::Ult, Ty::U64, i2, k2);
        fb.condbr(ok2, store_first, vec![], abort, vec![]);

        fb.switch_to_block(store_first);
        let a2 = fb.gep(Ty::I32, a, vec![i2]);
        let t2 = fb.load(Ty::I32, a2);
        let s3 = stride(&mut fb);
        let sy = fb.mul(Ty::U64, s3, y);
        let i1_again = fb.add(Ty::U64, x, sy);
        let k3 = length(&mut fb);
        let ok3 = fb.icmp(ICmpOp::Ult, Ty::U64, i1_again, k3);
        fb.condbr(ok3, store_second, vec![], abort, vec![]);

        fb.switch_to_block(store_second);
        let a3 = fb.gep(Ty::I32, a, vec![i1_again]);
        fb.store(Ty::I32, a3, t2);
        let s4 = stride(&mut fb);
        let sx = fb.mul(Ty::U64, s4, x);
        let i2_again = fb.add(Ty::U64, y, sx);
        let k4 = length(&mut fb);
        let ok4 = fb.icmp(ICmpOp::Ult, Ty::U64, i2_again, k4);
        fb.condbr(ok4, latch, vec![], abort, vec![]);

        fb.switch_to_block(latch);
        let a4 = fb.gep(Ty::I32, a, vec![i2_again]);
        fb.store(Ty::I32, a4, t1);
        let step = fb.iconst(Ty::U64, 1);
        let x_next = fb.add(Ty::U64, x, step);
        fb.br(header, vec![x_next]);

        fb.switch_to_block(abort);
        let aborted = fb.iconst(Ty::U64, i128::from(ABORTED));
        fb.ret(vec![aborted]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// Plain-Rust model of the swap loop; returns the function's result.
    fn model(a: &mut [i32], y: u64, x0: u64, bound: u64) -> u64 {
        let mut x = x0;
        while x < bound {
            let i1 = y * S + x;
            if i1 >= K {
                return ABORTED;
            }
            let t1 = a[i1 as usize];
            let i2 = x * S + y;
            if i2 >= K {
                return ABORTED;
            }
            let t2 = a[i2 as usize];
            a[i1 as usize] = t2;
            a[i2 as usize] = t1;
            x += 1;
        }
        0
    }

    /// The loop swaps exactly the pairs for `x in [x0, C)`, where `C` is the
    /// register the unrolled search left: `sel` on every early-exit path and 8
    /// only on the path that runs the search out. Resolving `C` to its
    /// layout-last `#8` makes the fast path swap every pair up to `x == 8`.
    #[test]
    fn swap_loop_against_a_multi_def_register_bound_swaps_only_the_real_range() {
        let name = "swap_range_guard_rbound";
        let module = build_module(name);
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let fired = pass_changes(&module, opt_level, PASS);
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the entry's trust-ir signature is (ptr, u64, u64, u64) ->
            // u64, matching `Kernel`; every access is checked against `K < BUF`,
            // and `result` outlives every call.
            let entry =
                unsafe { result.buffer.get_fn_bound::<Kernel>(name) }.expect("entry symbol");
            for sel in 0..=LIMIT + 1 {
                let bound = stepped_search_stop(LIMIT, 1, sel);
                for (y, x0) in [(0u64, 1u64), (1, 2), (2, 3), (0, 0), (3, 1)] {
                    let mut got_a: Vec<i32> = (0..BUF as i32).collect();
                    let mut want_a = got_a.clone();
                    let got = entry.as_ref()(got_a.as_mut_ptr(), y, x0, sel);
                    let want = model(&mut want_a, y, x0, bound);
                    if got != want || got_a != want_a {
                        let at = (0..BUF).find(|&i| got_a[i] != want_a[i]);
                        failures.push(format!(
                            "{opt_level:?} sel={sel} C={bound} y={y} x0={x0}: returned {got:#x}, \
                         expected {want:#x}; first differing index {at:?} \
                         ({PASS} changes: {fired})"
                        ));
                    }
                }
            }
        }
        assert_no_failures(&failures);
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
