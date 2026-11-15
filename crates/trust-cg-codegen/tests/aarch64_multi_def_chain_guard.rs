// trust-cg-codegen - chain body guards against a register with several constant definitions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Body-guard coverage in the forward-chain vectorizers, against a guard
//! register written with different constants on different paths.
//!
//! The invariant these rows pin: a register written with different constants
//! on different paths is not one constant. Machine IR is not SSA, and
//! `effects::build_reaching_def_map` keeps one definition per vreg, the
//! layout-last one; a resolver that reads it takes that definition's value on
//! every path. `mach_util::const_value` and the pass-local resolvers (which
//! delegate to `mach_util::copied_const`) give a register a constant only
//! when EVERY definition of it writes that constant, so the multi-def rows
//! below are refused rather than read as their layout-last value.
//!
//! Each vectorizer admits a body guard `i <u r` (or a header test `i <u r`)
//! as covered by, or equal to, the loop's bound when it resolves `r` to that
//! bound. The shapes, one module per pass:
//!
//! * `r` is the stop index of an early-exit search that O2/O3 unroll fully:
//!   one `Movz r, #k` per exit edge, the loop's bound laid out last
//!   (`bitrev`, `bytesum`, `find`, `minmax`, `predsum`, `map`), against an
//!   immediate header bound or a register holding it, with the guard leaving
//!   to its own block or to the loop's exit;
//! * the guard on the taken arm of a conditional sum (`predsum`);
//! * `r` on the header side against an immediate guard, `r` a phi of two
//!   constants through a diamond, and `r` a constant an outer loop carries
//!   (`map`).
//!
//! Every row JIT-runs at O2 and O3, compares with a plain Rust model of the
//! same loops, and reports how often the pass changed the function. A test's
//! doc names what a resolver that reads the layout-last definition does with
//! its shape: the misreading the row pins against. The rows are bounded host
//! executions; they are tests, not a proof.
#![cfg(target_arch = "aarch64")]

#[path = "common/unreachable_blocks.rs"]
mod unreachable_blocks;

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;

/// The host triple the metrics pipeline prepares for.
const TRIPLE: &str = if cfg!(target_os = "linux") {
    "aarch64-unknown-linux-gnu"
} else {
    "aarch64-apple-darwin"
};

/// Added to an early exit's result so it differs from the loop exit's.
const EARLY: u64 = 1000;
/// Scales the induction folded into an early exit's result.
const IV_SCALE: u64 = 1_000_003;

/// How the body guard leaves the loop.
#[derive(Clone, Copy, Debug)]
enum GuardExit {
    /// To its own block, whose result folds `i * IV_SCALE` (and the
    /// accumulator, when the loop has one) in and adds `EARLY`.
    Early,
    /// To the loop's exit, or to a block returning a fixed value.
    Shared,
}

/// Changing runs of `pass` when `module` is prepared at `opt_level` with
/// every pass enabled (an explicit empty disable list).
fn pass_changes(module: &trust_ir::Module, opt_level: OptLevel, pass: &str) -> u32 {
    let module = unreachable_blocks::without_unreachable_blocks(module);
    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
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
/// Each shape builds both of its guard-exit blocks and branches to one of
/// them; the other is dropped (`unreachable_blocks`), as trust-ir refuses a
/// block no edge reaches at every ingestion entry (WS7.3).
fn jit(module: &trust_ir::Module, opt_level: OptLevel) -> Result<JitCompilationResult, String> {
    let module = unreachable_blocks::without_unreachable_blocks(module);
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(&module, &HashMap::new())
        .map_err(|error| error.to_string())
}

/// The run-time stop index of `j = lo; loop { j += 1; if j == hi || j == sel
/// { break } }`, which is in `lo+1..=hi`. Fully unrolled, the search writes
/// one `Movz r, #k` per exit edge, `#hi` laid out last.
fn search_stop(lo: u64, hi: u64, sel: u64) -> u64 {
    let mut j = lo;
    loop {
        j += 1;
        if j == hi || j == sel {
            break j;
        }
    }
}

/// Every stop index of a `lo..hi` search, the `sel` values that miss it, and
/// `0..=2`.
fn search_sels(lo: u64, hi: u64) -> Vec<u64> {
    let mut sels: Vec<u64> = (0..=2).collect();
    sels.extend(lo.max(3)..=hi + 1);
    sels
}

/// `len` successive states of the xorshift32 (13, 17, 5) generator after
/// `seed`.
fn xorshift32(seed: u32, len: usize) -> Vec<u32> {
    let mut x = seed;
    (0..len)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 17;
            x ^= x << 5;
            x
        })
        .collect()
}

/// Fails the test with every collected mismatch.
fn assert_no_failures(failures: &[String]) {
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

mod bitrev {
    //! `neon-bitrev` (`Recognized::recognize`) takes every `iv <u x` compare in
    //! the loop as the loop's single constant bound when its pass-local
    //! `const_value(x)` agrees, and its loop contract admits a guard `i <u r` as
    //! the loop bound (`is_bound`) or as covering it (`covers_loop_bound`) by the
    //! same resolver. That resolver stopped copy-stripping at a multi-def register
    //! but then read the register's last-wins def, so a register with one `Movz`
    //! per incoming path resolved to whichever definition was laid out last.
    //!
    //! These tests JIT-run, at O2 and O3, the per-byte bit-reverse map over two
    //! `[u8; N]` stack arrays,
    //! `while i <u N { if !(i <u r) exit; out[i] = in[i].reverse_bits(); i += 1 }`,
    //! with the bridge's isolate/shift/OR ladder for `reverse_bits`, whose guard
    //! limit `r` is the stop index of an early-exit search that O2/O3 unroll
    //! fully (one `Movz r, #k` per exit edge, `#N` laid out last). They compare
    //! the returned value and the copied-out `out` with a plain Rust model.

    use super::*;
    use trust_ir::{BinOp, ICmpOp, Ty};
    use trust_ir_build::ModuleBuilder;

    /// The pass under test, by its pass-manager name.
    const PASS: &str = "neon-bitrev";
    /// Returned when the header test exits the loop.
    const DONE: u64 = 77;
    /// What `out` holds before the map writes it.
    const UNTOUCHED: u8 = 0xAA;

    /// One row: `r = j` where `j = lo; loop { j += 1; if j == hi || j == sel {
    /// break } }` (so `r` in `lo+1..=hi`, defs `Movz r, #lo+1 ..= #hi`), and the
    /// header bound and array length `hi`.
    #[derive(Clone, Copy, Debug)]
    struct Case {
        name: &'static str,
        lo: u64,
        hi: u64,
        exit: GuardExit,
    }

    /// `fn(src: *const u8, dst: *mut u8, sel: u64, _: u64) -> u64`:
    ///
    /// ```text
    /// let mut inp = [0u8; N]; let mut out = [0u8; N];
    /// for k in 0..N { inp[k] = src[k]; out[k] = UNTOUCHED }
    /// r = <search stop>
    /// i = 0
    /// res = loop {
    ///     if !(i <u N) { break DONE }
    ///     if !(i <u r) { break early(i) }          // or `break DONE`
    ///     out[i] = reverse8(inp[i])                // the isolate/shift/OR ladder
    ///     i += 1
    /// }
    /// for k in 0..N { dst[k] = out[k] }
    /// return res
    /// ```
    fn build_module(case: &Case) -> trust_ir::Module {
        let name = case.name;
        let n = case.hi;
        let mut mb = ModuleBuilder::new(name);
        let byte_ty = mb.add_type(Ty::U8);
        let array_ty = Ty::Array(byte_ty, n);
        let fty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::U64, Ty::U64], vec![Ty::U64]);
        let mut fb = mb.function(name, fty);
        let entry = fb.create_block();
        let src = fb.add_block_param(entry, Ty::Ptr);
        let dst = fb.add_block_param(entry, Ty::Ptr);
        let sel = fb.add_block_param(entry, Ty::U64);
        let _unused = fb.add_block_param(entry, Ty::U64);
        let fill = fb.create_block();
        let k = fb.add_block_param(fill, Ty::U64);
        let fill_body = fb.create_block();
        let search = fb.create_block();
        let j = fb.add_block_param(search, Ty::U64);
        let search_test = fb.create_block();
        let pre = fb.create_block();
        let r = fb.add_block_param(pre, Ty::U64);
        let header = fb.create_block();
        let iv = fb.add_block_param(header, Ty::U64);
        let guard = fb.create_block();
        let body = fb.create_block();
        let early = fb.create_block();
        let early_iv = fb.add_block_param(early, Ty::U64);
        let done = fb.create_block();
        let res = fb.add_block_param(done, Ty::U64);
        let copy = fb.create_block();
        let c = fb.add_block_param(copy, Ty::U64);
        let copy_body = fb.create_block();
        let ret = fb.create_block();

        fb.switch_to_block(entry);
        let inp = fb.alloca(array_ty.clone());
        let out = fb.alloca(array_ty);
        let zero = fb.iconst(Ty::U64, 0);
        let seed = fb.iconst(Ty::U64, i128::from(case.lo));
        fb.br(fill, vec![zero]);

        fb.switch_to_block(fill);
        let n_fill = fb.iconst(Ty::U64, i128::from(n));
        let more_fill = fb.icmp(ICmpOp::Ult, Ty::U64, k, n_fill);
        fb.condbr(more_fill, fill_body, vec![], search, vec![seed]);

        fb.switch_to_block(fill_body);
        let src_at = fb.gep(Ty::U8, src, vec![k]);
        let byte_in = fb.load(Ty::U8, src_at);
        let inp_at = fb.gep(Ty::U8, inp, vec![k]);
        fb.store(Ty::U8, inp_at, byte_in);
        let out_init_at = fb.gep(Ty::U8, out, vec![k]);
        let untouched = fb.iconst(Ty::U8, i128::from(UNTOUCHED));
        fb.store(Ty::U8, out_init_at, untouched);
        let one_fill = fb.iconst(Ty::U64, 1);
        let k_next = fb.add(Ty::U64, k, one_fill);
        fb.br(fill, vec![k_next]);

        fb.switch_to_block(search);
        let one = fb.iconst(Ty::U64, 1);
        let next = fb.add(Ty::U64, j, one);
        fb.br(search_test, vec![]);

        fb.switch_to_block(search_test);
        let stop = fb.iconst(Ty::U64, i128::from(case.hi));
        let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, stop);
        let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, sel);
        let more = fb.binop(BinOp::And, Ty::Bool, trip, not_found);
        fb.condbr(more, search, vec![next], pre, vec![next]);

        fb.switch_to_block(pre);
        let i0 = fb.iconst(Ty::U64, 0);
        fb.br(header, vec![i0]);

        fb.switch_to_block(header);
        let n_loop = fb.iconst(Ty::U64, i128::from(n));
        let go = fb.icmp(ICmpOp::Ult, Ty::U64, iv, n_loop);
        let done_header = fb.iconst(Ty::U64, i128::from(DONE));
        fb.condbr(go, guard, vec![], done, vec![done_header]);

        fb.switch_to_block(guard);
        let in_range = fb.icmp(ICmpOp::Ult, Ty::U64, iv, r);
        match case.exit {
            GuardExit::Early => fb.condbr(in_range, body, vec![], early, vec![iv]),
            GuardExit::Shared => {
                let done_guard = fb.iconst(Ty::U64, i128::from(DONE));
                fb.condbr(in_range, body, vec![], done, vec![done_guard]);
            }
        }

        // `bitmanip_reverse_bits(n=8)`: bit `b` of the zero-extended byte moves
        // to bit `7-b` (`shl 7-2b` for `b < 4`, `lshr 2b-7` otherwise), OR-combined.
        fb.switch_to_block(body);
        let inp_i = fb.gep(Ty::U8, inp, vec![iv]);
        let byte = fb.load(Ty::U8, inp_i);
        let wide = fb.zext(Ty::U8, Ty::I64, byte);
        let mut acc = None;
        for bit in 0..8i128 {
            let mask = fb.iconst(Ty::I64, 1 << bit);
            let isolated = fb.binop(BinOp::And, Ty::I64, wide, mask);
            let placed = if bit < 4 {
                let sh = fb.iconst(Ty::I64, 7 - 2 * bit);
                fb.binop(BinOp::Shl, Ty::I64, isolated, sh)
            } else {
                let sh = fb.iconst(Ty::I64, 2 * bit - 7);
                fb.binop(BinOp::LShr, Ty::I64, isolated, sh)
            };
            acc = Some(match acc {
                None => placed,
                Some(prev) => fb.binop(BinOp::Or, Ty::I64, prev, placed),
            });
        }
        let reversed = fb.trunc(Ty::I64, Ty::U8, acc.expect("eight ladder terms"));
        let out_i = fb.gep(Ty::U8, out, vec![iv]);
        fb.store(Ty::U8, out_i, reversed);
        let step = fb.iconst(Ty::U64, 1);
        let iv_next = fb.add(Ty::U64, iv, step);
        fb.br(header, vec![iv_next]);

        fb.switch_to_block(early);
        let scale = fb.iconst(Ty::U64, i128::from(IV_SCALE));
        let scaled = fb.mul(Ty::U64, early_iv, scale);
        let bias = fb.iconst(Ty::U64, i128::from(EARLY));
        let early_result = fb.add(Ty::U64, scaled, bias);
        fb.br(done, vec![early_result]);

        fb.switch_to_block(done);
        fb.br(copy, vec![zero]);

        fb.switch_to_block(copy);
        let n_copy = fb.iconst(Ty::U64, i128::from(n));
        let more_copy = fb.icmp(ICmpOp::Ult, Ty::U64, c, n_copy);
        fb.condbr(more_copy, copy_body, vec![], ret, vec![]);

        fb.switch_to_block(copy_body);
        let out_c = fb.gep(Ty::U8, out, vec![c]);
        let byte_out = fb.load(Ty::U8, out_c);
        let dst_c = fb.gep(Ty::U8, dst, vec![c]);
        fb.store(Ty::U8, dst_c, byte_out);
        let one_copy = fb.iconst(Ty::U64, 1);
        let c_next = fb.add(Ty::U64, c, one_copy);
        fb.br(copy, vec![c_next]);

        fb.switch_to_block(ret);
        fb.ret(vec![res]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// Plain-Rust model of the whole function; `out` receives the copied-out
    /// array.
    fn model(src: &[u8], out: &mut [u8], case: &Case, sel: u64) -> u64 {
        let r = search_stop(case.lo, case.hi, sel);
        out.fill(UNTOUCHED);
        for i in 0..case.hi {
            if i >= r {
                return match case.exit {
                    GuardExit::Early => i.wrapping_mul(IV_SCALE).wrapping_add(EARLY),
                    GuardExit::Shared => DONE,
                };
            }
            out[i as usize] = src[i as usize].reverse_bits();
        }
        DONE
    }

    /// Deterministic bytes.
    fn data_for(len: usize) -> Vec<u8> {
        xorshift32(0x0BAD_F00D, len)
            .into_iter()
            .map(|x| x as u8)
            .collect()
    }

    /// Every stop index of the search (and the `sel` values that miss it) at O2
    /// and O3. Returns the failures as text.
    fn probe(case: &Case) -> Vec<String> {
        let name = case.name;
        let module = build_module(case);
        let n = case.hi as usize;
        let src = data_for(n);
        let sels = search_sels(case.lo, case.hi);
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let fired = pass_changes(&module, opt_level, PASS);
            eprintln!("{name} {opt_level:?}: {PASS} changed the function {fired} time(s)");
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{name} {opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the entry's trust-ir signature is (ptr, ptr, u64, u64) ->
            // u64; `src` and `dst` hold `N` bytes, the function reads and writes
            // exactly `N` of each, and `result` outlives every call.
            let entry = unsafe {
                result
                    .buffer
                    .get_fn_bound::<extern "C" fn(*const u8, *mut u8, u64, u64) -> u64>(name)
            }
            .expect("entry symbol");
            for &sel in &sels {
                let mut want = vec![0u8; n];
                let expected = model(&src, &mut want, case, sel);
                let mut got_out = vec![0u8; n];
                let got = entry.as_ref()(src.as_ptr(), got_out.as_mut_ptr(), sel, 0);
                if got != expected || got_out != want {
                    let first = (0..n).find(|&x| got_out[x] != want[x]);
                    failures.push(format!(
                        "{name} {opt_level:?} ({PASS} fired {fired}x) sel={sel}: got {got:#x}, \
                     expected {expected:#x}; first differing byte {first:?}"
                    ));
                }
            }
        }
        failures
    }

    /// Header `i <u N` (immediate), body guard `i <u r`: the pass-local
    /// `const_value(r)` reads `r`'s layout-last `Movz r, #N`, so the guard joins
    /// the single bound `N` and the loop contract admits it, and the vector map
    /// writes `out[r..N)` and skips the guard's exit.
    #[test]
    fn bitrev_guard_against_a_search_stop_register_is_kept() {
        let mut failures = Vec::new();
        for case in [
            Case {
                name: "nbr_rguard_search_48_64",
                lo: 48,
                hi: 64,
                exit: GuardExit::Early,
            },
            Case {
                name: "nbr_rguard_search_48_64_shared",
                lo: 48,
                hi: 64,
                exit: GuardExit::Shared,
            },
            Case {
                name: "nbr_rguard_search_112_128",
                lo: 112,
                hi: 128,
                exit: GuardExit::Early,
            },
        ] {
            failures.extend(probe(&case));
        }
        assert_no_failures(&failures);
    }
}

mod bytesum {
    //! `neon-bytesum` (`Recognized::recognize`) takes every `iv <u x` compare in
    //! the loop as the loop's single constant bound when its pass-local
    //! `const_value(x)` agrees, and its loop-contract `covers_loop_bound` closure
    //! admits a guard `i <u r` whose `const_value(r) >= N`. That resolver stopped
    //! copy-stripping at a multi-def register but then read the register's
    //! last-wins def, so a register with one `Movz` per incoming path resolved to
    //! whichever definition was laid out last.
    //!
    //! These tests JIT-run, at O2 and O3, a u64 byte sum
    //! `while i <u N { if !(i <u r) exit; s += a[i] as u64; i += 1 }`
    //! whose guard limit `r` is the stop index of an early-exit search that O2/O3
    //! unroll fully (one `Movz r, #k` per exit edge, `#N` laid out last), and
    //! compare with a plain Rust model of the same loops. The pass needs
    //! `N >= 128` for the byte sum, so the search runs over `N-16+1..=N`.
    //! A diamond phi or an outer-loop-carried `r` reaches the pass as `MovR`
    //! copies of single-def registers, whose last-wins def is no `Movz`
    //! (the `map` rows keep those shapes).

    use super::*;
    use trust_ir::{BinOp, ICmpOp, Ty};
    use trust_ir_build::ModuleBuilder;

    /// The pass under test, by its pass-manager name.
    const PASS: &str = "neon-bytesum";
    /// One row: `r = j` where `j = lo; loop { j += 1; if j == hi || j == sel {
    /// break } }` (so `r` in `lo+1..=hi`, defs `Movz r, #lo+1 ..= #hi`), and the
    /// header bound `hi`.
    #[derive(Clone, Copy, Debug)]
    struct Case {
        name: &'static str,
        lo: u64,
        hi: u64,
        exit: GuardExit,
    }

    /// `fn(a: *const u8, sel: u64, _: u64, _: u64) -> u64`:
    ///
    /// ```text
    /// r = <search stop>
    /// i = 0; s = 0
    /// while i <u hi {
    ///     if !(i <u r) { return early(i, s) }      // or `return s`
    ///     s += a[i] as u64
    ///     i += 1
    /// }
    /// return s
    /// ```
    fn build_module(case: &Case) -> trust_ir::Module {
        let name = case.name;
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
        let body = fb.create_block();
        let latch = fb.create_block();
        let early = fb.create_block();
        let early_iv = fb.add_block_param(early, Ty::U64);
        let early_acc = fb.add_block_param(early, Ty::U64);
        let exit = fb.create_block();
        let exit_acc = fb.add_block_param(exit, Ty::U64);

        fb.switch_to_block(entry);
        let seed = fb.iconst(Ty::U64, i128::from(case.lo));
        fb.br(search, vec![seed]);

        fb.switch_to_block(search);
        let one = fb.iconst(Ty::U64, 1);
        let next = fb.add(Ty::U64, j, one);
        fb.br(search_test, vec![]);

        fb.switch_to_block(search_test);
        let stop = fb.iconst(Ty::U64, i128::from(case.hi));
        let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, stop);
        let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, sel);
        let more = fb.binop(BinOp::And, Ty::Bool, trip, not_found);
        fb.condbr(more, search, vec![next], pre, vec![next]);

        fb.switch_to_block(pre);
        let i0 = fb.iconst(Ty::U64, 0);
        let s0 = fb.iconst(Ty::U64, 0);
        fb.br(header, vec![i0, s0]);

        fb.switch_to_block(header);
        let n = fb.iconst(Ty::U64, i128::from(case.hi));
        let go = fb.icmp(ICmpOp::Ult, Ty::U64, iv, n);
        fb.condbr(go, body, vec![], exit, vec![acc]);

        fb.switch_to_block(body);
        let in_range = fb.icmp(ICmpOp::Ult, Ty::U64, iv, r);
        match case.exit {
            GuardExit::Early => fb.condbr(in_range, latch, vec![], early, vec![iv, acc]),
            GuardExit::Shared => fb.condbr(in_range, latch, vec![], exit, vec![acc]),
        }

        fb.switch_to_block(latch);
        let addr = fb.gep(Ty::U8, p, vec![iv]);
        let byte = fb.load(Ty::U8, addr);
        let wide = fb.zext(Ty::U8, Ty::U64, byte);
        let acc_next = fb.add(Ty::U64, acc, wide);
        let step = fb.iconst(Ty::U64, 1);
        let iv_next = fb.add(Ty::U64, iv, step);
        fb.br(header, vec![iv_next, acc_next]);

        fb.switch_to_block(exit);
        fb.ret(vec![exit_acc]);

        fb.switch_to_block(early);
        let k = fb.iconst(Ty::U64, i128::from(IV_SCALE));
        let scaled = fb.mul(Ty::U64, early_iv, k);
        let mixed = fb.binop(BinOp::Xor, Ty::U64, early_acc, scaled);
        let bias = fb.iconst(Ty::U64, i128::from(EARLY));
        let result = fb.add(Ty::U64, mixed, bias);
        fb.ret(vec![result]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// Plain-Rust model of the whole function.
    fn model(a: &[u8], case: &Case, sel: u64) -> u64 {
        let r = search_stop(case.lo, case.hi, sel);
        let mut s = 0u64;
        for i in 0..case.hi {
            if i >= r {
                return match case.exit {
                    GuardExit::Early => (s ^ i.wrapping_mul(IV_SCALE)).wrapping_add(EARLY),
                    GuardExit::Shared => s,
                };
            }
            s += u64::from(a[i as usize]);
        }
        s
    }

    /// Deterministic bytes.
    fn data_for(len: usize) -> Vec<u8> {
        xorshift32(0x1234_5678, len)
            .into_iter()
            .map(|x| x as u8)
            .collect()
    }

    /// Every stop index of the search (and the `sel` values that miss it) at O2
    /// and O3. Returns the failures as text.
    fn probe(case: &Case) -> Vec<String> {
        let name = case.name;
        let module = build_module(case);
        let data = data_for(case.hi as usize + 64);
        let sels = search_sels(case.lo, case.hi);
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let fired = pass_changes(&module, opt_level, PASS);
            eprintln!("{name} {opt_level:?}: {PASS} changed the function {fired} time(s)");
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{name} {opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the entry's trust-ir signature is (ptr, u64, u64, u64) ->
            // u64, `data` holds `hi + 64` bytes while the scalar loop reads only
            // indices below `hi`, and `result` outlives every call.
            let entry = unsafe {
                result
                    .buffer
                    .get_fn_bound::<extern "C" fn(*const u8, u64, u64, u64) -> u64>(name)
            }
            .expect("entry symbol");
            for &sel in &sels {
                let expected = model(&data, case, sel);
                let got = entry.as_ref()(data.as_ptr(), sel, 0, 0);
                if got != expected {
                    failures.push(format!(
                        "{name} {opt_level:?} ({PASS} fired {fired}x) sel={sel}: got {got:#x}, \
                     expected {expected:#x}"
                    ));
                }
            }
        }
        failures
    }

    /// Header `i <u N` (immediate), body guard `i <u r`: the pass-local
    /// `const_value(r)` reads `r`'s layout-last `Movz r, #N`, so the guard joins
    /// the single bound `N` and `covers_loop_bound` admits it, and the vector sum
    /// adds `a[r..N)` in and skips the guard's exit.
    #[test]
    fn bytesum_chain_guard_against_a_search_stop_register_is_kept() {
        let mut failures = Vec::new();
        for case in [
            Case {
                name: "nbs_rguard_search_112_128",
                lo: 112,
                hi: 128,
                exit: GuardExit::Early,
            },
            Case {
                name: "nbs_rguard_search_240_256",
                lo: 240,
                hi: 256,
                exit: GuardExit::Early,
            },
            Case {
                name: "nbs_rguard_search_240_256_shared",
                lo: 240,
                hi: 256,
                exit: GuardExit::Shared,
            },
        ] {
            failures.extend(probe(&case));
        }
        assert_no_failures(&failures);
    }
}

mod find {
    //! `neon-find`'s forward-chain search (`FindRecognized::recognize_forward_chain`
    //! and `walk_find_chain`) admits a body guard `i <u r` as covered by the
    //! loop's bound when `chain_bound_agrees` resolves `r` to that bound through
    //! `mach_util::const_value`. That resolver read the last-wins def map, so a
    //! register with one constant definition per incoming path resolved to
    //! whichever definition was laid out last.
    //!
    //! These tests JIT-run, at O2 and O3, a first-match search
    //! `while i <u N { if !(i <u r) exit; if a[i] == key { return i }; i += 1 }`
    //! whose guard limit `r` is the stop index of an early-exit search that O2/O3
    //! unroll fully (one `Movz r, #k` per exit edge, `#N` laid out last), and
    //! compare with a plain Rust model of the same loops. The header bound is the
    //! immediate `N` (`CmpRI`) or a register holding `N` (`CmpRR` against one
    //! `Movz #N`). A diamond phi or an outer-loop-carried `r` reaches the pass as
    //! `MovR` copies, which `const_value` did not follow
    //! (the `map` rows keep those shapes).

    use super::*;
    use trust_ir::{BinOp, ICmpOp, Ty, ValueId};
    use trust_ir_build::{FunctionBuilder, ModuleBuilder};

    /// The pass under test, by its pass-manager name.
    const PASS: &str = "neon-find";
    /// Returned when the header test exits the loop (no match below the bound).
    const NOT_FOUND: u64 = 0xFFFF_FFFF_FFFF_FF00;
    /// Returned by the shared guard exit.
    const GUARD_DONE: u64 = 0xFFFF_FFFF_FFFF_FE00;
    /// A key no element holds (every element is odd).
    const ABSENT: i32 = 0;

    /// One side of the chain's `i <u _` tests.
    #[derive(Clone, Copy, Debug)]
    enum Bound {
        /// The constant `k`, which instruction selection folds into a `CmpRI`.
        Imm(u64),
        /// A register holding the constant `k`: a parameter of a block the entry
        /// block alone branches to with `k`, so the compare stays a `CmpRR`, which
        /// copy propagation points at the single-def `Movz #k` register.
        Reg(u64),
        /// The search's stop register `r`.
        R,
    }

    /// One row: `r = j` where `j = lo; loop { j += 1; if j == hi || j == sel {
    /// break } }` (so `r` in `lo+1..=hi`, defs `Movz r, #lo+1 ..= #hi`), and the
    /// header and body-guard bounds.
    #[derive(Clone, Copy, Debug)]
    struct Case {
        name: &'static str,
        lo: u64,
        hi: u64,
        header: Bound,
        guard: Bound,
        exit: GuardExit,
    }

    /// `fn(a: *const i32, sel: u64, key: i32, _: u64) -> u64`:
    ///
    /// ```text
    /// r = <search stop>
    /// i = 0
    /// while i <u <header> {
    ///     if !(i <u <guard>) { return early(i) }   // or `return GUARD_DONE`
    ///     if a[i] == key { return i }
    ///     i += 1
    /// }
    /// return NOT_FOUND
    /// ```
    fn build_module(case: &Case) -> trust_ir::Module {
        let name = case.name;
        let mut mb = ModuleBuilder::new(name);
        let fty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::I32, Ty::U64], vec![Ty::U64]);
        let mut fb = mb.function(name, fty);
        let entry = fb.create_block();
        let p = fb.add_block_param(entry, Ty::Ptr);
        let sel = fb.add_block_param(entry, Ty::U64);
        let key = fb.add_block_param(entry, Ty::I32);
        let _unused = fb.add_block_param(entry, Ty::U64);

        fb.switch_to_block(entry);
        let b = [case.header, case.guard]
            .into_iter()
            .find_map(|bound| match bound {
                Bound::Reg(k) => {
                    let setup = fb.create_block();
                    let b = fb.add_block_param(setup, Ty::U64);
                    let k = fb.iconst(Ty::U64, i128::from(k));
                    fb.br(setup, vec![k]);
                    fb.switch_to_block(setup);
                    Some(b)
                }
                _ => None,
            });

        let search = fb.create_block();
        let j = fb.add_block_param(search, Ty::U64);
        let search_test = fb.create_block();
        let pre = fb.create_block();
        let r = fb.add_block_param(pre, Ty::U64);
        let seed = fb.iconst(Ty::U64, i128::from(case.lo));
        fb.br(search, vec![seed]);

        fb.switch_to_block(search);
        let one = fb.iconst(Ty::U64, 1);
        let next = fb.add(Ty::U64, j, one);
        fb.br(search_test, vec![]);

        fb.switch_to_block(search_test);
        let stop = fb.iconst(Ty::U64, i128::from(case.hi));
        let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, stop);
        let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, sel);
        let more = fb.binop(BinOp::And, Ty::Bool, trip, not_found);
        fb.condbr(more, search, vec![next], pre, vec![next]);

        fb.switch_to_block(pre);
        let header = fb.create_block();
        let iv = fb.add_block_param(header, Ty::U64);
        let guard = fb.create_block();
        let test = fb.create_block();
        let latch = fb.create_block();
        let found = fb.create_block();
        let found_iv = fb.add_block_param(found, Ty::U64);
        let early = fb.create_block();
        let early_iv = fb.add_block_param(early, Ty::U64);
        let guard_done = fb.create_block();
        let exit = fb.create_block();
        let i0 = fb.iconst(Ty::U64, 0);
        fb.br(header, vec![i0]);

        fb.switch_to_block(header);
        let go = below(&mut fb, iv, b, r, case.header);
        fb.condbr(go, guard, vec![], exit, vec![]);

        fb.switch_to_block(guard);
        let in_range = below(&mut fb, iv, b, r, case.guard);
        match case.exit {
            GuardExit::Early => fb.condbr(in_range, test, vec![], early, vec![iv]),
            GuardExit::Shared => fb.condbr(in_range, test, vec![], guard_done, vec![]),
        }

        fb.switch_to_block(test);
        let addr = fb.gep(Ty::I32, p, vec![iv]);
        let v = fb.load(Ty::I32, addr);
        let hit = fb.icmp(ICmpOp::Eq, Ty::I32, v, key);
        fb.condbr(hit, found, vec![iv], latch, vec![]);

        fb.switch_to_block(latch);
        let step = fb.iconst(Ty::U64, 1);
        let iv_next = fb.add(Ty::U64, iv, step);
        fb.br(header, vec![iv_next]);

        fb.switch_to_block(found);
        fb.ret(vec![found_iv]);

        fb.switch_to_block(early);
        let k = fb.iconst(Ty::U64, i128::from(IV_SCALE));
        let scaled = fb.mul(Ty::U64, early_iv, k);
        let bias = fb.iconst(Ty::U64, i128::from(EARLY));
        let early_result = fb.add(Ty::U64, scaled, bias);
        fb.ret(vec![early_result]);

        fb.switch_to_block(guard_done);
        let done = fb.iconst(Ty::U64, i128::from(GUARD_DONE));
        fb.ret(vec![done]);

        fb.switch_to_block(exit);
        let none = fb.iconst(Ty::U64, i128::from(NOT_FOUND));
        fb.ret(vec![none]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// `i <u bound` for one side of the chain.
    fn below(
        fb: &mut FunctionBuilder<'_>,
        iv: ValueId,
        b: Option<ValueId>,
        r: ValueId,
        bound: Bound,
    ) -> ValueId {
        let rhs = match bound {
            Bound::Imm(k) => fb.iconst(Ty::U64, i128::from(k)),
            Bound::Reg(_) => b.expect("the entry block defines the bound register"),
            Bound::R => r,
        };
        fb.icmp(ICmpOp::Ult, Ty::U64, iv, rhs)
    }

    /// Plain-Rust model of the whole function.
    fn model(a: &[i32], case: &Case, sel: u64, key: i32) -> u64 {
        let r = search_stop(case.lo, case.hi, sel);
        let value = |bound: Bound| match bound {
            Bound::Imm(k) | Bound::Reg(k) => k,
            Bound::R => r,
        };
        let mut i = 0u64;
        while i < value(case.header) {
            if i >= value(case.guard) {
                return match case.exit {
                    GuardExit::Early => i.wrapping_mul(IV_SCALE).wrapping_add(EARLY),
                    GuardExit::Shared => GUARD_DONE,
                };
            }
            if a[i as usize] == key {
                return i;
            }
            i += 1;
        }
        NOT_FOUND
    }

    /// Distinct odd elements, so `ABSENT` matches none of them.
    fn data_for(len: usize) -> Vec<i32> {
        (0..len as i32).map(|i| i * 2 + 1).collect()
    }

    /// Every stop index of the search (and the `sel` values that miss it), with
    /// the key absent and at a few positions, at O2 and O3. Returns the failures
    /// as text.
    fn probe(case: &Case) -> Vec<String> {
        let name = case.name;
        let module = build_module(case);
        let data = data_for(case.hi as usize + 64);
        let mut keys = vec![ABSENT];
        for at in [0, case.lo, case.hi - 1, case.hi, case.hi + 3] {
            keys.push(data[at as usize]);
        }
        let sels = search_sels(case.lo, case.hi);
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let fired = pass_changes(&module, opt_level, PASS);
            eprintln!("{name} {opt_level:?}: {PASS} changed the function {fired} time(s)");
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{name} {opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the entry's trust-ir signature is (ptr, u64, i32, u64) ->
            // u64, `data` holds `hi + 64` elements while the scalar loop reads
            // only indices below `hi`, and `result` outlives every call.
            let entry = unsafe {
                result
                    .buffer
                    .get_fn_bound::<extern "C" fn(*const i32, u64, i32, u64) -> u64>(name)
            }
            .expect("entry symbol");
            for &sel in &sels {
                for &key in &keys {
                    let expected = model(&data, case, sel, key);
                    let got = entry.as_ref()(data.as_ptr(), sel, key, 0);
                    if got != expected {
                        failures.push(format!(
                            "{name} {opt_level:?} ({PASS} fired {fired}x) sel={sel} key={key}: \
                         got {got:#x}, expected {expected:#x}"
                        ));
                    }
                }
            }
        }
        failures
    }

    fn run(cases: &[Case]) {
        let mut failures = Vec::new();
        for case in cases {
            failures.extend(probe(case));
        }
        assert_no_failures(&failures);
    }

    /// Header `i <u N` (immediate), body guard `i <u r`:
    /// `chain_bound_agrees(Const(N), Reg(r))` holds through `r`'s layout-last
    /// `Movz r, #N`, so the block filter skips 16-blocks past the guard exit and
    /// the search reports `NOT_FOUND` (or a match at or past `r`) instead of the
    /// guard's exit.
    #[test]
    fn find_chain_guard_against_a_search_stop_register_is_kept() {
        let imm = |name, lo, hi, exit| Case {
            name,
            lo,
            hi,
            header: Bound::Imm(hi),
            guard: Bound::R,
            exit,
        };
        run(&[
            imm("nf_rguard_search_l16", 0, 16, GuardExit::Early),
            imm("nf_rguard_search_l16_shared", 0, 16, GuardExit::Shared),
            imm("nf_rguard_search_16_32", 16, 32, GuardExit::Early),
            imm("nf_rguard_search_48_64", 48, 64, GuardExit::Early),
        ]);
    }

    /// Header `i <u b` with `b` one `Movz b, #N`, body guard `i <u r`:
    /// `chain_bound_agrees(Reg(b), Reg(r))` equates the registers through
    /// `const_value(b) == const_value(r) == N`.
    #[test]
    fn find_chain_guard_register_against_a_header_register_is_kept() {
        let reg = |name, lo, hi, exit| Case {
            name,
            lo,
            hi,
            header: Bound::Reg(hi),
            guard: Bound::R,
            exit,
        };
        run(&[
            reg("nf_rguard_hreg_l16", 0, 16, GuardExit::Early),
            reg("nf_rguard_hreg_16_32", 16, 32, GuardExit::Early),
            reg("nf_rguard_hreg_16_32_shared", 16, 32, GuardExit::Shared),
        ]);
    }
}

mod minmax {
    //! `neon-minmax`'s forward-chain reduction (`ChainRecognized::recognize` and
    //! `walk_chain`) admits a body guard `i <u r` as covered by the header's
    //! constant bound `N` when `chain_bound_agrees` resolves `r` to `N` through
    //! `mach_util::const_value`. That resolver read the last-wins def map, so a
    //! register with one constant definition per incoming path resolved to
    //! whichever definition was laid out last.
    //!
    //! These tests JIT-run, at O2 and O3, an i32 min or max reduction written as
    //! a branch diamond,
    //! `while i <u N { if !(i <u r) exit; if a[i] < m { m = a[i] }; i += 1 }`,
    //! whose guard limit `r` is the stop index of an early-exit search that O2/O3
    //! unroll fully (one `Movz r, #k` per exit edge, `#N` laid out last), and
    //! compare with a plain Rust model of the same loops. The chain path takes
    //! only an immediate header bound, so its register-register agreement arm is
    //! out of reach here. A diamond phi or an outer-loop-carried `r` reaches the
    //! pass as `MovR` copies, which `const_value` did not follow
    //! (the `map` rows keep those shapes).

    use super::*;
    use trust_ir::{BinOp, ICmpOp, Ty};
    use trust_ir_build::ModuleBuilder;

    /// The pass under test, by its pass-manager name.
    const PASS: &str = "neon-minmax";
    /// The reduction.
    #[derive(Clone, Copy, Debug)]
    enum Op {
        /// `if a[i] < m { m = a[i] }`, seeded with `i32::MAX`.
        Min,
        /// `if a[i] > m { m = a[i] }`, seeded with `i32::MIN`.
        Max,
    }

    /// One row: `r = j` where `j = lo; loop { j += 1; if j == hi || j == sel {
    /// break } }` (so `r` in `lo+1..=hi`, defs `Movz r, #lo+1 ..= #hi`), a
    /// header bound `hi`, and the reduction.
    #[derive(Clone, Copy, Debug)]
    struct Case {
        name: &'static str,
        lo: u64,
        hi: u64,
        op: Op,
        exit: GuardExit,
    }

    impl Op {
        fn seed(self) -> i32 {
            match self {
                Op::Min => i32::MAX,
                Op::Max => i32::MIN,
            }
        }

        fn pred(self) -> ICmpOp {
            match self {
                Op::Min => ICmpOp::Slt,
                Op::Max => ICmpOp::Sgt,
            }
        }

        fn takes(self, v: i32, m: i32) -> bool {
            match self {
                Op::Min => v < m,
                Op::Max => v > m,
            }
        }
    }

    /// `fn(a: *const i32, sel: u64, _: u64, _: u64) -> u64`:
    ///
    /// ```text
    /// r = <search stop>
    /// i = 0; m = SEED
    /// while i <u hi {
    ///     if !(i <u r) { return early(i, m) }      // or `return m`
    ///     if a[i] OP m { m = a[i] }                // a branch diamond
    ///     i += 1
    /// }
    /// return m
    /// ```
    fn build_module(case: &Case) -> trust_ir::Module {
        let name = case.name;
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
        let acc = fb.add_block_param(header, Ty::I32);
        let guard = fb.create_block();
        let test = fb.create_block();
        let take = fb.create_block();
        let keep = fb.create_block();
        let latch = fb.create_block();
        let merged = fb.add_block_param(latch, Ty::I32);
        let early = fb.create_block();
        let early_iv = fb.add_block_param(early, Ty::U64);
        let early_acc = fb.add_block_param(early, Ty::I32);
        let exit = fb.create_block();
        let exit_acc = fb.add_block_param(exit, Ty::I32);

        fb.switch_to_block(entry);
        let seed = fb.iconst(Ty::U64, i128::from(case.lo));
        fb.br(search, vec![seed]);

        fb.switch_to_block(search);
        let one = fb.iconst(Ty::U64, 1);
        let next = fb.add(Ty::U64, j, one);
        fb.br(search_test, vec![]);

        fb.switch_to_block(search_test);
        let stop = fb.iconst(Ty::U64, i128::from(case.hi));
        let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, stop);
        let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, sel);
        let more = fb.binop(BinOp::And, Ty::Bool, trip, not_found);
        fb.condbr(more, search, vec![next], pre, vec![next]);

        fb.switch_to_block(pre);
        let i0 = fb.iconst(Ty::U64, 0);
        let m0 = fb.iconst(Ty::I32, i128::from(case.op.seed()));
        fb.br(header, vec![i0, m0]);

        fb.switch_to_block(header);
        let n = fb.iconst(Ty::U64, i128::from(case.hi));
        let go = fb.icmp(ICmpOp::Ult, Ty::U64, iv, n);
        fb.condbr(go, guard, vec![], exit, vec![acc]);

        fb.switch_to_block(guard);
        let in_range = fb.icmp(ICmpOp::Ult, Ty::U64, iv, r);
        match case.exit {
            GuardExit::Early => fb.condbr(in_range, test, vec![], early, vec![iv, acc]),
            GuardExit::Shared => fb.condbr(in_range, test, vec![], exit, vec![acc]),
        }

        fb.switch_to_block(test);
        let addr = fb.gep(Ty::I32, p, vec![iv]);
        let v = fb.load(Ty::I32, addr);
        let better = fb.icmp(case.op.pred(), Ty::I32, v, acc);
        fb.condbr(better, take, vec![], keep, vec![]);

        // The taken arm reloads `a[i]`, as the bridge's `m = a[i]` does; a load
        // keeps if-convert from flattening the diamond into a `Csel`.
        fb.switch_to_block(take);
        let take_addr = fb.gep(Ty::I32, p, vec![iv]);
        let reloaded = fb.load(Ty::I32, take_addr);
        fb.br(latch, vec![reloaded]);

        fb.switch_to_block(keep);
        fb.br(latch, vec![acc]);

        fb.switch_to_block(latch);
        let step = fb.iconst(Ty::U64, 1);
        let iv_next = fb.add(Ty::U64, iv, step);
        fb.br(header, vec![iv_next, merged]);

        fb.switch_to_block(exit);
        let wide = fb.zext(Ty::I32, Ty::U64, exit_acc);
        fb.ret(vec![wide]);

        fb.switch_to_block(early);
        let acc_wide = fb.zext(Ty::I32, Ty::U64, early_acc);
        let k = fb.iconst(Ty::U64, i128::from(IV_SCALE));
        let scaled = fb.mul(Ty::U64, early_iv, k);
        let mixed = fb.binop(BinOp::Xor, Ty::U64, acc_wide, scaled);
        let bias = fb.iconst(Ty::U64, i128::from(EARLY));
        let result = fb.add(Ty::U64, mixed, bias);
        fb.ret(vec![result]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// Plain-Rust model of the whole function.
    fn model(a: &[i32], case: &Case, sel: u64) -> u64 {
        let r = search_stop(case.lo, case.hi, sel);
        let mut m = case.op.seed();
        for i in 0..case.hi {
            if i >= r {
                let wide = u64::from(m as u32);
                return match case.exit {
                    GuardExit::Early => (wide ^ i.wrapping_mul(IV_SCALE)).wrapping_add(EARLY),
                    GuardExit::Shared => wide,
                };
            }
            let v = a[i as usize];
            if case.op.takes(v, m) {
                m = v;
            }
        }
        u64::from(m as u32)
    }

    /// Element data whose extremes sit past every early stop: the values fall
    /// (rise) with the index for a min (max), with a little noise.
    fn data_for(case: &Case, len: usize) -> Vec<i32> {
        xorshift32(0x2545_F491, len)
            .into_iter()
            .zip(0i32..)
            .map(|(x, i)| {
                let trend = match case.op {
                    Op::Min => -i * 1000,
                    Op::Max => i * 1000,
                };
                trend + (x % 997) as i32
            })
            .collect()
    }

    /// Every stop index of the search (and the `sel` values that miss it) at O2
    /// and O3. Returns the failures as text.
    fn probe(case: &Case) -> Vec<String> {
        let name = case.name;
        let module = build_module(case);
        let data = data_for(case, case.hi as usize + 64);
        let sels = search_sels(case.lo, case.hi);
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let fired = pass_changes(&module, opt_level, PASS);
            eprintln!("{name} {opt_level:?}: {PASS} changed the function {fired} time(s)");
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{name} {opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the entry's trust-ir signature is (ptr, u64, u64, u64) ->
            // u64, `data` holds `hi + 64` elements while the scalar loop reads
            // only indices below `hi`, and `result` outlives every call.
            let entry = unsafe {
                result
                    .buffer
                    .get_fn_bound::<extern "C" fn(*const i32, u64, u64, u64) -> u64>(name)
            }
            .expect("entry symbol");
            for &sel in &sels {
                let expected = model(&data, case, sel);
                let got = entry.as_ref()(data.as_ptr(), sel, 0, 0);
                if got != expected {
                    failures.push(format!(
                        "{name} {opt_level:?} ({PASS} fired {fired}x) sel={sel}: got {got:#x}, \
                     expected {expected:#x}"
                    ));
                }
            }
        }
        failures
    }

    /// Header `i <u N` (immediate), body guard `i <u r`:
    /// `chain_bound_agrees(Const(N), Reg(r))` holds through `r`'s layout-last
    /// `Movz r, #N`, so the vector reduction folds `a[r..N)` in and skips the
    /// guard's exit.
    #[test]
    fn minmax_chain_guard_against_a_search_stop_register_is_kept() {
        let mut failures = Vec::new();
        for case in [
            Case {
                name: "nmm_rguard_min_l16",
                lo: 0,
                hi: 16,
                op: Op::Min,
                exit: GuardExit::Early,
            },
            Case {
                name: "nmm_rguard_min_l16_shared",
                lo: 0,
                hi: 16,
                op: Op::Min,
                exit: GuardExit::Shared,
            },
            Case {
                name: "nmm_rguard_max_16_32",
                lo: 16,
                hi: 32,
                op: Op::Max,
                exit: GuardExit::Early,
            },
            Case {
                name: "nmm_rguard_min_48_64_shared",
                lo: 48,
                hi: 64,
                op: Op::Min,
                exit: GuardExit::Shared,
            },
        ] {
            failures.extend(probe(&case));
        }
        assert_no_failures(&failures);
    }
}

mod predsum {
    //! `neon-predsum`'s forward-chain conditional sum (`PredSumChainRecognized`:
    //! `walk_chain`, the loop-contract `is_bound` closure, and
    //! `walk_back_to_split_thru_guards` for a guard on the taken arm) admits a
    //! guard `i <u r` as covered by the loop's bound when `chain_bound_agrees`
    //! resolves `r` through `mach_util::const_value`. That resolver read the
    //! last-wins def map, so a register with one constant definition per
    //! incoming path resolved to whichever definition was laid out last.
    //!
    //! These tests JIT-run, at O2 and O3, an i32 conditional sum written as a
    //! branch diamond,
    //! `while i <u N { if !(i <u r) exit; if a[i] > t { s += a[i] }; i += 1 }`
    //! (or with the guard on the taken arm, before its reload of `a[i]`), whose
    //! guard limit `r` is the stop index of an early-exit search that O2/O3
    //! unroll fully (one `Movz r, #k` per exit edge, `#N` laid out last), and
    //! compare with a plain Rust model of the same loops. The header bound is
    //! the immediate `N` (`CmpRI`) or a register holding `N` (`CmpRR` against one
    //! `Movz #N`). A diamond phi or an outer-loop-carried `r` reaches the pass as
    //! `MovR` copies, which `const_value` did not follow
    //! (the `map` rows keep those shapes).

    use super::*;
    use trust_ir::{BinOp, ICmpOp, Ty, ValueId};
    use trust_ir_build::{FunctionBuilder, ModuleBuilder};

    /// The pass under test, by its pass-manager name.
    const PASS: &str = "neon-predsum";
    /// One side of the chain's `i <u _` tests.
    #[derive(Clone, Copy, Debug)]
    enum Bound {
        /// The constant `k`, which instruction selection folds into a `CmpRI`.
        Imm(u64),
        /// A register holding the constant `k`: a parameter of a block the entry
        /// block alone branches to with `k`, so the compare stays a `CmpRR`, which
        /// copy propagation points at the single-def `Movz #k` register.
        Reg(u64),
    }

    /// Where the guard `i <u r` sits.
    #[derive(Clone, Copy, Debug)]
    enum GuardAt {
        /// Before the predicate test, on every iteration.
        Body,
        /// On the taken arm, before its reload of `a[i]`.
        TakenArm,
    }

    /// One row: `r = j` where `j = lo; loop { j += 1; if j == hi || j == sel {
    /// break } }` (so `r` in `lo+1..=hi`, defs `Movz r, #lo+1 ..= #hi`), the
    /// header bound (always the value `hi`), and the guard.
    #[derive(Clone, Copy, Debug)]
    struct Case {
        name: &'static str,
        lo: u64,
        hi: u64,
        header: Bound,
        at: GuardAt,
        exit: GuardExit,
    }

    /// `fn(a: *const i32, sel: u64, t: i32, _: u64) -> u64`:
    ///
    /// ```text
    /// r = <search stop>
    /// i = 0; s = 0
    /// while i <u <header> {
    ///     if !(i <u r) { return early(i, s) }      // GuardAt::Body
    ///     if a[i] > t {                            // a branch diamond
    ///         if !(i <u r) { return early(i, s) }  // GuardAt::TakenArm
    ///         s += a[i]
    ///     }
    ///     i += 1
    /// }
    /// return s
    /// ```
    fn build_module(case: &Case) -> trust_ir::Module {
        let name = case.name;
        let mut mb = ModuleBuilder::new(name);
        let fty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::I32, Ty::U64], vec![Ty::U64]);
        let mut fb = mb.function(name, fty);
        let entry = fb.create_block();
        let p = fb.add_block_param(entry, Ty::Ptr);
        let sel = fb.add_block_param(entry, Ty::U64);
        let threshold = fb.add_block_param(entry, Ty::I32);
        let _unused = fb.add_block_param(entry, Ty::U64);

        fb.switch_to_block(entry);
        let b = match case.header {
            Bound::Reg(k) => {
                let setup = fb.create_block();
                let b = fb.add_block_param(setup, Ty::U64);
                let k = fb.iconst(Ty::U64, i128::from(k));
                fb.br(setup, vec![k]);
                fb.switch_to_block(setup);
                Some(b)
            }
            _ => None,
        };

        let search = fb.create_block();
        let j = fb.add_block_param(search, Ty::U64);
        let search_test = fb.create_block();
        let pre = fb.create_block();
        let r = fb.add_block_param(pre, Ty::U64);
        let header = fb.create_block();
        let iv = fb.add_block_param(header, Ty::U64);
        let acc = fb.add_block_param(header, Ty::I32);
        let guard = fb.create_block();
        let test = fb.create_block();
        let take = fb.create_block();
        let take_body = fb.create_block();
        let keep = fb.create_block();
        let latch = fb.create_block();
        let merged = fb.add_block_param(latch, Ty::I32);
        let early = fb.create_block();
        let early_iv = fb.add_block_param(early, Ty::U64);
        let early_acc = fb.add_block_param(early, Ty::I32);
        let exit = fb.create_block();
        let exit_acc = fb.add_block_param(exit, Ty::I32);

        let seed = fb.iconst(Ty::U64, i128::from(case.lo));
        fb.br(search, vec![seed]);

        fb.switch_to_block(search);
        let one = fb.iconst(Ty::U64, 1);
        let next = fb.add(Ty::U64, j, one);
        fb.br(search_test, vec![]);

        fb.switch_to_block(search_test);
        let stop = fb.iconst(Ty::U64, i128::from(case.hi));
        let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, stop);
        let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, sel);
        let more = fb.binop(BinOp::And, Ty::Bool, trip, not_found);
        fb.condbr(more, search, vec![next], pre, vec![next]);

        fb.switch_to_block(pre);
        let i0 = fb.iconst(Ty::U64, 0);
        let s0 = fb.iconst(Ty::I32, 0);
        fb.br(header, vec![i0, s0]);

        fb.switch_to_block(header);
        let go = below(&mut fb, iv, b, case.header);
        fb.condbr(go, guard, vec![], exit, vec![acc]);

        // The body guard, or a pass-through when the guard sits on the arm.
        fb.switch_to_block(guard);
        match case.at {
            GuardAt::Body => guard_branch(&mut fb, iv, acc, r, test, early, exit, case.exit),
            GuardAt::TakenArm => fb.br(test, vec![]),
        }

        fb.switch_to_block(test);
        let addr = fb.gep(Ty::I32, p, vec![iv]);
        let v = fb.load(Ty::I32, addr);
        // A register threshold: the chain diamond decodes only a `CmpRR` split.
        let above = fb.icmp(ICmpOp::Sgt, Ty::I32, v, threshold);
        fb.condbr(above, take, vec![], keep, vec![]);

        fb.switch_to_block(take);
        match case.at {
            GuardAt::Body => fb.br(take_body, vec![]),
            GuardAt::TakenArm => {
                guard_branch(&mut fb, iv, acc, r, take_body, early, exit, case.exit)
            }
        }

        // The taken arm reloads `a[i]`, as the bridge's `s += a[i]` does; a load
        // keeps if-convert from flattening the diamond into a `Csel`.
        fb.switch_to_block(take_body);
        let take_addr = fb.gep(Ty::I32, p, vec![iv]);
        let reloaded = fb.load(Ty::I32, take_addr);
        let sum = fb.binop(BinOp::Add, Ty::I32, acc, reloaded);
        fb.br(latch, vec![sum]);

        fb.switch_to_block(keep);
        fb.br(latch, vec![acc]);

        fb.switch_to_block(latch);
        let step = fb.iconst(Ty::U64, 1);
        let iv_next = fb.add(Ty::U64, iv, step);
        fb.br(header, vec![iv_next, merged]);

        fb.switch_to_block(exit);
        let wide = fb.zext(Ty::I32, Ty::U64, exit_acc);
        fb.ret(vec![wide]);

        fb.switch_to_block(early);
        let acc_wide = fb.zext(Ty::I32, Ty::U64, early_acc);
        let k = fb.iconst(Ty::U64, i128::from(IV_SCALE));
        let scaled = fb.mul(Ty::U64, early_iv, k);
        let mixed = fb.binop(BinOp::Xor, Ty::U64, acc_wide, scaled);
        let bias = fb.iconst(Ty::U64, i128::from(EARLY));
        let result = fb.add(Ty::U64, mixed, bias);
        fb.ret(vec![result]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// `i <u bound` for the header.
    fn below(
        fb: &mut FunctionBuilder<'_>,
        iv: ValueId,
        b: Option<ValueId>,
        bound: Bound,
    ) -> ValueId {
        let rhs = match bound {
            Bound::Imm(k) => fb.iconst(Ty::U64, i128::from(k)),
            Bound::Reg(_) => b.expect("the entry block defines the bound register"),
        };
        fb.icmp(ICmpOp::Ult, Ty::U64, iv, rhs)
    }

    /// The guard `if i <u r { continue } else { exit }`, ending the current block.
    #[allow(clippy::too_many_arguments)]
    fn guard_branch(
        fb: &mut FunctionBuilder<'_>,
        iv: ValueId,
        acc: ValueId,
        r: ValueId,
        cont: trust_ir::BlockId,
        early: trust_ir::BlockId,
        exit: trust_ir::BlockId,
        how: GuardExit,
    ) {
        let in_range = fb.icmp(ICmpOp::Ult, Ty::U64, iv, r);
        match how {
            GuardExit::Early => fb.condbr(in_range, cont, vec![], early, vec![iv, acc]),
            GuardExit::Shared => fb.condbr(in_range, cont, vec![], exit, vec![acc]),
        }
    }

    /// Plain-Rust model of the whole function.
    fn model(a: &[i32], case: &Case, sel: u64, t: i32) -> u64 {
        let r = search_stop(case.lo, case.hi, sel);
        let leave = |i: u64, s: i32| {
            let wide = u64::from(s as u32);
            match case.exit {
                GuardExit::Early => (wide ^ i.wrapping_mul(IV_SCALE)).wrapping_add(EARLY),
                GuardExit::Shared => wide,
            }
        };
        let mut s = 0i32;
        for i in 0..case.hi {
            if matches!(case.at, GuardAt::Body) && i >= r {
                return leave(i, s);
            }
            let v = a[i as usize];
            if v > t {
                if matches!(case.at, GuardAt::TakenArm) && i >= r {
                    return leave(i, s);
                }
                s = s.wrapping_add(v);
            }
        }
        u64::from(s as u32)
    }

    /// Deterministic element data of both signs, mostly positive.
    fn data_for(len: usize) -> Vec<i32> {
        xorshift32(0x9E37_79B9, len)
            .into_iter()
            .map(|x| (x % 2001) as i32 - 500)
            .collect()
    }

    /// Every stop index of the search (and the `sel` values that miss it) at O2
    /// and O3. Returns the failures as text.
    fn probe(case: &Case) -> Vec<String> {
        let name = case.name;
        let module = build_module(case);
        let data = data_for(case.hi as usize + 64);
        let sels = search_sels(case.lo, case.hi);
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let fired = pass_changes(&module, opt_level, PASS);
            eprintln!("{name} {opt_level:?}: {PASS} changed the function {fired} time(s)");
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{name} {opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the entry's trust-ir signature is (ptr, u64, i32, u64) ->
            // u64, `data` holds `hi + 64` elements while the scalar loop reads
            // only indices below `hi`, and `result` outlives every call.
            let entry = unsafe {
                result
                    .buffer
                    .get_fn_bound::<extern "C" fn(*const i32, u64, i32, u64) -> u64>(name)
            }
            .expect("entry symbol");
            for &sel in &sels {
                let expected = model(&data, case, sel, 0);
                let got = entry.as_ref()(data.as_ptr(), sel, 0, 0);
                if got != expected {
                    failures.push(format!(
                        "{name} {opt_level:?} ({PASS} fired {fired}x) sel={sel}: got {got:#x}, \
                     expected {expected:#x}"
                    ));
                }
            }
        }
        failures
    }

    fn run(cases: &[Case]) {
        let mut failures = Vec::new();
        for case in cases {
            failures.extend(probe(case));
        }
        assert_no_failures(&failures);
    }

    /// Header `i <u N` (immediate), body guard `i <u r`:
    /// `chain_bound_agrees(Const(N), Reg(r))` holds through `r`'s layout-last
    /// `Movz r, #N`, so the vector sum adds `a[r..N)` in and skips the guard's
    /// exit.
    #[test]
    fn predsum_chain_guard_against_a_search_stop_register_is_kept() {
        let imm = |name, lo, hi, exit| Case {
            name,
            lo,
            hi,
            header: Bound::Imm(hi),
            at: GuardAt::Body,
            exit,
        };
        run(&[
            imm("nps_rguard_search_l16", 0, 16, GuardExit::Early),
            imm("nps_rguard_search_l16_shared", 0, 16, GuardExit::Shared),
            imm("nps_rguard_search_16_32", 16, 32, GuardExit::Early),
            imm("nps_rguard_search_48_64_shared", 48, 64, GuardExit::Shared),
        ]);
    }

    /// Header `i <u b` with `b` one `Movz b, #N`, body guard `i <u r`:
    /// `chain_bound_agrees(Reg(b), Reg(r))` equates the registers through
    /// `const_value(b) == const_value(r) == N`.
    #[test]
    fn predsum_chain_guard_register_against_a_header_register_is_kept() {
        let reg = |name, lo, hi, exit| Case {
            name,
            lo,
            hi,
            header: Bound::Reg(hi),
            at: GuardAt::Body,
            exit,
        };
        run(&[
            reg("nps_rguard_hreg_l16", 0, 16, GuardExit::Early),
            reg("nps_rguard_hreg_16_32", 16, 32, GuardExit::Early),
            reg("nps_rguard_hreg_16_32_shared", 16, 32, GuardExit::Shared),
        ]);
    }

    /// The guard `i <u r` sits on the taken arm, before the reload:
    /// `walk_back_to_split_thru_guards` skips it as a redundant bounds check when
    /// `chain_bound_agrees(loop bound, Reg(r))` holds.
    #[test]
    fn predsum_chain_taken_arm_guard_against_a_search_stop_register_is_kept() {
        let arm = |name, lo, hi, header, exit| Case {
            name,
            lo,
            hi,
            header,
            at: GuardAt::TakenArm,
            exit,
        };
        run(&[
            arm(
                "nps_rarm_search_l16",
                0,
                16,
                Bound::Imm(16),
                GuardExit::Early,
            ),
            arm(
                "nps_rarm_search_16_32",
                16,
                32,
                Bound::Imm(32),
                GuardExit::Early,
            ),
            arm(
                "nps_rarm_search_16_32_shared",
                16,
                32,
                Bound::Imm(32),
                GuardExit::Shared,
            ),
            arm(
                "nps_rarm_hreg_16_32",
                16,
                32,
                Bound::Reg(32),
                GuardExit::Early,
            ),
        ]);
    }
}

mod map {
    //! `neon-map`'s forward-chain path (`Recognized::recognize_forward_chain`)
    //! admits a bounds guard as agreeing with the header's bound when
    //! `mach_util::const_value` resolves the guard's register to the header's
    //! immediate (the chain walk's `(Reg, None, Some(k))` arm and the loop
    //! contract's `is_bound` closure), or when `bound_agrees` equates the guard's
    //! register with a header register through it. That resolver read the
    //! last-wins def map, so a register with several constant definitions, one
    //! per incoming path, resolved to whichever definition was laid out last.
    //!
    //! These tests JIT-run, at O2 and O3, an in-place `a[i] += 7` chain map whose
    //! header or body guard compares against such a register, and compare the
    //! returned value and the whole array with a plain Rust model of the same
    //! loops. The register `r` is
    //!
    //! * the stop index of an early-exit search that O2/O3 unroll fully, which
    //!   leaves one `Movz r, #k` per exit edge (the shape that reaches the pass);
    //! * a phi of two constants merged through a diamond, or a register an outer
    //!   loop carries (`first` on the first pass, `later` afterwards). Lowering
    //!   leaves both as `MovR` copies of single-def `Movz` registers, which
    //!   `const_value` does not follow, so the pass declines them today; they stay
    //!   as guards.
    //!
    //! A multi-def register on the header side (`while i <u r`, guard `i <u K`)
    //! is declined as well: `recognize_tail` requires the bound's last-wins def to
    //! dominate the preheader, and a per-exit-edge `Movz` does not.

    use super::*;
    use trust_ir::{BinOp, ICmpOp, Ty, ValueId};
    use trust_ir_build::{FunctionBuilder, ModuleBuilder};

    /// The pass under test, by its pass-manager name.
    const PASS: &str = "neon-map";
    /// Returned when the header test exits the loop.
    const DONE: u64 = 77;
    /// The map's per-element increment.
    const BUMP: i32 = 7;

    /// How the limit register `r` is defined.
    #[derive(Clone, Copy, Debug)]
    enum Limit {
        /// `j = lo; loop { j += 1; if j == hi || j == sel { break } }; r = j`:
        /// `r` in `lo+1..=hi`, defs `Movz r, #lo+1 ..= #hi`, `#hi` laid out last.
        Ascending { lo: u64, hi: u64 },
        /// `j = hi + 1; loop { j -= 1; if j == lo || j == sel { break } }; r = j`:
        /// `r` in `lo..=hi`, defs `Movz r, #hi ..= #lo`, `#lo` laid out last.
        Descending { lo: u64, hi: u64 },
        /// `r = if sel != 0 { other } else { last }`, the `last` arm laid out last.
        Diamond { other: u64, last: u64 },
        /// `r` carried by an outer loop of `passes` passes: `first` on the first
        /// pass, `later` (set in the outer latch) on every later one.
        Carried { first: u64, later: u64 },
    }

    /// One side of the chain's `i <u _` tests.
    #[derive(Clone, Copy, Debug)]
    enum Bound {
        /// The constant `k`, which instruction selection folds into a `CmpRI`.
        Imm(u64),
        /// A register holding the constant `k`: a parameter of a block the entry
        /// block alone branches to with `k`, so the compare stays a `CmpRR`, which
        /// copy propagation points at the single-def `Movz #k` register.
        Reg(u64),
        /// The limit register `r`.
        R,
    }

    /// One row: the limit register, the header and body-guard bounds, the exit.
    #[derive(Clone, Copy, Debug)]
    struct Case {
        name: &'static str,
        limit: Limit,
        header: Bound,
        guard: Bound,
        exit: GuardExit,
    }

    /// `fn(a: *mut i32, sel: u64, passes: u64, _: u64) -> u64`:
    ///
    /// ```text
    /// r = <limit>                                  // see `Limit`
    /// i = 0
    /// while i <u <header> {
    ///     if !(i <u <guard>) { return early(i) }   // or `return DONE`
    ///     a[i] += BUMP; i += 1
    /// }
    /// return DONE
    /// ```
    ///
    /// `Limit::Carried` wraps the chain loop in `for _ in 0..passes`, returning
    /// the wrapping sum of the per-pass results.
    fn build_module(case: &Case) -> trust_ir::Module {
        let name = case.name;
        let mut mb = ModuleBuilder::new(name);
        let fty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]);
        let mut fb = mb.function(name, fty);
        let entry = fb.create_block();
        let p = fb.add_block_param(entry, Ty::Ptr);
        let sel = fb.add_block_param(entry, Ty::U64);
        let passes = fb.add_block_param(entry, Ty::U64);
        let _unused = fb.add_block_param(entry, Ty::U64);

        fb.switch_to_block(entry);
        let b = [case.header, case.guard]
            .into_iter()
            .find_map(|bound| match bound {
                Bound::Reg(k) => {
                    let setup = fb.create_block();
                    let b = fb.add_block_param(setup, Ty::U64);
                    let k = fb.iconst(Ty::U64, i128::from(k));
                    fb.br(setup, vec![k]);
                    fb.switch_to_block(setup);
                    Some(b)
                }
                _ => None,
            });
        let regs = Regs { p, b };
        match case.limit {
            Limit::Ascending { lo, hi } | Limit::Descending { lo, hi } => {
                let ascending = matches!(case.limit, Limit::Ascending { .. });
                let search = fb.create_block();
                let j = fb.add_block_param(search, Ty::U64);
                let search_test = fb.create_block();
                let pre = fb.create_block();
                let r = fb.add_block_param(pre, Ty::U64);
                let seed = fb.iconst(Ty::U64, i128::from(if ascending { lo } else { hi + 1 }));
                fb.br(search, vec![seed]);

                fb.switch_to_block(search);
                let one = fb.iconst(Ty::U64, 1);
                let next = if ascending {
                    fb.add(Ty::U64, j, one)
                } else {
                    fb.sub(Ty::U64, j, one)
                };
                fb.br(search_test, vec![]);

                fb.switch_to_block(search_test);
                let stop = fb.iconst(Ty::U64, i128::from(if ascending { hi } else { lo }));
                let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, stop);
                let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, sel);
                let more = fb.binop(BinOp::And, Ty::Bool, trip, not_found);
                fb.condbr(more, search, vec![next], pre, vec![next]);

                fb.switch_to_block(pre);
                let result = chain_loop(&mut fb, regs, r, case);
                fb.ret(vec![result]);
            }
            Limit::Diamond { other, last } => {
                let other_arm = fb.create_block();
                let last_arm = fb.create_block();
                let pre = fb.create_block();
                let r = fb.add_block_param(pre, Ty::U64);
                let zero = fb.iconst(Ty::U64, 0);
                let is_other = fb.icmp(ICmpOp::Ne, Ty::U64, sel, zero);
                fb.condbr(is_other, other_arm, vec![], last_arm, vec![]);

                fb.switch_to_block(other_arm);
                let k_other = fb.iconst(Ty::U64, i128::from(other));
                fb.br(pre, vec![k_other]);

                fb.switch_to_block(last_arm);
                let k_last = fb.iconst(Ty::U64, i128::from(last));
                fb.br(pre, vec![k_last]);

                fb.switch_to_block(pre);
                let result = chain_loop(&mut fb, regs, r, case);
                fb.ret(vec![result]);
            }
            Limit::Carried { first, later } => {
                let outer = fb.create_block();
                let pass = fb.add_block_param(outer, Ty::U64);
                let r = fb.add_block_param(outer, Ty::U64);
                let total = fb.add_block_param(outer, Ty::U64);
                let run = fb.create_block();
                let done = fb.create_block();
                let zero = fb.iconst(Ty::U64, 0);
                let k_first = fb.iconst(Ty::U64, i128::from(first));
                fb.br(outer, vec![zero, k_first, zero]);

                fb.switch_to_block(outer);
                let more = fb.icmp(ICmpOp::Ult, Ty::U64, pass, passes);
                fb.condbr(more, run, vec![], done, vec![]);

                fb.switch_to_block(run);
                let result = chain_loop(&mut fb, regs, r, case);
                let total_next = fb.add(Ty::U64, total, result);
                let one = fb.iconst(Ty::U64, 1);
                let pass_next = fb.add(Ty::U64, pass, one);
                let k_later = fb.iconst(Ty::U64, i128::from(later));
                fb.br(outer, vec![pass_next, k_later, total_next]);

                fb.switch_to_block(done);
                fb.ret(vec![total]);
            }
        }
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// The entry-block values the chain loop reads.
    #[derive(Clone, Copy)]
    struct Regs {
        /// The array.
        p: ValueId,
        /// The register of a `Bound::Reg`, if the case has one.
        b: Option<ValueId>,
    }

    /// `i <u bound` for one side of the chain.
    fn below(
        fb: &mut FunctionBuilder<'_>,
        iv: ValueId,
        regs: Regs,
        r: ValueId,
        bound: Bound,
    ) -> ValueId {
        let rhs = match bound {
            Bound::Imm(k) => fb.iconst(Ty::U64, i128::from(k)),
            Bound::Reg(_) => regs.b.expect("the entry block defines the bound register"),
            Bound::R => r,
        };
        fb.icmp(ICmpOp::Ult, Ty::U64, iv, rhs)
    }

    /// Emit the chain map loop from the current block. Returns its result value,
    /// a parameter of the block left current (the loop's join).
    fn chain_loop(fb: &mut FunctionBuilder<'_>, regs: Regs, r: ValueId, case: &Case) -> ValueId {
        let header = fb.create_block();
        let iv = fb.add_block_param(header, Ty::U64);
        let body = fb.create_block();
        let latch = fb.create_block();
        let early = fb.create_block();
        let early_iv = fb.add_block_param(early, Ty::U64);
        let join = fb.create_block();
        let out = fb.add_block_param(join, Ty::U64);

        let i0 = fb.iconst(Ty::U64, 0);
        fb.br(header, vec![i0]);

        fb.switch_to_block(header);
        let go = below(fb, iv, regs, r, case.header);
        let done = fb.iconst(Ty::U64, i128::from(DONE));
        fb.condbr(go, body, vec![], join, vec![done]);

        fb.switch_to_block(body);
        let in_range = below(fb, iv, regs, r, case.guard);
        match case.exit {
            GuardExit::Early => fb.condbr(in_range, latch, vec![], early, vec![iv]),
            GuardExit::Shared => {
                let done_shared = fb.iconst(Ty::U64, i128::from(DONE));
                fb.condbr(in_range, latch, vec![], join, vec![done_shared]);
            }
        }

        fb.switch_to_block(latch);
        let addr = fb.gep(Ty::I32, regs.p, vec![iv]);
        let v = fb.load(Ty::I32, addr);
        let bump = fb.iconst(Ty::I32, i128::from(BUMP));
        let bumped = fb.binop(BinOp::Add, Ty::I32, v, bump);
        fb.store(Ty::I32, addr, bumped);
        let step = fb.iconst(Ty::U64, 1);
        let iv_next = fb.add(Ty::U64, iv, step);
        fb.br(header, vec![iv_next]);

        fb.switch_to_block(early);
        let k = fb.iconst(Ty::U64, i128::from(IV_SCALE));
        let scaled = fb.mul(Ty::U64, early_iv, k);
        let bias = fb.iconst(Ty::U64, i128::from(EARLY));
        let early_result = fb.add(Ty::U64, scaled, bias);
        fb.br(join, vec![early_result]);

        fb.switch_to_block(join);
        out
    }

    /// The run-time value of `r` on the given (0-based) pass.
    fn limit_value(limit: Limit, sel: u64, pass: u64) -> u64 {
        match limit {
            Limit::Ascending { lo, hi } => search_stop(lo, hi, sel),
            Limit::Descending { lo, hi } => {
                let mut j = hi + 1;
                loop {
                    j -= 1;
                    if j == lo || j == sel {
                        break j;
                    }
                }
            }
            Limit::Diamond { other, last } => {
                if sel != 0 {
                    other
                } else {
                    last
                }
            }
            Limit::Carried { first, later } => {
                if pass == 0 {
                    first
                } else {
                    later
                }
            }
        }
    }

    /// Plain-Rust model of one chain loop over `a` with the limit `r`.
    fn model_chain(a: &mut [i32], case: &Case, r: u64) -> u64 {
        let value = |bound: Bound| match bound {
            Bound::Imm(k) | Bound::Reg(k) => k,
            Bound::R => r,
        };
        let mut i = 0u64;
        while i < value(case.header) {
            if i >= value(case.guard) {
                return match case.exit {
                    GuardExit::Early => i.wrapping_mul(IV_SCALE).wrapping_add(EARLY),
                    GuardExit::Shared => DONE,
                };
            }
            a[i as usize] = a[i as usize].wrapping_add(BUMP);
            i += 1;
        }
        DONE
    }

    /// Plain-Rust model of the whole function.
    fn model(a: &mut [i32], case: &Case, sel: u64, passes: u64) -> u64 {
        match case.limit {
            Limit::Carried { .. } => {
                let mut total = 0u64;
                for pass in 0..passes {
                    let r = limit_value(case.limit, sel, pass);
                    total = total.wrapping_add(model_chain(a, case, r));
                }
                total
            }
            _ => model_chain(a, case, limit_value(case.limit, sel, 0)),
        }
    }

    /// The largest value any of the case's bounds can take.
    fn max_index(case: &Case) -> u64 {
        let r_max = match case.limit {
            Limit::Ascending { hi, .. } | Limit::Descending { hi, .. } => hi,
            Limit::Diamond { other, last } => other.max(last),
            Limit::Carried { first, later } => first.max(later),
        };
        let side = |bound: Bound| match bound {
            Bound::Imm(k) | Bound::Reg(k) => k,
            Bound::R => r_max,
        };
        side(case.header).max(side(case.guard))
    }

    /// The `sel` values worth running: every stop index of a search, plus the
    /// values below and just past it.
    fn sels(case: &Case) -> Vec<u64> {
        match case.limit {
            Limit::Ascending { lo, hi } | Limit::Descending { lo, hi } => {
                let mut sels: Vec<u64> = (0..=2).collect();
                sels.extend(lo.saturating_sub(1).max(3)..=hi + 1);
                sels
            }
            Limit::Diamond { .. } | Limit::Carried { .. } => (0..=2).collect(),
        }
    }

    /// Deterministic element data.
    fn data_for(len: usize) -> Vec<i32> {
        xorshift32(0x0F1E_2D3C, len)
            .into_iter()
            .map(|x| x as i32)
            .collect()
    }

    /// Every `sel` of [`sels`] (and `passes` in `0..=3` for `Carried`) at O2 and
    /// O3. Returns the failures as text.
    fn probe(case: &Case) -> Vec<String> {
        let name = case.name;
        let module = build_module(case);
        let top = max_index(case);
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let fired = pass_changes(&module, opt_level, PASS);
            eprintln!("{name} {opt_level:?}: {PASS} changed the function {fired} time(s)");
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{name} {opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the entry's trust-ir signature is (ptr, u64, u64, u64) ->
            // u64, `a` holds `top + 64` elements while the scalar loop touches
            // only indices below `top`, and `result` outlives every call.
            let entry = unsafe {
                result
                    .buffer
                    .get_fn_bound::<extern "C" fn(*mut i32, u64, u64, u64) -> u64>(name)
            }
            .expect("entry symbol");
            let pass_counts: &[u64] = match case.limit {
                Limit::Carried { .. } => &[0, 1, 2, 3],
                _ => &[1],
            };
            for &passes in pass_counts {
                for sel in sels(case) {
                    let init = data_for(top as usize + 64);
                    let mut want = init.clone();
                    let expected = model(&mut want, case, sel, passes);
                    let mut got_a = init;
                    let got = entry.as_ref()(got_a.as_mut_ptr(), sel, passes, 0);
                    if got != expected || got_a != want {
                        let first = (0..got_a.len()).find(|&x| got_a[x] != want[x]);
                        failures.push(format!(
                            "{name} {opt_level:?} ({PASS} fired {fired}x) sel={sel} \
                         passes={passes}: got {got:#x}, expected {expected:#x}; first \
                         differing element {first:?}"
                        ));
                    }
                }
            }
        }
        failures
    }

    fn run(cases: &[Case]) {
        let mut failures = Vec::new();
        for case in cases {
            failures.extend(probe(case));
        }
        assert_no_failures(&failures);
    }

    /// Header `i <u N` (immediate), body guard `i <u r` with `r` the stop index
    /// of a fully unrolled search: `r` is `sel` on every early-exit path and `N`
    /// only on the path that runs the search out. Its layout-last def is
    /// `Movz r, #N`, so `const_value(r) == N` admits the guard as the header's
    /// own bound (neon_map.rs `recognize_forward_chain`'s `(Reg(n), None,
    /// Some(k))` agreement and the `is_bound` loop-contract closure), and the
    /// vector map stores `a[r..N)` and skips the guard's exit.
    #[test]
    fn map_chain_guard_against_a_search_stop_register_is_kept() {
        let ascending = |name, lo, hi, exit| Case {
            name,
            limit: Limit::Ascending { lo, hi },
            header: Bound::Imm(hi),
            guard: Bound::R,
            exit,
        };
        run(&[
            ascending("nm_rguard_search_l8", 0, 8, GuardExit::Early),
            ascending("nm_rguard_search_l16", 0, 16, GuardExit::Early),
            ascending("nm_rguard_search_l16_shared", 0, 16, GuardExit::Shared),
            // `r` in 17..=32 against a header bound of 32.
            ascending("nm_rguard_search_16_32", 16, 32, GuardExit::Early),
            ascending("nm_rguard_search_16_32_shared", 16, 32, GuardExit::Shared),
            // `r` in 49..=64 against a header bound of 64.
            ascending("nm_rguard_search_48_64", 48, 64, GuardExit::Early),
        ]);
    }

    /// Header `i <u b`, body guard `i <u r`: the header compares against a
    /// register `b` that one `Movz b, #N` in the entry block defines, and `r` is
    /// the stop index of an unrolled search. `bound_agrees(b, r)` equates the two
    /// registers through `const_value(b) == const_value(r) == N`, the second one
    /// read from `r`'s layout-last def.
    #[test]
    fn map_chain_guard_register_against_a_header_register_is_kept() {
        let reg = |name, lo, hi, exit| Case {
            name,
            limit: Limit::Ascending { lo, hi },
            header: Bound::Reg(hi),
            guard: Bound::R,
            exit,
        };
        run(&[
            reg("nm_rguard_hreg_l16", 0, 16, GuardExit::Early),
            reg("nm_rguard_hreg_16_32", 16, 32, GuardExit::Early),
            reg("nm_rguard_hreg_16_32_shared", 16, 32, GuardExit::Shared),
        ]);
    }

    /// Header `i <u r`, body guard `i <u K` (immediate), with `r` the stop index
    /// of a fully unrolled descending search whose layout-last def is
    /// `Movz r, #K`: `const_value(r) == K` would let the guard agree with the
    /// header, and the vector trip would run to the run-time `r > K`.
    #[test]
    fn map_chain_header_register_against_a_guard_immediate_is_kept() {
        let descending = |name, lo, hi, exit| Case {
            name,
            limit: Limit::Descending { lo, hi },
            header: Bound::R,
            guard: Bound::Imm(lo),
            exit,
        };
        run(&[
            descending("nm_rheader_search_16_32", 16, 32, GuardExit::Early),
            descending("nm_rheader_search_16_32_shared", 16, 32, GuardExit::Shared),
            descending("nm_rheader_search_8_24", 8, 24, GuardExit::Early),
        ]);
    }

    /// The body guard's register is a phi of two constants, the header's bound
    /// laid out last.
    #[test]
    fn map_chain_guard_against_a_diamond_constant_register_is_kept() {
        let diamond = |name, other, n, exit| Case {
            name,
            limit: Limit::Diamond { other, last: n },
            header: Bound::Imm(n),
            guard: Bound::R,
            exit,
        };
        run(&[
            diamond("nm_rguard_diamond_l16", 5, 16, GuardExit::Early),
            diamond("nm_rguard_diamond_l16_shared", 5, 16, GuardExit::Shared),
            diamond("nm_rguard_diamond_l64", 9, 64, GuardExit::Early),
        ]);
    }

    /// The body guard's register is carried by an outer loop: `first` on the
    /// first pass, the header's bound (the layout-last def, in the outer latch)
    /// afterwards.
    #[test]
    fn map_chain_guard_against_a_loop_carried_constant_register_is_kept() {
        let carried = |name, first, n, exit| Case {
            name,
            limit: Limit::Carried { first, later: n },
            header: Bound::Imm(n),
            guard: Bound::R,
            exit,
        };
        run(&[
            carried("nm_rguard_carried_l16", 3, 16, GuardExit::Early),
            carried("nm_rguard_carried_l64", 9, 64, GuardExit::Early),
            carried("nm_rguard_carried_l64_shared", 9, 64, GuardExit::Shared),
        ]);
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
