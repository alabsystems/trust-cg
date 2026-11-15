// trust-cg-codegen - induction starts read from a register with several constant definitions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Induction starts read from a register written with different constants on
//! different paths.
//!
//! The invariant these rows pin: a register written with different constants
//! on different paths is not one constant. Machine IR is not SSA, and a
//! last-wins reaching-definition map keeps one definition per vreg, the
//! layout-last one; a resolver that reads it takes that definition's value on
//! every path. The resolvers these passes use now refuse such a register:
//! `mach_util::const_value` (behind `mac-reg-block`'s pass-local resolver)
//! gives a register a constant only when EVERY definition of it writes that
//! constant, `reduction_split::resolve_const` (behind
//! `closed-form-reduction` and `reduction-split`) requires every definition,
//! inside the loop or not, to write the same constant, and `alias-hoist`
//! reads the start as the ONE definition reaching its use
//! (`crate::reaching_const`).
//!
//! Each pass admits a loop only when its induction starts at a known
//! constant: 0 for `alias-hoist`'s store range and `mac-reg-block`'s j-loop
//! counter, any constant for the closed form and the split. The start
//! register's shapes:
//!
//! * the stop index of a fully unrolled early-exit search, one `Movz s, #k`
//!   per exit edge: counting down (`j = limit-1 ..= 0`, layout-last `#0`;
//!   `alias_hoist`, `mac_reg_block`) or up (`j = 1..=limit`, layout-last
//!   `#limit`; `reduction`);
//! * a phi of two constants through a diamond;
//! * a constant an outer loop carries (one value on entry, another on the
//!   back edge).
//!
//! Each search-stop row first reports the pass's change count through the
//! public `Pipeline` with an explicit disable list (so the ambient
//! `TRUST_CG_DISABLE_PASSES` cannot hide a firing) and checks that the pass's
//! key switches it off. The passes now decline these shapes, so the JIT
//! comparison with a plain Rust model, at O2 and O3, is the guard; a sound
//! future rewrite of a shape still has to pass it. The diamond and carried
//! rows are correctness controls. `reduction::reduction_split_start_from_search_stop`
//! is ignored by default: it needs `TRUST_CG_DISABLE_PASSES=looplatch`,
//! because `loop-latch-layout` rotates the loop before `reduction-split` runs.
//!
//! A test's doc names what a resolver that reads the layout-last definition
//! does with its shape: the misreading the row pins against. The rows are a
//! bounded differential over the listed shapes and inputs: tests, not a
//! proof.
#![cfg(target_arch = "aarch64")]

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

/// Where an inner loop's induction starts in `alias_hoist` and
/// `mac_reg_block` (`reduction` keeps its own, whose search counts up).
#[derive(Clone, Copy, Debug)]
enum Start {
    /// `sel != 0 ? then_start : else_start`, merged in a block parameter.
    Diamond { then_start: u64, else_start: u64 },
    /// Where a down-counting early-exit search `j = limit-1 ..= 0, stop when
    /// j == sel` stopped. Full unrolling writes one `Movz s, #k` per exit
    /// edge, the layout-last being `#0`.
    SearchDown { limit: u64 },
    /// An enclosing loop of `sel` iterations starts the inner loop at `first`
    /// on its first iteration and at `then` afterwards.
    Carried { first: u64, then: u64 },
}

/// The start on the path `sel` selects, on enclosing-loop iteration `trip`.
fn start_of(start: Start, sel: u64, trip: u64) -> u64 {
    match start {
        Start::Diamond {
            then_start,
            else_start,
        } => {
            if sel != 0 {
                then_start
            } else {
                else_start
            }
        }
        Start::SearchDown { limit } => {
            let mut j = limit;
            loop {
                j -= 1;
                if j == 0 || j == sel {
                    break j;
                }
            }
        }
        Start::Carried { first, then } => {
            if trip == 0 {
                first
            } else {
                then
            }
        }
    }
}

/// Per-pass change counts of `module` (named `name`) at `opt` with
/// `disabled` switched off.
fn pass_change_counts(
    name: &str,
    module: &trust_ir::Module,
    opt: OptLevel,
    disabled: &str,
) -> HashMap<String, u32> {
    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{name}: lowering: {error}"));
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: opt,
        target_triple: TRIPLE.into(),
        disabled_passes_override: Some(disabled.to_string()),
        ..PipelineConfig::default()
    });
    let mut changes = HashMap::new();
    for (function, _) in &lowered {
        let (_, metrics) = pipeline
            .prepare_function_with_metrics(function, None)
            .unwrap_or_else(|error| panic!("{name} {opt:?}: {error}"));
        for (pass, count) in &metrics.optimization_pass_changes {
            *changes.entry(pass.clone()).or_insert(0) += count;
        }
    }
    changes
}

/// Reports how often `pass` changes `module` at O2 and O3 with `base`
/// disabled, and checks that `base` plus `key` switches it off.
fn report_firing(name: &str, module: &trust_ir::Module, pass: &str, key: &str, base: &str) {
    for opt in [OptLevel::O2, OptLevel::O3] {
        let on = pass_change_counts(name, module, opt, base);
        eprintln!(
            "{name} {opt:?} (disabled {base:?}): {pass} changed the function {} time(s)",
            on.get(pass).copied().unwrap_or(0)
        );
        let both = if base.is_empty() {
            key.to_string()
        } else {
            format!("{base},{key}")
        };
        let off = pass_change_counts(name, module, opt, &both);
        assert_eq!(
            off.get(pass).copied().unwrap_or(0),
            0,
            "{name} {opt:?}: {key} must switch {pass} off"
        );
    }
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

/// Fails the test with every collected mismatch.
fn assert_no_failures(failures: &[String]) {
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

mod alias_hoist {
    //! `alias-hoist` sizes an indexed store's byte range as `[a, a + 8*n)` only
    //! for an index that starts at 0. It read the index's out-of-loop init
    //! `MovR i, s` through `alias_hoist::resolve_const`, which followed the copy
    //! source through a last-wins reaching-definition map. Machine IR is not SSA:
    //! `s` can be written once per incoming path with a different constant, for
    //! example
    //!
    //! * a block parameter merged from two constants through a diamond;
    //! * the stop index of a fully unrolled down-counting early-exit search
    //!   (`j = limit-1 ..= 0`, stop when `j == sel`), one `Movz s, #k` per exit
    //!   edge, the layout-last being `#0`;
    //! * a constant carried around an outer loop (one value on entry, another on
    //!   the back edge).
    //!
    //! When `s` resolves to its layout-last `#0` while another path starts the
    //! index at `K > 0`, the modeled store range misses the stores the loop really
    //! performs. The kernel is the do-while `i = s; loop { a[i] = 7; *o = *p;
    //! i += 1; if i >= n { break } }` with `p = a + K` and `n <= K`: iteration 0
    //! stores `a[K] = 7` and then loads `*p`, so `*o` must be 7. A fast clone
    //! entered on the wrong range loads `*p` before the store and returns the old
    //! value.
    //!
    //! The pass fired once at O2 and once at O3 on every multi-def shape below,
    //! and its fast clone loaded `*p` before the store, while it read the start
    //! through the last-wins map. It now declines them; its key is `aliashoist`.

    use super::*;
    use trust_ir::{BinOp, ICmpOp, Ty};
    use trust_ir_build::ModuleBuilder;

    const PASS: &str = "alias-hoist";
    const KEY: &str = "aliashoist";

    /// Elements of the `a` buffer the driver passes.
    const A_LEN: usize = 24;
    /// Elements of the `out` buffer.
    const OUT_LEN: usize = 8;

    #[derive(Clone, Copy, Debug)]
    struct Shape {
        name: &'static str,
        start: Start,
    }

    /// `fn(a: *mut u64, p: *const u64, out: *mut u64, n: u64, sel: u64)`.
    fn build_module(shape: &Shape) -> trust_ir::Module {
        let mut mb = ModuleBuilder::new(shape.name);
        let fty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::U64, Ty::U64], vec![]);
        let mut fb = mb.function(shape.name, fty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::Ptr);
        let p = fb.add_block_param(entry, Ty::Ptr);
        let out = fb.add_block_param(entry, Ty::Ptr);
        let n = fb.add_block_param(entry, Ty::U64);
        let sel = fb.add_block_param(entry, Ty::U64);

        let pre = fb.create_block();
        let pre_start = fb.add_block_param(pre, Ty::U64);
        let header = fb.create_block();
        let i = fb.add_block_param(header, Ty::U64);
        let done = fb.create_block();

        // Outer loop `oh(j, s)` and its exit (Carried only).
        let outer = if let Start::Carried { .. } = shape.start {
            let oh = fb.create_block();
            let j = fb.add_block_param(oh, Ty::U64);
            let s = fb.add_block_param(oh, Ty::U64);
            let fin = fb.create_block();
            Some((oh, j, s, fin))
        } else {
            None
        };

        fb.switch_to_block(entry);
        match shape.start {
            Start::Diamond {
                then_start,
                else_start,
            } => {
                let then_b = fb.create_block();
                let else_b = fb.create_block();
                let zero = fb.iconst(Ty::U64, 0);
                let c = fb.icmp(ICmpOp::Ne, Ty::U64, sel, zero);
                fb.condbr(c, then_b, vec![], else_b, vec![]);
                fb.switch_to_block(then_b);
                let s = fb.iconst(Ty::U64, i128::from(then_start));
                fb.br(pre, vec![s]);
                fb.switch_to_block(else_b);
                let s = fb.iconst(Ty::U64, i128::from(else_start));
                fb.br(pre, vec![s]);
            }
            Start::SearchDown { limit } => {
                let search = fb.create_block();
                let j = fb.add_block_param(search, Ty::U64);
                let search_test = fb.create_block();
                let lim = fb.iconst(Ty::U64, i128::from(limit));
                fb.br(search, vec![lim]);
                fb.switch_to_block(search);
                let one = fb.iconst(Ty::U64, 1);
                let next = fb.binop(BinOp::Sub, Ty::U64, j, one);
                fb.br(search_test, vec![]);
                fb.switch_to_block(search_test);
                let zero = fb.iconst(Ty::U64, 0);
                let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, zero);
                let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, sel);
                let more = fb.binop(BinOp::And, Ty::Bool, trip, not_found);
                fb.condbr(more, search, vec![next], pre, vec![next]);
            }
            Start::Carried { first, .. } => {
                let (oh, j, s, fin) = outer.expect("outer loop");
                let zero = fb.iconst(Ty::U64, 0);
                let s0 = fb.iconst(Ty::U64, i128::from(first));
                fb.br(oh, vec![zero, s0]);
                fb.switch_to_block(oh);
                let more = fb.icmp(ICmpOp::Ult, Ty::U64, j, sel);
                fb.condbr(more, pre, vec![s], fin, vec![]);
                fb.switch_to_block(fin);
                fb.ret(vec![]);
            }
        }

        // The do-while writes `*o`, one `out` slot per outer iteration.
        fb.switch_to_block(pre);
        let o = match outer {
            Some((_, j, _, _)) => fb.gep(Ty::U64, out, vec![j]),
            None => out,
        };
        fb.br(header, vec![pre_start]);

        fb.switch_to_block(header);
        let slot = fb.gep(Ty::U64, a, vec![i]);
        let seven = fb.iconst(Ty::U64, 7);
        fb.store(Ty::U64, slot, seven);
        let value = fb.load(Ty::U64, p);
        fb.store(Ty::U64, o, value);
        let one = fb.iconst(Ty::U64, 1);
        let step = fb.add(Ty::U64, i, one);
        let stop = fb.icmp(ICmpOp::Uge, Ty::U64, step, n);
        fb.condbr(stop, done, vec![], header, vec![step]);

        fb.switch_to_block(done);
        if let (Some((oh, j, _, _)), Start::Carried { then, .. }) = (outer, shape.start) {
            let one = fb.iconst(Ty::U64, 1);
            let j2 = fb.add(Ty::U64, j, one);
            let s_next = fb.iconst(Ty::U64, i128::from(then));
            fb.br(oh, vec![j2, s_next]);
        } else {
            fb.ret(vec![]);
        }
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// Plain-Rust model over `a` (with `p = a + p_index`) and `out`.
    fn model(shape: &Shape, a: &mut [u64], p_index: usize, out: &mut [u64], n: u64, sel: u64) {
        let trips = match shape.start {
            Start::Carried { .. } => sel,
            _ => 1,
        };
        for t in 0..trips {
            let mut i = start_of(shape.start, sel, t);
            loop {
                a[i as usize] = 7;
                out[t as usize] = a[p_index];
                i += 1;
                if i >= n {
                    break;
                }
            }
        }
    }

    type Kernel = extern "C" fn(*mut u64, *const u64, *mut u64, u64, u64);

    /// JIT-run `shape` at O2 and O3 on every `(p_index, n, sel)` row; return the
    /// mismatches as text.
    fn probe(shape: &Shape, rows: &[(usize, u64, u64)]) -> Vec<String> {
        let module = build_module(shape);
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!(
                        "{} {opt_level:?}: compile refused: {error}",
                        shape.name
                    ));
                    continue;
                }
            };
            // SAFETY: the entry's trust-ir signature is (ptr, ptr, ptr, u64, u64)
            // -> (), matching `Kernel`, and `result` outlives every call.
            let entry =
                unsafe { result.buffer.get_fn_bound::<Kernel>(shape.name) }.expect("entry symbol");
            for &(p_index, n, sel) in rows {
                let mut want_a = [0u64; A_LEN];
                let mut want_out = [u64::MAX; OUT_LEN];
                model(shape, &mut want_a, p_index, &mut want_out, n, sel);
                let mut a = [0u64; A_LEN];
                let mut out = [u64::MAX; OUT_LEN];
                let base = a.as_mut_ptr();
                // SAFETY: every row keeps the start below 12 and `n <= 12`, so
                // the stores `a[s..max(n, s+1))` stay inside `a`; `p_index <
                // A_LEN`, and the outer loop writes at most `OUT_LEN` slots.
                entry.as_ref()(base, unsafe { base.add(p_index) }, out.as_mut_ptr(), n, sel);
                if a != want_a || out != want_out {
                    let slots = |v: &[u64]| -> Vec<i64> { v.iter().map(|&x| x as i64).collect() };
                    failures.push(format!(
                    "{} {opt_level:?} p=a+{p_index} n={n} sel={sel}: out {:?} (want {:?}), a {:?} (want {:?})",
                    shape.name,
                    slots(&out),
                    slots(&want_out),
                    &a[..12],
                    &want_a[..12]
                ));
                }
            }
        }
        failures
    }

    const DIAMOND_ROWS: &[(usize, u64, u64)] = &[
        (5, 1, 0),
        (5, 1, 1),
        (5, 2, 0),
        (5, 2, 1),
        (5, 5, 1),
        (5, 5, 0),
        (3, 4, 0),
        (3, 4, 1),
    ];
    const CARRIED_ROWS: &[(usize, u64, u64)] =
        &[(5, 1, 1), (5, 2, 1), (5, 2, 3), (5, 1, 3), (3, 4, 2)];

    /// The index starts at 5 when `sel != 0` and at 0 otherwise; the else arm's
    /// copy of the zero is the layout-last definition of the merged register.
    /// With `p = a + 5` and `n <= 5`, the path starting at 5 stores `a[5]` once
    /// and must then load 7 through `p`.
    #[test]
    fn store_index_start_from_diamond() {
        let shape = Shape {
            name: "ah_diamond_5_0",
            start: Start::Diamond {
                then_start: 5,
                else_start: 0,
            },
        };
        report_firing(shape.name, &build_module(&shape), PASS, KEY, "");
        let failures = probe(&shape, DIAMOND_ROWS);
        assert_no_failures(&failures);
    }

    /// The index starts at the stop of an unrolled down-counting search
    /// (`limit - 1 ..= 0`, layout-last `#0`).
    #[test]
    fn store_index_start_from_search_stop() {
        let shape = Shape {
            name: "ah_search8_down",
            start: Start::SearchDown { limit: 8 },
        };
        report_firing(shape.name, &build_module(&shape), PASS, KEY, "");
        let mut rows = Vec::new();
        for sel in 0..=9u64 {
            let s = start_of(shape.start, sel, 0) as usize;
            rows.push((s, 1, sel));
            rows.push((s, 2, sel));
        }
        let failures = probe(&shape, &rows);
        assert_no_failures(&failures);
    }

    /// The index starts at 5 on the outer loop's first iteration and at 0
    /// afterwards; the back edge's zero is the layout-last definition.
    #[test]
    fn store_index_start_carried_by_outer_loop() {
        let shape = Shape {
            name: "ah_carried_5_0",
            start: Start::Carried { first: 5, then: 0 },
        };
        report_firing(shape.name, &build_module(&shape), PASS, KEY, "");
        let failures = probe(&shape, CARRIED_ROWS);
        assert_no_failures(&failures);
    }

    /// Controls: the same shapes with the constants swapped, so the layout-last
    /// definition is the nonzero start and the pass declines today. They must
    /// stay correct whatever the resolver becomes.
    #[test]
    fn swapped_starts_stay_correct() {
        let mut failures = Vec::new();
        failures.extend(probe(
            &Shape {
                name: "ah_diamond_0_5",
                start: Start::Diamond {
                    then_start: 0,
                    else_start: 5,
                },
            },
            DIAMOND_ROWS,
        ));
        failures.extend(probe(
            &Shape {
                name: "ah_carried_0_5",
                start: Start::Carried { first: 0, then: 5 },
            },
            CARRIED_ROWS,
        ));
        assert_no_failures(&failures);
    }
}

mod mac_reg_block {
    //! `mac-reg-block` admits a counted loop of the ikj matmul nest only when its
    //! counter starts at 0. For a copy init `MovR counter, src` it read `src`
    //! with a pass-local `const_value`: `strip_copies` stopped at a register with
    //! more than one live definition, and `const_value` then read that
    //! register's definition from a LAST-WINS map. Machine IR is not SSA: the stop
    //! index of a fully unrolled down-counting early-exit search (`j = limit-1 ..=
    //! 0`, stop when `j == sel`) is one `Movz src, #k` per exit edge, the
    //! layout-last being `#0`, so the counter is admitted as starting at 0 while
    //! every early-exit path starts it at `sel`.
    //!
    //! The kernel is the bounds-checked ikj nest of
    //! `e2e_aarch64_mac_reg_block_differential` (stack-local `a`, `b`, `c` copied
    //! in from and `c` copied back out to the pointer arguments) with the j-loop
    //! starting at `S` instead of 0. When `S` resolves to its layout-last `#0`
    //! while another path starts j at `K > 0`, the tiled fast path updates
    //! `c[i*N + 0..K]`, which the scalar nest never touches.
    //!
    //! A diamond merge of two constants and a constant carried around the repeat
    //! loop reach the init as copies (`MovR src, x` per path), which
    //! `const_value` declines at the multi-def register; those shapes are
    //! correctness controls.
    //!
    //! The rows compare every element of `c`. The pass fired once at O2 and once
    //! at O3 on the search-stop shapes, and the tiled path updated
    //! `c[i*N + 0..sel]`, while the counter init was read through the last-wins
    //! map. It now declines them; its key is `mac_reg_block`.

    use super::*;
    use std::fmt::Write as _;

    const PASS: &str = "mac-reg-block";
    const KEY: &str = "mac_reg_block";
    /// Elements appended to every array (copied in and out, never indexed).
    const PAD: u64 = 8;

    #[derive(Clone, Copy, Debug)]
    struct Shape {
        name: &'static str,
        n: u64,
        start: Start,
    }

    /// The trust-ir text of `shape`:
    /// `fn(a_in: ptr, b_in: ptr, c_io: ptr, sel: i64) -> i64`.
    #[allow(clippy::too_many_lines)]
    fn kernel_ir(shape: &Shape) -> String {
        let n = shape.n;
        let len = n * n + PAD;
        let nn = n * n;
        let symbol = shape.name;
        let mut s = String::new();
        let _ = write!(
            s,
            "fn @{symbol}(functy.0) {{\n\
bb0(%0: ptr, %1: ptr, %2: ptr, %300: i64):\n\
    %3 = const i64 0\n\
    %4 = const i64 1\n\
    %5 = const i64 {n}\n\
    %8 = const i64 -1\n\
    %13 = const i64 {len}\n\
    %16 = const i64 {nn}\n\
    %10 = alloca i64, %13\n\
    %11 = alloca i64, %13\n\
    %12 = alloca i64, %13\n"
        );
        // The repeat count (`%19`) and the start value `%S` (= `%301`) the
        // j-loops begin at; the repeat loop header `bb4` carries `%S` for the
        // carried shape.
        match shape.start {
            Start::Diamond {
                then_start,
                else_start,
            } => {
                let _ = write!(
                    s,
                    "    %19 = const i64 1\n\
    %302 = icmp ne i64 %300, %3\n\
    condbr %302, bb60, bb61\n\
bb60:\n\
    %303 = const i64 {then_start}\n\
    br bb62(%303)\n\
bb61:\n\
    %304 = const i64 {else_start}\n\
    br bb62(%304)\n\
bb62(%301: i64):\n\
    br bb1(%3)\n"
                );
            }
            Start::SearchDown { limit } => {
                let _ = write!(
                    s,
                    "    %19 = const i64 1\n\
    %305 = const i64 {limit}\n\
    br bb70(%305)\n\
bb70(%310: i64):\n\
    %311 = sub i64 %310, %4\n\
    br bb71\n\
bb71:\n\
    %314 = icmp ne i64 %311, %3\n\
    %315 = icmp ne i64 %311, %300\n\
    %316 = and bool %314, %315\n\
    condbr %316, bb70(%311), bb62(%311)\n\
bb62(%301: i64):\n\
    br bb1(%3)\n"
                );
            }
            Start::Carried { .. } => {
                let _ = writeln!(s, "    %19 = add i64 %300, %3\n    br bb1(%3)");
            }
        }
        // Whole-cell copy loop `dst[t] = src[t]` for t in 0..len.
        let copy = |s: &mut String, bb: u32, next: &str, src: &str, dst: &str, v: u32| {
            let _ = write!(
                s,
                "bb{bb}(%{v}: i64):\n\
    %{v1} = icmp ult i64 %{v}, %13\n\
    condbr %{v1}, bb{body}, {next}\n\
bb{body}:\n\
    %{v2} = gep i64, ptr {src}, %{v}\n\
    %{v3} = load i64, ptr %{v2}\n\
    %{v4} = gep i64, ptr {dst}, %{v}\n\
    store i64 %{v3}, ptr %{v4}\n\
    %{v5} = add i64 %{v}, %4\n\
    br bb{bb}(%{v5})\n",
                v1 = v + 1,
                v2 = v + 2,
                v3 = v + 3,
                v4 = v + 4,
                v5 = v + 5,
                body = bb + 100,
            );
        };
        let r_entry = match shape.start {
            Start::Carried { first, .. } => {
                let _ = writeln!(
                    s,
                    "bb63:\n    %306 = const i64 {first}\n    br bb4(%3, %306)"
                );
                "bb63"
            }
            _ => "bb4(%3)",
        };
        copy(&mut s, 1, "bb2(%3)", "%0", "%10", 200);
        copy(&mut s, 2, "bb3(%3)", "%1", "%11", 210);
        copy(&mut s, 3, r_entry, "%2", "%12", 220);
        let carried = matches!(shape.start, Start::Carried { .. });
        let _ = write!(
            s,
            "bb4(%30: i64{sp}):\n\
    %31 = icmp ult i64 %30, %19\n\
    condbr %31, bb5(%3), bb40(%3)\n\
bb5(%40: i64):\n\
    %42 = icmp ult i64 %40, %5\n\
    condbr %42, bb6, bb39\n\
bb6:\n\
    br bb7(%3)\n\
bb7(%50: i64):\n\
    %52 = icmp ult i64 %50, %5\n\
    condbr %52, bb8, bb14\n\
bb8:\n\
    %53 = mul i64 %40, %5\n\
    %54 = add i64 %53, %50\n\
    %55 = icmp ult i64 %54, %16\n\
    condbr %55, bb9, bb90\n\
bb9:\n\
    %56 = gep i64, ptr %10, %54\n\
    %57 = load i64, ptr %56\n\
    br bb10(%301)\n\
bb10(%60: i64):\n\
    %61 = icmp ult i64 %60, %5\n\
    condbr %61, bb11, bb13\n\
bb11:\n\
    %62 = mul i64 %40, %5\n\
    %63 = add i64 %62, %60\n\
    %64 = icmp ult i64 %63, %16\n\
    condbr %64, bb12, bb90\n\
bb12:\n\
    %65 = mul i64 %50, %5\n\
    %66 = add i64 %65, %60\n\
    %67 = icmp ult i64 %66, %16\n\
    condbr %67, bb15, bb90\n\
bb15:\n\
    %68 = gep i64, ptr %12, %63\n\
    %69 = load i64, ptr %68\n\
    %70 = gep i64, ptr %11, %66\n\
    %71 = load i64, ptr %70\n\
    %72 = mul i64 %57, %71\n\
    %73 = add i64 %69, %72\n\
    store i64 %73, ptr %68\n\
    %74 = add i64 %60, %4\n\
    br bb10(%74)\n\
bb13:\n\
    %75 = add i64 %50, %4\n\
    br bb7(%75)\n\
bb14:\n\
    %76 = add i64 %40, %4\n\
    br bb5(%76)\n\
bb39:\n\
    {c307}%32 = add i64 %30, %4\n\
    br bb4(%32{sl})\n\
bb40(%80: i64):\n\
    %81 = icmp ult i64 %80, %13\n\
    condbr %81, bb41, bb42\n\
bb41:\n\
    %82 = gep i64, ptr %12, %80\n\
    %83 = load i64, ptr %82\n\
    %84 = gep i64, ptr %2, %80\n\
    store i64 %83, ptr %84\n\
    %85 = add i64 %80, %4\n\
    br bb40(%85)\n\
bb42:\n\
    ret %3\n\
bb90:\n\
    ret %8\n\
}}\n",
            sp = if carried { ", %301: i64" } else { "" },
            sl = if carried { ", %307" } else { "" },
            c307 = match shape.start {
                Start::Carried { then, .. } => format!("%307 = const i64 {then}\n"),
                _ => String::new(),
            },
        );
        s
    }

    fn module(shape: &Shape) -> trust_ir::Module {
        let text = format!(
            "; TrustIr text format v1\nmodule \"mrbmd\"\ntarget \"{TRIPLE}\" 8 little abi=\"aapcs64\"\n\
         functy.0 = (ptr, ptr, ptr, i64) -> (i64)\n{}",
            kernel_ir(shape)
        );
        trust_ir::parser::parse_module(&text)
            .unwrap_or_else(|error| panic!("{}: trust-ir parse: {error:?}\n{text}", shape.name))
    }

    /// Plain-Rust model: the return value and the final `c_io`.
    fn model(shape: &Shape, a_in: &[u64], b_in: &[u64], c_io: &[u64], sel: u64) -> (u64, Vec<u64>) {
        let n = shape.n;
        let a = a_in.to_vec();
        let b = b_in.to_vec();
        let mut c = c_io.to_vec();
        let reps = match shape.start {
            Start::Carried { .. } => sel,
            _ => 1,
        };
        for rep in 0..reps {
            for i in 0..n {
                for k in 0..n {
                    let aik = a[(i * n + k) as usize];
                    let mut j = start_of(shape.start, sel, rep);
                    while j < n {
                        let ci = (i * n + j) as usize;
                        let bi = (k * n + j) as usize;
                        c[ci] = c[ci].wrapping_add(aik.wrapping_mul(b[bi]));
                        j += 1;
                    }
                }
            }
        }
        (0, c)
    }

    fn fill(len: usize, seed: u64) -> Vec<u64> {
        let mut x = seed | 1;
        (0..len)
            .map(|_| {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                x % 1000
            })
            .collect()
    }

    type Kernel = extern "C" fn(*const u64, *const u64, *mut u64, u64) -> u64;

    /// JIT-run `shape` at O2 and O3 for every selector; return the mismatches.
    fn probe(shape: &Shape, sels: &[u64]) -> Vec<String> {
        let module = module(shape);
        let len = (shape.n * shape.n + PAD) as usize;
        let a_in = fill(len, 0x1234_5678);
        let b_in = fill(len, 0x9abc_def0);
        let c0 = fill(len, 0x0f0f_1111);
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!(
                        "{} {opt_level:?}: compile refused: {error}",
                        shape.name
                    ));
                    continue;
                }
            };
            // SAFETY: the entry's trust-ir signature is (ptr, ptr, ptr, i64) ->
            // i64, matching `Kernel`, and `result` outlives every call.
            let entry =
                unsafe { result.buffer.get_fn_bound::<Kernel>(shape.name) }.expect("entry symbol");
            for &sel in sels {
                let (want_ret, want_c) = model(shape, &a_in, &b_in, &c0, sel);
                let mut c = c0.clone();
                let ret = entry.as_ref()(a_in.as_ptr(), b_in.as_ptr(), c.as_mut_ptr(), sel);
                if ret != want_ret || c != want_c {
                    let first = c.iter().zip(&want_c).position(|(x, y)| x != y);
                    failures.push(format!(
                    "{} {opt_level:?} sel={sel}: ret {ret:#x} (want {want_ret:#x}), first c diff at {first:?}{}",
                    shape.name,
                    first.map_or(String::new(), |k| format!(
                        ": got {} want {}",
                        c[k], want_c[k]
                    )),
                ));
                }
            }
        }
        failures
    }

    /// The j-loops start where an unrolled down-counting search stopped
    /// (`7 ..= 0`, layout-last `Movz #0`). `strip_copies` stops at the multi-def
    /// register and `const_value` reads its layout-last `Movz #0`, so the counter
    /// is admitted as starting at 0. For `sel` in `1..=7` the scalar nest starts
    /// every j-loop at `sel`; the tiled fast path updates `c[i*N + 0..sel]` too.
    #[test]
    fn j_start_from_search_stop() {
        let mut failures = Vec::new();
        for shape in [
            Shape {
                name: "mrb_search8_down_n16",
                n: 16,
                start: Start::SearchDown { limit: 8 },
            },
            Shape {
                name: "mrb_search8_down_n24",
                n: 24,
                start: Start::SearchDown { limit: 8 },
            },
        ] {
            report_firing(shape.name, &module(&shape), PASS, KEY, "");
            failures.extend(probe(&shape, &(0..=9).collect::<Vec<_>>()));
        }
        assert_no_failures(&failures);
    }

    /// Controls: a diamond merge or a repeat-loop carry reaches the j-loop's init
    /// as copies (`MovR s, x` per path), and `const_value` declines a copy at the
    /// multi-def register today, so the pass does not fire. They must stay
    /// correct whatever the resolver becomes.
    #[test]
    fn copy_defined_starts_stay_correct() {
        let mut failures = Vec::new();
        for shape in [
            Shape {
                name: "mrb_diamond_3_0_n16",
                n: 16,
                start: Start::Diamond {
                    then_start: 3,
                    else_start: 0,
                },
            },
            Shape {
                name: "mrb_diamond_0_3_n16",
                n: 16,
                start: Start::Diamond {
                    then_start: 0,
                    else_start: 3,
                },
            },
        ] {
            failures.extend(probe(&shape, &[0, 1]));
        }
        for shape in [
            Shape {
                name: "mrb_carried_3_0_n16",
                n: 16,
                start: Start::Carried { first: 3, then: 0 },
            },
            Shape {
                name: "mrb_carried_0_3_n16",
                n: 16,
                start: Start::Carried { first: 0, then: 3 },
            },
        ] {
            failures.extend(probe(&shape, &[1, 2, 3]));
        }
        assert_no_failures(&failures);
    }
}

mod reduction {
    //! `closed-form-reduction` (`ClosedFormReduction`) and `reduction-split`
    //! (`ReductionSplit`) both require the induction's start to be a compile-time
    //! constant and read it with `reduction_split::resolve_const` on the
    //! preheader copy's source. That resolver scanned every out-of-loop definition
    //! of the register in layout order and kept the last `Movz`/`MovI`/`Movk`
    //! value; any other definition (a copy) makes it decline. Machine IR is not
    //! SSA: the stop index of a fully unrolled early-exit search (`j = 1..=limit`,
    //! stop when `j == sel`) is one `Movz r, #k` per exit edge, the layout-last
    //! being `#limit`, so the resolver reports `limit` while every early-exit
    //! path starts at `sel`.
    //!
    //! A diamond merge of two constants and a constant carried around an outer
    //! loop reach the preheader as copies (`MovR r, x` per path), which the
    //! resolver declines; those shapes are correctness controls.
    //!
    //! Both passes fired on the search-stop shapes (with `looplatch` off for
    //! reduction-split) and summed from the layout-last start while
    //! `resolve_const` kept the last constant definition. They now decline them.
    //! The shapes' `Start` is this module's own: its search counts up.

    use super::*;
    use trust_ir::{BinOp, ICmpOp, Ty};
    use trust_ir_build::{FunctionBuilder, ModuleBuilder};

    /// Where the reduction's induction starts.
    #[derive(Clone, Copy, Debug)]
    enum Start {
        /// Where an early-exit search `j = 1..=limit, stop when j == sel` stopped.
        SearchStop { limit: u64 },
        /// `sel != 0 ? then_start : else_start`, merged in a block parameter.
        Diamond { then_start: u64, else_start: u64 },
        /// An outer loop of `trips` (run-time) iterations re-enters the reduction
        /// at `first` on its first iteration and at `then` afterwards.
        Carried { first: u64, then: u64 },
    }

    /// The reduction's term `f(i)`.
    #[derive(Clone, Copy, Debug)]
    enum Term {
        /// `i * i` (a degree-2 polynomial: the closed form's shape).
        Square,
        /// `3 * i + 5` (degree 1).
        Affine,
        /// `(i * i) ^ (i * 3)` (no closed form: reduction-split's shape).
        XorPoly,
    }

    /// The header's continue test.
    #[derive(Clone, Copy, Debug)]
    enum Limit {
        /// `i <u n` with the run-time `n` argument.
        Param,
        /// `i <u N` with a constant `N`.
        Const(u64),
    }

    #[derive(Clone, Copy, Debug)]
    struct Shape {
        name: &'static str,
        start: Start,
        term: Term,
        limit: Limit,
        /// Test `i >=u LIMIT` and branch to the exit on true (`cmp; b.hs exit;
        /// b body`), the header orientation `reduction-split` recognizes, instead
        /// of `i <u LIMIT` branching to the body.
        exit_on_true: bool,
    }

    fn term(fb: &mut FunctionBuilder<'_>, t: Term, i: trust_ir::ValueId) -> trust_ir::ValueId {
        match t {
            Term::Square => fb.mul(Ty::U64, i, i),
            Term::Affine => {
                let three = fb.iconst(Ty::U64, 3);
                let m = fb.mul(Ty::U64, i, three);
                let five = fb.iconst(Ty::U64, 5);
                fb.add(Ty::U64, m, five)
            }
            Term::XorPoly => {
                let sq = fb.mul(Ty::U64, i, i);
                let three = fb.iconst(Ty::U64, 3);
                let m = fb.mul(Ty::U64, i, three);
                fb.binop(BinOp::Xor, Ty::U64, sq, m)
            }
        }
    }

    fn term_model(t: Term, i: u64) -> u64 {
        match t {
            Term::Square => i.wrapping_mul(i),
            Term::Affine => i.wrapping_mul(3).wrapping_add(5),
            Term::XorPoly => i.wrapping_mul(i) ^ i.wrapping_mul(3),
        }
    }

    /// `fn(sel: u64, n: u64, trips: u64) -> u64`:
    ///
    /// ```text
    /// s = START(sel)
    /// acc = 0; i = s
    /// while i <u LIMIT { acc += f(i); i += 1 }
    /// return acc
    /// ```
    ///
    /// With `Start::Carried`, the reduction runs inside
    /// `for j in 0..trips { ...; total = total * 31 + acc }` and the next
    /// iteration starts at `then`.
    fn build_module(shape: &Shape) -> trust_ir::Module {
        let mut mb = ModuleBuilder::new(shape.name);
        let fty = mb.add_func_type(vec![Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]);
        let mut fb = mb.function(shape.name, fty);
        let entry = fb.create_block();
        let sel = fb.add_block_param(entry, Ty::U64);
        let n_rt = fb.add_block_param(entry, Ty::U64);
        let trips = fb.add_block_param(entry, Ty::U64);

        let pre = fb.create_block();
        let pre_start = fb.add_block_param(pre, Ty::U64);
        let header = fb.create_block();
        let iv = fb.add_block_param(header, Ty::U64);
        let acc = fb.add_block_param(header, Ty::U64);
        let body = fb.create_block();
        let exit = fb.create_block();
        let exit_acc = fb.add_block_param(exit, Ty::U64);

        // Outer loop `oh(j, total, s)` and its exit `done(t)` (Carried only).
        let outer = if let Start::Carried { .. } = shape.start {
            let oh = fb.create_block();
            let j = fb.add_block_param(oh, Ty::U64);
            let total = fb.add_block_param(oh, Ty::U64);
            let s = fb.add_block_param(oh, Ty::U64);
            let done = fb.create_block();
            let t = fb.add_block_param(done, Ty::U64);
            Some((oh, j, total, s, done, t))
        } else {
            None
        };

        fb.switch_to_block(entry);
        match shape.start {
            Start::SearchStop { limit } => {
                let search = fb.create_block();
                let j = fb.add_block_param(search, Ty::U64);
                let search_test = fb.create_block();
                let zero = fb.iconst(Ty::U64, 0);
                fb.br(search, vec![zero]);
                fb.switch_to_block(search);
                let one = fb.iconst(Ty::U64, 1);
                let next = fb.add(Ty::U64, j, one);
                fb.br(search_test, vec![]);
                fb.switch_to_block(search_test);
                let lim = fb.iconst(Ty::U64, i128::from(limit));
                let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, lim);
                let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, sel);
                let more = fb.binop(BinOp::And, Ty::Bool, trip, not_found);
                fb.condbr(more, search, vec![next], pre, vec![next]);
            }
            Start::Diamond {
                then_start,
                else_start,
            } => {
                let then_b = fb.create_block();
                let else_b = fb.create_block();
                let zero = fb.iconst(Ty::U64, 0);
                let c = fb.icmp(ICmpOp::Ne, Ty::U64, sel, zero);
                fb.condbr(c, then_b, vec![], else_b, vec![]);
                fb.switch_to_block(then_b);
                let s = fb.iconst(Ty::U64, i128::from(then_start));
                fb.br(pre, vec![s]);
                fb.switch_to_block(else_b);
                let s = fb.iconst(Ty::U64, i128::from(else_start));
                fb.br(pre, vec![s]);
            }
            Start::Carried { first, .. } => {
                let (oh, j, total, s, done, t) = outer.expect("outer loop");
                let zero = fb.iconst(Ty::U64, 0);
                let s0 = fb.iconst(Ty::U64, i128::from(first));
                fb.br(oh, vec![zero, zero, s0]);
                fb.switch_to_block(oh);
                let more = fb.icmp(ICmpOp::Ult, Ty::U64, j, trips);
                fb.condbr(more, pre, vec![s], done, vec![total]);
                fb.switch_to_block(done);
                fb.ret(vec![t]);
            }
        }

        fb.switch_to_block(pre);
        let zero = fb.iconst(Ty::U64, 0);
        fb.br(header, vec![pre_start, zero]);

        fb.switch_to_block(header);
        let lim = match shape.limit {
            Limit::Param => n_rt,
            Limit::Const(n) => fb.iconst(Ty::U64, i128::from(n)),
        };
        if shape.exit_on_true {
            let stop = fb.icmp(ICmpOp::Uge, Ty::U64, iv, lim);
            fb.condbr(stop, exit, vec![acc], body, vec![]);
        } else {
            let go = fb.icmp(ICmpOp::Ult, Ty::U64, iv, lim);
            fb.condbr(go, body, vec![], exit, vec![acc]);
        }

        fb.switch_to_block(body);
        let t = term(&mut fb, shape.term, iv);
        let acc2 = fb.add(Ty::U64, acc, t);
        let one = fb.iconst(Ty::U64, 1);
        let iv2 = fb.add(Ty::U64, iv, one);
        fb.br(header, vec![iv2, acc2]);

        fb.switch_to_block(exit);
        if let (Some((oh, j, total, _, _, _)), Start::Carried { then, .. }) = (outer, shape.start) {
            let k31 = fb.iconst(Ty::U64, 31);
            let scaled = fb.mul(Ty::U64, total, k31);
            let total2 = fb.add(Ty::U64, scaled, exit_acc);
            let one = fb.iconst(Ty::U64, 1);
            let j2 = fb.add(Ty::U64, j, one);
            let s_next = fb.iconst(Ty::U64, i128::from(then));
            fb.br(oh, vec![j2, total2, s_next]);
        } else {
            fb.ret(vec![exit_acc]);
        }
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    fn model(shape: &Shape, sel: u64, n_rt: u64, trips: u64) -> u64 {
        let lim = match shape.limit {
            Limit::Param => n_rt,
            Limit::Const(n) => n,
        };
        let reduce = |mut i: u64| {
            let mut acc = 0u64;
            while i < lim {
                acc = acc.wrapping_add(term_model(shape.term, i));
                i += 1;
            }
            acc
        };
        match shape.start {
            Start::SearchStop { limit } => {
                let mut j = 0u64;
                let s = loop {
                    j += 1;
                    if j == limit || j == sel {
                        break j;
                    }
                };
                reduce(s)
            }
            Start::Diamond {
                then_start,
                else_start,
            } => reduce(if sel != 0 { then_start } else { else_start }),
            Start::Carried { first, then } => {
                let mut total = 0u64;
                let mut s = first;
                for _ in 0..trips {
                    total = total.wrapping_mul(31).wrapping_add(reduce(s));
                    s = then;
                }
                total
            }
        }
    }

    /// JIT-run `shape` at O2 and O3 on every `(sel, n, trips)` row; return the
    /// mismatches as text.
    fn probe(shape: &Shape, rows: &[(u64, u64, u64)]) -> Vec<String> {
        let module = build_module(shape);
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!(
                        "{} {opt_level:?}: compile refused: {error}",
                        shape.name
                    ));
                    continue;
                }
            };
            // SAFETY: the entry's trust-ir signature is (u64, u64, u64) -> u64,
            // and `result` outlives every call through `entry`.
            let entry = unsafe {
                result
                    .buffer
                    .get_fn_bound::<extern "C" fn(u64, u64, u64) -> u64>(shape.name)
            }
            .expect("entry symbol");
            for &(sel, n, trips) in rows {
                let expected = model(shape, sel, n, trips);
                let got = entry.as_ref()(sel, n, trips);
                if got != expected {
                    failures.push(format!(
                    "{} {opt_level:?} sel={sel} n={n} trips={trips}: got {got:#x}, expected {expected:#x}",
                    shape.name
                ));
                }
            }
        }
        failures
    }

    /// Changes `pass` reports for `shape` at O2 and O3 with nothing disabled.
    fn default_changes(shape: &Shape, pass: &str) -> Vec<u32> {
        let module = build_module(shape);
        [OptLevel::O2, OptLevel::O3]
            .iter()
            .map(|&opt| {
                pass_change_counts(shape.name, &module, opt, "")
                    .get(pass)
                    .copied()
                    .unwrap_or(0)
            })
            .collect()
    }

    fn search_rows(limit: u64, ns: &[u64]) -> Vec<(u64, u64, u64)> {
        let mut rows = Vec::new();
        for &n in ns {
            for key in 0..=limit + 1 {
                rows.push((key, n, 0));
            }
        }
        rows
    }

    // --- closed-form-reduction ---------------------------------------------------

    const CLOSED_FORM: &str = "closed-form-reduction";
    const CLOSED_FORM_KEY: &str = "closed_form_reduction";

    const fn shape(
        name: &'static str,
        start: Start,
        term: Term,
        limit: Limit,
        exit_on_true: bool,
    ) -> Shape {
        Shape {
            name,
            start,
            term,
            limit,
            exit_on_true,
        }
    }

    /// The closed form `F(n) - F(start)` with `start` read from a search stop
    /// register that holds `1..=limit` depending on `sel`. The register has one
    /// `Movz` per unrolled exit edge, the layout-last being `#limit`, so the
    /// closed form sums from `limit` on every path.
    #[test]
    fn closed_form_start_from_search_stop() {
        let mut failures = Vec::new();
        for shape in [
            shape(
                "cf_search8_sq",
                Start::SearchStop { limit: 8 },
                Term::Square,
                Limit::Param,
                false,
            ),
            shape(
                "cf_search8_aff",
                Start::SearchStop { limit: 8 },
                Term::Affine,
                Limit::Param,
                false,
            ),
            shape(
                "cf_search5_sq_exit_on_true",
                Start::SearchStop { limit: 5 },
                Term::Square,
                Limit::Param,
                true,
            ),
        ] {
            report_firing(
                shape.name,
                &build_module(&shape),
                CLOSED_FORM,
                CLOSED_FORM_KEY,
                "",
            );
            failures.extend(probe(&shape, &search_rows(8, &[0, 5, 9, 100])));
        }
        assert_no_failures(&failures);
    }

    /// Controls: a diamond merge or an outer-loop carry reaches the preheader as
    /// copies (`MovR s, x`), which `resolve_const` declines today, so the pass
    /// does not fire. They must stay correct whatever the resolver becomes.
    #[test]
    fn closed_form_copy_defined_starts_stay_correct() {
        let mut failures = Vec::new();
        for shape in [
            shape(
                "cf_diamond_0_7_sq",
                Start::Diamond {
                    then_start: 0,
                    else_start: 7,
                },
                Term::Square,
                Limit::Param,
                false,
            ),
            shape(
                "cf_diamond_7_0_sq",
                Start::Diamond {
                    then_start: 7,
                    else_start: 0,
                },
                Term::Square,
                Limit::Param,
                false,
            ),
        ] {
            failures.extend(probe(
                &shape,
                &[(0, 100, 0), (1, 100, 0), (0, 3, 0), (1, 3, 0)],
            ));
        }
        for shape in [
            shape(
                "cf_carried_0_7_sq",
                Start::Carried { first: 0, then: 7 },
                Term::Square,
                Limit::Param,
                false,
            ),
            shape(
                "cf_carried_7_0_sq",
                Start::Carried { first: 7, then: 0 },
                Term::Square,
                Limit::Param,
                false,
            ),
        ] {
            failures.extend(probe(&shape, &[(0, 100, 1), (0, 100, 3), (0, 5, 2)]));
        }
        assert_no_failures(&failures);
    }

    // --- reduction-split ---------------------------------------------------------

    const REDUCTION_SPLIT: &str = "reduction-split";
    const REDUCTION_SPLIT_KEY: &str = "redsplit";

    /// `loop-latch-layout` (key `looplatch`) runs before `reduction-split` and
    /// rotates every two-block loop of the shape `reduction-split` recognizes
    /// (`cmp iv, limit; b.hs exit; b latch`), so in the default pipeline the pass
    /// does not see this loop. With `looplatch` disabled it does.
    const ROTATION_KEY: &str = "looplatch";

    fn rs_search_shapes() -> [Shape; 2] {
        [
            shape(
                "rs_search8_xor_c64",
                Start::SearchStop { limit: 8 },
                Term::XorPoly,
                Limit::Const(64),
                true,
            ),
            shape(
                "rs_search8_xor_rt",
                Start::SearchStop { limit: 8 },
                Term::XorPoly,
                Limit::Param,
                true,
            ),
        ]
    }

    /// Default pipeline: reduction-split does not fire on the search-stop shape
    /// (the loop is rotated first), and the result is correct.
    #[test]
    fn reduction_split_search_stop_default_pipeline() {
        let mut failures = Vec::new();
        for shape in rs_search_shapes() {
            assert_eq!(
                default_changes(&shape, REDUCTION_SPLIT),
                [0, 0],
                "{}: reduction-split fired in the default pipeline",
                shape.name
            );
            if !std::env::var("TRUST_CG_DISABLE_PASSES")
                .is_ok_and(|v| v.split(',').any(|k| k.trim() == ROTATION_KEY))
            {
                failures.extend(probe(&shape, &search_rows(8, &[0, 5, 9, 100])));
            }
        }
        assert_no_failures(&failures);
    }

    /// reduction-split with the start read from a search stop register (layout
    /// last `#limit`). With a constant limit the pass checks `limit - start` is a
    /// multiple of its split factor for the wrong start and runs the 4-wide loop
    /// from the real one; with a run-time limit it seeds its polynomial
    /// difference engine with `L(limit)` instead of `L(start)`.
    ///
    /// The JIT has no per-compile disable list, so the run-time comparison needs
    /// the process-level control:
    /// `TRUST_CG_DISABLE_PASSES=looplatch` (reproduces) and
    /// `TRUST_CG_DISABLE_PASSES=looplatch,redsplit` (clears).
    #[test]
    #[ignore = "needs TRUST_CG_DISABLE_PASSES=looplatch: loop-latch-layout rotates the loop before reduction-split runs"]
    fn reduction_split_start_from_search_stop() {
        let ambient = std::env::var("TRUST_CG_DISABLE_PASSES").unwrap_or_default();
        assert!(
            ambient.split(',').any(|k| k.trim() == ROTATION_KEY),
            "run with TRUST_CG_DISABLE_PASSES={ROTATION_KEY} (optionally ,{REDUCTION_SPLIT_KEY})"
        );
        let mut failures = Vec::new();
        for shape in rs_search_shapes() {
            report_firing(
                shape.name,
                &build_module(&shape),
                REDUCTION_SPLIT,
                REDUCTION_SPLIT_KEY,
                ROTATION_KEY,
            );
            failures.extend(probe(&shape, &search_rows(8, &[0, 5, 9, 100])));
        }
        assert_no_failures(&failures);
    }

    /// Controls (see `closed_form_copy_defined_starts_stay_correct`).
    #[test]
    fn reduction_split_copy_defined_starts_stay_correct() {
        let mut failures = Vec::new();
        for limit in [Limit::Param, Limit::Const(64)] {
            failures.extend(probe(
                &shape(
                    "rs_diamond_0_7_xor",
                    Start::Diamond {
                        then_start: 0,
                        else_start: 7,
                    },
                    Term::XorPoly,
                    limit,
                    true,
                ),
                &[(0, 100, 0), (1, 100, 0), (0, 3, 0), (1, 3, 0)],
            ));
            failures.extend(probe(
                &shape(
                    "rs_carried_0_7_xor",
                    Start::Carried { first: 0, then: 7 },
                    Term::XorPoly,
                    limit,
                    true,
                ),
                &[(0, 100, 1), (0, 100, 3), (0, 5, 2)],
            ));
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
