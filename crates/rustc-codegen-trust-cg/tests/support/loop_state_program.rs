//! The whole-program rows of trust-cg-opt's loop-state contract, run by
//! `opt_loop_state_run.rs` for aarch64 (native) and x86-64 (native, or under
//! Rosetta through `x86_rosetta.rs`).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! A vectorizer, unroller or idiom rewrite that runs new code INSTEAD OF some
//! of a scalar loop's iterations reproduces only the registers it names: the
//! induction and its accumulators. Any other register the loop carries across
//! its back edge (a second accumulator), or leaves live at an exit (a
//! `last = i`), keeps the value it had before the skipped iterations. And it
//! decides only the exits it names: a `break`, a `return` or a bounds check
//! the skipped iterations would have taken is run past. trust-cg-opt states
//! that rule once (`crates/trust-cg-opt/src/loop_contract.rs`, its control and
//! register clauses) and routes every such rewrite through it.
//!
//! THE PROGRAM. One `no_std` program, identical source on both targets: every
//! kernel is an `#[inline(never)]` function generic over the trip count `N`
//! and its array length `L = max(N, 1)` (the bridge refuses a dynamic index
//! into a zero-length array by name, a separate fail-closed limit), with its
//! own local arrays (the shape the x86 recognizers require), for each `N` in
//! [`TRIPS`]: empty, one, one short of a vector block and exactly one block
//! (16 and 64 bytes), 1000 (a scalar remainder) and 1024 (an EMPTY
//! remainder, the live-out trigger). Each prints `kernel N value` through
//! libSystem's `write`, and the bridge's output must equal LLVM's line for
//! line. The `last = i` rows come in two loop forms: top-tested (the header
//! half of the rule sees `last`) and bottom-tested with `last` written first
//! (only the exit half sees it). Both compile the whole program,
//! `-Cpanic=abort -Ccodegen-units=1`, at
//! O2 and O3; the bridge with the backend knobs the calling fixture builds
//! (the rows judge codegen, not proof promotion).
//!
//! THE EARLY-EXIT ROWS ([`EXIT_KERNELS`], in the same program). Fills and
//! zero-fills (u8, u32 and u64; constant and runtime values) whose loop also
//! leaves by a `break` or a `return` at index 40 (inside the first vector
//! block) or 700 (inside the vector prefix of N = 1000 and 1024), with a
//! constant or a runtime stop, and the same `break` over a safe slice. Before
//! the contract's control clause `neon_fill` ran its vector loop past such an
//! exit whenever the exit index lay inside the vector prefix, so the loop left
//! with `i = N` and filled past the exit: 30 of these rows wrong at each of O2
//! and O3 on aarch64 (none at N = 0, 1 or 15), measured 2026-09-30 at
//! `c84d39e93` and on this change before the clause, the same rows at both;
//! x86-64 agreed. The remaining early-exit kernels (byte-sum, i32-sum, count,
//! strided store) are regression rows: their passes declined the shape
//! already.
//!
//! PERFORMANCE SIDE. A gate that bails too much would pass the rows by
//! vectorizing nothing. So [`check_target`] also requires the bridge binary
//! to keep the vector code of the kernels with no extra state (`count_only`,
//! `bsum_only`, `isum_only`, and on aarch64 `fill_only`; x86-64 fills through
//! a runtime call, not SSE code).
//!
//! This module never builds a backend knob itself: each fixture passes the
//! argument it built with `toolchain_support::backend_knobs_arg`. It is
//! test-rung evidence; nothing here is a proof.
#![allow(dead_code)]

use std::path::{Path, PathBuf};
use std::process::Command;

pub const TRIPS: &[usize] = &[0, 1, 15, 16, 63, 64, 1000, 1024];
pub const OPTS: &[&str] = &["2", "3"];

/// One kernel: a name, the element and accumulator types, the array
/// initializer (in `k`), the loop body (over `a`, `acc`, `i`) and the result
/// (over `a`, `acc`, `N`). `extra` selects the state beside the kernel's own.
pub struct Kernel {
    pub name: &'static str,
    pub elem: &'static str,
    pub acc: &'static str,
    pub init: &'static str,
    pub body: &'static str,
    pub result: &'static str,
    pub extra: Extra,
}

/// The register state beside the kernel's own `acc` / `i`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Extra {
    /// Nothing added: the controls the rewrite must still vectorize, and
    /// `countif_sum_arm`, whose body updates the declared `t` itself.
    None,
    /// A second accumulator carried across the back edge,
    /// `t = t + (3i + 1)` — the p09 `sum += i` beside `count += 1`.
    Carried,
    /// A register live out of the loop only: `last = i`.
    LiveOut,
    /// The same `last = i`, in a bottom-tested loop that writes it FIRST:
    /// `if N > 0 { loop { last = i; .. ; i += 1; if i == N { break } } }`.
    /// The loop header defines `last` before any read, so it is not live into
    /// the header; only an exit reads it, and only the contract's EXIT half
    /// can see it. The `LiveOut` rows do not need the exit half: with it
    /// removed every row still agreed (measured 2026-09-30). No pass
    /// vectorizes this bottom-tested shape today (0 vector instructions at O2
    /// on either target, before and after the contract), so these rows guard a
    /// future rewrite of it; the exit half's evidence is the contract's unit
    /// table, not these rows.
    LiveOutRotated,
}

pub const KERNELS: &[Kernel] = &[
    // --- a second carried register (the design's and challenge's sweep) ---
    Kernel {
        name: "bsum_carried",
        elem: "u8",
        acc: "u64",
        init: "((k * 37) % 251) as u8",
        body: "acc += a[i] as u64;",
        result: "acc",
        extra: Extra::Carried,
    },
    Kernel {
        name: "cnt0_carried",
        elem: "u8",
        acc: "u64",
        init: "if k % 7 == 3 { 0 } else { 1 }",
        body: "if a[i] == 0 { acc += 1; }",
        result: "acc",
        extra: Extra::Carried,
    },
    Kernel {
        name: "pop_carried",
        elem: "u8",
        acc: "u64",
        init: "((k * 37) % 251) as u8",
        body: "acc += (a[i] as u32).count_ones() as u64;",
        result: "acc",
        extra: Extra::Carried,
    },
    Kernel {
        name: "fill_carried",
        elem: "u8",
        acc: "u64",
        init: "0",
        body: "a[i] = 7;",
        result: "if N == 0 { 0 } else { a[N / 2] as u64 + a[N - 1] as u64 }",
        extra: Extra::Carried,
    },
    Kernel {
        name: "zero_carried",
        elem: "u32",
        acc: "u64",
        init: "(k as u32) | 1",
        body: "a[i] = 0;",
        result: "if N == 0 { 0 } else { a[N / 2] as u64 + a[N - 1] as u64 }",
        extra: Extra::Carried,
    },
    // The p09 shape itself: the count-if arm updates a second register.
    Kernel {
        name: "countif_sum_arm",
        elem: "u8",
        acc: "u64",
        init: "if k % 7 == 3 || k % 11 == 5 { 0 } else { 1 }",
        body: "if a[i] == 0 { acc += 1; t = t.wrapping_add(i as u64); }",
        result: "acc",
        extra: Extra::None,
    },
    // --- a register live out of the loop only (the challenge's new rows) ---
    Kernel {
        name: "bsum_last",
        elem: "u8",
        acc: "u64",
        init: "((k * 37) % 251) as u8",
        body: "acc += a[i] as u64;",
        result: "acc",
        extra: Extra::LiveOut,
    },
    Kernel {
        name: "cnt0_last",
        elem: "u8",
        acc: "u64",
        init: "if k % 7 == 3 { 0 } else { 1 }",
        body: "if a[i] == 0 { acc += 1; }",
        result: "acc",
        extra: Extra::LiveOut,
    },
    Kernel {
        name: "pop_last",
        elem: "u8",
        acc: "u64",
        init: "((k * 37) % 251) as u8",
        body: "acc += (a[i] as u32).count_ones() as u64;",
        result: "acc",
        extra: Extra::LiveOut,
    },
    Kernel {
        name: "fill_last",
        elem: "u8",
        acc: "u64",
        init: "0",
        body: "a[i] = 7;",
        result: "if N == 0 { 0 } else { a[N / 2] as u64 + a[N - 1] as u64 }",
        extra: Extra::LiveOut,
    },
    Kernel {
        name: "zero_last",
        elem: "u32",
        acc: "u64",
        init: "(k as u32) | 1",
        body: "a[i] = 0;",
        result: "if N == 0 { 0 } else { a[N / 2] as u64 + a[N - 1] as u64 }",
        extra: Extra::LiveOut,
    },
    // --- `last = i` written first in a bottom-tested loop (exit half only) ---
    Kernel {
        name: "bsum_last_rot",
        elem: "u8",
        acc: "u64",
        init: "((k * 37) % 251) as u8",
        body: "acc += a[i] as u64;",
        result: "acc",
        extra: Extra::LiveOutRotated,
    },
    Kernel {
        name: "cnt0_last_rot",
        elem: "u8",
        acc: "u64",
        init: "if k % 7 == 3 { 0 } else { 1 }",
        body: "if a[i] == 0 { acc += 1; }",
        result: "acc",
        extra: Extra::LiveOutRotated,
    },
    Kernel {
        name: "fill_last_rot",
        elem: "u8",
        acc: "u64",
        init: "0",
        body: "a[i] = 7;",
        result: "if N == 0 { 0 } else { a[N / 2] as u64 + a[N - 1] as u64 }",
        extra: Extra::LiveOutRotated,
    },
    Kernel {
        name: "zero_last_rot",
        elem: "u32",
        acc: "u64",
        init: "(k as u32) | 1",
        body: "a[i] = 0;",
        result: "if N == 0 { 0 } else { a[N / 2] as u64 + a[N - 1] as u64 }",
        extra: Extra::LiveOutRotated,
    },
    // --- an i32 reduction (`neon_array` on aarch64, the x86 `Reduce` plan) ---
    Kernel {
        name: "isum_carried",
        elem: "i32",
        acc: "i32",
        init: "((k * 37) % 251) as i32 - 100",
        body: "acc = acc.wrapping_add(a[i]);",
        result: "acc as u32 as u64",
        extra: Extra::Carried,
    },
    Kernel {
        name: "isum_last",
        elem: "i32",
        acc: "i32",
        init: "((k * 37) % 251) as i32 - 100",
        body: "acc = acc.wrapping_add(a[i]);",
        result: "acc as u32 as u64",
        extra: Extra::LiveOut,
    },
    // --- controls: nothing beside the kernel (these must stay vectorized) ---
    Kernel {
        name: "isum_only",
        elem: "i32",
        acc: "i32",
        init: "((k * 37) % 251) as i32 - 100",
        body: "acc = acc.wrapping_add(a[i]);",
        result: "acc as u32 as u64",
        extra: Extra::None,
    },
    Kernel {
        name: "count_only",
        elem: "u8",
        acc: "u64",
        init: "if k % 7 == 3 || k % 11 == 5 { 0 } else { 1 }",
        body: "if a[i] == 0 { acc += 1; }",
        result: "acc",
        extra: Extra::None,
    },
    Kernel {
        name: "fill_only",
        elem: "u8",
        acc: "u64",
        init: "0",
        body: "a[i] = 7;",
        result: "if N == 0 { 0 } else { a[N / 2] as u64 + a[N - 1] as u64 + a[0] as u64 }",
        extra: Extra::None,
    },
    Kernel {
        name: "bsum_only",
        elem: "u8",
        acc: "u64",
        init: "((k * 37) % 251) as u8",
        body: "acc += a[i] as u64;",
        result: "acc",
        extra: Extra::None,
    },
    Kernel {
        name: "sum_u64_carried",
        elem: "u64",
        acc: "u64",
        init: "((k * 37) % 251) as u64",
        body: "acc = acc.wrapping_add(a[i]);",
        result: "acc",
        extra: Extra::Carried,
    },
];

/// One early-exit kernel: its loop leaves by a `break` or a `return` as well as
/// by its own test. `code` runs over `a` (the kernel's local array of `L =
/// max(N, 1)` elements of `elem`, initialized by `init` over `k`) and binds
/// `let r: u64`; a `return` returns the function's own `u64`.
pub struct ExitKernel {
    pub name: &'static str,
    pub elem: &'static str,
    pub init: &'static str,
    pub code: &'static str,
}

/// Every early-exit kernel: the shapes the control clause refuses, and the
/// passes' own early-exit refusals kept as rows.
pub const EXIT_KERNELS: &[ExitKernel] = &[
    // --- fills (`neon_fill` on aarch64; failing-first before the clause) ---
    ExitKernel {
        name: "fill_brk40",
        elem: "u8",
        init: "0",
        code: "let mut i = 0usize;\n    \
               while i < N { a[i] = 7; if i == 40 { break; } i += 1; }\n    \
               let a = black_box(a);\n    \
               let r: u64 = (i as u64).wrapping_mul(7) \
               ^ if N == 0 { 0 } else { a[N / 2] as u64 + (a[N - 1] as u64) * 3 };",
    },
    ExitKernel {
        name: "fill_brk_before40",
        elem: "u8",
        init: "0",
        code: "let mut i = 0usize;\n    \
               while i < N { if i == 40 { break; } a[i] = 7; i += 1; }\n    \
               let a = black_box(a);\n    \
               let r: u64 = (i as u64).wrapping_mul(7) \
               ^ if N == 0 { 0 } else { a[N / 2] as u64 + (a[N - 1] as u64) * 3 };",
    },
    ExitKernel {
        name: "fill_brk700",
        elem: "u8",
        init: "0",
        code: "let mut i = 0usize;\n    \
               while i < N { a[i] = 7; if i == 700 { break; } i += 1; }\n    \
               let a = black_box(a);\n    \
               let r: u64 = (i as u64).wrapping_mul(7) \
               ^ if N == 0 { 0 } else { a[N / 2] as u64 + (a[N - 1] as u64) * 3 };",
    },
    ExitKernel {
        name: "fill_brk_rt",
        elem: "u8",
        init: "0",
        code: "let stop = black_box(40usize);\n    \
               let mut i = 0usize;\n    \
               while i < N { a[i] = 7; if i == stop { break; } i += 1; }\n    \
               let a = black_box(a);\n    \
               let r: u64 = (i as u64).wrapping_mul(7) \
               ^ if N == 0 { 0 } else { a[N / 2] as u64 + (a[N - 1] as u64) * 3 };",
    },
    ExitKernel {
        name: "fill_ret700",
        elem: "u8",
        init: "0",
        code: "let mut i = 0usize;\n    \
               while i < N { a[i] = 7; if i == 700 { return black_box(i as u64 + 11); } i += 1; }\n    \
               let a = black_box(a);\n    \
               let r: u64 = if N == 0 { 0 } else { a[N / 2] as u64 + a[N - 1] as u64 };",
    },
    ExitKernel {
        name: "fill_u32_brk40",
        elem: "u32",
        init: "0",
        code: "let mut i = 0usize;\n    \
               while i < N { a[i] = 0x0101_0101; if i == 40 { break; } i += 1; }\n    \
               let a = black_box(a);\n    \
               let r: u64 = (i as u64).wrapping_mul(7) \
               ^ if N == 0 { 0 } else { a[N / 2] as u64 + (a[N - 1] as u64) * 3 };",
    },
    ExitKernel {
        name: "fill_u64_rt_brk40",
        elem: "u64",
        init: "0",
        code: "let v = black_box(0x1234_5678_9abc_def0u64);\n    \
               let mut i = 0usize;\n    \
               while i < N { a[i] = v; if i == 40 { break; } i += 1; }\n    \
               let a = black_box(a);\n    \
               let r: u64 = (i as u64).wrapping_mul(7) \
               ^ if N == 0 { 0 } else { a[N / 2] ^ a[N - 1].rotate_left(3) };",
    },
    ExitKernel {
        name: "zero_brk40",
        elem: "u32",
        init: "(k as u32) | 1",
        code: "let mut i = 0usize;\n    \
               while i < N { a[i] = 0; if i == 40 { break; } i += 1; }\n    \
               let a = black_box(a);\n    \
               let r: u64 = (i as u64).wrapping_mul(7) \
               ^ if N == 0 { 0 } else { a[N / 2] as u64 + (a[N - 1] as u64) * 3 };",
    },
    ExitKernel {
        name: "zero_ret700",
        elem: "u32",
        init: "(k as u32) | 1",
        code: "let mut i = 0usize;\n    \
               while i < N { a[i] = 0; if i == 700 { let a = black_box(a); \
               return black_box(a[N - 1] as u64 + i as u64 * 5); } i += 1; }\n    \
               let a = black_box(a);\n    \
               let r: u64 = if N == 0 { 0 } else { a[N / 2] as u64 + a[N - 1] as u64 };",
    },
    ExitKernel {
        name: "fill_slice_brk",
        elem: "u8",
        init: "0",
        code: "let lim = black_box(40usize);\n    \
               let s = &mut a[..];\n    \
               let mut i = 0usize;\n    \
               while i < s.len() { if i == lim { break; } s[i] = 7; i += 1; }\n    \
               let a = black_box(a);\n    \
               let r: u64 = (i as u64).wrapping_mul(7) \
               ^ if N == 0 { 0 } else { a[N / 2] as u64 + (a[N - 1] as u64) * 3 };",
    },
    // --- regression rows: these passes declined an early exit already ---
    ExitKernel {
        name: "bsum_brk40",
        elem: "u8",
        init: "((k * 37) % 251) as u8",
        code: "let mut acc: u64 = 0;\n    \
               let mut i = 0usize;\n    \
               while i < N { acc += a[i] as u64; if i == 40 { break; } i += 1; }\n    \
               let r: u64 = acc ^ (i as u64).wrapping_mul(7);",
    },
    ExitKernel {
        name: "isum_brk700",
        elem: "i32",
        init: "((k * 37) % 251) as i32 - 100",
        code: "let mut acc: i32 = 0;\n    \
               let mut i = 0usize;\n    \
               while i < N { acc = acc.wrapping_add(a[i]); if i == 700 { break; } i += 1; }\n    \
               let r: u64 = (acc as u32 as u64) ^ (i as u64).wrapping_mul(7);",
    },
    ExitKernel {
        name: "cnt_ret700",
        elem: "u8",
        init: "if k % 7 == 3 { 0 } else { 1 }",
        code: "let mut acc: u64 = 0;\n    \
               let mut i = 0usize;\n    \
               while i < N { if a[i] == 0 { acc += 1; } if i == 700 { return black_box(acc * 3 + 1); } i += 1; }\n    \
               let r: u64 = acc;",
    },
    ExitKernel {
        name: "strided_brk",
        elem: "u8",
        init: "0",
        code: "let st = black_box(3usize);\n    \
               let mut q = 0usize;\n    \
               while q < N { a[q] = 9; if q == 42 { break; } q += st; }\n    \
               let a = black_box(a);\n    \
               let mut h: u64 = 0;\n    \
               let mut z = 0usize;\n    \
               while z < N { h = h.wrapping_mul(3).wrapping_add(a[z] as u64); z += 1; }\n    \
               let r: u64 = h ^ (q as u64).wrapping_mul(7);",
    },
];

/// The `no_std` program: one function per (kernel, N), printed in order.
pub fn program_source() -> String {
    let mut src = String::from(
        "#![no_std]\n#![no_main]\n\
         use core::hint::black_box;\n\
         extern \"C\" {\n    fn write(fd: i32, buf: *const u8, len: usize) -> isize;\n    fn abort() -> !;\n}\n\
         #[panic_handler]\nfn panic(_: &core::panic::PanicInfo) -> ! { unsafe { abort() } }\n\
         #[inline(never)]\nfn put(name: &[u8], n: usize, value: u64) {\n\
         \x20   let mut line = [0u8; 96];\n    let mut len = 0usize;\n\
         \x20   for &b in name { line[len] = b; len += 1; }\n\
         \x20   for v in [n as u64, value] {\n\
         \x20       line[len] = b' '; len += 1;\n\
         \x20       let mut digits = [0u8; 20];\n        let mut count = 0usize;\n        let mut x = v;\n\
         \x20       loop { digits[count] = b'0' + (x % 10) as u8; count += 1; x /= 10; if x == 0 { break; } }\n\
         \x20       while count > 0 { count -= 1; line[len] = digits[count]; len += 1; }\n\
         \x20   }\n\
         \x20   line[len] = b'\\n'; len += 1;\n\
         \x20   unsafe { write(1, line.as_ptr(), len); }\n}\n",
    );
    for kernel in KERNELS {
        let (declare, update, fold) = match kernel.extra {
            Extra::None => ("let mut t: u64 = 0;", "", "r ^ t.wrapping_mul(5)"),
            Extra::Carried => (
                "let mut t: u64 = 0;",
                "t = t.wrapping_add(i as u64 * 3 + 1);",
                "r ^ t.wrapping_mul(5)",
            ),
            Extra::LiveOut | Extra::LiveOutRotated => (
                "let mut last: usize = usize::MAX;",
                "last = i;",
                "r ^ (last as u64).wrapping_mul(7)",
            ),
        };
        let lp = if kernel.extra == Extra::LiveOutRotated {
            format!(
                "if N > 0 {{ loop {{ {update} {body} i += 1; if i == N {{ break; }} }} }}",
                body = kernel.body
            )
        } else {
            format!(
                "while i < N {{ {body} {update} i += 1; }}",
                body = kernel.body
            )
        };
        src.push_str(&format!(
            "#[inline(never)]\nfn {name}<const N: usize, const L: usize>() -> u64 {{\n\
             \x20   let mut a = [0 as {elem}; L];\n    let mut k = 0usize;\n\
             \x20   while k < L {{ a[k] = {init}; k += 1; }}\n\
             \x20   let mut a = black_box(a);\n    let mut acc: {acc} = 0;\n    {declare}\n\
             \x20   let mut i: usize = 0;\n\
             \x20   {lp}\n\
             \x20   let a = black_box(a);\n    let r: u64 = {result};\n\
             \x20   let _ = (&a, &mut acc);\n    black_box({fold})\n}}\n",
            name = kernel.name,
            elem = kernel.elem,
            acc = kernel.acc,
            init = kernel.init,
            result = kernel.result,
        ));
    }
    for kernel in EXIT_KERNELS {
        src.push_str(&format!(
            "#[inline(never)]\nfn {name}<const N: usize, const L: usize>() -> u64 {{\n\
             \x20   let mut a = [0 as {elem}; L];\n    let mut k = 0usize;\n\
             \x20   while k < L {{ a[k] = {init}; k += 1; }}\n\
             \x20   let mut a = black_box(a);\n\
             \x20   {code}\n\
             \x20   black_box(r)\n}}\n",
            name = kernel.name,
            elem = kernel.elem,
            init = kernel.init,
            code = kernel.code,
        ));
    }
    src.push_str(
        "#[no_mangle]\npub extern \"C\" fn main(_argc: i32, _argv: *const *const u8) -> i32 {\n",
    );
    let names = KERNELS
        .iter()
        .map(|kernel| kernel.name)
        .chain(EXIT_KERNELS.iter().map(|kernel| kernel.name));
    for name in names {
        for &n in TRIPS {
            src.push_str(&format!(
                "    put(b\"{name}\", {n}, {name}::<{n}, {len}>());\n",
                len = n.max(1)
            ));
        }
    }
    src.push_str("    0\n}\n");
    src
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Target {
    Aarch64,
    X86_64,
}

impl Target {
    pub fn triple(self) -> &'static str {
        match self {
            Target::Aarch64 => "aarch64-apple-darwin",
            Target::X86_64 => crate::x86_rosetta_support::X86_TARGET,
        }
    }
}

pub fn scratch_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
}

pub fn workdir(stem: &str) -> PathBuf {
    let dir = scratch_dir().join(format!("opt_loop_state_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// A bridge build: the backend dylib and the knob argument the fixture built.
#[derive(Clone, Copy)]
pub struct Bridge<'a> {
    pub dylib: &'a Path,
    pub knobs: &'a str,
}

/// Compile `src` whole with LLVM (`backend = None`) or the bridge,
/// `-Cpanic=abort`.
pub fn compile(
    dir: &Path,
    name: &str,
    src: &str,
    target: Target,
    opt: &str,
    backend: Option<Bridge<'_>>,
    no_std: bool,
) -> Result<PathBuf, String> {
    compile_with_panic(dir, name, src, target, opt, backend, no_std, "abort")
}

/// [`compile`] with the given `-Cpanic` strategy (`abort` or `unwind`).
#[allow(clippy::too_many_arguments)]
pub fn compile_with_panic(
    dir: &Path,
    name: &str,
    src: &str,
    target: Target,
    opt: &str,
    backend: Option<Bridge<'_>>,
    no_std: bool,
    panic: &str,
) -> Result<PathBuf, String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let tag = if backend.is_some() { "tcg" } else { "llvm" };
    let bin = dir.join(format!("{name}.{tag}.O{opt}"));
    let mut cmd = crate::toolchain_support::rustc_command();
    cmd.env("MACOSX_DEPLOYMENT_TARGET", "13.0")
        .args(["--crate-type", "bin", "-Ccodegen-units=1"])
        .arg(format!("-Cpanic={panic}"))
        .arg(format!("-Copt-level={opt}"));
    match (target, no_std) {
        // The x86-64 route (native, or Rosetta with the `core` it built for
        // this level) supplies the target and the link arguments.
        (Target::X86_64, _) => {
            cmd.args(crate::x86_rosetta_support::x86_execution(opt).compile_args());
        }
        (target, true) => {
            cmd.args(["--target", target.triple(), "-Clink-arg=-lSystem"]);
        }
        (target, false) => {
            cmd.args(["--target", target.triple()]);
        }
    }
    if let Some(bridge) = backend {
        let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
        arg.push(bridge.dylib);
        cmd.arg(arg).arg(bridge.knobs);
    }
    cmd.arg("-o").arg(&bin).arg(&src_path);
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(bin)
}

/// Run `bin`, compiled at `opt` for `target`; `(exit code, stdout)`.
pub fn run(bin: &Path, target: Target, opt: &str) -> (Option<i32>, String) {
    let output = match target {
        Target::Aarch64 => Command::new(bin).output().expect("run the program"),
        Target::X86_64 => crate::x86_rosetta_support::x86_execution(opt)
            .run(bin)
            .expect("this host has an x86-64 execution route"),
    };
    (
        output.status.code(),
        String::from_utf8_lossy(&output.stdout).into_owned(),
    )
}

/// The disassembly of every function whose symbol contains `name`, or `None`
/// when no symbol does (a matcher that finds nothing must not read as "no
/// vector code").
pub fn disassembly_of(bin: &Path, name: &str) -> Option<String> {
    let output = Command::new("objdump")
        .args(["-d", "--no-show-raw-insn"])
        .arg(bin)
        .output()
        .expect("run objdump");
    assert!(
        output.status.success(),
        "objdump failed for {bin:?} ({}): {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8_lossy(&output.stdout);
    let mut out = String::new();
    let mut found = false;
    let mut inside = false;
    for line in text.lines() {
        if line.ends_with(">:") {
            inside = line.contains(name);
            found |= inside;
        } else if line.is_empty() {
            inside = false;
        }
        if inside {
            out.push_str(line);
            out.push('\n');
        }
    }
    found.then_some(out)
}

/// The v0-mangled symbol fragment of `name::<n, _>` (`Kj<hex>_` is the first
/// `usize` const argument), which both backends emit here.
pub fn instance(name: &str, n: usize) -> String {
    format!("{name}Kj{n:x}_")
}

/// Vector instructions in `asm`.
pub fn vector_ops(asm: &str, target: Target) -> usize {
    let needles: &[&str] = match target {
        Target::Aarch64 => &["udot", ".16b", ".4s", "uaddlp", "stp\tq", "ldp\tq", "cnt."],
        Target::X86_64 => &[
            "psadbw", "pcmpeqb", "paddq", "paddd", "movdqu", "movdqa", "pxor",
        ],
    };
    asm.lines()
        .filter(|line| needles.iter().any(|needle| line.contains(needle)))
        .count()
}

/// The rows for one target: every (kernel, N) line equals LLVM's, at O2 and
/// O3, and the control kernels still carry vector code in the bridge binary.
pub fn check_target(target: Target, bridge: Bridge<'_>) -> Vec<String> {
    let src = program_source();
    let rows = (KERNELS.len() + EXIT_KERNELS.len()) * TRIPS.len();
    assert_eq!(
        src.matches("put(b\"").count(),
        rows,
        "the program prints one line per (kernel, N)"
    );
    let mut failures = Vec::new();
    for &opt in OPTS {
        let dir = workdir(&format!("{target:?}_O{opt}"));
        let oracle_bin = compile(&dir, "kernels", &src, target, opt, None, true)
            .unwrap_or_else(|e| panic!("{target:?} O{opt}: LLVM failed to compile:\n{e}"));
        let (oracle_code, oracle_out) = run(&oracle_bin, target, opt);
        assert_eq!(
            oracle_code,
            Some(0),
            "{target:?} O{opt}: the LLVM oracle ran"
        );
        let bridge_bin = match compile(&dir, "kernels", &src, target, opt, Some(bridge), true) {
            Ok(bin) => bin,
            Err(e) => {
                failures.push(format!(
                    "{target:?} O{opt}: the bridge failed to compile:\n{e}"
                ));
                continue;
            }
        };
        let (bridge_code, bridge_out) = run(&bridge_bin, target, opt);
        if bridge_code != Some(0) {
            failures.push(format!(
                "{target:?} O{opt}: the bridge binary exited {bridge_code:?}"
            ));
        }
        let oracle_lines: Vec<&str> = oracle_out.lines().collect();
        let bridge_lines: Vec<&str> = bridge_out.lines().collect();
        assert_eq!(
            oracle_lines.len(),
            rows,
            "{target:?} O{opt}: the oracle printed every row"
        );
        for (index, expected) in oracle_lines.iter().enumerate() {
            let got = bridge_lines.get(index).copied().unwrap_or("<missing>");
            if got != *expected {
                failures.push(format!(
                    "{target:?} O{opt}: WRONG `{got}`, LLVM `{expected}`"
                ));
            }
        }
        // x86-64 turns `fill_only` into a runtime fill call, not SSE code,
        // so its control is the two SSE kernels.
        let controls: &[&str] = match target {
            Target::Aarch64 => &["count_only", "fill_only", "bsum_only", "isum_only"],
            Target::X86_64 => &["count_only", "bsum_only", "isum_only"],
        };
        for &control in controls {
            let Some(asm) = disassembly_of(&bridge_bin, &instance(control, 1024)) else {
                failures.push(format!(
                    "{target:?} O{opt}: no symbol for {control}::<1024> in the bridge binary"
                ));
                continue;
            };
            let ops = vector_ops(&asm, target);
            eprintln!("{target:?} O{opt}: {control}::<1024> vector ops: {ops}");
            if ops == 0 {
                failures.push(format!(
                    "{target:?} O{opt}: {control}::<1024> lost its vector code"
                ));
            }
        }
        let _ = std::fs::remove_dir_all(&dir);
    }
    failures
}
