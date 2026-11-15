// Compiled only on an aarch64-apple-darwin host: the rows are x86-64 programs
// run under Rosetta (`support/x86_rosetta.rs`), the route the bridge's other
// x86-64 run rows (`opt_loop_state_run`) use.
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/loop_state_program.rs"]
mod loop_state;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;
#[path = "support/x86_rosetta.rs"]
mod x86_rosetta_support;

// Integration test: the x86-64 register allocator's split copies survive the
// replay into the emitted stream, checked on whole x86_64-apple-darwin programs
// through this bridge against the LLVM oracle.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Each kernel copies a `[u64; N]` through `black_box` and folds it with a
// second carried register `t`. At O3 the backend's x86 frame-slot forwarding
// turns the array reads into register copies into one multiply-defined
// destination, greedy splitting then leaves split children whose only readers
// are those original copies, and the replay of the allocator's stream into the
// x86 instruction stream must keep every split copy such a reader reads. The
// rule is stated once, on `replay_x86_regalloc_stream_mutations` in
// trust-cg-codegen's `src/x86_64/pipeline.rs`; its unit tests and
// `tests/e2e_x86_64_split_copy_replay.rs` (two of these kernels as bridge
// dumps) pin it below the bridge. These rows guard the whole bridge path.
//
// Before the rule (this test against a bridge built from trust-cg `a0603f3bc`,
// whose replay is the one the rule replaced; measured 2026-10-01, x86-64 under
// Rosetta 2): 10 of the 20 rows failed, all at O3. `k_xsh::<8>` printed
// 5374597959403525797 (LLVM 8275365051531202673) and `pop64_ref::<8>` printed
// 199 (LLVM 309); the other eight O3 rows were refused
// `[TCG-POST-RA-SPILL-INIT]`, a spilled split child read with no store. Every
// O2 row agreed.
//
// Every compile uses the backend's no-proof-certs knob: the rows judge
// codegen, not proof promotion (the x86-64 opcode inventory has no promotable
// evidence today, so the default lane refuses every x86-64 program at proof
// promotion). Test-rung evidence; a run under Rosetta qualifies Rosetta's
// execution of the x86-64 code, not a native x86-64 machine. Nothing here is a
// proof.

use loop_state::{Bridge, Target, compile, run, workdir};
use std::fmt::Write as _;

/// One kernel: its name, the loop-body statement over `x = a[i]` and `acc`,
/// the trip counts it runs at, and its value computed on the host.
struct Kernel {
    name: &'static str,
    body: &'static str,
    trips: &'static [usize],
    host: fn(u64, u64) -> u64,
}

const KERNELS: &[Kernel] = &[
    Kernel {
        name: "k_xsh",
        body: "acc = acc.wrapping_add(x ^ (x >> 29) ^ (x << 7));",
        trips: &[8, 12, 16],
        host: |acc, x| acc.wrapping_add(x ^ (x >> 29) ^ (x << 7)),
    },
    Kernel {
        name: "k_mul",
        body: "acc = acc.wrapping_add((x ^ (x >> 29)).wrapping_mul(0x2545_F491_4F6C_DD1D));",
        trips: &[8, 12, 16],
        host: |acc, x| acc.wrapping_add((x ^ (x >> 29)).wrapping_mul(0x2545_F491_4F6C_DD1D)),
    },
    Kernel {
        name: "k_rot",
        body: "acc = acc.wrapping_add(x.rotate_left(13) ^ (x >> 3));",
        trips: &[8, 12, 16],
        host: |acc, x| acc.wrapping_add(x.rotate_left(13) ^ (x >> 3)),
    },
    Kernel {
        name: "pop64_ref",
        body: "acc += x.count_ones() as u64;",
        trips: &[8],
        host: |acc, x| acc + u64::from(x.count_ones()),
    },
];

const OPTS: &[&str] = &["2", "3"];

/// The kernels' input: `s[k] = k * 0x9E3779B97F4A7C15` (wrapping).
fn input(k: usize) -> u64 {
    (k as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
}

/// The value `kernel::<n>` returns, computed on the host.
fn host_value(kernel: &Kernel, n: usize) -> u64 {
    let mut acc = 0u64;
    let mut t = 0u64;
    for i in 0..n {
        acc = (kernel.host)(acc, input(i));
        t = t.wrapping_add(i as u64 * 3 + 1);
    }
    acc ^ t.wrapping_mul(5)
}

/// The `no_std` program for one row: it calls `kernel::<n>` once and prints
/// `name n value` through libSystem's `write`.
///
/// The program is spelled so that every function reaches this backend's
/// register allocator as a well-formed module:
/// * no array is indexed. Every element access is a thin raw pointer
///   (`&raw const a as *const u64`) read or written at an offset its loop
///   bounds (the kernel's `i < N`, `main`'s `k < n`, `put`'s at most
///   9 + 2 * 21 + 1 of 96 bytes). An index carries a bounds check, a source
///   Assert, which the bridge refuses under `panic=abort` (`[TCG-ASSERT-PANIC]`)
///   before register allocation, so an indexed row would test nothing here;
/// * no slice and no byte-string literal. `a.as_ptr()` on an array goes through
///   an unsized `&[u64]`, and `b"..."` is a reference-typed constant; the
///   bridge lowers both into modules `trust-ir validate` rejects
///   (`FieldAccessInvalid`, `ConstTypeMismatch`), so `put` builds the name
///   from byte literals.
///
/// Measured 2026-10-01 on all 20 rows: the optimized MIR has no Assert,
/// unsizing or UB-check branch, and every module the bridge dumps
/// (`dump-trust-ir`) passes `trust-ir validate`. This test does not re-check
/// either; a row the bridge refuses fails it by name.
fn program_source(kernel: &Kernel, n: usize) -> String {
    let name_bytes: Vec<String> = kernel
        .name
        .bytes()
        .map(|b| format!("b'{}'", b as char))
        .collect();
    let mut src = String::from(
        "#![no_std]\n#![no_main]\n\
         use core::hint::black_box;\n\
         extern \"C\" {\n    fn write(fd: i32, buf: *const u8, len: usize) -> isize;\n    fn abort() -> !;\n}\n\
         #[panic_handler]\nfn panic(_: &core::panic::PanicInfo) -> ! { unsafe { abort() } }\n",
    );
    let _ = write!(
        src,
        "#[inline(never)]\nfn put(n: usize, value: u64) {{\n\
         \x20   let name: [u8; {name_len}] = [{name_bytes}];\n\
         \x20   let mut line = [0u8; 96];\n    let out = &raw mut line as *mut u8;\n    let mut len = 0usize;\n\
         \x20   while len < {name_len} {{ unsafe {{ *out.add(len) = *(&raw const name as *const u8).add(len); }} len += 1; }}\n\
         \x20   let mut field = 0usize;\n\
         \x20   while field < 2 {{\n\
         \x20       let mut x = if field == 0 {{ n as u64 }} else {{ value }};\n\
         \x20       unsafe {{ *out.add(len) = b' '; }}\n        len += 1;\n\
         \x20       let mut digits = [0u8; 20];\n        let d = &raw mut digits as *mut u8;\n        let mut count = 0usize;\n\
         \x20       loop {{ unsafe {{ *d.add(count) = b'0' + (x % 10) as u8; }} count += 1; x /= 10; if x == 0 {{ break; }} }}\n\
         \x20       while count > 0 {{ count -= 1; unsafe {{ *out.add(len) = *d.add(count); }} len += 1; }}\n\
         \x20       field += 1;\n\
         \x20   }}\n\
         \x20   unsafe {{ *out.add(len) = b'\\n'; }}\n    len += 1;\n\
         \x20   unsafe {{ write(1, out as *const u8, len); }}\n}}\n\
         #[inline(never)]\nfn {name}<const N: usize>(src: &[u64; N]) -> u64 {{\n\
         \x20   let a = black_box(*src);\n\
         \x20   let mut acc: u64 = 0;\n    let mut t: u64 = 0;\n    let mut i = 0usize;\n\
         \x20   while i < N {{ let x = unsafe {{ *(&raw const a as *const u64).add(i) }}; {body} t = t.wrapping_add(i as u64 * 3 + 1); i += 1; }}\n\
         \x20   black_box(acc ^ t.wrapping_mul(5))\n}}\n\
         #[no_mangle]\npub extern \"C\" fn main(_argc: i32, _argv: *const *const u8) -> i32 {{\n\
         \x20   let mut s = [0u64; {n}];\n    let p = &raw mut s as *mut u64;\n    let mut k = 0usize;\n\
         \x20   while k < {n} {{ unsafe {{ *p.add(k) = (k as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15); }} k += 1; }}\n\
         \x20   put({n}, {name}::<{n}>(black_box(&s)));\n\
         \x20   0\n}}\n",
        name = kernel.name,
        name_len = kernel.name.len(),
        name_bytes = name_bytes.join(", "),
        body = kernel.body,
    );
    src
}

/// The distinct `[TCG-...]` codes in a refused compile's diagnostics.
fn tcg_codes(stderr: &str) -> String {
    let mut codes: Vec<&str> = stderr
        .match_indices("[TCG-")
        .filter_map(|(at, _)| stderr[at..].find(']').map(|end| &stderr[at..=at + end]))
        .collect();
    codes.sort_unstable();
    codes.dedup();
    if codes.is_empty() {
        "no [TCG-*] code".to_string()
    } else {
        codes.join(" ")
    }
}

#[test]
fn x86_64_split_copies_survive_the_regalloc_replay_on_whole_programs() {
    if let x86_rosetta_support::X86Exec::Unavailable(reason) =
        x86_rosetta_support::x86_execution(OPTS[0])
    {
        panic!("x86-64 rows: this Apple-silicon host has no x86-64 execution route: {reason}");
    }
    let dylib = backend_artifact_support::current_test_backend();
    let knobs = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    let bridge = Bridge {
        dylib: &dylib,
        knobs: &knobs,
    };
    let mut rows = 0usize;
    let mut failures = Vec::new();
    for &opt in OPTS {
        for kernel in KERNELS {
            for &n in kernel.trips {
                rows += 1;
                let row = format!("{}::<{n}> O{opt}", kernel.name);
                let expected = format!("{} {n} {}", kernel.name, host_value(kernel, n));
                let src = program_source(kernel, n);
                let dir = workdir(&format!("x86_split_copy_{}_{n}_O{opt}", kernel.name));
                // The LLVM build is the oracle, and the host's own computation
                // checks the oracle: a disagreement there is a harness defect.
                let oracle_bin = compile(&dir, "row", &src, Target::X86_64, opt, None, true)
                    .unwrap_or_else(|e| panic!("{row}: LLVM failed to compile:\n{e}"));
                let (oracle_code, oracle_out) = run(&oracle_bin, Target::X86_64, opt);
                assert_eq!(oracle_code, Some(0), "{row}: the LLVM oracle ran");
                assert_eq!(
                    oracle_out.trim_end(),
                    expected,
                    "{row}: the LLVM oracle disagrees with the host computation"
                );
                match compile(&dir, "row", &src, Target::X86_64, opt, Some(bridge), true) {
                    Err(stderr) => failures.push(format!(
                        "{row}: refused by the bridge ({}), LLVM `{expected}`",
                        tcg_codes(&stderr)
                    )),
                    Ok(bin) => {
                        let (code, out) = run(&bin, Target::X86_64, opt);
                        if code != Some(0) || out.trim_end() != expected {
                            failures.push(format!(
                                "{row}: WRONG `{}` (exit {code:?}), LLVM `{expected}`",
                                out.trim_end()
                            ));
                        }
                    }
                }
                let _ = std::fs::remove_dir_all(&dir);
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {rows} x86-64 split-copy row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    println!("X86_SPLIT_COPY_REPLAY rows={rows} matched={rows}");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
