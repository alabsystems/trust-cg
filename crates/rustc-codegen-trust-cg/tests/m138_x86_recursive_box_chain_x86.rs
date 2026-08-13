// E2E (x86_64-apple-darwin): FUZZ-10 pins for the RECURSIVE pure-Box drop glue
// (commit 80eea9f: `boxed_payload_drop_recursively_lowerable` +
// `emit_recursive_payload_drop` + `lower_box_drop_recursive` — inner-before-outer
// dealloc-only glue for `Box^N`, N<=5, no-drop leaf).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ----------------------------------------------------------------------------
// WHAT THIS PINS (from the FUZZ-10 adversarial differential sweep — ~45 programs
// x O0/O2/O3 x panic=abort/unwind, direct tcg-binary-vs-LLVM-binary, plus
// `leaks -atExit` and MallocErrorAbort/Scribble/GuardEdges heap oracles: the
// sweep found ZERO live miscompiles, ZERO leaks, ZERO double-frees on every
// admitted shape — this file pins the boundary so it STAYS that way):
//
//   POSITIVE (live, must keep matching LLVM):
//     * `Box^5` with an i64 leaf — the DEEPEST admitted chain (the cap is 4
//       droppable payload levels; the no-drop leaf at depth 5 is admitted by
//       the leaf-first check). Exercised at panic=abort AND panic=unwind.
//     * a depth-3 chain built by MOVING existing boxes in (`Box::new(a)`) —
//       the ctor stores a runtime box pointer, not a fresh literal.
//     * a `u128` leaf at depth 3 — the dealloc size/align pair (16,16) differs
//       from the pointer levels' (8,8); a swapped pair is a wrong dealloc.
//     * a depth-1 user-`Drop` guard ADJACENT to a live chain — the recursive
//       arm must not perturb the untouched custom-Drop path (base-10
//       accumulator drop-order oracle).
//     * a scope-end (non-explicit-`drop`) chain drop.
//     * a depth-4 chain returned from a callee (return-slot binding).
//   Each positive also passes the heap oracles on the trust-cg binary:
//     `leaks -atExit` reports 0 leaks (every level freed — no missed dealloc)
//     and MallocErrorAbort+Scribble+GuardEdges leaves the exit code unchanged
//     (no double-free, no use-after-free — a wrong free aborts loudly).
//
//   NEGATIVE (fail-closed-or-match tripwires; MUST NEVER be a silent wrong
//   value — each has a built-in value oracle so if a future widening admits
//   the shape, the test PROMOTES to a differential instead of passing vacuously):
//     * `Box^6` — one droppable level past the MAX_BOX_DROP_RECURSION_DEPTH=4
//       cap. Fails closed today; if admitted, must exit 17.
//     * `Box<Box<Guard>>` — a USER `Drop` at depth 2. THE paramount invariant:
//       a user Drop is NEVER silently skipped. Fails closed today; if admitted,
//       must exit 43 (40 + the guard's accumulator write — a skipped guard
//       exits 40, a double-run 73... any wrong value trips).
//     * `Box<Box<Vec<i64>>>` — a slot-modeled collection payload (the
//       [TCG-BOX-SLOT-ESCAPE] frame-lifetime hazard). Fails closed today; if
//       admitted, must exit 6.
//
// MIRROR INVARIANT REMINDER (for whoever widens the glue): the predicate
// `boxed_payload_drop_recursively_lowerable` and the emitter
// `emit_recursive_payload_drop` must stay arm-for-arm mirrored; this test's
// negative tripwires are the end-to-end backstop for that invariant.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";
const MACOS_DEPLOYMENT_TARGET: &str = "13.0";

fn pinned_toolchain() -> String {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let toolchain = std::fs::read_to_string(crate_dir.join("rust-toolchain.toml"))
        .expect("failed to read rust-toolchain.toml");
    for line in toolchain.lines() {
        let line = line.trim();
        if let Some(raw_channel) = line.strip_prefix("channel") {
            let Some((_, value)) = raw_channel.split_once('=') else {
                continue;
            };
            return value.trim().trim_matches('"').to_owned();
        }
    }
    panic!("rust-toolchain.toml did not contain a channel");
}

fn ensure_dylib_built() -> PathBuf {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let target_dir = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| crate_dir.join("target"));
    for cand in [
        target_dir
            .join("release")
            .join("librustc_codegen_trust_cg.dylib"),
        target_dir
            .join("debug")
            .join("librustc_codegen_trust_cg.dylib"),
    ] {
        if cand.exists() {
            return cand;
        }
    }
    let status = Command::new("cargo")
        .arg(format!("+{}", pinned_toolchain()))
        .args(["build"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run m138 test");
    let built = target_dir
        .join("debug")
        .join("librustc_codegen_trust_cg.dylib");
    assert!(built.exists(), "expected dylib at {built:?} but none produced");
    built
}

fn host_is_x86_64_macos() -> bool {
    cfg!(all(target_os = "macos", target_arch = "x86_64"))
}

fn x86_64_std_available() -> bool {
    Command::new("rustup")
        .args(["target", "list", "--installed", "--toolchain"])
        .arg(pinned_toolchain())
        .output()
        .map(|o| {
            String::from_utf8_lossy(&o.stdout)
                .lines()
                .any(|l| l.trim() == TARGET)
        })
        .unwrap_or(false)
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_m138_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile `src` to a fully linked bin at `dir/<stem>` (rustc drives the link),
/// through the bridge when `dylib` is `Some`, else plain LLVM. Returns
/// `Ok(bin)` or `Err(stderr)` on a compile/link failure (the tcg side failing
/// is a fail-closed signal the caller inspects; an LLVM failure is a broken
/// fixture).
fn compile_bin(
    dylib: Option<&Path>,
    dir: &Path,
    src_body: &str,
    stem: &str,
    opt: &str,
    panic: &str,
) -> Result<PathBuf, String> {
    let src = dir.join(format!("{stem}.rs"));
    std::fs::write(&src, src_body).expect("write source");
    let bin = dir.join(stem);
    let mut cmd = Command::new("rustup");
    cmd.env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET);
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"]);
    if let Some(dylib) = dylib {
        let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
        s.push(dylib);
        cmd.arg(&s).env("TCG_NO_PROOF_CERTS", "1");
    }
    cmd.args(["--target", TARGET])
        .arg(format!("-Cpanic={panic}"))
        .args(["-Coverflow-checks=off", "-Ccodegen-units=1"])
        .arg(format!("-Copt-level={opt}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src);
    let out = cmd.output().expect("spawn rustc via rustup");
    if out.status.success() && bin.exists() {
        Ok(bin)
    } else {
        Err(String::from_utf8_lossy(&out.stderr).into_owned())
    }
}

/// Run `bin` with extra env; returns (exit_code_or_neg_signal, stdout, stderr).
fn run_bin(bin: &Path, envs: &[(&str, &str)]) -> (i32, String, String) {
    let mut cmd = Command::new(bin);
    for (k, v) in envs {
        cmd.env(k, v);
    }
    let out = cmd.output().expect("run compiled binary");
    let code = out.status.code().unwrap_or_else(|| {
        #[cfg(unix)]
        {
            use std::os::unix::process::ExitStatusExt;
            return -out.status.signal().unwrap_or(-1);
        }
        #[cfg(not(unix))]
        -1
    });
    (
        code,
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

// ---------------------------------------------------------------------------
// Positive fixtures (validated live + matching in the FUZZ-10 sweep).
// ---------------------------------------------------------------------------

/// Deepest admitted chain: Box^5, i64 leaf, read + explicit drop. Exit 13.
const SRC_CHAIN5: &str = r#"
use std::hint::black_box;
fn main() {
    let b = Box::new(Box::new(Box::new(Box::new(Box::new(black_box(13i64))))));
    let v = *****b;
    drop(b);
    std::process::exit(v as i32);
}
"#;

/// Depth-3 chain built by MOVING existing boxes in (runtime pointer stores in
/// the ctor, not nested literals). Exit 61.
const SRC_REBOX3: &str = r#"
use std::hint::black_box;
fn main() {
    let a = Box::new(black_box(61i64));
    let b = Box::new(a);
    let c = Box::new(b);
    let v = ***c;
    drop(c);
    std::process::exit(v as i32);
}
"#;

/// u128 leaf at depth 3: the leaf dealloc pair is (16,16), the pointer levels
/// are (8,8) — a level/pair mix-up is a wrong dealloc. Exit 64.
const SRC_U128_D3: &str = r#"
use std::hint::black_box;
fn main() {
    let b = Box::new(Box::new(Box::new(black_box(64u128))));
    let v = ***b;
    drop(b);
    std::process::exit(v as i32);
}
"#;

/// Depth-1 user-Drop guard ADJACENT to a chain: the recursive arm must not
/// perturb the untouched custom-Drop path. Accumulator: chain freed, then
/// ORDER=2, then guard ORDER=27; exit 27 + **chain(3) = 30.
const SRC_GUARD_ADJACENT: &str = r#"
use std::hint::black_box;
static mut ORDER: i64 = 0;
struct G(i64);
impl Drop for G {
    fn drop(&mut self) { unsafe { ORDER = ORDER * 10 + self.0; } }
}
fn main() {
    let g = Box::new(G(black_box(7)));
    let chain = Box::new(Box::new(black_box(3i64)));
    let v = **chain;
    drop(chain);
    unsafe { ORDER = ORDER * 10 + 2; }
    drop(g);
    std::process::exit((unsafe { ORDER } + v) as i32);
}
"#;

/// Scope-end (drop-elaboration-driven, no explicit `drop`) chain drop. Exit 59.
const SRC_SCOPE_DROP: &str = r#"
use std::hint::black_box;
fn main() {
    let v;
    {
        let b = Box::new(Box::new(Box::new(black_box(59i64))));
        v = ***b;
    }
    std::process::exit(v as i32);
}
"#;

/// Depth-4 chain RETURNED from a callee (return-slot binding), then dropped in
/// main. Exit 66.
const SRC_FNRET_D4: &str = r#"
use std::hint::black_box;
fn make(n: i64) -> Box<Box<Box<Box<i64>>>> { Box::new(Box::new(Box::new(Box::new(n)))) }
fn main() {
    let b = make(black_box(66i64));
    let v = ****b;
    drop(b);
    std::process::exit(v as i32);
}
"#;

// ---------------------------------------------------------------------------
// Negative fixtures (fail-closed today; each carries a VALUE ORACLE so a
// future admission is forced into the differential, never a vacuous pass).
// ---------------------------------------------------------------------------

/// Box^6 — one droppable payload level past the depth cap. Exit 17 if live.
const SRC_D6_OVER_CAP: &str = r#"
use std::hint::black_box;
fn main() {
    let b = Box::new(Box::new(Box::new(Box::new(Box::new(Box::new(black_box(17i64)))))));
    let v = ******b;
    drop(b);
    std::process::exit(v as i32);
}
"#;

/// A USER `Drop` at depth 2 (`Box<Box<G>>`). The guard's side effect is the
/// oracle: exit 43 = 40 + ORDER(3). A silently-skipped guard would exit 40.
const SRC_GUARD_DEPTH2: &str = r#"
use std::hint::black_box;
static mut ORDER: i64 = 0;
struct G(i64);
impl Drop for G {
    fn drop(&mut self) { unsafe { ORDER = ORDER * 10 + self.0; } }
}
fn main() {
    let a = Box::new(Box::new(G(black_box(3))));
    drop(a);
    std::process::exit(unsafe { ORDER } as i32 + 40);
}
"#;

/// A slot-modeled collection payload under two boxes. Exit 6 if live.
const SRC_BOX_BOX_VEC: &str = r#"
use std::hint::black_box;
fn main() {
    let b = Box::new(Box::new(vec![black_box(1i64), 2, 3]));
    let v: i64 = (**b).iter().sum();
    drop(b);
    std::process::exit(v as i32);
}
"#;

struct Positive {
    stem: &'static str,
    src: &'static str,
    expect_exit: i32,
    /// (opt, panic) configs to pin. All were live+matching in the sweep.
    configs: &'static [(&'static str, &'static str)],
}

struct Negative {
    stem: &'static str,
    src: &'static str,
    /// Exit required IF a future widening admits the shape.
    expect_exit_if_live: i32,
}

fn positives() -> Vec<Positive> {
    vec![
        Positive {
            stem: "chain5",
            src: SRC_CHAIN5,
            expect_exit: 13,
            configs: &[("0", "abort"), ("3", "abort"), ("0", "unwind"), ("3", "unwind")],
        },
        Positive {
            stem: "rebox3",
            src: SRC_REBOX3,
            expect_exit: 61,
            configs: &[("0", "abort"), ("3", "abort")],
        },
        Positive {
            stem: "u128_d3",
            src: SRC_U128_D3,
            expect_exit: 64,
            configs: &[("0", "abort"), ("3", "abort")],
        },
        Positive {
            stem: "guard_adjacent",
            src: SRC_GUARD_ADJACENT,
            expect_exit: 30,
            configs: &[("0", "abort"), ("3", "abort")],
        },
        Positive {
            stem: "scope_drop",
            src: SRC_SCOPE_DROP,
            expect_exit: 59,
            configs: &[("0", "abort"), ("3", "abort")],
        },
        Positive {
            stem: "fnret_d4",
            src: SRC_FNRET_D4,
            expect_exit: 66,
            configs: &[("0", "abort"), ("3", "abort")],
        },
    ]
}

fn negatives() -> Vec<Negative> {
    vec![
        Negative {
            stem: "d6_over_cap",
            src: SRC_D6_OVER_CAP,
            expect_exit_if_live: 17,
        },
        Negative {
            stem: "guard_depth2",
            src: SRC_GUARD_DEPTH2,
            expect_exit_if_live: 43,
        },
        Negative {
            stem: "box_box_vec",
            src: SRC_BOX_BOX_VEC,
            expect_exit_if_live: 6,
        },
    ]
}

/// `leaks -atExit` on `bin`: Some(report line) if the tool produced a leak
/// count, None if the tool is unavailable / produced no report (soft-skip; the
/// exit-code differential and malloc-debug oracle still ran).
fn leaks_report(bin: &Path) -> Option<String> {
    let out = Command::new("/usr/bin/leaks")
        .arg("-atExit")
        .arg("--")
        .arg(bin)
        .output()
        .ok()?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    stdout
        .lines()
        .find(|l| l.contains("total leaked bytes"))
        .map(|l| l.trim().to_owned())
}

/// POSITIVES: every admitted recursive-chain shape matches the LLVM binary's
/// exit code AND passes the heap oracles (0 leaks; malloc-debug exit
/// unchanged = no double-free / use-after-free).
#[test]
fn recursive_box_chain_positive_shapes_match_llvm_and_heap_oracles_x86_64() {
    if !host_is_x86_64_macos() {
        eprintln!("skipping: requires an x86_64-apple-darwin host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("pos");

    let mut failures: Vec<String> = Vec::new();
    for case in positives() {
        for (opt, panic) in case.configs {
            let tag = format!("{}.p{panic}.O{opt}", case.stem);
            let llvm = compile_bin(None, &dir, case.src, &format!("{}_l_{panic}_{opt}", case.stem), opt, panic)
                .unwrap_or_else(|e| panic!("FIXTURE BROKEN: LLVM could not compile {tag}: {e}"));
            let tcg = match compile_bin(
                Some(&dylib),
                &dir,
                case.src,
                &format!("{}_t_{panic}_{opt}", case.stem),
                opt,
                panic,
            ) {
                Ok(bin) => bin,
                Err(e) => {
                    // A positive REGRESSING to fail-closed is safe but loses
                    // the pinned coverage — fail the test so it is looked at.
                    failures.push(format!(
                        "{tag}: was live in FUZZ-10, now fails closed: {}",
                        e.lines().rev().take(4).collect::<Vec<_>>().join(" | ")
                    ));
                    continue;
                }
            };
            let (lc, _, _) = run_bin(&llvm, &[]);
            let (tc, _, _) = run_bin(&tcg, &[]);
            if lc != tc || tc != case.expect_exit {
                failures.push(format!(
                    "{tag}: MISCOMPILE llvm_exit={lc} tcg_exit={tc} expected={}",
                    case.expect_exit
                ));
                continue;
            }
            // Heap oracle 1: double-free / UAF — malloc debug must not change
            // the exit code (a wrong free aborts under MallocErrorAbort).
            let (mdc, _, mde) = run_bin(
                &tcg,
                &[
                    ("MallocErrorAbort", "1"),
                    ("MallocScribble", "1"),
                    ("MallocPreScribble", "1"),
                    ("MallocGuardEdges", "1"),
                ],
            );
            if mdc != tc {
                failures.push(format!(
                    "{tag}: MALLOC-DEBUG divergence exit={mdc} (plain={tc}): {}",
                    mde.lines().rev().take(3).collect::<Vec<_>>().join(" | ")
                ));
                continue;
            }
            // Heap oracle 2: leak — every chain level freed exactly once.
            match leaks_report(&tcg) {
                Some(line) if line.contains("0 leaks for 0 total leaked bytes") => {}
                Some(line) => {
                    failures.push(format!("{tag}: LEAK on trust-cg binary: {line}"));
                    continue;
                }
                None => eprintln!("note: {tag}: leaks tool unavailable/no report (soft-skip)"),
            }
        }
    }
    assert!(
        failures.is_empty(),
        "m138 recursive-box-chain positives failed:\n{}",
        failures.join("\n")
    );
}

/// NEGATIVES: the over-cap / user-Drop-at-depth / collection-payload shapes
/// FAIL CLOSED — and if a future widening admits one, it must produce the
/// exact expected value (tripwire-promotes to a differential; never a vacuous
/// pass, never a silently skipped user Drop).
#[test]
fn recursive_box_chain_negative_shapes_fail_closed_or_match_x86_64() {
    if !host_is_x86_64_macos() {
        eprintln!("skipping: requires an x86_64-apple-darwin host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("neg");

    let mut failures: Vec<String> = Vec::new();
    for case in negatives() {
        for opt in ["0", "3"] {
            let tag = format!("{}.O{opt}", case.stem);
            match compile_bin(
                Some(&dylib),
                &dir,
                case.src,
                &format!("{}_t_{opt}", case.stem),
                opt,
                "abort",
            ) {
                Err(stderr) => {
                    // Fail-closed is the pinned state — but it must be the
                    // LOUD compile error, not a link/tool accident.
                    if !stderr.contains("error") {
                        failures.push(format!(
                            "{tag}: compile failed without a rustc error (tool breakage?): {}",
                            stderr.lines().rev().take(4).collect::<Vec<_>>().join(" | ")
                        ));
                    }
                }
                Ok(bin) => {
                    // TRIPWIRE FIRED: the shape went live. It must now be
                    // CORRECT — run it and require the exact value oracle.
                    let (tc, _, _) = run_bin(&bin, &[]);
                    if tc != case.expect_exit_if_live {
                        failures.push(format!(
                            "{tag}: shape went LIVE and MISCOMPILES: exit={tc} expected={} \
                             (a user Drop skipped / wrong depth glue?)",
                            case.expect_exit_if_live
                        ));
                    } else {
                        eprintln!(
                            "note: {tag}: previously fail-closed shape is now LIVE and correct \
                             (exit={tc}); promote it to the positive differential set"
                        );
                    }
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "m138 recursive-box-chain negatives failed:\n{}",
        failures.join("\n")
    );
}
