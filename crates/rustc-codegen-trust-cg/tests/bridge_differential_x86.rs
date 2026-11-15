#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// crates/rustc-codegen-trust-cg/tests/bridge_differential_x86.rs
//
// P2 BRIDGE DIFFERENTIAL HARNESS — the real two-compiler driver.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// This is the out-of-workspace half of the P2 harness. It compiles each corpus
// program TWICE — once with trustc's own LLVM backend (the ORACLE), once with the
// trust-cg codegen backend (`-Zcodegen-backend=<backend library>`) — runs
// both binaries, captures exit-code / stdout / trap-vs-value, and diffs them.
//
// WHY THIS, NOT `trust-cg-fuzz/src/jit_diff.rs`:
//   `jit_diff`'s oracle is the trust-ir INTERPRETER, which is DOWNSTREAM of the
//   MIR->trust-ir adapter. The bridge bug classes (#54/#55/#56/#69/#71/#72,
//   &mut-to-join-local) live IN that adapter, so they appear identically in the
//   interpreter oracle and the JIT test side and cancel out. The only oracle that
//   does NOT pass through trust-cg is LLVM — the build compiler's (trustc's) own
//   LLVM backend, which is what this driver uses.
//
// This file lives in the bridge crate (its own workspace, pinned to the Trust
// toolchain with `rustc_private`), NOT in `trust-cg-fuzz`, because actually invoking the bridge
// requires the `target-bridge` toolchain. It re-derives a minimal outcome model +
// diff engine inline (mirroring `trust_cg_fuzz::bridge_diff`) because the bridge
// crate cannot depend on the workspace fuzz crate; the AUTHORITATIVE, unit-tested
// versions of `RunOutcome` / `diff_outcomes` / `reduce` / `seed_corpus` are in
// `crates/trust-cg-fuzz/src/bridge_diff.rs` and are tested in
// `crates/trust-cg-fuzz/tests/bridge_diff.rs` (in-workspace, no toolchain).
//
// Run (requires target-bridge + x86_64-apple-darwin std, x86_64 host):
//     cd crates/rustc-codegen-trust-cg
//     targo --unverified test --release --locked --test bridge_differential_x86 -- --nocapture

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = host_target_support::X86_64_TARGET;

// Pin the macOS deployment target for BOTH the rustc-oracle and the trust-cg
// compile, and for the `cc` link, so the produced object's `LC_BUILD_VERSION`
// minos and the linker's version floor agree on a value the host can run. The
// differential previously failed at link time with a deployment-target/linker
// mismatch (object built-for 14.0 vs a 13.x host); pinning it low (13.0) here in
// the single place both sides shell out keeps linking + running consistent on a
// 13.x host while staying forward-compatible on newer hosts.
const MACOS_DEPLOYMENT_TARGET: &str = "13.0";

// ---------------------------------------------------------------------------
// Outcome model + diff engine (mirror of trust_cg_fuzz::bridge_diff)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum RunOutcome {
    Exited { code: i32, stdout: Vec<u8> },
    Signalled { signal: i32 },
    CompileError { stderr_tail: String },
    Timeout,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DivergenceKind {
    WrongValue,
    TrapMismatch,
    HangMismatch,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum DiffVerdict {
    Agree,
    TrustCgFailedClosed(String),
    ReferenceCompileError(String),
    Divergence {
        kind: DivergenceKind,
        detail: String,
    },
}

/// Identical contract to `trust_cg_fuzz::bridge_diff::diff_outcomes`.
fn diff_outcomes(reference: &RunOutcome, test: &RunOutcome) -> DiffVerdict {
    if let RunOutcome::CompileError { stderr_tail } = reference {
        return DiffVerdict::ReferenceCompileError(stderr_tail.clone());
    }
    if let RunOutcome::CompileError { stderr_tail } = test {
        return DiffVerdict::TrustCgFailedClosed(stderr_tail.clone());
    }
    match (reference, test) {
        (
            RunOutcome::Exited {
                code: rc,
                stdout: rs,
            },
            RunOutcome::Exited {
                code: tc,
                stdout: ts,
            },
        ) => {
            if rc == tc && rs == ts {
                DiffVerdict::Agree
            } else {
                DiffVerdict::Divergence {
                    kind: DivergenceKind::WrongValue,
                    detail: format!("llvm_exit={rc} trust_cg_exit={tc}"),
                }
            }
        }
        (RunOutcome::Signalled { .. }, RunOutcome::Signalled { .. }) => DiffVerdict::Agree,
        (RunOutcome::Exited { code, .. }, RunOutcome::Signalled { signal }) => {
            DiffVerdict::Divergence {
                kind: DivergenceKind::TrapMismatch,
                detail: format!("llvm_exit={code} trust_cg=TRAP(sig={signal})"),
            }
        }
        (RunOutcome::Signalled { signal }, RunOutcome::Exited { code, .. }) => {
            DiffVerdict::Divergence {
                kind: DivergenceKind::TrapMismatch,
                detail: format!("llvm=TRAP(sig={signal}) trust_cg_exit={code}"),
            }
        }
        (RunOutcome::Timeout, RunOutcome::Timeout) => DiffVerdict::Agree,
        (RunOutcome::Timeout, _) => DiffVerdict::Divergence {
            kind: DivergenceKind::HangMismatch,
            detail: "llvm=TIMEOUT trust_cg=ran".to_string(),
        },
        (_, RunOutcome::Timeout) => DiffVerdict::Divergence {
            kind: DivergenceKind::HangMismatch,
            detail: "llvm=ran trust_cg=TIMEOUT".to_string(),
        },
        (RunOutcome::CompileError { .. }, _) | (_, RunOutcome::CompileError { .. }) => {
            unreachable!("compile errors handled above")
        }
    }
}

// ---------------------------------------------------------------------------
// Toolchain / dylib plumbing (mirror of the established x86 bridge tests)
// ---------------------------------------------------------------------------

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn x86_64_std_available() -> bool {
    toolchain_support::target_std_available(TARGET)
}

fn host_is_x86_64() -> bool {
    cfg!(target_arch = "x86_64")
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_bridgediff_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// `abort()` stubs for `core`'s undefined diverging helpers (`panic*`, `*_fail`) so
/// the object links standalone
/// (the corpus inputs are chosen so these checks never fire). Mirrors
/// `m51_signed_narrow_x86.rs::write_panic_stubs`.
fn write_panic_stubs(dir: &Path, obj: &Path) -> PathBuf {
    let nm = Command::new("nm").arg("-u").arg(obj).output().expect("nm");
    let mut stubs = String::from("#include <stdlib.h>\n");
    for line in String::from_utf8_lossy(&nm.stdout).lines() {
        let sym = line.trim().trim_start_matches('U').trim();
        if toolchain_support::is_abort_stub_symbol(sym) {
            let c = sym.strip_prefix('_').unwrap_or(sym);
            stubs.push_str(&format!(
                "void {c}(void) __asm__(\"{sym}\"); void {c}(void){{ abort(); }}\n"
            ));
        }
    }
    let stubs_path = dir.join("stubs.c");
    std::fs::write(&stubs_path, stubs).expect("write stubs");
    stubs_path
}

/// Compile `src` with `dylib` (Some=trust-cg, None=LLVM), link with panic stubs,
/// run, and classify the result as a `RunOutcome` (exit code+stdout, signal, or
/// compile error). Returns `CompileError` instead of panicking on a compile
/// failure, so a trust-cg fail-closed is observable to the diff engine.
fn compile_link_run(stem: &str, src: &str, opt: &str, dylib: Option<&Path>) -> RunOutcome {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");

    // A STD program (no `#![no_main]`: a `fn main` that prints) cannot be
    // linked standalone from its object — `std::rt::lang_start` and
    // `std::io::_print` live in the precompiled `std`. Build it as an ordinary
    // binary instead and run that; the comparison (exit code + stdout) is the
    // same. Three corpus rows are such programs.
    if !src.contains("#![no_main]") {
        let bin = dir.join("bin");
        let mut cmd = toolchain_support::rustc_command();
        cmd.env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET);
        cmd.arg("--crate-type").arg("bin");
        if let Some(dylib) = dylib {
            let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
            backend_arg.push(dylib);
            cmd.arg(&backend_arg);
        }
        cmd.args([
            "--target",
            TARGET,
            "-Cpanic=abort",
            "-Coverflow-checks=off",
            "-Ccodegen-units=1",
        ])
        .arg(format!("-Copt-level={opt}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
        let output = cmd.output().expect("failed to spawn trustc");
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let _ = std::fs::remove_dir_all(&dir);
            return RunOutcome::CompileError {
                stderr_tail: stderr.lines().rev().take(8).collect::<Vec<_>>().join(" | "),
            };
        }
        let run = Command::new(&bin).output().expect("run compiled binary");
        let _ = std::fs::remove_dir_all(&dir);
        return match run.status.code() {
            Some(code) => RunOutcome::Exited {
                code,
                stdout: run.stdout,
            },
            None => RunOutcome::Signalled {
                signal: signal_of(&run.status),
            },
        };
    }

    let mut cmd = toolchain_support::rustc_command();
    // Pin the deployment target for BOTH backends (this function is the single
    // rustc shell-out used for the oracle and the trust-cg side): the emitted
    // object's mach-o build-version minos is set from this env, so both sides
    // produce a 13.0 floor and link identically on a 13.x host.
    cmd.env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET);
    cmd.arg("--crate-type").arg("bin");
    if let Some(dylib) = dylib {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(&backend_arg);
    }
    // Force a single codegen unit: with `--emit=obj` at opt>=2 rustc defaults to
    // splitting into many CGUs, and the trust-cg backend emits only the main
    // CGU's object, so a cross-CGU reference (e.g. `main` -> `pick`) links to an
    // undefined symbol. One CGU puts every function in one object. Applied to
    // BOTH the LLVM-oracle and trust-cg sides, so the comparison stays fair.
    cmd.args([
        "--target",
        TARGET,
        "-Cpanic=abort",
        "-Coverflow-checks=off",
        "-Ccodegen-units=1",
    ])
    .arg(format!("-Copt-level={opt}"))
    .arg("--emit=obj")
    .arg("--out-dir")
    .arg(&dir)
    .arg(&src_path);
    let output = cmd.output().expect("failed to spawn trustc");
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let _ = std::fs::remove_dir_all(&dir);
        return RunOutcome::CompileError {
            stderr_tail: stderr.lines().rev().take(8).collect::<Vec<_>>().join(" | "),
        };
    }

    let objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    assert!(!objs.is_empty(), "{stem} (opt={opt}): no object produced");
    let stubs_path = write_panic_stubs(&dir, &objs[0]);

    let bin = dir.join("bin");
    let mut link = Command::new("cc");
    // Match the object's deployment floor at link time so the linker does not
    // reject (or re-stamp) the binary with a version the 13.x host can't run.
    // Both the env and the explicit `-mmacosx-version-min` flag are set: the env
    // covers tools that read MACOSX_DEPLOYMENT_TARGET, the flag is the
    // authoritative floor passed straight through cc to ld. The C stub is also
    // compiled by this same cc invocation, so it picks up the same floor.
    link.env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET)
        .args(host_target_support::deployment_min_flags(
            MACOS_DEPLOYMENT_TARGET,
        ));
    link.arg("-o").arg(&bin);
    for obj in &objs {
        link.arg(obj);
    }
    link.arg(&stubs_path);
    let link = link.output().expect("cc link");
    if !link.status.success() {
        let stderr_tail = String::from_utf8_lossy(&link.stderr)
            .lines()
            .rev()
            .take(8)
            .collect::<Vec<_>>()
            .join(" | ");
        let _ = std::fs::remove_dir_all(&dir);
        if dylib.is_some() {
            // trust-cg produced an object the linker rejected — e.g. a referenced
            // function the backend did not emit at this opt level (m56 `pick` at
            // opt=2). The program never links, never runs, so it CANNOT silently
            // miscompile. Classify it fail-closed (safe), exactly like a compile
            // error: the differential hunts wrong VALUES, not backend coverage
            // gaps (which are loud and tracked separately, e.g. #65).
            return RunOutcome::CompileError { stderr_tail };
        }
        // The LLVM oracle must link any valid fixture; a failure here is a broken
        // corpus entry or host/toolchain problem, not a backend signal.
        panic!("{stem} (opt={opt}): LLVM-oracle link failed: <<<{stderr_tail}>>>");
    }

    let run = Command::new(&bin).output().expect("run compiled binary");
    let _ = std::fs::remove_dir_all(&dir);
    if let Some(code) = run.status.code() {
        RunOutcome::Exited {
            code,
            stdout: run.stdout,
        }
    } else {
        // No exit code => terminated by signal (a hardware trap / abort).
        let signal = signal_of(&run.status);
        RunOutcome::Signalled { signal }
    }
}

#[cfg(unix)]
fn signal_of(status: &std::process::ExitStatus) -> i32 {
    use std::os::unix::process::ExitStatusExt;
    status.signal().unwrap_or(-1)
}

#[cfg(not(unix))]
fn signal_of(_status: &std::process::ExitStatus) -> i32 {
    -1
}

// ---------------------------------------------------------------------------
// Corpus (subset of trust_cg_fuzz::bridge_diff::seed_corpus, the x86-runnable
// shapes). Each (name, bug_ref, source) maps 1:1 to a workspace corpus entry.
// ---------------------------------------------------------------------------

struct Case {
    name: &'static str,
    bug_ref: &'static str,
    src: &'static str,
}

fn corpus() -> Vec<Case> {
    vec![
        Case {
            name: "inline_hot_loop",
            bug_ref: "OPT-4: shared trust-ir-level inlining of a pure scalar leaf \
                      callee (`mix`) called in a hot loop; the compiler.rs \
                      translate_module_for_arch seam splices the body before ISel \
                      (LLVM keeps the #[inline(never)] call) — both fold the same \
                      accumulator, exit codes identical at O0/O2/O3",
            src: include_str!("bridge_corpus/inline_hot_loop.rs"),
        },
        Case {
            name: "m71_loop_carried_aggregate_field",
            bug_ref: "#71 loop-carried scalarized aggregate field",
            src: include_str!("bridge_corpus/m71_loop_carried_aggregate_field.rs"),
        },
        Case {
            name: "sib_addr_fold_matmul",
            bug_ref: "OPT-7 / LEVER 1: x86 base+index*scale (SIB) address-mode fold on \
                      8-byte array loads AND stores in a hot loop \
                      (x86_peephole::sib_addr_fold_run_on_block folds `imul index,{1,2,4,8}`/\
                      `shl` + `add base` + `mov [reg]` into MovRMSib/MovMRSib). A wrong \
                      scale/base/index/disp would corrupt the running sum; oracle exit 14 \
                      at O0/O2/O3 must match LLVM byte-for-byte",
            src: include_str!("bridge_corpus/sib_addr_fold_matmul.rs"),
        },
        Case {
            name: "strength_reduce_matmul",
            bug_ref: "OPT-3a / LEVER 2: x86 induction-variable strength reduction on a \
                      matmul-like nested loop with a NON-SIB constant stride (N=6): the \
                      per-inner-iteration `imul iv, N` becomes a preheader seed + \
                      per-outer-iteration add recurrence \
                      (trust_cg_opt::x86_strength_reduce, admission gated on the \
                      solver-proven `(iv+step)*s == iv*s + s*step` identity). A wrong \
                      seed/advance/stride or corrupted RFLAGS at the insertion points \
                      diverges the order-sensitive checksum from LLVM at O2/O3",
            src: include_str!("bridge_corpus/strength_reduce_matmul.rs"),
        },
        Case {
            name: "rev_range_iter",
            bug_ref: "reverse range `for k in (a..b).rev()` at O0: compile the libcore \
                      Rev::next body (sub-aggregate `&mut Range` ref + `&mut Rev<Range>` \
                      nested-aggregate thin-pointer call arg); order-sensitive",
            src: include_str!("bridge_corpus/rev_range_iter.rs"),
        },
        Case {
            name: "ovf_tuple_loop",
            bug_ref: "loop-carried (iN,bool) overflow tuple: back-edge threading VC proves the \
                      flag slot via a shared uninterpreted overflow symbol (was [TCG-SSA-071] \
                      fail-closed on the non-scalar (i32,bool) temp); O2/O3 admitted by proof, \
                      O0 non-inlined overflowing_add call fails closed (safe)",
            src: include_str!("bridge_corpus/ovf_tuple_loop.rs"),
        },
        Case {
            name: "stale_celled_entry_arg",
            bug_ref: "an ENTRY ARGUMENT written through an escaped `&mut` \
                      (`*identity(&mut p) = q; p.b`): every read must load its cell (was a \
                      SILENT wrong value at O0 — the incoming parameter, 20 vs 40)",
            src: include_str!("bridge_corpus/stale_celled_entry_arg.rs"),
        },
        Case {
            name: "stale_celled_local_copy",
            bug_ref: "a celled local / scalar entry argument written through an escaped \
                      `&mut`, then read (the companion shapes that failed closed before)",
            src: include_str!("bridge_corpus/stale_celled_local_copy.rs"),
        },
        Case {
            name: "partial_eightbyte_blackbox",
            bug_ref: "3/5/6/7/11-byte arrays round-tripped through `black_box`: the lane \
                      assembly must zero-extend byte/word pieces and the call result must be \
                      stored width-exactly (was garbage at O0 for 3 and 7 bytes)",
            src: include_str!("bridge_corpus/partial_eightbyte_blackbox.rs"),
        },
        Case {
            name: "cma_u128_fallback",
            bug_ref: "`u128::carrying_mul_add` calls the intrinsic's fallback body (was \
                      `carrying_mul_add width 128 is not modeled`); narrower unsigned \
                      widths stay inline",
            src: include_str!("bridge_corpus/cma_u128_fallback.rs"),
        },
        Case {
            name: "cma_signed_fallback",
            bug_ref: "signed `carrying_mul_add` (i128/i64/i32 MIN/MAX corners) through the \
                      fallback body",
            src: include_str!("bridge_corpus/cma_signed_fallback.rs"),
        },
        Case {
            name: "opt_u128_pair_args",
            bug_ref: "by-value `Option<u128>` / `Option<i128>` / `(u128, bool)` / \
                      `(u64, u128)` arguments on the x86-64 Pair lane with I128 scalars, \
                      incl. register exhaustion (was [TCG-ARG-ABI])",
            src: include_str!("bridge_corpus/opt_u128_pair_args.rs"),
        },
        Case {
            name: "fn_item_shim_aggregate_arg",
            bug_ref: "a fn-ITEM `FnPtrShim` whose tupled argument is a by-value aggregate \
                      (`Option::map(Map::into_inner)`; was `Place projection field 0 \
                      before aggregate binding`)",
            src: include_str!("bridge_corpus/fn_item_shim_aggregate_arg.rs"),
        },
        Case {
            name: "aggregate_ref_stored_as_value",
            bug_ref: "a bare `&agg` stored as a value into a closure / ADT / tuple / \
                      `Option<&T>` (`wtf8::EncodeWide::next`; was `borrowed aggregate \
                      reference used without deref`)",
            src: include_str!("bridge_corpus/aggregate_ref_stored_as_value.rs"),
        },
        Case {
            name: "nonnull_str_field_through_ref",
            bug_ref: "scalar fields read through `&S` where S's first field is `NonNull<str>` \
                      (core::panic::Location): the pointee tuple collapsed the 16-byte field \
                      to one lane (was a SILENT wrong value: 133/118 vs 68)",
            src: include_str!("bridge_corpus/nonnull_str_field_through_ref.rs"),
        },
        Case {
            name: "panic_location_unwrap",
            bug_ref: "the location a synthesized panic reports (`Option::unwrap` on None): \
                      the raise now asks rustc's caller-location walk \
                      (`caller_location_value_for`) instead of passing a raw span \
                      (was the callee's own line in core/option.rs)",
            src: include_str!("bridge_corpus/panic_location_unwrap.rs"),
        },
        Case {
            name: "ssa071_celled_return_place",
            bug_ref: "a CELLED return place (`&_0` into a ref-returning callee: core \
                      `io::error::repr::Repr::new_custom`, u64 newtype, bool, u128): Return \
                      must load the cell (was [TCG-SSA-071] `ValueId(0)` never defined)",
            src: include_str!("bridge_corpus/ssa071_celled_return_place.rs"),
        },
        Case {
            name: "celled_index_arg_custom_mir",
            bug_ref: "a CELLED entry-argument index (`p = &raw const i; i = 5; (*a)[i]`): \
                      the Index readers read the INCOMING parameter (a silent wrong value, \
                      LLVM 17 vs 5); a celled index is now loaded from its cell",
            src: include_str!("bridge_corpus/celled_index_arg_custom_mir.rs"),
        },
        Case {
            name: "celled_index_local_custom_mir",
            bug_ref: "a CELLED non-argument index local: the Index readers read the \
                      never-defined `ValueId(local)` ([TCG-SSA-071] fail closed); a celled \
                      index is now loaded from its cell",
            src: include_str!("bridge_corpus/celled_index_local_custom_mir.rs"),
        },
        Case {
            name: "celled_index_readers_custom_mir",
            bug_ref: "a CELLED entry-argument index through EVERY Index reader (array \
                      through a reference, memory-backed local array, slice read, slice \
                      store, `&(*s)[i]` borrow, `&[&dyn Tr]` element, const slice): each \
                      read the stale incoming index (checksum 198 vs LLVM 19)",
            src: include_str!("bridge_corpus/celled_index_readers_custom_mir.rs"),
        },
        Case {
            name: "ssa071_cell_retry_loops",
            bug_ref: "SSA-071 cell retry: core `overflowing_pow` (u64/u128/i128 — the \
                      in-loop join param hides `overflow`'s derivation), `maximal_suffix` \
                      (`left = right` rotation + `period = right - left`), a \
                      diamond-then-combine accumulator; the VC declines, the flagged slots \
                      are re-lowered in memory cells and every gate re-runs",
            src: include_str!("bridge_corpus/ssa071_cell_retry_loops.rs"),
        },
        Case {
            name: "niche_nested_enum",
            bug_ref: "by-value niche-encoded NESTED enum Option<Option<Result>>: admit a \
                      niche-encoded nested enum FIELD (scalar niche) in the memory-aggregate \
                      layout descent + decode the projected sub-enum discriminant via the niche \
                      formula; every arm exercised, distinct values (wrong discriminant diverges)",
            src: include_str!("bridge_corpus/niche_nested_enum.rs"),
        },
        Case {
            name: "niche_nested_enum_ref",
            bug_ref: "niche-encoded nested enum matched THROUGH A REFERENCE: \
                      `discriminant(((*r) as M).0)` (deref + downcast + field) decodes the \
                      projected sub-enum's tag at the pointer + layout offset; every arm distinct",
            src: include_str!("bridge_corpus/niche_nested_enum_ref.rs"),
        },
        Case {
            name: "m69_byval_mixed_int_sse_aggregate",
            bug_ref: "#69 by-value aggregate mixed INT+SSE eightbyte ABI",
            src: include_str!("bridge_corpus/m69_byval_mixed_int_sse_aggregate.rs"),
        },
        Case {
            name: "c6_mut_ref_to_join_local",
            bug_ref: "c6 &mut-to-join-local",
            src: include_str!("bridge_corpus/c6_mut_ref_to_join_local.rs"),
        },
        Case {
            name: "m54_call_arg_parallel_move",
            bug_ref: "#54 multi-arg call parallel-move",
            src: include_str!("bridge_corpus/m54_call_arg_parallel_move.rs"),
        },
        Case {
            name: "m55_byref_closure_capture",
            bug_ref: "#55 by-ref closure capture",
            src: include_str!("bridge_corpus/m55_byref_closure_capture.rs"),
        },
        Case {
            name: "m56_narrow_repr_enum",
            bug_ref: "#56 narrow-representation enum discriminant",
            src: include_str!("bridge_corpus/m56_narrow_repr_enum.rs"),
        },
        Case {
            name: "m72_nested_closure_wrapping_shl",
            bug_ref: "#72 nested-closure wrapping_shl",
            src: include_str!("bridge_corpus/m72_nested_closure_wrapping_shl.rs"),
        },
        Case {
            name: "m51_signed_narrow_sar",
            bug_ref: "#51 signed-narrow SAR from narrowing cast",
            src: include_str!("bridge_corpus/m51_signed_narrow_sar.rs"),
        },
        Case {
            name: "m67_overflowing_mul_by_zero",
            bug_ref: "#67 overflowing_mul by zero (TrapMismatch)",
            src: include_str!("bridge_corpus/m67_overflowing_mul_by_zero.rs"),
        },
        Case {
            name: "i128_u128_literal",
            bug_ref: "u128 literal with high bit set (ConstValue::Scalar fail-closed)",
            src: include_str!("bridge_corpus/i128_u128_literal.rs"),
        },
        Case {
            name: "i128_u128_arith",
            bug_ref: "u128 wrapping_mul (i128 call-arg register pair / real surface re-check)",
            src: include_str!("bridge_corpus/i128_u128_arith.rs"),
        },
        Case {
            name: "i128_store_roundtrip",
            bug_ref: "i128 store/load two-limb round-trip (0c6eefc, end-to-end)",
            src: include_str!("bridge_corpus/i128_store_roundtrip.rs"),
        },
        Case {
            name: "i128_neg",
            bug_ref: "i128 wrapping_neg (end-to-end; was a presumed gap, actually lowers)",
            src: include_str!("bridge_corpus/probe_i128_neg.rs"),
        },
        Case {
            name: "i128_count_ones",
            bug_ref: "i128 count_ones via per-limb popcount (was width>64 fail-closed)",
            src: include_str!("bridge_corpus/i128_count_ones.rs"),
        },
        Case {
            name: "i128_saturating",
            bug_ref: "unsigned i128 saturating_add (wrapping+Ult+select; was width>64 fail-closed)",
            src: include_str!("bridge_corpus/i128_saturating.rs"),
        },
        Case {
            name: "i128_clz_ctz",
            bug_ref: "i128 leading_zeros/trailing_zeros via per-limb clz/ctz + select",
            src: include_str!("bridge_corpus/i128_clz_ctz.rs"),
        },
        Case {
            name: "i128_swap_rev",
            bug_ref: "i128 swap_bytes/reverse_bits via per-limb op + limb-swap recombine",
            src: include_str!("bridge_corpus/i128_swap_rev.rs"),
        },
        Case {
            name: "i128_signed_sat",
            bug_ref: "signed i128 saturating_add (xor/and overflow detect + clamp select)",
            src: include_str!("bridge_corpus/i128_signed_sat.rs"),
        },
        Case {
            name: "i128_rotate",
            bug_ref: "i128 rotate_left/right via the funnel-shift fallback (n==128)",
            src: include_str!("bridge_corpus/i128_rotate.rs"),
        },
        Case {
            name: "raw_ptr_writethrough",
            bug_ref: "Rvalue::RawPtr of a scalar (cell referent + bind cell addr): *mut write-through, mutate-then-deref, aliasing",
            src: include_str!("bridge_corpus/raw_ptr_writethrough.rs"),
        },
        Case {
            name: "raw_ptr_int_roundtrip",
            bug_ref: "ptr<->int round-trip: PointerExposeProvenance/PointerWithExposedProvenance -> PtrToInt/IntToPtr",
            src: include_str!("bridge_corpus/raw_ptr_int_roundtrip.rs"),
        },
        Case {
            name: "raw_ptr_field_elem",
            bug_ref: "projected RawPtr addr_of!(s.field)/addr_of!(a[i]) (force base memory-backed, case 4d) + write-through",
            src: include_str!("bridge_corpus/raw_ptr_field_elem.rs"),
        },
        Case {
            name: "copy_nonoverlapping",
            bug_ref: "ptr::copy_nonoverlapping memcpy intrinsic, CONST scalar count -> unrolled proven load/store; correct at O0/O2/O3 (the O0 library-call CGU now lowers: the runtime-count wrapper -> memcpy and its precondition's dead ArgumentType panic blocks are trapped)",
            src: include_str!("bridge_corpus/copy_nonoverlapping.rs"),
        },
        Case {
            name: "copy_nonoverlapping_runtime",
            bug_ref: "ptr::copy_nonoverlapping with a RUNTIME count (+ count=0, i8/struct elems, copy_to_nonoverlapping): runtime/non-scalar/over-large count -> libc memcpy(dst,src,count*size); the precondition's is_aligned_to / maybe_is_nonoverlapping dead panic_fmt blocks are trapped (were failing closed on core::fmt::rt::ArgumentType because def_path_str elides the `panicking` module); O0/O2/O3",
            src: include_str!("bridge_corpus/copy_nonoverlapping_runtime.rs"),
        },
        Case {
            name: "copy_overlapping",
            bug_ref: "ptr::copy / slice::copy_within overlap in BOTH directions -> libc memmove(dst,src,count*size); adversarial dst>src distinguishes memmove from a corrupting forward loop, and runtime u16 count pins byte scaling; O0/O2/O3",
            src: include_str!("bridge_corpus/copy_overlapping.rs"),
        },
        Case {
            name: "maybe_uninit",
            bug_ref: "MaybeUninit<T> uninit()->write->assume_init (union memory layout + ZST-field-skip ABI + uninit-const no-op); correct at O0/O2/O3",
            src: include_str!("bridge_corpus/maybe_uninit.rs"),
        },
        Case {
            name: "maybe_uninit_o0",
            bug_ref: "MaybeUninit<T> at -O0 where uninit()/as_mut_ptr()/assume_init() are NON-inlined libcore calls: union construct through the ZST `uninit: ()` field (uninitialized carrier), &raw mut (*self) RawPtr through a reference PARAMETER, assert_inhabited no-op for inhabited T, by-value scalar-union ABI (return + param stored into the union slot), MaybeUninit::new(v) non-ZST active field, [MaybeUninit<i64>;N] element write/read; O0 correct (exit 7), O2/O3 inlined new()/array fail closed (sound)",
            src: include_str!("bridge_corpus/maybe_uninit_o0.rs"),
        },
        Case {
            name: "maybe_uninit_aggregate",
            bug_ref: "MaybeUninit<T> for a NON-scalar MULTI-FIELD T ((i64,i64) / (i32,i32,i32) / struct / (i8,i64) padding / [i64;3] / distinct-per-field) at -O0: the aggregate union rides the memory-aggregate by-value ABI + construct + read (active `value: ManuallyDrop<T>` field at byte offset 0); uninit()/as_mut_ptr().write()/assume_init() NON-inlined. O0 correct (exit 7, each shape a distinct observable); O2/O3 inline away and the [i64;3] scalarized-array raw-ptr deref stays fail closed (sound)",
            src: include_str!("bridge_corpus/maybe_uninit_aggregate.rs"),
        },
        Case {
            name: "cmp_ordering",
            bug_ref: "Cmp / core::cmp::Ordering (signum, Ord::cmp, max/min): Ordering->I8 lang-item type + Cmp binop (nested Select) + discriminant-of-Ordering",
            src: include_str!("bridge_corpus/cmp_ordering.rs"),
        },
        Case {
            name: "cmp_ordering_methods",
            bug_ref: "Ordering-value methods reverse/then_with/is_ge (Ordering kept off the scalarized-aggregate path; const/reconstructed Ordering is a scalar i8)",
            src: include_str!("bridge_corpus/cmp_ordering_methods.rs"),
        },
        Case {
            name: "closure_zst_upvar",
            bug_ref: "closure with a ZERO-SIZED upvar (captured fn item) types/lowers: keep ZST upvar in the tuple (preserve indices), don't require it to be a memory scalar",
            src: include_str!("bridge_corpus/closure_zst_upvar.rs"),
        },
        Case {
            name: "int_byte_transmute",
            bug_ref: "int<->[u8;N] to_le_bytes/to_be_bytes/from_le_bytes (Transmute as store/load through a memory-backed array slot); byte-order + roundtrip",
            src: include_str!("bridge_corpus/int_byte_transmute.rs"),
        },
        Case {
            name: "raw_ptr_deref_field",
            bug_ref: "&raw const/mut (*r).field / (*r)[i] (Deref-first projected RawPtr: base = reference's pointer value + field offset)",
            src: include_str!("bridge_corpus/raw_ptr_deref_field.rs"),
        },
        Case {
            name: "unsafe_cell",
            bug_ref: "UnsafeCell<T> get()+read/write (cell a transparent scalar-newtype referent; store a transparent single-field aggregate as its inner scalar)",
            src: include_str!("bridge_corpus/unsafe_cell.rs"),
        },
        Case {
            name: "cell",
            bug_ref: "Cell<T> new/get/set/replace (nested transparent Cell->UnsafeCell->u32: Field-RawPtr of celled scalar + single-scalar-newtype construct binds the inner scalar)",
            src: include_str!("bridge_corpus/cell.rs"),
        },
        Case {
            name: "nonzero_niche",
            bug_ref: "Option<NonZero<T>> niche enum + ilog (int->Option<NonZero> niche Transmute stored to the enum slot + memory-backed transmute dest; 0=None)",
            src: include_str!("bridge_corpus/nonzero_niche.rs"),
        },
        Case {
            name: "option_take_loop",
            bug_ref: "Option::take/replace + mem::replace on a loop-carried enum (whole-enum copy memory-backing propagated across both ends of D=copy S; was 'ADT Use source discriminant before aggregate binding' / 'memory aggregate whole assignment from non-memory source'); O2/O3 correct, O0 fail-closed (range-iter helper)",
            src: include_str!("bridge_corpus/option_take_loop.rs"),
        },
        Case {
            name: "union_float_pun",
            bug_ref: "union type-pun between same-width float and int fields (union_projection_cast_op: float<->int reinterpret is a Bitcast, as in to_bits/from_bits; was 'union field type U32 differs from active field type F32'); all opt levels",
            src: include_str!("bridge_corpus/union_float_pun.rs"),
        },
        Case {
            name: "struct_int_transmute",
            bug_ref: "transmute between a dense (padding-free) struct/tuple and a same-width int (store/load through the aggregate slot, generalizing int<->[u8;N]); padded aggregates fail closed; was 'Ty::Adt multi-field struct' / 'memory-backed aggregate assignment Rvalue::Cast'; all opt levels",
            src: include_str!("bridge_corpus/struct_int_transmute.rs"),
        },
        Case {
            name: "union_loop_carried",
            bug_ref: "REGRESSION GUARD: a union local mutated across a loop back-edge silently dropped its store-back (loop-carried union read stale init value; reaudit found llvm=31/tcg=1). Now FAILS CLOSED via the loop-carried-completeness verification improvement (a post-lowering back-edge faithfulness check that fails closed when a mutated loop-carried local's back-edge arg is the unchanged phi param, plus a closed-world gate + union net); this fixture pins it can never compile-and-miscompile again",
            src: include_str!("bridge_corpus/union_loop_carried.rs"),
        },
        Case {
            name: "i128_array_slot",
            bug_ref: "16-byte-aligned i128/u128 aggregate (a [u128;N]/[i128;N] array, struct of u128 fields): memory_slot_lane_ty now supports align-16 slots (I128 lanes); was 'memory slot alignment 16 unsupported'. i128 leaves access as two i64 limbs so the lane only sizes/aligns the slot; all opt levels",
            src: include_str!("bridge_corpus/i128_array_slot.rs"),
        },
        Case {
            name: "i128_overflow_addsub",
            bug_ref: "i128/u128 overflowing_add/sub + checked/saturating: composed from proven i128 primitives (wrapping add/sub + bit-exact overflow condition) since the adapter rejects Inst::Overflow on 128-bit; was '[TCG-REGALLOC-063] Inst::Overflow on I128/U128 not yet supported'; O2/O3 (O0 fail-closed range-iter helper). overflowing_mul still fails closed",
            src: include_str!("bridge_corpus/i128_overflow_addsub.rs"),
        },
        Case {
            name: "i128_eq_switch",
            bug_ref: "128-bit ==/!=/single-arm match: a single-case switchInt on an i128/u128 value is lowered as an Eq compare + CondBr (the verified Inst::Switch only supports 8/16/32/64-bit selectors); was 'unsupported switch selector width for I128/U128'. Multi-case 128-bit match still fails closed; all opt levels",
            src: include_str!("bridge_corpus/i128_eq_switch.rs"),
        },
        Case {
            name: "u128_mul_overflow",
            bug_ref: "u128 overflowing_mul/checked_mul/saturating_mul via the division identity (a!=0 && wrapped/u a != b, with a select(a==0,1,a) divisor so UDIV is div-by-zero-safe); composed from proven primitives, no 256-bit product; O2/O3",
            src: include_str!("bridge_corpus/u128_mul_overflow.rs"),
        },
        Case {
            name: "i128_mul_overflow_signed",
            bug_ref: "SIGNED i128 overflowing_mul/checked_mul via the division identity, guarding BOTH x86 IDIV traps (/0 and MIN/-1): a==0->false, a==-1->b==MIN, else wrapped/s a != b, with selects mapping {0,-1} to a safe divisor; the trap-prone MIN*-1/-1*MIN/MIN*MIN detect overflow without a trapping IDIV; O2/O3",
            src: include_str!("bridge_corpus/i128_mul_overflow_signed.rs"),
        },
        Case {
            name: "i128_byval_aggregate_abi",
            bug_ref: "16-byte-aligned i128-containing aggregate crossing a BY-VALUE ABI boundary \
                      (a `(i128, bool)` / `(i128, i128)` / `(bool, i128)` tuple return, a \
                      `struct { i128, i64 }`, an `[i128; 2]`, an `(i128, bool)` passed by value AND \
                      returned): memory-backed as `I128` slot lanes (`memory_slot_lane_ty`), each \
                      field at its rustc-layout byte offset (i128 as two i64 limbs), sret bytes \
                      relocated lane-by-lane, the backend's verified SysV classifier modeling the \
                      i128 as two INTEGER eightbytes. Was 'memory aggregate ... alignment 16 \
                      unsupported' / 'Ty::(i128, bool)'. The 16-byte-lane P1 memory-refinement is \
                      now encoded (encode_store_le/encode_load_le admit 16 bytes). O0/O2/O3",
            src: include_str!("bridge_corpus/i128_byval_aggregate_abi.rs"),
        },
        Case {
            name: "static_mut_basic",
            bug_ref: "gap E (d8aed8b): static mut write-then-read = cross-object writable data global",
            src: include_str!("bridge_corpus/static_mut_basic.rs"),
        },
        Case {
            name: "static_mut_loop_rmw",
            bug_ref: "gap E boundary: static mut read-modify-write across a loop back-edge — \
                      MATCH (O0) or fail-closed (O2/O3 back-edge gate), NEVER a dropped-store miscompile",
            src: include_str!("bridge_corpus/static_mut_loop_rmw.rs"),
        },
        Case {
            name: "static_mut_cross_fn",
            bug_ref: "gap E: static mut mutated by inline(never) helpers in separate objects (cross-object import)",
            src: include_str!("bridge_corpus/static_mut_cross_fn.rs"),
        },
        Case {
            name: "nested_aggregate_field_projection",
            bug_ref: "struct construction whose nested-aggregate field is sourced from a PROJECTION \
                      (`Outer { inner: o.inner, k: .. }`, rustc spilling `o.inner` to a whole-Inner \
                      temp): flat-leaf enumeration threads a nested-aggregate-containing struct \
                      through the by-value call-arg pack, the memory->scalarized nested-field load, \
                      the scalarized->memory nested-operand store, and the mem->mem whole-field \
                      return copy; reordered (a:i8,b:i64) + 3-level nesting so a wrong byte offset \
                      diverges; was 'Ty::Adt multi-field struct Inner' fail-closed; O0/O2/O3",
            src: include_str!("bridge_corpus/nested_aggregate_field_projection.rs"),
        },
        Case {
            name: "const_bounds_check_elim",
            bug_ref: "Constant-index bounds checks retain the original MIR condition as a runtime assertion. In-bounds execution must equal LLVM at O0/O2/O3.",
            src: include_str!("bridge_corpus/const_bounds_check_elim.rs"),
        },
        Case {
            name: "dom_bounds_check_elim",
            bug_ref: "Runtime-index accesses dominated by loop guards retain their bounds assertions. Marking loops and the last valid index must equal LLVM at O0/O2/O3.",
            src: include_str!("bridge_corpus/dom_bounds_check_elim.rs"),
        },
        Case {
            name: "dom_bounds_check_keep",
            bug_ref: "OPT-6b REFUTATIONS (in-bounds side): a WEAKER dominating fact (t < 64 over \
                      a [u8;16] — ay refutes the implication with witness t=16), an index \
                      MUTATED between guard and check (q += 1), and a DERIVED index (t2 - 1) \
                      must all KEEP their checks; runtime stays in bounds so the result must \
                      equal LLVM regardless. The OOB/trap side of the same shapes is pinned by \
                      dom_bounds_refutation_x86.rs. O0/O2/O3",
            src: include_str!("bridge_corpus/dom_bounds_check_keep.rs"),
        },
        // ---- OPT-12 x86 SSE2 integer vectorizer (element-wise map over
        // distinct local arrays). Positives must vectorize (MOVDQU+PADDD/…) and
        // still equal LLVM at O0/O2/O3; adversarials must stay scalar (or
        // fail-closed) and equal LLVM. ----
        Case {
            name: "vectorize_add_i32",
            bug_ref: "OPT-12: c[i]=a[i]+b[i] over 3 distinct local [i32;N] arrays -> \
                      packed MOVDQU+PADDD for floor(N/4) iters + scalar remainder; \
                      legality by construction (distinct StackSlots, write-only dest, \
                      unit stride, const N). O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_add_i32.rs"),
        },
        Case {
            name: "vectorize_sub_i32",
            bug_ref: "OPT-12: c[i]=a[i]-b[i] (non-commutative operand order) -> PSUBD. \
                      O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_sub_i32.rs"),
        },
        Case {
            name: "vectorize_xor_i32",
            bug_ref: "OPT-12: c[i]=a[i]^b[i] (bitwise) -> PXOR. O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_xor_i32.rs"),
        },
        Case {
            name: "vectorize_adv_same_array",
            bug_ref: "OPT-12 adversarial: dest == source array (a==b==c); distinct-slot \
                      guard rejects vectorization; stays scalar+correct. O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_adv_same_array.rs"),
        },
        Case {
            name: "vectorize_adv_loop_carried",
            bug_ref: "OPT-12 adversarial: loop-carried dep c[i]=c[i-1]+a[i]; rejected \
                      (dest also read, offset index); stays scalar. O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_adv_loop_carried.rs"),
        },
        Case {
            name: "vectorize_reduce_sum_i32",
            bug_ref: "OPT-12-REDUCE positive: integer sum-reduction s+=a[i] over a local \
                      [i32;N] with a loop-carried Gpr32 accumulator -> PADDD-accumulate \
                      loop (four i32 lane-partials in a loop-carried XMM) + a COVERED \
                      horizontal reduce (MOVDQU spill + 4 scalar loads/adds, no PHADDD/ \
                      PSHUFD) + scalar remainder; integer add is assoc+commutative so \
                      lane-partials+combine == the sequential sum, bit-for-bit. \
                      O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_adv_reduction.rs"),
        },
        Case {
            name: "vectorize_reduce_dot_i32",
            bug_ref: "OPT-12-REDUCE positive: integer dot-product d+=a[i]*b[i] over two \
                      distinct local [i32;N] -> PMULLD + PADDD-accumulate + COVERED \
                      horizontal reduce + scalar remainder; PMULLD low-dword product == \
                      scalar i32 wrapping_mul, integer add assoc+commutative. \
                      O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_reduce_dot_i32.rs"),
        },
        Case {
            name: "vectorize_regarg_sum_i64",
            bug_ref: "OPT-12 reg-arg REDUCE positive: i64 sum over a &[i64] whose (ptr,len) \
                      are REGISTERS (inline(never) g) -> recognize_regarg_sumq_loop rewrites \
                      to PADDQ-accumulate + COVERED horizontal reduce + scalar tail behind a \
                      runtime vN=len&!1 gate. Own-length identity (header bound reg == every \
                      guard bound reg), no stores (no aliasing), i64 add assoc+commutative. \
                      O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_regarg_sum_i64.rs"),
        },
        Case {
            name: "vectorize_adv_regarg_crosslen",
            bug_ref: "OPT-12 reg-arg adversarial (CRITICAL): loop trip count k != slice \
                      length; header bound reg (k) differs from the per-element guard bound \
                      reg (s.len()). The own-length identity check fails -> REFUSES to \
                      vectorize (fail-safe to scalar). Called with k==s.len() so the value is \
                      defined; stays SCALAR == LLVM O0/O2/O3",
            src: include_str!("bridge_corpus/vectorize_adv_regarg_crosslen.rs"),
        },
        Case {
            name: "vectorize_adv_regarg_store",
            bug_ref: "OPT-12 reg-arg adversarial: in-place map s[i]=s[i]*2+1 over &mut [i64]; \
                      the loop STORES, so the pure-reduction register tier (admits no stores) \
                      refuses it and no stack-slot recognizer matches a register base -> stays \
                      SCALAR + correct == LLVM O0/O2/O3",
            src: include_str!("bridge_corpus/vectorize_adv_regarg_store.rs"),
        },
        Case {
            name: "vectorize_adv_reduce_float_sum",
            bug_ref: "OPT-12-REDUCE adversarial (CRITICAL): FLOAT sum s+=f[i]. Float add is \
                      NOT associative, so lane-partials+combine != the sequential sum. \
                      Rejected (MOVSS not MOVRM32, Fpr128 not Gpr32, ADDSS not ADDRR — \
                      triple fail-safe); stays scalar. Rust has no fast-math so LLVM keeps \
                      an ordered scalar sum -> bridge==LLVM (or fails closed = safe). \
                      O0/O2/O3",
            src: include_str!("bridge_corpus/vectorize_adv_reduce_float_sum.rs"),
        },
        Case {
            name: "vectorize_adv_reduce_float_dot",
            bug_ref: "OPT-12-REDUCE adversarial: FLOAT dot d+=a[i]*b[i] over [f32;N]; non- \
                      associative -> stays scalar (float loads/acc/add rejected); == LLVM \
                      (or fails closed = safe). O0/O2/O3",
            src: include_str!("bridge_corpus/vectorize_adv_reduce_float_dot.rs"),
        },
        Case {
            name: "vectorize_adv_reduce_prefix",
            bug_ref: "OPT-12-REDUCE adversarial: prefix-sum c[i]=s after s+=a[i] — the \
                      running accumulator ESCAPES to memory each iteration, so reordering \
                      the adds would change the stored intermediates. Rejected (a reduction \
                      writes ZERO memory in-loop); stays scalar. O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_adv_reduce_prefix.rs"),
        },
        Case {
            name: "vectorize_adv_reduce_nonassoc",
            bug_ref: "OPT-12-REDUCE adversarial: non-associative reduce s=s.rotate_left(1)^ \
                      a[i]; the combine is not a plain wrapping AddRR, so it is rejected \
                      (only integer add is proven assoc/commutative); stays scalar. \
                      O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_adv_reduce_nonassoc.rs"),
        },
        Case {
            name: "vectorize_adv_stride2",
            bug_ref: "OPT-12 adversarial: non-unit stride i+=2; unit-stride guard \
                      rejects; odd c[] stays init in both backends. O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_adv_stride2.rs"),
        },
        Case {
            name: "vectorize_adv_offset",
            bug_ref: "OPT-12 adversarial: offset source c[i]=a[i+1]+b[i]; index!=iv guard \
                      rejects; stays scalar. O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_adv_offset.rs"),
        },
        // ---- OPT-12-FILL: constant fill a[i]=K over ONE distinct write-only
        // local array. The positive must vectorize to MOVDQU stores (a scratch
        // [K;4] built with covered i32 stores + MOVDQU load, no broadcast) and
        // equal LLVM; adversarials must stay scalar (or fail-closed). ----
        Case {
            name: "vectorize_fill_i32",
            bug_ref: "OPT-12-FILL: a[i]=K over one distinct write-only [i32;N] local -> \
                      build [K;4] once (4 covered i32 stores + MOVDQU load) then MOVDQU \
                      stores for floor(N/4) iters + scalar remainder; legality by \
                      construction (single distinct StackSlot, write-only=no dependence, \
                      unit stride, const N). O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_fill_i32.rs"),
        },
        Case {
            name: "vectorize_adv_fill_variable",
            bug_ref: "OPT-12-FILL adversarial: runtime (non-const) fill value; no covered \
                      broadcast; recognizer rejects; stays scalar. O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_adv_fill_variable.rs"),
        },
        Case {
            name: "vectorize_adv_fill_iota",
            bug_ref: "OPT-12-FILL adversarial: per-iteration-varying value a[i]=i (traces \
                      to the IV, not a constant); rejected; stays scalar. O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_adv_fill_iota.rs"),
        },
        Case {
            name: "vectorize_adv_fill_struct_field",
            bug_ref: "OPT-12-FILL adversarial: array field at non-zero struct offset \
                      (base is StackSlot+4, not a bare SlotBase); rejected; stays scalar. \
                      O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_adv_fill_struct_field.rs"),
        },
        Case {
            name: "vectorize_adv_fill_pointer",
            bug_ref: "OPT-12-FILL adversarial: fill through a &mut [i32;N] reference param \
                      (pointer base, not a distinct local StackSlot); aliasing not ruled \
                      out; rejected; stays scalar. O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_adv_fill_pointer.rs"),
        },
        // ---- OPT-12-SAXPY: element-wise FMA dest[i]=(k*x[i])(+|-)y[i] over i32
        // arrays, k loop-invariant. The DEST slot may equal a source slot but
        // only at the SAME index i (dest==source relaxation, provably same-index-
        // only by the ElemAddr(index==iv) guard). Positives vectorize to
        // [k;4]-broadcast + PMULLD + PADDD/PSUBD + MOVDQU and equal LLVM;
        // adversarials (cross-element dep, offset, non-invariant k, aliasing,
        // reduction) must stay scalar (or fail-closed). ----
        Case {
            name: "vectorize_saxpy_i32",
            bug_ref: "OPT-12-SAXPY: a[i]=a[i]*k+b[i] (dest==mul source, same index), k \
                      loop-invariant runtime scalar -> broadcast [k;4] once + PMULLD + \
                      PADDD + MOVDQU for floor(N/4) iters + scalar remainder; PMULLD low- \
                      dword product == scalar i32 wrapping_mul; dest==source legal by the \
                      same-index (ElemAddr@iv) construction. O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_saxpy_i32.rs"),
        },
        Case {
            name: "vectorize_saxpy_dest_add",
            bug_ref: "OPT-12-SAXPY commuted: y[i]=k*x[i]+y[i] (dest==the ADDED source, same \
                      index); distinct multiplied source x. Vectorizes; same-index dest== \
                      source. O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_saxpy_dest_add.rs"),
        },
        Case {
            name: "vectorize_adv_saxpy_carried",
            bug_ref: "OPT-12-SAXPY adversarial (CRITICAL): c[i]=a[i]*k+c[i-1] reads the DEST \
                      array at index i-1 (cross-element recurrence). The c[i-1] address has \
                      index provenance iv-1 (Unknown), not ElemAddr@iv, so classification \
                      fails and the recognizer bails -> proves dest==source is same-index- \
                      ONLY. Stays scalar. O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_adv_saxpy_carried.rs"),
        },
        Case {
            name: "vectorize_adv_saxpy_offset",
            bug_ref: "OPT-12-SAXPY adversarial: c[i]=a[i]*k+b[i+1] reads the added source at \
                      a different index (non-zero disp / iv+1 provenance); not ElemAddr@iv; \
                      rejected; stays scalar. O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_adv_saxpy_offset.rs"),
        },
        Case {
            name: "vectorize_adv_saxpy_variant",
            bug_ref: "OPT-12-SAXPY adversarial: multiplier alpha recomputed per iteration \
                      (IV-dependent, def inside the loop body); fails the loop-invariance \
                      check (single-def + def-outside-body + dominates-preheader); a wrong \
                      decision would broadcast a stale alpha; rejected; stays scalar. \
                      O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_adv_saxpy_variant.rs"),
        },
        Case {
            name: "vectorize_adv_saxpy_aliased",
            bug_ref: "OPT-12-SAXPY adversarial: c[i]=a[i]*k+a[i+2] — the same slot supplies \
                      both sources at DIFFERENT indices; the a[i+2] access is not \
                      ElemAddr@iv so it fails classification; rejected; stays scalar. \
                      O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_adv_saxpy_aliased.rs"),
        },
        Case {
            name: "vectorize_adv_saxpy_reduction",
            bug_ref: "OPT-12-SAXPY adversarial: s += a[i]*k horizontal reduction; no \
                      element-wise ElemAddr@iv store (accumulator is loop-carried); \
                      recognizer bails; stays scalar. O0/O2/O3 == LLVM",
            src: include_str!("bridge_corpus/vectorize_adv_saxpy_reduction.rs"),
        },
        // NOTE: an end-to-end i128 memory-roundtrip fixture
        // (bridge_corpus/i128_store_high_limb.rs) is intentionally NOT wired in
        // yet: it currently fails closed on SIBLING i128 gaps (128-bit literals,
        // the u128-multiply libcall's by-value i128 args) before the i128
        // store/load is even reached, so it cannot yet exercise the fix
        // end-to-end. The store/load two-limb lowering itself is validated by
        // the `select_i128_store_emits_two_movmr_lo_then_hi` /
        // `select_i128_load_emits_two_movrm_and_defines_pair` unit tests in
        // trust-cg-lower. Re-wire this fixture once the i128 libcall-arg + wide
        // const cluster lands.
        Case {
            name: "fuzz2_rev_enumerate_order",
            bug_ref: "FUZZ-2: `.rev().enumerate().map(g).sum()` at O2/O3 (specialized to \
                      `rfold(enumerate(map_fold(sum)))`): the rfold commutative-reduction \
                      fast path drove the FORWARD chain, but the peeled ORDER-SENSITIVE \
                      Enumerate paired index 0 with the FIRST (not LAST) element -> silent \
                      55 instead of 35. Now rejects a peeled enumerate/count adapter and \
                      fails closed at O2/O3; O0 drives the whole chain correctly (== 35)",
            src: include_str!("bridge_corpus/fuzz2_rev_enumerate_order.rs"),
        },
        Case {
            name: "fuzz2_scan_reduction",
            bug_ref: "FUZZ-2: `.scan(st, f).sum()` — `Scan` is unmodeled, so the general \
                      `Sum::sum::<Scan<..>>` reached the TRAPPED `<Scan as Iterator>::\
                      try_fold` ud2 stub at runtime -> SIGILL. Now the sum/fold/count \
                      terminal fails closed at compile time on an unmodeled chain (and \
                      scan bodies are excluded from the dead-iterator trap)",
            src: include_str!("bridge_corpus/fuzz2_scan_reduction.rs"),
        },
        Case {
            name: "fuzz2_filter_map_take_reduction",
            bug_ref: "FUZZ-2: `.filter_map(..).take(n).sum()` — Take WRAPPING an unmodeled \
                      FilterMap reached the TRAPPED `<Take<..> as Iterator>::try_fold` ud2 \
                      stub at runtime -> SIGILL. Now the reduction terminal fails closed \
                      at compile time on any unmodeled chain",
            src: include_str!("bridge_corpus/fuzz2_filter_map_take_reduction.rs"),
        },
        // -------------------------------------------------------------------
        // FUZZ-3 memory-model / heap differential sweep (Box / Rc / Cell /
        // RefCell / unions / transmute / raw pointers / MaybeUninit / statics /
        // signed-narrow loads / small-struct-by-value ABI). The sweep found
        // ZERO live miscompiles at HEAD; these are the compile-THROUGH shapes
        // (Agree at O0/O2/O3) that most directly exercise the memory surface —
        // pinned as regression tripwires so a future lowering/opt change that
        // silently corrupts one is caught by the differential.
        // -------------------------------------------------------------------
        Case {
            name: "fuzz3_struct_ptr_field_byval",
            bug_ref: "FUZZ-3: a by-value #[derive(Copy)] struct of four u8 passed into a fn, \
                      read back through `&s as *const S as *const u8` + `.add(i)` byte walk \
                      (the historical 1-byte-stride struct-ptr-field-by-value SIGSEGV class); \
                      Agree O0/O2/O3",
            src: include_str!("bridge_corpus/fuzz3_struct_ptr_field_byval.rs"),
        },
        Case {
            name: "fuzz3_ptr_width_pun",
            bug_ref: "FUZZ-3: two u32 stores through `(*mut u64 as *mut u32)` + `.add(1)` into \
                      one u64 stack slot, read back as the whole u64 (store-to-load forwarding \
                      across narrower type-punned writes); Agree O0/O2/O3",
            src: include_str!("bridge_corpus/fuzz3_ptr_width_pun.rs"),
        },
        Case {
            name: "fuzz3_store_u64_load_u32",
            bug_ref: "FUZZ-3: store a u64 through *mut u64, immediately load the low and high \
                      halves through `*const u32` / `.add(1)` (sub-slot partial-overlap load \
                      forwarding); Agree O0/O2/O3",
            src: include_str!("bridge_corpus/fuzz3_store_u64_load_u32.rs"),
        },
        Case {
            name: "fuzz3_union_write_field",
            bug_ref: "FUZZ-3: `union U { v: u64, halves: [u32;2] }` — write both [u32;2] lanes \
                      then read the combined u64 field (union field write + differently-typed \
                      whole read); Agree O0/O2/O3",
            src: include_str!("bridge_corpus/fuzz3_union_write_field.rs"),
        },
        Case {
            name: "fuzz3_signed_mixed_struct",
            bug_ref: "FUZZ-3: #[repr(C)] struct { i8, i16, i32, i64 } with NEGATIVE values — \
                      each narrow field load must sign-extend (movsx not movzx) before widening \
                      to i64; a movzx would diverge; Agree O0/O2/O3",
            src: include_str!("bridge_corpus/fuzz3_signed_mixed_struct.rs"),
        },
        Case {
            name: "fuzz3_signed_packed",
            bug_ref: "FUZZ-3: #[repr(packed)] struct { i8, i32, i16 } with negative values — \
                      MISALIGNED signed narrow loads sign-extend correctly; Agree O0/O2/O3",
            src: include_str!("bridge_corpus/fuzz3_signed_packed.rs"),
        },
        Case {
            name: "fuzz3_nan_through_union",
            bug_ref: "FUZZ-3: qNaN bit pattern 0x7FF8.. reinterpreted u64->f64 through a union, \
                      `is_nan()` branch + `to_bits()` round-trip (bit-exact float pun, no \
                      NaN-canonicalization); Agree O0/O2/O3",
            src: include_str!("bridge_corpus/fuzz3_nan_through_union.rs"),
        },
        Case {
            name: "fuzz3_transmute_struct_ints",
            bug_ref: "FUZZ-3: mem::transmute of a dense #[repr(C)] struct { u32, u32 } to a u64 \
                      then field-wise recovery (aggregate-slot store/load transmute); \
                      Agree O0/O2/O3",
            src: include_str!("bridge_corpus/fuzz3_transmute_struct_ints.rs"),
        },
        Case {
            name: "fuzz3_abi_struct_mixed_ret",
            bug_ref: "FUZZ-3: #[inline(never)] fn returning a by-value #[repr(C)] struct \
                      { u8, u16, u32 } (mixed-width single-eightbyte INTEGER-class ABI return), \
                      fields recombined in the caller; Agree O0/O2/O3",
            src: include_str!("bridge_corpus/fuzz3_abi_struct_mixed_ret.rs"),
        },
        Case {
            name: "fuzz3_abi_struct_pad",
            bug_ref: "FUZZ-3: #[inline(never)] fn returning a by-value #[repr(C)] struct \
                      { u8, u64 } with internal padding (two-eightbyte INTEGER ABI return); \
                      Agree O0/O2/O3",
            src: include_str!("bridge_corpus/fuzz3_abi_struct_pad.rs"),
        },
        Case {
            name: "fuzz3_static_mut_array",
            bug_ref: "FUZZ-3: `static mut BUF: [u32;8]` written then summed in a loop \
                      (cross-object mutable global array store/load through the data symbol); \
                      Agree O0/O2/O3",
            src: include_str!("bridge_corpus/fuzz3_static_mut_array.rs"),
        },
        Case {
            name: "fuzz3_reprc_nested",
            bug_ref: "FUZZ-3: nested #[repr(C)] { Inner{u16,u16}, u32, Inner{u16,u16} } — read \
                      the middle u32 through `(&o as *const _ as *const u8).add(4) as *const u32` \
                      (layout-offset raw read of a nested aggregate); Agree O0/O2/O3",
            src: include_str!("bridge_corpus/fuzz3_reprc_nested.rs"),
        },
        Case {
            name: "fuzz3_alias_store_load",
            bug_ref: "FUZZ-3: two `*mut u64` raw pointers to the SAME local, store through one + \
                      load through the other (must not assume no-alias / must not drop the \
                      forwarded store); Agree O0/O2/O3",
            src: include_str!("bridge_corpus/fuzz3_alias_store_load.rs"),
        },
        Case {
            name: "fuzz4_float_nan_cast_const",
            bug_ref: "FUZZ-4: float/NaN/saturating-cast/const sweep in one oracle — all 6 \
                      comparison predicates with NaN in BOTH operand positions (x86 ucomisd \
                      parity edge: ordered ==/</<= AND-NOT-parity, unordered != OR-parity), \
                      saturating float->int `as` casts (huge->MAX, neg->MIN/0, NaN->0, at \
                      i8/u8/i32/u32 CVTTSD2SI+CMOV-clamp widths), a const-fn-built array indexed \
                      at a runtime index, and -0.0 sign propagation; Agree O0/O2/O3 -> 178",
            src: include_str!("bridge_corpus/fuzz4_float_nan_cast_const.rs"),
        },
        Case {
            name: "float_to_int_unchecked",
            bug_ref: "float_to_int_unchecked lowers to the saturating FPToSISat/FPToUISat, \
                      which equal it on its defined domain; f32/f64 to narrow/wide \
                      signed/unsigned integers, with fractional truncation; UB inputs \
                      intentionally absent",
            src: include_str!("bridge_corpus/float_to_int_unchecked.rs"),
        },
        Case {
            name: "ffi_extern_c_foreign_call",
            bug_ref: "FUZZ-5: call to a FOREIGN `extern \"C\" { fn abs/labs }` item — a \
                      body-less foreign fn is `is_local()`, so the direct-call interception \
                      probes called `tcx.instance_mir` on it and ICE'd (typeck of a body-less \
                      body); guarded with `is_foreign_item` so foreign calls route to generic \
                      external-symbol emission; Agree O0/O2/O3 -> 14",
            src: include_str!("bridge_corpus/ffi_extern_c_foreign_call.rs"),
        },
        Case {
            name: "ffi_c_abi_sse_aggregate",
            bug_ref: "FUZZ-5: `extern \"C\"` by-value aggregate `{ i64, f64 }` with a SysV SSE \
                      eightbyte — the bridge's uniform-integer-lane aggregate ABI passed it in a \
                      GPR instead of the required XMM register (a silent wrong value at a real \
                      C/FFI boundary, found by the clang-oracle differential); the PROPER FIX \
                      threads class-correct per-eightbyte SSE/INTEGER lane types so the SSE \
                      eightbyte routes to XMM — this now COMPILES and MATCHES LLVM (clang-oracle \
                      conformance is validated in the pinned m136_x86_c_abi_sse_aggregate test)",
            src: include_str!("bridge_corpus/ffi_c_abi_sse_aggregate.rs"),
        },
        Case {
            name: "atomics_slice1_x86",
            bug_ref: "ATOMICS slice 1: x86 atomic load/store/RMW frontend hookup over the \
                      already-proven trust-ir AtomicLoad/AtomicStore/AtomicRMW ops (ZERO new \
                      proofs). AtomicUsize/U8/I8/U16/I16/U32/I32/U64/I64 load @ \
                      Relaxed/Acquire/SeqCst (MOV r,[m]), store @ Relaxed/Release (MOV [m],r), \
                      fetch_add/sub/and/or/xor @ all orderings (LOCK-CMPXCHG retry loop, returns \
                      OLD value) incl an Arc-refcount inc/dec loop; ==LLVM O0/O2/O3. SeqCst \
                      store / swap / compare_exchange / fence / AtomicPtr / u128 stay fail-closed \
                      (slices 2-4); narrow (I8/I16) RMW is O0-only (backend CAS-loop regalloc), \
                      AtomicBool is O2/O3-only (constructor bool->u8 transmute) — neither in this \
                      all-opt-level fixture.",
            src: include_str!("bridge_corpus/atomics_slice1_x86.rs"),
        },
        Case {
            name: "atomics_slice2_x86",
            bug_ref: "ATOMICS slice 2: swap + SOUND SeqCst store + NARROW-width RMW at O2/O3. \
                      swap()/atomic_xchg routes through the CAS-loop pseudo (bare XCHG fast \
                      path DELETED — no proof), cert-covered by AtomicRmwCasLoop_Xchg_I{8,16,\
                      32,64} (old-value + new-memory=operand); returns OLD value. SeqCst .store() \
                      is now SOUND (was a ud2 trap): lowered as an atomic XCHG-and-discard (the \
                      standard C++-on-x86 SeqCst-store mapping — a locked exchange writing the \
                      value AND a full barrier), the store effect proven by the Xchg 'updates \
                      memory' obligation. NARROW (I8/I16) fetch_*/swap now work at O2/O3: the \
                      AtomicRmwCasLoop8/16 fixed-RAX clobber is now DECLARED to regalloc (the \
                      byte/word alias AL/AX maps to its parent RAX for the implicit-def), so the \
                      allocator never places source/base into RAX and the encoder conflict never \
                      fires. ==LLVM O0/O2/O3. compare_exchange/fence/AtomicPtr/u128 stay \
                      fail-closed (slices 3-4).",
            src: include_str!("bridge_corpus/atomics_slice2_x86.rs"),
        },
        Case {
            name: "atomics_fence_x86",
            bug_ref: "ATOMICS slice 3: FENCES. fence()/compiler_fence() at every ordering, \
                      interleaved with real atomic loads/stores/RMWs. On x86 TSO the isel \
                      lowers fence(Relaxed/Acquire/Release/AcqRel) to ZERO instructions (TSO \
                      already forbids the reorderings they forbid; matches LLVM's empty \
                      codegen) — sound because Inst::Fence is HAS_SIDE_EFFECTS so no pre-isel \
                      pass moves a memory op across it, and there is no post-isel memory \
                      reordering. fence(SeqCst) -> a single MFENCE bound to a GENUINE \
                      single-thread identity proof (MFENCE writes no register / no memory; \
                      cross-thread ordering is an Intel-SDM architectural axiom, not an SMT \
                      theorem — replaces the retracted #62 const==const tautology). Unblocks \
                      Arc::drop's fence(Acquire). ==LLVM O0/O2/O3. compare_exchange / AtomicPtr \
                      / u128 / unknown ordering stay fail-closed (slice 4).",
            src: include_str!("bridge_corpus/atomics_fence_x86.rs"),
        },
        Case {
            name: "atomics_cxchg_x86",
            bug_ref: "ATOMICS slice 4: COMPARE-EXCHANGE. AtomicT::compare_exchange / \
                      compare_exchange_weak at i32/u32/i64/usize -> atomic_cxchg{,weak}:: \
                      <T,ORD_SUCC,ORD_FAIL> -> Inst::CmpXchg -> LOCK CMPXCHG (F0 0F B1). The \
                      instruction returns the old value in RAX; the success bool is re-derived \
                      as Icmp Equal(old, expected) (exactly the ZF CMPXCHG sets). Bound to the \
                      GENUINE conditional-data-flow proofs Cmpxchg_I{32,64} (returns-old + \
                      conditional-store + success-flag) over symbolic (mem, expected, desired) \
                      state — NOT a #62 X==X (the unconditional-store / returns-desired / \
                      backwards-flag negative controls REFUTE). Exercises SUCCESS (memory \
                      becomes new, returns Ok(old==expected)) AND FAILURE (memory UNCHANGED, \
                      returns Err(actual current)) with value oracles on the old value, \
                      is_ok()/is_err(), and the read-back memory, plus the canonical CAS retry \
                      loop. compare_exchange_weak never spuriously fails on x86 CMPXCHG so it is \
                      lowered identically to strong (sound refinement). ==LLVM O0/O2/O3. Narrow \
                      i8/i16/AtomicBool cxchg, AtomicPtr, u128, invalid/unknown orderings stay \
                      fail-closed (only i32/i64 CMPXCHG is proven).",
            src: include_str!("bridge_corpus/atomics_cxchg_x86.rs"),
        },
        Case {
            name: "array_repeat_fill",
            bug_ref: "PERF-SIEVE: large `[v; N]` array-repeat (N >= 16, fixed-width int \
                      element) lowered as ONE call to the verified __trustcg_array_fill_iN \
                      helper loop instead of N unrolled stores (p7_sieve's [0u8;1024] \
                      unrolled to 1024 stores + a 16KB frame of hoisted address pairs), \
                      with the byte variant vectorized by the runtime byte-fill \
                      x86_vectorize slice (guarded MOVDQU loop, scalar tail). Pins the \
                      threshold boundary (15 vs 16/17), packed-lane tails (100/1024), a \
                      per-entry-VARYING runtime fill value (stale-broadcast oracle), \
                      fill-then-overwrite ordering, first/last/middle reads, and \
                      u16/i32/u64 sign bits through the I64 helper lane. ==LLVM O0/O2/O3.",
            src: include_str!("bridge_corpus/array_repeat_fill.rs"),
        },
        Case {
            name: "fix_thin_raw_ptr_metadata",
            bug_ref: "THIN-pointer metadata is the ZST `()`: `PtrMetadata(*const T)` for \
                      `T: Sized` produces no bits and `from_raw_parts_mut(data, ())` IS the \
                      data pointer. Both were `library/core` roots at O0 (\"pointer metadata \
                      unsupported operand type *const ()\" / \"AggregateKind::RawPtr\"): the \
                      first died in the slice-LENGTH resolver, the second in the generic \
                      RawPtr refusal. The FAT case (a real `meta` length) keeps its \
                      `{data,len}` slot path and is untouched. Prints 7 + 9 == 16, so a \
                      rebuilt pointer aimed at the wrong object cannot read as a pass",
            src: include_str!("bridge_corpus/fix_thin_raw_ptr_metadata.rs"),
        },
        Case {
            name: "fix_refret_cell_nonprimitive",
            bug_ref: "reference-RETURNING callee over a NON-PRIMITIVE scalar referent: \
                      without a real address the `&mut` reaches the callee as a materialized \
                      temp, so the `&mut` it returns addresses a DEAD temp and `*r = ..` is \
                      dropped. `direct_scalar_ref_select_return` refused it by name (6 + 2 \
                      `library/core` roots); the cure is the ADDRESS — the reference-escaping \
                      arm of `compute_scalar_cell_locals` now cells every referent the memory \
                      model can represent, not only Int/Uint/Float/Bool/Char. A guard-only \
                      'fix' compiles this and prints the STALE 7 instead of 99. CONTROL: \
                      bridge_corpus/fix_ctl_refret_vec_intercepted.rs must still fail closed",
            src: include_str!("bridge_corpus/fix_refret_cell_nonprimitive.rs"),
        },
        Case {
            name: "fix_o_identity_nonlocal_callee",
            bug_ref: "the same dead-temp hazard through a NON-LOCAL callee \
                      (`core::convert::identity::<&mut Cur>`), which \
                      `direct_scalar_ref_select_return` never inspects: with the \
                      pre-widening primitive-only narrowing of \
                      `cellable_reference_referent_ty` restored, O0 COMPILES and prints \
                      the stale `seen=5`, exit 1 (measured) — no refusal exists to catch \
                      it, unlike the LOCAL-callee twin fix_refret_cell_nonprimitive",
            src: include_str!("bridge_corpus/fix_o_identity_nonlocal_callee.rs"),
        },
        Case {
            name: "fix_o_nonnull_as_mut_scalarized_temp",
            bug_ref: "the `IterMut::next` shape: a SCALARIZED `NonNull<u64>` temp borrowed \
                      into a local `&mut NonNull<u64> -> &mut u64` callee that returns the \
                      address the NonNull HOLDS; the referent is celled by the widened \
                      reference-escaping arm. a=42 b=100 s=142",
            src: include_str!("bridge_corpus/fix_o_nonnull_as_mut_scalarized_temp.rs"),
        },
        Case {
            name: "fix_o_wrapping_and_rawptr_referents",
            bug_ref: "`Wrapping<u32>` and `*mut u64` referents through local \
                      `&mut`-returning callees; a new pointer stored through the returned \
                      `&mut *mut u64` must re-aim `p` (a lost store would print a=41 b=2). \
                      w=42 a=1 b=42",
            src: include_str!("bridge_corpus/fix_o_wrapping_and_rawptr_referents.rs"),
        },
        Case {
            name: "fix_o_box_referent_probe",
            bug_ref: "PROBE: a `Box<u32>` referent through a local `&mut Box<u32>`-returning \
                      callee; refused by name today ([TCG-SCALAR-CELL-LAYOUT]), and if it \
                      ever compiles it must print seen=9",
            src: include_str!("bridge_corpus/fix_o_box_referent_probe.rs"),
        },
        Case {
            name: "fix_o_ref_of_ref_referent_probe",
            bug_ref: "PROBE: a `&u32` referent (whose own referent is a scalarized local) \
                      through a local `&mut &u32`-returning callee — the partial-chain-cell \
                      miscompile shape; refused by name today, and if it ever compiles it \
                      must print seen=9, never the stale 5",
            src: include_str!("bridge_corpus/fix_o_ref_of_ref_referent_probe.rs"),
        },
        Case {
            name: "fix_u128_leading_ones_pow2",
            bug_ref: "`u128` leading_ones / trailing_ones / is_power_of_two — the three \
                      bit-manipulation ops with no two-limb decomposition, and the reason \
                      `<u128>::checked_pow` / `overflowing_pow` were `library/core` roots \
                      (\"bitmanip op with width > 64 unsupported\"; checked_pow's \
                      change-of-base fast path opens with `base.is_power_of_two()`). Same \
                      limb arithmetic as the eight ops already decomposed. A wrong identity \
                      returns a plausible small integer, so ten seeds (incl. the 2^64 \
                      boundary, the top bit, all-ones and zero) fold into one checksum",
            src: include_str!("bridge_corpus/fix_u128_leading_ones_pow2.rs"),
        },
        Case {
            name: "pointee_lanes_tuple_nested",
            bug_ref: "[TCG-POINTEE-LANES] tuple pointee with a NESTED struct / array field \
                      (`&(Range, i16)`, `&(u16, [u16; 3])` — core's `unicode_data::conversions` \
                      table elements; 10 `library/core` roots: `get_unchecked`, \
                      `binary_search_by` closures, `lookup`). The flat scalar-field lane \
                      fails on the aggregate field; the byte-offset lane now types the \
                      pointee from rustc's layout (`memory_aggregate_reference_pointee_lane_ty` \
                      tuple arm) and every `(*r).N` walks real offsets. A wrong field offset \
                      or element stride changes the folded checksum",
            src: include_str!("bridge_corpus/pointee_lanes_tuple_nested.rs"),
        },
        Case {
            name: "pair_arg_lanes",
            bug_ref: "[TCG-ARG-ABI] by-value `PassMode::Pair` ARGUMENTS (74 `library/core` \
                      roots): `Option<u8>` through a closure body's `?`, `Option<u32>`, \
                      `Range<u16>`, `(i16, i16)` after three scalars, a `{u32, u16}` \
                      mixed-width struct, two pairs in one list and a pair through a \
                      trait-object method. The declaration, the callee entry block and every \
                      call site ask one `scalar_pair_param_plan`; the two lanes move through \
                      the argument's slot at rustc's own offsets. A wrong lane offset, a \
                      swapped lane or a dirty tag byte changes the folded checksum",
            src: include_str!("bridge_corpus/pair_arg_lanes.rs"),
        },
        Case {
            name: "union_fat_leaf",
            bug_ref: "union with a FAT-POINTER leaf (`MaybeUninit<Part>`, `Part::Copy(&[u8])` — \
                      core's `flt2dec` formatting buffer; 21 `library/core` roots): the union \
                      slot layout carries the leaf flags instead of refusing, a whole union \
                      element is stored through `&mut [MaybeUninit<Part>]` and into a local \
                      array by a lane copy of the source slot, and `MaybeUninit::new` / \
                      `assume_init` round-trip the 24-byte value. A torn `{data, len}`, a \
                      wrong element stride or a lost tag changes the folded checksum",
            src: include_str!("bridge_corpus/union_fat_leaf.rs"),
        },
        Case {
            name: "small_classes_batch2",
            bug_ref: "four small `library/core` refusal classes: `array::from_fn`'s \
                      `try_from_fn::<NeverShortCircuit<T>, N, _>` (a `from_residual` over an \
                      UNINHABITED residual, lowered as the unreachable rustc leaves there), \
                      `AtomicPtr<T>::{store, load}` (an atomic over a pointer element), a \
                      `const_eval_select` runtime arm taking a `&[u8]` argument PROJECTED out \
                      of the tupled-args place, and a whole `Use` copy out of an address-taken \
                      struct (leaves loaded from its slot at rustc's layout offsets). A wrong \
                      leaf offset, a torn slice pair or a lost atomic store changes the \
                      folded checksum",
            src: include_str!("bridge_corpus/small_classes_batch2.rs"),
        },
        Case {
            name: "closure_slice_arg",
            bug_ref: "P0 (measured 2026-09-22): a closure whose parameter is a `&[u8]` / `&str` \
                      fat pointer, called through `Fn::call` at O0 — the call site pushed ONE \
                      8-byte value (the data-only `Ptr`) against the closure body's 16-byte \
                      `{ data, len }` slot declaration, so the body read the pair out of the \
                      slice's own bytes and SIGSEGV'd; the element is now passed as the \
                      address of its pair inside the tupled-args slot, as a direct call does",
            src: include_str!("bridge_corpus/closure_slice_arg.rs"),
        },
        Case {
            name: "pointee_lanes_simd_overaligned",
            bug_ref: "[TCG-POINTEE-LANES] over-aligned (32/64-byte) `#[repr(simd)]` / \
                      `#[repr(C, align(N))]` struct pointee (core_arch `as_array`, 8 \
                      `library/core` roots): `&Self` / `*const Self` typed as a 16-byte-lane \
                      shell for the address-preserving cast to `&[T; N]`. Agrees with LLVM at \
                      O2/O3; at O0 the fixture's `main` stops on a pre-existing `&*p` reborrow \
                      shape (a refusal, reported as a note)",
            src: include_str!("bridge_corpus/pointee_lanes_simd_overaligned.rs"),
        },
        Case {
            name: "m143_nonnull_slice_boundary",
            bug_ref: "[TCG-ARG-ABI]/[TCG-RET-ABI] x47: the transparent wide-slice newtype \
                      (`NonNull<[T]>` / `NonNull<str>`) by value in a signature takes the \
                      `&[T]` two-lane slot; at O0 this instantiates `NonNull::<[u8]>::{as_ptr, \
                      cast, from_ref, from_mut}`, `NonNull::<str>::as_ptr`, `slice::Iter::<u8>::new` \
                      and `IterMut::<u8>::new` as roots. A lost length lane, a data lane \
                      read as a slot address or a wrong register pairing changes the sum",
            src: include_str!("bridge_corpus/m143_nonnull_slice_boundary.rs"),
        },
        Case {
            name: "nonnull_holder_field",
            bug_ref: "review 2026-09-22 (predicted torn lane, measured whole): a struct \
                      carrying a `NonNull<[u8]>` field built from a slotted parameter, read \
                      back two-lane through `&Holder` and through a by-value field copy into \
                      the return slot, stack poisoned before each call",
            src: include_str!("bridge_corpus/nonnull_holder_field.rs"),
        },
        Case {
            name: "pair_arg_exhaustion",
            bug_ref: "cross-backend ABI (measured 2026-09-23): a `PassMode::Pair` argument \
                      with exactly one integer register left — the bridge placed a 16-byte \
                      two-INTEGER pair (slices, `&str`, `NonNull<[u8]>`, `(u64, u64)`, \
                      `Range<usize>`, `Option<u64>`) as one all-or-nothing aggregate where \
                      rustc places two independent scalars (R9 + stack). Every `Pair` now \
                      rides the two-value lane on x86-64; this whole-program fixture pins \
                      the bridge's own consistency across the shapes it now owns, plus \
                      closure bodies, which keep the whole slot by structure",
            src: include_str!("bridge_corpus/pair_arg_exhaustion.rs"),
        },
        Case {
            name: "fix_return_celled_local",
            bug_ref: "a CELLED return local. `&res` on the tail-returned local (NRVO makes \
                      `res` BE `_0`) cells `_0` via the widened reference-escaping arm of \
                      `compute_scalar_cell_locals`, so every whole-local write to `_0` \
                      STORES into the cell instead of binding an SSA scalar — and \
                      `TerminatorKind::Return` then asked `value_for_scalar_binding` for \
                      `_0`, found nothing, and FABRICATED the never-defined synthetic \
                      `ValueId(0)`: \"[TCG-SSA-071] value ValueId(0) used in bbN is never \
                      defined\". That was `core::io::error::repr::Repr::new_custom`, the one \
                      genuine capability LOSS of the reference-return cell widening. \
                      CAPABILITY, not soundness: the definition was in the cell and the \
                      return was not looking there, so the return LOADS it. Prints one \
                      checksum folding the tag (survived the cell round trip), an \
                      identity check against the original address (a garbage cell load \
                      moves it) and the payload read through the recovered pointer",
            src: include_str!("bridge_corpus/fix_return_celled_local.rs"),
        },
        Case {
            name: "fix_q_control_flow_from_residual",
            bug_ref: "`?` on a `ControlFlow` — the THIRD std `Try` type. `from_residual` \
                      modeled only Result/Option, so every `ControlFlow` accumulator failed \
                      closed (3 `library/core` roots, all `Iterator::try_fold`/`try_rfold` \
                      monomorphizations). `ControlFlow`'s `FromResidual` is the IDENTITY \
                      (`Break(b) => Break(b)`, no `From` anywhere), so the lowering is write \
                      the `Break` tag + copy the `Break` payload. Covers a SCALAR payload \
                      (memory slot), a ZST payload (tag-only enum) and an AGGREGATE payload \
                      (multi-leaf copy), each with its CONTINUE path — a fix that wrote \
                      `Break` unconditionally still prints plausible break values and is \
                      caught only by the continue rows",
            src: include_str!("bridge_corpus/fix_q_control_flow_from_residual.rs"),
        },
        Case {
            name: "fix_q_agg_field_through_deref",
            bug_ref: "a by-value AGGREGATE read straight out of `&self` — `_0 = copy \
                      ((*_1).0: [u8; 4])`, i.e. `fn f(&self) -> [T; N] { self.field }`. The \
                      projected-source arm admitted only a MEMORY-BACKED base, never a \
                      `Deref`-leading chain through a thin reference, so the whole accessor \
                      family stopped there (`Ipv4Addr::octets`, `Ipv6Addr::octets`, \
                      `Ipv6Addr::segments` — 3 `library/core` roots) even though the address \
                      arithmetic is identical. Fields carry distinct values at a NON-ZERO \
                      offset so an offset-0 or wrong-field read is visible; the raw-pointer \
                      base rides the same arm",
            src: include_str!("bridge_corpus/fix_q_agg_field_through_deref.rs"),
        },
        Case {
            name: "fix_q_slice_arg_from_struct_field",
            bug_ref: "a `&[T]` call ARGUMENT that is a FIELD of an aggregate — `f(move \
                      (_3.1: &[u8]))`, which is what `const_eval_select!`'s `@capture` tuple \
                      produces (`slice::memchr::memchr_aligned` arg 1 and \
                      `str::validations::run_utf8_validation` arg 0, 2 `library/core` roots). \
                      A slice field of a memory-backed aggregate is ALREADY the two lanes \
                      `{data @ off, len @ off+8}`, so the field's own address IS the \
                      `{data,len}` slot the parameter ABI wants. Ordinary source spells this \
                      with a temp at every opt level, so the fixture uses the intrinsic \
                      directly. Both lanes are checked (length seeds and bounds the fold) \
                      against the whole-local argument path on the same slices",
            src: include_str!("bridge_corpus/fix_q_slice_arg_from_struct_field.rs"),
        },
        Case {
            name: "fix_q_single_upvar_closure_leaf",
            bug_ref: "a SINGLE-UPVAR closure IS its upvar and must map like one. The struct \
                      arm of the type mapper collapses a single-scalar-leaf aggregate to that \
                      leaf; the closure arm always built a tuple, so `FromFn<F>` mapped to \
                      the upvar's scalar while the closure mapped to `Tuple([<that scalar>])` \
                      — not a memory scalar — and every place-address walk bottoming out at \
                      the closure field failed closed (3 `library/core` roots, all \
                      `fmt::builders::from_fn::<closure>`). The collapse is gated on rustc's \
                      OWN layout (one upvar, at offset 0, closure size == leaf size); the \
                      TWO-upvar row is the CONTROL that the tuple mapping and its `(*env).N` \
                      index scheme are untouched",
            src: include_str!("bridge_corpus/fix_q_single_upvar_closure_leaf.rs"),
        },
        Case {
            name: "indirect_arg_lanes",
            bug_ref: "cross-backend ABI (measured 2026-09-27): rustc passes every sized \
                      `Memory` argument larger than a pointer (`{u32, u32, u32}`, `[u32; 3]`, \
                      `[u8; 16]`, 24/40-byte structs, a non-`ScalarPair` float struct, a \
                      `Memory` enum, a capturing closure) as `PassMode::Indirect` — ONE \
                      pointer to a caller-made copy — while the bridge passed the bytes \
                      (register lanes <=16 bytes, a `byval` stack copy above): an LLVM caller \
                      of a bridge callee SIGSEGV'd, the other direction read wrong values. \
                      The indirect argument lane passes the pointer; this whole-program \
                      fixture pins the bridge's own consistency across every call-site \
                      family the lane owns (direct, register exhaustion, sret + indirect, a \
                      mutating callee, recursion, closures, generic and `dyn` methods, fn \
                      pointers, const / deref / scalarized operands)",
            src: include_str!("bridge_corpus/indirect_arg_lanes.rs"),
        },
        Case {
            name: "indirect_scalar_newtype_lanes",
            bug_ref: "cross-backend ABI (measured 2026-09-28): an over-aligned single-scalar \
                      newtype (`#[repr(C, align(16))] struct A16 { a: u64 }`, \
                      `#[repr(align(128))] struct CP(u64)`) is ONE scalar to the bridge's type \
                      mapper but a padded `Memory` value rustc passes as `PassMode::Indirect`; \
                      the bridge used the pointer register as the value (LLVM rlib + bridge bin \
                      SIGSEGV). The scalar sub-lane passes a fresh padded copy; this \
                      whole-program fixture pins the bridge's own consistency across direct, \
                      exhaustion, a mutating callee, recursion, `dyn` / generic methods, fn \
                      pointers, the closure lane, const operands and an alignment above the \
                      stack's",
            src: include_str!("bridge_corpus/indirect_scalar_newtype_lanes.rs"),
        },
        Case {
            name: "padded_scalar_home_alignment",
            bug_ref: "over-aligned scalar HOMES (measured 2026-09-28): an over-aligned \
                      single-scalar newtype (`A16`, `CP` at align 128, `A8(u8)`) is ONE scalar \
                      to the bridge, and every stack home it got — the temporary behind a \
                      `&a` call argument, a raw-borrowed or closure-captured local's cell, a \
                      `&dyn` data pointer, a `&mut` temporary — was an `Alloca` of the scalar, \
                      so a `&A16` rustc promises 16-aligned was 8 mod 16 (O0 aborted on the \
                      `&*p` alignment check, O2 / O3 exited 70 against 147; an LLVM `-O2` \
                      callee loading the promised 16 bytes SIGSEGV'd). Each home now has \
                      rustc's extent and alignment",
            src: include_str!("bridge_corpus/padded_scalar_home_alignment.rs"),
        },
        Case {
            name: "entry_ref_field_address",
            bug_ref: "a field reference through a thin entry `&self` stored into a CELL \
                      (derived `Debug`'s `&&self.last_field`, unsized to `&dyn`): the x86-64 \
                      macOS bridge refused a raw-pointer / newtype / tuple field with `Place \
                      deref memory store from Rvalue::Ref (projected source's base is not a \
                      reference to a memory-eligible aggregate)` (`<VaListInner as \
                      Debug>::fmt`, the one `library/core` lowering root at O0) and a \
                      nested-struct field with `Ty::Adt multi-field struct`; the cell now \
                      holds `arg + layout offset`, read and written back through it",
            src: include_str!("bridge_corpus/entry_ref_field_address.rs"),
        },
    ]
}

// ---------------------------------------------------------------------------
// The differential test
// ---------------------------------------------------------------------------

/// THE harness: every corpus program is compiled by BOTH backends at O0/O2/O3,
/// run, and diffed. Any `Divergence` is a bridge miscompile and fails the test
/// with the bug_ref + detail. A trust-cg fail-closed is reported but not a
/// failure (the bridge refused — safe). LLVM compile errors fail loudly (bad
/// fixture).
#[test]
fn bridge_corpus_matches_llvm_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();

    let mut failures: Vec<String> = Vec::new();
    for case in corpus() {
        for opt in ["0", "2", "3"] {
            let reference = compile_link_run(case.name, case.src, opt, None);
            // A bad fixture: the oracle itself did not compile.
            if let RunOutcome::CompileError { stderr_tail } = &reference {
                panic!(
                    "FIXTURE BROKEN: LLVM could not compile `{}` (opt={opt}): {stderr_tail}",
                    case.name
                );
            }
            let test = compile_link_run(case.name, case.src, opt, Some(&dylib));
            match diff_outcomes(&reference, &test) {
                DiffVerdict::Agree => {}
                DiffVerdict::TrustCgFailedClosed(tail) => {
                    eprintln!(
                        "note: `{}` (opt={opt}) trust-cg failed closed (safe, not a miscompile): {tail}",
                        case.name
                    );
                }
                DiffVerdict::ReferenceCompileError(tail) => {
                    panic!("FIXTURE BROKEN: `{}` (opt={opt}): {tail}", case.name);
                }
                DiffVerdict::Divergence { kind, detail } => {
                    failures.push(format!(
                        "MISCOMPILE [{:?}] `{}` (opt={opt}) [{}]: {detail}",
                        kind, case.name, case.bug_ref
                    ));
                }
            }
        }
    }

    assert!(
        failures.is_empty(),
        "bridge differential found {} miscompile(s):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Two former SILENT miscompiles are claimed supported surfaces: a celled entry
/// argument read after a write through an escaped `&mut` (the read loads the
/// cell), and partial-eightbyte arrays through `black_box` (zero-extended lane
/// assembly, width-exact result stores). Every optimization level must compile
/// and agree with LLVM — a refusal here would hide the regression the row pins.
#[test]
fn former_silent_miscompiles_are_supported_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    for (name, src, code) in [
        (
            "stale_celled_entry_arg_strict",
            include_str!("bridge_corpus/stale_celled_entry_arg.rs"),
            40,
        ),
        (
            "partial_eightbyte_blackbox_strict",
            include_str!("bridge_corpus/partial_eightbyte_blackbox.rs"),
            53,
        ),
        (
            "nonnull_str_field_through_ref_strict",
            include_str!("bridge_corpus/nonnull_str_field_through_ref.rs"),
            68,
        ),
    ] {
        for opt in ["0", "2", "3"] {
            let reference = compile_link_run(name, src, opt, None);
            assert_eq!(
                reference,
                RunOutcome::Exited {
                    code,
                    stdout: Vec::new(),
                },
                "{name}: LLVM fixture result changed at opt={opt}"
            );
            let test = compile_link_run(name, src, opt, Some(&dylib));
            assert_eq!(
                diff_outcomes(&reference, &test),
                DiffVerdict::Agree,
                "{name} must compile and equal LLVM at opt={opt}; got {test:?}"
            );
        }
    }
}

/// A field reference through a thin entry reference, stored into a cell, is a
/// CLAIMED supported surface on x86-64: every optimization level must compile
/// and agree with LLVM (exit 42: every field read back through its stored
/// address is that field's) — never regress back to the deref-store refusal.
/// The four-cell cross-backend twin is `m148_x86_entry_ref_field_addr_xback`.
#[test]
fn entry_reference_field_addresses_are_supported_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let name = "entry_ref_field_address_strict";
    let src = include_str!("bridge_corpus/entry_ref_field_address.rs");
    for opt in ["0", "2", "3"] {
        let reference = compile_link_run(name, src, opt, None);
        assert_eq!(
            reference,
            RunOutcome::Exited {
                code: 42,
                stdout: Vec::new(),
            },
            "{name}: LLVM fixture result changed at opt={opt}"
        );
        let test = compile_link_run(name, src, opt, Some(&dylib));
        assert_eq!(
            diff_outcomes(&reference, &test),
            DiffVerdict::Agree,
            "{name} must compile and equal LLVM at opt={opt}; got {test:?}"
        );
    }
}

/// A CELLED return place (`library/core`'s `io::error::repr::Repr::new_custom`:
/// `&_0` borrowed into a callee whose return carries a reference) is a CLAIMED
/// supported surface: `Return` loads the cell. Every optimization level must
/// compile and agree with LLVM — never regress back to fail-closed — and the
/// readable fixture checksum must remain 4.
#[test]
fn ssa071_celled_return_place_is_supported_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = include_str!("bridge_corpus/ssa071_celled_return_place.rs");
    for opt in ["0", "2", "3"] {
        let reference = compile_link_run("ssa071_celled_return_place_strict", src, opt, None);
        assert_eq!(
            reference,
            RunOutcome::Exited {
                code: 4,
                stdout: Vec::new(),
            },
            "LLVM fixture result changed at opt={opt}"
        );
        let test = compile_link_run("ssa071_celled_return_place_strict", src, opt, Some(&dylib));
        assert_eq!(
            diff_outcomes(&reference, &test),
            DiffVerdict::Agree,
            "a celled return place must remain supported and equal LLVM at opt={opt}; \
             got {test:?}"
        );
    }
}

/// A CELLED index local (an address-taken entry argument or local) must be read
/// from its CELL by every `Index(local)` reader (`index_local_value`). The SSA
/// binding of a celled entry argument is its INCOMING parameter, which the
/// readers used to read — a SILENT WRONG VALUE (LLVM 17 vs 5; the reader battery
/// 19 vs 198) — and a celled non-argument local's is never defined (fail closed).
/// Every optimization level must compile and agree with LLVM, and the readable
/// fixture results must remain 17, 17 and 19.
#[test]
fn celled_index_locals_are_read_from_their_cells_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let rows = [
        (
            "celled_index_arg_strict",
            include_str!("bridge_corpus/celled_index_arg_custom_mir.rs"),
            17,
        ),
        (
            "celled_index_local_strict",
            include_str!("bridge_corpus/celled_index_local_custom_mir.rs"),
            17,
        ),
        (
            "celled_index_readers_strict",
            include_str!("bridge_corpus/celled_index_readers_custom_mir.rs"),
            19,
        ),
    ];
    for (stem, src, code) in rows {
        for opt in ["0", "2", "3"] {
            let reference = compile_link_run(stem, src, opt, None);
            assert_eq!(
                reference,
                RunOutcome::Exited {
                    code,
                    stdout: Vec::new(),
                },
                "{stem}: LLVM fixture result changed at opt={opt}"
            );
            let test = compile_link_run(stem, src, opt, Some(&dylib));
            assert_eq!(
                diff_outcomes(&reference, &test),
                DiffVerdict::Agree,
                "{stem}: a celled index must be read from its cell and equal LLVM at \
                 opt={opt}; got {test:?}"
            );
        }
    }
}

/// Three `library/core` [TCG-SSA-071] roots' shapes are a CLAIMED supported
/// surface through the cell retry (`overflowing_pow` for u64/u128/i128,
/// `maximal_suffix`, a diamond-then-combine accumulator). Every optimization level
/// must compile and agree with LLVM — never regress back to fail-closed — and the
/// readable fixture checksum must remain 58.
#[test]
fn ssa071_cell_retry_loops_are_supported_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = include_str!("bridge_corpus/ssa071_cell_retry_loops.rs");
    for opt in ["0", "2", "3"] {
        let reference = compile_link_run("ssa071_cell_retry_loops_strict", src, opt, None);
        assert_eq!(
            reference,
            RunOutcome::Exited {
                code: 58,
                stdout: Vec::new(),
            },
            "LLVM fixture result changed at opt={opt}"
        );
        let test = compile_link_run("ssa071_cell_retry_loops_strict", src, opt, Some(&dylib));
        assert_eq!(
            diff_outcomes(&reference, &test),
            DiffVerdict::Agree,
            "the cell-retry loops must remain supported and equal LLVM at opt={opt}; \
             got {test:?}"
        );
    }
}

/// Unlike the broad corpus (where a fail-closed result is generally acceptable),
/// overlapping copy is a claimed supported surface. Pin that stronger contract:
/// every optimization level must compile and agree with LLVM, never regress back
/// to fail-closed, and the readable fixture result must remain 110.
#[test]
fn overlapping_copy_memmove_is_supported_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = include_str!("bridge_corpus/copy_overlapping.rs");
    for opt in ["0", "2", "3"] {
        let reference = compile_link_run("copy_overlapping_strict", src, opt, None);
        assert_eq!(
            reference,
            RunOutcome::Exited {
                code: 110,
                stdout: Vec::new(),
            },
            "LLVM fixture result changed at opt={opt}"
        );
        let test = compile_link_run("copy_overlapping_strict", src, opt, Some(&dylib));
        assert_eq!(
            diff_outcomes(&reference, &test),
            DiffVerdict::Agree,
            "overlapping copy must remain supported and equal LLVM at opt={opt}; got {test:?}"
        );
    }
}

/// A tuple pointee with a nested struct / array field is a CLAIMED supported
/// surface (the `unicode_data::conversions` table shape; 10 `library/core`
/// roots). Pin the stronger contract: every optimization level must compile and
/// agree with LLVM, never regress back to fail-closed, and the readable fixture
/// checksum must remain 120.
#[test]
fn tuple_pointee_with_nested_aggregate_field_is_supported_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = include_str!("bridge_corpus/pointee_lanes_tuple_nested.rs");
    for opt in ["0", "2", "3"] {
        let reference = compile_link_run("pointee_lanes_tuple_nested_strict", src, opt, None);
        assert_eq!(
            reference,
            RunOutcome::Exited {
                code: 120,
                stdout: Vec::new(),
            },
            "LLVM fixture result changed at opt={opt}"
        );
        let test = compile_link_run("pointee_lanes_tuple_nested_strict", src, opt, Some(&dylib));
        assert_eq!(
            diff_outcomes(&reference, &test),
            DiffVerdict::Agree,
            "tuple pointee with a nested aggregate field must remain supported and equal \
             LLVM at opt={opt}; got {test:?}"
        );
    }
}

/// By-value `PassMode::Pair` ARGUMENTS are a CLAIMED supported surface (the
/// two-value argument lane; 74 `library/core` roots). Pin the stronger contract:
/// every optimization level must compile and agree with LLVM, never regress
/// back to fail-closed, and the readable fixture checksum must remain 48.
#[test]
fn scalar_pair_arguments_are_supported_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = include_str!("bridge_corpus/pair_arg_lanes.rs");
    for opt in ["0", "2", "3"] {
        let reference = compile_link_run("pair_arg_lanes_strict", src, opt, None);
        assert_eq!(
            reference,
            RunOutcome::Exited {
                code: 48,
                stdout: Vec::new(),
            },
            "LLVM fixture result changed at opt={opt}"
        );
        let test = compile_link_run("pair_arg_lanes_strict", src, opt, Some(&dylib));
        assert_eq!(
            diff_outcomes(&reference, &test),
            DiffVerdict::Agree,
            "scalar-pair arguments must remain supported and equal LLVM at opt={opt}; got {test:?}"
        );
    }
}

/// A union with a fat-pointer leaf (`MaybeUninit<Part>`) is a CLAIMED supported
/// surface (core's `flt2dec` buffers; 21 `library/core` roots). Pin the stronger
/// contract: every optimization level must compile and agree with LLVM, never
/// regress back to fail-closed, and the readable fixture checksum must remain 61.
#[test]
fn fat_leaf_union_is_supported_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = include_str!("bridge_corpus/union_fat_leaf.rs");
    for opt in ["0", "2", "3"] {
        let reference = compile_link_run("union_fat_leaf_strict", src, opt, None);
        assert_eq!(
            reference,
            RunOutcome::Exited {
                code: 61,
                stdout: Vec::new(),
            },
            "LLVM fixture result changed at opt={opt}"
        );
        let test = compile_link_run("union_fat_leaf_strict", src, opt, Some(&dylib));
        assert_eq!(
            diff_outcomes(&reference, &test),
            DiffVerdict::Agree,
            "fat-leaf union must remain supported and equal LLVM at opt={opt}; got {test:?}"
        );
    }
}

/// A closure taking a slice / `str` fat pointer is a CLAIMED supported surface
/// and its failure mode was a crash, not a refusal. Pin the stronger contract:
/// every optimization level must compile and agree with LLVM, never regress to
/// fail-closed, and the readable fixture checksum must remain 43.
#[test]
fn closure_with_a_fat_pointer_parameter_is_supported_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = include_str!("bridge_corpus/closure_slice_arg.rs");
    for opt in ["0", "2", "3"] {
        let reference = compile_link_run("closure_slice_arg_strict", src, opt, None);
        assert_eq!(
            reference,
            RunOutcome::Exited {
                code: 43,
                stdout: Vec::new(),
            },
            "LLVM fixture result changed at opt={opt}"
        );
        let test = compile_link_run("closure_slice_arg_strict", src, opt, Some(&dylib));
        assert_eq!(
            diff_outcomes(&reference, &test),
            DiffVerdict::Agree,
            "a closure with a fat-pointer parameter must remain supported and equal LLVM at \
             opt={opt}; got {test:?}"
        );
    }
}

/// Every x86-64 `PassMode::Pair` argument rides the two-value lane, including at
/// register exhaustion (one integer register left). The cross-backend agreement
/// is `m144`; this pins the bridge's own whole-program consistency across every
/// call-site family the lane now owns: every optimization level must compile,
/// agree with LLVM and keep 23.
#[test]
fn pair_arguments_at_register_exhaustion_are_supported_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = include_str!("bridge_corpus/pair_arg_exhaustion.rs");
    for opt in ["0", "2", "3"] {
        let reference = compile_link_run("pair_arg_exhaustion_strict", src, opt, None);
        assert_eq!(
            reference,
            RunOutcome::Exited {
                code: 23,
                stdout: Vec::new(),
            },
            "LLVM fixture result changed at opt={opt}"
        );
        let test = compile_link_run("pair_arg_exhaustion_strict", src, opt, Some(&dylib));
        assert_eq!(
            diff_outcomes(&reference, &test),
            DiffVerdict::Agree,
            "a pair argument at register exhaustion must remain supported and equal LLVM at \
             opt={opt}; got {test:?}"
        );
    }
}

/// Every sized `Memory` argument larger than a pointer rides rustc's
/// `PassMode::Indirect` pointer (the indirect argument lane). The cross-backend
/// agreement is `m145`; this pins the bridge's own whole-program consistency
/// across every call-site family the lane owns: every optimization level must
/// compile, agree with LLVM and keep 107.
#[test]
fn indirect_arguments_are_supported_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = include_str!("bridge_corpus/indirect_arg_lanes.rs");
    for opt in ["0", "2", "3"] {
        let reference = compile_link_run("indirect_arg_lanes_strict", src, opt, None);
        assert_eq!(
            reference,
            RunOutcome::Exited {
                code: 107,
                stdout: Vec::new(),
            },
            "LLVM fixture result changed at opt={opt}"
        );
        let test = compile_link_run("indirect_arg_lanes_strict", src, opt, Some(&dylib));
        assert_eq!(
            diff_outcomes(&reference, &test),
            DiffVerdict::Agree,
            "an indirect (`PassMode::Indirect`) argument must remain supported and equal LLVM \
             at opt={opt}; got {test:?}"
        );
    }
}

/// An over-aligned single-scalar newtype rides the indirect argument lane's
/// SCALAR SUB-LANE (a fresh padded copy, the scalar at offset 0). The
/// cross-backend agreement is `m145`'s `w1_*` rows; this pins the bridge's own
/// whole-program consistency: every optimization level must compile, agree with
/// LLVM and keep 7.
#[test]
fn indirect_scalar_newtype_arguments_are_supported_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = include_str!("bridge_corpus/indirect_scalar_newtype_lanes.rs");
    for opt in ["0", "2", "3"] {
        let reference = compile_link_run("indirect_scalar_newtype_lanes_strict", src, opt, None);
        assert_eq!(
            reference,
            RunOutcome::Exited {
                code: 7,
                stdout: Vec::new(),
            },
            "LLVM fixture result changed at opt={opt}"
        );
        let test = compile_link_run(
            "indirect_scalar_newtype_lanes_strict",
            src,
            opt,
            Some(&dylib),
        );
        assert_eq!(
            diff_outcomes(&reference, &test),
            DiffVerdict::Agree,
            "a padded single-scalar newtype argument must remain supported and equal LLVM at \
             opt={opt}; got {test:?}"
        );
    }
}

/// Every stack home of an over-aligned single-scalar newtype (the temporary
/// behind a `&a` call argument, a raw-borrowed or closure-captured local's
/// cell, a `&dyn` data pointer, a `&mut` temporary) has rustc's extent and
/// alignment (`padded_scalar_home_extent`): no misalignment flag, every
/// optimization level, equal to LLVM (147).
#[test]
fn padded_scalar_homes_are_rustc_aligned_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = include_str!("bridge_corpus/padded_scalar_home_alignment.rs");
    for opt in ["0", "2", "3"] {
        let reference = compile_link_run("padded_scalar_home_alignment_strict", src, opt, None);
        assert_eq!(
            reference,
            RunOutcome::Exited {
                code: 147,
                stdout: Vec::new(),
            },
            "LLVM fixture result changed at opt={opt}"
        );
        let test = compile_link_run(
            "padded_scalar_home_alignment_strict",
            src,
            opt,
            Some(&dylib),
        );
        assert_eq!(
            diff_outcomes(&reference, &test),
            DiffVerdict::Agree,
            "an over-aligned scalar newtype's stack homes must be rustc-aligned and equal \
             LLVM at opt={opt}; got {test:?}"
        );
    }
}

/// A struct field of the transparent wide-slice newtype, built from a slotted
/// parameter and read back two-lane, is a CLAIMED supported surface. Pin it
/// strict: every optimization level must compile, agree with LLVM and keep 77.
#[test]
fn nonnull_holder_field_is_supported_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = include_str!("bridge_corpus/nonnull_holder_field.rs");
    for opt in ["0", "2", "3"] {
        let reference = compile_link_run("nonnull_holder_field_strict", src, opt, None);
        assert_eq!(
            reference,
            RunOutcome::Exited {
                code: 77,
                stdout: Vec::new(),
            },
            "LLVM fixture result changed at opt={opt}"
        );
        let test = compile_link_run("nonnull_holder_field_strict", src, opt, Some(&dylib));
        assert_eq!(
            diff_outcomes(&reference, &test),
            DiffVerdict::Agree,
            "the newtype struct field must remain supported and equal LLVM at opt={opt}; got {test:?}"
        );
    }
}

/// The transparent wide-slice newtype at a boundary (`NonNull<[T]>` / `NonNull<str>`
/// by value) is a CLAIMED supported surface (47 `library/core` roots). Pin the
/// stronger contract: every optimization level must compile and agree with
/// LLVM, never regress back to fail-closed, and the fixture sum must remain 52.
#[test]
fn transparent_wide_slice_newtype_at_the_boundary_is_supported_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = include_str!("bridge_corpus/m143_nonnull_slice_boundary.rs");
    for opt in ["0", "2", "3"] {
        let reference = compile_link_run("m143_nonnull_slice_boundary_strict", src, opt, None);
        assert_eq!(
            reference,
            RunOutcome::Exited {
                code: 52,
                stdout: Vec::new(),
            },
            "LLVM fixture result changed at opt={opt}"
        );
        let test = compile_link_run("m143_nonnull_slice_boundary_strict", src, opt, Some(&dylib));
        assert_eq!(
            diff_outcomes(&reference, &test),
            DiffVerdict::Agree,
            "the transparent wide-slice newtype must remain supported and equal LLVM at opt={opt}; got {test:?}"
        );
    }
}

/// Unlike the broad corpus, this pins the newly claimed intrinsic at the O0 call
/// path that actually reaches `float_to_int_unchecked`: it must compile, execute,
/// and agree with LLVM over defined (in-range, non-NaN) inputs.
#[test]
fn float_to_int_unchecked_is_supported_and_matches_llvm_at_o0() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = include_str!("bridge_corpus/float_to_int_unchecked.rs");
    let reference = compile_link_run("float_to_int_unchecked_strict", src, "0", None);
    assert_eq!(
        reference,
        RunOutcome::Exited {
            code: 145,
            stdout: Vec::new(),
        },
        "LLVM fixture result changed"
    );
    let test = compile_link_run("float_to_int_unchecked_strict", src, "0", Some(&dylib));
    assert_eq!(
        diff_outcomes(&reference, &test),
        DiffVerdict::Agree,
        "float_to_int_unchecked must compile and equal LLVM at O0; got {test:?}"
    );
}

// ---------------------------------------------------------------------------
// In-test smoke for the inline diff engine (no compiler needed). The
// authoritative tests are in trust-cg-fuzz; this just guards the inline copy.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// P1.3 gate wiring regression (no compiler / toolchain / x86 host required).
//
// The bridge's `mir_to_trust_ir` now calls
// `trust_cg_verify::ssa_loop_complete::check_function_fail_closed(&func)` before
// inserting the produced function into the module. These two tests exercise that
// EXACT symbol against trust-ir built by hand, so the wiring residual is proven
// closed independent of the Trust x86 std + x86 host the differential needs:
//   - the #71 dropped-aggregate-field loop shape is REJECTED (fail closed),
//     which is the bug the bridge could previously emit silently; and
//   - a correctly-threaded loop is ACCEPTED (no over-eager fail-closed that
//     would reject all real loops).
// The shapes mirror `trust_cg_verify::ssa_loop_complete`'s own unit fixtures.
// ---------------------------------------------------------------------------

use trust_ir::{
    BinOp, Block, BlockId, Constant, FuncId, FuncTyId, Function, ICmpOp, Inst, InstrNode, Ty,
    ValueId,
};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
fn bb(n: u32) -> BlockId {
    BlockId::new(n)
}

/// CORRECTLY-THREADED scalar loop: both loop-carried scalars (`acc`, `i`) are
/// threaded through header params + back-edge args. The gate must ACCEPT this.
///
///   bb0: %0=0(acc) %1=0(i); br bb1(%0,%1)
///   bb1(%acc,%i): %2=10; %3=icmp slt %i,%2; condbr %3, bb2, bb3
///   bb2: %4=1; %5=add %acc,%4; %6=add %i,%4; br bb1(%5,%6)
///   bb3: return %acc
fn threaded_scalar_loop() -> Function {
    let mut f = Function::new(FuncId::new(0), "threaded", FuncTyId::new(0), bb(0));

    let mut bb0 = Block::new(bb(0));
    bb0.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(0),
        })
        .with_result(v(0)),
    );
    bb0.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(0),
        })
        .with_result(v(1)),
    );
    bb0.body.push(InstrNode::new(Inst::Br {
        target: bb(1),
        args: vec![v(0), v(1)],
    }));

    let mut bb1 = Block::new(bb(1))
        .with_param(v(10), Ty::I32)
        .with_param(v(11), Ty::I32);
    bb1.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(10),
        })
        .with_result(v(2)),
    );
    bb1.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Slt,
            ty: Ty::I32,
            lhs: v(11),
            rhs: v(2),
        })
        .with_result(v(3)),
    );
    bb1.body.push(InstrNode::new(Inst::CondBr {
        cond: v(3),
        then_target: bb(2),
        then_args: vec![],
        else_target: bb(3),
        else_args: vec![],
    }));

    let mut bb2 = Block::new(bb(2));
    bb2.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(1),
        })
        .with_result(v(4)),
    );
    bb2.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(10),
            rhs: v(4),
        })
        .with_result(v(5)),
    );
    bb2.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(11),
            rhs: v(4),
        })
        .with_result(v(6)),
    );
    bb2.body.push(InstrNode::new(Inst::Br {
        target: bb(1),
        args: vec![v(5), v(6)],
    }));

    let mut bb3 = Block::new(bb(3));
    bb3.body.push(InstrNode::new(Inst::Return {
        values: vec![v(10)],
    }));

    f.blocks = vec![bb0, bb1, bb2, bb3];
    f
}

/// The #71 DROPPED-UPDATE shape: the scalarized aggregate field `q.a` has NO
/// header param; its in-loop redefinition (`%5 = add %0(entry q.a), 1`) is
/// computed in the latch and then DROPPED on the back-edge (only `i'` is
/// threaded). The header keeps the entry value `%0` (which dominates it, so plain
/// SSA dominance is satisfied), so the update is silently lost — exactly #71. The
/// gate must REJECT this.
fn dropped_aggregate_loop() -> Function {
    let mut f = Function::new(FuncId::new(0), "dropped", FuncTyId::new(0), bb(0));

    let mut bb0 = Block::new(bb(0));
    bb0.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(0),
        })
        .with_result(v(0)),
    );
    bb0.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(0),
        })
        .with_result(v(1)),
    );
    bb0.body.push(InstrNode::new(Inst::Br {
        target: bb(1),
        args: vec![v(1)],
    }));

    let mut bb1 = Block::new(bb(1)).with_param(v(11), Ty::I32);
    bb1.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(10),
        })
        .with_result(v(2)),
    );
    bb1.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Slt,
            ty: Ty::I32,
            lhs: v(11),
            rhs: v(2),
        })
        .with_result(v(3)),
    );
    bb1.body.push(InstrNode::new(Inst::CondBr {
        cond: v(3),
        then_target: bb(2),
        then_args: vec![],
        else_target: bb(3),
        else_args: vec![],
    }));

    let mut bb2 = Block::new(bb(2));
    bb2.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(1),
        })
        .with_result(v(4)),
    );
    // q.a' = entry q.a (%0) + 1 — computed but never threaded back (DROPPED).
    bb2.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(4),
        })
        .with_result(v(5)),
    );
    bb2.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(11),
            rhs: v(4),
        })
        .with_result(v(6)),
    );
    // Only i' (%6) is threaded; q.a' (%5) is silently dropped.
    bb2.body.push(InstrNode::new(Inst::Br {
        target: bb(1),
        args: vec![v(6)],
    }));

    let mut bb3 = Block::new(bb(3));
    bb3.body
        .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));

    f.blocks = vec![bb0, bb1, bb2, bb3];
    f
}

/// The gate the bridge now calls must REJECT the #71 dropped-update loop. Before
/// the wiring, the bridge could insert this exact malformed function and emit a
/// silent miscompile; the gate turns the whole class into a fail-closed compile
/// error (`Err`), which the diff engine reports as `TrustCgFailedClosed`.
#[test]
fn p1_3_gate_rejects_71_dropped_aggregate_update() {
    let f = dropped_aggregate_loop();
    let err = trust_cg_verify::ssa_loop_complete::check_function_fail_closed(&f)
        .expect_err("P1.3 gate must reject the #71 dropped-update loop");
    assert!(
        err.contains("loop-carried") || err.contains("#71"),
        "expected a loop-completeness fail-closed message, got: {err}"
    );
}

/// The gate must ACCEPT a correctly-threaded loop — guarding against an
/// over-eager fail-closed that would reject every real loop the bridge produces.
#[test]
fn p1_3_gate_accepts_threaded_scalar_loop() {
    let f = threaded_scalar_loop();
    let result = trust_cg_verify::ssa_loop_complete::check_function_fail_closed(&f);
    assert!(
        result.is_ok(),
        "P1.3 gate wrongly rejected a correctly-threaded loop: {:?}",
        result.err()
    );
}

#[test]
fn inline_diff_engine_smoke() {
    assert_eq!(
        diff_outcomes(
            &RunOutcome::Exited {
                code: 1,
                stdout: vec![]
            },
            &RunOutcome::Exited {
                code: 1,
                stdout: vec![]
            }
        ),
        DiffVerdict::Agree
    );
    assert!(matches!(
        diff_outcomes(
            &RunOutcome::Exited {
                code: 60,
                stdout: vec![]
            },
            &RunOutcome::Exited {
                code: 30,
                stdout: vec![]
            }
        ),
        DiffVerdict::Divergence {
            kind: DivergenceKind::WrongValue,
            ..
        }
    ));
    assert!(matches!(
        diff_outcomes(
            &RunOutcome::Exited {
                code: 0,
                stdout: vec![]
            },
            &RunOutcome::Signalled { signal: 8 }
        ),
        DiffVerdict::Divergence {
            kind: DivergenceKind::TrapMismatch,
            ..
        }
    ));
    assert!(matches!(
        diff_outcomes(
            &RunOutcome::Exited {
                code: 0,
                stdout: vec![]
            },
            &RunOutcome::CompileError {
                stderr_tail: "x".into()
            }
        ),
        DiffVerdict::TrustCgFailedClosed(_)
    ));
}
