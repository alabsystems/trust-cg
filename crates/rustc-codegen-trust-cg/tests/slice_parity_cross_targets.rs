#![cfg(all(target_arch = "x86_64", target_os = "linux"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: the target sets of the slice capabilities, measured by
// object emission for the bridge's other targets on an x86-64 Linux host.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Each `support/slice_parity/cap_*.rs` library crate drives one admission and
// is compiled by the bridge to an object (`--emit obj`, O0 and O2) for
// aarch64-unknown-linux-gnu, aarch64-apple-darwin and wasm32-unknown-unknown.
// The expected outcome of every cell is the target set its predicate states
// (`print_std_fallback_target`, `array_element_aggregate_target`,
// `union_transmute_slot_target`, `typed_swap_thin_pointer_target`,
// `slice_element_newtype_borrow_target`,
// `aggregate_stored_reference_cell_target`, and the Box payload lane's
// `abort_payload_lane`): an admitted target must produce an object that
// defines the crate's export; an excluded target must refuse with the
// refusal it had before the admission. Widening or narrowing a predicate
// flips a row and fails here.
//
// EVIDENCE BOUNDARY: compile-only. Nothing here is executed; an AArch64
// object compiled here is "written, compiled, not executed" (its executing
// test is `tests/slice_capabilities_2_linux.rs` on an AArch64 Linux host).
// The AArch64 Darwin and wasm32 rows record EXCLUSION only: each capability
// must still be refused there with the refusal it had before.
//
// Prerequisite: SLICE_PARITY_CROSS_SYSROOT. When it is unset the test prints
// "SKIPPED" and PASSES without judging a cell, so an ordinary `cargo test`
// run (the landing train's included) checks none of this; only a run that
// sets the variable does (`reports/2026-11-15-slice-parity/AARCH64_VALIDATION.md`
// section 4). It names a sysroot whose `lib/rustlib/<target>/lib` holds std
// for the three targets, built by `scripts/build_cross_sysroot.sh` with this
// test's build compiler.
// The name is deliberately outside the `TRUST_CG_*` / `TCG_*` family, which
// trustc refuses in its environment and the Cargo runner forwards to every
// test process (a variable of that family would make every compile in the
// run fail and every toolchain-probing test skip).

use std::path::{Path, PathBuf};

const SYSROOT_ENV: &str = "SLICE_PARITY_CROSS_SYSROOT";
const LINUX: &str = "aarch64-unknown-linux-gnu";
const DARWIN: &str = "aarch64-apple-darwin";
const WASM: &str = "wasm32-unknown-unknown";
const TARGETS: [&str; 3] = [LINUX, DARWIN, WASM];

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// An object defining this export.
    Object(&'static str),
    /// A refusal whose text contains this.
    Refused(&'static str),
    /// No claim (the cell is outside this test's scope and recorded as such).
    Unjudged,
}

struct Case {
    crate_file: &'static str,
    /// Expected outcome per target at O0, then at O2.
    expect: fn(&str, &str) -> Expect,
}

fn object_magic(target: &str) -> &'static [u8] {
    match target {
        LINUX => b"\x7fELF",
        DARWIN => b"\xcf\xfa\xed\xfe",
        _ => b"\0asm",
    }
}

fn cases() -> Vec<Case> {
    vec![
        Case {
            crate_file: "cap_print.rs",
            expect: |target, _| match target {
                LINUX => Expect::Object("cap_print"),
                _ => Expect::Refused("[TCG-FMT-DECLINED]"),
            },
        },
        Case {
            crate_file: "cap_box.rs",
            expect: |target, _| match target {
                // AArch64 Linux keeps the refusal its native control pins
                // (`tests/drop_heap_linux.rs`, "recursive drop glue").
                LINUX => Expect::Refused("drop_glue"),
                _ => Expect::Unjudged,
            },
        },
        Case {
            crate_file: "cap_elem.rs",
            expect: |target, _| match target {
                LINUX => Expect::Object("unflatten"),
                _ => Expect::Refused("copy_el: ADT Use source projection"),
            },
        },
        Case {
            crate_file: "cap_union.rs",
            expect: |target, opt| match (target, opt) {
                (LINUX, _) => Expect::Object("cap_union"),
                (_, "2") => Expect::Refused("Ty::Adt multi-field struct Ids"),
                // O0 elsewhere: refused before the transmute is reached
                // (Darwin cross: the aggregate ABI scope; wasm32: the
                // `assume_init` call's by-value union argument).
                _ => Expect::Unjudged,
            },
        },
        Case {
            crate_file: "cap_swap.rs",
            expect: |target, _| match target {
                LINUX => Expect::Object("cap_swap"),
                // The crate's `[&x, &y, &z]` is refused first: the
                // stored-reference cells are excluded there too. This row
                // therefore pins the CELLS exclusion; the swap exclusion is
                // pinned by `cap_swap_only` below.
                _ => Expect::Refused("cap_swap: borrowed scalar reference used without deref"),
            },
        },
        Case {
            crate_file: "cap_swap_only.rs",
            expect: |target, _| match target {
                LINUX => Expect::Object("cap_swap_raw"),
                // No aggregate-stored reference: the swap's own refusal.
                _ => Expect::Refused("typed_swap_nonoverlapping over non-scalar *const u32"),
            },
        },
        Case {
            crate_file: "cap_slicepart.rs",
            expect: |target, _| match target {
                LINUX => Expect::Object("cap_bump"),
                _ => Expect::Refused(
                    "cap_bump: Rvalue::Ref source projection is not scalar-bindable",
                ),
            },
        },
        Case {
            crate_file: "cap_coroutine.rs",
            expect: |target, _| match target {
                // A coroutine upvar aggregate is not followed by the
                // stored-reference cell pass: AArch64 Linux keeps the refusal
                // its native control pins (`tests/coroutine_generator_linux.rs`,
                // `ay_gen_resume_args`). The other targets are not judged.
                LINUX => {
                    Expect::Refused("cap_coroutine: borrowed scalar reference used without deref")
                }
                _ => Expect::Unjudged,
            },
        },
        Case {
            crate_file: "cap_cells.rs",
            expect: |target, _| match target {
                LINUX => Expect::Object("cap_cells"),
                _ => Expect::Refused("cap_cells: borrowed scalar reference used without deref"),
            },
        },
    ]
}

fn rust_lld(sysroot_of_driver: &Path) -> PathBuf {
    sysroot_of_driver.join("lib/rustlib/x86_64-unknown-linux-gnu/bin/rust-lld")
}

fn driver_sysroot() -> PathBuf {
    let out = toolchain_support::rustc_driver_command()
        .env_remove(SYSROOT_ENV)
        .args(["--print", "sysroot"])
        .output()
        .expect("driver --print sysroot");
    PathBuf::from(String::from_utf8_lossy(&out.stdout).trim())
}

#[test]
fn slice_capability_target_sets_hold_on_cross_targets() {
    if toolchain_support::skip_without_backend_knobs(
        "slice_capability_target_sets_hold_on_cross_targets",
    ) {
        return;
    }
    let Some(cross) = std::env::var_os(SYSROOT_ENV).map(PathBuf::from) else {
        eprintln!(
            "slice_capability_target_sets_hold_on_cross_targets: SKIPPED — {SYSROOT_ENV} is \
             unset; build one with scripts/build_cross_sysroot.sh"
        );
        return;
    };
    for target in TARGETS {
        let lib = cross.join("lib/rustlib").join(target).join("lib");
        assert!(lib.is_dir(), "{SYSROOT_ENV} has no {}", lib.display());
    }
    let lld = rust_lld(&driver_sysroot());
    assert!(lld.is_file(), "no rust-lld at {}", lld.display());
    let dylib = backend_artifact_support::current_test_backend();
    let dir = std::env::temp_dir().join(format!("rcl2_slice_parity_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("workdir");
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/support/slice_parity");
    let mut failures = Vec::new();
    let mut judged = 0;
    for case in cases() {
        let src = fixtures.join(case.crate_file);
        for target in TARGETS {
            for opt in ["0", "2"] {
                let expect = (case.expect)(target, opt);
                if matches!(expect, Expect::Unjudged) {
                    continue;
                }
                judged += 1;
                let obj = dir.join(format!("{}.{target}.O{opt}.o", case.crate_file));
                let mut backend = std::ffi::OsString::from("-Zcodegen-backend=");
                backend.push(&dylib);
                let mut cmd = toolchain_support::rustc_command();
                cmd.env_remove(SYSROOT_ENV)
                    .arg("--sysroot")
                    .arg(&cross)
                    .args(["--target", target, "--crate-type", "lib", "--emit", "obj"])
                    .args(["-Cpanic=abort", "-Awarnings"])
                    .arg(format!("-Copt-level={opt}"))
                    .arg(backend)
                    .arg("-Ztrust-ir-cg-args=no-proof-certs")
                    .arg("-Ztrust-ir-cg-args=refine-solver=0");
                // A multi-object compile is partially linked; the host `cc`
                // cannot link AArch64 objects, the toolchain's own lld can.
                match target {
                    LINUX => {
                        cmd.arg(format!("-Clinker={}", lld.display()))
                            .arg("-Clinker-flavor=ld.lld");
                    }
                    DARWIN => {
                        cmd.arg(format!("-Clinker={}", lld.display()))
                            .arg("-Clinker-flavor=ld64.lld");
                    }
                    _ => {}
                }
                let out = cmd
                    .arg("-o")
                    .arg(&obj)
                    .arg(&src)
                    .output()
                    .expect("spawn rustc");
                let stderr = String::from_utf8_lossy(&out.stderr);
                let cell = format!("{} {target} -O{opt}", case.crate_file);
                match expect {
                    Expect::Object(symbol) => {
                        if !out.status.success() {
                            failures.push(format!("{cell}: expected an object, refused: {stderr}"));
                            continue;
                        }
                        let bytes = std::fs::read(&obj).unwrap_or_default();
                        if !bytes.starts_with(object_magic(target)) {
                            failures.push(format!("{cell}: output is not a {target} object"));
                        }
                        if !bytes.windows(symbol.len()).any(|w| w == symbol.as_bytes()) {
                            failures.push(format!("{cell}: object does not name `{symbol}`"));
                        }
                    }
                    Expect::Refused(text) => {
                        if out.status.success() {
                            failures.push(format!(
                                "{cell}: compiled, expected a refusal naming {text:?}"
                            ));
                        } else if !stderr.contains(text) {
                            failures
                                .push(format!("{cell}: refusal does not name {text:?}: {stderr}"));
                        }
                    }
                    Expect::Unjudged => unreachable!(),
                }
            }
        }
    }
    eprintln!("slice parity cross-target cells judged: {judged}");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "{} cell(s) off their target set:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
