#![cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: four capabilities the Clean slices needed (second round,
// 2026-11-15), and the two first-round ones widened to AArch64 Linux (5, 6),
// each compiled by the bridge for the HOST and RUN at -O0..-O3 and compared
// with rustc's LLVM backend at the same level on stdout bytes, stderr bytes
// and exit status. It runs on x86-64 Linux (where it was measured) and on
// AArch64 Linux (`reports/2026-11-15-slice-parity/AARCH64_VALIDATION.md`;
// on the authoring host the AArch64 leg is written, compiled, not executed).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// 1. `typed_swap_nonoverlapping` of one THIN pointer value
//    (`typed_swap_thin_pointer_value`): `slice::reverse` over `[&T]`,
//    `mem::swap` of `*const T` / `&mut T`. Wide pointers keep their own arms.
// 2. A borrow of a single-scalar STRUCT part of a slice element
//    (`&all[i].name` with `struct Name(u32)`,
//    `slice_element_part_is_scalar_value`), in the scalar-binding arm and its
//    deref-store twin. Enum parts keep their route (pinned below).
// 3. A reference to a scalar local stored into an aggregate (`[&x, &y]`,
//    `(&a, &b, 2)`, a struct field): the referent is celled
//    (`compute_scalar_cell_locals`' aggregate-stored pass), so the stored
//    address is real. A slot-modelled collection referent is not celled
//    (pinned: match or named refusal), and neither is a `fn` pointer referent
//    (pinned: refused on x86-64). A reference local celled this way may itself
//    hold a slice-element part borrow: the deref-store twin of 2.
// 4. `MaybeUninit<S>` of a multi-field struct transmuted to `S`
//    (`assume_init` inlined) on x86-64 Linux: rule 0f gives the union endpoint
//    a byte slot (`union_transmute_slot_target`).
// 5. The `print!` std fallback (`print_std_fallback_target`).
// 6. A whole aggregate stored to an element of a referenced sized array
//    (`array_element_aggregate_target`).
//
// EVIDENCE BOUNDARY: a differential test on fixed inputs, proofs-off lane
// (`-Ztrust-verify=off`, `no-proof-certs`); not proof evidence.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = if cfg!(target_arch = "aarch64") {
    host_target_support::AARCH64_TARGET
} else {
    host_target_support::X86_64_TARGET
};
const OPT_LEVELS: [&str; 4] = ["0", "1", "2", "3"];

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_slicecap2_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

#[derive(Debug, PartialEq, Eq)]
struct RunResult {
    stdout: String,
    stderr: String,
    code: Option<i32>,
    signal: Option<i32>,
}

fn run_bin(bin: &Path) -> RunResult {
    use std::os::unix::process::ExitStatusExt;
    let out = Command::new(bin).output().expect("run binary");
    RunResult {
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
        code: out.status.code(),
        signal: out.status.signal(),
    }
}

enum Outcome {
    Ran(RunResult),
    Refused(String),
}

fn compile(dir: &Path, dylib: Option<&Path>, stem: &str, src: &str, opt: &str) -> Outcome {
    let src_path = dir.join(format!("{stem}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let arm = if dylib.is_some() { "cg" } else { "llvm" };
    let bin = dir.join(format!("{stem}_{arm}_O{opt}"));
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "--target", TARGET])
        .arg("-Cpanic=abort")
        .arg(format!("-Copt-level={opt}"))
        .args(["-Coverflow-checks=off", "-Ccodegen-units=1", "-Awarnings"]);
    if let Some(dylib) = dylib {
        let mut backend = std::ffi::OsString::from("-Zcodegen-backend=");
        backend.push(dylib);
        cmd.arg(backend)
            .arg("-Ztrust-ir-cg-args=no-proof-certs")
            .arg("-Ztrust-ir-cg-args=refine-solver=0");
    }
    let output = cmd
        .arg("-o")
        .arg(&bin)
        .arg(&src_path)
        .output()
        .expect("spawn rustc");
    if !output.status.success() {
        return Outcome::Refused(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Outcome::Ran(run_bin(&bin))
}

fn llvm(dir: &Path, stem: &str, src: &str, opt: &str) -> RunResult {
    match compile(dir, None, stem, src, opt) {
        Outcome::Ran(result) => result,
        Outcome::Refused(stderr) => panic!("LLVM failed to compile `{stem}`: {stderr}"),
    }
}

/// Every case must compile under the bridge and equal LLVM at every level.
fn require_match(test: &str, cases: &[(&str, &str)]) {
    if skip() {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir(test);
    for (stem, src) in cases {
        for opt in OPT_LEVELS {
            let want = llvm(&dir, stem, src, opt);
            match compile(&dir, Some(&dylib), stem, src, opt) {
                Outcome::Ran(got) => {
                    assert_eq!(
                        got, want,
                        "`{stem}` at -O{opt}: bridge output differs from LLVM"
                    )
                }
                Outcome::Refused(stderr) => {
                    panic!("`{stem}` refused at -O{opt}, expected to compile: {stderr}")
                }
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Each case must either compile and equal LLVM, or refuse by name; a wrong
/// value never passes.
fn require_match_or_named_refusal(test: &str, cases: &[(&str, &str)]) {
    if skip() {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir(test);
    for (stem, src) in cases {
        for opt in OPT_LEVELS {
            let want = llvm(&dir, stem, src, opt);
            match compile(&dir, Some(&dylib), stem, src, opt) {
                Outcome::Ran(got) => assert_eq!(got, want, "`{stem}` at -O{opt}: WRONG output"),
                Outcome::Refused(stderr) => assert!(
                    stderr.contains("[TCG-MIR-UNSUPPORTED]"),
                    "`{stem}` at -O{opt}: refusal is not a named fail-closed: {stderr}"
                ),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

fn skip() -> bool {
    if !toolchain_support::target_std_available(TARGET) {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return true;
    }
    false
}

const SWAP_POINTERS: &str = include_str!("support/slice_capabilities_2/swap_pointers.rs");
const SWAP_SHAPES: &str = include_str!("support/slice_capabilities_2/swap_shapes.rs");
const SWAP_CSTR: &str = include_str!("support/slice_capabilities_2/swap_cstr.rs");
const SWAP_DST: &str = include_str!("support/slice_capabilities_2/swap_dst.rs");
const SWAP_WIDE_MORE: &str = include_str!("support/slice_capabilities_2/swap_wide_more.rs");
const SLICE_PART: &str = include_str!("support/slice_capabilities_2/slice_part.rs");
const SLICE_PART_SHAPES: &str = include_str!("support/slice_capabilities_2/slice_part_shapes.rs");
const PIN_ENUM_PART: &str = include_str!("support/slice_capabilities_2/pin_enum_part.rs");
const CELLS_ARRAY: &str = include_str!("support/slice_capabilities_2/cells_array.rs");
const CELLS_SHAPES: &str = include_str!("support/slice_capabilities_2/cells_shapes.rs");
const PIN_VEC_REFERENCE: &str = include_str!("support/slice_capabilities_2/pin_vec_reference.rs");
const CELLS_SLICE_PART: &str = include_str!("support/slice_capabilities_2/cells_slice_part.rs");
const PIN_FN_POINTER_REFERENCE: &str =
    include_str!("support/slice_capabilities_2/pin_fn_pointer_reference.rs");
const UNION_STRUCT: &str = include_str!("support/slice_capabilities_2/union_struct.rs");
const UNION_SHAPES: &str = include_str!("support/slice_capabilities_2/union_shapes.rs");
const PRINT_SHAPES: &str = include_str!("support/slice_capabilities_2/print_shapes.rs");
const ELEMENT_STORE: &str = include_str!("support/slice_capabilities_2/element_store.rs");

/// `slice::reverse` over `[&E]` and `[*mut u16]`, `mem::swap` of `*const u8`,
/// `&mut u64`, `*const Zst` and `Option<&u64>`, `<[&u64]>::swap`.
#[test]
fn thin_pointer_swaps_match_llvm() {
    require_match(
        "swap",
        &[
            ("swap_pointers", SWAP_POINTERS),
            ("swap_shapes", SWAP_SHAPES),
        ],
    );
}

/// Wide-pointer swaps (`&CStr`, slice-tail DSTs `&Hdr<[u8]>` / `&Hdr<[u32]>`,
/// `*const [u16]`, `&mut str`, `&Path`, `[u8]` newtypes) are not this
/// admission's: they keep the two-lane arms. Match or named refusal. A net:
/// removing the layout thinness check of `typed_swap_thin_pointer_value`
/// changes none of them (no producer reaches that check; it is kept as a
/// fail-closed condition, not credited as tested).
#[test]
fn wide_pointer_swaps_keep_their_two_lane_route() {
    require_match_or_named_refusal(
        "swap_wide",
        &[
            ("swap_cstr", SWAP_CSTR),
            ("swap_dst", SWAP_DST),
            ("swap_wide_more", SWAP_WIDE_MORE),
        ],
    );
}

/// `&all[i].name == n` over `&[Ind]` and `&mut all[i].name` with
/// `struct Name(u32)`, plus `u64`, `f32`, `repr(transparent)` `i16`, a nested
/// newtype, an `Option` part, a `Cell<u32>` part written through `&`, and a
/// slice pattern's last element.
#[test]
fn slice_element_newtype_parts_match_llvm() {
    require_match(
        "slice_part",
        &[
            ("slice_part", SLICE_PART),
            ("slice_part_shapes", SLICE_PART_SHAPES),
        ],
    );
}

/// An ENUM part of a slice element (`&all[i].w` with a fieldless `enum K16`,
/// whose layout is one `Scalar`) is not admitted: the struct-only arm of
/// `slice_element_part_is_scalar_value`. Pinned as measured on 2026-11-15:
/// `findw` refuses by name at every level (O0/O1 "Rvalue::Ref source
/// projection is not scalar-bindable", O2/O3 a discriminant read through the
/// slice). Admitting enum parts is a new capability that must update this pin.
#[test]
fn slice_element_enum_part_keeps_its_refusal() {
    if skip() {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("enum_part");
    for opt in OPT_LEVELS {
        let _ = llvm(&dir, "pin_enum_part", PIN_ENUM_PART, opt);
        match compile(&dir, Some(&dylib), "pin_enum_part", PIN_ENUM_PART, opt) {
            Outcome::Refused(stderr) => {
                assert!(
                    stderr.contains("[TCG-MIR-UNSUPPORTED]") && stderr.contains("5findw"),
                    "-O{opt}: expected the named refusal of `findw`: {stderr}"
                );
                // The O0/O1 text was measured on x86-64; AArch64 Linux gives a
                // borrowed reference passed to a call its own home
                // (`call_references`), so its refusal may be raised by the
                // deref-store path instead. Only the named refusal is pinned there.
                if cfg!(target_arch = "x86_64") && matches!(opt, "0" | "1") {
                    assert!(
                        stderr.contains("Rvalue::Ref source projection is not scalar-bindable"),
                        "-O{opt}: expected the scalar-binding refusal: {stderr}"
                    );
                }
            }
            Outcome::Ran(got) => {
                panic!("-O{opt}: the enum part compiled ({got:?}); pinned as refused")
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// `[&x]` / `[&x, &y]` of scalar newtype locals, a struct holding two
/// references, a tuple `(&u32, &bool, u8)`, `[&mut x, &mut y]` written
/// through, pointer identity of two stored `&x`, and `char`/`bool`/`f64`
/// referents.
#[test]
fn references_stored_into_aggregates_match_llvm() {
    require_match(
        "cells",
        &[("cells_array", CELLS_ARRAY), ("cells_shapes", CELLS_SHAPES)],
    );
}

/// The deref-STORE twin of the slice-element-part borrow
/// (`lower_scalar_memory_store_value`): `let r = &s[k].part;` where `r` is
/// itself stored into an aggregate (`[&r]`, `(&r, 5)`), so the stored-reference
/// cell pass gives `r` a home and the borrow is a store into it. Newtype,
/// array-field, `[.., x]`-tail and `u64` parts, and a closure capturing `r`.
#[test]
fn celled_slice_part_references_match_llvm() {
    require_match("cells_part", &[("cells_slice_part", CELLS_SLICE_PART)]);
}

/// `[&g]` of a `fn` pointer local: `cellable_address_referent` does not admit
/// a `fn` pointer referent, so `f` keeps "borrowed scalar reference used
/// without deref". Measured 2026-11-15: skipping the admission check compiles
/// this program (and agrees with LLVM), so this pin is what fails when the
/// check is removed. Admitting `fn` pointer referents is a new capability that
/// must update this pin. The refusal text is pinned on x86-64; AArch64 Linux
/// pins only "match or named refusal" (its other cell routes were not measured
/// on this program).
#[test]
fn fn_pointer_referent_keeps_its_refusal() {
    if skip() {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("fn_pointer_ref");
    for opt in OPT_LEVELS {
        let want = llvm(
            &dir,
            "pin_fn_pointer_reference",
            PIN_FN_POINTER_REFERENCE,
            opt,
        );
        match compile(
            &dir,
            Some(&dylib),
            "pin_fn_pointer_reference",
            PIN_FN_POINTER_REFERENCE,
            opt,
        ) {
            Outcome::Refused(stderr) => assert!(
                stderr.contains("[TCG-MIR-UNSUPPORTED]")
                    && (!cfg!(target_arch = "x86_64")
                        || stderr.contains("1f (reachable Rust-internal monomorphization")
                            && stderr.contains("borrowed scalar reference used without deref")),
                "-O{opt}: expected the named refusal of `f`: {stderr}"
            ),
            Outcome::Ran(got) => {
                assert!(
                    !cfg!(target_arch = "x86_64"),
                    "-O{opt}: the fn pointer referent compiled ({got:?}); pinned as refused"
                );
                assert_eq!(got, want, "-O{opt}: WRONG output");
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// `[&a, &b]` of two `Vec<u32>` locals: a slot-modelled collection is not a
/// cellable referent (`cellable_address_referent`). Match or named refusal.
#[test]
fn collection_references_in_aggregates_keep_their_route() {
    require_match_or_named_refusal("cells_vec", &[("pin_vec_reference", PIN_VEC_REFERENCE)]);
}

/// `MaybeUninit<S>::assume_init` for a 4-field and a padded struct, a generic
/// struct with an array field, `[u64; 3]`, `(u8, u64)`, an enum, and an array
/// of `MaybeUninit<P>` transmuted to `[P; 2]`.
#[test]
fn maybe_uninit_struct_transmutes_match_llvm() {
    require_match(
        "union",
        &[
            ("union_struct", UNION_STRUCT),
            ("union_shapes", UNION_SHAPES),
        ],
    );
}

/// `{:#010X}`, i128 hex, width/fill/sign, `{:w$}`, `{:.*}`, derived `Debug`
/// and `{:#?}`, positional and named arguments, `eprintln!`: shapes the
/// interception does not synthesize, lowered as the real `_print`.
#[test]
fn print_std_fallback_matches_llvm() {
    require_match("print", &[("print_shapes", PRINT_SHAPES)]);
}

/// `out[i] = LR { .. }` through `&mut [LR; 4]`, a padded struct with an
/// element-to-element copy, and an array field of a struct behind `&mut`.
#[test]
fn array_element_aggregate_stores_match_llvm() {
    require_match("element", &[("element_store", ELEMENT_STORE)]);
}

/// Compile a library crate to a host object through the bridge.
fn compile_lib_object(dir: &Path, dylib: &Path, src: &Path, opt: &str) -> std::process::Output {
    let mut backend = std::ffi::OsString::from("-Zcodegen-backend=");
    backend.push(dylib);
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "lib", "--emit", "obj", "--target", TARGET])
        .args(["-Cpanic=abort", "-Awarnings"])
        .arg(format!("-Copt-level={opt}"))
        .arg(backend)
        .arg("-Ztrust-ir-cg-args=no-proof-certs")
        .arg("-Ztrust-ir-cg-args=refine-solver=0")
        .arg("-o")
        .arg(dir.join(format!("lib_O{opt}.o")))
        .arg(src)
        .output()
        .expect("spawn rustc")
}

/// A coroutine whose upvar aggregate holds a borrow of a captured scalar is
/// NOT followed by the stored-reference cell pass (array, tuple and ADT
/// constructors only): `cap_coroutine` keeps "borrowed scalar reference used
/// without deref" on the host, as `tests/coroutine_generator_linux.rs`'s
/// `ay_gen_resume_args` does natively on AArch64 Linux. Following coroutine
/// aggregates compiled this crate at every level, unmeasured.
#[test]
fn coroutine_upvar_borrow_keeps_its_refusal() {
    if skip() {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("coroutine");
    let src =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/support/slice_parity/cap_coroutine.rs");
    for opt in OPT_LEVELS {
        let out = compile_lib_object(&dir, &dylib, &src, opt);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            !out.status.success(),
            "-O{opt}: the coroutine compiled; pinned as refused"
        );
        assert!(
            stderr.contains("cap_coroutine: borrowed scalar reference used without deref"),
            "-O{opt}: expected the named refusal of `cap_coroutine`: {stderr}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}
