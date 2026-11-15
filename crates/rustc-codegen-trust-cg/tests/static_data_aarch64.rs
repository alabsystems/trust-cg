// Compiled only on an aarch64-apple-darwin host: another host builds this
// target with no test in it, never one that passes without running (L06-P10).
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/emitted_objects.rs"]
mod emitted_objects_support;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// E2E (aarch64-apple-darwin): a `MonoItem::Static` lowered to its own object.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// This pins the plain-data `MonoItem::Static` cases end-to-end on aarch64. The
// immutable lane checks exact scalar / byte-array initializer bytes in exported
// read-only globals. The mutable lane checks that one canonical writable global
// is shared by Rust reader/writer objects and a C driver. Together they cover
// definition, import, section writability, relocation, linkage, and run-time
// state identity (without the static arm, the symbols are undefined at link).
//
// PROOF LANES, measured 2026-09-29 on Trust 9192. The immutable-statics crate
// holds three data statics and the `#[panic_handler]` a `no_std` staticlib
// needs. Its bridge compile runs with proof certificates ON (the default lane):
// the statics are emitted and the compile exits 0, but the panic handler
// (`rust_begin_unwind`) is refused at proof promotion (`[TCG-PROOF-465]`,
// uncovered opcode `B`) and left out as an unreachable Rust-internal function.
// Nothing reaches it (the C driver reads data only), so the link and run are
// unaffected; the test fails if any other function is left out or refused.
// The bridge runner cannot see that diagnostic, because the test does not
// echo rustc's output on success. The mutable-static and over-aligned crates
// hold code, and with certificates on they are refused at proof promotion
// (`[TCG-PROOF-465]`: instruction-derived obligations without a checked
// certificate and registry name lookups; the proof wall of ledger L07-P2). Those
// two tests and the extern-static linkage test are PROOFS-OFF DIAGNOSTICS:
// their bridge compiles pass the backend's
// `no-proof-certs` knob (`-Ztrust-ir-cg-args=no-proof-certs`; trustc refuses the
// former `TCG_NO_PROOF_CERTS=1` environment spelling), so a pass pins runtime
// semantics only and claims no certification or exact-object binding.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "aarch64-apple-darwin";

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_sd_a64_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// The static-only crate: immutable, plain scalar / byte-array statics with NO
/// internal pointers — the simplest sound `MonoItem::Static` shape the bridge
/// admits. `#[no_mangle]` so the C driver can name the symbols directly.
const STATIC_CRATE: &str = "\
#![no_std]\n\
#![no_main]\n\
#[no_mangle]\npub static AY_STATIC_N: u32 = 0xDEAD_BEEF;\n\
#[no_mangle]\npub static AY_STATIC_BYTES: [u8; 4] = [0x42, 0x43, 0x00, 0x44];\n\
#[no_mangle]\npub static AY_STATIC_W: u64 = 0x0102_0304_0506_0708;\n\
#[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! { loop {} }\n";

/// C driver: reads each static through its `extern` symbol and returns 0 only if
/// every byte matches. A wrong byte / layout / section silently miscompiles the
/// read, surfacing as a nonzero exit.
const DRIVER_C: &str = "\
#include <stdint.h>\n\
extern const uint32_t AY_STATIC_N;\n\
extern const uint8_t  AY_STATIC_BYTES[4];\n\
extern const uint64_t AY_STATIC_W;\n\
int main(void){\n\
    if (AY_STATIC_N != 0xDEADBEEFu) return 1;\n\
    if (AY_STATIC_BYTES[0] != 0x42) return 2;\n\
    if (AY_STATIC_BYTES[1] != 0x43) return 3;\n\
    if (AY_STATIC_BYTES[2] != 0x00) return 4;\n\
    if (AY_STATIC_BYTES[3] != 0x44) return 5;\n\
    if (AY_STATIC_W != 0x0102030405060708ull) return 6;\n\
    return 0;\n\
}\n";

#[test]
fn immutable_statics_emit_correct_bytes_and_link_runs_aarch64() {
    // Darwin rust-std and `cc` are required here; a missing one fails the test
    // by name instead of returning early.
    darwin_native::require("static_data_aarch64", &["cc"]);

    let dylib = ensure_dylib_built();
    let dir = workdir("immutable");

    // 1. Compile the static-only crate THROUGH THE BRIDGE to an object.
    let src_path = dir.join("statics.rs");
    std::fs::write(&src_path, STATIC_CRATE).expect("write source");
    let backend_arg = {
        let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
        s.push(&dylib);
        s
    };
    let obj_out = dir.join("statics");
    // Proof certificates stay ON: only the panic handler is refused, and it is
    // left out (see PROOF LANES).
    let output = toolchain_support::rustc_command()
        .args(["--crate-type", "staticlib"])
        .arg(&backend_arg)
        .args(["--target", TARGET, "-Cpanic=abort", "-Copt-level=0"])
        .arg("--emit=obj")
        .arg("-o")
        .arg(&obj_out)
        .arg(&src_path)
        .output()
        .expect("failed to spawn trustc");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "bridge failed to compile the static-only crate. stderr: <<<{stderr}>>>"
    );
    // With certificates on, the backend still exits 0 when it leaves out a
    // Rust-internal function it cannot promote, because nothing in the program
    // may reach it (see PROOF LANES). Only the panic handler may be left out.
    const SKIPPED: &str = "rustc_codegen_trust_cg: skipped Rust-internal function with unsupported \
                           MIR (not an external root; must be unreachable from the program for the \
                           link to succeed): ";
    for line in stderr.lines().filter(|line| {
        line.contains("skipped Rust-internal function") || line.contains("TCG-PROOF-465")
    }) {
        let symbol = line
            .strip_prefix(SKIPPED)
            .and_then(|rest| rest.split(": ").next())
            .unwrap_or("");
        assert!(
            symbol.ends_with("rust_begin_unwind"),
            "the certificates-on compile of the static-only crate left out or refused something \
             other than its panic handler (`rust_begin_unwind`): <<<{line}>>>\n\
             stderr: <<<{stderr}>>>"
        );
    }

    // rustc places each `static` in its own CGU, so the bridge emits one object
    // PER static. Collect them ALL — the static symbols are spread across them.
    let objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    assert!(
        !objs.is_empty(),
        "bridge produced no object file. stderr: <<<{stderr}>>>"
    );

    // Each static symbol must be DEFINED (as a GLOBAL symbol) in some object —
    // the whole point of the `MonoItem::Static` arm. `nm` prints a defined data
    // symbol with an uppercase section letter (e.g. `S`); a `U` is undefined and
    // a lowercase letter is local (not exported), neither of which links from a C
    // driver.
    let nm_all: String = objs
        .iter()
        .map(|o| {
            String::from_utf8_lossy(&Command::new("nm").arg(o).output().expect("nm").stdout)
                .into_owned()
        })
        .collect();
    for sym in ["_AY_STATIC_N", "_AY_STATIC_BYTES", "_AY_STATIC_W"] {
        assert!(
            nm_all.lines().any(|l| {
                let mut it = l.split_whitespace();
                let kind = it.nth(1);
                let name = it.next();
                // Exported defined symbol: a non-`U`, UPPERCASE section letter.
                name == Some(sym)
                    && kind
                        .map(|k| k != "U" && k.chars().all(|c| c.is_ascii_uppercase()))
                        .unwrap_or(false)
            }),
            "static symbol {sym} is not DEFINED+EXPORTED in any bridge object.\nnm:\n{nm_all}"
        );
    }

    // 2. Link ALL bridge objects with a C driver that reads the statics.
    let driver_path = dir.join("driver.c");
    std::fs::write(&driver_path, DRIVER_C).expect("write driver.c");
    let bin = dir.join("bin");
    let mut link = Command::new("cc");
    link.arg("-o").arg(&bin).arg(&driver_path);
    for o in &objs {
        link.arg(o);
    }
    link.arg(toolchain_support::write_abort_stubs(&dir, &objs));
    let link = link.output().expect("cc link");
    assert!(
        link.status.success(),
        "link failed (the static symbols must be defined+exported). stderr: <<<{}>>>",
        String::from_utf8_lossy(&link.stderr)
    );

    // 3. RUN: exit 0 iff every static byte read back correctly.
    let run = Command::new(&bin).output().expect("run linked binary");
    let code = run.status.code().expect("process terminated by signal");
    assert_eq!(
        code, 0,
        "static-read driver returned {code} (nonzero == a wrong byte/layout/section for some \
         static; exit code identifies which check failed)"
    );

    let _ = std::fs::remove_dir_all(&dir);
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::On,
    );
}

/// A mutable static is one canonical writable global. Its defining object owns
/// the initialized bytes; Rust functions in other objects import that symbol;
/// and foreign code can read and write the same storage. Exercising both
/// directions catches a read-only-section mistake, a per-object copy, a missing
/// undefined-external relocation, or a non-exported definition.
#[test]
fn mutable_static_is_shared_writable_and_link_runs_aarch64() {
    // The backend knob option, Darwin rust-std and `cc` are required here; a
    // missing one fails the test by name instead of returning early.
    darwin_native::require("static_data_aarch64", &["cc"]);
    let dylib = ensure_dylib_built();
    let dir = workdir("mutable");
    let src = "\
#![no_std]\n#![no_main]\n\
#[no_mangle]\npub static mut AY_STATIC_MUT: u32 = 7;\n\
#[no_mangle]\npub unsafe extern \"C\" fn ay_static_get() -> u32 { AY_STATIC_MUT }\n\
#[no_mangle]\npub unsafe extern \"C\" fn ay_static_set(value: u32) { AY_STATIC_MUT = value; }\n\
#[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! { loop {} }\n";
    let src_path = dir.join("mut.rs");
    std::fs::write(&src_path, src).expect("write source");
    let backend_arg = {
        let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
        s.push(&dylib);
        s
    };
    let obj_out = dir.join("mut");
    let output = toolchain_support::rustc_command()
        .args(["--crate-type", "staticlib"])
        .arg(&backend_arg)
        .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]))
        .args(["--target", TARGET, "-Cpanic=abort", "-Copt-level=0"])
        .arg("--emit=obj")
        .arg("-o")
        .arg(&obj_out)
        .arg(&src_path)
        .output()
        .expect("failed to spawn trustc");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "bridge failed to compile the mutable-static crate. stderr: <<<{stderr}>>>"
    );

    let objs = emitted_objects_support::emitted_objects(&obj_out).expect("read emitted objects");
    assert!(
        !objs.is_empty(),
        "bridge produced no object file. stderr: <<<{stderr}>>>"
    );

    let nm_all: String = objs
        .iter()
        .map(|o| {
            String::from_utf8_lossy(&Command::new("nm").arg(o).output().expect("nm").stdout)
                .into_owned()
        })
        .collect();
    let definitions = nm_all
        .lines()
        .filter(|line| {
            let mut fields = line.split_whitespace();
            let kind = fields.nth(1);
            let name = fields.next();
            name == Some("_AY_STATIC_MUT")
                && kind
                    .map(|kind| kind != "U" && kind.chars().all(|c| c.is_ascii_uppercase()))
                    .unwrap_or(false)
        })
        .count();
    assert_eq!(
        definitions, 1,
        "mutable static must have exactly one exported definition. nm:\n{nm_all}"
    );

    let driver = "\
#include <stdint.h>\n\
extern uint32_t AY_STATIC_MUT;\n\
extern uint32_t ay_static_get(void);\n\
extern void ay_static_set(uint32_t);\n\
int main(void) {\n\
    if (AY_STATIC_MUT != 7u) return 1;\n\
    if (ay_static_get() != 7u) return 2;\n\
    AY_STATIC_MUT = 19u;\n\
    if (ay_static_get() != 19u) return 3;\n\
    ay_static_set(42u);\n\
    if (AY_STATIC_MUT != 42u) return 4;\n\
    return 0;\n\
}\n";
    let driver_path = dir.join("driver.c");
    std::fs::write(&driver_path, driver).expect("write driver.c");
    let bin = dir.join("bin");
    let mut link = Command::new("cc");
    link.arg("-o").arg(&bin).arg(&driver_path);
    for obj in &objs {
        link.arg(obj);
    }
    link.arg(toolchain_support::write_abort_stubs(&dir, &objs));
    let link = link.output().expect("cc link");
    assert!(
        link.status.success(),
        "link failed (mutable definition/imports must resolve once). stderr: <<<{}>>>",
        String::from_utf8_lossy(&link.stderr)
    );

    let run = Command::new(&bin).output().expect("run linked binary");
    let code = run.status.code().expect("process terminated by signal");
    assert_eq!(
        code, 0,
        "mutable-static driver returned {code}; the exit code identifies which shared-state \
         observation failed"
    );

    let _ = std::fs::remove_dir_all(&dir);
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// OVER-ALIGNED statics: a `static` whose type demands MORE than 8-byte alignment
/// lands at an address that honors it, and an alignment-FAULTING access through
/// it runs.
///
/// Until 2026-09-27 the bridge refused every such static ("static requires
/// 16-byte alignment, which exceeds the 8-byte data-section alignment of this
/// slice") — `static X: u128` (align 16 on AArch64) and alloc's
/// `STATIC_INNER_SLICE` (`#[repr(C, align(16))]`) could not compile. The object
/// writers had honored per-global alignment for a long time; the refusal was
/// stale. Lifting it is only right if the alignment really reaches the object,
/// and that is what this test pins, in three shapes: a WRITABLE `u128` (the
/// `__DATA,__data` writer), a READ-ONLY `#[repr(align(64))]` struct and a
/// read-only `u128` (the `__TEXT,__const` writer), and the NESTED allocation
/// behind a pointer-bearing `static REF: &u128` (the owner's module, emitted by
/// `emit_static_nested_alloc_global`).
///
/// THE ALIGNMENT-SENSITIVE ACCESS is the C driver's `__atomic_fetch_add` on the
/// `unsigned __int128`: clang lowers it to a 16-byte compare-and-swap
/// (`caspal`, or an `ldaxp`/`stlxp` loop), which AArch64 requires to be
/// 16-byte aligned and FAULTS on otherwise (measured: SIGBUS on an 8-mod-16
/// address). An under-aligned `AY_WIDE` therefore does not print a wrong
/// number — it kills the process, which `status.code()` turns into a hard test
/// failure. Every static's address is ALSO checked against its own alignment,
/// which is what catches an under-aligned read-only static (no faulting access
/// is legal on read-only memory). Measured with the definition's alignment
/// capped at 8 (the mutation this test exists for): exit 10; with every
/// address check deleted from the driver, the same objects die on SIGBUS
/// (exit 138) at the `caspal`.
///
/// LLVM IS THE ORACLE: the same crate compiled by LLVM, linked with the same
/// driver, must exit 0 first, or this test is measuring something else. Both
/// sides are compiled with `-Cdebug-assertions=off`: the null-pointer UB check
/// LLVM inserts at `-O0` calls into `core`, which a bare `cc` link of the crate's
/// own objects cannot resolve.
#[test]
fn over_aligned_statics_land_aligned_and_survive_a_16_byte_atomic_aarch64() {
    // The backend knob option, Darwin rust-std and `cc` are required here; a
    // missing one fails the test by name instead of returning early.
    darwin_native::require("static_data_aarch64", &["cc"]);
    // Object files are linked in SORTED name order, and the bridge names each
    // static's object after its symbol, so `AY_WIDE_A`, `AY_WIDE_B`,
    // `AY_WIDE_C` are consecutive in `__DATA,__data`. Under ANY writer that caps
    // their alignment at 8, `A` and `C` sit 24 bytes apart — one of them is
    // 8-mod-16 whatever the section base is. `AY_REFS` does the same for NESTED
    // allocations: `a` (16 bytes), `b` (8), `c` (16) are emitted into one section
    // in field order, so an 8-cap puts `a` and `c` 24 bytes apart too.
    const SRC: &str = "\
#![no_std]\n#![no_main]\n\
#[no_mangle]\npub static mut AY_PAD_A: u64 = 0x0A;\n\
#[no_mangle]\npub static mut AY_PAD_B: u64 = 0x0B;\n\
#[no_mangle]\npub static mut AY_WIDE_A: u128 = 0x1111_2222_3333_4444_5555_6666_7777_8888;\n\
#[no_mangle]\npub static mut AY_WIDE_B: u64 = 0x0D;\n\
#[no_mangle]\npub static mut AY_WIDE_C: u128 = 0x9999_aaaa_bbbb_cccc_dddd_eeee_ffff_0000;\n\
#[repr(C, align(64))]\npub struct Line { pub a: u64, pub b: u64, pub c: u8 }\n\
#[no_mangle]\npub static AY_LINE: Line = Line { a: 7, b: 9, c: 1 };\n\
#[no_mangle]\npub static AY_PAD_C: u64 = 0x0C;\n\
#[no_mangle]\npub static AY_BIG: u128 = 0x0123_4567_89ab_cdef_fedc_ba98_7654_3210;\n\
#[repr(C)]\npub struct Refs { pub a: &'static u128, pub b: &'static u64, pub c: &'static u128 }\n\
#[no_mangle]\npub static AY_REFS: Refs = Refs {\n\
    a: &0x0f0f_0f0f_0f0f_0f0f_f0f0_f0f0_f0f0_f0f1,\n\
    b: &0x77,\n\
    c: &0x1234_5678_9abc_def0_0fed_cba9_8765_4321,\n\
};\n\
#[no_mangle]\npub unsafe extern \"C\" fn ay_wide_lo() -> u64 { AY_WIDE_A as u64 ^ AY_WIDE_C as u64 }\n\
#[no_mangle]\npub unsafe extern \"C\" fn ay_wide_addr() -> usize { core::ptr::addr_of!(AY_WIDE_A) as usize }\n\
#[no_mangle]\npub extern \"C\" fn ay_refs_lo() -> u64 { (*AY_REFS.a as u64) ^ (*AY_REFS.c as u64) ^ *AY_REFS.b }\n\
#[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! { loop {} }\n";
    const DRIVER: &str = "\
#include <stdint.h>\n\
typedef unsigned __int128 u128;\n\
struct Line { uint64_t a, b; uint8_t c; } __attribute__((aligned(64)));\n\
struct Refs { const u128 *a; const uint64_t *b; const u128 *c; };\n\
extern uint64_t AY_PAD_A, AY_PAD_B, AY_WIDE_B;\n\
extern const uint64_t AY_PAD_C;\n\
extern u128 AY_WIDE_A, AY_WIDE_C;\n\
extern const struct Line AY_LINE;\n\
extern const u128 AY_BIG;\n\
extern const struct Refs AY_REFS;\n\
extern uint64_t ay_wide_lo(void);\n\
extern uintptr_t ay_wide_addr(void);\n\
extern uint64_t ay_refs_lo(void);\n\
static u128 w(uint64_t hi, uint64_t lo) { return ((u128)hi << 64) | lo; }\n\
int main(void) {\n\
    if ((uintptr_t)&AY_WIDE_A % 16) return 10;\n\
    if ((uintptr_t)&AY_WIDE_C % 16) return 11;\n\
    if ((uintptr_t)&AY_LINE % 64) return 12;\n\
    if ((uintptr_t)&AY_BIG % 16) return 13;\n\
    if ((uintptr_t)AY_REFS.a % 16) return 14;\n\
    if ((uintptr_t)AY_REFS.c % 16) return 15;\n\
    if (ay_wide_addr() != (uintptr_t)&AY_WIDE_A) return 16;\n\
    u128 old_a = __atomic_fetch_add(&AY_WIDE_A, 1, __ATOMIC_SEQ_CST);\n\
    u128 old_c = __atomic_fetch_add(&AY_WIDE_C, 2, __ATOMIC_SEQ_CST);\n\
    if (old_a != w(0x1111222233334444ull, 0x5555666677778888ull)) return 20;\n\
    if (old_c != w(0x9999aaaabbbbccccull, 0xddddeeeeffff0000ull)) return 21;\n\
    if (ay_wide_lo() != (0x5555666677778889ull ^ 0xddddeeeeffff0002ull)) return 22;\n\
    if (AY_LINE.a != 7 || AY_LINE.b != 9 || AY_LINE.c != 1) return 30;\n\
    if (AY_BIG != w(0x0123456789abcdefull, 0xfedcba9876543210ull)) return 31;\n\
    if (*AY_REFS.a != w(0x0f0f0f0f0f0f0f0full, 0xf0f0f0f0f0f0f0f1ull)) return 32;\n\
    if (*AY_REFS.b != 0x77 || *AY_REFS.c != w(0x123456789abcdef0ull, 0x0fedcba987654321ull)) return 33;\n\
    if (ay_refs_lo() != (0xf0f0f0f0f0f0f0f1ull ^ 0x0fedcba987654321ull ^ 0x77)) return 34;\n\
    if (AY_PAD_A != 0x0A || AY_PAD_B != 0x0B || AY_PAD_C != 0x0C || AY_WIDE_B != 0x0D) return 40;\n\
    return 0;\n\
}\n";

    let dylib = ensure_dylib_built();
    let dir = workdir("overaligned");
    let src_path = dir.join("overaligned.rs");
    std::fs::write(&src_path, SRC).expect("write source");
    let driver_path = dir.join("driver.c");
    std::fs::write(&driver_path, DRIVER).expect("write driver.c");

    // Compile SRC to objects in `out` (bridge when `backend` is Some), link them
    // with the driver in a DETERMINISTIC (sorted) object order, run, and return
    // the exit code. A signal (the SIGBUS of a misaligned 16-byte atomic) panics.
    let build_and_run = |label: &str, backend: Option<&Path>| -> i32 {
        let out = dir.join(label);
        std::fs::create_dir_all(&out).expect("create output dir");
        let obj_out = out.join("overaligned.o");
        let mut cmd = toolchain_support::rustc_command();
        cmd.args(["--crate-type", "staticlib"]);
        if let Some(dylib) = backend {
            let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
            backend_arg.push(dylib);
            cmd.arg(backend_arg)
                .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
        } else {
            cmd.arg("-Ccodegen-units=1");
        }
        cmd.args(["--target", TARGET, "-Cpanic=abort", "-Copt-level=0"])
            .arg("-Cdebug-assertions=off")
            .arg("--emit=obj")
            .arg("-o")
            .arg(&obj_out)
            .arg(&src_path);
        let output = cmd.output().expect("spawn rustc");
        assert!(
            output.status.success(),
            "{label}: failed to compile the over-aligned-statics crate. A refusal naming \
             `static requires 16-byte alignment` is the stale limit this test pins as \
             lifted. stderr: <<<{}>>>",
            String::from_utf8_lossy(&output.stderr)
        );
        let objs =
            emitted_objects_support::emitted_objects(&obj_out).expect("read emitted objects");
        assert!(!objs.is_empty(), "{label}: no object produced");
        let bin = out.join("bin");
        let mut link = Command::new("cc");
        link.arg("-o").arg(&bin).arg(&driver_path);
        for o in &objs {
            link.arg(o);
        }
        link.arg(toolchain_support::write_abort_stubs(&out, &objs));
        let link = link.output().expect("cc link");
        assert!(
            link.status.success(),
            "{label}: link failed. stderr: <<<{}>>>",
            String::from_utf8_lossy(&link.stderr)
        );
        let run = Command::new(&bin).output().expect("run linked binary");
        run.status.code().unwrap_or_else(|| {
            panic!(
                "{label}: the driver was KILLED BY A SIGNAL ({:?}) — the signature of a \
                 16-byte `caspal` on an under-aligned `AY_WIDE` (SIGBUS)",
                run.status
            )
        })
    };

    let oracle = build_and_run("llvm", None);
    assert_eq!(
        oracle, 0,
        "the LLVM ORACLE returned {oracle}; this test is measuring something else"
    );
    let bridge = build_and_run("bridge", Some(&dylib));
    assert_eq!(
        bridge, 0,
        "the bridge-compiled statics returned {bridge} where LLVM returned 0. 10..=15: a \
         static is NOT at an address its own alignment requires (10/11 `AY_WIDE_A`/`_C` %16, \
         12 `AY_LINE` %64, 13 `AY_BIG` %16, 14/15 the NESTED allocations behind \
         `AY_REFS.a`/`.c` %16); 16/22: the Rust reader and the definition disagree about \
         the storage; 20/21/30..=34: wrong bytes; 40: a padding static"
    );
    let _ = std::fs::remove_dir_all(&dir);
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// A pointer-bearing static whose relocations name `extern` statics, directly
/// and through a nested memory allocation, beside a `fn(..)` pointer to a
/// non-capturing closure. The static's object splices each extern static's
/// symbol (an undefined external the C driver defines) and never evaluates a
/// foreign item's initializer, which has none; the closure slot names the
/// module-local fn-pointer entry with the pointer's untupled signature, so the
/// call through the loaded pointer receives its two arguments. The pair is read
/// through an array pattern: a native `panic=abort` bounds check is refused
/// (`[TCG-ASSERT-PANIC]`).
#[test]
fn statics_pointing_at_extern_statics_link_and_run_aarch64() {
    // The backend knob option, Darwin rust-std and `cc` are required here; a
    // missing one fails the test by name instead of returning early.
    darwin_native::require("static_data_aarch64", &["cc"]);
    let dylib = ensure_dylib_built();
    let src = "\
#![no_std]\n#![no_main]\n\
extern \"C\" { static AY_EXT_ONE: u32; static AY_EXT_TWO: u32; }\n\
pub struct P(*const u32);\nunsafe impl Sync for P {}\n\
static PTR: P = P(&raw const AY_EXT_ONE);\n\
static PAIR: &[P; 2] = &[P(&raw const AY_EXT_ONE), P(&raw const AY_EXT_TWO)];\n\
pub struct Mix(*const u32, fn(u32, u32) -> u32);\nunsafe impl Sync for Mix {}\n\
static MIX: &Mix = &Mix(&raw const AY_EXT_TWO, |a, b| a ^ b);\n\
#[no_mangle]\npub extern \"C\" fn ay_ext_direct() -> u32 { unsafe { *core::hint::black_box(&PTR).0 } }\n\
#[no_mangle]\npub extern \"C\" fn ay_ext_nested() -> u32 {\n\
    let [first, second] = core::hint::black_box(PAIR);\n\
    unsafe { (*first.0).wrapping_mul(3).wrapping_add(*second.0) }\n\
}\n\
#[no_mangle]\npub extern \"C\" fn ay_ext_mix(a: u32) -> u32 {\n\
    let m = core::hint::black_box(MIX);\n\
    unsafe { (m.1)(*m.0, a) }\n\
}\n\
#[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! { loop {} }\n";
    let driver = "\
#include <stdint.h>\n\
uint32_t AY_EXT_ONE = 0x1234u;\n\
uint32_t AY_EXT_TWO = 0xABCDu;\n\
extern uint32_t ay_ext_direct(void);\n\
extern uint32_t ay_ext_nested(void);\n\
extern uint32_t ay_ext_mix(uint32_t);\n\
int main(void) {\n\
    if (ay_ext_direct() != 0x1234u) return 1;\n\
    if (ay_ext_nested() != 0x1234u * 3u + 0xABCDu) return 2;\n\
    if (ay_ext_mix(0xFFu) != (0xABCDu ^ 0xFFu)) return 3;\n\
    AY_EXT_TWO = 7u;\n\
    if (ay_ext_mix(5u) != (7u ^ 5u)) return 4;\n\
    return 0;\n\
}\n";
    for opt in ["0", "2"] {
        let dir = workdir(&format!("extern_o{opt}"));
        let src_path = dir.join("ext.rs");
        std::fs::write(&src_path, src).expect("write source");
        let backend_arg = {
            let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
            s.push(&dylib);
            s
        };
        let obj_out = dir.join("ext");
        let output = toolchain_support::rustc_command()
            .args(["--crate-type", "staticlib"])
            .arg(&backend_arg)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]))
            .args(["--target", TARGET, "-Cpanic=abort"])
            // As the other tests here: the `-O0` null-pointer UB check calls
            // into `core`, which this bare `cc` link of the crate's own
            // objects cannot resolve.
            .arg("-Cdebug-assertions=off")
            .arg(format!("-Copt-level={opt}"))
            .arg("--emit=obj")
            .arg("-o")
            .arg(&obj_out)
            .arg(&src_path)
            .output()
            .expect("failed to spawn rustc via rustup");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success(),
            "bridge failed to compile statics pointing at extern statics at -Copt-level={opt}. \
             stderr: <<<{stderr}>>>"
        );
        let objs =
            emitted_objects_support::emitted_objects(&obj_out).expect("read emitted objects");
        assert!(
            !objs.is_empty(),
            "bridge produced no object file. stderr: <<<{stderr}>>>"
        );
        let driver_path = dir.join("driver.c");
        std::fs::write(&driver_path, driver).expect("write driver.c");
        let bin = dir.join("bin");
        let mut link = Command::new("cc");
        link.arg("-o").arg(&bin).arg(&driver_path);
        for obj in &objs {
            link.arg(obj);
        }
        let link = link.output().expect("cc link");
        assert!(
            link.status.success(),
            "link failed at -Copt-level={opt} (each extern static must be an undefined external \
             the driver defines). stderr: <<<{}>>>",
            String::from_utf8_lossy(&link.stderr)
        );
        let run = Command::new(&bin).output().expect("run linked binary");
        let code = run.status.code().expect("process terminated by signal");
        assert_eq!(
            code, 0,
            "extern-static driver returned {code} at -Copt-level={opt}; the exit code identifies \
             which read or closure call through a static failed"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }
    eprintln!("EXTERN_STATIC_LINK rows=2 matched=2 opts=0,2");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

// Linux ELF twin: `static_data_linux.rs` compiles these four crates and runs
// these drivers for aarch64-unknown-linux-gnu; keep the two byte-identical.
