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

// E2E (aarch64-apple-darwin): a REAL `#[thread_local]` static, read and written
// through the rustc bridge, links and runs with correct per-thread isolation.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS — THE TLS FRONTEND GAP, NOW CLOSED. The Darwin TLV BACKEND was
// already landed + verified through a HAND-AUTHORED trust-ir module (see
// `trust-cg-codegen/tests/e2e_aarch64_link.rs ::
// e2e_aarch64_thread_local_read_is_correct_and_per_thread`). This test pins the
// missing FRONTEND half: a REAL `.rs` `#[thread_local]` static compiled THROUGH
// THE BRIDGE. The bridge lowers MIR `Rvalue::ThreadLocalRef(def_id)` to an
// `Inst::GlobalAddr` of a `tls: Some(GeneralDynamic)` module global, which the
// adapter turns into `Opcode::TlsRef` -> the TLV descriptor access sequence
// (`select_tls_ref`, `TlsModel::Tlv`: ADRP/LdrTlvp -> LDR thunk -> BLR -> the
// variable's per-thread address). Before this, the bridge fail-closed every
// `Rvalue::ThreadLocalRef`, so NO real Rust thread-local could compile.
//
// CROSS-CRATE DESCRIPTOR MODEL. Compile the descriptor and its accessors as
// separate Rust crates, so this checks cross-object TLS linkage independently
// of how the compiler groups MonoItems into CGUs or combines their objects.
// The descriptor crate DEFINES one External `_X` plus `_X$tlv$init` template
// and `__tlv_bootstrap` import. The accessor crate IMPORTS `_X`; its TLVP
// relocations must resolve to that single canonical descriptor. A duplicate
// descriptor would fail linking or give the threads divergent storage.
//
// HOW CORRECTNESS IS OBSERVED. A C driver reads `X` in `main`, mutates `main`'s
// copy, spawns a worker thread that mutates the worker's OWN copy, joins, and
// re-reads `main`'s copy. Exit 0 iff (a) the initial read is `0xABCD`, (b) each
// thread's write is observed in its own copy, and (c) `main`'s copy is UNPERTURBED
// by the worker (true per-thread isolation). The binary RUNS under `timeout 10`;
// a botched TLV descriptor / BLR would hang or crash.
//
// PROOFS-OFF DIAGNOSTIC: the bridge compile passes the backend's
// `no-proof-certs` knob (`-Ztrust-ir-cg-args=no-proof-certs`; trustc refuses
// the former `TCG_NO_PROOF_CERTS=1` environment spelling). This lane pins
// semantics without claiming certification or exact-object binding. With
// certificates on, the original combined fixture was refused at proof promotion
// (`[TCG-PROOF-465]`,
// measured 2026-09-29 on Trust 9192: the frame's `StpPreIndex` is statistical
// sampling; the proof wall of ledger L07-P2).

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "aarch64-apple-darwin";

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_tls_a64_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// The descriptor and accessor crates jointly implement:
/// ```rust
/// #[thread_local] pub static mut X: i32 = 0xABCD;
/// extern "C" fn read_x()       -> i32 { X }            // TLS read
/// extern "C" fn bump_x(d: i32) -> i32 { X += d; X }    // TLS read-modify-write
/// ```
/// `read_x` exercises `Rvalue::ThreadLocalRef` + a deref load; `bump_x` adds a
/// deref STORE through the same TLV address (the write half of the access path).
const TLS_DESCRIPTOR_CRATE: &str = r#"
#![crate_type = "staticlib"]
#![feature(thread_local)]

#[no_mangle]
#[thread_local]
pub static mut X: i32 = 0xABCD;
"#;

const TLS_ACCESSOR_CRATE: &str = r#"
#![crate_type = "staticlib"]
#![feature(thread_local)]

unsafe extern "C" {
    #[thread_local]
    static mut X: i32;
}

#[no_mangle]
pub extern "C" fn read_x() -> i32 {
    unsafe { X }
}

#[no_mangle]
pub extern "C" fn bump_x(delta: i32) -> i32 {
    unsafe { X += delta; X }
}
"#;

/// C driver: reads `X` in `main`, mutates main's copy, spawns a worker that
/// mutates the WORKER's own copy, joins, and re-reads main's copy. Exit 0 iff the
/// value is correct AND per-thread isolated.
const DRIVER: &str = r#"
#include <stdio.h>
#include <pthread.h>

extern int read_x(void);
extern int bump_x(int);

static int worker_result;
static void *worker(void *arg) {
    (void)arg;
    bump_x(100);
    worker_result = bump_x(100); /* worker's OWN copy: 0xABCD + 200 = 44181 */
    return NULL;
}

int main(void) {
    int v0 = read_x();   /* init 0xABCD = 43981 */
    int vm = bump_x(1);  /* main's copy -> 43982 */
    pthread_t t;
    pthread_create(&t, NULL, worker, NULL);
    pthread_join(t, NULL);
    int vm2 = read_x();  /* main's copy must be unperturbed by the worker */
    printf("%d %d %d %d\n", v0, vm, worker_result, vm2);
    int ok = (v0 == 43981) && (vm == 43982) && (worker_result == 44181) && (vm2 == 43982);
    if (v0 != 43981) return 1;          /* wrong initial TLS read */
    if (vm != 43982) return 2;          /* main's TLS write not observed */
    if (worker_result != 44181) return 3; /* worker's TLS write not observed */
    if (vm2 != 43982) return 4;         /* main's copy perturbed == NOT isolated */
    return ok ? 0 : 5;
}
"#;

#[test]
fn thread_local_static_reads_writes_per_thread_isolated_aarch64() {
    // The backend knob option, Darwin rust-std and `cc` are required here; a
    // missing one fails the test by name instead of returning early.
    darwin_native::require("tls_thread_local_aarch64", &["cc"]);

    let dylib = ensure_dylib_built();
    let dir = workdir("x");

    // Compile both sides of the TLS import through the same bridge. Separate
    // output roots prevent a combined single-CGU object from hiding the ABI.
    let backend_arg = {
        let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
        s.push(&dylib);
        s
    };
    let mut all_objs = Vec::new();
    let mut stderr = String::new();
    for (crate_name, source) in [
        ("tls_descriptor", TLS_DESCRIPTOR_CRATE),
        ("tls_accessors", TLS_ACCESSOR_CRATE),
    ] {
        let out = dir.join(crate_name);
        std::fs::create_dir_all(&out).expect("create crate output directory");
        let src_path = out.join(format!("{crate_name}.rs"));
        std::fs::write(&src_path, source).expect("write source");
        let obj_out = out.join(crate_name);
        let output = toolchain_support::rustc_command()
            .args(["--crate-type", "staticlib", "--crate-name", crate_name])
            .arg(&backend_arg)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]))
            .args(["-Ccodegen-units=1"])
            // O1 keeps the TLS load/store MIR free of unrelated O0 alignment
            // debug assertions, as in the original single-crate fixture.
            .args(["--target", TARGET, "-Cpanic=abort", "-Copt-level=1"])
            .arg("--emit=obj")
            .arg("-o")
            .arg(&obj_out)
            .arg(&src_path)
            .output()
            .expect("failed to spawn trustc");
        let crate_stderr = String::from_utf8_lossy(&output.stderr);
        stderr.push_str(&format!("{crate_name}:\n{crate_stderr}\n"));
        assert!(
            output.status.success(),
            "bridge failed to compile {crate_name}. stderr: <<<{crate_stderr}>>>"
        );
        all_objs.extend(
            emitted_objects_support::emitted_objects(&obj_out).expect("read emitted objects"),
        );
    }
    all_objs.sort();
    all_objs.dedup();
    assert!(
        !all_objs.is_empty(),
        "bridge produced no object file. stderr: <<<{stderr}>>>"
    );

    // Link only the program-REACHABLE closure, selected by DEFINED symbol (never
    // by filename): the exported `read_x`/`bump_x` entry points and the canonical
    // `_X` thread-local descriptor object. The accessor objects reference `_X` as
    // an UNDEFINED external import; the descriptor object defines it.
    let nm = |obj: &Path| -> String {
        String::from_utf8_lossy(&Command::new("nm").arg(obj).output().expect("nm").stdout)
            .into_owned()
    };
    let defines_reachable = |obj: &Path| -> bool {
        nm(obj).lines().any(|l| {
            let mut it = l.split_whitespace();
            let kind = it.nth(1); // address, KIND, name
            let name = it.next();
            kind.map(|k| k != "U").unwrap_or(false)
                && name
                    .map(|n| n == "_read_x" || n == "_bump_x" || n == "_X")
                    .unwrap_or(false)
        })
    };
    let objs: Vec<PathBuf> = all_objs
        .iter()
        .filter(|o| defines_reachable(o))
        .cloned()
        .collect();

    // Structural soundness: `_X` is DEFINED in EXACTLY ONE object (the canonical
    // descriptor), and the accessor objects reference it as an UNDEFINED import.
    // A duplicate descriptor would be a link-time duplicate-symbol error (and a
    // divergent-storage miscompile); an absent one would be an unresolved symbol.
    let defines_x = |obj: &Path| -> bool {
        nm(obj).lines().any(|l| {
            let mut it = l.split_whitespace();
            let kind = it.nth(1);
            let name = it.next();
            kind.map(|k| k != "U").unwrap_or(false) && name == Some("_X")
        })
    };
    let imports_x = |obj: &Path| -> bool {
        nm(obj).lines().any(|l| {
            let mut it = l.split_whitespace();
            // An undefined symbol prints as `U <name>` (no address column).
            it.next() == Some("U") && it.next() == Some("_X")
        })
    };
    let definers: Vec<&PathBuf> = objs.iter().filter(|o| defines_x(o)).collect();
    assert_eq!(
        definers.len(),
        1,
        "the thread-local descriptor `_X` must be DEFINED in exactly one object \
         (the canonical descriptor); found {} definers among {objs:?}",
        definers.len()
    );
    let descriptor_obj = definers[0];
    // The descriptor object must carry the full Darwin TLV shape.
    let desc_nm = nm(descriptor_obj);
    assert!(
        desc_nm.contains("_X$tlv$init"),
        "descriptor object missing the `_X$tlv$init` template symbol:\n{desc_nm}"
    );
    assert!(
        desc_nm.contains("__tlv_bootstrap"),
        "descriptor object missing the `__tlv_bootstrap` dyld import:\n{desc_nm}"
    );
    // Each accessor object imports `_X` (undefined external), never re-defines it.
    let accessors: Vec<&PathBuf> = objs
        .iter()
        .filter(|o| {
            let s = nm(o);
            s.contains("_read_x") || s.contains("_bump_x")
        })
        .collect();
    assert!(
        !accessors.is_empty(),
        "did not find the read_x/bump_x accessor objects among {objs:?}"
    );
    for acc in &accessors {
        assert!(
            imports_x(acc) && !defines_x(acc),
            "accessor object {acc:?} must IMPORT `_X` (undefined external) and not \
             define it:\n{}",
            nm(acc)
        );
    }

    // 2. Link the reachable objects with the C driver.
    let driver_path = dir.join("driver.c");
    std::fs::write(&driver_path, DRIVER).expect("write driver.c");
    let bin = dir.join("bin");
    let mut link = Command::new("cc");
    link.arg("-o").arg(&bin).arg(&driver_path);
    for o in &objs {
        link.arg(o);
    }
    let link = link.output().expect("cc link");
    assert!(
        link.status.success(),
        "link failed (the TLVP `_X` import must resolve to the single canonical \
         descriptor). stderr: <<<{}>>>",
        String::from_utf8_lossy(&link.stderr)
    );

    // 3. RUN natively on aarch64 under an in-process watchdog: exit 0 iff the TLS
    //    reads/writes are correct AND per-thread isolated.
    //
    //    RETRY-ON-WATCHDOG-KILL: a freshly `cc`-linked Mach-O carrying a
    //    Darwin TLV descriptor can stall in dyld's first-execution `__tlv_bootstrap`
    //    processing under heavy concurrent system load (e.g. parallel `rustc`
    //    compiles), tripping the watchdog BEFORE `main` runs (observed: empty
    //    stdout on the kill; the very same flake hits the hand-authored backend
    //    oracle `e2e_aarch64_thread_local_read_is_correct_and_per_thread`, so it is
    //    a PRE-EXISTING dyld/TLV-under-load artifact, NOT a property of the bridge
    //    lowering). A run that reaches `main` is value-correct EVERY time (<0.2s),
    //    so a short per-attempt watchdog plus generous retries rides out a stall
    //    without ever masking an error: a WRONG value fails the value assertions
    //    below, and a genuine in-code deadlock would be killed on every attempt and
    //    still fail. Only the environmental cold-start stall is tolerated.
    let run_once = || {
        darwin_native::run_with_deadline(&mut Command::new(&bin), std::time::Duration::from_secs(6))
    };
    let mut run = run_once();
    for _ in 0..30 {
        if run.is_ok() {
            break;
        }
        // Small backoff so a load spike has time to ease between attempts.
        std::thread::sleep(std::time::Duration::from_millis(200));
        run = run_once();
    }
    let run = run.unwrap_or_else(|killed| {
        panic!(
            "tls driver was killed at the 6 s deadline on all 31 attempts, more than \
             the cold-start stall the retries tolerate. stdout: {:?} stderr: {:?}",
            String::from_utf8_lossy(&killed.stdout),
            String::from_utf8_lossy(&killed.stderr)
        )
    });
    let stdout = String::from_utf8_lossy(&run.stdout);
    let code = run.status.code().expect("process terminated by signal");
    assert_eq!(
        code, 0,
        "tls driver returned {code} (1=wrong initial read, 2=main write lost, \
         3=worker write lost, 4=main copy PERTURBED == not per-thread isolated). \
         stdout: {stdout:?}"
    );
    assert_eq!(
        stdout.trim(),
        "43981 43982 44181 43982",
        "expected correct + per-thread-isolated TLS reads/writes"
    );

    let _ = std::fs::remove_dir_all(&dir);
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

// Linux ELF twin: `tls_thread_local_linux.rs` combines the descriptor and accessor
// definitions in one crate and runs
// this `DRIVER` for aarch64-unknown-linux-gnu; keep the two byte-identical.
