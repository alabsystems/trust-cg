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
// CROSS-OBJECT DESCRIPTOR MODEL. The bridge emits one object per `MonoItem`, so
// the `#[thread_local] static X` (its `MonoItem::Static`) and the functions that
// access it land in SEPARATE objects. A `#[thread_local]` has ONE program-wide
// `tlv_descriptor`: it is DEFINED once (External `_X` + `_X$tlv$init` template +
// `__tlv_bootstrap` import, in the static's own object) and IMPORTED (undefined
// external `_X`) by every accessor object, whose `__text` TLVP relocation the
// linker resolves to the single canonical descriptor. (Emitting a descriptor per
// object would be a duplicate-symbol link error / divergent per-thread storage.)
//
// HOW CORRECTNESS IS OBSERVED. A C driver reads `X` in `main`, mutates `main`'s
// copy, spawns a worker thread that mutates the worker's OWN copy, joins, and
// re-reads `main`'s copy. Exit 0 iff (a) the initial read is `0xABCD`, (b) each
// thread's write is observed in its own copy, and (c) `main`'s copy is UNPERTURBED
// by the worker (true per-thread isolation). The binary RUNS under `timeout 10`;
// a botched TLV descriptor / BLR would hang or crash.
//
// PROOF GATE. Compiled with `TCG_NO_PROOF_CERTS=1`: the TLVP text relocations
// and per-instruction mappings are proven, but the final Mach-O object also
// carries two `ARM64_RELOC_UNSIGNED` descriptor rows per TLS definition plus
// compact-unwind rows. The complete production-surface inventory exposes those
// still-unproven object-side rows, so this lane pins semantics without claiming
// certification or exact-object binding.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "aarch64-apple-darwin";

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
    let candidates = [
        target_dir
            .join("release")
            .join("librustc_codegen_trust_cg.dylib"),
        target_dir
            .join("debug")
            .join("librustc_codegen_trust_cg.dylib"),
    ];
    for cand in &candidates {
        if cand.exists() {
            return cand.clone();
        }
    }
    let status = Command::new("cargo")
        .arg(format!("+{}", pinned_toolchain()))
        .args(["build"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run tls test");
    let built = target_dir
        .join("debug")
        .join("librustc_codegen_trust_cg.dylib");
    assert!(built.exists(), "expected dylib at {built:?} but none produced");
    built
}

fn aarch64_std_available() -> bool {
    let output = Command::new("rustup")
        .args(["target", "list", "--installed", "--toolchain"])
        .arg(pinned_toolchain())
        .output();
    match output {
        Ok(output) => String::from_utf8_lossy(&output.stdout)
            .lines()
            .any(|line| line.trim() == TARGET),
        Err(_) => false,
    }
}

fn host_is_aarch64_macos() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

fn has_cc() -> bool {
    Command::new("cc")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_tls_a64_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// The thread-local crate:
/// ```rust
/// #[thread_local] pub static mut X: i32 = 0xABCD;
/// extern "C" fn read_x()       -> i32 { X }            // TLS read
/// extern "C" fn bump_x(d: i32) -> i32 { X += d; X }    // TLS read-modify-write
/// ```
/// `read_x` exercises `Rvalue::ThreadLocalRef` + a deref load; `bump_x` adds a
/// deref STORE through the same TLV address (the write half of the access path).
const TLS_CRATE: &str = "\
#![crate_type = \"staticlib\"]\n\
#![feature(thread_local)]\n\
\n\
#[no_mangle]\n\
#[thread_local]\n\
pub static mut X: i32 = 0xABCD;\n\
\n\
#[no_mangle]\n\
pub extern \"C\" fn read_x() -> i32 {\n\
    unsafe { X }\n\
}\n\
\n\
#[no_mangle]\n\
pub extern \"C\" fn bump_x(delta: i32) -> i32 {\n\
    unsafe { X += delta; X }\n\
}\n";

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
    if !host_is_aarch64_macos() {
        eprintln!("skipping: requires an aarch64-apple-darwin host");
        return;
    }
    if !aarch64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    if !has_cc() {
        eprintln!("skipping: cc not available");
        return;
    }

    let dylib = ensure_dylib_built();
    let dir = workdir("x");

    // 1. Compile the thread-local crate THROUGH THE BRIDGE to objects.
    let src_path = dir.join("tls.rs");
    std::fs::write(&src_path, TLS_CRATE).expect("write source");
    let backend_arg = {
        let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
        s.push(&dylib);
        s
    };
    let obj_out = dir.join("tls");
    let output = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "staticlib"])
        .arg(&backend_arg)
        .env("TCG_NO_PROOF_CERTS", "1")
        // One CGU keeps the bridge's per-MonoItem objects predictable; the TLS
        // descriptor is still its own object (a `MonoItem::Static`).
        .args(["-Ccodegen-units=1"])
        // -O1 gives the clean `_p = &/*tls*/ X; _r = *_p` MIR shape (the -O0
        // alignment-debug-assert sequence around the TLS ref is unrelated noise).
        .args(["--target", TARGET, "-Cpanic=abort", "-Copt-level=1"])
        .arg("--emit=obj")
        .arg("-o")
        .arg(&obj_out)
        .arg(&src_path)
        .output()
        .expect("failed to spawn rustc via rustup");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "bridge failed to compile the thread-local crate. stderr: <<<{stderr}>>>"
    );

    // Collect every emitted object.
    let all_objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
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

    // 3. RUN natively on aarch64 under a watchdog: exit 0 iff the TLS reads/writes
    //    are correct AND per-thread isolated.
    //
    //    RETRY-ON-WATCHDOG-KILL (124): a freshly `cc`-linked Mach-O carrying a
    //    Darwin TLV descriptor can stall in dyld's first-execution `__tlv_bootstrap`
    //    processing under heavy concurrent system load (e.g. parallel `rustc`
    //    compiles), tripping the watchdog BEFORE `main` runs (observed: empty
    //    stdout on the kill; the very same flake hits the hand-authored backend
    //    oracle `e2e_aarch64_thread_local_read_is_correct_and_per_thread`, so it is
    //    a PRE-EXISTING dyld/TLV-under-load artifact, NOT a property of the bridge
    //    lowering). A run that reaches `main` is value-correct EVERY time (<0.2s),
    //    so a short per-attempt watchdog plus generous retries rides out a stall
    //    without ever masking an error: a WRONG value fails the value assertions
    //    below, and a genuine in-code deadlock would 124 on every attempt and still
    //    fail. Only the environmental cold-start stall is tolerated.
    let run_once = || {
        Command::new("timeout")
            .args(["6"])
            .arg(&bin)
            .output()
            .or_else(|_| Command::new(&bin).output())
            .expect("run linked binary")
    };
    let mut run = run_once();
    for _ in 0..30 {
        if run.status.code() != Some(124) {
            break;
        }
        // Small backoff so a load spike has time to ease between attempts.
        std::thread::sleep(std::time::Duration::from_millis(200));
        run = run_once();
    }
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
}
