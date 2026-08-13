// trust-cg-drat-trim build script.
//
// Provenance: vendored from upstream drat-trim at commit
// 2e3b2dc0ecf938addbd779d42877b6ed69d9a985 (Marijn Heule, MIT, 2024-11-25).
// The release source under `third_party/vendor/drat-trim/` stays pristine.
//
// Strategy
// --------
// drat-trim is naturally a CLI verifier: a single `.c` file with its own
// `main`. Rather than link it into a Rust binary (which would force us
// to rename `main` and expose a C library facade upstream does not
// provide), we mirror the upstream `Makefile` rule
//
//     gcc drat-trim.c -std=c99 -O2 -o drat-trim
//
// and produce a standalone executable inside `OUT_DIR`. Tests invoke
// the executable as a subprocess via `Command::new(...)`, exactly as
// they would a system-installed `drat-trim`. The `cc` crate is used to
// pick the same toolchain Cargo would otherwise use for C sources, so
// host/target overrides and `CC=...` propagate correctly.

use std::env;
use std::fs;
use std::path::PathBuf;

fn main() {
    let manifest_dir =
        PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let workspace_root = manifest_dir
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root has two ancestors above CARGO_MANIFEST_DIR")
        .to_path_buf();
    let src = workspace_root.join("third_party/vendor/drat-trim/drat-trim.c");
    assert!(
        src.is_file(),
        "vendored drat-trim source not found at {}; is the release source tree complete?",
        src.display()
    );

    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR is set by cargo"));
    let exe_name = if cfg!(windows) {
        "drat-trim.exe"
    } else {
        "drat-trim"
    };
    let exe_path = out_dir.join(exe_name);

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed={}", src.display());

    // Discover the C compiler Cargo would use. `Build::get_compiler()`
    // honours `CC`, target triples, and cross-compilation toolchains.
    let tool = cc::Build::new().get_compiler();

    let mut cmd = tool.to_command();
    if tool.is_like_msvc() {
        // MSVC's CRT ships no POSIX <sys/time.h>, which upstream
        // drat-trim.c includes for `struct timeval` + `gettimeofday`
        // (elapsed-time reporting only). Rather than patch the pristine
        // vendored source, drop a faithful Win32 shim header on the
        // include path so the upstream translation unit compiles
        // byte-verbatim (see WIN_SYS_TIME_SHIM). cl.exe also rejects
        // GCC's `-std=c99` and `-o` spellings, so emit the MSVC
        // equivalents: `/Fe:` names the executable and `/Fo:` routes the
        // object into OUT_DIR instead of the crate root.
        let shim_include = out_dir.join("win-posix-shim");
        let shim_sys = shim_include.join("sys");
        fs::create_dir_all(&shim_sys)
            .unwrap_or_else(|e| panic!("create win-posix-shim dir {}: {e}", shim_sys.display()));
        fs::write(shim_sys.join("time.h"), WIN_SYS_TIME_SHIM)
            .unwrap_or_else(|e| panic!("write win-posix-shim sys/time.h: {e}"));
        cmd.arg(format!("-I{}", shim_include.display()))
            // drat-trim.c reads its proof file with the POSIX/GNU
            // `getc_unlocked`, which the MSVC CRT does not provide. Its
            // exact MSVC twin is `_getc_nolock` (same `int(FILE *)`
            // contract, same single-threaded-fast-path intent).
            // `getc_unlocked` appears only at call sites in the upstream
            // source (never defined or address-taken), so redirecting the
            // identifier with `-D` is safe and keeps the source pristine.
            .arg("-Dgetc_unlocked=_getc_nolock")
            // Mirror upstream's Makefile optimisation tier.
            .arg("-O2")
            .arg(&src)
            .arg(format!("-Fe:{}", exe_path.display()))
            .arg(format!("-Fo:{}", out_dir.join("drat-trim.obj").display()));
    } else {
        // Mirror upstream's Makefile: `-std=c99 -O2`.
        cmd.arg("-std=c99")
            .arg("-O2")
            .arg(&src)
            .arg("-o")
            .arg(&exe_path);
    }

    let status = cmd
        .status()
        .unwrap_or_else(|e| panic!("invoke C compiler to build drat-trim: {e}"));
    assert!(
        status.success(),
        "compiling drat-trim failed: {:?} status={:?}",
        cmd,
        status
    );

    // Surface the resulting executable path to the crate's `env!` lookup
    // (`drat_trim_executable_path` in `lib.rs`). The variable name must NOT
    // carry the `TCG_`/`TRUST_CG_` prefix: cargo injects `rustc-env` vars into
    // the compiler process environment, and trustc fail-closes on any env var
    // in those reserved codegen-control namespaces
    // (`UNTRACKED_TRUST_CODEGEN_ENV_PREFIXES` in rustc_driver_impl). This is a
    // build-time constant embedded into the crate, not a codegen control.
    println!("cargo:rustc-env=DRAT_TRIM_BUILT_EXE={}", exe_path.display());
}

/// Windows-only shim for POSIX `<sys/time.h>`, written to the include path
/// when the vendored drat-trim.c is built under MSVC (which ships no such
/// header). It provides exactly the two symbols upstream uses — `struct
/// timeval` and `gettimeofday` — backed by `GetSystemTimeAsFileTime` from
/// kernel32 (declared inline so no windows.h macro surface leaks into the
/// upstream translation unit and no extra crate is pulled in). The `long`
/// field widths match Windows' own winsock `struct timeval`; every
/// drat-trim call site consumes a *differenced* (elapsed) time, so 32-bit
/// seconds are sufficient and honest. POSIX hosts never see this file and
/// keep using the real system header.
const WIN_SYS_TIME_SHIM: &str = r#"/* trust-cg-drat-trim: generated Win32 shim for POSIX <sys/time.h>.
 * MSVC only. Keeps third_party/vendor/drat-trim/drat-trim.c byte-verbatim by
 * satisfying its `#include <sys/time.h>` with a faithful Windows
 * implementation of `struct timeval` + `gettimeofday`. */
#ifndef TRUST_CG_WIN_POSIX_SYS_TIME_H
#define TRUST_CG_WIN_POSIX_SYS_TIME_H

/* Minimal, windows.h-free declaration of the one kernel32 entry point we
 * need. FILETIME's fields are 32-bit (DWORD) on every Windows ABI. */
typedef struct _TRUST_CG_FILETIME {
    unsigned long dwLowDateTime;
    unsigned long dwHighDateTime;
} TRUST_CG_FILETIME;

__declspec(dllimport) void __stdcall GetSystemTimeAsFileTime(TRUST_CG_FILETIME *);

struct timeval {
    long tv_sec;
    long tv_usec;
};

/* FILETIME counts 100-ns intervals since 1601-01-01; 116444736000000000
 * such intervals separate that epoch from the 1970-01-01 Unix epoch. */
static int gettimeofday(struct timeval *tv, void *tz) {
    TRUST_CG_FILETIME ft;
    unsigned long long ticks;
    unsigned long long micros;
    (void) tz;
    GetSystemTimeAsFileTime(&ft);
    ticks = ((unsigned long long) ft.dwHighDateTime << 32)
          | (unsigned long long) ft.dwLowDateTime;
    micros = (ticks - 116444736000000000ULL) / 10ULL;
    tv->tv_sec = (long) (micros / 1000000ULL);
    tv->tv_usec = (long) (micros % 1000000ULL);
    return 0;
}

#endif /* TRUST_CG_WIN_POSIX_SYS_TIME_H */
"#;
