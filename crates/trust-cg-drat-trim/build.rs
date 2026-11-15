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
use std::path::{Path, PathBuf};

/// The macOS deployment target the checker is built for. This is a pinned
/// INPUT to the checker's exact bytes (clang stamps it into
/// `LC_BUILD_VERSION.minos`), not a compatibility floor: every Apple
/// `host-checker` row of
/// `crates/trust-cg-verify/verdict_db/canary_certs/manifest.v1` must be minted
/// under this value, so the constant and those rows form a bound set. Moving it
/// re-keys the checker on EVERY Apple host, and each Apple row must then be
/// re-qualified on its own host (docs/portable-checker-host-qualification.md);
/// a row minted on a tree without this pin is equally stale once the pin
/// reaches it. Both Apple rows went stale that way after the 2026-09-21 merge
/// (x86-64 re-qualified 2026-09-27, ARM64 2026-09-29). See the note at the
/// `cc::Build` below.
const APPLE_DEPLOYMENT_TARGET: &str = "26.5";

// `main` returns `Result` instead of panicking.
// A build script's only caller is cargo, and `Termination for Result` prints
// the error and exits non-zero, so every path that aborted the build before
// still aborts it — with a strictly more specific message. Nothing here
// degrades to a silent fallback.
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let manifest_dir = PathBuf::from(
        env::var_os("CARGO_MANIFEST_DIR").ok_or("CARGO_MANIFEST_DIR is not set by cargo")?,
    );
    let workspace_root = manifest_dir
        .parent()
        .and_then(|p| p.parent())
        .ok_or_else(|| {
            format!(
                "workspace root needs two ancestors above CARGO_MANIFEST_DIR {}",
                manifest_dir.display()
            )
        })?
        .to_path_buf();
    let src = workspace_root.join("third_party/vendor/drat-trim/drat-trim.c");
    let reproducible_src = Path::new("third_party/vendor/drat-trim/drat-trim.c");
    assert!(
        src.is_file(),
        "vendored drat-trim source not found at {}; is the release source tree complete?",
        src.display()
    );

    let out_dir = PathBuf::from(env::var_os("OUT_DIR").ok_or("OUT_DIR is not set by cargo")?);
    // Build scripts run on the host, so `cfg!(windows)` describes the machine
    // running Cargo rather than the checker we are producing. Use Cargo's
    // target configuration so cross-checks embed a correctly named Windows
    // executable too.
    let target_os = env::var("CARGO_CFG_TARGET_OS")
        .map_err(|e| format!("CARGO_CFG_TARGET_OS is not set by cargo: {e}"))?;
    let target_is_windows = target_os == "windows";
    let exe_name = if target_is_windows {
        "drat-trim.exe"
    } else {
        "drat-trim"
    };
    let exe_path = out_dir.join(exe_name);

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed={}", src.display());

    // Discover the C compiler Cargo would use. Pin the options that affect
    // executable bytes before asking `cc` for its command: otherwise Cargo's
    // debug/release profile leaks `-g` and differing optimization defaults
    // into two checkers built from the same source, defeating the exact binary
    // identity carried by portable-certificate manifests.
    let mut build = cc::Build::new();
    build.opt_level(2).debug(false);
    if target_os == "macos" {
        // The Apple deployment target is executable bytes too. Left to `cc`,
        // the value comes from `MACOSX_DEPLOYMENT_TARGET` in the caller's
        // environment, else from the DEFAULT SDK's version (`xcrun
        // --show-sdk-version --sdk macosx`, which ignores `SDKROOT`). A
        // CommandLineTools update that registers a newer default SDK therefore
        // re-keys the checker with nothing in this repository changed. Measured
        // 2026-09-20 with identical source, clang 21, flags and
        // `SDKROOT=MacOSX26.5.sdk`: the CLT 26.6 install of 2026-09-13 made
        // 27.0 the default, the inferred `-mmacosx-version-min` moved
        // 26.5 -> 27.0, and the checker moved from 0f634db2… (the committed
        // manifest identity) to 54c6f06f…, which declined every portable
        // certificate fail-closed — and silently, until `canary_cert` learned
        // to announce it. Re-minting the manifest does not remove the
        // mechanism: its checker line has moved three times already
        // (2026-08-31, 09-01, 09-10), the last time back to the 08-20 value.
        //
        // Pin the value every Apple manifest row is minted with. `cc` reads
        // this override BEFORE the process environment, so a developer's own
        // `MACOSX_DEPLOYMENT_TARGET` cannot re-key the checker either. What
        // remains unpinned is real toolchain identity — the compiler and the
        // SDK (`LC_BUILD_VERSION.sdk`) — and a change there is a deliberate
        // re-authorization, not drift.
        build.env("MACOSX_DEPLOYMENT_TARGET", APPLE_DEPLOYMENT_TARGET);
    }
    let tool = build.get_compiler();

    let mut cmd = tool.to_command();
    if target_os == "macos" {
        // cc appends caller CFLAGS after its computed defaults and builder
        // flags. Reassert this exact-byte input on the final command, after
        // every tool argument, so a caller's deployment flag cannot replace
        // the value bound by the reviewed checker manifests. Other compiler
        // and SDK inputs remain real inputs to checker identity.
        cmd.arg(format!("-mmacosx-version-min={APPLE_DEPLOYMENT_TARGET}"));
    }
    // drat-trim's assertions expand `__FILE__`.  Passing `src` here used to
    // embed the absolute checkout path in the checker, so otherwise identical
    // builds in trust-cg and Trust's nested first-party/trust-cg checkout had
    // different hashes.  Portable-proof manifests intentionally authorize the
    // exact checker bytes, which made every certificate fail closed in the
    // nested build.  Compile from a stable root with a stable relative spelling
    // while retaining `src` above for filesystem/rerun checks.
    cmd.current_dir(&workspace_root);
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
            .map_err(|e| format!("create win-posix-shim dir {}: {e}", shim_sys.display()))?;
        fs::write(shim_sys.join("time.h"), WIN_SYS_TIME_SHIM)
            .map_err(|e| format!("write win-posix-shim sys/time.h: {e}"))?;
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
            .arg(reproducible_src)
            .arg(format!("-Fe:{}", exe_path.display()))
            .arg(format!("-Fo:{}", out_dir.join("drat-trim.obj").display()));
    } else {
        // Mirror upstream's Makefile: `-std=c99 -O2`. Strict C99 hides the
        // POSIX `getc_unlocked` on glibc (`__STRICT_ANSI__` gates it; Darwin
        // declares it regardless, which is why only Linux ever missed it), so
        // re-expose the POSIX surface with a feature macro instead of touching
        // the pristine vendored source — the same keep-the-source-verbatim
        // move as the MSVC `-D` redirect above.
        cmd.arg("-std=c99").arg("-D_DEFAULT_SOURCE");
        if target_is_windows {
            // MinGW is GCC-like, so it takes this branch rather than the MSVC
            // shim above, but its CRT does not export the POSIX/GNU
            // `getc_unlocked` symbol. The checker is a single-threaded
            // subprocess; `getc` has the same result and the extra stream lock
            // cannot change proof acceptance.
            cmd.arg("-Dgetc_unlocked=getc");
        }
        cmd.arg("-O2").arg(reproducible_src);
        // Apple's linker derives LC_UUID from content by default. Preserve it:
        // current macOS rejects linker-signed executables with no LC_UUID. The
        // stable basename plus normalized compiler options above make both the
        // UUID and ad-hoc code signature reproducible across OUT_DIR/profile.
        cmd.arg("-o").arg(&exe_path);
    }

    let status = cmd
        .status()
        .map_err(|e| format!("invoke C compiler to build drat-trim: {e}"))?;
    assert!(
        status.success(),
        "compiling drat-trim failed: {:?} status={:?}",
        cmd,
        status
    );

    // This is load-bearing for exact-byte certificate authorization.  Catch a
    // compiler/toolchain change that starts recording the checkout root before
    // it can silently disable every portable certificate again.
    let executable = fs::read(&exe_path)
        .map_err(|e| format!("read built checker {}: {e}", exe_path.display()))?;
    let workspace_bytes = workspace_root.to_string_lossy();
    assert!(
        workspace_bytes.is_empty()
            || !executable
                .windows(workspace_bytes.len())
                .any(|window| window == workspace_bytes.as_bytes()),
        "built drat-trim embeds checkout root {}; compile inputs must remain path-stable",
        workspace_root.display()
    );

    // Surface the resulting executable path to the crate's `env!` lookup
    // (`drat_trim_executable_path` in `lib.rs`). The variable name must NOT
    // carry the `TCG_`/`TRUST_CG_` prefix: cargo injects `rustc-env` vars into
    // the compiler process environment, and trustc fail-closes on any env var
    // in those reserved codegen-control namespaces
    // (`UNTRACKED_TRUST_CODEGEN_ENV_PREFIXES` in rustc_driver_impl). This is a
    // build-time constant embedded into the crate, not a codegen control.
    println!("cargo:rustc-env=DRAT_TRIM_BUILT_EXE={}", exe_path.display());
    // The executable is compiled for Cargo's TARGET, not the build-script
    // HOST. Embed this immutable qualifier beside its path; runtime variables
    // must not select another platform's reviewed checker authorization.
    let target = env::var("TARGET").map_err(|e| format!("TARGET is not set by cargo: {e}"))?;
    println!("cargo:rustc-env=DRAT_TRIM_BUILT_TARGET={target}");
    Ok(())
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
