//! Host-derived target facts shared by the x86-64 bridge integration tests.
//!
//! The x86-64 tests were written on macOS and pinned `x86_64-apple-darwin`.
//! That target only executes on a Darwin host, so on a Linux x86-64 host every
//! test skipped as "rust-std not installed" and the corpus was vacuous there.
//! Each test now compiles for the host operating system's x86-64 triple: the
//! Darwin triple on macOS and the GNU/Linux triple on Linux. A test that has a
//! genuine Darwin-only dependency (compact unwind, `otool`) keeps its own guard.
//!
//! This selects the target; it does not make any platform's execution evidence
//! stand in for another's. A run on one host qualifies only that host.
#![allow(dead_code)]

/// The x86-64 triple this host can natively link and execute.
pub const X86_64_TARGET: &str = if cfg!(target_os = "macos") {
    "x86_64-apple-darwin"
} else if cfg!(target_os = "linux") {
    "x86_64-unknown-linux-gnu"
} else {
    // Unsupported hosts keep the historical pin so `target_std_available`
    // reports it absent and the test skips with the usual message.
    "x86_64-apple-darwin"
};

/// The AArch64 triple this host can natively link and execute.
pub const AARCH64_TARGET: &str = if cfg!(target_os = "macos") {
    "aarch64-apple-darwin"
} else if cfg!(target_os = "linux") {
    "aarch64-unknown-linux-gnu"
} else {
    "aarch64-apple-darwin"
};

/// Whether the host operating system executes `X86_64_TARGET` binaries
/// natively (the architecture check is the caller's `cfg!(target_arch)`).
pub const HOST_OS_SUPPORTED: bool = cfg!(any(target_os = "macos", target_os = "linux"));

/// Linker flags pinning the macOS deployment floor; empty on other hosts,
/// where `cc` rejects `-mmacosx-version-min`.
pub fn deployment_min_flags(deployment_target: &str) -> Vec<String> {
    if cfg!(target_os = "macos") {
        vec![format!("-mmacosx-version-min={deployment_target}")]
    } else {
        Vec::new()
    }
}

/// Whether an emitted object's `llvm-objdump` header names this host's object
/// format for `X86_64_TARGET` (Mach-O on macOS, ELF on Linux).
pub fn object_format_name() -> &'static str {
    if cfg!(target_os = "macos") {
        "mach-o"
    } else {
        "elf64-x86-64"
    }
}
