// Typed wrappers around every external tool `trust-cg-test` may invoke.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Only `shell.rs` and this module may construct a subprocess. Any other
// file doing so fails `trust-cg-test ratchet shell-isolation`.

//! Typed external-tool wrappers.
//!
//! [`probe_one`] reports a tool's presence and version as a [`VersionInfo`];
//! [`Cargo`] names the one tool subcommands spawn by type.

use serde::{Deserialize, Serialize};

use crate::shell::{Spawn, which};

/// Tool presence + reported version.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct VersionInfo {
    /// Short tool label, e.g. `"clang"`.
    pub name: String,
    /// Absolute path to the executable (if resolvable).
    pub path: Option<String>,
    /// Reported version string — empty if `--version` failed.
    pub version: String,
    /// Whether the tool was found on `$PATH`.
    pub present: bool,
}

impl VersionInfo {
    fn missing(name: &str) -> Self {
        Self {
            name: name.to_string(),
            path: None,
            version: String::new(),
            present: false,
        }
    }
}

fn probe(name: &str, arg: &str) -> VersionInfo {
    let Some(path) = which(name) else {
        return VersionInfo::missing(name);
    };
    let res = Spawn::new(name).arg(arg).capture();
    let version = res
        .as_ref()
        .map(|c| {
            let raw = if c.stdout.trim().is_empty() {
                c.stderr.clone()
            } else {
                c.stdout.clone()
            };
            raw.lines().next().unwrap_or("").trim().to_string()
        })
        .unwrap_or_default();
    VersionInfo {
        name: name.to_string(),
        path: Some(path.to_string_lossy().into_owned()),
        version,
        present: true,
    }
}

/// `targo` — the Trust toolchain's Cargo (owner directive 2026-09-28: ALab
/// systems build with Trust). Build verbs need a lane: callers pass
/// `--unverified`. Used by WS1 and WS6.
#[derive(Clone, Copy, Debug, Default)]
pub struct Cargo;

impl Cargo {
    /// Short program name used on `PATH`.
    #[must_use]
    pub const fn program() -> &'static str {
        "targo"
    }
}

/// Called by `cmd::doctor` and `cmd::rustc` to tell the operator how to
/// install a missing tool.
#[must_use]
pub fn install_hint(program: &str) -> &'static str {
    match program {
        "clang" | "cc" => "install Xcode Command Line Tools: `xcode-select --install`",
        "csmith" => "brew install csmith",
        "yarpgen" => "build from source: https://github.com/intel/yarpgen",
        "creduce" => "brew install creduce",
        "ay" => {
            "install a Trust toolchain that ships `bin/ay`; trust-cg's verifier runs ONLY that \
             identity-checked AY (crates/trust-cg-verify/src/ay_identity.rs), never one found on PATH"
        }
        "gh" => "brew install gh",
        "targo" | "trustc" => {
            "install the Trust toolchain package (aterm's atpkg; see `aterm help rust`); \
             there is no stock rustup fallback"
        }
        _ => "check tool documentation",
    }
}

/// Convenience: call `probe` once for a single tool name.
#[must_use]
pub fn probe_one(name: &str) -> VersionInfo {
    if name == "ay" {
        return probe_toolchain_ay();
    }
    probe(name, "--version")
}

/// AY is never searched for on `PATH` and never executed here. trust-cg's
/// verifier admits exactly one AY: the `bin/ay` of the Trust toolchain it was
/// built with, identified by the SHA-256 of its bytes recorded at build time
/// (`crates/trust-cg-verify/src/ay_identity.rs`), and starts only that. This
/// row reports whether the Trust package `trustc`'s sysroot ships that file; the
/// identity itself is checked by the verifier when it is used.
fn probe_toolchain_ay() -> VersionInfo {
    let sysroot = Spawn::new("trustc")
        .args(["--print", "sysroot"])
        .capture()
        .ok()
        .filter(crate::shell::Captured::success)
        .map(|captured| captured.stdout.trim().to_string())
        .filter(|sysroot| !sysroot.is_empty());
    let Some(sysroot) = sysroot else {
        return VersionInfo::missing("ay");
    };
    let path = std::path::Path::new(&sysroot).join("bin").join("ay");
    if !path.is_file() {
        return VersionInfo::missing("ay");
    }
    VersionInfo {
        name: "ay".to_string(),
        path: Some(path.to_string_lossy().into_owned()),
        version: "not executed (identity checked by sha256 at use)".to_string(),
        present: true,
    }
}
