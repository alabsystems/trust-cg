// trust-cg-jit-matrix - build script
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Computes a build-time content identity for the complete machine-code pipeline
// and writes it to an `OUT_DIR` file consumed with `include_str!`.
// `codegen_version_hash()` folds this identity into the on-disk
// (L2) machine-code buffer cache key so that *any* change to lowering,
// optimization, register allocation, verification, code generation, or an
// embedded verifier asset invalidates cached buffers -- even when workspace
// package versions are unchanged.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

#[path = "src/pipeline_source_identity.rs"]
mod pipeline_source_identity;

// `main` returns `Result` so the panic-family lint set is empty in this file,
// the same discipline `trust-cg-sat-host` and `trust-cg-drat-trim` adopted in
// 2c94d27d: the ratchet baseline's scope is `crates/*/src/**`, so a build
// script can never be inventoried, and `check_panic_clippy.sh` compares it
// against a baseline of 0 that no regeneration can satisfy. A build script's
// only caller is cargo, and `Termination for Result` prints the error and exits
// non-zero, so every path that aborted the build before still aborts it — with
// a strictly more specific message. Nothing degrades to a silent fallback.
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let manifest_dir =
        env::var("CARGO_MANIFEST_DIR").map_err(|_| "CARGO_MANIFEST_DIR is not set by cargo")?;
    let manifest_dir = Path::new(&manifest_dir);
    let workspace_root = manifest_dir
        .parent()
        .and_then(Path::parent)
        .ok_or("trust-cg workspace root is two ancestors above CARGO_MANIFEST_DIR")?;
    let identity = pipeline_source_identity::compute_pipeline_source_identity(workspace_root)
        .map_err(|error| format!("compute machine-code pipeline source identity: {error}"))?;

    // Cargo needs both file watches (content mutation/deletion) and directory
    // watches (addition/rename). The identity itself is workspace-relative, so
    // equivalent source trees in different worktrees still share cache entries.
    for path in &identity.watched_paths {
        println!("cargo:rerun-if-changed={}", path.display());
    }

    let out_dir = env::var_os("OUT_DIR").ok_or("OUT_DIR is not set by cargo")?;
    fs::write(
        PathBuf::from(out_dir).join("pipeline_source_identity.txt"),
        identity.hex,
    )
    .map_err(|error| format!("write machine-code pipeline source identity: {error}"))?;
    Ok(())
}
