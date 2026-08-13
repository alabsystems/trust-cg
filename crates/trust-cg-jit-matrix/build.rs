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

fn main() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR is set by cargo");
    let manifest_dir = Path::new(&manifest_dir);
    let workspace_root = manifest_dir
        .parent()
        .and_then(Path::parent)
        .expect("trust-cg workspace root is two ancestors above CARGO_MANIFEST_DIR");
    let identity = pipeline_source_identity::compute_pipeline_source_identity(workspace_root)
        .unwrap_or_else(|error| panic!("compute machine-code pipeline source identity: {error}"));

    // Cargo needs both file watches (content mutation/deletion) and directory
    // watches (addition/rename). The identity itself is workspace-relative, so
    // equivalent source trees in different worktrees still share cache entries.
    for path in &identity.watched_paths {
        println!("cargo:rerun-if-changed={}", path.display());
    }

    let out_dir = env::var_os("OUT_DIR").expect("OUT_DIR is set by cargo");
    fs::write(
        PathBuf::from(out_dir).join("pipeline_source_identity.txt"),
        identity.hex,
    )
    .expect("write machine-code pipeline source identity");
}
