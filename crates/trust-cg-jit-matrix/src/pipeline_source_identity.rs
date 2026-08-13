// trust-cg-jit-matrix - deterministic machine-code pipeline source identity
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Build-time content identity for every local input capable of changing an
//! executable buffer. Kept in a standalone module so the build script and its
//! mutation regression tests execute the exact same implementation.

use sha2::{Digest, Sha256};
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

/// Local Rust crates in the executable-buffer production and admission path.
pub const PIPELINE_CRATES: &[&str] = &[
    "trust-cg-jit-matrix",
    "trust-cg-codegen",
    "trust-cg-ir",
    "trust-cg-dialect",
    "trust-cg-lower",
    "trust-cg-opt",
    "trust-cg-regalloc",
    "trust-cg-verify",
    "trust-cg-drat-trim",
];

/// Sibling trust-ir crates whose algorithms feed lowering and validation.
pub const TRUST_IR_PIPELINE_CRATES: &[&str] = &["trust-ir", "trust-ir-build", "trust-ir-giveback"];

/// Sibling Clean crates reached through TY's local dependency patches.
pub const CLEAN_PIPELINE_CRATES: &[&str] = &["clean-kernel"];

const PIPELINE_ASSET_TREES: &[&str] = &[
    "crates/trust-cg-verify/verdict_db",
    "crates/trust-cg-verify/lrat_fixtures",
];

const PIPELINE_FILES: &[&str] = &[
    "Cargo.toml",
    "Cargo.lock",
    "third_party/vendor/drat-trim/drat-trim.c",
];

/// The identity and every file/directory Cargo must watch to keep it current.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PipelineSourceIdentity {
    pub hex: String,
    pub watched_paths: Vec<PathBuf>,
    #[cfg(test)]
    pub hashed_relative_paths: Vec<String>,
}

/// Compute the full trust-cg executable-buffer pipeline identity.
pub fn compute_pipeline_source_identity(
    workspace_root: &Path,
) -> io::Result<PipelineSourceIdentity> {
    let mut trees = Vec::new();
    let mut files = Vec::new();
    let mut crate_roots = Vec::new();

    for crate_name in PIPELINE_CRATES {
        let crate_root = PathBuf::from("crates").join(crate_name);
        crate_roots.push(workspace_root.join(&crate_root));
        trees.push(crate_root.join("src"));
        files.push(crate_root.join("Cargo.toml"));
        let build_script = crate_root.join("build.rs");
        if workspace_root.join(&build_script).is_file() {
            files.push(build_script);
        }
    }
    trees.extend(PIPELINE_ASSET_TREES.iter().map(PathBuf::from));
    files.extend(PIPELINE_FILES.iter().map(PathBuf::from));

    let mut identity = compute_source_identity(workspace_root, &trees, &files)?;
    // Watching each crate root observes a newly-added optional build.rs without
    // recursively hashing unrelated tests, examples, or benchmarks.
    identity.watched_paths.extend(crate_roots);

    // TY co-development patches trust-ir and clean-kernel to adjacent dirty
    // worktrees. Hash those exact sources when present; standalone trust-cg
    // checkouts without siblings remain covered by pinned revisions in
    // Cargo.lock.
    let mut external_identities = Vec::new();
    if let Some(parent) = workspace_root.parent() {
        let trust_ir_root = parent.join("trust-ir");
        if trust_ir_root.join("crates/trust-ir/Cargo.toml").is_file() {
            let external = compute_trust_ir_source_identity(&trust_ir_root)?;
            external_identities.push(("trust-ir", external.hex.clone()));
            identity.watched_paths.extend(external.watched_paths);
            #[cfg(test)]
            identity.hashed_relative_paths.extend(
                external
                    .hashed_relative_paths
                    .into_iter()
                    .map(|path| format!("external-trust-ir/{path}")),
            );
        }
        let clean_root = parent.join("clean");
        if clean_root.join("crates/clean-kernel/Cargo.toml").is_file() {
            let external = compute_clean_source_identity(&clean_root)?;
            external_identities.push(("clean", external.hex.clone()));
            identity.watched_paths.extend(external.watched_paths);
            #[cfg(test)]
            identity.hashed_relative_paths.extend(
                external
                    .hashed_relative_paths
                    .into_iter()
                    .map(|path| format!("external-clean/{path}")),
            );
        }
    }
    if !external_identities.is_empty() {
        let mut combined = Sha256::new();
        combined.update(b"trust-cg.machine-code-pipeline.combined-identity.v2\0");
        combined.update(identity.hex.as_bytes());
        for (label, external_hex) in external_identities {
            combined.update((label.len() as u64).to_le_bytes());
            combined.update(label.as_bytes());
            combined.update(external_hex.as_bytes());
        }
        identity.hex = combined
            .finalize()
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();
    }
    identity.watched_paths.sort();
    identity.watched_paths.dedup();
    Ok(identity)
}

fn compute_clean_source_identity(root: &Path) -> io::Result<PipelineSourceIdentity> {
    let mut trees = Vec::new();
    let mut files = vec![
        PathBuf::from("Cargo.toml"),
        PathBuf::from("Cargo.lock"),
        PathBuf::from("data/soundness_tcb.json"),
    ];
    let mut crate_roots = Vec::new();
    for crate_name in CLEAN_PIPELINE_CRATES {
        let crate_root = PathBuf::from("crates").join(crate_name);
        crate_roots.push(root.join(&crate_root));
        trees.push(crate_root.join("src"));
        files.push(crate_root.join("Cargo.toml"));
        let build_script = crate_root.join("build.rs");
        if root.join(&build_script).is_file() {
            files.push(build_script);
        }
    }
    let mut identity = compute_source_identity(root, &trees, &files)?;
    identity.watched_paths.extend(crate_roots);
    identity.watched_paths.sort();
    identity.watched_paths.dedup();
    Ok(identity)
}

fn compute_trust_ir_source_identity(root: &Path) -> io::Result<PipelineSourceIdentity> {
    let mut trees = Vec::new();
    let mut files = vec![PathBuf::from("Cargo.toml"), PathBuf::from("Cargo.lock")];
    let mut crate_roots = Vec::new();
    for crate_name in TRUST_IR_PIPELINE_CRATES {
        let crate_root = PathBuf::from("crates").join(crate_name);
        crate_roots.push(root.join(&crate_root));
        trees.push(crate_root.join("src"));
        files.push(crate_root.join("Cargo.toml"));
        let build_script = crate_root.join("build.rs");
        if root.join(&build_script).is_file() {
            files.push(build_script);
        }
    }
    let mut identity = compute_source_identity(root, &trees, &files)?;
    identity.watched_paths.extend(crate_roots);
    identity.watched_paths.sort();
    identity.watched_paths.dedup();
    Ok(identity)
}

/// Hash required trees and files using workspace-relative paths.
///
/// This helper is public so integration tests can prove that content mutation,
/// addition, deletion, and rename all change the production identity algorithm.
pub fn compute_source_identity(
    workspace_root: &Path,
    relative_trees: &[PathBuf],
    relative_files: &[PathBuf],
) -> io::Result<PipelineSourceIdentity> {
    let mut watched_paths = Vec::new();
    let mut hashed_files = Vec::new();

    for relative_tree in relative_trees {
        let tree = workspace_root.join(relative_tree);
        require_kind(&tree, true)?;
        watched_paths.push(tree.clone());
        collect_files(workspace_root, &tree, &mut hashed_files, &mut watched_paths)?;
    }
    for relative_file in relative_files {
        let file = workspace_root.join(relative_file);
        require_kind(&file, false)?;
        watched_paths.push(file.clone());
        hashed_files.push(file);
    }

    hashed_files.sort_by(|left, right| {
        relative_key(workspace_root, left).cmp(&relative_key(workspace_root, right))
    });
    hashed_files.dedup();
    watched_paths.sort();
    watched_paths.dedup();

    let mut hasher = Sha256::new();
    hasher.update(b"trust-cg.machine-code-pipeline.source-identity.v2\0");
    let mut hashed_relative_paths = Vec::with_capacity(hashed_files.len());
    for file in hashed_files {
        let relative = relative_key(workspace_root, &file);
        let bytes = fs::read(&file)?;
        hasher.update((relative.len() as u64).to_le_bytes());
        hasher.update(relative.as_bytes());
        hasher.update((bytes.len() as u64).to_le_bytes());
        hasher.update(&bytes);
        hashed_relative_paths.push(relative);
    }

    let digest = hasher.finalize();
    let hex = digest.iter().map(|byte| format!("{byte:02x}")).collect();
    Ok(PipelineSourceIdentity {
        hex,
        watched_paths,
        #[cfg(test)]
        hashed_relative_paths,
    })
}

fn require_kind(path: &Path, directory: bool) -> io::Result<()> {
    let valid = if directory {
        path.is_dir()
    } else {
        path.is_file()
    };
    if valid {
        Ok(())
    } else {
        Err(io::Error::new(
            io::ErrorKind::NotFound,
            format!(
                "required pipeline {} is missing: {}",
                if directory { "directory" } else { "file" },
                path.display()
            ),
        ))
    }
}

fn collect_files(
    workspace_root: &Path,
    directory: &Path,
    files: &mut Vec<PathBuf>,
    watched_paths: &mut Vec<PathBuf>,
) -> io::Result<()> {
    let mut entries = fs::read_dir(directory)?.collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(std::fs::DirEntry::file_name);
    for entry in entries {
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            watched_paths.push(path.clone());
            collect_files(workspace_root, &path, files, watched_paths)?;
        } else if file_type.is_file() {
            files.push(path.clone());
            watched_paths.push(path);
        } else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "pipeline identity refuses non-regular source entry: {}",
                    relative_key(workspace_root, &path)
                ),
            ));
        }
    }
    Ok(())
}

fn relative_key(workspace_root: &Path, path: &Path) -> String {
    path.strip_prefix(workspace_root)
        .unwrap_or(path)
        .components()
        .map(|component| component.as_os_str().to_string_lossy())
        .collect::<Vec<_>>()
        .join("/")
}
