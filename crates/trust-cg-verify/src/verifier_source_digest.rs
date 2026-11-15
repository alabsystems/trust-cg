// trust-cg-verify - the verifier's source identity
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! SHA-256 over the source files whose code decides a live proof replay's
//! outcome: this crate's manifest, build script and `src/` tree, and the
//! manifest and `src/` of `trust-cg-process-env` (the sanitized child
//! environment and subprocess helpers the replay starts AY and Clean with).
//! `build.rs` records it as `VERIFIER_SOURCE_SHA256`; it is part of every
//! source-bound negative-memo key, so an entry never crosses builds whose
//! replay or verdict code differ. The library's test build re-derives it from
//! the same files. Shared verbatim by both (`#[path]`), so the two cannot
//! disagree about what is hashed.

use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

/// The hashed inputs, relative to this crate's manifest directory. A
/// directory is hashed recursively (every regular file, by relative path); a
/// missing input is hashed as absent.
pub const INPUTS: &[&str] = &[
    "Cargo.toml",
    "build.rs",
    "src",
    "../trust-cg-process-env/Cargo.toml",
    "../trust-cg-process-env/src",
];

/// The lowercase-hex SHA-256 of [`INPUTS`] under `manifest_dir`.
pub fn digest(manifest_dir: &Path) -> Result<String, String> {
    let mut files: Vec<(String, Option<PathBuf>)> = Vec::new();
    for input in INPUTS {
        collect(&manifest_dir.join(input), input, &mut files)?;
    }
    files.sort();
    let mut hasher = Sha256::new();
    hasher.update(b"trust-cg-verify.source-identity.v1\0");
    for (label, path) in files {
        hasher.update((label.len() as u64).to_be_bytes());
        hasher.update(label.as_bytes());
        match path {
            Some(path) => {
                let bytes = std::fs::read(&path)
                    .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
                hasher.update([1]);
                hasher.update((bytes.len() as u64).to_be_bytes());
                hasher.update(&bytes);
            }
            None => hasher.update([0]),
        }
    }
    Ok(hasher
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

fn collect(
    path: &Path,
    label: &str,
    files: &mut Vec<(String, Option<PathBuf>)>,
) -> Result<(), String> {
    let metadata = match std::fs::symlink_metadata(path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            files.push((label.to_owned(), None));
            return Ok(());
        }
        Err(error) => return Err(format!("cannot stat {}: {error}", path.display())),
    };
    if metadata.is_dir() {
        let entries = std::fs::read_dir(path)
            .map_err(|error| format!("cannot list {}: {error}", path.display()))?;
        for entry in entries {
            let entry =
                entry.map_err(|error| format!("cannot list {}: {error}", path.display()))?;
            let name = entry.file_name();
            let child = format!("{label}/{}", name.to_string_lossy());
            collect(&entry.path(), &child, files)?;
        }
    } else if metadata.is_file() {
        files.push((label.to_owned(), Some(path.to_path_buf())));
    }
    Ok(())
}
