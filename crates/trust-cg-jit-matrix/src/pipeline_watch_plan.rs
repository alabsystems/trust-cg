// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Recursive Cargo watch compaction, independent of the pipeline's hash algorithm.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Component, PathBuf};

/// Cargo recursively watches a declared directory, including its entries and
/// symlink targets. Keep that declaration, rather than also declaring every
/// descendant and making a bounded content observer read the same bytes again.
/// Identity hashing is independent of this watch plan and still reads every
/// selected source file. Do not canonicalize aliases or reason across `..`.
/// A symlink/error cannot establish a covering directory of its own.
pub(crate) fn compact_recursive_watches(paths: &mut Vec<PathBuf>) {
    paths.sort();
    paths.dedup();
    let mut directories = BTreeSet::new();
    paths.retain(|path| {
        if path.components().any(|part| part == Component::ParentDir) {
            return true;
        }
        if path
            .ancestors()
            .skip(1)
            .any(|parent| directories.contains(parent))
        {
            return false;
        }
        if fs::symlink_metadata(path).is_ok_and(|metadata| {
            let plain = metadata.file_type().is_dir() && !metadata.file_type().is_symlink();
            #[cfg(windows)]
            {
                use std::os::windows::fs::MetadataExt as _;
                plain && metadata.file_attributes() & 0x400 == 0
            }
            #[cfg(not(windows))]
            {
                plain
            }
        }) {
            directories.insert(path.clone());
        }
        true
    });
}
