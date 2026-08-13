// trust-cg-test repository-root discovery.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Repository-root discovery for `trust-cg-test`.

use std::path::{Path, PathBuf};

/// The resolved project root. All I/O paths in `trust-cg-test` are derived
/// from this type — nothing is hard-coded.
#[derive(Clone, Debug)]
pub struct RepoRoot(pub PathBuf);

impl RepoRoot {
    /// Locate the repo root by walking up from `start` looking for the
    /// workspace `Cargo.toml`. Falls back to the current working
    /// directory if the walk fails.
    pub fn locate(start: &Path) -> anyhow::Result<Self> {
        let mut cur = start.canonicalize().unwrap_or_else(|_| start.to_path_buf());
        loop {
            if cur.join("Cargo.toml").is_file() && cur.join("crates").is_dir() {
                return Ok(Self(cur));
            }
            if !cur.pop() {
                // Fall back to cwd — keeps `trust-cg-test` runnable from the
                // binary directory during development.
                return Ok(Self(std::env::current_dir()?));
            }
        }
    }

    /// Path relative to the repo root.
    #[must_use]
    pub fn join<P: AsRef<Path>>(&self, rel: P) -> PathBuf {
        self.0.join(rel)
    }
}
