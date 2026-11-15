// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Scratch directories for the CLI tests.
//!
//! [`create`] makes a new directory under the system temporary directory with
//! an exclusive `mkdir` under a random name, so no two calls share one, and
//! returns a [`ScratchDir`] that owns it (RAII): dropping it removes the
//! directory and everything in it, whether the test passed or failed. A
//! failing test's directory is kept for inspection only when
//! `TRUST_CG_KEEP_TEST_OBJECTS` is set (to anything); the kept path is
//! printed. The Darwin floor never passes that variable on, and fails a target
//! that leaves anything in its TMPDIR.

// Declared unconditionally; a target that uses only part of this module must
// not trip the workspace's `warnings = "deny"`.
#![allow(dead_code)]

use std::ffi::OsStr;
use std::fmt;
use std::ops::Deref;
use std::path::{Path, PathBuf};

/// The environment variable that keeps a failing test's scratch directory.
pub const KEEP_ON_FAILURE: &str = "TRUST_CG_KEEP_TEST_OBJECTS";

/// A scratch directory this test owns. It dereferences to its path, and
/// dropping it removes the directory unless the test is failing and
/// [`KEEP_ON_FAILURE`] is set.
pub struct ScratchDir {
    directory: Option<tempfile::TempDir>,
    path: PathBuf,
}

impl ScratchDir {
    /// The directory's path.
    pub fn path(&self) -> &Path {
        &self.path
    }
}

impl Deref for ScratchDir {
    type Target = PathBuf;

    fn deref(&self) -> &PathBuf {
        &self.path
    }
}

impl AsRef<Path> for ScratchDir {
    fn as_ref(&self) -> &Path {
        &self.path
    }
}

impl AsRef<OsStr> for ScratchDir {
    fn as_ref(&self) -> &OsStr {
        self.path.as_os_str()
    }
}

impl fmt::Debug for ScratchDir {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.path, formatter)
    }
}

impl Drop for ScratchDir {
    fn drop(&mut self) {
        let Some(directory) = self.directory.take() else {
            return;
        };
        if std::thread::panicking() && std::env::var_os(KEEP_ON_FAILURE).is_some() {
            let kept = directory.keep();
            eprintln!(
                "{KEEP_ON_FAILURE} is set: keeping the failing test's scratch directory {}",
                kept.display()
            );
        }
        // Otherwise `directory` is dropped here, which removes it.
    }
}

/// Create a new directory whose name starts with `prefix`, owned by the
/// returned [`ScratchDir`]. Panics if it cannot be created.
pub fn create(prefix: &str) -> ScratchDir {
    let directory = tempfile::Builder::new()
        .prefix(prefix)
        .tempdir()
        .unwrap_or_else(|error| panic!("create a unique {prefix}* scratch directory: {error}"));
    let path = directory.path().to_path_buf();
    ScratchDir {
        directory: Some(directory),
        path,
    }
}
