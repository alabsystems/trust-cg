// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Scratch directories owned by the whole test process.
//!
//! [`process_scoped`] makes a new directory under the system temporary
//! directory (exclusive `mkdir`, random name) for a fixture whose path
//! outlives any one scope: a fake tool a request names, or an evidence
//! directory a fixture records. Every such directory is removed when the test
//! process exits, after every test has finished; libtest exits the process
//! normally after a failing test too, so only a killed process leaves one.
//! `TRUST_CG_KEEP_TEST_OBJECTS` set (to anything) keeps them for inspection.

// Declared unconditionally; a target whose callers are all cfg'd out for this
// host must not trip the workspace's `warnings = "deny"`.
#![allow(dead_code)]

use std::path::PathBuf;
use std::sync::{Mutex, OnceLock, PoisonError};

/// The environment variable that keeps these directories.
pub const KEEP: &str = "TRUST_CG_KEEP_TEST_OBJECTS";

static PATHS: OnceLock<Mutex<Vec<PathBuf>>> = OnceLock::new();

extern "C" fn remove_registered() {
    if std::env::var_os(KEEP).is_some() {
        return;
    }
    if let Some(paths) = PATHS.get() {
        for path in paths.lock().unwrap_or_else(PoisonError::into_inner).iter() {
            let _ = std::fs::remove_dir_all(path);
        }
    }
}

/// A new directory whose name starts with `prefix`, removed at process exit.
pub fn process_scoped(prefix: &str) -> PathBuf {
    let path = tempfile::Builder::new()
        .prefix(prefix)
        .tempdir()
        .unwrap_or_else(|error| panic!("create a unique {prefix}* scratch directory: {error}"))
        .keep();
    let mut first = false;
    PATHS
        .get_or_init(|| {
            first = true;
            Mutex::new(Vec::new())
        })
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .push(path.clone());
    #[cfg(unix)]
    if first {
        // SAFETY: `remove_registered` takes no arguments and only reads a
        // static and the environment; registering it has no other effect.
        unsafe {
            libc::atexit(remove_registered);
        }
    }
    #[cfg(not(unix))]
    let _ = first;
    path
}
