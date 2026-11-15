// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Per-call scratch directories for tests that compile, link and run fixtures.
//!
//! A name built from the process id and a wall-clock stamp is NOT unique: the
//! tests of one binary share the pid and run on parallel threads, and the
//! realtime clock is coarse (on macOS it advances in whole microseconds, so
//! consecutive readings repeat). Two threads that stamp in the same tick build
//! the same path; `create_dir` then fails with `AlreadyExists`, and
//! `create_dir_all` silently hands both tests one directory to overwrite.
//!
//! [`create`] makes the directory with an exclusive `mkdir` under a random
//! name, retrying on collision, so every call owns a directory no other call
//! can be given. It returns a [`ScratchDir`] that owns the directory (RAII):
//! dropping it removes the directory and everything in it, on success and on
//! failure alike, so a test run leaves nothing in the temporary directory.
//! A failing test's directory is kept for inspection only when the
//! `TRUST_CG_KEEP_TEST_OBJECTS` environment variable is set (to anything);
//! the kept path is printed. The Darwin floor never passes that variable on,
//! and fails a target that leaves anything in its TMPDIR.

// Declared unconditionally; a target whose callers are all cfg'd out for this
// host must not trip the workspace's `warnings = "deny"`.
#![allow(dead_code)]

use std::ffi::OsStr;
use std::fmt;
use std::ops::Deref;
use std::path::{Path, PathBuf};

/// The environment variable that keeps a failing test's scratch directory.
pub const KEEP_ON_FAILURE: &str = "TRUST_CG_KEEP_TEST_OBJECTS";

/// A scratch directory this test owns. It dereferences to its path (a
/// [`PathBuf`], so `&dir` still coerces where a `&PathBuf` or `&Path` is
/// taken and `dir.clone()` is the path), and dropping it removes the directory
/// unless the test is failing and [`KEEP_ON_FAILURE`] is set.
pub struct ScratchDir {
    directory: Option<tempfile::TempDir>,
    path: PathBuf,
}

impl ScratchDir {
    /// The directory's path.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Give up ownership: the directory is no longer removed, and its path is
    /// returned. Only for an explicit, documented request to retain evidence
    /// (such as a test's `TCG_RETAIN_TEST_EVIDENCE`).
    pub fn keep(mut self) -> PathBuf {
        if let Some(directory) = self.directory.take() {
            let _ = directory.keep();
        }
        self.path.clone()
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
        // Otherwise `directory` is dropped here, which removes it (a missing
        // directory, one the test already removed, is not an error).
    }
}

/// A directory for a fixture every test of this process shares (a runtime
/// library built once and loaded, say), which no single test can own. It is
/// removed when the process exits, after every test has finished: libtest
/// exits the process normally after a failing test too, so only a killed
/// process leaves it. [`KEEP_ON_FAILURE`] set keeps it.
pub fn process_scoped(prefix: &str) -> PathBuf {
    use std::sync::{Mutex, OnceLock, PoisonError};
    static PATHS: OnceLock<Mutex<Vec<PathBuf>>> = OnceLock::new();
    extern "C" fn remove_registered() {
        if std::env::var_os(KEEP_ON_FAILURE).is_some() {
            return;
        }
        if let Some(paths) = PATHS.get() {
            for path in paths.lock().unwrap_or_else(PoisonError::into_inner).iter() {
                let _ = std::fs::remove_dir_all(path);
            }
        }
    }
    unsafe extern "C" {
        fn atexit(callback: extern "C" fn()) -> std::ffi::c_int;
    }
    let path = create(prefix).keep();
    let mut first = false;
    PATHS
        .get_or_init(|| {
            first = true;
            Mutex::new(Vec::new())
        })
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .push(path.clone());
    if first {
        // SAFETY: `remove_registered` takes no arguments and only reads a
        // static and the environment; registering it has no other effect.
        unsafe {
            atexit(remove_registered);
        }
    }
    path
}

/// Create a new directory under the system temporary directory whose name
/// starts with `prefix`, owned by the returned [`ScratchDir`]. Panics if it
/// cannot be created.
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
