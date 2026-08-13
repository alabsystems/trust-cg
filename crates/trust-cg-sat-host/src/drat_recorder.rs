// trust-cg-sat-host - DRAT proof recorder.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Purpose
// -------
// Implements the Rust side of the DRAT trampoline. The C trampoline in
// `drat_trampoline.c` calls `rs_drat_record_add` and
// `rs_drat_record_delete` on every clause addition/deletion in MicroSAT.
// This module:
//
//   - Maintains a process-global `Option<DratRecorder>` behind a `Mutex`
//     (paired with `OnceLock` so the lock is initialised exactly once,
//     matching the pattern used elsewhere in the workspace, e.g.
//     `crates/trust-cg-jit-matrix/src/lib.rs` for `DISABLE_PASSES_ENV_LOCK`).
//   - Buffers DRAT output through a `BufWriter<File>` so per-clause
//     overhead stays in the formatter rather than syscalls.
//   - Exposes `enable_drat_output(path)` / `disable_drat_output()` so
//     callers can toggle proof emission around a `solve` call.
//
// DRAT format (see <https://github.com/marijnheule/drat-trim>):
//
//   - clause addition: `<lit1> <lit2> ... <litN> 0\n`
//   - clause deletion: `d <lit1> <lit2> ... <litN> 0\n`
//
// Literals are non-zero decimal integers (positive = variable true,
// negative = variable false). Zero terminates each line.

use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::path::Path;
use std::sync::{Mutex, OnceLock};

/// A live DRAT proof writer. Buffers writes through a `BufWriter<File>`
/// so each clause records as a small handful of `write_all` calls into
/// the buffer rather than a syscall per literal.
pub struct DratRecorder {
    writer: BufWriter<File>,
}

impl DratRecorder {
    fn new(path: &Path) -> io::Result<Self> {
        let file = File::create(path)?;
        Ok(Self {
            writer: BufWriter::new(file),
        })
    }

    fn write_clause(&mut self, prefix: Option<&str>, lits: &[i32]) -> io::Result<()> {
        if let Some(p) = prefix {
            self.writer.write_all(p.as_bytes())?;
        }
        for lit in lits {
            write!(self.writer, "{} ", lit)?;
        }
        self.writer.write_all(b"0\n")?;
        Ok(())
    }

    /// Record an `addClause` event.
    pub fn record_add(&mut self, lits: &[i32]) -> io::Result<()> {
        self.write_clause(None, lits)
    }

    /// Record a `reduceDB`-driven clause deletion.
    pub fn record_delete(&mut self, lits: &[i32]) -> io::Result<()> {
        self.write_clause(Some("d "), lits)
    }
}

impl Drop for DratRecorder {
    fn drop(&mut self) {
        // Best-effort flush on drop. If the underlying file is gone (e.g.
        // tempdir already torn down) we cannot do anything useful here
        // and propagating an error would require a custom destructor; we
        // explicitly ignore the result, matching the contract that the
        // caller is responsible for confirming on-disk durability.
        let _ = self.writer.flush();
    }
}

fn global_slot() -> &'static Mutex<Option<DratRecorder>> {
    static SLOT: OnceLock<Mutex<Option<DratRecorder>>> = OnceLock::new();
    SLOT.get_or_init(|| Mutex::new(None))
}

/// Enable DRAT proof output to `path`. Truncates any existing file at
/// that path. While enabled, every clause learned by MicroSAT and every
/// clause deletion triggered by `reduceDB` is recorded.
///
/// Returns an `io::Error` if the file cannot be created. Replaces any
/// previously enabled recorder; the previous file is flushed via the
/// recorder's `Drop` impl.
pub fn enable_drat_output(path: &Path) -> io::Result<()> {
    let recorder = DratRecorder::new(path)?;
    let mut slot = global_slot().lock().expect("DRAT recorder mutex poisoned");
    *slot = Some(recorder);
    Ok(())
}

/// Disable DRAT proof output. Flushes and drops the active recorder, if
/// any. Safe to call when no recorder is active (no-op in that case).
pub fn disable_drat_output() {
    let mut slot = global_slot().lock().expect("DRAT recorder mutex poisoned");
    *slot = None;
}

/// Flush the active recorder's buffer to disk. Useful in tests that want
/// to read the proof file before tearing down the recorder.
pub fn flush_drat_output() -> io::Result<()> {
    let mut slot = global_slot().lock().expect("DRAT recorder mutex poisoned");
    if let Some(recorder) = slot.as_mut() {
        recorder.writer.flush()?;
    }
    Ok(())
}

/// Internal helper used by the C trampoline. Forwards an `addClause`
/// event into the active recorder. No-op if no recorder is attached.
fn record_add_internal(lits: &[i32]) {
    if let Ok(mut slot) = global_slot().lock()
        && let Some(recorder) = slot.as_mut()
    {
        // Best-effort: if the disk fills or the file vanishes we have
        // no good way to surface the error from a C callback. Tests
        // call `flush_drat_output()` and then read the file to detect
        // truncation.
        let _ = recorder.record_add(lits);
    }
}

/// Internal helper used by the C trampoline. Forwards a `reduceDB`-driven
/// clause deletion event into the active recorder. No-op if no recorder
/// is attached.
fn record_delete_internal(lits: &[i32]) {
    if let Ok(mut slot) = global_slot().lock()
        && let Some(recorder) = slot.as_mut()
    {
        let _ = recorder.record_delete(lits);
    }
}

/// C-callable trampoline entry point invoked by `drat_trampoline.c`
/// inside `addClause`. The caller passes a pointer to the literal
/// buffer + the number of literals.
///
/// # Safety
///
/// The caller must ensure that `lits` points to at least `size`
/// readable `c_int` values and that the buffer is not concurrently
/// mutated for the duration of the call. MicroSAT's `addClause` reads
/// its `in` parameter only to copy it into the database, so the buffer
/// is stable for the call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rs_drat_record_add(lits: *const core::ffi::c_int, size: core::ffi::c_int) {
    if lits.is_null() || size <= 0 {
        return;
    }
    // SAFETY: precondition documented above. `size` is non-negative
    // after the guard, and `lits` is non-null. The slice has the same
    // lifetime as the call, which is shorter than MicroSAT's hold on
    // the buffer.
    let slice = unsafe { core::slice::from_raw_parts(lits, size as usize) };
    record_add_internal(slice);
}

/// C-callable trampoline entry point invoked by `drat_trampoline.c`
/// inside `reduceDB` for each lemma about to be removed.
///
/// # Safety
///
/// Same contract as [`rs_drat_record_add`]: `lits` must point to at
/// least `size` readable `c_int` values, not concurrently mutated.
/// `reduceDB` reads its own database before the bulk free, so the
/// buffer is stable for the call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rs_drat_record_delete(
    lits: *const core::ffi::c_int,
    size: core::ffi::c_int,
) {
    if lits.is_null() || size <= 0 {
        return;
    }
    // SAFETY: as above.
    let slice = unsafe { core::slice::from_raw_parts(lits, size as usize) };
    record_delete_internal(slice);
}
