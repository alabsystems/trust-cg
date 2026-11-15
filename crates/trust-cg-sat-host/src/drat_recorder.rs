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
//     shared by the native solver callbacks).
//   - Buffers DRAT output through a `BufWriter<File>` so per-clause
//     overhead stays in the formatter rather than syscalls.
//   - Exposes `enable_drat_output(path)` / `disable_drat_output()` so
//     callers can toggle proof emission around a `solve` call and must check
//     finalization for any write failure observed inside a C callback.
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
pub struct DratRecorder<W: Write = File> {
    writer: BufWriter<W>,
    first_error: Option<(io::ErrorKind, String)>,
}

impl DratRecorder {
    fn new(path: &Path) -> io::Result<Self> {
        let file = File::create(path)?;
        Ok(Self {
            writer: BufWriter::new(file),
            first_error: None,
        })
    }
}

impl<W: Write> DratRecorder<W> {
    // C callbacks cannot return an I/O error to MicroSAT. Keep the first one
    // sticky: a transient write failure must not turn into an apparently
    // successful proof when a later flush happens to succeed.
    fn with_writer(
        &mut self,
        operation: impl FnOnce(&mut BufWriter<W>) -> io::Result<()>,
    ) -> io::Result<()> {
        if let Some((kind, message)) = &self.first_error {
            return Err(io::Error::new(*kind, message.clone()));
        }
        let result = operation(&mut self.writer);
        if let Err(error) = &result {
            self.first_error = Some((error.kind(), error.to_string()));
        }
        result
    }

    fn write_clause(&mut self, prefix: Option<&str>, lits: &[i32]) -> io::Result<()> {
        self.with_writer(|writer| {
            if let Some(p) = prefix {
                writer.write_all(p.as_bytes())?;
            }
            for lit in lits {
                write!(writer, "{} ", lit)?;
            }
            writer.write_all(b"0\n")
        })
    }

    /// Record an `addClause` event.
    pub fn record_add(&mut self, lits: &[i32]) -> io::Result<()> {
        self.write_clause(None, lits)
    }

    /// Record a `reduceDB`-driven clause deletion.
    pub fn record_delete(&mut self, lits: &[i32]) -> io::Result<()> {
        self.write_clause(Some("d "), lits)
    }

    /// Flush buffered bytes, reporting any earlier write failure as well.
    /// This is not an `fsync` or a proof-validity check.
    pub fn flush(&mut self) -> io::Result<()> {
        self.with_writer(Write::flush)
    }
}

impl<W: Write> Drop for DratRecorder<W> {
    fn drop(&mut self) {
        // Drop cannot report failure. Callers must use explicit flush or
        // disable/finalization before treating the output as complete.
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
/// Returns an `io::Error` if the previous recorder failed, the lock is poisoned,
/// or the new file cannot be created. A failed replacement leaves the previous
/// recorder active and does not create or truncate the new path.
pub fn enable_drat_output(path: &Path) -> io::Result<()> {
    let mut slot = global_slot()
        .lock()
        .map_err(|_| io::Error::other("DRAT recorder mutex poisoned"))?;
    if let Some(previous) = slot.as_mut() {
        previous.flush()?;
    }
    let recorder = DratRecorder::new(path)?;
    *slot = Some(recorder);
    Ok(())
}

/// Disable DRAT proof output. Flushes and drops the active recorder, if
/// any, returning any earlier callback or final flush failure. Detaches the
/// recorder even on an I/O error. No-op when no recorder is active.
pub fn disable_drat_output() -> io::Result<()> {
    let mut slot = global_slot()
        .lock()
        .map_err(|_| io::Error::other("DRAT recorder mutex poisoned"))?;
    if let Some(mut recorder) = slot.take() {
        recorder.flush()?;
    }
    Ok(())
}

/// Flush the active buffer to its file, including any prior callback error.
/// This does not synchronize storage or establish proof validity.
pub fn flush_drat_output() -> io::Result<()> {
    let mut slot = global_slot()
        .lock()
        .map_err(|_| io::Error::other("DRAT recorder mutex poisoned"))?;
    if let Some(recorder) = slot.as_mut() {
        recorder.flush()?;
    }
    Ok(())
}

/// Internal helper used by the C trampoline. Forwards an `addClause`
/// event into the active recorder. No-op if no recorder is attached.
fn record_add_internal(lits: &[i32]) {
    if let Ok(mut slot) = global_slot().lock()
        && let Some(recorder) = slot.as_mut()
    {
        // The recorder retains errors for explicit flush/finalization.
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
/// For positive `size`, the caller must ensure that `lits` points to at least `size`
/// readable `c_int` values and that the buffer is not concurrently
/// mutated for the duration of the call. MicroSAT's `addClause` reads
/// its `in` parameter only to copy it into the database, so the buffer
/// is stable for the call. A zero size records the empty clause and may use
/// a null pointer.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rs_drat_record_add(lits: *const core::ffi::c_int, size: core::ffi::c_int) {
    if size == 0 {
        record_add_internal(&[]);
        return;
    }
    if lits.is_null() || size < 0 {
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
    if size == 0 {
        record_delete_internal(&[]);
        return;
    }
    if lits.is_null() || size < 0 {
        return;
    }
    // SAFETY: as above.
    let slice = unsafe { core::slice::from_raw_parts(lits, size as usize) };
    record_delete_internal(slice);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::propagate::test_support::SOLVER_LOCK;

    #[derive(Default)]
    struct RecoveringWriter {
        fail_write: bool,
        fail_flush: bool,
        bytes: Vec<u8>,
    }

    impl Write for RecoveringWriter {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            if std::mem::take(&mut self.fail_write) {
                return Err(io::Error::other("injected write failure"));
            }
            self.bytes.extend_from_slice(bytes);
            Ok(bytes.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            if std::mem::take(&mut self.fail_flush) {
                return Err(io::Error::other("injected flush failure"));
            }
            Ok(())
        }
    }

    #[test]
    fn callback_write_failure_cannot_be_hidden_by_a_successful_later_flush() {
        let mut recorder = DratRecorder {
            writer: BufWriter::with_capacity(
                1,
                RecoveringWriter {
                    fail_write: true,
                    ..Default::default()
                },
            ),
            first_error: None,
        };
        let first = recorder.record_add(&[1, -2]).unwrap_err().to_string();
        assert_eq!(recorder.flush().unwrap_err().to_string(), first);
        assert_eq!(recorder.record_delete(&[3]).unwrap_err().to_string(), first);
        assert!(recorder.writer.get_ref().bytes.is_empty());
        // The underlying writer has recovered; the proof stream has not.
        recorder.writer.get_mut().flush().unwrap();
    }

    #[test]
    fn final_flush_failure_remains_sticky_after_writer_recovers() {
        let mut recorder = DratRecorder {
            writer: BufWriter::new(RecoveringWriter {
                fail_flush: true,
                ..Default::default()
            }),
            first_error: None,
        };
        recorder.record_add(&[]).unwrap();
        assert_eq!(
            recorder.flush().unwrap_err().to_string(),
            "injected flush failure"
        );
        recorder.writer.get_mut().flush().unwrap();
        assert_eq!(
            recorder.flush().unwrap_err().to_string(),
            "injected flush failure"
        );
        assert_eq!(recorder.writer.get_ref().bytes, b"0\n");
    }

    #[test]
    fn ffi_records_empty_clauses_without_dereferencing_null() {
        let _guard = SOLVER_LOCK.lock().unwrap();
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("empty.drat");
        enable_drat_output(&path).unwrap();
        // SAFETY: zero-length clauses require no readable pointer.
        unsafe {
            rs_drat_record_add(std::ptr::null(), 0);
            rs_drat_record_delete(std::ptr::null(), 0);
        }
        disable_drat_output().unwrap();
        assert_eq!(std::fs::read(path).unwrap(), b"0\nd 0\n");
    }

    #[test]
    fn failed_callback_blocks_replacement_and_finalization_reports_it() {
        let _guard = SOLVER_LOCK.lock().unwrap();
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("readonly.drat");
        let replacement = dir.path().join("preserved.drat");
        std::fs::write(&path, b"original").unwrap();
        std::fs::write(&replacement, b"preserve replacement").unwrap();
        *global_slot().lock().unwrap() = Some(DratRecorder {
            writer: BufWriter::with_capacity(1, File::open(&path).unwrap()),
            first_error: None,
        });
        // A read-only handle is a deterministic write failure on every host.
        record_add_internal(&[1]);
        let error = flush_drat_output().unwrap_err().to_string();
        assert_eq!(
            enable_drat_output(&replacement).unwrap_err().to_string(),
            error
        );
        assert_eq!(
            std::fs::read(&replacement).unwrap(),
            b"preserve replacement"
        );
        assert_eq!(disable_drat_output().unwrap_err().to_string(), error);
        assert!(global_slot().lock().unwrap().is_none());
        disable_drat_output().unwrap();
    }
}
