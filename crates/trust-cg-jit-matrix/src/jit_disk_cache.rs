// trust-cg-jit-matrix/src/jit_disk_cache.rs - Persistent on-disk
// content-addressed cache of trust-ir module text for JIT BCP kernels.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// # Why this exists
//
// The in-memory `JitCompileCache` in `jit_compile_cache.rs` amortizes
// JIT compile cost across solves within a single process. SAT-Comp,
// however, launches a fresh process per instance, so the in-memory
// cache always starts cold. This module persists the trust-ir module
// text (the format consumed by `Compiler::compile_module_to_jit`) to
// `$XDG_CACHE_HOME/trust-cg/jit/<hash>-<kernel>-<builder-id>.trust_ir` (or
// `~/.cache/trust-cg/jit/` when XDG is not set), so cross-process
// invocations can skip module construction and re-enter the JIT
// compiler directly with the cached IR.
//
// # Scope of savings
//
// The disk cache stores the IR module text, NOT the final
// ExecutableBuffer. A disk hit eliminates the per-kernel module-build
// step (the call to `build_bcp_propagate_*_module()`); it does NOT
// eliminate ISel + regalloc + encoding (the bulk of compile cost per
// TT's profile, with regalloc alone at ~58%). The savings are smaller
// than a full ExecutableBuffer cache would be, but the implementation
// remains machine-code independent because trust-ir text is a stable
// interchange format. The filename nevertheless carries the complete local
// builder/pipeline source identity: a compiler, schema, feature, or module-
// builder change must be a cold miss rather than replaying stale semantics.
//
// # Failure mode
//
// Every disk I/O failure in this module degrades to "act as if the
// disk cache did not exist": missing directories, permission errors,
// unreadable files, corrupt content, and concurrent-writer races all
// fall back to a fresh in-process compile. The kernel-construction
// path therefore NEVER fails because of disk issues - it only fails
// because of an actual JIT-compile error.

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::SystemTime;

use sha2::{Digest, Sha256};

/// Default eviction bound: keep at most this many cached IR files on
/// disk. The watched-literal kernel's text representation is currently
/// on the order of ~40 KB, so 256 entries is comfortably below 16 MB
/// of disk usage even across all three kernel variants.
pub const DEFAULT_DISK_CACHE_FILE_LIMIT: usize = 256;

/// Stable subdirectory under the user cache root. Picked to avoid
/// collision with any future trust-cg artifact directories (object
/// files, replay bundles, etc.).
const DISK_CACHE_SUBDIR: &str = "trust-cg/jit";

/// Filename extension for cached IR text. The file contains the
/// integrity envelope described by [`CACHE_ENTRY_MAGIC`], not bare
/// Trust-IR text; [`disk_lookup`] validates and unwraps it before the
/// compiler sees the payload.
const DISK_CACHE_EXT: &str = "trust_ir";

/// On-disk IR-text cache envelope. All integers are little-endian:
///
/// ```text
/// 0       8       magic = b"TCGIRTXT"
/// 8       4       schema version (u32)
/// 12      8       payload length (u64)
/// 20      32      SHA-256(payload)
/// 52      ...     UTF-8 Trust-IR module text
/// ```
///
/// The schema and exact length make format changes and truncation fail
/// closed; the digest rejects otherwise well-formed corruption or
/// substitution. The filename independently carries the complete local
/// builder/pipeline identity.
const CACHE_ENTRY_MAGIC: &[u8; 8] = b"TCGIRTXT";
const CACHE_ENTRY_SCHEMA: u32 = 1;
const CACHE_ENTRY_HEADER_LEN: usize = CACHE_ENTRY_MAGIC.len() + 4 + 8 + 32;

/// Environment variable that gates *all* disk-cache I/O. When unset
/// (the default), every `disk_lookup` and `disk_store` returns the
/// "cache absent" answer without touching the filesystem. This keeps
/// `cargo test` runs from writing to a developer's real
/// `~/.cache/trust-cg/jit/` directory just because some test path
/// exercises a `compile_or_get_cached` code path.
///
/// Set this variable to `1` in production SAT-Comp launchers, bench
/// scripts, and the small number of in-tree tests that intentionally
/// exercise the disk cache (those also call
/// [`set_disk_cache_root_for_tests`] to redirect the root to a
/// per-test tempdir, so concurrent test runners do not collide).
pub const DISK_CACHE_ENABLE_ENV: &str = "TRUST_CG_JIT_DISK_CACHE";

/// Override hook for tests. When set (via `set_disk_cache_root_for_tests`)
/// the disk cache uses this directory instead of the XDG-derived path.
/// Setting an override also implicitly enables disk I/O for the
/// current process (the test wants disk behaviour or it would not
/// have set the override).
static DISK_CACHE_ROOT_OVERRIDE: OnceLock<std::sync::Mutex<Option<PathBuf>>> = OnceLock::new();

/// Monotonic same-process discriminator for atomic-write staging files.
/// Filesystem clocks can return the same nanosecond value to concurrent
/// threads, so PID + timestamp alone is not a unique staging name.
static NEXT_TEMP_FILE_DISCRIMINATOR: AtomicU64 = AtomicU64::new(0);

fn override_slot() -> &'static std::sync::Mutex<Option<PathBuf>> {
    DISK_CACHE_ROOT_OVERRIDE.get_or_init(|| std::sync::Mutex::new(None))
}

/// Returns true when disk I/O is allowed. Disk I/O is allowed when
/// EITHER the override is set (tests that have opted in) OR the
/// `TRUST_CG_JIT_DISK_CACHE` env var is set to a non-empty value
/// other than `0`/`false`/`off` (production / bench launchers).
fn disk_io_enabled() -> bool {
    if let Ok(guard) = override_slot().lock()
        && guard.is_some()
    {
        return true;
    }
    match crate::env_lock::var(DISK_CACHE_ENABLE_ENV) {
        Ok(val) => {
            let v = val.trim().to_ascii_lowercase();
            !v.is_empty() && v != "0" && v != "false" && v != "off"
        }
        Err(_) => false,
    }
}

/// Force the disk cache to use `path` as its root for the remainder of
/// the process. Intended for tests only. Pass `None` to clear the
/// override and resume XDG-based resolution.
pub fn set_disk_cache_root_for_tests(path: Option<PathBuf>) {
    if let Ok(mut guard) = override_slot().lock() {
        *guard = path;
    }
}

/// Resolve the on-disk cache directory. Returns the override path when
/// set; otherwise consults `$XDG_CACHE_HOME` and falls back to
/// `$HOME/.cache/trust-cg/jit`. Returns `None` when neither variable is
/// usable, which the caller treats as a cold miss with no error.
pub fn disk_cache_dir() -> Option<PathBuf> {
    if let Ok(guard) = override_slot().lock()
        && let Some(p) = guard.as_ref()
    {
        return Some(p.clone());
    }
    if let Some(root) = std::env::var_os("XDG_CACHE_HOME") {
        let p = PathBuf::from(root);
        if !p.as_os_str().is_empty() {
            return Some(p.join(DISK_CACHE_SUBDIR));
        }
    }
    if let Some(home) = std::env::var_os("HOME") {
        let p = PathBuf::from(home);
        if !p.as_os_str().is_empty() {
            return Some(p.join(".cache").join(DISK_CACHE_SUBDIR));
        }
    }
    None
}

/// Build the per-(hash, kernel, builder-identity) filename. Kernel name is included as a
/// suffix because the three BCP kernels emit different IR; the same
/// formula hash must produce three distinct files when the caller asks
/// for `scan`, `with-decisions`, and `watched-literal` respectively. The
/// stable build identity covers this crate's module builders plus the full
/// local lowering/codegen/schema source closure, so a valid-but-stale Trust-IR
/// module can never survive a semantic source update under the same formula
/// slot. Runtime codegen controls and detected CPU features are deliberately
/// excluded because every hit is recompiled under the current configuration.
fn cache_filename(hash: u64, kernel_name: &str) -> String {
    cache_filename_with_identity(
        hash,
        kernel_name,
        &crate::executable_buffer_cache::ir_builder_version_hash(),
    )
}

fn cache_filename_with_identity(
    hash: u64,
    kernel_name: &str,
    builder_identity: &[u8; 32],
) -> String {
    let identity = builder_identity
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    format!("{hash:016x}-{kernel_name}-{identity}.{DISK_CACHE_EXT}")
}

fn cache_path(hash: u64, kernel_name: &str) -> Option<PathBuf> {
    Some(disk_cache_dir()?.join(cache_filename(hash, kernel_name)))
}

fn temporary_cache_filename(
    hash: u64,
    kernel_name: &str,
    pid: u32,
    timestamp_nanos: u128,
) -> String {
    let discriminator = NEXT_TEMP_FILE_DISCRIMINATOR.fetch_add(1, Ordering::Relaxed);
    format!(
        "{}.tmp.{pid}.{timestamp_nanos}.{discriminator}",
        cache_filename(hash, kernel_name)
    )
}

/// Ensure the cache directory exists. Idempotent: a pre-existing
/// directory is success; a creation failure is logged once and treated
/// as "no disk cache available". Returns `Some(path)` when the
/// directory is ready for use.
fn ensure_cache_dir() -> Option<PathBuf> {
    let dir = disk_cache_dir()?;
    match fs::create_dir_all(&dir) {
        Ok(()) => Some(dir),
        Err(err) => {
            eprintln!(
                "trust-cg jit disk cache: failed to create {} ({err}); falling back to in-memory only",
                dir.display()
            );
            None
        }
    }
}

/// Attempt to read the trust-ir text for `(hash, kernel_name)`.
/// Returns `None` on any failure (missing file, permission error,
/// unreadable bytes) and also when disk I/O has not been enabled for
/// this process via `TRUST_CG_JIT_DISK_CACHE` or a test override. On
/// success, also bumps the file's mtime so touch-based LRU sees it
/// as recently used.
pub fn disk_lookup(hash: u64, kernel_name: &str) -> Option<String> {
    if !disk_io_enabled() {
        return None;
    }
    let path = cache_path(hash, kernel_name)?;
    let encoded = fs::read(&path).ok()?;
    let text = match decode_cache_entry(&encoded) {
        Some(text) => text,
        None => {
            // Cache entries are disposable. Once bytes have been read and
            // proven malformed, remove them so every future lookup does not
            // repeat the same failed validation. A concurrent writer uses an
            // atomic rename, so readers never observe its partial staging
            // file; removal is best-effort and semantically only a cold miss.
            let _ = fs::remove_file(&path);
            return None;
        }
    };
    // Touch mtime via a no-op rewrite. Avoid `filetime` crate so we
    // stay zero-dependency. Best-effort: ignore failures.
    let _ = touch(&path);
    Some(text)
}

fn encode_cache_entry(module_text: &str) -> Option<Vec<u8>> {
    let payload = module_text.as_bytes();
    let payload_len = u64::try_from(payload.len()).ok()?;
    let capacity = CACHE_ENTRY_HEADER_LEN.checked_add(payload.len())?;
    let digest = Sha256::digest(payload);

    let mut encoded = Vec::with_capacity(capacity);
    encoded.extend_from_slice(CACHE_ENTRY_MAGIC);
    encoded.extend_from_slice(&CACHE_ENTRY_SCHEMA.to_le_bytes());
    encoded.extend_from_slice(&payload_len.to_le_bytes());
    encoded.extend_from_slice(&digest);
    encoded.extend_from_slice(payload);
    Some(encoded)
}

fn decode_cache_entry(encoded: &[u8]) -> Option<String> {
    if encoded.len() < CACHE_ENTRY_HEADER_LEN
        || &encoded[..CACHE_ENTRY_MAGIC.len()] != CACHE_ENTRY_MAGIC
    {
        return None;
    }

    let schema_offset = CACHE_ENTRY_MAGIC.len();
    let schema = u32::from_le_bytes(encoded[schema_offset..schema_offset + 4].try_into().ok()?);
    if schema != CACHE_ENTRY_SCHEMA {
        return None;
    }

    let length_offset = schema_offset + 4;
    let payload_len =
        u64::from_le_bytes(encoded[length_offset..length_offset + 8].try_into().ok()?);
    let payload_len = usize::try_from(payload_len).ok()?;
    let expected_len = CACHE_ENTRY_HEADER_LEN.checked_add(payload_len)?;
    if encoded.len() != expected_len {
        return None;
    }

    let digest_offset = length_offset + 8;
    let expected_digest = &encoded[digest_offset..digest_offset + 32];
    let payload = &encoded[CACHE_ENTRY_HEADER_LEN..];
    let actual_digest = Sha256::digest(payload);
    if actual_digest.as_slice() != expected_digest {
        return None;
    }

    String::from_utf8(payload.to_vec()).ok()
}

/// Persist `module_text` for `(hash, kernel_name)` inside a versioned,
/// SHA-256-protected envelope. Creates the cache directory if needed.
/// Writes atomically via tmpfile + rename so a concurrent reader never
/// observes a partial file. Failures are logged (once per call site) but
/// never propagated; the caller's compile proceeds normally on a write
/// error.
pub fn disk_store(hash: u64, kernel_name: &str, module_text: &str) {
    if !disk_io_enabled() {
        return;
    }
    let dir = match ensure_cache_dir() {
        Some(d) => d,
        None => return,
    };
    let final_path = dir.join(cache_filename(hash, kernel_name));

    // The monotonic discriminator guarantees that same-process writers do not
    // collide even when the filesystem clock returns the same timestamp.
    let nanos = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let pid = std::process::id();
    let tmp_name = temporary_cache_filename(hash, kernel_name, pid, nanos);
    let tmp_path = dir.join(&tmp_name);

    let encoded = match encode_cache_entry(module_text) {
        Some(encoded) => encoded,
        None => return,
    };

    let write_res: std::io::Result<()> = (|| {
        let mut f = fs::File::create(&tmp_path)?;
        f.write_all(&encoded)?;
        f.sync_data()?;
        drop(f);
        // rename is atomic within the same directory on POSIX. On
        // Linux/macOS this overwrites any existing destination, which
        // is exactly the "last writer wins" semantics we want for the
        // concurrent-writers test. If two writers race, both produce
        // identical bytes (the module builder is deterministic for a
        // given kernel) so the observed content is always valid IR.
        fs::rename(&tmp_path, &final_path)?;
        Ok(())
    })();

    if let Err(err) = write_res {
        eprintln!(
            "trust-cg jit disk cache: failed to write {} ({err}); continuing without persistence",
            final_path.display()
        );
        // Best-effort cleanup of any leftover tmpfile.
        let _ = fs::remove_file(&tmp_path);
    } else {
        // Successful write: prune to enforce the file-count cap. The
        // bound is set above the steady-state corpus size for the
        // benchmark workloads we care about, so eviction is rare in
        // practice. Failures here are logged but never propagated.
        if let Err(err) = enforce_file_cap(&dir, DEFAULT_DISK_CACHE_FILE_LIMIT) {
            eprintln!(
                "trust-cg jit disk cache: eviction sweep on {} failed ({err}); cache may exceed cap",
                dir.display()
            );
        }
    }
}

/// Bump the mtime of `path` to "now" without changing its contents.
///
/// Merely opening a file for append does not update `st_mtime` on POSIX; an
/// actual write is required. Rewrite the first byte with its existing value so
/// the integrity envelope remains byte-identical while the LRU timestamp moves
/// forward. Cache entries always contain a non-empty envelope, but retaining the
/// empty-file branch keeps this helper harmless for malformed inputs.
fn touch(path: &Path) -> std::io::Result<()> {
    use std::io::{Read, Seek, SeekFrom};

    let mut file = fs::OpenOptions::new().read(true).write(true).open(path)?;
    let mut first = [0u8; 1];
    if file.read(&mut first)? == 1 {
        file.seek(SeekFrom::Start(0))?;
        file.write_all(&first)?;
        file.flush()?;
    }
    Ok(())
}

/// Remove the oldest cached IR files until the directory holds no
/// more than `cap` entries with the `.trust_ir` extension. Files are
/// ordered by mtime ascending; ties broken by filename so the result
/// is deterministic. Non-cache files in the directory (e.g.
/// leftover `.tmp` files from a crashed writer) are also pruned when
/// they have a mtime older than the oldest retained entry.
fn enforce_file_cap(dir: &Path, cap: usize) -> std::io::Result<()> {
    let mut entries: Vec<(PathBuf, SystemTime, bool)> = Vec::new();
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        let meta = match entry.metadata() {
            Ok(m) => m,
            Err(_) => continue,
        };
        if !meta.is_file() {
            continue;
        }
        let mtime = meta.modified().unwrap_or(SystemTime::UNIX_EPOCH);
        let is_cache_file = path
            .extension()
            .and_then(|s| s.to_str())
            .map(|s| s == DISK_CACHE_EXT)
            .unwrap_or(false);
        // Also clean obviously stale tmpfiles older than five minutes.
        let is_stale_tmp = path
            .file_name()
            .and_then(|s| s.to_str())
            .map(|s| s.contains(".tmp."))
            .unwrap_or(false)
            && SystemTime::now()
                .duration_since(mtime)
                .map(|d| d.as_secs() > 300)
                .unwrap_or(false);
        if is_cache_file || is_stale_tmp {
            entries.push((path, mtime, is_cache_file));
        }
    }
    // Always remove stale tmpfiles regardless of cap.
    entries.retain(|(p, _m, is_cache)| {
        if !*is_cache {
            let _ = fs::remove_file(p);
            false
        } else {
            true
        }
    });
    if entries.len() <= cap {
        return Ok(());
    }
    // Sort by mtime ascending; tie-break by path string so the
    // eviction order is reproducible across platforms that may report
    // identical mtimes.
    entries.sort_by(|a, b| a.1.cmp(&b.1).then(a.0.cmp(&b.0)));
    let to_remove = entries.len() - cap;
    for (path, _mtime, _is_cache) in entries.iter().take(to_remove) {
        let _ = fs::remove_file(path);
    }
    Ok(())
}

/// Clear all `.trust_ir` files in the disk cache directory. Used by
/// tests and exposed via the public crate API so harnesses can reset
/// disk state between scenarios. Missing directory is treated as
/// success (already clear). When disk I/O is not enabled for this
/// process, the call is a no-op.
pub fn clear_disk_cache() {
    if !disk_io_enabled() {
        return;
    }
    let dir = match disk_cache_dir() {
        Some(d) => d,
        None => return,
    };
    let read = match fs::read_dir(&dir) {
        Ok(r) => r,
        Err(_) => return,
    };
    for entry in read.flatten() {
        let path = entry.path();
        let is_cache_file = path
            .extension()
            .and_then(|s| s.to_str())
            .map(|s| s == DISK_CACHE_EXT)
            .unwrap_or(false);
        if is_cache_file {
            let _ = fs::remove_file(&path);
        }
    }
}

/// Count the number of `.trust_ir` files currently on disk. Test-facing.
pub fn disk_cache_file_count() -> usize {
    let dir = match disk_cache_dir() {
        Some(d) => d,
        None => return 0,
    };
    let read = match fs::read_dir(&dir) {
        Ok(r) => r,
        Err(_) => return 0,
    };
    read.flatten()
        .filter(|e| {
            e.path()
                .extension()
                .and_then(|s| s.to_str())
                .map(|s| s == DISK_CACHE_EXT)
                .unwrap_or(false)
        })
        .count()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;
    use tempfile::TempDir;

    /// Process-global serialization for any test that mutates the
    /// disk-cache root override. Tests in this module run in parallel
    /// by default and the override slot is shared; without this
    /// guard, two tests could clobber each other's tempdir choice.
    /// Held for the lifetime of the guard, dropped at test exit.
    static TEST_SERIAL: Mutex<()> = Mutex::new(());

    /// Guard that points the disk cache at a private tempdir for the
    /// duration of a single test and restores the previous override
    /// when dropped. Holds `TEST_SERIAL` so concurrent test threads
    /// see consistent disk state.
    struct CacheRootGuard {
        _tmp: TempDir,
        previous: Option<PathBuf>,
        _serial: std::sync::MutexGuard<'static, ()>,
    }

    impl CacheRootGuard {
        fn new() -> Self {
            let serial = TEST_SERIAL
                .lock()
                .unwrap_or_else(|poison| poison.into_inner());
            let tmp = TempDir::new().expect("create tempdir for disk cache test");
            let previous = override_slot().lock().ok().and_then(|g| g.clone());
            set_disk_cache_root_for_tests(Some(tmp.path().to_path_buf()));
            Self {
                _tmp: tmp,
                previous,
                _serial: serial,
            }
        }
    }

    impl Drop for CacheRootGuard {
        fn drop(&mut self) {
            set_disk_cache_root_for_tests(self.previous.clone());
        }
    }

    #[test]
    fn store_then_lookup_roundtrips() {
        let _g = CacheRootGuard::new();
        disk_store(42, "test-kernel", "module text body");
        let got = disk_lookup(42, "test-kernel").expect("expected disk hit after store");
        assert_eq!(got, "module text body");

        let encoded = fs::read(cache_path(42, "test-kernel").expect("cache path"))
            .expect("read stored envelope");
        assert_eq!(&encoded[..CACHE_ENTRY_MAGIC.len()], CACHE_ENTRY_MAGIC);
        assert_ne!(encoded, b"module text body");
    }

    #[test]
    fn lookup_touch_refreshes_lru_without_changing_integrity_envelope() {
        use std::fs::FileTimes;
        use std::time::Duration;

        fn set_modified(path: &Path, when: SystemTime) {
            fs::OpenOptions::new()
                .read(true)
                .write(true)
                .open(path)
                .expect("open cache entry to set deterministic mtime")
                .set_times(FileTimes::new().set_modified(when))
                .expect("set deterministic cache-entry mtime");
        }

        let _g = CacheRootGuard::new();
        let touched_hash = 0x000a_11ce_u64;
        let untouched_hash = 0xb0b_u64;
        let kernel = "touch-lru";
        disk_store(touched_hash, kernel, "touched payload");
        disk_store(untouched_hash, kernel, "untouched payload");

        let touched_path = cache_path(touched_hash, kernel).expect("touched cache path");
        let untouched_path = cache_path(untouched_hash, kernel).expect("untouched cache path");
        let original_envelope = fs::read(&touched_path).expect("read original cache envelope");

        // Pin both mtimes far in the past so this test does not depend on sleeps
        // or the filesystem's timestamp resolution. Before lookup, `touched` is
        // deliberately the older entry and therefore the eviction candidate.
        set_modified(
            &touched_path,
            SystemTime::UNIX_EPOCH + Duration::from_secs(1),
        );
        set_modified(
            &untouched_path,
            SystemTime::UNIX_EPOCH + Duration::from_secs(2),
        );
        let untouched_mtime = fs::metadata(&untouched_path)
            .and_then(|meta| meta.modified())
            .expect("read untouched cache-entry mtime");

        assert_eq!(
            disk_lookup(touched_hash, kernel).as_deref(),
            Some("touched payload")
        );
        let refreshed_mtime = fs::metadata(&touched_path)
            .and_then(|meta| meta.modified())
            .expect("read refreshed cache-entry mtime");
        assert!(
            refreshed_mtime > untouched_mtime,
            "a cache hit must move the entry ahead of an untouched peer in LRU order"
        );
        assert_eq!(
            fs::read(&touched_path).expect("read touched cache envelope"),
            original_envelope,
            "touching an entry must leave its integrity envelope byte-identical"
        );

        enforce_file_cap(&disk_cache_dir().expect("disk cache dir"), 1)
            .expect("evict oldest cache entry");
        assert!(
            touched_path.exists(),
            "the just-read entry must survive LRU eviction"
        );
        assert!(
            !untouched_path.exists(),
            "the untouched entry must be the LRU eviction victim"
        );
    }

    #[test]
    fn valid_envelope_with_invalid_ir_is_replaced_after_fresh_build() {
        use std::cell::Cell;

        use trust_cg_codegen::pipeline::{encode_trust_ir_text, parse_trust_ir_text};

        use crate::bcp_module_builder::build_bcp_propagate_module;
        use crate::jit_compile_cache::{JitCompileCache, formula_key_hex};

        let _g = CacheRootGuard::new();
        let hash = 0x0051_a7e1_u64;
        let formula_key = [0x5au8; 32];
        let kernel_name = "semantic-poison";
        let disk_kernel = format!("{kernel_name}-{}", formula_key_hex(&formula_key));
        let poisoned_text = "; TrustIr text format v1\nthis is not a module\n";

        // `disk_store` constructs a valid schema/length/digest envelope. The
        // payload therefore reaches the module parser even though it is not
        // syntactically valid Trust-IR.
        disk_store(hash, &disk_kernel, poisoned_text);
        assert_eq!(
            disk_lookup(hash, &disk_kernel).as_deref(),
            Some(poisoned_text),
            "the integrity layer alone must accept this deliberately poisoned payload"
        );

        let rebuilds = Cell::new(0usize);
        let mut cache = JitCompileCache::<String>::new(1);
        let compile = |cache: &mut JitCompileCache<String>| {
            cache.get_or_compile_with_buffer_disk(
                hash,
                formula_key,
                kernel_name,
                |_buffer| -> Result<String, &'static str> {
                    Err("the quarantined executable tier must remain cold")
                },
                |disk_text| -> Result<(String, Vec<u8>, String), &'static str> {
                    let (module, module_text) = match disk_text {
                        Some(text) => match parse_trust_ir_text(&text) {
                            Ok(module) => (module, text),
                            Err(_) => {
                                rebuilds.set(rebuilds.get() + 1);
                                let module = build_bcp_propagate_module();
                                let text = encode_trust_ir_text(&module);
                                (module, text)
                            }
                        },
                        None => {
                            rebuilds.set(rebuilds.get() + 1);
                            let module = build_bcp_propagate_module();
                            let text = encode_trust_ir_text(&module);
                            (module, text)
                        }
                    };
                    let _ = module;
                    Ok(("compiled".to_owned(), Vec::new(), module_text))
                },
            )
        };

        compile(&mut cache).expect("poisoned entry must fall back to a fresh build");
        assert_eq!(rebuilds.get(), 1);
        let repaired = disk_lookup(hash, &disk_kernel).expect("fresh IR must replace poison");
        assert_ne!(repaired, poisoned_text);
        parse_trust_ir_text(&repaired).expect("replacement must be parseable Trust-IR");

        // Simulate the next process. Its L3 hit must consume the repaired
        // payload directly instead of rebuilding the same poisoned slot again.
        cache.clear();
        compile(&mut cache).expect("repaired entry must be reusable");
        assert_eq!(
            rebuilds.get(),
            1,
            "a repaired entry must not poison every subsequent process"
        );
    }

    #[test]
    fn payload_mutation_is_cold_miss_and_removes_entry() {
        let _g = CacheRootGuard::new();
        disk_store(43, "mutated-kernel", "valid ascii module text");
        let path = cache_path(43, "mutated-kernel").expect("cache path");
        let mut encoded = fs::read(&path).expect("read stored envelope");
        let payload_byte = encoded
            .last_mut()
            .expect("stored envelope has a non-empty payload");
        *payload_byte ^= 1;
        fs::write(&path, encoded).expect("mutate cached payload");

        assert!(
            disk_lookup(43, "mutated-kernel").is_none(),
            "digest mismatch must be a cold miss"
        );
        assert!(
            !path.exists(),
            "a proven-corrupt cache entry should be removed"
        );
    }

    #[test]
    fn truncated_envelope_is_cold_miss_and_removes_entry() {
        let _g = CacheRootGuard::new();
        disk_store(44, "truncated-kernel", "module text that will be truncated");
        let path = cache_path(44, "truncated-kernel").expect("cache path");
        let mut encoded = fs::read(&path).expect("read stored envelope");
        encoded.pop().expect("stored envelope is non-empty");
        fs::write(&path, encoded).expect("truncate cached envelope");

        assert!(
            disk_lookup(44, "truncated-kernel").is_none(),
            "declared length mismatch must be a cold miss"
        );
        assert!(
            !path.exists(),
            "a proven-truncated cache entry should be removed"
        );
    }

    #[test]
    fn unknown_schema_is_rejected() {
        let mut encoded = encode_cache_entry("module text").expect("encode cache entry");
        let schema_offset = CACHE_ENTRY_MAGIC.len();
        encoded[schema_offset..schema_offset + 4]
            .copy_from_slice(&(CACHE_ENTRY_SCHEMA + 1).to_le_bytes());
        assert!(decode_cache_entry(&encoded).is_none());
    }

    #[test]
    fn lookup_missing_returns_none() {
        let _g = CacheRootGuard::new();
        assert!(disk_lookup(0xdeadbeef, "test-kernel").is_none());
    }

    #[test]
    fn builder_identity_partitions_valid_ir_text_slots() {
        let first = cache_filename_with_identity(42, "scan", &[0x11; 32]);
        let second = cache_filename_with_identity(42, "scan", &[0x22; 32]);
        assert_ne!(first, second, "builder changes must force a cold miss");
        assert!(first.contains(&"11".repeat(32)));
        assert!(second.contains(&"22".repeat(32)));
    }

    #[test]
    fn runtime_codegen_controls_do_not_rekey_ir_text_cache() {
        const CHILD_MODE_ENV: &str = "JIT_MATRIX_TEST_IR_CACHE_CHILD_MODE";
        const CHILD_ROOT_ENV: &str = "JIT_MATRIX_TEST_IR_CACHE_CHILD_ROOT";
        const TEST_NAME: &str =
            "jit_disk_cache::tests::runtime_codegen_controls_do_not_rekey_ir_text_cache";
        const HASH: u64 = 0xc01d_cac4e;
        const KERNEL: &str = "runtime-control-stable";
        const PAYLOAD: &str = "persisted Trust-IR is recompiled under live codegen controls";

        if let Some(mode) = std::env::var_os(CHILD_MODE_ENV) {
            let root = std::env::var_os(CHILD_ROOT_ENV)
                .map(PathBuf::from)
                .expect("child cache root");
            set_disk_cache_root_for_tests(Some(root));
            match mode.to_str() {
                Some("store") => {
                    disk_store(HASH, KERNEL, PAYLOAD);
                    assert_eq!(disk_lookup(HASH, KERNEL).as_deref(), Some(PAYLOAD));
                }
                Some("lookup") => {
                    assert_eq!(
                        disk_lookup(HASH, KERNEL).as_deref(),
                        Some(PAYLOAD),
                        "a runtime codegen-control change must not hide reusable Trust-IR text"
                    );
                }
                _ => panic!("unknown IR-cache child mode: {mode:?}"),
            }
            return;
        }

        let _serial = TEST_SERIAL
            .lock()
            .unwrap_or_else(|poison| poison.into_inner());
        let tmp = TempDir::new().expect("create tempdir for cross-process IR-cache test");
        let test_binary = std::env::current_exe().expect("resolve current test binary");

        // Scope each real backend control to a child process instead of
        // mutating this parallel test process's environment. Child exit makes
        // restoration unwind-safe even if either assertion fails.
        let run_child = |mode: &str, disabled_pass: &str| {
            std::process::Command::new(&test_binary)
                .arg(TEST_NAME)
                .arg("--exact")
                .arg("--nocapture")
                .arg("--test-threads=1")
                .env(CHILD_MODE_ENV, mode)
                .env(CHILD_ROOT_ENV, tmp.path())
                .env("TRUST_CG_DISABLE_PASSES", disabled_pass)
                .output()
                .expect("run isolated IR-cache child test")
        };
        let assert_success = |phase: &str, output: std::process::Output| {
            assert!(
                output.status.success(),
                "IR-cache {phase} child failed ({}):\nstdout:\n{}\nstderr:\n{}",
                output.status,
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
            );
        };

        assert_success("store", run_child("store", "aliashoist"));
        assert_success("lookup", run_child("lookup", "vec"));
    }

    #[test]
    fn temporary_filenames_remain_unique_when_clock_does_not_advance() {
        let first = temporary_cache_filename(42, "scan", 7, 11);
        let second = temporary_cache_filename(42, "scan", 7, 11);
        assert_ne!(
            first, second,
            "the atomic discriminator must separate same-PID, same-timestamp writers"
        );

        let common_prefix = format!("{}.tmp.7.11.", cache_filename(42, "scan"));
        assert!(first.starts_with(&common_prefix));
        assert!(second.starts_with(&common_prefix));
    }

    #[test]
    fn clear_removes_files() {
        let _g = CacheRootGuard::new();
        disk_store(1, "k1", "a");
        disk_store(2, "k2", "b");
        assert_eq!(disk_cache_file_count(), 2);
        clear_disk_cache();
        assert_eq!(disk_cache_file_count(), 0);
    }

    #[test]
    fn eviction_bounded_at_count() {
        let _g = CacheRootGuard::new();
        // Insert cap + extras and assert oldest get removed.
        let cap = 4;
        for k in 0..(cap + 3) {
            // Tiny pause so mtimes are distinguishable on
            // coarse-resolution filesystems (macOS HFS+ has 1s mtime
            // resolution; APFS has nanosecond resolution but CI may
            // still need a hint). The eviction sort breaks ties by
            // path so this is belt-and-braces.
            disk_store(k as u64, "k", &format!("payload-{k}"));
            std::thread::sleep(std::time::Duration::from_millis(2));
        }
        let dir = disk_cache_dir().unwrap();
        enforce_file_cap(&dir, cap).expect("enforce");
        assert_eq!(disk_cache_file_count(), cap);
        // The most-recently-stored entry must still be present.
        assert!(disk_lookup((cap + 2) as u64, "k").is_some());
        // The oldest entry must be gone.
        assert!(disk_lookup(0, "k").is_none());
    }

    #[test]
    fn concurrent_writes_do_not_corrupt() {
        let _g = CacheRootGuard::new();
        let threads: Vec<_> = (0..8)
            .map(|i| {
                std::thread::spawn(move || {
                    let payload = format!("payload-shared-{i}");
                    // All threads write to the SAME (hash, kernel)
                    // key. The atomic-rename guarantee is the
                    // contract under test: a reader must never see a
                    // partial file, and the final content must be one
                    // of the writers' payloads verbatim.
                    disk_store(7777, "k-concurrent", &payload);
                    disk_lookup(7777, "k-concurrent")
                })
            })
            .collect();
        let mut contents = Vec::new();
        for t in threads {
            if let Ok(Some(c)) = t.join() {
                contents.push(c);
            }
        }
        // Whatever any reader saw must be one of the writers' bytes.
        for c in &contents {
            assert!(
                c.starts_with("payload-shared-"),
                "observed corrupt content: {c:?}"
            );
        }
        // And the final on-disk content must also be a valid payload.
        let final_text = disk_lookup(7777, "k-concurrent").expect("file present after writers");
        assert!(final_text.starts_with("payload-shared-"));
    }

    #[test]
    fn missing_dir_is_cold_miss_not_error() {
        let _serial = TEST_SERIAL
            .lock()
            .unwrap_or_else(|poison| poison.into_inner());
        // Point at a directory we never create, then look up.
        let tmp = TempDir::new().expect("tempdir");
        let bogus = tmp.path().join("does-not-exist-yet");
        let previous = override_slot().lock().ok().and_then(|g| g.clone());
        set_disk_cache_root_for_tests(Some(bogus));
        assert!(disk_lookup(1, "k").is_none());
        // Storing into the same bogus dir should still succeed by
        // creating the dir on demand.
        disk_store(1, "k", "ok");
        assert!(disk_lookup(1, "k").is_some());
        set_disk_cache_root_for_tests(previous);
    }
}
