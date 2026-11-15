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
// `~/.cache/trust-cg/jit/` when XDG_CACHE_HOME is not an absolute path), so cross-process
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
// Its payload is pre-codegen semantic TrustIR rather than executable bytes,
// but it is still an artifact of module construction. A future prefixed
// control could affect that builder, so lookup and publication share the same
// fail-closed environment guard as compiled-provider L1 and executable L2.
//
// # Custody
//
// A hit is parsed, JIT-compiled and executed, so an entry another user
// could plant would choose the code that runs. The cache is therefore used
// only from an owner-private canonical directory, the rule the TCJ2
// executable store holds (`private_fs::canonical_owner_private_directory`:
// every canonical ancestor owned by this user or root and renamable by
// nobody else, the directory itself not group/other-writable). A directory
// that fails is ignored, never repaired: lookups miss and nothing is written
// into it. Every entry is named from the canonical path the check returned,
// never from `$XDG_CACHE_HOME`'s spelling, which may lead there through a
// symlink another user can re-point. Each entry's integrity tag is an
// HMAC-SHA256 under a random 32-byte key kept beside the entries in an
// owner-private (`0600`) file (`IR_TEXT_SEAL_KEY_FILE`), over the entry's
// file name and payload, so an entry nobody holding that key wrote (an
// unkeyed digest anyone could recompute, before X-HOST-P13's fourth closure
// audit) misses instead of being compiled.
//
// # Failure mode
//
// Every disk I/O failure in this module degrades to "act as if the
// disk cache did not exist": missing directories, permission errors,
// unreadable files, corrupt content, a non-private directory, a missing or
// non-private seal key, and concurrent-writer races all fall back to a
// fresh in-process compile. The kernel-construction path therefore NEVER
// fails because of disk issues - it only fails because of an actual
// JIT-compile error.

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::SystemTime;

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
/// 20      32      HMAC-SHA256(seal key, domain || file name || payload length || payload)
/// 52      ...     UTF-8 Trust-IR module text
/// ```
///
/// The schema and exact length make format changes and truncation fail
/// closed; the keyed tag rejects corruption, substitution, an entry moved to
/// another slot's name, and an entry written by anyone without the seal key
/// (schema 1's unkeyed SHA-256 could be recomputed by whoever wrote the
/// file). The filename independently carries the complete local
/// builder/pipeline identity.
const CACHE_ENTRY_MAGIC: &[u8; 8] = b"TCGIRTXT";
const CACHE_ENTRY_SCHEMA: u32 = 2;
const CACHE_ENTRY_HEADER_LEN: usize = CACHE_ENTRY_MAGIC.len() + 4 + 8 + 32;
/// Domain separation of the entry tag from every other use of a seal key.
const CACHE_ENTRY_TAG_DOMAIN: &[u8] = b"trust-cg.jit-ir-text-cache.entry.v2\0";
/// The seal key's file in the cache directory: 32 random bytes, created
/// exclusively with mode `0600` and read only when this user owns it and no
/// other user can read or write it (the TCJ2 store's key discipline,
/// `executable_buffer_cache::open_seal_key`). Not a `.trust_ir` file, so no
/// eviction or clear removes it.
pub const IR_TEXT_SEAL_KEY_FILE: &str = "ir-text-seal.key";
/// An entry larger than this is refused before it is read.
const CACHE_ENTRY_MAX_BYTES: u64 = 64 << 20;

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
/// set; otherwise `<user cache>/trust-cg/jit`, the user cache by the one
/// rule every trust-cg cache root shares
/// (`trust_cg_process_env::private_fs::user_cache_base`: an absolute
/// `$XDG_CACHE_HOME`, else an absolute `$HOME/.cache`). Returns `None` when
/// neither variable names an absolute directory, which the caller treats as
/// a cold miss with no error.
pub fn disk_cache_dir() -> Option<PathBuf> {
    if let Ok(guard) = override_slot().lock()
        && let Some(p) = guard.as_ref()
    {
        return Some(p.clone());
    }
    default_disk_cache_dir(
        std::env::var_os("XDG_CACHE_HOME").as_deref(),
        std::env::var_os("HOME").as_deref(),
    )
}

/// `<user cache>/trust-cg/jit` for these `XDG_CACHE_HOME` and `HOME` values,
/// by the one user-cache rule every trust-cg cache root shares: an empty or
/// relative XDG_CACHE_HOME is ignored, a relative HOME names no cache.
fn default_disk_cache_dir(
    xdg_cache_home: Option<&std::ffi::OsStr>,
    home: Option<&std::ffi::OsStr>,
) -> Option<PathBuf> {
    trust_cg_process_env::private_fs::user_cache_base(xdg_cache_home, home)
        .ok()
        .map(|base| base.join(DISK_CACHE_SUBDIR))
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

/// The entry's path in the cache directory as [`private_cache_dir`] names it
/// (`None` when the directory is missing or not private).
#[cfg(test)]
fn cache_path(hash: u64, kernel_name: &str) -> Option<PathBuf> {
    Some(private_cache_dir(false)?.join(cache_filename(hash, kernel_name)))
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

/// Whether a refusal of a non-private cache directory was already reported
/// in this process (reported once, not per lookup).
static REFUSAL_REPORTED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// The cache directory's canonical path, only when no other user can change
/// it or any entry along it
/// (`private_fs::canonical_owner_private_directory`, the rule the TCJ2
/// executable store holds). With `create`, a missing directory (and its
/// missing ancestors) is first created `0700` whatever the umask; an
/// existing one is never changed. `None` (a cold miss, nothing written) for
/// no cache location, a missing directory without `create`, or a directory
/// the rule refuses, which is reported once per process. Every entry is named
/// from the returned canonical path.
fn private_cache_dir(create: bool) -> Option<PathBuf> {
    let dir = disk_cache_dir()?;
    if create {
        // Under `<cache>/trust-cg`, the root the AY private copy is created
        // under: every directory created is `0700` whatever the umask.
        if let Err(err) = trust_cg_process_env::private_fs::create_private_dir_all(&dir) {
            eprintln!(
                "trust-cg jit disk cache: failed to create {} ({err}); falling back to in-memory only",
                dir.display()
            );
            return None;
        }
    }
    match trust_cg_process_env::private_fs::canonical_owner_private_directory(&dir) {
        Ok(canonical) => Some(canonical),
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => None,
        Err(err) => {
            if !REFUSAL_REPORTED.swap(true, Ordering::Relaxed) {
                eprintln!(
                    "trust-cg jit disk cache: ignoring {} ({err}): another user could plant an \
                     entry there; using the in-memory cache only (an existing directory is never \
                     changed: make it and its ancestors writable by you alone, or point \
                     XDG_CACHE_HOME at a private directory)",
                    dir.display()
                );
            }
            None
        }
    }
}

/// The seal key in the canonical cache directory `dir`: read when present
/// and owner-private; with `create`, published when absent, and a wrong-size
/// or all-zero key replaced ([`publish_seal_key`]). `None` otherwise.
fn cache_seal_key(dir: &Path, create: bool) -> Option<[u8; 32]> {
    let key_path = dir.join(IR_TEXT_SEAL_KEY_FILE);
    match crate::executable_buffer_cache::read_seal_key(&key_path) {
        Ok(key) => Some(key),
        Err(error)
            if create
                && matches!(
                    error.kind(),
                    std::io::ErrorKind::NotFound | std::io::ErrorKind::InvalidData
                ) =>
        {
            publish_seal_key(
                dir,
                &key_path,
                error.kind() == std::io::ErrorKind::InvalidData,
            )
            .ok()
        }
        Err(_) => None,
    }
}

/// Distinguishes the staging names of one process's concurrent key creators.
static SEAL_KEY_STAGING_SEQUENCE: AtomicU64 = AtomicU64::new(0);

/// Publish a fresh random seal key at `key_path` in the canonical cache
/// directory `dir` and return the key every opener then holds.
///
/// The key is written whole into a private (`0600`, `O_EXCL`) staging file
/// first and only then given its final name, so the final name never holds a
/// partly written key. A missing key (`replace` false) is published with a
/// hard link, which fails when a key is already there: one creator wins, and
/// every other one reads the winner's complete key. Before X-HOST-P13's fifth
/// closure audit the key was created under its final name and written
/// afterwards; a concurrent opener that read the short file in between
/// replaced it with its own key, the two then sealed under different keys,
/// and entries sealed under the lost key missed and were removed
/// (`concurrent_writes_do_not_corrupt` failed 20 times in 200). The TCJ2
/// store keeps its in-place creation (`executable_buffer_cache::open_seal_key`,
/// measured cheaper per fresh store); this key is created once per cache
/// directory.
///
/// A wrong-size or all-zero key (`replace` true: a crash's remains, since the
/// key is not fsynced) is replaced by renaming the staging file over it, and
/// the key is read back, so a later opener uses whichever replacement landed
/// last. Two concurrent replacements can still leave one opener holding a
/// key no longer on disk until it reopens; its entries then miss, which
/// costs a rebuild, never soundness.
fn publish_seal_key(dir: &Path, key_path: &Path, replace: bool) -> std::io::Result<[u8; 32]> {
    let key = crate::executable_buffer_cache::random_seal_key()?;
    let nanos = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let sequence = SEAL_KEY_STAGING_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    // `.tmp.` in the name: a crashed creator's staging file is pruned with
    // the other stale temporaries (`enforce_file_cap`).
    let staging = dir.join(format!(
        "{IR_TEXT_SEAL_KEY_FILE}.tmp.{}.{nanos}.{sequence}",
        std::process::id()
    ));
    let written = (|| {
        let mut file = trust_cg_process_env::private_fs::create_private_file(&staging)?;
        file.write_all(&key)
    })();
    if let Err(error) = written {
        let _ = fs::remove_file(&staging);
        return Err(error);
    }
    if replace {
        let renamed = fs::rename(&staging, key_path);
        if let Err(error) = renamed {
            let _ = fs::remove_file(&staging);
            return Err(error);
        }
        return crate::executable_buffer_cache::read_seal_key(key_path);
    }
    let linked = fs::hard_link(&staging, key_path);
    let _ = fs::remove_file(&staging);
    match linked {
        Ok(()) => Ok(key),
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            crate::executable_buffer_cache::read_seal_key(key_path)
        }
        Err(error) => Err(error),
    }
}

/// Attempt to read the trust-ir text for `(hash, kernel_name)`.
/// Returns `None` on any failure (missing file, permission error,
/// unreadable bytes, a cache directory another user could change, no seal
/// key, an entry whose keyed tag does not verify) and also when disk I/O has
/// not been enabled for this process via `TRUST_CG_JIT_DISK_CACHE` or a test
/// override. On success, also bumps the file's mtime so touch-based LRU sees
/// it as recently used.
pub fn disk_lookup(hash: u64, kernel_name: &str) -> Option<String> {
    if !crate::env_lock::artifact_reuse_environment_safety().is_reuse_safe() || !disk_io_enabled() {
        return None;
    }
    let dir = private_cache_dir(false)?;
    let name = cache_filename(hash, kernel_name);
    let path = dir.join(&name);
    let metadata = fs::symlink_metadata(&path).ok()?;
    if !metadata.file_type().is_file() || metadata.len() > CACHE_ENTRY_MAX_BYTES {
        return None;
    }
    let seal_key = cache_seal_key(&dir, false)?;
    let encoded = fs::read(&path).ok()?;
    let text = match decode_cache_entry(&seal_key, &name, &encoded) {
        Some(text) => text,
        None => {
            // Cache entries are disposable. Once bytes have been read and
            // proven malformed or not sealed under this cache's key, remove
            // them so every future lookup does not repeat the same failed
            // validation. A concurrent writer uses an atomic rename, so
            // readers never observe its partial staging file; removal is
            // best-effort and semantically only a cold miss.
            let _ = fs::remove_file(&path);
            return None;
        }
    };
    // Touch mtime via a no-op rewrite. Avoid `filetime` crate so we
    // stay zero-dependency. Best-effort: ignore failures.
    let _ = touch(&path);
    Some(text)
}

/// The keyed tag of an entry named `name` holding `payload`.
fn cache_entry_tag(seal_key: &[u8; 32], name: &str, payload: &[u8]) -> Option<[u8; 32]> {
    let payload_len = u64::try_from(payload.len()).ok()?;
    let name_len = u64::try_from(name.len()).ok()?;
    let mut message = Vec::with_capacity(
        CACHE_ENTRY_TAG_DOMAIN
            .len()
            .checked_add(16)?
            .checked_add(name.len())?
            .checked_add(payload.len())?,
    );
    message.extend_from_slice(CACHE_ENTRY_TAG_DOMAIN);
    message.extend_from_slice(&name_len.to_le_bytes());
    message.extend_from_slice(name.as_bytes());
    message.extend_from_slice(&payload_len.to_le_bytes());
    message.extend_from_slice(payload);
    Some(crate::executable_buffer_cache::hmac_sha256(
        seal_key, &message,
    ))
}

fn encode_cache_entry(seal_key: &[u8; 32], name: &str, module_text: &str) -> Option<Vec<u8>> {
    let payload = module_text.as_bytes();
    let payload_len = u64::try_from(payload.len()).ok()?;
    let capacity = CACHE_ENTRY_HEADER_LEN.checked_add(payload.len())?;
    let tag = cache_entry_tag(seal_key, name, payload)?;

    let mut encoded = Vec::with_capacity(capacity);
    encoded.extend_from_slice(CACHE_ENTRY_MAGIC);
    encoded.extend_from_slice(&CACHE_ENTRY_SCHEMA.to_le_bytes());
    encoded.extend_from_slice(&payload_len.to_le_bytes());
    encoded.extend_from_slice(&tag);
    encoded.extend_from_slice(payload);
    Some(encoded)
}

fn decode_cache_entry(seal_key: &[u8; 32], name: &str, encoded: &[u8]) -> Option<String> {
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

    let tag_offset = length_offset + 8;
    let stored_tag = &encoded[tag_offset..tag_offset + 32];
    let payload = &encoded[CACHE_ENTRY_HEADER_LEN..];
    let expected_tag = cache_entry_tag(seal_key, name, payload)?;
    if !crate::executable_buffer_cache::constant_time_eq(&expected_tag, stored_tag) {
        return None;
    }

    String::from_utf8(payload.to_vec()).ok()
}

/// Persist `module_text` for `(hash, kernel_name)` inside a versioned
/// envelope sealed under the cache's key. Creates the cache directory and
/// its seal key if needed, and writes only into an owner-private canonical
/// directory ([`private_cache_dir`]). Writes atomically via tmpfile + rename
/// so a concurrent reader never observes a partial file. Failures are
/// logged (once per call site) but never propagated; the caller's compile
/// proceeds normally on a write error.
pub fn disk_store(hash: u64, kernel_name: &str, module_text: &str) {
    if !crate::env_lock::artifact_reuse_environment_safety().is_reuse_safe() || !disk_io_enabled() {
        return;
    }
    let Some(dir) = private_cache_dir(true) else {
        return;
    };
    let Some(seal_key) = cache_seal_key(&dir, true) else {
        return;
    };
    let name = cache_filename(hash, kernel_name);
    let final_path = dir.join(&name);

    // The monotonic discriminator guarantees that same-process writers do not
    // collide even when the filesystem clock returns the same timestamp.
    let nanos = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let pid = std::process::id();
    let tmp_name = temporary_cache_filename(hash, kernel_name, pid, nanos);
    let tmp_path = dir.join(&tmp_name);

    let encoded = match encode_cache_entry(&seal_key, &name, module_text) {
        Some(encoded) => encoded,
        None => return,
    };

    let write_res: std::io::Result<()> = (|| {
        // `0600` whatever the umask, like every file under `<cache>/trust-cg`
        // (`private_fs`); `File::create` made it `0664` under umask `0002`.
        let mut f = trust_cg_process_env::private_fs::create_private_file(&tmp_path)?;
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
    // Only a private directory, by its canonical name, is ever written.
    let dir = match private_cache_dir(false) {
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

    /// The default directory follows the one user-cache rule: an empty or
    /// relative `XDG_CACHE_HOME` is ignored and a relative `HOME` names no
    /// cache, never a directory below the working directory.
    #[test]
    fn default_disk_cache_dir_is_the_one_user_cache_rule() {
        use std::ffi::OsStr;
        let at = |xdg: Option<&str>, home: Option<&str>| {
            default_disk_cache_dir(xdg.map(OsStr::new), home.map(OsStr::new))
        };
        assert_eq!(
            at(Some("/xdg"), Some("/h")),
            Some(PathBuf::from("/xdg/trust-cg/jit"))
        );
        for ignored in ["", "relative"] {
            assert_eq!(
                at(Some(ignored), Some("/h")),
                Some(PathBuf::from("/h/.cache/trust-cg/jit"))
            );
        }
        assert_eq!(at(Some("relative"), Some("relative-home")), None);
        assert_eq!(at(None, Some("")), None);
    }

    /// A temporary directory only this user can write: the cache is used
    /// only below one (`private_cache_dir`), and `TempDir::new` makes it
    /// `0777 & !umask` (`0775` under umask `0002`).
    fn private_tempdir() -> TempDir {
        let tmp = TempDir::new().expect("create tempdir for disk cache test");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(tmp.path(), fs::Permissions::from_mode(0o700))
                .expect("make the test cache root private");
        }
        tmp
    }

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
            let tmp = private_tempdir();
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

    /// The cache directory and every entry are private whatever the umask:
    /// entries were written with `File::create`, `0664` under umask `0002`
    /// (`0644` under `0022`), beside the AY private copy's `<cache>/trust-cg`
    /// (X-HOST-P13). Asserting `0600` fails the old writer under any umask
    /// that leaves group or other bits.
    #[cfg(unix)]
    #[test]
    fn stored_entries_and_created_directories_are_private() {
        use std::os::unix::fs::MetadataExt;
        let mode = |path: &Path| fs::symlink_metadata(path).unwrap().mode() & 0o7777;
        let guard = CacheRootGuard::new();
        let root = guard._tmp.path().join("cache").join("trust-cg").join("jit");
        set_disk_cache_root_for_tests(Some(root.clone()));
        disk_store(7, "private-kernel", "module text body");
        assert_eq!(mode(&guard._tmp.path().join("cache")), 0o700);
        assert_eq!(
            mode(&guard._tmp.path().join("cache").join("trust-cg")),
            0o700
        );
        assert_eq!(mode(&root), 0o700);
        let entry = cache_path(7, "private-kernel").expect("cache path");
        assert_eq!(mode(&entry), 0o600, "{}", entry.display());
        assert_eq!(
            disk_lookup(7, "private-kernel").as_deref(),
            Some("module text body")
        );
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
                |disk_text| -> Result<(String, Option<Vec<u8>>, String), &'static str> {
                    let (module, module_text) = match disk_text {
                        Some(text) => match parse_trust_ir_text(&text) {
                            Ok(module) => (module, text),
                            Err(_) => {
                                rebuilds.set(rebuilds.get() + 1);
                                let module =
                                    build_bcp_propagate_module().expect("the kernel module builds");
                                let text = encode_trust_ir_text(&module);
                                (module, text)
                            }
                        },
                        None => {
                            rebuilds.set(rebuilds.get() + 1);
                            let module =
                                build_bcp_propagate_module().expect("the kernel module builds");
                            let text = encode_trust_ir_text(&module);
                            (module, text)
                        }
                    };
                    let _ = module;
                    Ok(("compiled".to_owned(), None, module_text))
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
        let key = [7u8; 32];
        let mut encoded = encode_cache_entry(&key, "slot", "module text").expect("encode");
        assert_eq!(
            decode_cache_entry(&key, "slot", &encoded).as_deref(),
            Some("module text")
        );
        let schema_offset = CACHE_ENTRY_MAGIC.len();
        encoded[schema_offset..schema_offset + 4]
            .copy_from_slice(&(CACHE_ENTRY_SCHEMA + 1).to_le_bytes());
        assert!(decode_cache_entry(&key, "slot", &encoded).is_none());
    }

    /// The schema-1 envelope: an unkeyed SHA-256 of the payload, which
    /// anyone who can write the file can compute.
    fn unkeyed_schema_1_entry(module_text: &str) -> Vec<u8> {
        let payload = module_text.as_bytes();
        let mut encoded = Vec::new();
        encoded.extend_from_slice(CACHE_ENTRY_MAGIC);
        encoded.extend_from_slice(&1u32.to_le_bytes());
        encoded.extend_from_slice(&(payload.len() as u64).to_le_bytes());
        encoded.extend_from_slice(&<sha2::Sha256 as sha2::Digest>::digest(payload));
        encoded.extend_from_slice(payload);
        encoded
    }

    /// An entry nobody holding this cache's seal key wrote never matches,
    /// however well formed: an unkeyed envelope (schema 1), one sealed under
    /// another key, and one moved from another slot's name each miss and are
    /// removed; the genuine entry still hits (X-HOST-P13 fourth closure
    /// audit: the unkeyed digest made a planted entry valid).
    #[test]
    fn an_entry_not_sealed_under_this_caches_key_misses() {
        let _g = CacheRootGuard::new();
        disk_store(51, "sealed", "genuine module text");
        let path = cache_path(51, "sealed").expect("cache path");
        let genuine = fs::read(&path).expect("read the genuine entry");
        assert_eq!(
            disk_lookup(51, "sealed").as_deref(),
            Some("genuine module text")
        );
        let name = cache_filename(51, "sealed");
        let other_slot = cache_filename(52, "sealed");
        let dir = private_cache_dir(false).expect("private cache dir");
        let key = cache_seal_key(&dir, false).expect("the cache's seal key");
        let planted = [
            unkeyed_schema_1_entry("PLANTED module text"),
            encode_cache_entry(&[0x42; 32], &name, "PLANTED module text").unwrap(),
            encode_cache_entry(&key, &other_slot, "PLANTED module text").unwrap(),
        ];
        for (index, forged) in planted.iter().enumerate() {
            fs::write(&path, forged).expect("plant an entry");
            assert_eq!(disk_lookup(51, "sealed"), None, "planted entry {index}");
            assert!(!path.exists(), "planted entry {index} is removed");
        }
        fs::write(&path, &genuine).expect("restore the genuine entry");
        assert_eq!(
            disk_lookup(51, "sealed").as_deref(),
            Some("genuine module text")
        );
    }

    /// A cache directory, or a seal key, another user could change is
    /// ignored, never repaired: lookups miss, nothing is written into it,
    /// and its mode is left as it was. The rule is the TCJ2 store's
    /// (`canonical_owner_private_directory`).
    #[cfg(unix)]
    #[test]
    fn a_non_private_cache_is_ignored_and_never_written() {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};
        let set_mode = |path: &Path, mode: u32| {
            fs::set_permissions(path, fs::Permissions::from_mode(mode)).unwrap();
        };
        let mode = |path: &Path| fs::symlink_metadata(path).unwrap().mode() & 0o7777;
        let guard = CacheRootGuard::new();
        let base = guard._tmp.path().canonicalize().unwrap();
        set_mode(&base, 0o700);
        let root = base.join("jit");
        set_disk_cache_root_for_tests(Some(root.clone()));
        disk_store(61, "k", "private payload");
        assert_eq!(disk_lookup(61, "k").as_deref(), Some("private payload"));
        assert_eq!(mode(&root.join(IR_TEXT_SEAL_KEY_FILE)), 0o600);

        // The cache directory group-writable.
        set_mode(&root, 0o775);
        assert_eq!(disk_lookup(61, "k"), None);
        disk_store(62, "k", "must not be written");
        assert!(!root.join(cache_filename(62, "k")).exists());
        assert_eq!(mode(&root), 0o775, "an existing directory is never changed");
        set_mode(&root, 0o700);
        assert_eq!(disk_lookup(61, "k").as_deref(), Some("private payload"));

        // The seal key readable or writable by others.
        let key = root.join(IR_TEXT_SEAL_KEY_FILE);
        for loose in [0o644, 0o660] {
            set_mode(&key, loose);
            assert_eq!(disk_lookup(61, "k"), None, "{loose:o}");
            disk_store(63, "k", "must not be written");
            assert!(!root.join(cache_filename(63, "k")).exists());
            assert_eq!(mode(&key), loose, "the key is never changed");
        }
        set_mode(&key, 0o600);

        // An ancestor others can rename entries in, named directly and
        // through a symlink.
        let shared = base.join("shared");
        fs::create_dir(&shared).unwrap();
        set_mode(&shared, 0o777);
        let inner = shared.join("jit");
        set_disk_cache_root_for_tests(Some(inner.clone()));
        disk_store(64, "k", "must not be written");
        assert!(
            fs::read_dir(&inner).map_or(true, |mut read| read.next().is_none()),
            "nothing is written below an open ancestor"
        );
        let alias = base.join("alias");
        std::os::unix::fs::symlink(&inner, &alias).unwrap();
        set_disk_cache_root_for_tests(Some(alias));
        assert_eq!(disk_lookup(64, "k"), None);

        // A private cache reached through a symlink in the open directory is
        // used by its canonical name.
        let link = shared.join("link");
        std::os::unix::fs::symlink(&root, &link).unwrap();
        set_disk_cache_root_for_tests(Some(link.clone()));
        assert_eq!(disk_lookup(61, "k").as_deref(), Some("private payload"));
        disk_store(65, "k", "through the link");
        assert!(root.join(cache_filename(65, "k")).is_file());
        assert!(
            fs::symlink_metadata(&link)
                .unwrap()
                .file_type()
                .is_symlink()
        );
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
    fn runtime_codegen_controls_bypass_ir_text_cache() {
        const CHILD_MODE_ENV: &str = "JIT_MATRIX_TEST_IR_CACHE_CHILD_MODE";
        const CHILD_ROOT_ENV: &str = "JIT_MATRIX_TEST_IR_CACHE_CHILD_ROOT";
        const TEST_NAME: &str =
            "jit_disk_cache::tests::runtime_codegen_controls_bypass_ir_text_cache";
        const HASH: u64 = 0xc01d_cac4e;
        const KERNEL: &str = "runtime-control-stable";
        const PAYLOAD: &str = "persisted default-policy TrustIR";

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
                        "default-policy lookup must recover the original TrustIR"
                    );
                }
                Some("blocked-lookup") => assert!(
                    disk_lookup(HASH, KERNEL).is_none(),
                    "an unkeyed control must bypass TrustIR lookup"
                ),
                Some("blocked-store") => {
                    disk_store(HASH, KERNEL, "must not replace the default-policy entry");
                    assert!(
                        disk_lookup(HASH, KERNEL).is_none(),
                        "an unkeyed control must bypass TrustIR publication and lookup"
                    );
                }
                _ => panic!("unknown IR-cache child mode: {mode:?}"),
            }
            return;
        }

        let _serial = TEST_SERIAL
            .lock()
            .unwrap_or_else(|poison| poison.into_inner());
        let tmp = private_tempdir();
        let test_binary = std::env::current_exe().expect("resolve current test binary");

        // Scope each real backend control to a child process instead of
        // mutating this parallel test process's environment. Child exit makes
        // restoration unwind-safe even if either assertion fails.
        let run_child = |mode: &str, disabled_pass: Option<&str>| {
            let mut command = std::process::Command::new(&test_binary);
            command
                .arg(TEST_NAME)
                .arg("--exact")
                .arg("--nocapture")
                .arg("--test-threads=1")
                .env(CHILD_MODE_ENV, mode)
                .env(CHILD_ROOT_ENV, tmp.path());
            if let Some(disabled_pass) = disabled_pass {
                command.env("TRUST_CG_DISABLE_PASSES", disabled_pass);
            }
            command.output().expect("run isolated IR-cache child test")
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

        assert_success("default store", run_child("store", None));
        assert_success(
            "blocked lookup",
            run_child("blocked-lookup", Some("aliashoist")),
        );
        assert_success("blocked store", run_child("blocked-store", Some("vec")));
        assert_success(
            "default lookup after blocked store",
            run_child("lookup", None),
        );
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

    /// Concurrent first openers of a cache directory all hold one complete
    /// seal key, the one on disk: the key reaches its final name only whole
    /// ([`publish_seal_key`]). Before X-HOST-P13's fifth closure audit a
    /// creator wrote the key after creating its final name, a concurrent
    /// opener that read the short file replaced it with its own key, and an
    /// entry sealed under the lost key missed and was removed
    /// (`concurrent_writes_do_not_corrupt` failed 20 times in 200). A short
    /// key a crash left is replaced and read back, never by a lookup, and a
    /// crashed creator's staging file is never taken as the key.
    #[cfg(unix)]
    #[test]
    fn concurrent_first_openers_share_one_complete_seal_key() {
        use crate::executable_buffer_cache::read_seal_key;
        use std::os::unix::fs::PermissionsExt;
        const OPENERS: usize = 8;
        let private_dir = |path: &Path| {
            fs::create_dir(path).unwrap();
            fs::set_permissions(path, fs::Permissions::from_mode(0o700)).unwrap();
        };
        let write_private = |path: &Path, bytes: &[u8]| {
            trust_cg_process_env::private_fs::create_private_file(path)
                .unwrap()
                .write_all(bytes)
                .unwrap();
        };
        let base = tempfile::tempdir().unwrap();
        fs::set_permissions(base.path(), fs::Permissions::from_mode(0o700)).unwrap();
        for round in 0..64 {
            let dir = base.path().join(format!("round-{round}"));
            private_dir(&dir);
            let barrier = std::sync::Arc::new(std::sync::Barrier::new(OPENERS));
            let openers: Vec<_> = (0..OPENERS)
                .map(|_| {
                    let dir = dir.clone();
                    let barrier = std::sync::Arc::clone(&barrier);
                    std::thread::spawn(move || {
                        barrier.wait();
                        cache_seal_key(&dir, true)
                    })
                })
                .collect();
            let keys: Vec<_> = openers
                .into_iter()
                .map(|opener| opener.join().unwrap())
                .collect();
            let on_disk = read_seal_key(&dir.join(IR_TEXT_SEAL_KEY_FILE))
                .unwrap_or_else(|error| panic!("round {round}: one complete key: {error}"));
            for key in keys {
                assert_eq!(
                    key,
                    Some(on_disk),
                    "round {round}: every opener holds the key on disk"
                );
            }
            let names: Vec<_> = fs::read_dir(&dir)
                .unwrap()
                .map(|entry| entry.unwrap().file_name())
                .collect();
            assert_eq!(
                names,
                [IR_TEXT_SEAL_KEY_FILE],
                "round {round}: no staging file is left"
            );
        }

        let dir = base.path().join("crashed");
        private_dir(&dir);
        let key_path = dir.join(IR_TEXT_SEAL_KEY_FILE);
        write_private(
            &dir.join(format!("{IR_TEXT_SEAL_KEY_FILE}.tmp.1.2.3")),
            &[7; 32],
        );
        write_private(&key_path, &[9; 5]);
        assert_eq!(
            cache_seal_key(&dir, false),
            None,
            "a lookup never repairs a key"
        );
        let replaced = cache_seal_key(&dir, true).expect("a short key is replaced");
        assert_ne!(replaced, [7; 32], "a staging file is never the key");
        assert_eq!(read_seal_key(&key_path).unwrap(), replaced);
        assert_eq!(cache_seal_key(&dir, false), Some(replaced));
    }

    #[test]
    fn missing_dir_is_cold_miss_not_error() {
        let _serial = TEST_SERIAL
            .lock()
            .unwrap_or_else(|poison| poison.into_inner());
        // Point at a directory we never create, then look up.
        let tmp = private_tempdir();
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
