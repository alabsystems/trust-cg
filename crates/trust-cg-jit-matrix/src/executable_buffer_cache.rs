// trust-cg-jit-matrix/src/executable_buffer_cache.rs - Quarantined serialized
// JIT ExecutableBuffer format (TCJ1) and same-process cache test support, and
// the cross-process, content-keyed, sealed relocatable-image store (TCJ2; see
// the TCJ2 section below).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// # Why this exists
//
// `jit_disk_cache` persists the trust-ir module text. On a disk hit it eliminates
// module construction and lowering, but still pays the full ISel +
// regalloc + encoding cost. TT's compile-cost profile attributes ~58%
// of compile time to regalloc, ~19% to optimization, ~8% to ISel and
// the remaining ~15% to encoding / frame / branch — so the IR-text
// cache only recovers the front-end fraction.
//
// This module contains option (b)'s format: the FULL compiled
// [`ExecutableBuffer`] (the `.text` section plus its symbol table).
// Production persistence/replay is quarantined because the format does not
// yet carry relocations for process-local external veneers and profiling
// pointers. Tests and an explicitly enabled microbenchmark may exercise
// same-process serialization; the disk envelope is process-bound so even that
// override cannot replay bytes after a restart.
//
// # On-disk format (.tcg-jit-buf)
//
// Disk files wrap the reusable `TCJ1` payload in a slot-bound `TCD1`
// envelope. All multi-byte fields are little-endian.
//
// ```text
// 0       4       disk magic = b"TCD1"
// 4       4       disk version (u32)
// 8       32      SHA-256 identity of process + requested (hash, kernel_name)
// 40      8       TCJ1 payload length (u64)
// 48      ...     TCJ1 payload (format below, including its own SHA-256)
// ...     32      disk-envelope SHA-256
//
// Inner TCJ1 payload:
// 0       4       magic = b"TCJ1"
// 4       4       version (u32) = TCJ_VERSION
// 8       4       host_triple_len (u32)
// 12      ...     host_triple bytes (UTF-8, no NUL)
// ...     32      codegen_version_hash (raw 32-byte SHA-256 digest)
// ...     4       code_len (u32)
// ...     ...     code bytes
// ...     4       canonical_symbol_count (u32)
// (per canonical symbol)
// ...     4         name_len (u32)
// ...     ...       name bytes (UTF-8)
// ...     4       symbol_offset_count (u32)
// (per symbol_offset entry — these include Mach-O `_`-prefixed aliases)
// ...     4         name_len (u32)
// ...     ...       name bytes (UTF-8)
// ...     8         offset (u64)
// ...     4       function_range_count (u32)
// (per function range)
// ...     4         name_len (u32)
// ...     ...       name bytes (UTF-8)
// ...     8         range_start (u64)
// ...     8         range_end   (u64)
// ...     32      payload_sha256 (raw digest of every byte preceding it)
// ```
//
// The trailing `payload_sha256` is the cheap integrity check — if a
// partial write or unrelated bit-flip corrupted the file, the loader
// rejects the buffer and falls back to the IR-text cache (or a fresh
// compile).
//
// # Versioning and fail-closed cache invalidation
//
// Two independent guards reject stale buffers:
//
// 1. `host_triple` — `std::env::consts::ARCH-OS`. Refuses an aarch64
//    buffer on x86_64 (and vice versa) even if the magic and SHA both
//    match. The CPU would crash on an undefined-opcode trap; we fail
//    closed before that can happen.
// 2. `codegen_version_hash` — a 32-byte digest of the complete local
//    lowering/codegen/verification source closure, build features, codegen
//    control environment, host target, and detected CPU features.
// 3. The outer slot identity includes a per-process nonce plus the requested
//    content hash and kernel name. A valid file cannot cross processes or be
//    substituted under another requested slot.
//
// All checks are `==`-strict: any mismatch is treated as a cache
// miss without an error, so a stale `.tcg-jit-buf` on disk degrades
// to a fresh recompile rather than a misbehaving execution.
//
// # Failure mode
//
// Mirrors `jit_disk_cache`: every I/O failure (missing directory,
// permission error, truncated file, hash mismatch, corrupt content)
// is observed as a miss. The caller's compile path proceeds normally
// on every error, never propagating disk problems into a kernel
// build error.

use std::collections::HashMap;
use std::fs;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::SystemTime;

use sha2::{Digest, Sha256};
use trust_cg_codegen::jit::{
    ExecutableBuffer, RelinkError, RelocatableImage, publish_serialized_buffer_for_target,
};
use trust_cg_codegen::jit_contract::TargetDescriptor;

/// Magic preamble identifying a trust-cg JIT buffer file. `TCJ` is for
/// "trust-cg JIT" and `1` is the file-format version (NOT the codegen
/// version — see [`codegen_version_hash`]).
pub const TCJ_MAGIC: &[u8; 4] = b"TCJ1";

/// File-format version. Bump when changing the on-disk layout.
pub const TCJ_VERSION: u32 = 1;

const TCJ_DISK_MAGIC: &[u8; 4] = b"TCD1";
const TCJ_DISK_VERSION: u32 = 1;

/// Filename extension for serialized buffers. Distinct from KKK's
/// `.trust_ir` so the two caches can coexist in the same directory
/// without colliding on disk-eviction sweeps.
const BUFFER_CACHE_EXT: &str = "tcg-jit-buf";

/// Subdirectory under the cache root. Sits beside KKK's `trust-cg/jit`
/// IR-text cache.
const BUFFER_CACHE_SUBDIR: &str = "trust-cg/jit-buf";

/// Legacy environment name retained for launcher/API compatibility. It still
/// gates the separate IR-text cache, but cannot enable executable-buffer I/O;
/// production replay is quarantined until relocations can be rebound.
pub const BUFFER_CACHE_ENABLE_ENV: &str = "TRUST_CG_JIT_DISK_CACHE";

/// Default eviction bound: keep at most this many cached buffers on
/// disk. Each watched-literal buffer is on the order of ~16 KB so 256
/// entries fits in <4 MB of disk.
pub const DEFAULT_BUFFER_CACHE_FILE_LIMIT: usize = 256;

/// Same-process test/benchmark root. Files written through this path are also
/// process-bound by the disk envelope and cannot be replayed after restart.
static BUFFER_CACHE_ROOT_OVERRIDE: OnceLock<std::sync::Mutex<Option<PathBuf>>> = OnceLock::new();

fn override_slot() -> &'static std::sync::Mutex<Option<PathBuf>> {
    BUFFER_CACHE_ROOT_OVERRIDE.get_or_init(|| std::sync::Mutex::new(None))
}

/// Returns true when on-disk buffer I/O is permitted for this process.
fn disk_io_enabled() -> bool {
    if let Ok(guard) = override_slot().lock()
        && guard.is_some()
    {
        return true;
    }
    // Cross-process replay remains fail-closed until serialized buffers carry
    // relocations for external veneers and process-local profiling pointers.
    // The explicit test-root override keeps decode/integrity tests available;
    // production environment gates cannot enable unsafe unrelocated replay.
    false
}

/// Override the buffer-cache root for same-process tests and microbenchmarks.
/// Pass `None` to clear. This hook is absent unless tests or the explicitly
/// unsafe benchmark feature are being built.
///
/// # Safety
///
/// The caller must keep the root private to this process and replay only code
/// whose process-local external targets remain alive. The disk envelope also
/// binds files to the current process as defense in depth.
#[cfg(any(test, feature = "unsafe-unrelocated-buffer-cache-test-hooks"))]
#[doc(hidden)]
pub unsafe fn set_buffer_cache_root_for_tests(path: Option<PathBuf>) {
    if let Ok(mut guard) = override_slot().lock() {
        *guard = path;
    }
}

/// Compatibility entry point for production launchers.
///
/// This deliberately does not enable persistence. Serialized machine code
/// cannot safely cross process boundaries until external relocations and
/// process-local pointers are recorded and rebound.
pub fn set_buffer_cache_root(dir: PathBuf) {
    let _ = dir;
    eprintln!(
        "trust-cg jit buffer cache: cross-process replay disabled until external relocations can be rebound"
    );
}

/// Resolve the directory holding `.tcg-jit-buf` files.
pub fn buffer_cache_dir() -> Option<PathBuf> {
    if let Ok(guard) = override_slot().lock()
        && let Some(p) = guard.as_ref()
    {
        return Some(p.clone());
    }
    default_buffer_cache_dir(
        std::env::var_os("XDG_CACHE_HOME").as_deref(),
        std::env::var_os("HOME").as_deref(),
    )
}

/// `<user cache>/trust-cg/jit-buf` for these `XDG_CACHE_HOME` and `HOME`
/// values, by the one user-cache rule every trust-cg cache root shares
/// (`private_fs::user_cache_base`): an empty or relative XDG_CACHE_HOME is
/// ignored, a relative HOME names no cache.
fn default_buffer_cache_dir(
    xdg_cache_home: Option<&std::ffi::OsStr>,
    home: Option<&std::ffi::OsStr>,
) -> Option<PathBuf> {
    trust_cg_process_env::private_fs::user_cache_base(xdg_cache_home, home)
        .ok()
        .map(|base| base.join(BUFFER_CACHE_SUBDIR))
}

fn cache_filename(hash: u64, kernel_name: &str) -> String {
    format!("{hash:016x}-{kernel_name}.{BUFFER_CACHE_EXT}")
}

fn cache_path(hash: u64, kernel_name: &str) -> Option<PathBuf> {
    Some(buffer_cache_dir()?.join(cache_filename(hash, kernel_name)))
}

fn disk_slot_identity(hash: u64, kernel_name: &str) -> [u8; 32] {
    disk_slot_identity_for_process(hash, kernel_name, process_replay_identity())
}

fn disk_slot_identity_for_process(
    hash: u64,
    kernel_name: &str,
    process_identity: &[u8; 32],
) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"trust-cg.executable-buffer.disk-slot.v2\0");
    hasher.update(process_identity);
    hasher.update(hash.to_le_bytes());
    hasher.update((kernel_name.len() as u64).to_le_bytes());
    hasher.update(kernel_name.as_bytes());
    hasher.finalize().into()
}

fn process_replay_identity() -> &'static [u8; 32] {
    static IDENTITY: OnceLock<[u8; 32]> = OnceLock::new();
    IDENTITY.get_or_init(|| {
        let mut hasher = Sha256::new();
        hasher.update(b"trust-cg.executable-buffer.process-replay.v1\0");
        hasher.update(std::process::id().to_le_bytes());
        hasher.update(
            SystemTime::now()
                .duration_since(SystemTime::UNIX_EPOCH)
                .map(|duration| duration.as_nanos())
                .unwrap_or_default()
                .to_le_bytes(),
        );
        hasher.update(((&IDENTITY as *const OnceLock<[u8; 32]>) as usize).to_le_bytes());
        hasher.finalize().into()
    })
}

fn wrap_disk_payload(hash: u64, kernel_name: &str, payload: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(payload.len().saturating_add(80));
    out.extend_from_slice(TCJ_DISK_MAGIC);
    write_u32(&mut out, TCJ_DISK_VERSION);
    out.extend_from_slice(&disk_slot_identity(hash, kernel_name));
    write_u64(&mut out, payload.len() as u64);
    out.extend_from_slice(payload);
    let digest = Sha256::digest(&out);
    out.extend_from_slice(&digest);
    out
}

fn unwrap_disk_payload<'a>(bytes: &'a [u8], hash: u64, kernel_name: &str) -> io::Result<&'a [u8]> {
    const FIXED_PREFIX: usize = 4 + 4 + 32 + 8;
    if bytes.len() < FIXED_PREFIX + 32 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "disk envelope too short",
        ));
    }
    let (envelope, recorded_digest) = bytes.split_at(bytes.len() - 32);
    if Sha256::digest(envelope).as_slice() != recorded_digest {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "disk envelope SHA-256 mismatch",
        ));
    }
    let mut cursor = envelope;
    if read_bytes(&mut cursor, 4)? != TCJ_DISK_MAGIC {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "bad disk envelope magic",
        ));
    }
    let version = read_u32(&mut cursor)?;
    if version != TCJ_DISK_VERSION {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("unsupported disk envelope version {version}"),
        ));
    }
    let recorded_slot = read_bytes(&mut cursor, 32)?;
    if recorded_slot != disk_slot_identity(hash, kernel_name) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "disk buffer slot identity mismatch",
        ));
    }
    let payload_len = usize::try_from(read_u64(&mut cursor)?)
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "disk payload length overflow"))?;
    let payload = read_bytes(&mut cursor, payload_len)?;
    if !cursor.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "trailing bytes in disk envelope",
        ));
    }
    Ok(payload)
}

fn ensure_cache_dir() -> Option<PathBuf> {
    let dir = buffer_cache_dir()?;
    // Under `<cache>/trust-cg`, the root the AY private copy is created
    // under: every directory created is `0700` whatever the umask.
    match trust_cg_process_env::private_fs::create_private_dir_all(&dir) {
        Ok(()) => Some(dir),
        Err(err) => {
            eprintln!(
                "trust-cg jit buffer cache: failed to create {} ({err}); buffer cache disabled",
                dir.display()
            );
            None
        }
    }
}

/// Host triple captured into every buffer file. Cross-architecture
/// loads are caught here without ever calling `mmap`.
pub fn host_triple() -> String {
    format!("{}-{}", std::env::consts::ARCH, std::env::consts::OS)
}

/// Process-local override for the codegen version hash. Tests use this
/// to simulate a stale buffer without rebuilding the codegen crate.
#[cfg(test)]
static CODEGEN_VERSION_OVERRIDE: OnceLock<std::sync::Mutex<Option<[u8; 32]>>> = OnceLock::new();

#[cfg(test)]
fn codegen_version_override_slot() -> &'static std::sync::Mutex<Option<[u8; 32]>> {
    CODEGEN_VERSION_OVERRIDE.get_or_init(|| std::sync::Mutex::new(None))
}

/// Test-facing override of the codegen version digest. Pass `None` to
/// restore the package-version-derived default.
#[cfg(test)]
pub(crate) fn set_codegen_version_hash_for_tests(hash: Option<[u8; 32]>) {
    if let Ok(mut guard) = codegen_version_override_slot().lock() {
        *guard = hash;
    }
}

/// Stable 32-byte digest representing the complete machine-code pipeline that
/// produced a buffer. The build-time content identity covers JIT assembly,
/// lowering, optimization, register allocation, verification, code generation,
/// manifests/lockfile, and embedded verifier assets. A change anywhere in that
/// closure invalidates every cached buffer without a manual version bump.
pub fn codegen_version_hash() -> [u8; 32] {
    #[cfg(test)]
    {
        if let Ok(guard) = codegen_version_override_slot().lock()
            && let Some(h) = guard.as_ref()
        {
            return *h;
        }
    }
    production_codegen_version_hash()
}

/// Append the stable build inputs shared by the Trust-IR module builder and
/// the downstream machine-code pipeline. These inputs change only when the
/// package, source closure, or compiled codegen features change.
fn append_pipeline_build_identity(hasher: &mut Sha256) {
    // Workspace package version (coarse) ...
    hasher.update(env!("CARGO_PKG_VERSION").as_bytes());
    // ... plus the authoritative build-time identity for the entire local
    // machine-code pipeline and its embedded proof/verdict inputs.
    hasher.update(b"\0pipeline-src\0");
    hasher
        .update(include_str!(concat!(env!("OUT_DIR"), "/pipeline_source_identity.txt")).as_bytes());
    hasher.update(b"\0codegen-features\0");
    hasher.update(trust_cg_codegen::BUILD_FEATURE_IDENTITY.as_bytes());
}

/// Stable identity for persisted Trust-IR module text.
///
/// Runtime codegen controls, the host target, and detected CPU features are
/// intentionally absent: a disk hit is parsed and recompiled under the live
/// machine-code configuration. Source, schema, module-builder, or build-feature
/// changes remain fail-closed through the build-time pipeline identity.
pub(crate) fn ir_builder_version_hash() -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"trust-cg-jit.ir-builder.v1\0");
    append_pipeline_build_identity(&mut hasher);
    hasher.finalize().into()
}

/// Authoritative machine-code build/runtime identity without the unit-test
/// stale-buffer override. Unlike [`ir_builder_version_hash`], executable bytes
/// must remain partitioned by runtime controls and detected machine features.
pub(crate) fn production_codegen_version_hash() -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"trust-cg-codegen.executable-buffer.v3\0");
    append_pipeline_build_identity(&mut hasher);
    hasher.update(b"\0codegen-control-environment\0");
    append_codegen_control_environment(&mut hasher, crate::env_lock::vars_os());
    hasher.update(b"\0host-target-contract\0");
    append_target_contract_identity(&mut hasher, &TargetDescriptor::for_trust_cg_host_jit());
    let digest = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}

fn append_target_contract_identity(hasher: &mut Sha256, target: &TargetDescriptor) {
    let canonical = target.canonical_bytes();
    hasher.update((canonical.len() as u64).to_le_bytes());
    hasher.update(canonical);
}

fn append_codegen_control_environment<I>(hasher: &mut Sha256, variables: I)
where
    I: IntoIterator<Item = (std::ffi::OsString, std::ffi::OsString)>,
{
    let mut controls = variables
        .into_iter()
        .filter_map(|(key, value)| {
            let key_bytes = os_string_identity_bytes(&key);
            let key_text = key.to_string_lossy();
            is_codegen_control_environment_key(&key_text)
                .then(|| (key_bytes, os_string_identity_bytes(&value)))
        })
        .collect::<Vec<_>>();
    controls.sort();
    hasher.update((controls.len() as u64).to_le_bytes());
    for (key, value) in controls {
        hasher.update((key.len() as u64).to_le_bytes());
        hasher.update(&key);
        hasher.update((value.len() as u64).to_le_bytes());
        hasher.update(&value);
    }
}

fn is_codegen_control_environment_key(key: &str) -> bool {
    // Compilation parallelism changes only when independent artifacts are
    // scheduled. Binding it into each artifact's machine-code identity made
    // deterministic batch partitioning and cache reuse depend on the requested
    // worker count even though the emitted code is unchanged.
    if key == "TY_TRUST_CG_NATIVE_CALLOUT_COMPILE_JOBS" {
        return false;
    }
    key.starts_with("TCG_") || key.starts_with("TRUST_CG_") || key.starts_with("TY_TRUST_CG_")
}

#[cfg(unix)]
fn os_string_identity_bytes(value: &std::ffi::OsStr) -> Vec<u8> {
    use std::os::unix::ffi::OsStrExt as _;
    value.as_bytes().to_vec()
}

#[cfg(windows)]
fn os_string_identity_bytes(value: &std::ffi::OsStr) -> Vec<u8> {
    use std::os::windows::ffi::OsStrExt as _;
    value
        .encode_wide()
        .flat_map(u16::to_le_bytes)
        .collect::<Vec<_>>()
}

#[cfg(not(any(unix, windows)))]
fn os_string_identity_bytes(value: &std::ffi::OsStr) -> Vec<u8> {
    value.to_string_lossy().as_bytes().to_vec()
}

fn write_u32(buf: &mut Vec<u8>, value: u32) {
    buf.extend_from_slice(&value.to_le_bytes());
}

fn write_u64(buf: &mut Vec<u8>, value: u64) {
    buf.extend_from_slice(&value.to_le_bytes());
}

fn payload_u32_len(length: usize, field: &str) -> io::Result<u32> {
    u32::try_from(length).map_err(|_| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("{field} exceeds the u32 cache format limit"),
        )
    })
}

fn write_str(buf: &mut Vec<u8>, value: &str) -> io::Result<()> {
    let bytes = value.as_bytes();
    let len = payload_u32_len(bytes.len(), "symbol name length")?;
    write_u32(buf, len);
    buf.extend_from_slice(bytes);
    Ok(())
}

fn read_u32(cur: &mut &[u8]) -> io::Result<u32> {
    if cur.len() < 4 {
        return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "u32"));
    }
    let mut bytes = [0u8; 4];
    bytes.copy_from_slice(&cur[..4]);
    *cur = &cur[4..];
    Ok(u32::from_le_bytes(bytes))
}

fn read_u64(cur: &mut &[u8]) -> io::Result<u64> {
    if cur.len() < 8 {
        return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "u64"));
    }
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&cur[..8]);
    *cur = &cur[8..];
    Ok(u64::from_le_bytes(bytes))
}

fn read_bytes<'a>(cur: &mut &'a [u8], n: usize) -> io::Result<&'a [u8]> {
    if cur.len() < n {
        return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "bytes"));
    }
    let (head, rest) = cur.split_at(n);
    *cur = rest;
    Ok(head)
}

fn read_str(cur: &mut &[u8]) -> io::Result<String> {
    let len = read_u32(cur)? as usize;
    let bytes = read_bytes(cur, len)?;
    std::str::from_utf8(bytes)
        .map(|s| s.to_string())
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
}

/// Serialize `buffer` into the binary `.tcg-jit-buf` form.
///
/// The returned `Vec<u8>` is the reusable inner `TCJ1` payload.
/// [`write_buffer_to_disk`] wraps these bytes in the process- and slot-bound
/// `TCD1` disk envelope. Expose the inner payload directly for callers that
/// want to round-trip in memory (the buffer-replay test does this).
/// Returns an error when a length cannot be represented by the wire format.
pub fn serialize_buffer(buffer: &ExecutableBuffer) -> io::Result<Vec<u8>> {
    // The payload carries code bytes only. Replay would publish EH or
    // panic-unwind code without its registered unwind tables, so refuse it.
    if buffer.unwind_tables().is_some() {
        return Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "executable buffer carries JIT unwind tables, which the TCJ1 payload cannot replay",
        ));
    }
    // Replay publishes under the plain host-JIT contract, which does not name
    // the target features a function states for itself (L03-P9); the payload
    // does not record them, so it cannot carry such a buffer.
    if buffer.serialized_target_contract() != TargetDescriptor::for_trust_cg_host_jit() {
        return Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "executable buffer holds functions that state target features beyond the host-JIT contract, which the TCJ1 payload does not record",
        ));
    }
    let code = buffer.code_slice();
    let code_len = payload_u32_len(code.len(), "code length")?;
    let mut out = Vec::new();
    out.extend_from_slice(TCJ_MAGIC);
    write_u32(&mut out, TCJ_VERSION);

    let triple = host_triple();
    write_str(&mut out, &triple)?;

    let version_hash = codegen_version_hash();
    out.extend_from_slice(&version_hash);

    write_u32(&mut out, code_len);
    out.extend_from_slice(code);

    let canonical = buffer.canonical_symbols();
    let canonical_count = payload_u32_len(canonical.len(), "canonical symbol count")?;
    write_u32(&mut out, canonical_count);
    for name in canonical {
        write_str(&mut out, name)?;
    }

    let symbol_offsets = buffer.symbol_offsets();
    let offsets_count = payload_u32_len(symbol_offsets.len(), "symbol offset count")?;
    write_u32(&mut out, offsets_count);
    // Sort by name so the on-disk bytes are deterministic across runs.
    let mut offsets_sorted: Vec<(&String, &u64)> = symbol_offsets.iter().collect();
    offsets_sorted.sort_by(|a, b| a.0.cmp(b.0));
    for (name, offset) in offsets_sorted {
        write_str(&mut out, name)?;
        write_u64(&mut out, *offset);
    }

    let ranges = buffer.function_ranges();
    let ranges_count = payload_u32_len(ranges.len(), "range count")?;
    write_u32(&mut out, ranges_count);
    for (name, range) in ranges {
        write_str(&mut out, name)?;
        write_u64(&mut out, range.start);
        write_u64(&mut out, range.end);
    }

    let mut hasher = Sha256::new();
    hasher.update(&out);
    let digest = hasher.finalize();
    out.extend_from_slice(&digest);
    Ok(out)
}

/// Prepare optional cache bytes only when the quarantined disk tier is enabled.
/// Serialization failure must not invalidate an already compiled provider.
pub(crate) fn serialize_buffer_for_cache(buffer: &ExecutableBuffer) -> Option<Vec<u8>> {
    if !disk_io_enabled() {
        return None;
    }
    match serialize_buffer(buffer) {
        Ok(bytes) => Some(bytes),
        Err(error) => {
            eprintln!("[trust-cg] executable-buffer cache serialization failed: {error}");
            None
        }
    }
}

/// Decoded buffer payload, prior to re-publication into an
/// [`ExecutableBuffer`]. Pulled out as a distinct type so the tests
/// can probe header fields (host triple, version hash) without
/// triggering a real `mmap`.
#[derive(Debug)]
pub struct DecodedBufferPayload {
    pub host_triple: String,
    pub codegen_version_hash: [u8; 32],
    pub code: Vec<u8>,
    pub canonical_symbols: Vec<String>,
    pub symbol_offsets: HashMap<String, u64>,
    pub function_ranges: Vec<(String, std::ops::Range<u64>)>,
}

/// Parse a serialized buffer payload. Validates magic + version +
/// trailing SHA. Header-level identity (host triple, codegen version)
/// is left for the caller to compare against the live process, so
/// tests can observe the mismatch directly.
pub fn decode_buffer_payload(bytes: &[u8]) -> io::Result<DecodedBufferPayload> {
    if bytes.len() < TCJ_MAGIC.len() + 4 + 32 {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "file too short"));
    }
    // Verify trailing SHA first so we never trust any byte of a
    // corrupted file.
    let (payload, digest) = bytes.split_at(bytes.len() - 32);
    let mut hasher = Sha256::new();
    hasher.update(payload);
    let computed = hasher.finalize();
    if computed.as_slice() != digest {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "payload SHA-256 mismatch",
        ));
    }

    let mut cur = payload;
    let magic = read_bytes(&mut cur, 4)?;
    if magic != TCJ_MAGIC {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "bad magic"));
    }
    let version = read_u32(&mut cur)?;
    if version != TCJ_VERSION {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("unsupported version {version}"),
        ));
    }
    let host_triple = read_str(&mut cur)?;
    let version_hash_slice = read_bytes(&mut cur, 32)?;
    let mut version_hash = [0u8; 32];
    version_hash.copy_from_slice(version_hash_slice);

    let code_len = read_u32(&mut cur)? as usize;
    let code_slice = read_bytes(&mut cur, code_len)?;
    let code = code_slice.to_vec();

    let canonical_count = read_u32(&mut cur)? as usize;
    let mut canonical_symbols = Vec::with_capacity(canonical_count);
    for _ in 0..canonical_count {
        canonical_symbols.push(read_str(&mut cur)?);
    }

    let offsets_count = read_u32(&mut cur)? as usize;
    let mut symbol_offsets = HashMap::with_capacity(offsets_count);
    for _ in 0..offsets_count {
        let name = read_str(&mut cur)?;
        let offset = read_u64(&mut cur)?;
        symbol_offsets.insert(name, offset);
    }

    let ranges_count = read_u32(&mut cur)? as usize;
    let mut function_ranges = Vec::with_capacity(ranges_count);
    for _ in 0..ranges_count {
        let name = read_str(&mut cur)?;
        let start = read_u64(&mut cur)?;
        let end = read_u64(&mut cur)?;
        function_ranges.push((name, start..end));
    }

    Ok(DecodedBufferPayload {
        host_triple,
        codegen_version_hash: version_hash,
        code,
        canonical_symbols,
        symbol_offsets,
        function_ranges,
    })
}

/// Re-publish a decoded payload into a live [`ExecutableBuffer`].
///
/// Host-triple and codegen-version-hash checks are enforced here. Any mismatch
/// returns `Err(io::ErrorKind::InvalidData)` so the caller treats it as a cache
/// miss. Those integrity checks are not proof that the native bytes came from
/// Trust Codegen; callers must establish provenance separately.
///
/// # Safety
///
/// `payload` must be authenticated as Trust Codegen output for the exact live
/// compiler build, target, optional-feature profile, symbol layout, and
/// function ABIs. A self-consistent checksum and publicly reproducible version
/// hash alone do not authenticate attacker-controlled native code.
pub unsafe fn publish_decoded_payload(
    payload: DecodedBufferPayload,
) -> io::Result<ExecutableBuffer> {
    if payload.host_triple != host_triple() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "host triple mismatch: file={} live={}",
                payload.host_triple,
                host_triple()
            ),
        ));
    }
    if payload.codegen_version_hash != codegen_version_hash() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "codegen version hash mismatch",
        ));
    }
    let target_contract = trust_cg_codegen::jit_contract::TargetDescriptor::for_trust_cg_host_jit();
    // SAFETY: the caller authenticated provenance as required by this
    // function's safety contract. The checks above additionally establish the
    // exact live target/compiler identity, while decode established structural
    // bounds and transport integrity.
    unsafe {
        publish_serialized_buffer_for_target(
            &payload.code,
            payload.canonical_symbols,
            payload.symbol_offsets,
            payload.function_ranges,
            &target_contract,
        )
    }
    .map_err(|e| io::Error::other(format!("publish failed: {e}")))
}

/// Serialize `buffer` and write it atomically to disk under the
/// `(hash, kernel_name)` slot. Errors are logged but never propagated;
/// the caller's compile path is unaffected. Without the feature-gated
/// same-process test/benchmark override, this is a no-op.
pub fn write_buffer_to_disk(hash: u64, kernel_name: &str, buffer: &ExecutableBuffer) {
    if let Some(bytes) = serialize_buffer_for_cache(buffer) {
        write_buffer_bytes_to_disk(hash, kernel_name, &bytes);
    }
}

/// Write a previously-serialized buffer payload to disk. Used by the
/// compile-cache tier when it already holds the serialized bytes (the
/// kernel-side closure produces them so the live provider keeps its
/// owned `ExecutableBuffer` untouched).
pub fn write_buffer_bytes_to_disk(hash: u64, kernel_name: &str, payload: &[u8]) {
    if !crate::env_lock::artifact_reuse_environment_safety().is_reuse_safe() || !disk_io_enabled() {
        return;
    }
    let dir = match ensure_cache_dir() {
        Some(d) => d,
        None => return,
    };
    let final_path = dir.join(cache_filename(hash, kernel_name));

    let nanos = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let pid = std::process::id();
    let tmp_name = format!("{}.tmp.{pid}.{nanos}", cache_filename(hash, kernel_name));
    let tmp_path = dir.join(&tmp_name);

    let disk_payload = wrap_disk_payload(hash, kernel_name, payload);
    let write_res: io::Result<()> = (|| {
        // `0600` whatever the umask (`private_fs`), as every cache file.
        let mut f = trust_cg_process_env::private_fs::create_private_file(&tmp_path)?;
        f.write_all(&disk_payload)?;
        f.sync_data()?;
        drop(f);
        fs::rename(&tmp_path, &final_path)?;
        Ok(())
    })();

    if let Err(err) = write_res {
        eprintln!(
            "trust-cg jit buffer cache: failed to write {} ({err}); continuing without persistence",
            final_path.display()
        );
        let _ = fs::remove_file(&tmp_path);
    } else if let Err(err) = enforce_file_cap(&dir, DEFAULT_BUFFER_CACHE_FILE_LIMIT) {
        eprintln!(
            "trust-cg jit buffer cache: eviction sweep on {} failed ({err}); cache may exceed cap",
            dir.display()
        );
    }
}

/// Attempt a same-process load of an [`ExecutableBuffer`] from disk. Returns
/// `None` on any failure: missing file, process/slot identity mismatch, magic /
/// version / SHA mismatch, host triple / codegen mismatch, or mmap failure.
/// Touches the file's mtime on success so the LRU sweep keeps it.
pub fn read_buffer_from_disk(hash: u64, kernel_name: &str) -> Option<ExecutableBuffer> {
    if !crate::env_lock::artifact_reuse_environment_safety().is_reuse_safe() || !disk_io_enabled() {
        return None;
    }
    let path = cache_path(hash, kernel_name)?;
    let mut file = fs::File::open(&path).ok()?;
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes).ok()?;
    drop(file);
    let serialized = unwrap_disk_payload(&bytes, hash, kernel_name).ok()?;
    let payload = decode_buffer_payload(serialized).ok()?;
    // SAFETY: executable-buffer disk I/O can only be enabled by the unsafe,
    // process-private test/benchmark hook. Its caller promises that the root
    // is private and contains only buffers produced by this live process; the
    // disk envelope then binds the payload to this process and cache slot.
    let buffer = unsafe { publish_decoded_payload(payload) }.ok()?;
    let _ = touch(&path);
    Some(buffer)
}

/// Bump `path`'s mtime to "now" so the LRU sweep treats this buffer as
/// recently used.
///
/// Opening in append mode and dropping the handle does NOT update mtime:
/// POSIX only bumps `st_mtime` on an actual `write()`, so the previous
/// implementation was a no-op and silently degraded the disk LRU to FIFO
/// (oldest-created evicted first, regardless of recent hits). We rewrite
/// the file's first byte in place — `write()` is required to update mtime
/// and rewriting a byte with its own value preserves content exactly.
/// This avoids pulling in a `filetime`/`libc` dependency.
fn touch(path: &Path) -> io::Result<()> {
    use std::io::{Seek, SeekFrom};
    let mut f = fs::OpenOptions::new().read(true).write(true).open(path)?;
    let mut first = [0u8; 1];
    let n = f.read(&mut first)?;
    if n == 1 {
        f.seek(SeekFrom::Start(0))?;
        f.write_all(&first)?;
        f.flush()?;
    }
    Ok(())
}

fn enforce_file_cap(dir: &Path, cap: usize) -> io::Result<()> {
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
            .map(|s| s == BUFFER_CACHE_EXT)
            .unwrap_or(false);
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
    entries.sort_by(|a, b| a.1.cmp(&b.1).then(a.0.cmp(&b.0)));
    let to_remove = entries.len() - cap;
    for (path, _mtime, _is_cache) in entries.iter().take(to_remove) {
        let _ = fs::remove_file(path);
    }
    Ok(())
}

/// Remove every `.tcg-jit-buf` file in the buffer-cache directory.
/// Missing directory is treated as success.
pub fn clear_buffer_cache() {
    if !disk_io_enabled() {
        return;
    }
    let dir = match buffer_cache_dir() {
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
            .map(|s| s == BUFFER_CACHE_EXT)
            .unwrap_or(false);
        if is_cache_file {
            let _ = fs::remove_file(&path);
        }
    }
}

/// Count the number of `.tcg-jit-buf` files currently on disk.
pub fn buffer_cache_file_count() -> usize {
    let dir = match buffer_cache_dir() {
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
                .map(|s| s == BUFFER_CACHE_EXT)
                .unwrap_or(false)
        })
        .count()
}

// ---------------------------------------------------------------------------
// TCJ2: relocatable images, content-keyed and sealed
// ---------------------------------------------------------------------------
//
// TCJ1 above persists a LINKED buffer, whose veneer literals are this
// process's addresses; that is why its disk envelope is bound to a process
// nonce and why it cannot cross a process boundary. TCJ2 persists the
// PRE-LINK image (`trust_cg_codegen::jit::RelocatableImage`): the same
// machine code with every process-local literal still unwritten, plus the
// relocation inventory `RelocatableImage::relink` needs to publish it in any
// process under the same replay check and bytes-hash seal a cold compile uses.
//
// A TCJ2 entry is therefore keyed by CONTENT, never by process. The caller
// supplies a 32-byte content key that must bind every input that changes the
// bytes (for TY: the frontend-neutral TrustIR digest, adapter and TrustCG
// identities, opt level, target, runtime-helper ABI, layout/caller identity
// and export/entry-role surface); TCJ2 adds the live host triple and the
// complete machine-code pipeline identity (`codegen_version_hash`: TrustCG's
// source closure, build features, codegen control environment and detected
// CPU features) and refuses an entry whose either differs.
//
// On-disk format (`<hex content key>.tcj2`, all integers little-endian):
//
// ```text
// "TCJ2" | u32 version | u64+bytes host triple | [32] codegen version hash
// | [32] content key | u64+bytes caller receipt | u64+bytes relocatable image
// | [32] image SHA-256 | [32] HMAC-SHA-256(seal key, every preceding byte)
// ```
//
// # The seal
//
// A cache of executable code is an injection surface. A plain digest only
// detects accidents: anyone who can write the file can recompute it. The
// trailer is instead an HMAC under a per-store secret (`tcj2-seal.key`, 32
// random bytes, mode 0600, created exclusively under its final name and
// written once), verified in constant time BEFORE any other byte is
// parsed. The store retains a canonical directory path, checks each ancestor
// from root to leaf for trusted ownership and protection against other users'
// renames, and reads the key through an owner-checked, no-follow descriptor.
// Its directory and key must be owned by the effective user and writable by
// no one else. So a flipped byte, a
// resealed forgery by someone without the key, an entry copied from another
// store, or an entry renamed into another key's slot all MISS; none runs.
//
// What the seal does not claim: a process running as the same user can read
// the key. The store defends against corruption, cross-store and cross-user
// substitution, and writers who cannot read the owner's files; it is not a
// sandbox against the owner's own processes. Filesystem admission checks Unix
// ownership and mode bits, not extended ACLs: the deployment must not grant
// additional write access outside that model.

/// Magic of a TCJ2 entry.
pub const TCJ2_MAGIC: &[u8; 4] = b"TCJ2";
/// TCJ2 layout version. Bump on any change.
pub const TCJ2_VERSION: u32 = 1;
/// Extension of TCJ2 entries.
pub const TCJ2_EXT: &str = "tcj2";
/// The per-store seal secret.
pub const TCJ2_SEAL_KEY_FILE: &str = "tcj2-seal.key";
/// Default bound on stored TCJ2 entries (least recently used evicted first).
pub const DEFAULT_TCJ2_FILE_LIMIT: usize = 256;
/// Largest TCJ2 file a load will read.
pub const TCJ2_MAX_FILE_BYTES: u64 = 256 * 1024 * 1024;

/// Why a TCJ2 load did not produce an entry. Every one is a cache MISS.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Tcj2Miss {
    /// No entry under this key.
    Absent,
    /// The live environment carries an unkeyed codegen control.
    UnsafeEnvironment,
    /// The file could not be read, or exceeds [`TCJ2_MAX_FILE_BYTES`].
    Io(String),
    /// The keyed seal does not verify: corrupt, forged or foreign.
    Seal,
    /// Structurally malformed after a valid seal.
    Malformed(String),
    /// Written for another host triple.
    HostTriple,
    /// Written by another machine-code pipeline build or configuration.
    CodegenVersion,
    /// The entry names another content key (renamed or copied into this slot).
    ContentKey,
    /// The relocatable image failed its own structural validation.
    Image(String),
}

impl Tcj2Miss {
    /// Stable reason name for counters.
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Absent => "absent",
            Self::UnsafeEnvironment => "unsafe_environment",
            Self::Io(_) => "io",
            Self::Seal => "seal",
            Self::Malformed(_) => "malformed",
            Self::HostTriple => "host_triple",
            Self::CodegenVersion => "codegen_version",
            Self::ContentKey => "content_key",
            Self::Image(_) => "image",
        }
    }
}

impl std::fmt::Display for Tcj2Miss {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(detail) | Self::Malformed(detail) | Self::Image(detail) => {
                write!(f, "{}: {detail}", self.as_str())
            }
            other => f.write_str(other.as_str()),
        }
    }
}

/// A decoded, authenticated TCJ2 entry.
#[derive(Debug)]
pub struct Tcj2Entry {
    /// Caller evidence stored beside the image (TY: its receipt projection).
    pub receipt: Vec<u8>,
    /// The relocatable image, structurally validated.
    pub image: RelocatableImage,
}

pub(crate) fn hmac_sha256(key: &[u8; 32], message: &[u8]) -> [u8; 32] {
    let mut inner_pad = [0x36u8; 64];
    let mut outer_pad = [0x5cu8; 64];
    for (index, byte) in key.iter().enumerate() {
        inner_pad[index] ^= byte;
        outer_pad[index] ^= byte;
    }
    let inner = Sha256::new()
        .chain_update(inner_pad)
        .chain_update(message)
        .finalize();
    Sha256::new()
        .chain_update(outer_pad)
        .chain_update(inner)
        .finalize()
        .into()
}

pub(crate) fn constant_time_eq(left: &[u8], right: &[u8]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .fold(0u8, |difference, (a, b)| difference | (a ^ b))
            == 0
}

fn write_len_prefixed(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    out.extend_from_slice(bytes);
}

/// Encode one TCJ2 entry, sealed under `seal_key`.
pub fn encode_tcj2(
    seal_key: &[u8; 32],
    content_key: &[u8; 32],
    receipt: &[u8],
    image: &RelocatableImage,
) -> Vec<u8> {
    let image_bytes = image.to_bytes();
    let mut out = Vec::with_capacity(image_bytes.len() + receipt.len() + 256);
    out.extend_from_slice(TCJ2_MAGIC);
    out.extend_from_slice(&TCJ2_VERSION.to_le_bytes());
    write_len_prefixed(&mut out, host_triple().as_bytes());
    out.extend_from_slice(&codegen_version_hash());
    out.extend_from_slice(content_key);
    write_len_prefixed(&mut out, receipt);
    write_len_prefixed(&mut out, &image_bytes);
    out.extend_from_slice(&image.image_sha256());
    let seal = hmac_sha256(seal_key, &out);
    out.extend_from_slice(&seal);
    out
}

fn tcj2_take<'a>(cursor: &mut &'a [u8], len: usize) -> Result<&'a [u8], Tcj2Miss> {
    if cursor.len() < len {
        return Err(Tcj2Miss::Malformed("truncated".into()));
    }
    let (head, tail) = cursor.split_at(len);
    *cursor = tail;
    Ok(head)
}

fn tcj2_len_prefixed<'a>(cursor: &mut &'a [u8]) -> Result<&'a [u8], Tcj2Miss> {
    let len = u64::from_le_bytes(tcj2_take(cursor, 8)?.try_into().expect("eight bytes"));
    let len = usize::try_from(len).map_err(|_| Tcj2Miss::Malformed("length overflow".into()))?;
    tcj2_take(cursor, len)
}

/// Authenticate and decode one TCJ2 entry for `expected_key`. The seal is
/// checked first, in constant time, before any other byte is interpreted.
pub fn decode_tcj2(
    seal_key: &[u8; 32],
    expected_key: &[u8; 32],
    bytes: &[u8],
) -> Result<Tcj2Entry, Tcj2Miss> {
    if bytes.len() < TCJ2_MAGIC.len() + 4 + 32 {
        return Err(Tcj2Miss::Seal);
    }
    let (body, seal) = bytes.split_at(bytes.len() - 32);
    if !constant_time_eq(&hmac_sha256(seal_key, body), seal) {
        return Err(Tcj2Miss::Seal);
    }
    let mut cursor = body;
    if tcj2_take(&mut cursor, 4)? != TCJ2_MAGIC {
        return Err(Tcj2Miss::Malformed("bad magic".into()));
    }
    let version = u32::from_le_bytes(tcj2_take(&mut cursor, 4)?.try_into().expect("four bytes"));
    if version != TCJ2_VERSION {
        return Err(Tcj2Miss::Malformed(format!(
            "unsupported version {version}"
        )));
    }
    if tcj2_len_prefixed(&mut cursor)? != host_triple().as_bytes() {
        return Err(Tcj2Miss::HostTriple);
    }
    if tcj2_take(&mut cursor, 32)? != codegen_version_hash() {
        return Err(Tcj2Miss::CodegenVersion);
    }
    if tcj2_take(&mut cursor, 32)? != expected_key {
        return Err(Tcj2Miss::ContentKey);
    }
    let receipt = tcj2_len_prefixed(&mut cursor)?.to_vec();
    let image_bytes = tcj2_len_prefixed(&mut cursor)?;
    let recorded_image_sha256 = tcj2_take(&mut cursor, 32)?;
    if !cursor.is_empty() {
        return Err(Tcj2Miss::Malformed("trailing bytes".into()));
    }
    let image = RelocatableImage::from_bytes(image_bytes).map_err(|error| match error {
        RelinkError::Rejected(detail) => Tcj2Miss::Image(detail),
        other => Tcj2Miss::Image(other.to_string()),
    })?;
    if image.image_sha256() != recorded_image_sha256 {
        return Err(Tcj2Miss::Image(
            "image SHA-256 differs from the envelope's".into(),
        ));
    }
    Ok(Tcj2Entry { receipt, image })
}

/// Lower-case hex of a content key: the entry's file stem.
pub fn tcj2_key_hex(key: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for byte in key {
        out.push_str(&format!("{byte:02x}"));
    }
    out
}

/// Stores between two cap sweeps of one [`Tcj2Store`]: the first store of a
/// store handle sweeps, then every `TCJ2_SWEEP_INTERVAL`-th. The cap is soft
/// by at most this many entries per open handle; a sweep lists and stats the
/// whole directory, which was ~10-20% of a small entry's store cost. A handle
/// whose [`Tcj2Store::open`] CREATED the directory skips the first sweep (the
/// directory held nothing a moment ago) and sweeps first at its
/// `TCJ2_SWEEP_INTERVAL`-th store.
pub const TCJ2_SWEEP_INTERVAL: u64 = 32;

/// An owner-private directory of sealed TCJ2 entries.
#[derive(Debug, Clone)]
pub struct Tcj2Store {
    dir: PathBuf,
    seal_key: [u8; 32],
    stores: std::sync::Arc<std::sync::atomic::AtomicU64>,
}

impl Tcj2Store {
    /// Open (creating when absent) the store at `dir`. Refuses a directory or
    /// seal key that is not owned by the effective user or that another user
    /// can write, and a canonical ancestor another user could replace. An
    /// owner-private seal key of the wrong size or all zeros (what a crash can
    /// leave, since the key is not fsynced, or what a reader racing its
    /// creator's single write can see) is replaced with a fresh random key;
    /// entries sealed under the lost key then miss with `Tcj2Miss::Seal`.
    /// Retains the canonical path, not a mutable alias.
    ///
    /// A store directory this call CREATED holds no key yet: the key is
    /// created at once, without first trying to read one, and the handle
    /// skips its first cap sweep (see [`TCJ2_SWEEP_INTERVAL`]).
    pub fn open(dir: &Path) -> io::Result<Self> {
        let created = trust_cg_process_env::private_fs::create_private_dir_all_reporting(dir)?;
        let dir = trust_cg_process_env::private_fs::canonical_owner_private_directory(dir)?;
        let key_path = dir.join(TCJ2_SEAL_KEY_FILE);
        let seal_key = open_seal_key(&key_path, created)?;
        Ok(Self {
            dir,
            seal_key,
            stores: std::sync::Arc::new(std::sync::atomic::AtomicU64::new(u64::from(created))),
        })
    }

    /// The store directory.
    pub fn dir(&self) -> &Path {
        &self.dir
    }

    /// Path of the entry for `key` (whether or not it exists).
    pub fn entry_path(&self, key: &[u8; 32]) -> PathBuf {
        self.dir.join(format!("{}.{TCJ2_EXT}", tcj2_key_hex(key)))
    }

    /// Load and authenticate the entry for `key`. Touches its mtime on
    /// success so the LRU sweep keeps it.
    pub fn load(&self, key: &[u8; 32]) -> Result<Tcj2Entry, Tcj2Miss> {
        if !crate::env_lock::artifact_reuse_environment_safety().is_reuse_safe() {
            return Err(Tcj2Miss::UnsafeEnvironment);
        }
        let path = self.entry_path(key);
        let metadata = match fs::symlink_metadata(&path) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Err(Tcj2Miss::Absent),
            Err(error) => return Err(Tcj2Miss::Io(error.to_string())),
        };
        if !metadata.file_type().is_file() {
            return Err(Tcj2Miss::Io("entry is not a regular file".into()));
        }
        if metadata.len() > TCJ2_MAX_FILE_BYTES {
            return Err(Tcj2Miss::Io("entry exceeds the size bound".into()));
        }
        let bytes = fs::read(&path).map_err(|error| Tcj2Miss::Io(error.to_string()))?;
        let entry = decode_tcj2(&self.seal_key, key, &bytes)?;
        let _ = touch(&path);
        Ok(entry)
    }

    /// Seal and publish the entry for `key`. Returns the bytes written.
    /// Enforces [`DEFAULT_TCJ2_FILE_LIMIT`] (swept every
    /// [`TCJ2_SWEEP_INTERVAL`] stores of this handle, starting with the first).
    ///
    /// A key with no entry is published directly: the entry file is created
    /// exclusively (`O_EXCL`, 0600) under its final name and written once. A
    /// reader that races the write, or finds the remains of a crash, reads a
    /// short or damaged file whose keyed seal fails: a MISS, never a run. An
    /// existing entry (a damaged one included) is replaced atomically through
    /// a temporary file and a rename, as before. The direct publish saves the
    /// rename (~0.65 M instructions on APFS) on every first store of a key.
    pub fn store(
        &self,
        key: &[u8; 32],
        receipt: &[u8],
        image: &RelocatableImage,
    ) -> io::Result<u64> {
        if !crate::env_lock::artifact_reuse_environment_safety().is_reuse_safe() {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "unkeyed codegen control in the environment",
            ));
        }
        let bytes = encode_tcj2(&self.seal_key, key, receipt, image);
        let final_path = self.entry_path(key);
        match trust_cg_process_env::private_fs::create_private_file(&final_path) {
            Ok(mut file) => {
                let written = file.write_all(&bytes);
                drop(file);
                if let Err(error) = written {
                    let _ = fs::remove_file(&final_path);
                    return Err(error);
                }
                self.sweep_after_store();
                return Ok(bytes.len() as u64);
            }
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
            Err(error) => return Err(error),
        }
        let nanos = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .map(|duration| duration.as_nanos())
            .unwrap_or(0);
        let tmp_path = self.dir.join(format!(
            "{}.{TCJ2_EXT}.tmp.{}.{nanos}",
            tcj2_key_hex(key),
            std::process::id()
        ));
        let written = (|| {
            let mut file = trust_cg_process_env::private_fs::create_private_file(&tmp_path)?;
            file.write_all(&bytes)?;
            drop(file);
            fs::rename(&tmp_path, &final_path)
        })();
        if let Err(error) = written {
            let _ = fs::remove_file(&tmp_path);
            return Err(error);
        }
        self.sweep_after_store();
        Ok(bytes.len() as u64)
    }

    fn sweep_after_store(&self) {
        let count = self
            .stores
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        if count.is_multiple_of(TCJ2_SWEEP_INTERVAL) {
            let _ = enforce_tcj2_file_cap(&self.dir, DEFAULT_TCJ2_FILE_LIMIT);
        }
    }

    /// Remove the entry for `key` (an entry proven wrong must not be served
    /// again). A missing entry is success.
    pub fn evict(&self, key: &[u8; 32]) -> io::Result<()> {
        match fs::remove_file(self.entry_path(key)) {
            Err(error) if error.kind() != io::ErrorKind::NotFound => Err(error),
            _ => Ok(()),
        }
    }

    /// Count the TCJ2 entries in the store.
    pub fn entry_count(&self) -> usize {
        fs::read_dir(&self.dir)
            .map(|read| {
                read.flatten()
                    .filter(|entry| {
                        entry.path().extension().and_then(|ext| ext.to_str()) == Some(TCJ2_EXT)
                    })
                    .count()
            })
            .unwrap_or(0)
    }

    // Only the AArch64 `tcj2` test module constructs a store under a chosen key.
    #[cfg(all(test, target_arch = "aarch64"))]
    fn with_seal_key_for_tests(dir: &Path, seal_key: [u8; 32]) -> Self {
        Self {
            dir: dir.to_path_buf(),
            seal_key,
            stores: std::sync::Arc::default(),
        }
    }
}

pub(crate) fn read_seal_key(path: &Path) -> io::Result<[u8; 32]> {
    let file = trust_cg_process_env::private_fs::open_owner_private_file(path)?;
    // One extra byte distinguishes an oversized key without trusting an
    // earlier length check or allowing an unbounded read of a growing file.
    let mut bytes = Vec::with_capacity(33);
    file.take(33).read_to_end(&mut bytes)?;
    let key = <[u8; 32]>::try_from(bytes.as_slice()).map_err(|_| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("{} is not a 32-byte seal key", path.display()),
        )
    })?;
    if key == [0u8; 32] {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("{} is an all-zero seal key", path.display()),
        ));
    }
    Ok(key)
}

/// The store's seal key at `key_path`: read it, or create it when absent
/// (`fresh`: the directory was just created, so go straight to creation).
///
/// An owner-private key of the wrong size or all zeros is the remains of a
/// crash (the key is not fsynced) or a creator whose single write a reader
/// raced: it is replaced, once. Replacing a racing creator's key costs only
/// cache efficiency, never soundness: each process seals and verifies with
/// the key it holds, so an entry sealed under a lost key MISSES
/// (`Tcj2Miss::Seal`) and never runs. The owner/mode check has already passed.
pub(crate) fn open_seal_key(key_path: &Path, fresh: bool) -> io::Result<[u8; 32]> {
    if !fresh {
        match read_seal_key(key_path) {
            Ok(key) => return Ok(key),
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) if error.kind() == io::ErrorKind::InvalidData => {
                let _ = fs::remove_file(key_path);
            }
            Err(error) => return Err(error),
        }
    }
    match create_seal_key(key_path) {
        Ok(key) => return Ok(key),
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
        Err(error) => return Err(error),
    }
    // A concurrent opener created the key first: use its key.
    match read_seal_key(key_path) {
        Err(error) if error.kind() == io::ErrorKind::InvalidData => {
            // Its single write is still in flight (or it crashed): replace
            // the key once rather than wait on another process.
            let _ = fs::remove_file(key_path);
            match create_seal_key(key_path) {
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                    read_seal_key(key_path)
                }
                created => created,
            }
        }
        read => read,
    }
}

/// Create the seal key: 32 bytes from the OS random source, written with ONE
/// `write` into a file created exclusively (`O_EXCL`, 0600) under the key's
/// final name, and returned as written (never re-read). An existing key
/// file fails the call with `AlreadyExists` and is left untouched, so a
/// concurrent creator's key is never replaced by this call.
///
/// Publishing under the final name (rather than a temporary file plus a
/// no-clobber rename) saves the rename and the temporary name on every fresh
/// store: measured on APFS (2026-09-29, M5 Max, instructions retired incl.
/// kernel) the temp-file path cost ~1.25 M instructions more (`renamex_np`
/// 0.68 M, the re-read 0.16 M, `/dev/urandom` 0.12 M against `getentropy`'s
/// 0.013 M). A reader that races the single write sees a short file, which
/// [`open_seal_key`] treats like a crash's remains (see there). The key is
/// not fsynced: durability of a cache secret is not worth a synchronous flush
/// on every cold store directory.
fn create_seal_key(key_path: &Path) -> io::Result<[u8; 32]> {
    let key = random_seal_key()?;
    let mut file = trust_cg_process_env::private_fs::create_private_file(key_path)?;
    let written = file.write_all(&key);
    drop(file);
    if let Err(error) = written {
        let _ = fs::remove_file(key_path);
        return Err(error);
    }
    Ok(key)
}

/// 32 bytes from the OS random source (`getentropy`, no file descriptor;
/// `/dev/urandom` where it is unavailable), never all zero.
pub(crate) fn random_seal_key() -> io::Result<[u8; 32]> {
    let mut key = [0u8; 32];
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        // SAFETY: `key` is a writable buffer of 32 bytes (<= 256, the
        // `getentropy` limit) that outlives the call.
        let status = unsafe { libc::getentropy(key.as_mut_ptr().cast(), key.len()) };
        if status != 0 {
            fs::File::open("/dev/urandom")?.read_exact(&mut key)?;
        }
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    fs::File::open("/dev/urandom")?.read_exact(&mut key)?;
    if key == [0u8; 32] {
        return Err(io::Error::other(
            "the OS random source returned an all-zero key",
        ));
    }
    Ok(key)
}

// ---------------------------------------------------------------------------
// TCJ2 store admission: no store before a key recurs
// ---------------------------------------------------------------------------
//
// A stored entry pays for itself only when a LATER process looks the same key
// up. A one-off run -- or every run of a module whose key never recurs --
// pays the store for nothing: opening a fresh store (directory, owner and
// ancestor checks, the seal key) and writing each entry are file-system work,
// measured on APFS (2026-09-28, M5 Max, instructions retired incl. kernel) at
// ~2.5 M and ~0.9 M instructions with the cheaper publication above, 7.1 M
// and 2.2 M before it (and a fresh store's open ~1.25 M less again since its
// key is published directly, 2026-09-29). For a JIT consumer whose cold runs are measured
// (TY's dominance ratchet), that is the difference between a cache that costs
// nothing on a first run and one that fails its cold column.
//
// So admission is a policy the store offers, not something each caller
// reinvents:
//
// * [`Tcj2Store::entry_absent`] recognises a missing entry with one `lstat`
//   of its path, without opening the store (no directory is created and no
//   seal key read on a first-ever lookup). Anything but "not found" answers
//   `false`, and the caller takes the full, authenticated load.
// * [`Tcj2Sightings`] is an append-only, bounded log of content keys that
//   missed. [`Tcj2Sightings::admit`] decides what a miss on an absent entry
//   does with the artifact it is about to compile:
//   - the key was recorded by an earlier process: it recurs, STORE it;
//   - first sighting, and the module is large (at least
//     [`TCJ2_FIRST_SIGHTING_STORE_MIN_TRUST_IR_INSTRUCTIONS`] TrustIR
//     instructions): its compile costs far more than the store, so STORE it
//     at once;
//   - first sighting of a small module: RECORD the sighting only (one 65-byte
//     line) and store nothing.
//   The decision reads the module's SIZE, never a measured cost, so every
//   process decides the same way.
//
// A sighting is a COST hint and never an authority: a hit still needs a
// sealed, authenticated TCJ2 entry, so a forged, lost or stale log moves a
// store by one run at most and can never make code run.

/// A first sighting of a module with at least this many TrustIR instructions
/// is stored at once. The raw AArch64 JIT lane retires ~65-110 K
/// instructions per TrustIR instruction on TY's callout modules, so such a
/// module's compile is >= ~4-7 M instructions against a ~0.8-1 M entry (plus
/// the store's one-time open) and a ~1.2 M hit: its first recurrence repays
/// the store.
///
/// Was 256 (2026-09-28). Measured 2026-09-29 through TY (lane
/// `cc-image-cache-live`, 15 cells, same binary, storing every first
/// sighting vs this rule): the recurrence rule moved each small module's
/// store into the SECOND run, where it cost ~1-5 M and hit nothing, while
/// storing at first sighting cost the first run about the same as recording
/// the sighting (within ~3 M noise) and made the second run 12-60 M cheaper
/// on every row with a module of 95-239 instructions (MCConsensus_2's 117:
/// second run +5 M -> -12 M). Below 64 instructions a compile (~2-6 M) is
/// within a few times one store plus one hit, so a tiny module still waits
/// for its key to recur.
pub const TCJ2_FIRST_SIGHTING_STORE_MIN_TRUST_IR_INSTRUCTIONS: usize = 64;

/// Largest sightings log read (1024 records of 65 bytes); a larger one is
/// discarded and restarted.
pub const TCJ2_SIGHTINGS_MAX_BYTES: u64 = 1024 * 65;

/// What a miss on an absent entry does with the artifact it compiles.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tcj2Admission {
    /// An earlier process recorded this key: it recurs. Store the artifact.
    StoreRecurred,
    /// First sighting of a large module: store the artifact at once.
    StoreFirstSighting,
    /// First sighting of a small module: its sighting is now recorded (or
    /// could not be, see the error); store nothing.
    RecordedSighting,
}

impl Tcj2Admission {
    /// Whether the caller should capture and store the artifact.
    pub fn stores(self) -> bool {
        !matches!(self, Self::RecordedSighting)
    }

    /// Stable name for counters.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::StoreRecurred => "store_recurred",
            Self::StoreFirstSighting => "store_first_sighting",
            Self::RecordedSighting => "record_sighting",
        }
    }
}

impl Tcj2Store {
    /// Whether `dir` certainly holds no entry for `key`: one `lstat` of the
    /// entry's path, without opening (or creating) the store. `false` for a
    /// present entry and for anything that is not a plain "not found", so the
    /// caller then takes the full, authenticated [`Tcj2Store::load`].
    pub fn entry_absent(dir: &Path, key: &[u8; 32]) -> bool {
        let path = dir.join(format!("{}.{TCJ2_EXT}", tcj2_key_hex(key)));
        matches!(fs::symlink_metadata(path), Err(error) if error.kind() == io::ErrorKind::NotFound)
    }
}

/// An append-only, bounded log of content keys that missed (see the section
/// docs). One lower-case hex key per line; read once per process.
#[derive(Debug)]
pub struct Tcj2Sightings {
    path: PathBuf,
    recorded: OnceLock<std::collections::HashSet<[u8; 32]>>,
    log: std::sync::Mutex<Option<fs::File>>,
}

impl Tcj2Sightings {
    /// The log at `path` (created on the first recorded sighting, mode 0600;
    /// its parent directory 0700 when it must be created).
    pub fn at(path: &Path) -> Self {
        Self {
            path: path.to_path_buf(),
            recorded: OnceLock::new(),
            log: std::sync::Mutex::new(None),
        }
    }

    /// The log's path.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Whether an earlier process recorded `key`.
    pub fn recurs(&self, key: &[u8; 32]) -> bool {
        self.recorded().contains(key)
    }

    /// Decide what a miss on an absent entry does (see the section docs),
    /// recording the sighting when it stores nothing. A sighting that cannot
    /// be written is returned as the error beside
    /// [`Tcj2Admission::RecordedSighting`]; it only costs a later recurrence.
    pub fn admit(
        &self,
        key: &[u8; 32],
        trust_ir_instructions: usize,
    ) -> (Tcj2Admission, Option<io::Error>) {
        if self.recurs(key) {
            return (Tcj2Admission::StoreRecurred, None);
        }
        if trust_ir_instructions >= TCJ2_FIRST_SIGHTING_STORE_MIN_TRUST_IR_INSTRUCTIONS {
            return (Tcj2Admission::StoreFirstSighting, None);
        }
        (Tcj2Admission::RecordedSighting, self.record(key).err())
    }

    /// Append `key`'s sighting (one write of one 65-byte line: with
    /// `O_APPEND` a record lands whole even when processes append at once).
    pub fn record(&self, key: &[u8; 32]) -> io::Result<()> {
        let mut log = self
            .log
            .lock()
            .map_err(|_| io::Error::other("sightings log lock poisoned"))?;
        if log.is_none() {
            let open = || {
                let mut options = fs::OpenOptions::new();
                options.append(true).create(true);
                #[cfg(unix)]
                {
                    use std::os::unix::fs::OpenOptionsExt;
                    options.mode(trust_cg_process_env::private_fs::PRIVATE_FILE_MODE);
                }
                options.open(&self.path)
            };
            let file = match open() {
                Err(error) if error.kind() == io::ErrorKind::NotFound => {
                    if let Some(parent) = self.path.parent() {
                        trust_cg_process_env::private_fs::create_private_dir_all(parent)?;
                    }
                    open()?
                }
                other => other?,
            };
            *log = Some(file);
        }
        let mut line = tcj2_key_hex(key);
        line.push('\n');
        log.as_mut()
            .ok_or_else(|| io::Error::other("sightings log not open"))?
            .write_all(line.as_bytes())
    }

    fn recorded(&self) -> &std::collections::HashSet<[u8; 32]> {
        self.recorded.get_or_init(|| {
            let mut keys = std::collections::HashSet::new();
            let Ok(file) = fs::File::open(&self.path) else {
                return keys;
            };
            let mut text = String::new();
            if file
                .take(TCJ2_SIGHTINGS_MAX_BYTES + 1)
                .read_to_string(&mut text)
                .is_err()
            {
                return keys;
            }
            if text.len() as u64 > TCJ2_SIGHTINGS_MAX_BYTES {
                // Bounded: restart the log (every record is only a hint).
                let _ = fs::remove_file(&self.path);
                return keys;
            }
            keys.extend(text.lines().filter_map(parse_tcj2_key_hex));
            keys
        })
    }
}

/// Parse one lower-case hex content key (the inverse of [`tcj2_key_hex`]).
pub fn parse_tcj2_key_hex(text: &str) -> Option<[u8; 32]> {
    let bytes = text.as_bytes();
    if bytes.len() != 64 {
        return None;
    }
    let digit = |c: u8| match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        _ => None,
    };
    let mut key = [0u8; 32];
    for (index, pair) in bytes.as_chunks::<2>().0.iter().enumerate() {
        key[index] = (digit(pair[0])? << 4) | digit(pair[1])?;
    }
    Some(key)
}

fn enforce_tcj2_file_cap(dir: &Path, cap: usize) -> io::Result<()> {
    let mut entries: Vec<(SystemTime, PathBuf)> = Vec::new();
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        let Ok(metadata) = entry.metadata() else {
            continue;
        };
        if !metadata.is_file() {
            continue;
        }
        let mtime = metadata.modified().unwrap_or(SystemTime::UNIX_EPOCH);
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("");
        if name.contains(".tmp.") {
            let stale = SystemTime::now()
                .duration_since(mtime)
                .is_ok_and(|age| age.as_secs() > 300);
            if stale {
                let _ = fs::remove_file(&path);
            }
            continue;
        }
        if path.extension().and_then(|ext| ext.to_str()) == Some(TCJ2_EXT) {
            entries.push((mtime, path));
        }
    }
    if entries.len() <= cap {
        return Ok(());
    }
    entries.sort();
    let excess = entries.len() - cap;
    for (_, path) in entries.into_iter().take(excess) {
        let _ = fs::remove_file(path);
    }
    Ok(())
}

#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
#[cfg(test)]
mod tests {
    use super::*;

    /// This file's fixtures are hand-built and carry no codegen license
    /// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
    /// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
    /// them passes because it was silently refused.
    fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
        trust_cg_codegen::CodegenLicensePolicy::default()
            .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
    }
    use crate::bcp_module_builder::{ENTRY_NAME, build_bcp_propagate_module};
    use std::collections::HashMap as StdHashMap;
    use std::sync::Mutex;
    use tempfile::TempDir;
    use trust_cg_codegen::{Compiler, CompilerConfig};

    static TEST_SERIAL: Mutex<()> = Mutex::new(());

    /// The default directory follows the one user-cache rule: an empty or
    /// relative `XDG_CACHE_HOME` is ignored and a relative `HOME` names no
    /// cache, never a directory below the working directory.
    #[test]
    fn default_buffer_cache_dir_is_the_one_user_cache_rule() {
        use std::ffi::OsStr;
        let at = |xdg: Option<&str>, home: Option<&str>| {
            default_buffer_cache_dir(xdg.map(OsStr::new), home.map(OsStr::new))
        };
        assert_eq!(
            at(Some("/xdg"), Some("/h")),
            Some(PathBuf::from("/xdg/trust-cg/jit-buf"))
        );
        for ignored in ["", "relative"] {
            assert_eq!(
                at(Some(ignored), Some("/h")),
                Some(PathBuf::from("/h/.cache/trust-cg/jit-buf"))
            );
        }
        assert_eq!(at(Some("relative"), Some("relative-home")), None);
        assert_eq!(at(None, Some("")), None);
    }

    fn private_temp_dir() -> TempDir {
        // Cache custody checks require private ancestors, regardless of the
        // shell's umask. Individual refusal tests widen their own fixtures.
        #[cfg(unix)]
        let tmp = {
            use std::os::unix::fs::PermissionsExt;
            tempfile::Builder::new()
                .permissions(fs::Permissions::from_mode(0o700))
                .tempdir()
        };
        #[cfg(not(unix))]
        let tmp = TempDir::new();
        tmp.expect("create private tempdir for buffer cache test")
    }

    struct CacheRootGuard {
        _tmp: TempDir,
        previous_root: Option<PathBuf>,
        previous_version: Option<[u8; 32]>,
        _serial: std::sync::MutexGuard<'static, ()>,
    }

    impl CacheRootGuard {
        fn new() -> Self {
            let serial = TEST_SERIAL
                .lock()
                .unwrap_or_else(|poison| poison.into_inner());
            let tmp = private_temp_dir();
            let previous_root = override_slot().lock().ok().and_then(|g| g.clone());
            // SAFETY: this guard owns a fresh tempdir for the lifetime of every
            // same-process buffer compiled and replayed by the test.
            unsafe { set_buffer_cache_root_for_tests(Some(tmp.path().to_path_buf())) };
            let previous_version = codegen_version_override_slot().lock().ok().and_then(|g| *g);
            Self {
                _tmp: tmp,
                previous_root,
                previous_version,
                _serial: serial,
            }
        }
    }

    impl Drop for CacheRootGuard {
        fn drop(&mut self) {
            // SAFETY: restore the serially held prior test root; all buffers
            // involved remain confined to this process.
            unsafe { set_buffer_cache_root_for_tests(self.previous_root.clone()) };
            set_codegen_version_hash_for_tests(self.previous_version);
        }
    }

    fn compile_scan_buffer() -> ExecutableBuffer {
        let module = build_bcp_propagate_module().expect("the kernel module builds");
        let config = CompilerConfig::for_host_jit();
        let extern_symbols: StdHashMap<String, *const u8> = StdHashMap::new();
        let result = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &extern_symbols)
            .expect("compile scan module");
        result.buffer
    }

    fn control_environment_digest(
        variables: impl IntoIterator<Item = (&'static str, &'static str)>,
    ) -> [u8; 32] {
        let mut hasher = Sha256::new();
        append_codegen_control_environment(
            &mut hasher,
            variables.into_iter().map(|(key, value)| {
                (
                    std::ffi::OsString::from(key),
                    std::ffi::OsString::from(value),
                )
            }),
        );
        hasher.finalize().into()
    }

    #[test]
    fn codegen_control_environment_identity_is_sorted_filtered_and_value_sensitive() {
        let first = control_environment_digest([
            ("TRUST_CG_DISABLE_PASSES", "alias_hoist"),
            ("TCG_NO_INLINE", "1"),
            ("UNRELATED", "ignored-a"),
        ]);
        let reordered = control_environment_digest([
            ("UNRELATED", "ignored-b"),
            ("TCG_NO_INLINE", "1"),
            ("TRUST_CG_DISABLE_PASSES", "alias_hoist"),
        ]);
        assert_eq!(first, reordered);

        let changed = control_environment_digest([
            ("TRUST_CG_DISABLE_PASSES", "alias_hoist"),
            ("TCG_NO_INLINE", "0"),
        ]);
        assert_ne!(first, changed);

        let ty_control = control_environment_digest([("TY_TRUST_CG_JIT_PROFILE", "1")]);
        let empty = control_environment_digest([]);
        assert_ne!(ty_control, empty);

        let compile_jobs_one =
            control_environment_digest([("TY_TRUST_CG_NATIVE_CALLOUT_COMPILE_JOBS", "1")]);
        let compile_jobs_eight =
            control_environment_digest([("TY_TRUST_CG_NATIVE_CALLOUT_COMPILE_JOBS", "8")]);
        assert_eq!(
            compile_jobs_one, compile_jobs_eight,
            "compile parallelism is a scheduling control, not machine-code identity material",
        );
        assert_eq!(
            compile_jobs_one, empty,
            "the scheduling-only compile-jobs key must be absent from machine-code identity",
        );
    }

    #[test]
    fn complete_target_contract_is_cache_key_material() {
        let digest = |target: &TargetDescriptor| {
            let mut hasher = Sha256::new();
            append_target_contract_identity(&mut hasher, target);
            <[u8; 32]>::from(hasher.finalize())
        };
        let base = TargetDescriptor::for_trust_cg_host_jit().with_features(Vec::<String>::new());
        let profiles = [
            vec![],
            vec!["lse"],
            vec!["dotprod"],
            vec!["fp16"],
            vec!["dotprod", "lse"],
            vec!["fp16", "lse"],
            vec!["dotprod", "fp16"],
            vec!["dotprod", "fp16", "lse"],
        ];
        let identities = profiles
            .into_iter()
            .map(|features| digest(&base.clone().with_features(features)))
            .collect::<std::collections::HashSet<_>>();
        assert_eq!(
            identities.len(),
            8,
            "every complete optional-feature contract must have a distinct replay key"
        );
    }

    #[test]
    fn disk_slot_identity_binds_process_hash_and_kernel_name() {
        let process_a = [0x11; 32];
        let process_b = [0x22; 32];
        let baseline = disk_slot_identity_for_process(7, "kernel-a", &process_a);
        assert_eq!(
            baseline,
            disk_slot_identity_for_process(7, "kernel-a", &process_a)
        );
        assert_ne!(
            baseline,
            disk_slot_identity_for_process(7, "kernel-a", &process_b)
        );
        assert_ne!(
            baseline,
            disk_slot_identity_for_process(8, "kernel-a", &process_a)
        );
        assert_ne!(
            baseline,
            disk_slot_identity_for_process(7, "kernel-b", &process_a)
        );
    }

    #[test]
    fn executable_buffer_round_trips_correctly() {
        let _g = CacheRootGuard::new();
        let buffer = compile_scan_buffer();
        let bytes = serialize_buffer(&buffer).expect("serialize buffer");
        let payload = decode_buffer_payload(&bytes).expect("decode");
        // SAFETY: this test round-trips a freshly compiled in-process buffer.
        let replayed = unsafe { publish_decoded_payload(payload) }.expect("re-publish");
        // The replayed buffer must expose the same entry symbol at the
        // same byte offset.
        let original_offset = *buffer
            .symbol_offsets()
            .get(ENTRY_NAME)
            .expect("scan entry present");
        let replayed_offset = *replayed
            .symbol_offsets()
            .get(ENTRY_NAME)
            .expect("scan entry present after replay");
        assert_eq!(original_offset, replayed_offset);
        assert_eq!(buffer.code_slice(), replayed.code_slice());
    }

    #[test]
    fn payload_length_checks_preserve_format_bounds() {
        assert_eq!(payload_u32_len(0, "code length").unwrap(), 0);
        assert_eq!(
            payload_u32_len(u32::MAX as usize, "code length").unwrap(),
            u32::MAX
        );
        #[cfg(target_pointer_width = "64")]
        {
            let error = payload_u32_len(u32::MAX as usize + 1, "code length").unwrap_err();
            assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
            assert!(error.to_string().contains("code length"));
        }
    }

    #[test]
    fn write_then_read_disk_round_trip() {
        let _g = CacheRootGuard::new();
        let buffer = compile_scan_buffer();
        write_buffer_to_disk(0xabcd_ef01, "scan", &buffer);
        assert_eq!(buffer_cache_file_count(), 1);
        // `0600` whatever the umask, as every cache file (`private_fs`).
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            let entry = buffer_cache_dir()
                .expect("cache dir")
                .join(cache_filename(0xabcd_ef01, "scan"));
            assert_eq!(fs::metadata(&entry).unwrap().mode() & 0o7777, 0o600);
        }
        let replayed = read_buffer_from_disk(0xabcd_ef01, "scan").expect("disk hit");
        assert_eq!(buffer.code_slice(), replayed.code_slice());
    }

    #[test]
    fn unkeyed_thread_local_control_bypasses_executable_buffer_disk_tier() {
        let _g = CacheRootGuard::new();
        let hash = 0xb10c_ed02;
        let kernel = "policy-blocked";

        crate::env_lock::with_env_overrides(&[("TCG_NO_SELECT_FOLD", "1")], || {
            write_buffer_bytes_to_disk(hash, kernel, b"must not be published");
            assert!(
                read_buffer_from_disk(hash, kernel).is_none(),
                "unkeyed policy must bypass executable-buffer lookup"
            );
        });
        assert!(
            !cache_path(hash, kernel).expect("cache path").exists(),
            "unkeyed policy must bypass executable-buffer publication"
        );
    }

    #[test]
    fn host_triple_mismatch_falls_back() {
        let _g = CacheRootGuard::new();
        let buffer = compile_scan_buffer();
        // Hand-craft a payload with a tampered host triple, then
        // observe the loader reject it as `Err`.
        let mut bytes = serialize_buffer(&buffer).expect("serialize buffer");
        // The host_triple field sits right after magic + version (= 8
        // bytes). Replace the 4-byte length prefix and string with a
        // marker triple that won't match any real host.
        let bogus = "bogus-os";
        let bogus_bytes = bogus.as_bytes();
        let bogus_len = bogus_bytes.len() as u32;
        let mut replacement = Vec::new();
        replacement.extend_from_slice(&bogus_len.to_le_bytes());
        replacement.extend_from_slice(bogus_bytes);
        // Determine the original host_triple span to know how many
        // bytes to splice out.
        let orig_len_bytes = &bytes[8..12];
        let orig_len = u32::from_le_bytes([
            orig_len_bytes[0],
            orig_len_bytes[1],
            orig_len_bytes[2],
            orig_len_bytes[3],
        ]) as usize;
        let orig_end = 12 + orig_len;
        bytes.splice(8..orig_end, replacement);
        // Recompute trailing SHA over the patched payload so the
        // integrity check passes and the host-triple check actually
        // gets exercised.
        let payload_len = bytes.len() - 32;
        let mut hasher = Sha256::new();
        hasher.update(&bytes[..payload_len]);
        let digest = hasher.finalize();
        bytes[payload_len..].copy_from_slice(&digest);
        let payload = decode_buffer_payload(&bytes).expect("decode-only OK");
        // SAFETY: the mismatch is rejected before publication; the payload is
        // otherwise a freshly serialized in-process test buffer.
        match unsafe { publish_decoded_payload(payload) } {
            Ok(_) => panic!("host triple mismatch must fail closed"),
            Err(e) => assert_eq!(e.kind(), io::ErrorKind::InvalidData),
        }
    }

    #[test]
    fn version_hash_mismatch_falls_back() {
        let _g = CacheRootGuard::new();
        let buffer = compile_scan_buffer();
        // Override the version hash, serialize, then restore.
        let bogus_hash = [0x42u8; 32];
        set_codegen_version_hash_for_tests(Some(bogus_hash));
        let bytes = serialize_buffer(&buffer).expect("serialize buffer");
        set_codegen_version_hash_for_tests(None);
        // Live process now has the default hash; the cached file has
        // `0x42` × 32, which must be rejected.
        let payload = decode_buffer_payload(&bytes).expect("decode-only OK");
        assert_eq!(payload.codegen_version_hash, bogus_hash);
        // SAFETY: the mismatch is rejected before publication; the payload is
        // otherwise a freshly serialized in-process test buffer.
        match unsafe { publish_decoded_payload(payload) } {
            Ok(_) => panic!("version hash mismatch must fail closed"),
            Err(e) => assert_eq!(e.kind(), io::ErrorKind::InvalidData),
        }
    }

    #[test]
    fn corrupt_disk_file_falls_back() {
        let _g = CacheRootGuard::new();
        let dir = ensure_cache_dir().expect("create cache dir");
        let path = dir.join(cache_filename(0xdead_beef, "scan"));
        fs::write(&path, b"this is not a real tcg-jit-buf file").expect("write garbage");
        assert!(read_buffer_from_disk(0xdead_beef, "scan").is_none());
    }

    #[test]
    fn truncated_file_falls_back() {
        let _g = CacheRootGuard::new();
        let buffer = compile_scan_buffer();
        write_buffer_to_disk(0x1234, "scan", &buffer);
        let path = cache_path(0x1234, "scan").unwrap();
        // Lop off the trailing SHA and one extra byte so the file is
        // both too short AND its hash no longer matches.
        let mut bytes = fs::read(&path).unwrap();
        bytes.truncate(bytes.len() - 33);
        fs::write(&path, &bytes).unwrap();
        assert!(read_buffer_from_disk(0x1234, "scan").is_none());
    }

    #[test]
    fn valid_buffer_copied_to_a_different_slot_falls_back() {
        let _g = CacheRootGuard::new();
        let buffer = compile_scan_buffer();
        write_buffer_to_disk(0x1111, "scan-a", &buffer);
        let source = cache_path(0x1111, "scan-a").unwrap();
        let swapped = cache_path(0x2222, "scan-b").unwrap();
        fs::copy(source, swapped).expect("copy valid payload into wrong cache slot");
        assert!(read_buffer_from_disk(0x2222, "scan-b").is_none());
        assert!(read_buffer_from_disk(0x1111, "scan-a").is_some());
    }

    #[test]
    fn replayed_buffer_invokes_correctly() {
        use crate::jit_bcp_kernel::JitBcpKernelProvider;
        use crate::solver_kernel_abi::SolverKernelHandle;

        let _g = CacheRootGuard::new();
        // Compile fresh, serialize, deserialize, and confirm the
        // round-tripped buffer can be invoked through the same
        // SolverKernelHandle dispatch as the original.
        let clauses: Vec<Vec<i32>> = vec![vec![1, 2], vec![-2, 3]];
        let num_vars = 3;
        let provider =
            JitBcpKernelProvider::compile(num_vars, clauses.clone()).expect("fresh compile");
        let original_bytes = provider.buffer().code_slice().to_vec();
        let serialized = serialize_buffer(provider.buffer()).expect("serialize buffer");
        let payload = decode_buffer_payload(&serialized).expect("decode");
        // SAFETY: this test round-trips a freshly compiled in-process buffer.
        let replayed_buffer = unsafe { publish_decoded_payload(payload) }.expect("re-publish");
        assert_eq!(replayed_buffer.code_slice(), original_bytes.as_slice());
        // Drive the original provider to confirm the fresh path still
        // works alongside an in-process replayed buffer (they must
        // not collide on mmap addresses).
        let mut handle = SolverKernelHandle::from_provider(&provider);
        let status = handle.call(&[]);
        assert_eq!(status.result, 0);
    }

    /// The TCJ1 payload carries code bytes only, so a buffer published with
    /// JIT unwind tables (here the frame-only tables of a `panic_unwind`
    /// module) must never be serialized: its replay would run without them.
    /// The same module without tables serializes (positive control).
    #[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
    #[test]
    fn buffers_with_unwind_tables_are_never_serialized() {
        use trust_ir::{
            Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty,
            ValueId,
        };

        let _g = CacheRootGuard::new();
        let mut module = Module::new("tcj1_unwind_refusal");
        let signature = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "answer", signature, BlockId::new(0));
        function.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(42),
                })
                .with_result(ValueId::new(0)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(0)],
                }),
            ],
        }];
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
        let compile = |panic_unwind: bool| {
            Compiler::new(CompilerConfig {
                panic_unwind,
                parallel: false,
                ..CompilerConfig::for_host_jit_unchecked()
            })
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &StdHashMap::new())
            .expect("the unchecked JIT publishes the module")
            .buffer
        };

        let plain = compile(false);
        assert!(plain.unwind_tables().is_none());
        serialize_buffer(&plain).expect("a buffer without unwind tables serializes");

        let walk = compile(true);
        assert!(walk.unwind_tables().is_some() && walk.unwind_tables_registered());
        let error = serialize_buffer(&walk).expect_err("unwind tables cannot ride a TCJ1 payload");
        assert_eq!(error.kind(), io::ErrorKind::Unsupported);
    }

    /// A buffer whose function states a target feature beyond the host-JIT
    /// profile (here `crc`, L03-P9) is never serialized: TCJ1 replays under
    /// the plain host-JIT contract, which does not name it. The same module
    /// without the attribute serializes (positive control).
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    #[test]
    fn buffers_with_function_target_features_are_never_serialized() {
        use trust_ir::{
            Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty,
            ValueId,
        };

        let _g = CacheRootGuard::new();
        let compile = |features: &[&str]| {
            let mut module = Module::new("tcj1_function_feature_refusal");
            let signature = module
                .add_func_type(FuncTy {
                    params: vec![],
                    returns: vec![Ty::I32],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut function = Function::new(FuncId::new(0), "answer", signature, BlockId::new(0));
            function.attrs.target_features =
                features.iter().map(|name| (*name).to_owned()).collect();
            function.blocks = vec![Block {
                id: BlockId::new(0),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(42),
                    })
                    .with_result(ValueId::new(0)),
                    InstrNode::new(Inst::Return {
                        values: vec![ValueId::new(0)],
                    }),
                ],
            }];
            module
                .try_add_function(function)
                .expect("Module::try_add_function: test fixture");
            Compiler::new(CompilerConfig {
                parallel: false,
                ..CompilerConfig::for_host_jit_unchecked()
            })
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &StdHashMap::new())
            .expect("the unchecked JIT publishes the module on this crc host")
            .buffer
        };

        let plain = compile(&[]);
        assert!(plain.aarch64_function_target_features().is_empty());
        serialize_buffer(&plain).expect("a buffer stating no feature serializes");

        let stating = compile(&["crc"]);
        assert!(
            stating
                .serialized_target_contract()
                .features
                .iter()
                .any(|feature| feature == "crc")
        );
        let error = serialize_buffer(&stating).expect_err("TCJ1 cannot record a stated feature");
        assert_eq!(error.kind(), io::ErrorKind::Unsupported);
    }

    // -- TCJ2 ----------------------------------------------------------------

    #[cfg(target_arch = "aarch64")]
    mod tcj2 {
        use super::super::*;
        use super::{TEST_SERIAL, private_temp_dir};
        use std::collections::HashMap as StdHashMap;
        use tempfile::TempDir;
        use trust_cg_codegen::jit::{JitCompiler, JitConfig};
        use trust_cg_ir::function::{MachFunction, Signature, Type};
        use trust_cg_ir::inst::{AArch64Opcode, MachInst};
        use trust_cg_ir::operand::MachOperand;
        use trust_cg_ir::operand::MachOperand::Special;
        use trust_cg_ir::regs::{FP, LR, SpecialReg, X0};

        const HOST: &str = "_trust_cg_tcj2_test_host";

        extern "C" fn host_times_three(x: i64) -> i64 {
            x * 3
        }

        fn push(func: &mut MachFunction, inst: MachInst) {
            let id = func.push_inst(inst);
            func.append_inst(func.entry, id);
        }

        fn caller() -> MachFunction {
            let mut func = MachFunction::new(
                "call_host".into(),
                Signature::new(vec![Type::I64], vec![Type::I64]),
            );
            push(
                &mut func,
                MachInst::new(
                    AArch64Opcode::StpPreIndex,
                    vec![
                        MachOperand::PReg(FP),
                        MachOperand::PReg(LR),
                        Special(SpecialReg::SP),
                        MachOperand::Imm(-16),
                    ],
                ),
            );
            push(
                &mut func,
                MachInst::new(AArch64Opcode::Bl, vec![MachOperand::Symbol(HOST.into())]),
            );
            push(
                &mut func,
                MachInst::new(
                    AArch64Opcode::LdpPostIndex,
                    vec![
                        MachOperand::PReg(FP),
                        MachOperand::PReg(LR),
                        Special(SpecialReg::SP),
                        MachOperand::Imm(16),
                    ],
                ),
            );
            push(
                &mut func,
                MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(&[X0]),
            );
            func
        }

        fn externs() -> StdHashMap<String, *const u8> {
            StdHashMap::from([(HOST.to_string(), host_times_three as *const u8)])
        }

        fn image() -> RelocatableImage {
            JitCompiler::new(JitConfig::default())
                .compile_raw_relocatable(&[caller()], &externs())
                .expect("raw link")
                .1
                .expect("relocatable")
        }

        const KEY: [u8; 32] = [0x5a; 32];
        const OTHER_KEY: [u8; 32] = [0xa5; 32];

        fn store_in(tmp: &TempDir) -> Tcj2Store {
            Tcj2Store::open(&tmp.path().join("machine-code")).expect("open store")
        }

        #[test]
        fn stored_entry_loads_relinks_and_runs() {
            let _serial = TEST_SERIAL.lock().unwrap_or_else(|p| p.into_inner());
            let tmp = private_temp_dir();
            let store = store_in(&tmp);
            let image = image();
            let written = store.store(&KEY, b"receipt-bytes", &image).unwrap();
            assert!(written > image.code_len() as u64);
            assert_eq!(store.entry_count(), 1);
            let entry = store.load(&KEY).expect("hit");
            assert_eq!(entry.receipt, b"receipt-bytes");
            assert_eq!(entry.image, image);
            let buffer = unsafe { entry.image.relink(&externs()) }.unwrap();
            let f: extern "C" fn(i64) -> i64 = unsafe {
                std::mem::transmute(buffer.get_fn_ptr_bound("call_host").unwrap().as_ptr())
            };
            assert_eq!(f(14), 42);
            // A second store over the same key replaces it; the store reopens
            // with the SAME seal key.
            store.store(&KEY, b"second", &image).unwrap();
            let reopened = store_in(&tmp);
            assert_eq!(reopened.load(&KEY).unwrap().receipt, b"second");
            assert_eq!(store.load(&OTHER_KEY).unwrap_err(), Tcj2Miss::Absent);
            store.evict(&KEY).unwrap();
            assert_eq!(store.load(&KEY).unwrap_err(), Tcj2Miss::Absent);
            store.evict(&KEY).unwrap();
        }

        #[test]
        fn every_tampered_entry_misses_and_never_decodes() {
            let _serial = TEST_SERIAL.lock().unwrap_or_else(|p| p.into_inner());
            let tmp = private_temp_dir();
            let store = store_in(&tmp);
            store.store(&KEY, b"r", &image()).unwrap();
            let path = store.entry_path(&KEY);
            let pristine = fs::read(&path).unwrap();
            for index in 0..pristine.len() {
                let mut flipped = pristine.clone();
                flipped[index] ^= 0x01;
                fs::write(&path, &flipped).unwrap();
                assert_eq!(
                    store.load(&KEY).unwrap_err(),
                    Tcj2Miss::Seal,
                    "flip at {index}"
                );
            }
            fs::write(&path, &pristine[..pristine.len() - 1]).unwrap();
            assert_eq!(store.load(&KEY).unwrap_err(), Tcj2Miss::Seal);
            fs::write(&path, &pristine).unwrap();
            assert!(store.load(&KEY).is_ok(), "the control entry loads");
        }

        #[test]
        fn a_forgery_sealed_under_another_key_or_copied_into_another_slot_misses() {
            let _serial = TEST_SERIAL.lock().unwrap_or_else(|p| p.into_inner());
            let tmp = private_temp_dir();
            let store = store_in(&tmp);
            let image = image();
            // Another store's key (a foreign or forged seal).
            let foreign = encode_tcj2(&[7u8; 32], &KEY, b"r", &image);
            fs::write(store.entry_path(&KEY), &foreign).unwrap();
            assert_eq!(store.load(&KEY).unwrap_err(), Tcj2Miss::Seal);
            // A valid entry renamed into another content key's slot.
            store.store(&KEY, b"r", &image).unwrap();
            fs::copy(store.entry_path(&KEY), store.entry_path(&OTHER_KEY)).unwrap();
            assert_eq!(store.load(&OTHER_KEY).unwrap_err(), Tcj2Miss::ContentKey);
            // A store opened on a copy of the directory with a replaced key.
            let copy = tmp.path().join("copy");
            let copied = Tcj2Store::with_seal_key_for_tests(&copy, [9u8; 32]);
            trust_cg_process_env::private_fs::create_private_dir_all(&copy).unwrap();
            fs::copy(store.entry_path(&KEY), copied.entry_path(&KEY)).unwrap();
            assert_eq!(copied.load(&KEY).unwrap_err(), Tcj2Miss::Seal);
        }

        #[test]
        fn another_pipeline_identity_misses() {
            let _serial = TEST_SERIAL.lock().unwrap_or_else(|p| p.into_inner());
            let tmp = private_temp_dir();
            let store = store_in(&tmp);
            set_codegen_version_hash_for_tests(Some([0x42; 32]));
            let written = store.store(&KEY, b"r", &image());
            set_codegen_version_hash_for_tests(None);
            written.unwrap();
            assert_eq!(store.load(&KEY).unwrap_err(), Tcj2Miss::CodegenVersion);
        }

        #[test]
        fn a_store_another_user_could_write_is_refused() {
            use std::os::unix::fs::PermissionsExt;
            let _serial = TEST_SERIAL.lock().unwrap_or_else(|p| p.into_inner());
            let tmp = private_temp_dir();
            let dir = tmp.path().join("machine-code");
            store_in(&tmp);
            fs::set_permissions(&dir, fs::Permissions::from_mode(0o777)).unwrap();
            assert!(Tcj2Store::open(&dir).is_err(), "world-writable store");
            fs::set_permissions(&dir, fs::Permissions::from_mode(0o700)).unwrap();
            let key = dir.join(TCJ2_SEAL_KEY_FILE);
            fs::set_permissions(&key, fs::Permissions::from_mode(0o644)).unwrap();
            assert!(Tcj2Store::open(&dir).is_err(), "readable seal key");
            fs::set_permissions(&key, fs::Permissions::from_mode(0o600)).unwrap();
            fs::remove_file(&key).unwrap();
            assert!(Tcj2Store::open(&dir).is_ok(), "a missing key is recreated");
        }

        #[test]
        fn store_refuses_mutable_ancestors_without_changing_them() {
            use std::os::unix::fs::{MetadataExt, PermissionsExt};

            let _serial = TEST_SERIAL.lock().unwrap_or_else(|p| p.into_inner());
            let tmp = private_temp_dir();
            let parent = tmp.path().join("shared");
            let dir = parent.join("machine-code");
            trust_cg_process_env::private_fs::create_private_dir_all(&dir).unwrap();
            for mode in [0o777, 0o770] {
                fs::set_permissions(&parent, fs::Permissions::from_mode(mode)).unwrap();
                assert_eq!(
                    Tcj2Store::open(&dir).unwrap_err().kind(),
                    io::ErrorKind::PermissionDenied
                );
                assert_eq!(fs::metadata(&parent).unwrap().mode() & 0o7777, mode);
                assert!(
                    !dir.join(TCJ2_SEAL_KEY_FILE).exists(),
                    "refuse before creating a secret"
                );
            }
            fs::set_permissions(&parent, fs::Permissions::from_mode(0o1777)).unwrap();
            let store = Tcj2Store::open(&dir).unwrap();
            assert_eq!(store.dir(), fs::canonicalize(&dir).unwrap());
        }

        #[test]
        fn store_uses_retained_canonical_path_after_alias_retargeting() {
            let _serial = TEST_SERIAL.lock().unwrap_or_else(|p| p.into_inner());
            let tmp = private_temp_dir();
            let original = store_in(&tmp);
            let alternate = Tcj2Store::open(&tmp.path().join("alternate")).unwrap();
            let alias = tmp.path().join("alias");
            std::os::unix::fs::symlink(original.dir(), &alias).unwrap();
            let through_alias = Tcj2Store::open(&alias).unwrap();
            assert_eq!(through_alias.dir(), original.dir());
            assert_eq!(through_alias.seal_key, original.seal_key);
            fs::remove_file(&alias).unwrap();
            std::os::unix::fs::symlink(alternate.dir(), &alias).unwrap();
            assert_ne!(fs::canonicalize(&alias).unwrap(), through_alias.dir());
            through_alias
                .store(&KEY, b"original-only", &image())
                .unwrap();
            assert_eq!(original.load(&KEY).unwrap().receipt, b"original-only");
            assert_eq!(alternate.load(&KEY).unwrap_err(), Tcj2Miss::Absent);
        }

        #[test]
        fn store_refuses_a_symlinked_secret_without_replacing_its_target() {
            let _serial = TEST_SERIAL.lock().unwrap_or_else(|p| p.into_inner());
            let tmp = private_temp_dir();
            let store = store_in(&tmp);
            let key = store.dir().join(TCJ2_SEAL_KEY_FILE);
            let moved = store.dir().join("retained-secret");
            let original = fs::read(&key).unwrap();
            fs::rename(&key, &moved).unwrap();
            std::os::unix::fs::symlink(&moved, &key).unwrap();
            assert!(Tcj2Store::open(store.dir()).is_err());
            assert!(fs::symlink_metadata(&key).unwrap().file_type().is_symlink());
            assert_eq!(fs::read(&moved).unwrap(), original);
        }

        #[test]
        fn a_damaged_entry_misses_and_the_next_store_replaces_it() {
            let _serial = TEST_SERIAL.lock().unwrap_or_else(|p| p.into_inner());
            let tmp = private_temp_dir();
            let store = store_in(&tmp);
            let image = image();
            // The remains of a crash mid-write, or a reader racing a direct
            // publish: a short file under the entry's final name.
            store.store(&KEY, b"r", &image).unwrap();
            let pristine = fs::read(store.entry_path(&KEY)).unwrap();
            fs::write(store.entry_path(&KEY), &pristine[..pristine.len() / 2]).unwrap();
            assert_eq!(store.load(&KEY).unwrap_err(), Tcj2Miss::Seal);
            store.store(&KEY, b"again", &image).unwrap();
            assert_eq!(store.load(&KEY).unwrap().receipt, b"again");
            // A first store of a key leaves no temporary file behind.
            store.store(&OTHER_KEY, b"other", &image).unwrap();
            let leftovers: Vec<_> = fs::read_dir(store.dir())
                .unwrap()
                .flatten()
                .filter(|entry| entry.file_name().to_string_lossy().contains(".tmp."))
                .collect();
            assert!(leftovers.is_empty(), "{leftovers:?}");
        }

        #[test]
        fn the_seal_key_is_published_once_and_never_replaced_by_a_second_creator() {
            let _serial = TEST_SERIAL.lock().unwrap_or_else(|p| p.into_inner());
            let tmp = private_temp_dir();
            let store = store_in(&tmp);
            let key_path = store.dir().join(TCJ2_SEAL_KEY_FILE);
            let original = fs::read(&key_path).unwrap();
            assert_eq!(original.as_slice(), store.seal_key.as_slice());
            // A second creator racing the first loses and keeps nothing.
            assert_eq!(
                create_seal_key(&key_path).unwrap_err().kind(),
                io::ErrorKind::AlreadyExists
            );
            assert_eq!(fs::read(&key_path).unwrap(), original);
            let leftovers: Vec<_> = fs::read_dir(store.dir())
                .unwrap()
                .flatten()
                .filter(|entry| entry.file_name().to_string_lossy().contains(".tmp."))
                .collect();
            assert!(leftovers.is_empty(), "{leftovers:?}");
            assert_eq!(store_in(&tmp).seal_key, store.seal_key);
        }

        #[test]
        fn the_file_cap_holds_across_handles_with_the_sweep_interval() {
            let _serial = TEST_SERIAL.lock().unwrap_or_else(|p| p.into_inner());
            let tmp = private_temp_dir();
            let image = image();
            // Each handle sweeps on its first store: a directory already over
            // the cap is brought back to it by the next process's first store.
            let first = store_in(&tmp);
            for index in 0..(DEFAULT_TCJ2_FILE_LIMIT + 8) {
                let mut key = [0u8; 32];
                key[..8].copy_from_slice(&(index as u64).to_le_bytes());
                first.store(&key, b"r", &image).unwrap();
            }
            assert!(first.entry_count() <= DEFAULT_TCJ2_FILE_LIMIT + TCJ2_SWEEP_INTERVAL as usize);
            store_in(&tmp).store(&KEY, b"r", &image).unwrap();
            assert!(first.entry_count() <= DEFAULT_TCJ2_FILE_LIMIT);
        }

        #[test]
        fn an_absent_entry_is_recognised_without_opening_the_store() {
            let _serial = TEST_SERIAL.lock().unwrap_or_else(|p| p.into_inner());
            let tmp = private_temp_dir();
            let dir = tmp.path().join("machine-code");
            assert!(Tcj2Store::entry_absent(&dir, &KEY));
            assert!(!dir.exists(), "the probe creates nothing");
            let store = store_in(&tmp);
            store.store(&KEY, b"r", &image()).unwrap();
            assert!(!Tcj2Store::entry_absent(&dir, &KEY));
            assert!(Tcj2Store::entry_absent(&dir, &OTHER_KEY));
        }

        #[test]
        fn admission_stores_a_recurring_key_or_a_large_module_and_records_the_rest() {
            let tmp = private_temp_dir();
            let path = tmp.path().join("sub").join("machine-code.sightings");
            let first = Tcj2Sightings::at(&path);
            let small = TCJ2_FIRST_SIGHTING_STORE_MIN_TRUST_IR_INSTRUCTIONS - 1;
            let large = TCJ2_FIRST_SIGHTING_STORE_MIN_TRUST_IR_INSTRUCTIONS;
            let (admission, error) = first.admit(&KEY, small);
            assert_eq!(admission, Tcj2Admission::RecordedSighting);
            assert!(error.is_none());
            assert!(!admission.stores());
            assert_eq!(
                first.admit(&OTHER_KEY, large).0,
                Tcj2Admission::StoreFirstSighting
            );
            {
                use std::os::unix::fs::MetadataExt;
                assert_eq!(fs::metadata(&path).unwrap().mode() & 0o777, 0o600);
            }
            // The recording process read the log before it recorded: the key
            // recurs for the NEXT process.
            let second = Tcj2Sightings::at(&path);
            assert!(second.recurs(&KEY));
            assert!(
                !second.recurs(&OTHER_KEY),
                "a large first sighting records nothing"
            );
            assert_eq!(second.admit(&KEY, small).0, Tcj2Admission::StoreRecurred);
        }

        #[test]
        fn a_malformed_or_oversized_sightings_log_is_only_a_hint() {
            let tmp = private_temp_dir();
            let path = tmp.path().join("machine-code.sightings");
            let mut text = format!(
                "{}\nnot-a-key\n{}\nZZ\n",
                tcj2_key_hex(&KEY),
                "f".repeat(63)
            );
            fs::write(&path, &text).unwrap();
            let log = Tcj2Sightings::at(&path);
            assert!(log.recurs(&KEY));
            assert!(!log.recurs(&OTHER_KEY));
            while (text.len() as u64) <= TCJ2_SIGHTINGS_MAX_BYTES {
                text.push_str(&format!("{}\n", tcj2_key_hex(&OTHER_KEY)));
            }
            fs::write(&path, &text).unwrap();
            let oversized = Tcj2Sightings::at(&path);
            assert!(!oversized.recurs(&KEY), "an oversized log is discarded");
            assert!(!path.exists(), "and restarted");
            assert_eq!(parse_tcj2_key_hex(&tcj2_key_hex(&KEY)), Some(KEY));
        }

        #[test]
        fn a_fresh_store_publishes_its_key_directly_and_skips_its_first_sweep() {
            use std::sync::atomic::Ordering;
            let _serial = TEST_SERIAL.lock().unwrap_or_else(|p| p.into_inner());
            let tmp = private_temp_dir();
            let fresh = store_in(&tmp);
            // The directory was created by this open: no sweep before the
            // TCJ2_SWEEP_INTERVAL-th store of this handle.
            assert_eq!(fresh.stores.load(Ordering::Relaxed), 1);
            // Only the key exists: no temporary name was ever published.
            let names: Vec<_> = fs::read_dir(fresh.dir())
                .unwrap()
                .flatten()
                .map(|entry| entry.file_name().to_string_lossy().into_owned())
                .collect();
            assert_eq!(names, vec![TCJ2_SEAL_KEY_FILE.to_string()]);
            {
                use std::os::unix::fs::MetadataExt;
                let key = fresh.dir().join(TCJ2_SEAL_KEY_FILE);
                assert_eq!(fs::metadata(&key).unwrap().mode() & 0o777, 0o600);
            }
            fresh.store(&KEY, b"fresh", &image()).unwrap();
            // An existing directory sweeps on its first store, reads the same
            // key, and serves what the fresh handle stored.
            let reopened = store_in(&tmp);
            assert_eq!(reopened.stores.load(Ordering::Relaxed), 0);
            assert_eq!(reopened.seal_key, fresh.seal_key);
            assert_eq!(reopened.load(&KEY).unwrap().receipt, b"fresh");
        }

        #[test]
        fn a_key_file_left_empty_by_a_racing_creator_is_replaced_once_and_its_entries_miss() {
            let _serial = TEST_SERIAL.lock().unwrap_or_else(|p| p.into_inner());
            let tmp = private_temp_dir();
            let dir = tmp.path().join("machine-code");
            // A creator that has made the key file but not yet written it.
            trust_cg_process_env::private_fs::create_private_dir_all(&dir).unwrap();
            let key = dir.join(TCJ2_SEAL_KEY_FILE);
            drop(trust_cg_process_env::private_fs::create_private_file(&key).unwrap());
            let opener = Tcj2Store::open(&dir).unwrap();
            assert_eq!(
                fs::read(&key).unwrap().as_slice(),
                opener.seal_key.as_slice()
            );
            // The racing creator then seals under the key it holds: a MISS for
            // everyone holding the published key, never a run.
            let racer = Tcj2Store::with_seal_key_for_tests(opener.dir(), [3u8; 32]);
            racer.store(&KEY, b"racer", &image()).unwrap();
            assert_eq!(opener.load(&KEY).unwrap_err(), Tcj2Miss::Seal);
            // Direct opener path after the file exists and is empty again.
            fs::write(&key, b"").unwrap();
            assert_eq!(
                open_seal_key(&key, true).unwrap().as_slice(),
                fs::read(&key).unwrap().as_slice()
            );
        }

        #[test]
        fn a_short_or_zeroed_seal_key_is_replaced_and_its_entries_miss() {
            let _serial = TEST_SERIAL.lock().unwrap_or_else(|p| p.into_inner());
            let tmp = private_temp_dir();
            let store = store_in(&tmp);
            store.store(&KEY, b"r", &image()).unwrap();
            let key = store.dir().join(TCJ2_SEAL_KEY_FILE);
            let original = fs::read(&key).unwrap();
            for damaged in [vec![0u8; 16], vec![0u8; 32], Vec::new(), vec![7u8; 33]] {
                fs::write(&key, &damaged).unwrap();
                let reopened = store_in(&tmp);
                let replaced = fs::read(&key).unwrap();
                assert_eq!(replaced.len(), 32);
                assert_ne!(replaced, vec![0u8; 32]);
                assert_ne!(replaced, original, "a new secret, not the lost one");
                assert_eq!(reopened.load(&KEY).unwrap_err(), Tcj2Miss::Seal);
            }
        }
    }
}
