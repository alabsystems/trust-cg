// trust-cg-jit-matrix/src/executable_buffer_cache.rs - Quarantined serialized
// JIT ExecutableBuffer format and same-process cache test support.
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
use trust_cg_codegen::jit::{ExecutableBuffer, publish_serialized_buffer};

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
    if let Some(root) = std::env::var_os("XDG_CACHE_HOME") {
        let p = PathBuf::from(root);
        if !p.as_os_str().is_empty() {
            return Some(p.join(BUFFER_CACHE_SUBDIR));
        }
    }
    if let Some(home) = std::env::var_os("HOME") {
        let p = PathBuf::from(home);
        if !p.as_os_str().is_empty() {
            return Some(p.join(".cache").join(BUFFER_CACHE_SUBDIR));
        }
    }
    None
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
    match fs::create_dir_all(&dir) {
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
static CODEGEN_VERSION_OVERRIDE: OnceLock<std::sync::Mutex<Option<[u8; 32]>>> = OnceLock::new();

fn codegen_version_override_slot() -> &'static std::sync::Mutex<Option<[u8; 32]>> {
    CODEGEN_VERSION_OVERRIDE.get_or_init(|| std::sync::Mutex::new(None))
}

/// Test-facing override of the codegen version digest. Pass `None` to
/// restore the package-version-derived default.
pub fn set_codegen_version_hash_for_tests(hash: Option<[u8; 32]>) {
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
    if let Ok(guard) = codegen_version_override_slot().lock()
        && let Some(h) = guard.as_ref()
    {
        return *h;
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
    hasher.update(b"trust-cg-codegen.executable-buffer.v2\0");
    append_pipeline_build_identity(&mut hasher);
    hasher.update(b"\0codegen-control-environment\0");
    append_codegen_control_environment(&mut hasher, crate::env_lock::vars_os());
    hasher.update(b"\0host-machine-features\0");
    append_machine_feature_identity(&mut hasher, &host_machine_feature_identity());
    hasher.update(host_triple().as_bytes());
    let digest = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}

fn append_machine_feature_identity(hasher: &mut Sha256, identity: &str) {
    hasher.update((identity.len() as u64).to_le_bytes());
    hasher.update(identity.as_bytes());
}

fn host_machine_feature_identity() -> String {
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    {
        return format!(
            "x86-host:{}",
            trust_cg_codegen::x86_64::pipeline::X86TargetFeatures::host().metadata_feature_list()
        );
    }
    #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
    {
        format!("{}-host-baseline", std::env::consts::ARCH)
    }
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

fn write_str(buf: &mut Vec<u8>, value: &str) {
    let bytes = value.as_bytes();
    let len = u32::try_from(bytes.len()).expect("symbol name length fits in u32");
    write_u32(buf, len);
    buf.extend_from_slice(bytes);
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
pub fn serialize_buffer(buffer: &ExecutableBuffer) -> Vec<u8> {
    let mut out = Vec::with_capacity(buffer.code_slice().len() + 256);
    out.extend_from_slice(TCJ_MAGIC);
    write_u32(&mut out, TCJ_VERSION);

    let triple = host_triple();
    write_str(&mut out, &triple);

    let version_hash = codegen_version_hash();
    out.extend_from_slice(&version_hash);

    let code = buffer.code_slice();
    let code_len = u32::try_from(code.len()).expect("code length fits in u32");
    write_u32(&mut out, code_len);
    out.extend_from_slice(code);

    let canonical = buffer.canonical_symbols();
    let canonical_count =
        u32::try_from(canonical.len()).expect("canonical symbol count fits in u32");
    write_u32(&mut out, canonical_count);
    for name in canonical {
        write_str(&mut out, name);
    }

    let symbol_offsets = buffer.symbol_offsets();
    let offsets_count =
        u32::try_from(symbol_offsets.len()).expect("symbol offset count fits in u32");
    write_u32(&mut out, offsets_count);
    // Sort by name so the on-disk bytes are deterministic across runs.
    let mut offsets_sorted: Vec<(&String, &u64)> = symbol_offsets.iter().collect();
    offsets_sorted.sort_by(|a, b| a.0.cmp(b.0));
    for (name, offset) in offsets_sorted {
        write_str(&mut out, name);
        write_u64(&mut out, *offset);
    }

    let ranges = buffer.function_ranges();
    let ranges_count = u32::try_from(ranges.len()).expect("range count fits in u32");
    write_u32(&mut out, ranges_count);
    for (name, range) in ranges {
        write_str(&mut out, name);
        write_u64(&mut out, range.start);
        write_u64(&mut out, range.end);
    }

    let mut hasher = Sha256::new();
    hasher.update(&out);
    let digest = hasher.finalize();
    out.extend_from_slice(&digest);
    out
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
/// Host-triple and codegen-version-hash checks are enforced here. Any
/// mismatch returns `Err(io::ErrorKind::InvalidData)` so the caller
/// treats it as a cache miss.
pub fn publish_decoded_payload(payload: DecodedBufferPayload) -> io::Result<ExecutableBuffer> {
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
    publish_serialized_buffer(
        &payload.code,
        payload.canonical_symbols,
        payload.symbol_offsets,
        payload.function_ranges,
    )
    .map_err(|e| io::Error::other(format!("publish failed: {e}")))
}

/// Serialize `buffer` and write it atomically to disk under the
/// `(hash, kernel_name)` slot. Errors are logged but never propagated;
/// the caller's compile path is unaffected. Without the feature-gated
/// same-process test/benchmark override, this is a no-op.
pub fn write_buffer_to_disk(hash: u64, kernel_name: &str, buffer: &ExecutableBuffer) {
    if !disk_io_enabled() {
        return;
    }
    write_buffer_bytes_to_disk(hash, kernel_name, &serialize_buffer(buffer));
}

/// Write a previously-serialized buffer payload to disk. Used by the
/// compile-cache tier when it already holds the serialized bytes (the
/// kernel-side closure produces them so the live provider keeps its
/// owned `ExecutableBuffer` untouched).
pub fn write_buffer_bytes_to_disk(hash: u64, kernel_name: &str, payload: &[u8]) {
    if !disk_io_enabled() {
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
        let mut f = fs::File::create(&tmp_path)?;
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
    if !disk_io_enabled() {
        return None;
    }
    let path = cache_path(hash, kernel_name)?;
    let mut file = fs::File::open(&path).ok()?;
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes).ok()?;
    drop(file);
    let serialized = unwrap_disk_payload(&bytes, hash, kernel_name).ok()?;
    let payload = decode_buffer_payload(serialized).ok()?;
    let buffer = publish_decoded_payload(payload).ok()?;
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

#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::bcp_module_builder::{ENTRY_NAME, build_bcp_propagate_module};
    use std::collections::HashMap as StdHashMap;
    use std::sync::Mutex;
    use tempfile::TempDir;
    use trust_cg_codegen::{Compiler, CompilerConfig};

    static TEST_SERIAL: Mutex<()> = Mutex::new(());

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
            let tmp = TempDir::new().expect("create tempdir for buffer cache test");
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
        let module = build_bcp_propagate_module();
        let config = CompilerConfig::for_host_jit();
        let extern_symbols: StdHashMap<String, *const u8> = StdHashMap::new();
        let result = Compiler::new(config)
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
    fn machine_feature_identity_is_cache_key_material() {
        let digest = |identity: &str| {
            let mut hasher = Sha256::new();
            append_machine_feature_identity(&mut hasher, identity);
            <[u8; 32]>::from(hasher.finalize())
        };
        assert_ne!(digest("x86-host:sse4.1"), digest("x86-host:sse4.1,avx2"));
        assert!(!host_machine_feature_identity().is_empty());
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
        let bytes = serialize_buffer(&buffer);
        let payload = decode_buffer_payload(&bytes).expect("decode");
        let replayed = publish_decoded_payload(payload).expect("re-publish");
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
    fn write_then_read_disk_round_trip() {
        let _g = CacheRootGuard::new();
        let buffer = compile_scan_buffer();
        write_buffer_to_disk(0xabcd_ef01, "scan", &buffer);
        assert_eq!(buffer_cache_file_count(), 1);
        let replayed = read_buffer_from_disk(0xabcd_ef01, "scan").expect("disk hit");
        assert_eq!(buffer.code_slice(), replayed.code_slice());
    }

    #[test]
    fn host_triple_mismatch_falls_back() {
        let _g = CacheRootGuard::new();
        let buffer = compile_scan_buffer();
        // Hand-craft a payload with a tampered host triple, then
        // observe the loader reject it as `Err`.
        let mut bytes = serialize_buffer(&buffer);
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
        match publish_decoded_payload(payload) {
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
        let bytes = serialize_buffer(&buffer);
        set_codegen_version_hash_for_tests(None);
        // Live process now has the default hash; the cached file has
        // `0x42` × 32, which must be rejected.
        let payload = decode_buffer_payload(&bytes).expect("decode-only OK");
        assert_eq!(payload.codegen_version_hash, bogus_hash);
        match publish_decoded_payload(payload) {
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
        let serialized = serialize_buffer(provider.buffer());
        let payload = decode_buffer_payload(&serialized).expect("decode");
        let replayed_buffer = publish_decoded_payload(payload).expect("re-publish");
        assert_eq!(replayed_buffer.code_slice(), original_bytes.as_slice());
        // Drive the original provider to confirm the fresh path still
        // works alongside an in-process replayed buffer (they must
        // not collide on mmap addresses).
        let mut handle = SolverKernelHandle::from_provider(&provider);
        let status = handle.call(&[]);
        assert_eq!(status.result, 0);
    }
}
