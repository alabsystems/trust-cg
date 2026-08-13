// trust-cg-opt/pgo/io.rs - .profdata writer + reader
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// v1 serializes as the little-endian binary container specified in
// designs/2026-04-18-pgo-workflow.md. v0 JSON is rejected with a migration
// diagnostic so profile-use cannot silently accept module-hash-only profiles.

//! I/O helpers for reading and writing `.profdata` files.

use std::collections::BTreeMap;
use std::fs;
use std::io::{self, Read, Write};
use std::path::Path;

use crate::cache::{CACHE_KEY_VERSION, CacheKey, StableHasher};

use super::schema::{
    BlockProfile, EdgeProfile, FunctionProfile, PROFDATA_MAGIC, PROFDATA_VERSION, ProfData,
    opt_level_label,
};

const PROFDATA_MAGIC_BYTES: &[u8; 8] = b"trcg-pgo";
const FIXED_HEADER_SIZE: usize = 64;
const MAX_PROFDATA_INPUT_BYTES: u64 = 64 * 1024 * 1024;
const FLAG_FUNCTION_ENTRY_COUNTS: u32 = 1 << 0;
const FLAG_BLOCK_COUNTS: u32 = 1 << 1;
const FLAG_EDGE_COUNTS: u32 = 1 << 2;
const FLAG_MERGED_MULTI_RUN: u32 = 1 << 4;

/// Errors that can be produced while reading or writing a `.profdata` file.
#[derive(Debug, thiserror::Error)]
pub enum ProfDataError {
    /// Filesystem or I/O failure.
    #[error("profdata I/O error: {0}")]
    Io(#[from] io::Error),
    /// JSON (de)serialization failure. Kept for tests that still create v0
    /// fixtures with serde; the v1 reader rejects JSON before parsing it.
    #[error("profdata serialization error: {0}")]
    Serde(#[from] serde_json::Error),
    /// File header did not start with [`PROFDATA_MAGIC`].
    #[error("profdata magic mismatch: expected {expected:?}, found {found:?}")]
    BadMagic {
        /// Expected magic string.
        expected: &'static str,
        /// Actual magic value found in the file.
        found: String,
    },
    /// v0 JSON profile data was found. Regenerate the profile to get a v1
    /// binary profile keyed by the full [`CacheKey`].
    #[error("profdata v0 JSON is unsupported; regenerate profile data as binary v1")]
    LegacyJsonUnsupported,
    /// Schema version is newer than this reader understands.
    #[error("profdata schema version too new: file={file}, reader={reader}")]
    VersionTooNew {
        /// Version recorded in the file.
        file: u32,
        /// Version supported by this reader.
        reader: u32,
    },
    /// A binary profile used an older schema version than v1.
    #[error("profdata schema version unsupported: file={file}, reader={reader}")]
    VersionTooOld {
        /// Version recorded in the file.
        file: u32,
        /// Version supported by this reader.
        reader: u32,
    },
    /// [`crate::cache::CACHE_KEY_VERSION`] mismatch.
    #[error("profdata cache_key_version mismatch: file={file}, reader={reader}")]
    CacheKeyVersionMismatch {
        /// `CACHE_KEY_VERSION` stored in the file.
        file: u32,
        /// Current [`crate::cache::CACHE_KEY_VERSION`].
        reader: u32,
    },
    /// The stored full profile key did not match the compile request.
    #[error("profdata profile key stale: file={file_key}, compile={compile_key}, reason={reason}")]
    StaleProfileKey {
        /// Cache-key digest recorded in the file.
        file_key: String,
        /// Cache-key digest for the module currently being compiled.
        compile_key: String,
        /// Human-readable mismatch category.
        reason: String,
    },
    /// Profiles could not be merged because a key/header field differed.
    #[error("profdata profiles are not merge-compatible: {field} mismatch ({left:?} != {right:?})")]
    IncompatibleMerge {
        /// Field that differed between candidate profiles.
        field: &'static str,
        /// Value in the first profile.
        left: String,
        /// Value in the later profile.
        right: String,
    },
    /// Summing counters during merge overflowed `u64`.
    #[error("profdata counter overflow while merging {field}")]
    CounterOverflow {
        /// Counter field being summed.
        field: &'static str,
    },
    /// A required 128-bit hex field was malformed.
    #[error("profdata malformed {field}: {value:?}")]
    MalformedHex {
        /// Field name.
        field: &'static str,
        /// Malformed value.
        value: String,
    },
    /// The profile ended before a complete field could be read.
    #[error("profdata truncated while reading {field}")]
    Truncated {
        /// Field being read.
        field: &'static str,
    },
    /// A string field was not valid UTF-8.
    #[error("profdata invalid UTF-8 in {field}")]
    InvalidUtf8 {
        /// Field being read.
        field: &'static str,
    },
    /// A format invariant was violated.
    #[error("profdata invalid format: {0}")]
    InvalidFormat(&'static str),
    /// A counted field exceeded the writer's supported range.
    #[error("profdata field too large: {0}")]
    TooLarge(&'static str),
    /// The trailer checksum did not match the payload.
    #[error("profdata checksum mismatch: file={file:#010x}, computed={computed:#010x}")]
    ChecksumMismatch {
        /// Checksum recorded in the file.
        file: u32,
        /// Checksum computed by the reader.
        computed: u32,
    },
}

/// Serialize a [`ProfData`] to a v1 binary byte vector.
pub fn encode(profile: &ProfData) -> Result<Vec<u8>, ProfDataError> {
    validate_logical_profile(profile)?;

    let mut bytes = Vec::new();
    bytes.extend_from_slice(PROFDATA_MAGIC_BYTES);
    write_u32(&mut bytes, PROFDATA_VERSION);
    write_u32(&mut bytes, profile_flags(profile));
    write_u32(&mut bytes, CACHE_KEY_VERSION);
    write_u32(&mut bytes, 0); // header size, patched after variable metadata.
    write_u128(
        &mut bytes,
        parse_hex_u128("profile_key_digest", &profile.profile_key_digest)?,
    );
    write_u128(
        &mut bytes,
        parse_hex_u128("module_hash", &profile.module_hash)?,
    );
    bytes.push(profile.opt_level_num);
    bytes.extend_from_slice(&[0; 7]);
    write_string(&mut bytes, &profile.target_triple, "target_triple")?;
    write_string(&mut bytes, &profile.target_cpu, "target_cpu")?;
    write_string_array(&mut bytes, &profile.target_features, "target_features")?;

    let header_size = u32::try_from(bytes.len()).map_err(|_| ProfDataError::TooLarge("header"))?;
    bytes[20..24].copy_from_slice(&header_size.to_le_bytes());

    write_u32(
        &mut bytes,
        u32::try_from(profile.functions.len())
            .map_err(|_| ProfDataError::TooLarge("function_count"))?,
    );
    for function in &profile.functions {
        write_function(&mut bytes, function)?;
    }

    let checksum = crc32c(&bytes);
    write_u32(&mut bytes, checksum);
    Ok(bytes)
}

/// Deserialize a [`ProfData`] from raw bytes, validating the v1 header and
/// trailer checksum.
pub fn decode(bytes: &[u8]) -> Result<ProfData, ProfDataError> {
    if bytes.starts_with(PROFDATA_MAGIC_BYTES) {
        return decode_binary_v1(bytes);
    }
    if bytes.first() == Some(&b'{') {
        return Err(ProfDataError::LegacyJsonUnsupported);
    }

    Err(ProfDataError::BadMagic {
        expected: PROFDATA_MAGIC,
        found: magic_preview(bytes),
    })
}

/// Write a [`ProfData`] to `path`, overwriting any existing file.
pub fn write_to_path(profile: &ProfData, path: &Path) -> Result<(), ProfDataError> {
    let bytes = encode(profile)?;
    let mut f = fs::File::create(path)?;
    f.write_all(&bytes)?;
    f.sync_all()?;
    Ok(())
}

/// Read a [`ProfData`] from `path`.
pub fn read_from_path(path: &Path) -> Result<ProfData, ProfDataError> {
    let size = fs::metadata(path)?.len();
    if size > MAX_PROFDATA_INPUT_BYTES {
        return Err(ProfDataError::TooLarge("file"));
    }

    let f = fs::File::open(path)?;
    let mut bytes = Vec::with_capacity(size as usize);
    let mut bounded = f.take(MAX_PROFDATA_INPUT_BYTES + 1);
    bounded.read_to_end(&mut bytes)?;
    if bytes.len() as u64 > MAX_PROFDATA_INPUT_BYTES {
        return Err(ProfDataError::TooLarge("file"));
    }
    decode(&bytes)
}

/// Verify a decoded [`ProfData`] against the full profile key for the module
/// currently being compiled.
pub fn enforce_fresh(profile: &ProfData, current_key: &CacheKey) -> Result<(), ProfDataError> {
    validate_header(profile)?;

    let expected = current_key.hex();
    if profile.profile_key_digest == expected {
        return Ok(());
    }

    Err(ProfDataError::StaleProfileKey {
        file_key: profile.profile_key_digest.clone(),
        compile_key: expected,
        reason: stale_reason(profile, current_key),
    })
}

/// Merge profiles from multiple canary windows for the same compile request.
///
/// Profiles are compatible only when their v1 headers and full profile key
/// fields match. The merge is deterministic: function, block, and edge records
/// are emitted in sorted key order regardless of input order.
pub fn merge_profdata(base: &ProfData, next: &ProfData) -> Result<ProfData, ProfDataError> {
    merge_compatible(&[base.clone(), next.clone()])
}

/// Merge any number of profiles from compatible canary windows.
pub fn merge_compatible(profiles: &[ProfData]) -> Result<ProfData, ProfDataError> {
    let (first, rest) = profiles
        .split_first()
        .ok_or(ProfDataError::InvalidFormat("cannot merge zero profiles"))?;
    validate_logical_profile(first)?;

    let mut merged = first.clone();
    merged.functions.clear();
    merged.merged = profiles.len() > 1 || first.merged;

    let mut functions: BTreeMap<String, FunctionAccumulator> = BTreeMap::new();
    accumulate_profile(first, &mut functions)?;
    for profile in rest {
        validate_logical_profile(profile)?;
        ensure_merge_compatible(first, profile)?;
        merged.merged = true;
        accumulate_profile(profile, &mut functions)?;
    }

    merged.functions = functions
        .into_iter()
        .map(|(name, acc)| acc.into_profile(name))
        .collect();
    Ok(merged)
}

fn decode_binary_v1(bytes: &[u8]) -> Result<ProfData, ProfDataError> {
    if bytes.len() < FIXED_HEADER_SIZE + 4 {
        return Err(ProfDataError::Truncated {
            field: "profdata header",
        });
    }

    let checksum_offset = bytes.len() - 4;
    let file_checksum = u32::from_le_bytes([
        bytes[checksum_offset],
        bytes[checksum_offset + 1],
        bytes[checksum_offset + 2],
        bytes[checksum_offset + 3],
    ]);
    let computed_checksum = crc32c(&bytes[..checksum_offset]);
    if file_checksum != computed_checksum {
        return Err(ProfDataError::ChecksumMismatch {
            file: file_checksum,
            computed: computed_checksum,
        });
    }

    let mut cursor = Cursor::new(&bytes[..checksum_offset]);
    let magic = cursor.read_exact(8, "magic")?;
    if magic != &PROFDATA_MAGIC_BYTES[..] {
        return Err(ProfDataError::BadMagic {
            expected: PROFDATA_MAGIC,
            found: String::from_utf8_lossy(magic).into_owned(),
        });
    }

    let version = cursor.read_u32("version")?;
    if version > PROFDATA_VERSION {
        return Err(ProfDataError::VersionTooNew {
            file: version,
            reader: PROFDATA_VERSION,
        });
    }
    if version < PROFDATA_VERSION {
        return Err(ProfDataError::VersionTooOld {
            file: version,
            reader: PROFDATA_VERSION,
        });
    }

    let flags = cursor.read_u32("flags")?;
    let cache_key_version = cursor.read_u32("cache_key_version")?;
    if cache_key_version != CACHE_KEY_VERSION {
        return Err(ProfDataError::CacheKeyVersionMismatch {
            file: cache_key_version,
            reader: CACHE_KEY_VERSION,
        });
    }

    let header_size = cursor.read_u32("header_size")? as usize;
    if header_size < FIXED_HEADER_SIZE {
        return Err(ProfDataError::InvalidFormat(
            "header_size is smaller than fixed header",
        ));
    }
    if header_size > checksum_offset {
        return Err(ProfDataError::Truncated {
            field: "variable header",
        });
    }

    let profile_key_digest = cursor.read_u128("profile_key_digest")?;
    let module_hash = cursor.read_u128("module_hash")?;
    let opt_level_num = cursor.read_u8("opt_level")?;
    let reserved = cursor.read_exact(7, "reserved header padding")?;
    if reserved.iter().any(|&b| b != 0) {
        return Err(ProfDataError::InvalidFormat(
            "reserved header padding must be zero",
        ));
    }

    let target_triple = cursor.read_string("target_triple")?;
    let target_cpu = cursor.read_string("target_cpu")?;
    let target_features = cursor.read_string_array("target_features")?;
    if cursor.position() != header_size {
        return Err(ProfDataError::InvalidFormat(
            "header_size does not match variable metadata",
        ));
    }

    let function_count = cursor.read_u32("function_count")? as usize;
    let mut functions = Vec::with_capacity(function_count);
    for _ in 0..function_count {
        functions.push(read_function(&mut cursor)?);
    }
    if cursor.position() != checksum_offset {
        return Err(ProfDataError::InvalidFormat(
            "trailing bytes before checksum",
        ));
    }

    let profile = ProfData {
        magic: PROFDATA_MAGIC.to_string(),
        version,
        cache_key_version,
        profile_key_digest: format!("{:032x}", profile_key_digest),
        module_hash: format!("{:032x}", module_hash),
        target_triple,
        target_cpu,
        target_features,
        opt_level: opt_level_label(opt_level_num).to_string(),
        opt_level_num,
        merged: flags & FLAG_MERGED_MULTI_RUN != 0,
        functions,
    };
    validate_header(&profile)?;
    Ok(profile)
}

fn write_function(bytes: &mut Vec<u8>, function: &FunctionProfile) -> Result<(), ProfDataError> {
    write_string(bytes, &function.name, "function.name")?;
    write_u64(bytes, stable_name_hash(&function.name));
    write_u64(bytes, function.call_count);
    write_u64(bytes, 0); // total_ns, reserved until timing fields land.
    write_u32(
        bytes,
        u32::try_from(function.blocks.len()).map_err(|_| ProfDataError::TooLarge("block_count"))?,
    );
    for block in &function.blocks {
        write_u32(bytes, block.block_id);
        write_u64(bytes, block.hits);
        write_u64(bytes, 0); // total_ns, reserved until timing fields land.
    }
    write_u32(
        bytes,
        u32::try_from(function.edges.len()).map_err(|_| ProfDataError::TooLarge("edge_count"))?,
    );
    for edge in &function.edges {
        write_u32(bytes, edge.from);
        write_u32(bytes, edge.to);
        write_u64(bytes, edge.hits);
    }
    Ok(())
}

fn read_function(cursor: &mut Cursor<'_>) -> Result<FunctionProfile, ProfDataError> {
    let name = cursor.read_string("function.name")?;
    let _name_hash = cursor.read_u64("function.name_hash")?;
    let call_count = cursor.read_u64("function.call_count")?;
    let _total_ns = cursor.read_u64("function.total_ns")?;

    let block_count = cursor.read_u32("function.block_count")? as usize;
    let mut blocks = Vec::with_capacity(block_count);
    for _ in 0..block_count {
        let block_id = cursor.read_u32("block.block_id")?;
        let hits = cursor.read_u64("block.hits")?;
        let _total_ns = cursor.read_u64("block.total_ns")?;
        blocks.push(BlockProfile::new(block_id, hits));
    }

    let edge_count = cursor.read_u32("function.edge_count")? as usize;
    let mut edges = Vec::with_capacity(edge_count);
    for _ in 0..edge_count {
        let from = cursor.read_u32("edge.from")?;
        let to = cursor.read_u32("edge.to")?;
        let hits = cursor.read_u64("edge.hits")?;
        edges.push(EdgeProfile::new(from, to, hits));
    }

    Ok(FunctionProfile {
        name,
        call_count,
        blocks,
        edges,
    })
}

fn validate_logical_profile(profile: &ProfData) -> Result<(), ProfDataError> {
    validate_header(profile)?;
    parse_hex_u128("profile_key_digest", &profile.profile_key_digest)?;
    parse_hex_u128("module_hash", &profile.module_hash)?;
    Ok(())
}

fn validate_header(profile: &ProfData) -> Result<(), ProfDataError> {
    if profile.magic != PROFDATA_MAGIC {
        return Err(ProfDataError::BadMagic {
            expected: PROFDATA_MAGIC,
            found: profile.magic.clone(),
        });
    }
    if profile.version > PROFDATA_VERSION {
        return Err(ProfDataError::VersionTooNew {
            file: profile.version,
            reader: PROFDATA_VERSION,
        });
    }
    if profile.version < PROFDATA_VERSION {
        return Err(ProfDataError::VersionTooOld {
            file: profile.version,
            reader: PROFDATA_VERSION,
        });
    }
    if profile.cache_key_version != CACHE_KEY_VERSION {
        return Err(ProfDataError::CacheKeyVersionMismatch {
            file: profile.cache_key_version,
            reader: CACHE_KEY_VERSION,
        });
    }
    Ok(())
}

fn stale_reason(profile: &ProfData, current_key: &CacheKey) -> String {
    let current_module = format!("{:032x}", current_key.module_hash());
    if profile.module_hash != current_module {
        return "module hash mismatch".to_string();
    }
    if profile.opt_level_num != current_key.opt_level() {
        return "opt-level mismatch".to_string();
    }
    if profile.target_triple != current_key.target_triple() {
        return "target triple mismatch".to_string();
    }
    if profile.target_cpu != current_key.cpu() {
        return "target CPU mismatch".to_string();
    }
    if profile.target_features != current_key.features() {
        return "target feature mismatch".to_string();
    }
    "profile key mismatch".to_string()
}

fn profile_flags(profile: &ProfData) -> u32 {
    let mut flags = 0;
    if !profile.functions.is_empty() {
        flags |= FLAG_FUNCTION_ENTRY_COUNTS;
    }
    if profile.functions.iter().any(|f| !f.blocks.is_empty()) {
        flags |= FLAG_BLOCK_COUNTS;
    }
    if profile.functions.iter().any(|f| !f.edges.is_empty()) {
        flags |= FLAG_EDGE_COUNTS;
    }
    if profile.merged {
        flags |= FLAG_MERGED_MULTI_RUN;
    }
    flags
}

fn ensure_merge_compatible(left: &ProfData, right: &ProfData) -> Result<(), ProfDataError> {
    compare_merge_field(
        "profile_key_digest",
        &left.profile_key_digest,
        &right.profile_key_digest,
    )?;
    compare_merge_field("module_hash", &left.module_hash, &right.module_hash)?;
    compare_merge_field("target_triple", &left.target_triple, &right.target_triple)?;
    compare_merge_field("target_cpu", &left.target_cpu, &right.target_cpu)?;
    compare_merge_field("opt_level", &left.opt_level, &right.opt_level)?;
    compare_merge_field(
        "opt_level_num",
        &left.opt_level_num.to_string(),
        &right.opt_level_num.to_string(),
    )?;
    if left.target_features != right.target_features {
        return Err(ProfDataError::IncompatibleMerge {
            field: "target_features",
            left: format!("{:?}", left.target_features),
            right: format!("{:?}", right.target_features),
        });
    }
    Ok(())
}

fn compare_merge_field(field: &'static str, left: &str, right: &str) -> Result<(), ProfDataError> {
    if left == right {
        return Ok(());
    }
    Err(ProfDataError::IncompatibleMerge {
        field,
        left: left.to_string(),
        right: right.to_string(),
    })
}

#[derive(Default)]
struct FunctionAccumulator {
    call_count: u64,
    blocks: BTreeMap<u32, u64>,
    edges: BTreeMap<(u32, u32), u64>,
}

impl FunctionAccumulator {
    fn into_profile(self, name: String) -> FunctionProfile {
        FunctionProfile {
            name,
            call_count: self.call_count,
            blocks: self
                .blocks
                .into_iter()
                .map(|(block_id, hits)| BlockProfile::new(block_id, hits))
                .collect(),
            edges: self
                .edges
                .into_iter()
                .map(|((from, to), hits)| EdgeProfile::new(from, to, hits))
                .collect(),
        }
    }
}

fn accumulate_profile(
    profile: &ProfData,
    functions: &mut BTreeMap<String, FunctionAccumulator>,
) -> Result<(), ProfDataError> {
    for function in &profile.functions {
        let acc = functions.entry(function.name.clone()).or_default();
        acc.call_count = checked_counter_add(acc.call_count, function.call_count, "call_count")?;
        for block in &function.blocks {
            let hits = acc.blocks.entry(block.block_id).or_default();
            *hits = checked_counter_add(*hits, block.hits, "block.hits")?;
        }
        for edge in &function.edges {
            let hits = acc.edges.entry((edge.from, edge.to)).or_default();
            *hits = checked_counter_add(*hits, edge.hits, "edge.hits")?;
        }
    }
    Ok(())
}

fn checked_counter_add(left: u64, right: u64, field: &'static str) -> Result<u64, ProfDataError> {
    left.checked_add(right)
        .ok_or(ProfDataError::CounterOverflow { field })
}

fn stable_name_hash(name: &str) -> u64 {
    let mut h = StableHasher::new();
    h.write(name.as_bytes());
    h.finish64()
}

fn parse_hex_u128(field: &'static str, value: &str) -> Result<u128, ProfDataError> {
    if value.len() != 32 {
        return Err(ProfDataError::MalformedHex {
            field,
            value: value.to_string(),
        });
    }
    u128::from_str_radix(value, 16).map_err(|_| ProfDataError::MalformedHex {
        field,
        value: value.to_string(),
    })
}

fn magic_preview(bytes: &[u8]) -> String {
    let end = bytes.len().min(PROFDATA_MAGIC_BYTES.len());
    String::from_utf8_lossy(&bytes[..end]).into_owned()
}

fn write_string(
    bytes: &mut Vec<u8>,
    value: &str,
    field: &'static str,
) -> Result<(), ProfDataError> {
    let len = u32::try_from(value.len()).map_err(|_| ProfDataError::TooLarge(field))?;
    write_u32(bytes, len);
    bytes.extend_from_slice(value.as_bytes());
    Ok(())
}

fn write_string_array(
    bytes: &mut Vec<u8>,
    values: &[String],
    field: &'static str,
) -> Result<(), ProfDataError> {
    let len = u32::try_from(values.len()).map_err(|_| ProfDataError::TooLarge(field))?;
    write_u32(bytes, len);
    for value in values {
        write_string(bytes, value, field)?;
    }
    Ok(())
}

fn write_u32(bytes: &mut Vec<u8>, value: u32) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

fn write_u64(bytes: &mut Vec<u8>, value: u64) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

fn write_u128(bytes: &mut Vec<u8>, value: u128) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

struct Cursor<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, pos: 0 }
    }

    fn position(&self) -> usize {
        self.pos
    }

    fn read_exact(&mut self, len: usize, field: &'static str) -> Result<&'a [u8], ProfDataError> {
        let end = self
            .pos
            .checked_add(len)
            .ok_or(ProfDataError::InvalidFormat("offset overflow"))?;
        if end > self.bytes.len() {
            return Err(ProfDataError::Truncated { field });
        }
        let slice = &self.bytes[self.pos..end];
        self.pos = end;
        Ok(slice)
    }

    fn read_u8(&mut self, field: &'static str) -> Result<u8, ProfDataError> {
        Ok(self.read_exact(1, field)?[0])
    }

    fn read_u32(&mut self, field: &'static str) -> Result<u32, ProfDataError> {
        let bytes = self.read_exact(4, field)?;
        Ok(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }

    fn read_u64(&mut self, field: &'static str) -> Result<u64, ProfDataError> {
        let bytes = self.read_exact(8, field)?;
        Ok(u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]))
    }

    fn read_u128(&mut self, field: &'static str) -> Result<u128, ProfDataError> {
        let bytes = self.read_exact(16, field)?;
        Ok(u128::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
            bytes[8], bytes[9], bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15],
        ]))
    }

    fn read_string(&mut self, field: &'static str) -> Result<String, ProfDataError> {
        let len = self.read_u32(field)? as usize;
        let bytes = self.read_exact(len, field)?;
        std::str::from_utf8(bytes)
            .map(|s| s.to_string())
            .map_err(|_| ProfDataError::InvalidUtf8 { field })
    }

    fn read_string_array(&mut self, field: &'static str) -> Result<Vec<String>, ProfDataError> {
        let len = self.read_u32(field)? as usize;
        let mut values = Vec::with_capacity(len);
        for _ in 0..len {
            values.push(self.read_string(field)?);
        }
        Ok(values)
    }
}

fn crc32c(bytes: &[u8]) -> u32 {
    let mut crc = !0_u32;
    for &byte in bytes {
        crc ^= u32::from(byte);
        for _ in 0..8 {
            let mask = 0_u32.wrapping_sub(crc & 1);
            crc = (crc >> 1) ^ (0x82f6_3b78 & mask);
        }
    }
    !crc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pgo::schema::{BlockProfile, EdgeProfile};

    fn sample_key() -> CacheKey {
        CacheKey::new(
            0xdead_beef_cafe_babe_0123_4567_89ab_cdef,
            2,
            "aarch64-unknown-unknown".into(),
            "generic-aarch64".into(),
            vec!["+neon".into(), "+fp16".into(), "+neon".into()],
        )
    }

    fn sample_profile() -> ProfData {
        let mut p = ProfData::new_with_key(&sample_key());

        let mut f = FunctionProfile::new("bfs_step");
        f.call_count = 10_000;
        f.blocks = vec![
            BlockProfile::new(0, 10_000),
            BlockProfile::new(1, 9_750),
            BlockProfile::new(2, 250),
            BlockProfile::new(3, 0),
        ];
        f.edges.push(EdgeProfile::new(0, 1, 9_750));
        p.functions.push(f);

        let g = FunctionProfile::new("cold_helper");
        p.functions.push(g);
        p
    }

    #[test]
    fn round_trip_bytes_match_structurally() {
        let p = sample_profile();
        let bytes = encode(&p).unwrap();
        assert_eq!(&bytes[0..8], PROFDATA_MAGIC_BYTES);
        assert_ne!(bytes[0], b'{', "v1 writer must not emit JSON");

        let q = decode(&bytes).unwrap();
        assert_eq!(p, q, "encode/decode round trip must be lossless");

        let f = q.function("bfs_step").unwrap();
        assert_eq!(f.call_count, 10_000);
        assert_eq!(f.block_hits(0), 10_000);
        assert_eq!(f.block_hits(1), 9_750);
        assert_eq!(f.block_hits(3), 0);
        assert_eq!(f.block_hits(42), 0, "missing blocks read back as 0");
        assert_eq!(f.edges, vec![EdgeProfile::new(0, 1, 9_750)]);
    }

    #[test]
    fn round_trip_file_path() {
        let p = sample_profile();
        let tmp = std::env::temp_dir().join(format!(
            "trust_cg_profdata_test_{}.profdata",
            std::process::id()
        ));
        write_to_path(&p, &tmp).unwrap();
        let q = read_from_path(&tmp).unwrap();
        assert_eq!(p, q);
        let _ = fs::remove_file(&tmp);
    }

    #[test]
    fn read_from_path_rejects_oversized_profile_before_decoding() {
        let tmp = std::env::temp_dir().join(format!(
            "trust_cg_profdata_oversized_{}_{}.profdata",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let file = fs::File::create(&tmp).unwrap();
        file.set_len(MAX_PROFDATA_INPUT_BYTES + 1).unwrap();
        drop(file);

        let result = read_from_path(&tmp);
        let _ = fs::remove_file(&tmp);

        match result {
            Err(ProfDataError::TooLarge("file")) => {}
            other => panic!("expected oversized file rejection, got {:?}", other),
        }
    }

    #[test]
    fn decode_rejects_bad_magic() {
        match decode(b"not a valid profdata") {
            Err(ProfDataError::BadMagic { .. }) => {}
            other => panic!("expected BadMagic, got {:?}", other),
        }
    }

    #[test]
    fn decode_rejects_v0_json_with_migration_error() {
        let mut p = sample_profile();
        p.version = 0;
        let bytes = serde_json::to_vec_pretty(&p).unwrap();
        match decode(&bytes) {
            Err(ProfDataError::LegacyJsonUnsupported) => {}
            other => panic!("expected LegacyJsonUnsupported, got {:?}", other),
        }
    }

    #[test]
    fn decode_rejects_future_version() {
        let p = sample_profile();
        let mut bytes = encode(&p).unwrap();
        bytes[8..12].copy_from_slice(&(PROFDATA_VERSION + 1).to_le_bytes());
        let checksum_offset = bytes.len() - 4;
        let checksum = crc32c(&bytes[..checksum_offset]);
        bytes[checksum_offset..].copy_from_slice(&checksum.to_le_bytes());

        match decode(&bytes) {
            Err(ProfDataError::VersionTooNew { file, reader }) => {
                assert_eq!(file, PROFDATA_VERSION + 1);
                assert_eq!(reader, PROFDATA_VERSION);
            }
            other => panic!("expected VersionTooNew, got {:?}", other),
        }
    }

    #[test]
    fn decode_rejects_cache_key_version_mismatch() {
        let p = sample_profile();
        let mut bytes = encode(&p).unwrap();
        bytes[16..20].copy_from_slice(&CACHE_KEY_VERSION.wrapping_add(7).to_le_bytes());
        let checksum_offset = bytes.len() - 4;
        let checksum = crc32c(&bytes[..checksum_offset]);
        bytes[checksum_offset..].copy_from_slice(&checksum.to_le_bytes());

        match decode(&bytes) {
            Err(ProfDataError::CacheKeyVersionMismatch { .. }) => {}
            other => panic!("expected CacheKeyVersionMismatch, got {:?}", other),
        }
    }

    #[test]
    fn decode_rejects_checksum_mismatch() {
        let p = sample_profile();
        let mut bytes = encode(&p).unwrap();
        bytes[70] ^= 0x55;
        match decode(&bytes) {
            Err(ProfDataError::ChecksumMismatch { .. }) => {}
            other => panic!("expected ChecksumMismatch, got {:?}", other),
        }
    }

    #[test]
    fn enforce_fresh_accepts_matching_key() {
        let p = sample_profile();
        enforce_fresh(&p, &sample_key()).unwrap();
    }

    #[test]
    fn enforce_fresh_rejects_opt_level_mismatch() {
        let p = sample_profile();
        let key = CacheKey::new(
            p.module_hash_u128().unwrap(),
            3,
            p.target_triple.clone(),
            p.target_cpu.clone(),
            p.target_features.clone(),
        );
        match enforce_fresh(&p, &key) {
            Err(ProfDataError::StaleProfileKey { reason, .. }) => {
                assert_eq!(reason, "opt-level mismatch");
            }
            other => panic!("expected StaleProfileKey, got {:?}", other),
        }
    }
}
