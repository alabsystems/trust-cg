// trust-cg-opt/pgo/schema.rs - .profdata on-disk schema (v0)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: designs/2026-04-18-pgo-workflow.md
//
// v1 serializes as a little-endian binary container. v0 JSON is no longer
// accepted by the writer; the reader returns an explicit migration diagnostic
// instead of silently falling back to module-hash-only freshness.

//! Logical schema for `.profdata` files.
//!
//! A `.profdata` file describes per-function basic-block execution counts
//! captured during a `--profile-generate` run. v1 profiles are keyed by the
//! full [`crate::cache::CacheKey`] digest so stale profiles are rejected when
//! the module, opt level, target triple, CPU, or target features differ.
//!
//! The v1 wire format is binary. See
//! [`write_to_path`](crate::pgo::write_to_path) and
//! [`read_from_path`](crate::pgo::read_from_path).

use serde::{Deserialize, Serialize};

use crate::cache::{CACHE_KEY_VERSION, CacheKey};

/// File magic string embedded in every `.profdata` file.
///
/// ASCII "trcg-pgo" in the spelling used by [`ProfData::magic`].
/// Kept in the JSON so a plain text `head` on a corrupt file is informative.
pub const PROFDATA_MAGIC: &str = "trcg-pgo";

/// Current binary schema version. Bump on any incompatible layout change.
///
/// The writer always stamps this value. The reader rejects files whose
/// `version` is greater than its own `PROFDATA_VERSION`.
pub const PROFDATA_VERSION: u32 = 1;

/// Per-function profile record.
///
/// Blocks are identified by their [`trust_cg_ir::BlockId`] value (`u32`).
/// Counts are raw `u64` hit totals and may be zero for blocks that were
/// not executed by the canary run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionProfile {
    /// Mangled function symbol name, as it appears in
    /// [`trust_cg_ir::MachFunction::name`].
    pub name: String,
    /// Total call count (entry-to-the-function). Mirrors the existing
    /// `ProfileHookMode::CallCounts` trampoline data.
    #[serde(default)]
    pub call_count: u64,
    /// Per-block hit counts. `blocks[i].block_id` is the `u32` from
    /// [`trust_cg_ir::BlockId`]. Order is not semantically significant; the
    /// reader indexes by `block_id`.
    #[serde(default)]
    pub blocks: Vec<BlockProfile>,
    /// Optional per-edge counts (`(from_block, to_block) -> hits`).
    ///
    /// v0 readers/writers may leave this empty. The field is reserved for
    /// Phase 3 edge-count instrumentation.
    #[serde(default)]
    pub edges: Vec<EdgeProfile>,
}

impl FunctionProfile {
    /// Create a new function profile with no counters.
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            call_count: 0,
            blocks: Vec::new(),
            edges: Vec::new(),
        }
    }

    /// Look up the hit count for a block id, returning 0 if the block was
    /// not present in the profile (i.e., not executed or not instrumented).
    pub fn block_hits(&self, block_id: u32) -> u64 {
        self.blocks
            .iter()
            .find(|b| b.block_id == block_id)
            .map(|b| b.hits)
            .unwrap_or(0)
    }
}

/// Per-block counter payload.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BlockProfile {
    /// Raw `u32` value of the `BlockId`.
    pub block_id: u32,
    /// Total hits during the canary run. `0` means the block was not
    /// executed by the canary (treat as cold, not as infinitely-rare).
    pub hits: u64,
}

impl BlockProfile {
    /// Convenience constructor.
    pub fn new(block_id: u32, hits: u64) -> Self {
        Self { block_id, hits }
    }
}

/// Per-edge counter payload (reserved; v0 writers emit none).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EdgeProfile {
    /// Source block id.
    pub from: u32,
    /// Destination block id.
    pub to: u32,
    /// Total traversals during the canary run.
    pub hits: u64,
}

impl EdgeProfile {
    /// Convenience constructor.
    pub fn new(from: u32, to: u32, hits: u64) -> Self {
        Self { from, to, hits }
    }
}

/// Top-level profile document.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProfData {
    /// Magic string, always [`PROFDATA_MAGIC`].
    #[serde(default = "default_magic")]
    pub magic: String,
    /// Schema version, always [`PROFDATA_VERSION`] on write.
    #[serde(default = "default_version")]
    pub version: u32,
    /// Hash-algorithm version ([`CACHE_KEY_VERSION`]). If this differs
    /// from the reader's version, the profile must be rejected because
    /// the `module_hash` is not comparable.
    #[serde(default = "default_cache_key_version")]
    pub cache_key_version: u32,
    /// 128-bit digest of the full [`CacheKey`] for the compile request,
    /// serialized as 32 lowercase hex characters.
    #[serde(default)]
    pub profile_key_digest: String,
    /// 128-bit stable hash of the source module, serialized as a
    /// 32-character lowercase hex string so the file is greppable.
    pub module_hash: String,
    /// Target triple included in the profile key.
    #[serde(default)]
    pub target_triple: String,
    /// Target CPU model included in the profile key.
    #[serde(default)]
    pub target_cpu: String,
    /// Target features included in the profile key. The key constructor
    /// canonicalizes this list by sorting and deduplicating it.
    #[serde(default)]
    pub target_features: Vec<String>,
    /// Opt-level label included for diagnostics. v1 binary stores the
    /// numeric value separately; this field uses the human-readable form.
    #[serde(default)]
    pub opt_level: String,
    /// Numeric optimization level included in the profile key.
    #[serde(default)]
    pub opt_level_num: u8,
    /// True when this profile was merged from multiple compatible canary runs.
    #[serde(default)]
    pub merged: bool,
    /// Per-function records.
    #[serde(default)]
    pub functions: Vec<FunctionProfile>,
}

fn default_magic() -> String {
    PROFDATA_MAGIC.to_string()
}
fn default_version() -> u32 {
    PROFDATA_VERSION
}
fn default_cache_key_version() -> u32 {
    CACHE_KEY_VERSION
}

impl ProfData {
    /// Create an empty profile using a legacy module-hash-only default key.
    ///
    /// New profile writers should prefer [`Self::new_with_key`] so the file
    /// records the real compile-request freshness key.
    pub fn new(module_hash: u128) -> Self {
        let key = CacheKey::new(module_hash, 0, String::new(), String::new(), Vec::new());
        Self::new_with_key(&key)
    }

    /// Create an empty `ProfData` stamped with the canonical v1 header fields
    /// and the supplied full profile key.
    pub fn new_with_key(profile_key: &CacheKey) -> Self {
        Self {
            magic: PROFDATA_MAGIC.to_string(),
            version: PROFDATA_VERSION,
            cache_key_version: CACHE_KEY_VERSION,
            profile_key_digest: format!("{:032x}", profile_key.digest()),
            module_hash: format!("{:032x}", profile_key.module_hash()),
            target_triple: profile_key.target_triple().to_string(),
            target_cpu: profile_key.cpu().to_string(),
            target_features: profile_key.features().to_vec(),
            opt_level: opt_level_label(profile_key.opt_level()).to_string(),
            opt_level_num: profile_key.opt_level(),
            merged: false,
            functions: Vec::new(),
        }
    }

    /// Return the module hash as the raw `u128`.
    ///
    /// Returns `None` if the stored hex string is malformed.
    pub fn module_hash_u128(&self) -> Option<u128> {
        parse_hex_u128(&self.module_hash)
    }

    /// Return the full profile key digest as the raw `u128`.
    ///
    /// Returns `None` if the stored hex string is malformed or missing.
    pub fn profile_key_digest_u128(&self) -> Option<u128> {
        parse_hex_u128(&self.profile_key_digest)
    }

    /// Refresh all key-derived fields from a full profile key.
    pub fn set_profile_key(&mut self, profile_key: &CacheKey) {
        self.version = PROFDATA_VERSION;
        self.cache_key_version = CACHE_KEY_VERSION;
        self.profile_key_digest = format!("{:032x}", profile_key.digest());
        self.module_hash = format!("{:032x}", profile_key.module_hash());
        self.target_triple = profile_key.target_triple().to_string();
        self.target_cpu = profile_key.cpu().to_string();
        self.target_features = profile_key.features().to_vec();
        self.opt_level = opt_level_label(profile_key.opt_level()).to_string();
        self.opt_level_num = profile_key.opt_level();
    }

    /// Look up a function profile by name.
    pub fn function(&self, name: &str) -> Option<&FunctionProfile> {
        self.functions.iter().find(|f| f.name == name)
    }

    /// Mutable lookup by name; inserts a default record if missing.
    pub fn function_mut_or_insert(&mut self, name: &str) -> &mut FunctionProfile {
        let pos = self.functions.iter().position(|f| f.name == name);
        match pos {
            Some(i) => &mut self.functions[i],
            None => {
                self.functions.push(FunctionProfile::new(name));
                self.functions.last_mut().unwrap()
            }
        }
    }
}

fn parse_hex_u128(hex: &str) -> Option<u128> {
    if hex.len() != 32 {
        return None;
    }
    u128::from_str_radix(hex, 16).ok()
}

/// Human-readable opt level label for profile diagnostics.
pub fn opt_level_label(level: u8) -> &'static str {
    match level {
        0 => "O0",
        1 => "O1",
        2 => "O2",
        3 => "O3",
        _ => "O?",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn profdata_constructs_with_stamped_headers() {
        let key = CacheKey::new(
            0x1234_5678_9abc_def0_1122_3344_5566_7788,
            2,
            "aarch64-unknown-unknown".into(),
            "generic-aarch64".into(),
            vec!["+neon".into()],
        );
        let p = ProfData::new_with_key(&key);
        assert_eq!(p.magic, PROFDATA_MAGIC);
        assert_eq!(p.version, PROFDATA_VERSION);
        assert_eq!(p.cache_key_version, CACHE_KEY_VERSION);
        assert_eq!(p.profile_key_digest_u128(), Some(key.digest()));
        assert_eq!(p.module_hash.len(), 32);
        assert_eq!(
            p.module_hash_u128(),
            Some(0x1234_5678_9abc_def0_1122_3344_5566_7788_u128)
        );
        assert_eq!(p.opt_level_num, 2);
        assert_eq!(p.opt_level, "O2");
        assert_eq!(p.target_triple, "aarch64-unknown-unknown");
        assert_eq!(p.target_cpu, "generic-aarch64");
        assert_eq!(p.target_features, vec!["+neon"]);
    }

    #[test]
    fn function_profile_block_hits_defaults_to_zero() {
        let mut f = FunctionProfile::new("foo");
        f.blocks.push(BlockProfile::new(0, 10));
        f.blocks.push(BlockProfile::new(1, 20));
        assert_eq!(f.block_hits(0), 10);
        assert_eq!(f.block_hits(1), 20);
        assert_eq!(f.block_hits(99), 0);
    }

    #[test]
    fn function_mut_or_insert_idempotent() {
        let mut p = ProfData::new(0);
        p.function_mut_or_insert("foo").call_count = 3;
        p.function_mut_or_insert("foo").call_count += 5;
        assert_eq!(p.functions.len(), 1);
        assert_eq!(p.function("foo").unwrap().call_count, 8);
    }

    #[test]
    fn module_hash_u128_rejects_malformed() {
        let mut p = ProfData::new(0);
        p.module_hash = "not-hex".to_string();
        assert!(p.module_hash_u128().is_none());
    }
}
