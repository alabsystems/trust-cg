// trust-cg-codegen/pgo_runner.rs - host-JIT PGO runner API
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Host-JIT PGO profile-generate/profile-use helpers.
//!
//! This module exposes the reusable API behind the CLI's host-JIT PGO capture
//! path. It compiles a trust_ir module with [`ProfileHookMode::BlockCounts`],
//! invokes one bounded entry shape, writes binary v1 `.profdata`, and returns
//! typed report data matching the `trust-cg.profile_report.v1` JSON shape.
//!
//! Downstream TY/MCC consumers should treat
//! [`HostJitPgoProfileAuthorityEvidence`] and its
//! [`HostJitPgoProfileAuthorityEvidence::manifest_lines`] helper as the
//! canonical sidecar surface for profile reuse authority. The manifest rows
//! are deliberately flat and escaped so consumers can forward Trust Codegen-owned
//! status, reason, target compatibility, and authorization fields without
//! reinterpreting profile-use policy locally.

use std::collections::HashMap;
use std::fs;
use std::io::Read;
use std::path::Path;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::compiler::{CompileError, Compiler, CompilerConfig, JitCompilationResult};
use crate::jit::{ExecutableBuffer, ProfileHookMode};
use crate::pipeline::OptLevel;
use crate::target::{Target, TargetSpec};

/// Schema tag for host-JIT PGO reports.
pub const TRUST_CG_PROFILE_REPORT_SCHEMA_V1: &str = "trust-cg.profile_report.v1";
/// Schema tag for the downstream host-JIT PGO provenance descriptor.
pub const TRUST_CG_HOST_JIT_PGO_PROVENANCE_DESCRIPTOR_SCHEMA: &str =
    "trust-cg.host_jit_pgo.provenance_descriptor.v1";
/// Version for [`TRUST_CG_HOST_JIT_PGO_PROVENANCE_DESCRIPTOR_SCHEMA`].
pub const TRUST_CG_HOST_JIT_PGO_PROVENANCE_DESCRIPTOR_SCHEMA_VERSION: u32 = 1;
/// Schema tag for host-JIT PGO profile authority evidence.
pub const TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_EVIDENCE_SCHEMA: &str =
    "trust-cg.host_jit_pgo.profile_authority.v1";
/// Version for [`TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_EVIDENCE_SCHEMA`].
pub const TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_EVIDENCE_SCHEMA_VERSION: u32 = 1;
/// Schema tag for line-oriented profile authority manifest rows.
pub const TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_MANIFEST_SCHEMA: &str =
    "trust-cg.host_jit_pgo.profile_authority.manifest.v1";
/// Version for [`TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_MANIFEST_SCHEMA`].
pub const TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_MANIFEST_SCHEMA_VERSION: u32 = 1;
/// Default bounded inputs for single-`u64` canary entry points.
pub const DEFAULT_I64_PROFILE_INPUTS: &[u64] = &[1, 2, 3, 4, 5, 6, 7, 0, 0, 0];
/// Default bounded parent values for the TY parent-loop entry shape.
pub const DEFAULT_TY_PARENT_PROFILE_INPUTS: &[u64] = &[2, 5, 8, 13, 21, 34];
/// Number of `u64` slots written by the supported TY parent-loop shape.
pub const TY_PARENT_SUMMARY_SLOTS: usize = 5;
/// Profile key fields that must match before a `.profdata` file is reusable.
pub const HOST_JIT_PGO_PROFILE_KEY_FIELDS: &[&str] = &[
    "profile_key_digest",
    "module_hash",
    "target_triple",
    "target_cpu",
    "target_features",
    "opt_level",
    "opt_level_num",
    "cache_key_version",
];
/// Capture fields emitted by profile-generate reports.
pub const HOST_JIT_PGO_CAPTURE_FIELDS: &[&str] = &[
    "kind",
    "hook_mode",
    "entry",
    "entry_shape",
    "call_count",
    "inputs",
    "window",
    "return_value",
    "ty_summary",
];
/// Profile-use fields emitted by profile-use reports.
pub const HOST_JIT_PGO_PROFILE_USE_FIELDS: &[&str] = &[
    "fresh",
    "consumer",
    "scheduled",
    "pass",
    "reason",
    "summary",
];
/// Fields that must indicate a fresh scheduled profile-use compile before
/// downstream consumers treat the profile as reused by the compiled function.
pub const HOST_JIT_PGO_PROFILE_USE_SOUNDNESS_FIELDS: &[&str] =
    &["fresh", "scheduled", "pass", "reason"];
/// Fields emitted by host-JIT PGO profile authority evidence.
pub const HOST_JIT_PGO_PROFILE_AUTHORITY_FIELDS: &[&str] = &[
    "schema",
    "schema_version",
    "status",
    "reason",
    "profile_key_digest",
    "module_hash",
    "target_triple",
    "target_cpu",
    "target_features",
    "opt_level",
    "opt_level_num",
    "cache_key_version",
    "profile_sha256",
    "fresh",
    "scheduled",
    "pass",
    "profile_use_reason",
    "target_compatible",
    "compiled_function_profile_reuse_sound",
    "authorizes_profile_reuse",
    "authorizes_useful_native",
];
/// Stable row keys emitted by [`HostJitPgoProfileAuthorityEvidence::manifest_rows`].
pub const HOST_JIT_PGO_PROFILE_AUTHORITY_MANIFEST_ROW_KEYS: &[&str] = &[
    "manifest.schema",
    "manifest.schema_version",
    "profile_authority.schema",
    "profile_authority.schema_version",
    "profile_authority.status",
    "profile_authority.reason",
    "profile_authority.profile_key_digest",
    "profile_authority.module_hash",
    "profile_authority.target_triple",
    "profile_authority.target_cpu",
    "profile_authority.target_features",
    "profile_authority.opt_level",
    "profile_authority.opt_level_num",
    "profile_authority.cache_key_version",
    "profile_authority.profile_sha256",
    "profile_authority.fresh",
    "profile_authority.scheduled",
    "profile_authority.pass",
    "profile_authority.profile_use_reason",
    "profile_authority.target_compatible",
    "profile_authority.compiled_function_profile_reuse_sound",
    "profile_authority.authorizes_profile_reuse",
    "profile_authority.authorizes_useful_native",
];
/// Stable entry-shape vocabulary accepted by the host-JIT PGO runner.
pub const HOST_JIT_PGO_ENTRY_SHAPE_CODES: &[&str] = &[
    "no_args_no_return",
    "no_args_i64_return",
    "i64_arg_no_return",
    "i64_arg_i64_return",
    "ty_parent_loop_u64_return",
];
/// Stable profile-use pass code emitted when profile-use is scheduled.
pub const HOST_JIT_PGO_PROFILE_USE_PASS_PROFILE_USE: &str = "profile-use";
/// Stable reason code emitted when the opt level schedules profile-use.
pub const HOST_JIT_PGO_PROFILE_USE_REASON_OPT_LEVEL_ENABLES: &str = "opt-level-enables-profile-use";
/// Stable reason code emitted when the opt level is too low for profile-use.
pub const HOST_JIT_PGO_PROFILE_USE_REASON_OPT_LEVEL_BELOW_O2: &str = "opt-level-below-o2";
/// Stable profile-use reason vocabulary.
pub const HOST_JIT_PGO_PROFILE_USE_REASON_CODES: &[&str] = &[
    HOST_JIT_PGO_PROFILE_USE_REASON_OPT_LEVEL_ENABLES,
    HOST_JIT_PGO_PROFILE_USE_REASON_OPT_LEVEL_BELOW_O2,
];
/// Stable profile authority status vocabulary.
pub const HOST_JIT_PGO_PROFILE_AUTHORITY_STATUS_CODES: &[&str] = &[
    "authoritative_for_compiled_function",
    "not_authoritative_for_compiled_function",
];
/// Stable profile authority reason vocabulary.
pub const HOST_JIT_PGO_PROFILE_AUTHORITY_REASON_CODES: &[&str] = &[
    "fresh_scheduled_profile_use",
    "report_schema_mismatch",
    "report_mode_mismatch",
    "profile_not_fresh",
    "profile_use_not_scheduled",
    "profile_use_pass_missing",
    "profile_use_pass_mismatch",
    "profile_use_reason_missing",
    "profile_use_reason_mismatch",
];
/// Stable host-JIT PGO runner error reason vocabulary.
pub const HOST_JIT_PGO_RUNNER_ERROR_REASON_CODES: &[&str] = &[
    "host_target_mismatch",
    "target_spec_mismatch",
    "host_target_triple_mismatch",
    "no_supported_entry",
    "entry_not_found",
    "unsupported_abi_shape",
    "inputs_for_no_arg_entry",
    "symbol_missing",
    "compile_error",
    "profdata_io",
    "profdata_serde",
    "profdata_bad_magic",
    "profdata_legacy_json_unsupported",
    "profdata_version_too_new",
    "profdata_version_too_old",
    "profdata_cache_key_version_mismatch",
    "profdata_stale_profile_key",
    "profdata_incompatible_merge",
    "profdata_counter_overflow",
    "profdata_malformed_hex",
    "profdata_truncated",
    "profdata_invalid_utf8",
    "profdata_invalid_format",
    "profdata_too_large",
    "profdata_checksum_mismatch",
];

/// Profile authority status for a compiled profile-use function.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HostJitPgoProfileAuthorityStatus {
    /// The fresh profile was consumed by the compiled function.
    AuthoritativeForCompiledFunction,
    /// The report does not prove profile reuse by the compiled function.
    NotAuthoritativeForCompiledFunction,
}

impl HostJitPgoProfileAuthorityStatus {
    /// Stable status code for downstream evidence rows.
    pub const fn code(self) -> &'static str {
        match self {
            Self::AuthoritativeForCompiledFunction => "authoritative_for_compiled_function",
            Self::NotAuthoritativeForCompiledFunction => "not_authoritative_for_compiled_function",
        }
    }

    /// Stable display name for diagnostics.
    pub const fn name(self) -> &'static str {
        match self {
            Self::AuthoritativeForCompiledFunction => "authoritative for compiled function",
            Self::NotAuthoritativeForCompiledFunction => "not authoritative for compiled function",
        }
    }
}

/// Reason code explaining profile authority status.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HostJitPgoProfileAuthorityReason {
    /// Fresh profile-use was scheduled and consumed by the compiled function.
    FreshScheduledProfileUse,
    /// The report schema is not the host-JIT PGO profile report schema.
    ReportSchemaMismatch,
    /// The report mode is not `profile-use`.
    ReportModeMismatch,
    /// The profile-use section did not prove freshness.
    ProfileNotFresh,
    /// Profile-use was available but not scheduled by the opt level.
    ProfileUseNotScheduled,
    /// Profile-use was scheduled but the pass field was absent.
    ProfileUsePassMissing,
    /// Profile-use was scheduled but the pass field was not `profile-use`.
    ProfileUsePassMismatch,
    /// Profile-use was scheduled but the reason field was absent.
    ProfileUseReasonMissing,
    /// Profile-use was scheduled but the reason field was not the enabling reason.
    ProfileUseReasonMismatch,
}

impl HostJitPgoProfileAuthorityReason {
    /// Stable reason code for downstream evidence rows.
    pub const fn code(self) -> &'static str {
        match self {
            Self::FreshScheduledProfileUse => "fresh_scheduled_profile_use",
            Self::ReportSchemaMismatch => "report_schema_mismatch",
            Self::ReportModeMismatch => "report_mode_mismatch",
            Self::ProfileNotFresh => "profile_not_fresh",
            Self::ProfileUseNotScheduled => "profile_use_not_scheduled",
            Self::ProfileUsePassMissing => "profile_use_pass_missing",
            Self::ProfileUsePassMismatch => "profile_use_pass_mismatch",
            Self::ProfileUseReasonMissing => "profile_use_reason_missing",
            Self::ProfileUseReasonMismatch => "profile_use_reason_mismatch",
        }
    }

    /// Stable display name for diagnostics.
    pub const fn name(self) -> &'static str {
        match self {
            Self::FreshScheduledProfileUse => "fresh scheduled profile-use",
            Self::ReportSchemaMismatch => "report schema mismatch",
            Self::ReportModeMismatch => "report mode mismatch",
            Self::ProfileNotFresh => "profile not fresh",
            Self::ProfileUseNotScheduled => "profile-use not scheduled",
            Self::ProfileUsePassMissing => "profile-use pass missing",
            Self::ProfileUsePassMismatch => "profile-use pass mismatch",
            Self::ProfileUseReasonMissing => "profile-use reason missing",
            Self::ProfileUseReasonMismatch => "profile-use reason mismatch",
        }
    }
}

/// Stable typed row kind for profile authority manifests.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HostJitPgoProfileAuthorityManifestRowKind {
    ManifestSchema,
    ManifestSchemaVersion,
    ProfileAuthoritySchema,
    ProfileAuthoritySchemaVersion,
    Status,
    Reason,
    ProfileKeyDigest,
    ModuleHash,
    TargetTriple,
    TargetCpu,
    TargetFeatures,
    OptLevel,
    OptLevelNum,
    CacheKeyVersion,
    ProfileSha256,
    Fresh,
    Scheduled,
    Pass,
    ProfileUseReason,
    TargetCompatible,
    CompiledFunctionProfileReuseSound,
    AuthorizesProfileReuse,
    AuthorizesUsefulNative,
}

impl HostJitPgoProfileAuthorityManifestRowKind {
    /// Return the stable manifest row key for this row kind.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ManifestSchema => "manifest.schema",
            Self::ManifestSchemaVersion => "manifest.schema_version",
            Self::ProfileAuthoritySchema => "profile_authority.schema",
            Self::ProfileAuthoritySchemaVersion => "profile_authority.schema_version",
            Self::Status => "profile_authority.status",
            Self::Reason => "profile_authority.reason",
            Self::ProfileKeyDigest => "profile_authority.profile_key_digest",
            Self::ModuleHash => "profile_authority.module_hash",
            Self::TargetTriple => "profile_authority.target_triple",
            Self::TargetCpu => "profile_authority.target_cpu",
            Self::TargetFeatures => "profile_authority.target_features",
            Self::OptLevel => "profile_authority.opt_level",
            Self::OptLevelNum => "profile_authority.opt_level_num",
            Self::CacheKeyVersion => "profile_authority.cache_key_version",
            Self::ProfileSha256 => "profile_authority.profile_sha256",
            Self::Fresh => "profile_authority.fresh",
            Self::Scheduled => "profile_authority.scheduled",
            Self::Pass => "profile_authority.pass",
            Self::ProfileUseReason => "profile_authority.profile_use_reason",
            Self::TargetCompatible => "profile_authority.target_compatible",
            Self::CompiledFunctionProfileReuseSound => {
                "profile_authority.compiled_function_profile_reuse_sound"
            }
            Self::AuthorizesProfileReuse => "profile_authority.authorizes_profile_reuse",
            Self::AuthorizesUsefulNative => "profile_authority.authorizes_useful_native",
        }
    }
}

/// Stable key/value row for JSON-free profile authority evidence manifests.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HostJitPgoProfileAuthorityManifestRow {
    /// Typed row kind for Rust/TY consumers.
    pub kind: HostJitPgoProfileAuthorityManifestRowKind,
    /// Raw manifest key.
    pub key: String,
    /// Raw manifest value.
    pub value: String,
}

impl HostJitPgoProfileAuthorityManifestRow {
    /// Create a typed profile authority manifest row.
    pub fn typed(
        kind: HostJitPgoProfileAuthorityManifestRowKind,
        value: impl Into<String>,
    ) -> Self {
        Self {
            kind,
            key: kind.as_str().to_owned(),
            value: value.into(),
        }
    }

    /// Stable row-kind code for structured downstream emitters.
    pub const fn kind_code(&self) -> &'static str {
        self.kind.as_str()
    }

    /// Escaped key for line-oriented `key=value` manifest output.
    pub fn escaped_key(&self) -> String {
        escape_profile_authority_manifest_component(&self.key)
    }

    /// Escaped value for line-oriented `key=value` manifest output.
    pub fn escaped_value(&self) -> String {
        escape_profile_authority_manifest_component(&self.value)
    }

    /// Stable one-line `key=value` representation.
    pub fn to_key_value_line(&self) -> String {
        format!("{}={}", self.escaped_key(), self.escaped_value())
    }
}

/// Descriptor for downstream host-JIT PGO/cache provenance consumers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HostJitPgoProvenanceDescriptor {
    /// Descriptor schema.
    pub schema: &'static str,
    /// Descriptor schema version.
    pub schema_version: u32,
    /// Report schema emitted by profile-generate/profile-use reports.
    pub profile_report_schema: &'static str,
    /// Profile key fields that define freshness.
    pub profile_key_fields: &'static [&'static str],
    /// Profile-generate capture fields.
    pub capture_fields: &'static [&'static str],
    /// Profile-use fields.
    pub profile_use_fields: &'static [&'static str],
    /// Fields used by [`ProfileUseReport::profile_reuse_sound_for_compiled_function`].
    pub profile_use_soundness_fields: &'static [&'static str],
    /// Profile authority evidence schema.
    pub profile_authority_evidence_schema: &'static str,
    /// Profile authority manifest schema.
    pub profile_authority_manifest_schema: &'static str,
    /// Profile authority manifest schema version.
    pub profile_authority_manifest_schema_version: u32,
    /// Profile authority evidence fields.
    pub profile_authority_fields: &'static [&'static str],
    /// Profile authority manifest row keys.
    pub profile_authority_manifest_row_keys: &'static [&'static str],
    /// Stable profile authority status vocabulary.
    pub profile_authority_status_codes: &'static [&'static str],
    /// Stable profile authority reason vocabulary.
    pub profile_authority_reason_codes: &'static [&'static str],
    /// Stable runner error reason vocabulary.
    pub runner_error_reason_codes: &'static [&'static str],
    /// Stable entry-shape vocabulary.
    pub entry_shape_codes: &'static [&'static str],
    /// Stable profile-use reason vocabulary.
    pub profile_use_reason_codes: &'static [&'static str],
    /// The opt pass code that means a profile was consumed by the compiled function.
    pub profile_use_pass_code: &'static str,
    /// Helper API downstream consumers can call instead of duplicating policy.
    pub soundness_helper: &'static str,
    /// Helper API that emits the full profile authority evidence row.
    pub profile_authority_helper: &'static str,
    /// Helper API that emits JSON-free profile authority manifest rows.
    pub profile_authority_manifest_helper: &'static str,
    /// Helper API that emits target compatibility failure reason codes.
    pub target_compatibility_helper: &'static str,
    /// Host-JIT PGO evidence is performance provenance and never native call authority.
    pub authorizes_useful_native: bool,
}

/// Stable host-JIT PGO/cache provenance descriptor.
pub const HOST_JIT_PGO_PROVENANCE_DESCRIPTOR: HostJitPgoProvenanceDescriptor =
    HostJitPgoProvenanceDescriptor {
        schema: TRUST_CG_HOST_JIT_PGO_PROVENANCE_DESCRIPTOR_SCHEMA,
        schema_version: TRUST_CG_HOST_JIT_PGO_PROVENANCE_DESCRIPTOR_SCHEMA_VERSION,
        profile_report_schema: TRUST_CG_PROFILE_REPORT_SCHEMA_V1,
        profile_key_fields: HOST_JIT_PGO_PROFILE_KEY_FIELDS,
        capture_fields: HOST_JIT_PGO_CAPTURE_FIELDS,
        profile_use_fields: HOST_JIT_PGO_PROFILE_USE_FIELDS,
        profile_use_soundness_fields: HOST_JIT_PGO_PROFILE_USE_SOUNDNESS_FIELDS,
        profile_authority_evidence_schema: TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_EVIDENCE_SCHEMA,
        profile_authority_manifest_schema: TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_MANIFEST_SCHEMA,
        profile_authority_manifest_schema_version:
            TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_MANIFEST_SCHEMA_VERSION,
        profile_authority_fields: HOST_JIT_PGO_PROFILE_AUTHORITY_FIELDS,
        profile_authority_manifest_row_keys: HOST_JIT_PGO_PROFILE_AUTHORITY_MANIFEST_ROW_KEYS,
        profile_authority_status_codes: HOST_JIT_PGO_PROFILE_AUTHORITY_STATUS_CODES,
        profile_authority_reason_codes: HOST_JIT_PGO_PROFILE_AUTHORITY_REASON_CODES,
        runner_error_reason_codes: HOST_JIT_PGO_RUNNER_ERROR_REASON_CODES,
        entry_shape_codes: HOST_JIT_PGO_ENTRY_SHAPE_CODES,
        profile_use_reason_codes: HOST_JIT_PGO_PROFILE_USE_REASON_CODES,
        profile_use_pass_code: HOST_JIT_PGO_PROFILE_USE_PASS_PROFILE_USE,
        soundness_helper: "HostJitPgoUseReport::profile_reuse_sound_for_compiled_function",
        profile_authority_helper: "HostJitPgoUseReport::profile_authority_evidence",
        profile_authority_manifest_helper: "HostJitPgoProfileAuthorityEvidence::manifest_rows",
        target_compatibility_helper: "HostJitPgoRunnerError::target_compatible",
        authorizes_useful_native: false,
    };

/// Return the stable host-JIT PGO/cache provenance descriptor.
pub const fn host_jit_pgo_provenance_descriptor() -> HostJitPgoProvenanceDescriptor {
    HOST_JIT_PGO_PROVENANCE_DESCRIPTOR
}

/// Errors returned by the host-JIT PGO runner.
#[derive(Debug, thiserror::Error)]
pub enum HostJitPgoRunnerError {
    /// In-process JIT execution must target the host architecture.
    #[error("host-JIT PGO requires target {target:?} to match host {host:?}")]
    HostTargetMismatch { target: Target, host: Target },
    /// The requested target spec architecture disagrees with the compiler
    /// target architecture.
    #[error(
        "host-JIT PGO target spec architecture {target:?} does not match compiler target {compiler_target:?}"
    )]
    TargetSpecMismatch {
        target: Target,
        compiler_target: Target,
    },
    /// An explicit OS/ABI target triple cannot be executed by this host.
    #[error(
        "host-JIT PGO requires target triple {target_triple} to match host triple {host_triple}"
    )]
    HostTargetTripleMismatch {
        target_triple: String,
        host_triple: String,
    },
    /// No supported profile-generate entry exists in the module.
    #[error(
        "no JIT PGO entry with supported signature; expected () -> (), () -> i64, (i64) -> (), (i64) -> i64, or TY parent loop (ptr, u64, ptr) -> u64"
    )]
    NoSupportedEntry,
    /// The requested entry symbol does not exist in the module.
    #[error("JIT PGO entry {entry:?} was not found in the module")]
    EntryNotFound { entry: String },
    /// The selected entry's trust_ir signature is not one of the supported ABI
    /// shapes, or it does not match the requested shape.
    #[error("JIT PGO entry {entry:?} has unsupported ABI shape: {signature}")]
    UnsupportedAbiShape { entry: String, signature: String },
    /// Caller supplied an input window to a no-argument entry point.
    #[error("JIT PGO inputs cannot be used with no-argument entry {entry:?}")]
    InputsForNoArgEntry { entry: String },
    /// The compiled symbol was missing from the executable buffer.
    #[error("JIT symbol {entry:?} was not emitted")]
    SymbolMissing { entry: String },
    /// trust_ir lowering/JIT compilation failed.
    #[error(transparent)]
    Compile(#[from] CompileError),
    /// `.profdata` encoding, writing, reading, or freshness validation failed.
    #[error(transparent)]
    ProfData(#[from] trust_cg_opt::pgo::ProfDataError),
}

impl HostJitPgoRunnerError {
    /// Stable reason code for fail-closed host-JIT PGO runner errors.
    pub fn reason_code(&self) -> &'static str {
        match self {
            Self::HostTargetMismatch { .. } => "host_target_mismatch",
            Self::TargetSpecMismatch { .. } => "target_spec_mismatch",
            Self::HostTargetTripleMismatch { .. } => "host_target_triple_mismatch",
            Self::NoSupportedEntry => "no_supported_entry",
            Self::EntryNotFound { .. } => "entry_not_found",
            Self::UnsupportedAbiShape { .. } => "unsupported_abi_shape",
            Self::InputsForNoArgEntry { .. } => "inputs_for_no_arg_entry",
            Self::SymbolMissing { .. } => "symbol_missing",
            Self::Compile(_) => "compile_error",
            Self::ProfData(err) => profdata_error_reason_code(err),
        }
    }

    /// Whether target compatibility validation had passed when this error was emitted.
    pub fn target_compatible(&self) -> bool {
        !matches!(
            self,
            Self::HostTargetMismatch { .. }
                | Self::TargetSpecMismatch { .. }
                | Self::HostTargetTripleMismatch { .. }
        )
    }
}

fn profdata_error_reason_code(err: &trust_cg_opt::pgo::ProfDataError) -> &'static str {
    match err {
        trust_cg_opt::pgo::ProfDataError::Io(_) => "profdata_io",
        trust_cg_opt::pgo::ProfDataError::Serde(_) => "profdata_serde",
        trust_cg_opt::pgo::ProfDataError::BadMagic { .. } => "profdata_bad_magic",
        trust_cg_opt::pgo::ProfDataError::LegacyJsonUnsupported => {
            "profdata_legacy_json_unsupported"
        }
        trust_cg_opt::pgo::ProfDataError::VersionTooNew { .. } => "profdata_version_too_new",
        trust_cg_opt::pgo::ProfDataError::VersionTooOld { .. } => "profdata_version_too_old",
        trust_cg_opt::pgo::ProfDataError::CacheKeyVersionMismatch { .. } => {
            "profdata_cache_key_version_mismatch"
        }
        trust_cg_opt::pgo::ProfDataError::StaleProfileKey { .. } => "profdata_stale_profile_key",
        trust_cg_opt::pgo::ProfDataError::IncompatibleMerge { .. } => "profdata_incompatible_merge",
        trust_cg_opt::pgo::ProfDataError::CounterOverflow { .. } => "profdata_counter_overflow",
        trust_cg_opt::pgo::ProfDataError::MalformedHex { .. } => "profdata_malformed_hex",
        trust_cg_opt::pgo::ProfDataError::Truncated { .. } => "profdata_truncated",
        trust_cg_opt::pgo::ProfDataError::InvalidUtf8 { .. } => "profdata_invalid_utf8",
        trust_cg_opt::pgo::ProfDataError::InvalidFormat(_) => "profdata_invalid_format",
        trust_cg_opt::pgo::ProfDataError::TooLarge(_) => "profdata_too_large",
        trust_cg_opt::pgo::ProfDataError::ChecksumMismatch { .. } => "profdata_checksum_mismatch",
    }
}

/// Supported host-JIT PGO entry shapes.
#[allow(clippy::enum_variant_names)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HostJitPgoEntryShape {
    /// `extern "C" fn()`.
    NoArgsNoReturn,
    /// `extern "C" fn() -> u64`.
    NoArgsI64Return,
    /// `extern "C" fn(u64)`.
    I64ArgNoReturn,
    /// `extern "C" fn(u64) -> u64`.
    I64ArgI64Return,
    /// TY parent-loop shape: `extern "C" fn(*const u64, u64, *mut u64) -> u64`.
    TyParentLoopU64Return,
}

impl HostJitPgoEntryShape {
    /// Report spelling used by `trust-cg.profile_report.v1`.
    pub fn as_report_str(self) -> &'static str {
        match self {
            Self::NoArgsNoReturn => "no_args_no_return",
            Self::NoArgsI64Return => "no_args_i64_return",
            Self::I64ArgNoReturn => "i64_arg_no_return",
            Self::I64ArgI64Return => "i64_arg_i64_return",
            Self::TyParentLoopU64Return => "ty_parent_loop_u64_return",
        }
    }

    fn default_inputs(self) -> Vec<u64> {
        match self {
            Self::NoArgsNoReturn | Self::NoArgsI64Return => Vec::new(),
            Self::I64ArgNoReturn | Self::I64ArgI64Return => DEFAULT_I64_PROFILE_INPUTS.to_vec(),
            Self::TyParentLoopU64Return => DEFAULT_TY_PARENT_PROFILE_INPUTS.to_vec(),
        }
    }

    fn call_count(self, inputs: &[u64]) -> usize {
        match self {
            Self::NoArgsNoReturn | Self::NoArgsI64Return | Self::TyParentLoopU64Return => 1,
            Self::I64ArgNoReturn | Self::I64ArgI64Return => inputs.len(),
        }
    }
}

/// Profile-generate entry selection.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HostJitPgoEntry {
    /// Select the first supported entry, preferring `main` or `_main` when
    /// present. `supplied_inputs` replaces the shape default for input-bearing
    /// shapes.
    Auto { supplied_inputs: Option<Vec<u64>> },
    /// Run a named `() -> ()` entry once.
    NoArgsNoReturn { entry: String },
    /// Run a named `() -> u64` entry once.
    NoArgsI64Return { entry: String },
    /// Run a named `(u64) -> ()` entry once for each input.
    I64ArgNoReturn { entry: String, inputs: Vec<u64> },
    /// Run a named `(u64) -> u64` entry once for each input.
    I64ArgI64Return { entry: String, inputs: Vec<u64> },
    /// Run a named TY parent-loop entry once over the supplied parent slice.
    TyParentLoopU64Return { entry: String, parents: Vec<u64> },
}

impl HostJitPgoEntry {
    fn entry_name(&self) -> Option<&str> {
        match self {
            Self::Auto { .. } => None,
            Self::NoArgsNoReturn { entry }
            | Self::NoArgsI64Return { entry }
            | Self::I64ArgNoReturn { entry, .. }
            | Self::I64ArgI64Return { entry, .. }
            | Self::TyParentLoopU64Return { entry, .. } => Some(entry),
        }
    }

    fn requested_shape(&self) -> Option<HostJitPgoEntryShape> {
        match self {
            Self::Auto { .. } => None,
            Self::NoArgsNoReturn { .. } => Some(HostJitPgoEntryShape::NoArgsNoReturn),
            Self::NoArgsI64Return { .. } => Some(HostJitPgoEntryShape::NoArgsI64Return),
            Self::I64ArgNoReturn { .. } => Some(HostJitPgoEntryShape::I64ArgNoReturn),
            Self::I64ArgI64Return { .. } => Some(HostJitPgoEntryShape::I64ArgI64Return),
            Self::TyParentLoopU64Return { .. } => Some(HostJitPgoEntryShape::TyParentLoopU64Return),
        }
    }

    fn requested_inputs(&self, shape: HostJitPgoEntryShape) -> Vec<u64> {
        match self {
            Self::Auto { supplied_inputs } => supplied_inputs
                .clone()
                .unwrap_or_else(|| shape.default_inputs()),
            Self::NoArgsNoReturn { .. } | Self::NoArgsI64Return { .. } => Vec::new(),
            Self::I64ArgNoReturn { inputs, .. } | Self::I64ArgI64Return { inputs, .. } => {
                inputs.clone()
            }
            Self::TyParentLoopU64Return { parents, .. } => parents.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ResolvedHostJitPgoTarget {
    name: String,
    shape: HostJitPgoEntryShape,
    inputs: Vec<u64>,
}

impl ResolvedHostJitPgoTarget {
    fn call_count(&self) -> usize {
        self.shape.call_count(&self.inputs)
    }
}

/// TY summary slots captured from the parent-loop ABI.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TyParentLoopSummary {
    pub state_count: u64,
    pub generated_count: u64,
    pub parent_digest: u64,
    pub fingerprint: u64,
    pub status: u64,
}

impl From<[u64; TY_PARENT_SUMMARY_SLOTS]> for TyParentLoopSummary {
    fn from(slots: [u64; TY_PARENT_SUMMARY_SLOTS]) -> Self {
        Self {
            state_count: slots[0],
            generated_count: slots[1],
            parent_digest: slots[2],
            fingerprint: slots[3],
            status: slots[4],
        }
    }
}

/// Runtime observation produced by invoking the selected host-JIT PGO entry.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HostJitPgoObservation {
    pub return_value: Option<u64>,
    pub ty_summary: Option<TyParentLoopSummary>,
}

impl HostJitPgoObservation {
    fn empty() -> Self {
        Self {
            return_value: None,
            ty_summary: None,
        }
    }
}

/// Counter totals emitted in `trust-cg.profile_report.v1`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProfileCounterSummary {
    pub function_count: usize,
    pub block_count: usize,
    pub edge_count: usize,
    pub total_call_count: u64,
    pub total_block_hits: u64,
    pub max_block_hits: u64,
}

impl ProfileCounterSummary {
    /// Summarize a decoded PGO profile.
    pub fn from_profile(profile: &trust_cg_opt::pgo::ProfData) -> Self {
        let block_count = profile.functions.iter().map(|f| f.blocks.len()).sum();
        let edge_count = profile.functions.iter().map(|f| f.edges.len()).sum();
        let total_call_count = profile.functions.iter().map(|f| f.call_count).sum();
        let total_block_hits = profile
            .functions
            .iter()
            .flat_map(|f| f.blocks.iter())
            .map(|b| b.hits)
            .sum();
        let max_block_hits = profile
            .functions
            .iter()
            .flat_map(|f| f.blocks.iter())
            .map(|b| b.hits)
            .max()
            .unwrap_or(0);

        Self {
            function_count: profile.functions.len(),
            block_count,
            edge_count,
            total_call_count,
            total_block_hits,
            max_block_hits,
        }
    }
}

/// Full PGO cache-key fields carried by binary v1 `.profdata`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProfileReportKey {
    pub profile_key_digest: String,
    pub module_hash: String,
    pub target_triple: String,
    pub target_cpu: String,
    pub target_features: Vec<String>,
    pub opt_level: String,
    pub opt_level_num: u8,
    pub cache_key_version: u32,
}

impl ProfileReportKey {
    /// Extract report key fields from a decoded PGO profile.
    pub fn from_profile(profile: &trust_cg_opt::pgo::ProfData) -> Self {
        Self {
            profile_key_digest: profile.profile_key_digest.clone(),
            module_hash: profile.module_hash.clone(),
            target_triple: profile.target_triple.clone(),
            target_cpu: profile.target_cpu.clone(),
            target_features: profile.target_features.clone(),
            opt_level: profile.opt_level.clone(),
            opt_level_num: profile.opt_level_num,
            cache_key_version: profile.cache_key_version,
        }
    }
}

/// Profile file identity in `trust-cg.profile_report.v1`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProfileFileReport {
    pub path: Option<String>,
    pub sha256: Option<String>,
}

/// Input window emitted for profile-generate captures.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HostJitPgoInputWindow {
    pub kind: String,
    pub start_index: usize,
    pub count: usize,
}

/// Capture section of a profile-generate report.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HostJitPgoCaptureReport {
    pub kind: String,
    pub hook_mode: String,
    pub entry: String,
    pub entry_shape: String,
    pub call_count: usize,
    pub inputs: Vec<u64>,
    pub window: HostJitPgoInputWindow,
    pub return_value: Option<u64>,
    pub ty_summary: Option<TyParentLoopSummary>,
}

/// Profile-use hotness summary emitted by the CLI report format.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProfileUseHotnessSummary {
    pub profiled_blocks: usize,
    pub hot_functions: usize,
    pub warm_functions: usize,
    pub cold_functions: usize,
    pub hot_blocks: usize,
    pub warm_blocks: usize,
    pub cold_blocks: usize,
    pub max_function_count: u64,
    pub total_function_count: u64,
}

/// Profile-use section of `trust-cg.profile_report.v1`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProfileUseReport {
    pub fresh: bool,
    pub consumer: String,
    pub scheduled: bool,
    pub pass: Option<String>,
    pub reason: Option<String>,
    pub summary: Option<ProfileUseHotnessSummary>,
}

impl ProfileUseReport {
    /// Whether the profile-use section proves that a fresh profile was consumed
    /// by the compiled function rather than merely being available.
    pub fn profile_reuse_sound_for_compiled_function(&self) -> bool {
        self.profile_authority_reason()
            == HostJitPgoProfileAuthorityReason::FreshScheduledProfileUse
    }

    /// Reason code explaining whether this profile-use section is authoritative.
    pub fn profile_authority_reason(&self) -> HostJitPgoProfileAuthorityReason {
        if !self.fresh {
            return HostJitPgoProfileAuthorityReason::ProfileNotFresh;
        }
        if !self.scheduled {
            return HostJitPgoProfileAuthorityReason::ProfileUseNotScheduled;
        }
        match self.pass.as_deref() {
            Some(HOST_JIT_PGO_PROFILE_USE_PASS_PROFILE_USE) => {}
            Some(_) => return HostJitPgoProfileAuthorityReason::ProfileUsePassMismatch,
            None => return HostJitPgoProfileAuthorityReason::ProfileUsePassMissing,
        }
        match self.reason.as_deref() {
            Some(HOST_JIT_PGO_PROFILE_USE_REASON_OPT_LEVEL_ENABLES) => {
                HostJitPgoProfileAuthorityReason::FreshScheduledProfileUse
            }
            Some(_) => HostJitPgoProfileAuthorityReason::ProfileUseReasonMismatch,
            None => HostJitPgoProfileAuthorityReason::ProfileUseReasonMissing,
        }
    }
}

/// Evidence row that explains whether a profile-use report authorizes profile
/// reuse for a compiled host-JIT function.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HostJitPgoProfileAuthorityEvidence {
    pub schema: String,
    pub schema_version: u32,
    pub status: String,
    pub reason: String,
    pub profile_key_digest: String,
    pub module_hash: String,
    pub target_triple: String,
    pub target_cpu: String,
    pub target_features: Vec<String>,
    pub opt_level: String,
    pub opt_level_num: u8,
    pub cache_key_version: u32,
    pub profile_sha256: Option<String>,
    pub fresh: bool,
    pub scheduled: bool,
    pub pass: Option<String>,
    pub profile_use_reason: Option<String>,
    pub target_compatible: bool,
    pub compiled_function_profile_reuse_sound: bool,
    pub authorizes_profile_reuse: bool,
    pub authorizes_useful_native: bool,
}

impl HostJitPgoProfileAuthorityEvidence {
    /// Emit stable JSON-free key/value rows for MCC sidecar consumers.
    pub fn manifest_rows(&self) -> Vec<HostJitPgoProfileAuthorityManifestRow> {
        let mut rows = Vec::new();
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::ManifestSchema,
            TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_MANIFEST_SCHEMA,
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::ManifestSchemaVersion,
            TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_MANIFEST_SCHEMA_VERSION.to_string(),
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::ProfileAuthoritySchema,
            &self.schema,
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::ProfileAuthoritySchemaVersion,
            self.schema_version.to_string(),
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::Status,
            &self.status,
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::Reason,
            &self.reason,
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::ProfileKeyDigest,
            &self.profile_key_digest,
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::ModuleHash,
            &self.module_hash,
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::TargetTriple,
            &self.target_triple,
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::TargetCpu,
            &self.target_cpu,
        );
        if self.target_features.is_empty() {
            push_profile_authority_manifest_row(
                &mut rows,
                HostJitPgoProfileAuthorityManifestRowKind::TargetFeatures,
                "",
            );
        } else {
            for feature in &self.target_features {
                push_profile_authority_manifest_row(
                    &mut rows,
                    HostJitPgoProfileAuthorityManifestRowKind::TargetFeatures,
                    feature,
                );
            }
        }
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::OptLevel,
            &self.opt_level,
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::OptLevelNum,
            self.opt_level_num.to_string(),
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::CacheKeyVersion,
            self.cache_key_version.to_string(),
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::ProfileSha256,
            self.profile_sha256.as_deref().unwrap_or(""),
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::Fresh,
            bool_code(self.fresh),
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::Scheduled,
            bool_code(self.scheduled),
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::Pass,
            self.pass.as_deref().unwrap_or(""),
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::ProfileUseReason,
            self.profile_use_reason.as_deref().unwrap_or(""),
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::TargetCompatible,
            bool_code(self.target_compatible),
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::CompiledFunctionProfileReuseSound,
            bool_code(self.compiled_function_profile_reuse_sound),
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::AuthorizesProfileReuse,
            bool_code(self.authorizes_profile_reuse),
        );
        push_profile_authority_manifest_row(
            &mut rows,
            HostJitPgoProfileAuthorityManifestRowKind::AuthorizesUsefulNative,
            bool_code(self.authorizes_useful_native),
        );
        rows
    }

    /// Emit stable escaped `key=value` manifest lines in [`Self::manifest_rows`] order.
    pub fn manifest_lines(&self) -> Vec<String> {
        self.manifest_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }
}

/// Typed profile-generate report equivalent to CLI
/// `trust-cg.profile_report.v1`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HostJitPgoGenerateReport {
    pub schema: String,
    pub mode: String,
    pub capture: HostJitPgoCaptureReport,
    pub profile_key: ProfileReportKey,
    pub profile: ProfileFileReport,
    pub counters: ProfileCounterSummary,
    pub profile_use: ProfileUseReport,
}

/// Typed profile-use report equivalent to CLI `trust-cg.profile_report.v1`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HostJitPgoUseReport {
    pub schema: String,
    pub mode: String,
    pub profile_key: ProfileReportKey,
    pub profile: ProfileFileReport,
    pub counters: ProfileCounterSummary,
    pub profile_use: ProfileUseReport,
}

impl HostJitPgoUseReport {
    /// Whether this report proves profile reuse was sound for the compiled
    /// profile-use artifact.
    pub fn profile_reuse_sound_for_compiled_function(&self) -> bool {
        self.profile_authority_reason()
            == HostJitPgoProfileAuthorityReason::FreshScheduledProfileUse
    }

    /// Status code for this report's profile authority.
    pub fn profile_authority_status(&self) -> HostJitPgoProfileAuthorityStatus {
        if self.profile_reuse_sound_for_compiled_function() {
            HostJitPgoProfileAuthorityStatus::AuthoritativeForCompiledFunction
        } else {
            HostJitPgoProfileAuthorityStatus::NotAuthoritativeForCompiledFunction
        }
    }

    /// Reason code explaining this report's profile authority status.
    pub fn profile_authority_reason(&self) -> HostJitPgoProfileAuthorityReason {
        if self.schema != TRUST_CG_PROFILE_REPORT_SCHEMA_V1 {
            return HostJitPgoProfileAuthorityReason::ReportSchemaMismatch;
        }
        if self.mode != "profile-use" {
            return HostJitPgoProfileAuthorityReason::ReportModeMismatch;
        }
        self.profile_use.profile_authority_reason()
    }

    /// Emit the complete profile authority evidence row for downstream tools.
    pub fn profile_authority_evidence(&self) -> HostJitPgoProfileAuthorityEvidence {
        let status = self.profile_authority_status();
        let reason = self.profile_authority_reason();
        let sound = status == HostJitPgoProfileAuthorityStatus::AuthoritativeForCompiledFunction;
        HostJitPgoProfileAuthorityEvidence {
            schema: TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_EVIDENCE_SCHEMA.to_string(),
            schema_version: TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_EVIDENCE_SCHEMA_VERSION,
            status: status.code().to_string(),
            reason: reason.code().to_string(),
            profile_key_digest: self.profile_key.profile_key_digest.clone(),
            module_hash: self.profile_key.module_hash.clone(),
            target_triple: self.profile_key.target_triple.clone(),
            target_cpu: self.profile_key.target_cpu.clone(),
            target_features: self.profile_key.target_features.clone(),
            opt_level: self.profile_key.opt_level.clone(),
            opt_level_num: self.profile_key.opt_level_num,
            cache_key_version: self.profile_key.cache_key_version,
            profile_sha256: self.profile.sha256.clone(),
            fresh: self.profile_use.fresh,
            scheduled: self.profile_use.scheduled,
            pass: self.profile_use.pass.clone(),
            profile_use_reason: self.profile_use.reason.clone(),
            target_compatible: true,
            compiled_function_profile_reuse_sound: sound,
            authorizes_profile_reuse: sound,
            authorizes_useful_native: false,
        }
    }
}

/// Result from a host-JIT profile-generate capture.
#[derive(Debug)]
pub struct HostJitPgoGenerateResult {
    /// Executable buffer used for the capture.
    pub jit: JitCompilationResult,
    /// Decoded profile written to `profile_path`.
    pub profile: trust_cg_opt::pgo::ProfData,
    /// Runtime observation from the selected entry call(s).
    pub observation: HostJitPgoObservation,
    /// Typed report equivalent to the CLI profile-generate report JSON.
    pub report: HostJitPgoGenerateReport,
}

/// Result from a host-JIT profile-use compile.
#[derive(Debug)]
pub struct HostJitPgoUseResult {
    /// Profile-use JIT compilation result.
    pub jit: JitCompilationResult,
    /// Typed report equivalent to the CLI profile-use report JSON.
    pub report: HostJitPgoUseReport,
}

impl HostJitPgoUseResult {
    /// Whether this result proves profile reuse was sound for the compiled
    /// profile-use artifact.
    pub fn profile_reuse_sound_for_compiled_function(&self) -> bool {
        self.report.profile_reuse_sound_for_compiled_function()
    }

    /// Emit the complete profile authority evidence row for downstream tools.
    pub fn profile_authority_evidence(&self) -> HostJitPgoProfileAuthorityEvidence {
        self.report.profile_authority_evidence()
    }
}

/// Numeric opt-level used in the full PGO cache key.
pub fn pgo_opt_level_num(level: OptLevel) -> u8 {
    match level {
        OptLevel::O0 => 0,
        OptLevel::O1 => 1,
        OptLevel::O2 => 2,
        OptLevel::O3 => 3,
    }
}

/// Human-readable opt-level spelling used in diagnostics.
pub fn pgo_opt_level_name(level: OptLevel) -> &'static str {
    match level {
        OptLevel::O0 => "O0",
        OptLevel::O1 => "O1",
        OptLevel::O2 => "O2",
        OptLevel::O3 => "O3",
    }
}

/// Target triple field used in the full PGO cache key.
pub fn pgo_target_triple(target_spec: TargetSpec) -> String {
    target_spec.with_default_os_abi().triple()
}

/// Target CPU field used in the full PGO cache key.
pub fn pgo_target_cpu(target: Target) -> &'static str {
    match target {
        Target::Aarch64 => "generic-aarch64",
        Target::X86_64 => "generic-x86_64",
        Target::Riscv64 => "generic-riscv64",
    }
}

/// Target features field used in the full PGO cache key.
pub fn pgo_target_features(target: Target) -> Vec<String> {
    match target {
        Target::Aarch64 => vec!["+neon".to_string()],
        Target::X86_64 => vec!["+sse2".to_string()],
        Target::Riscv64 => Vec::new(),
    }
}

/// Build the full PGO cache key used by CLI profile-generate/profile-use.
pub fn pgo_cache_key(
    trust_ir_bytes: &[u8],
    config: &CompilerConfig,
    target_spec: TargetSpec,
) -> trust_cg_opt::CacheKey {
    trust_cg_opt::CacheKey::new(
        trust_cg_opt::stable_hash(trust_ir_bytes),
        pgo_opt_level_num(config.opt_level),
        pgo_target_triple(target_spec),
        pgo_target_cpu(config.target).to_string(),
        pgo_target_features(config.target),
    )
}

/// Whether profile-use is scheduled by the optimization pipeline at `level`.
pub fn profile_use_enables_optimization(level: OptLevel) -> bool {
    matches!(level, OptLevel::O2 | OptLevel::O3)
}

/// Compile, run, write, and report a host-JIT block-count profile.
pub fn run_host_jit_pgo(
    module: &trust_ir::Module,
    trust_ir_bytes: &[u8],
    config: &CompilerConfig,
    target_spec: TargetSpec,
    profile_path: &Path,
    entry: HostJitPgoEntry,
) -> Result<HostJitPgoGenerateResult, HostJitPgoRunnerError> {
    run_host_jit_pgo_with_symbols(
        module,
        trust_ir_bytes,
        config,
        target_spec,
        profile_path,
        entry,
        &HashMap::new(),
    )
}

/// Compile, run, write, and report a host-JIT block-count profile with
/// explicit external symbol bindings.
#[allow(clippy::too_many_arguments)]
pub fn run_host_jit_pgo_with_symbols(
    module: &trust_ir::Module,
    trust_ir_bytes: &[u8],
    config: &CompilerConfig,
    target_spec: TargetSpec,
    profile_path: &Path,
    entry: HostJitPgoEntry,
    extern_symbols: &HashMap<String, *const u8>,
) -> Result<HostJitPgoGenerateResult, HostJitPgoRunnerError> {
    validate_host_target(config, target_spec)?;
    let target = resolve_target(module, &entry)?;

    let compiler = Compiler::new_for_target_spec(config.clone(), target_spec);
    let jit = compiler.compile_module_to_jit_with_profile_hooks(
        module,
        extern_symbols,
        ProfileHookMode::BlockCounts,
    )?;

    let observation = invoke_profile_target(&jit.buffer, &target)?;
    let profile_key = pgo_cache_key(trust_ir_bytes, config, target_spec);
    let profile = jit.buffer.block_profdata_with_key(&profile_key);
    trust_cg_opt::pgo::write_to_path(&profile, profile_path)?;

    let report = profile_generate_report(&profile, profile_path, &target, &observation);

    Ok(HostJitPgoGenerateResult {
        jit,
        profile,
        observation,
        report,
    })
}

/// Enforce profile freshness, compile with profile-use when the opt level
/// schedules the pass, and return the typed profile-use report.
pub fn compile_host_jit_with_profile_use(
    module: &trust_ir::Module,
    trust_ir_bytes: &[u8],
    config: &CompilerConfig,
    target_spec: TargetSpec,
    profile: trust_cg_opt::pgo::ProfData,
    profile_path: Option<&Path>,
) -> Result<HostJitPgoUseResult, HostJitPgoRunnerError> {
    compile_host_jit_with_profile_use_and_symbols(
        module,
        trust_ir_bytes,
        config,
        target_spec,
        profile,
        profile_path,
        &HashMap::new(),
    )
}

/// Profile-use compile helper with explicit external symbol bindings.
#[allow(clippy::too_many_arguments)]
pub fn compile_host_jit_with_profile_use_and_symbols(
    module: &trust_ir::Module,
    trust_ir_bytes: &[u8],
    config: &CompilerConfig,
    target_spec: TargetSpec,
    profile: trust_cg_opt::pgo::ProfData,
    profile_path: Option<&Path>,
    extern_symbols: &HashMap<String, *const u8>,
) -> Result<HostJitPgoUseResult, HostJitPgoRunnerError> {
    validate_host_target(config, target_spec)?;
    let profile_key = pgo_cache_key(trust_ir_bytes, config, target_spec);
    trust_cg_opt::pgo::enforce_fresh(&profile, &profile_key)?;

    let scheduled = profile_use_enables_optimization(config.opt_level);
    let report = profile_use_report(&profile, profile_path, scheduled);
    let compiler = Compiler::new_for_target_spec(config.clone(), target_spec);
    let compiler = if scheduled {
        compiler.with_profile_use(profile)
    } else {
        compiler
    };
    let jit = compiler.compile_module_to_jit(module, extern_symbols)?;

    Ok(HostJitPgoUseResult { jit, report })
}

fn validate_host_target(
    config: &CompilerConfig,
    target_spec: TargetSpec,
) -> Result<(), HostJitPgoRunnerError> {
    let host = Target::host();
    if config.target != host {
        return Err(HostJitPgoRunnerError::HostTargetMismatch {
            target: config.target,
            host,
        });
    }

    let effective_target_spec = target_spec.with_default_os_abi();
    if effective_target_spec.architecture != config.target {
        return Err(HostJitPgoRunnerError::TargetSpecMismatch {
            target: effective_target_spec.architecture,
            compiler_target: config.target,
        });
    }

    if target_spec.has_explicit_os_abi() && effective_target_spec != TargetSpec::host() {
        return Err(HostJitPgoRunnerError::HostTargetTripleMismatch {
            target_triple: effective_target_spec.triple(),
            host_triple: TargetSpec::host().triple(),
        });
    }

    Ok(())
}

fn profile_generate_report(
    profile: &trust_cg_opt::pgo::ProfData,
    profile_path: &Path,
    target: &ResolvedHostJitPgoTarget,
    observation: &HostJitPgoObservation,
) -> HostJitPgoGenerateReport {
    HostJitPgoGenerateReport {
        schema: TRUST_CG_PROFILE_REPORT_SCHEMA_V1.to_string(),
        mode: "profile-generate".to_string(),
        capture: HostJitPgoCaptureReport {
            kind: "host-jit-canary".to_string(),
            hook_mode: "block-counts".to_string(),
            entry: target.name.clone(),
            entry_shape: target.shape.as_report_str().to_string(),
            call_count: target.call_count(),
            inputs: target.inputs.clone(),
            window: HostJitPgoInputWindow {
                kind: "bounded-input-window".to_string(),
                start_index: 0,
                count: target.inputs.len(),
            },
            return_value: observation.return_value,
            ty_summary: observation.ty_summary,
        },
        profile_key: ProfileReportKey::from_profile(profile),
        profile: ProfileFileReport {
            path: Some(profile_path.display().to_string()),
            sha256: profile_sha256_from_path(profile_path),
        },
        counters: ProfileCounterSummary::from_profile(profile),
        profile_use: ProfileUseReport {
            fresh: true,
            consumer: "not-run-in-profile-generate".to_string(),
            scheduled: false,
            pass: None,
            reason: None,
            summary: None,
        },
    }
}

fn profile_use_report(
    profile: &trust_cg_opt::pgo::ProfData,
    profile_path: Option<&Path>,
    scheduled: bool,
) -> HostJitPgoUseReport {
    let hotness = trust_cg_opt::pgo::ProfileHotness::from_profile(profile);
    let stats = hotness.stats();
    HostJitPgoUseReport {
        schema: TRUST_CG_PROFILE_REPORT_SCHEMA_V1.to_string(),
        mode: "profile-use".to_string(),
        profile_key: ProfileReportKey::from_profile(profile),
        profile: ProfileFileReport {
            path: profile_path.map(|path| path.display().to_string()),
            sha256: profile_path.and_then(profile_sha256_from_path),
        },
        counters: ProfileCounterSummary::from_profile(profile),
        profile_use: ProfileUseReport {
            fresh: true,
            consumer: "optimization-pipeline".to_string(),
            scheduled,
            pass: scheduled.then(|| HOST_JIT_PGO_PROFILE_USE_PASS_PROFILE_USE.to_string()),
            reason: Some(
                if scheduled {
                    HOST_JIT_PGO_PROFILE_USE_REASON_OPT_LEVEL_ENABLES
                } else {
                    HOST_JIT_PGO_PROFILE_USE_REASON_OPT_LEVEL_BELOW_O2
                }
                .to_string(),
            ),
            summary: Some(ProfileUseHotnessSummary {
                profiled_blocks: stats.profiled_blocks,
                hot_functions: stats.hot_functions,
                warm_functions: stats.warm_functions,
                cold_functions: stats.cold_functions,
                hot_blocks: stats.hot_blocks,
                warm_blocks: stats.warm_blocks,
                cold_blocks: stats.cold_blocks,
                max_function_count: stats.max_function_count,
                total_function_count: stats.total_function_count,
            }),
        },
    }
}

fn push_profile_authority_manifest_row(
    rows: &mut Vec<HostJitPgoProfileAuthorityManifestRow>,
    kind: HostJitPgoProfileAuthorityManifestRowKind,
    value: impl Into<String>,
) {
    rows.push(HostJitPgoProfileAuthorityManifestRow::typed(kind, value));
}

fn escape_profile_authority_manifest_component(value: &str) -> String {
    let mut escaped = String::new();
    for ch in value.chars() {
        match ch {
            '\\' => escaped.push_str("\\\\"),
            '=' => escaped.push_str("\\="),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            _ if ch.is_control() => escaped.extend(ch.escape_default()),
            _ => escaped.push(ch),
        }
    }
    escaped
}

const fn bool_code(value: bool) -> &'static str {
    if value { "true" } else { "false" }
}

fn profile_sha256_from_path(path: &Path) -> Option<String> {
    let mut file = fs::File::open(path).ok()?;
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 64 * 1024];

    loop {
        let read = file.read(&mut buffer).ok()?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }

    Some(format!("sha256:{:x}", hasher.finalize()))
}

fn resolve_target(
    module: &trust_ir::Module,
    entry: &HostJitPgoEntry,
) -> Result<ResolvedHostJitPgoTarget, HostJitPgoRunnerError> {
    match entry {
        HostJitPgoEntry::Auto { supplied_inputs } => {
            let mut candidates = module.functions.iter().filter_map(|func| {
                let ft = module.func_types.get(func.ty.as_usize())?;
                let shape = profile_shape(ft)?;
                Some(ResolvedHostJitPgoTarget {
                    name: func.name.clone(),
                    shape,
                    inputs: supplied_inputs
                        .clone()
                        .unwrap_or_else(|| shape.default_inputs()),
                })
            });

            let first = candidates
                .next()
                .ok_or(HostJitPgoRunnerError::NoSupportedEntry)?;
            let target = if first.name == "main" || first.name == "_main" {
                first
            } else {
                candidates
                    .find(|target| target.name == "main" || target.name == "_main")
                    .unwrap_or(first)
            };
            validate_inputs_for_shape(&target.name, target.shape, &target.inputs)?;
            Ok(target)
        }
        _ => {
            let entry_name = entry
                .entry_name()
                .ok_or(HostJitPgoRunnerError::NoSupportedEntry)?;
            let func = module
                .functions
                .iter()
                .find(|func| func.name == entry_name)
                .ok_or_else(|| HostJitPgoRunnerError::EntryNotFound {
                    entry: entry_name.to_string(),
                })?;
            let ft = module.func_types.get(func.ty.as_usize()).ok_or_else(|| {
                HostJitPgoRunnerError::UnsupportedAbiShape {
                    entry: entry_name.to_string(),
                    signature: "<missing function type>".to_string(),
                }
            })?;
            let actual_shape =
                profile_shape(ft).ok_or_else(|| HostJitPgoRunnerError::UnsupportedAbiShape {
                    entry: entry_name.to_string(),
                    signature: describe_func_ty(ft),
                })?;
            let requested_shape = entry
                .requested_shape()
                .ok_or(HostJitPgoRunnerError::NoSupportedEntry)?;
            if actual_shape != requested_shape {
                return Err(HostJitPgoRunnerError::UnsupportedAbiShape {
                    entry: entry_name.to_string(),
                    signature: describe_func_ty(ft),
                });
            }
            let inputs = entry.requested_inputs(actual_shape);
            validate_inputs_for_shape(entry_name, actual_shape, &inputs)?;
            Ok(ResolvedHostJitPgoTarget {
                name: entry_name.to_string(),
                shape: actual_shape,
                inputs,
            })
        }
    }
}

fn validate_inputs_for_shape(
    entry: &str,
    shape: HostJitPgoEntryShape,
    inputs: &[u64],
) -> Result<(), HostJitPgoRunnerError> {
    if !inputs.is_empty()
        && matches!(
            shape,
            HostJitPgoEntryShape::NoArgsNoReturn | HostJitPgoEntryShape::NoArgsI64Return
        )
    {
        return Err(HostJitPgoRunnerError::InputsForNoArgEntry {
            entry: entry.to_string(),
        });
    }

    Ok(())
}

fn is_i64_abi_ty(ty: &trust_ir::Ty) -> bool {
    matches!(ty, trust_ir::Ty::I64 | trust_ir::Ty::U64)
}

fn is_no_return(returns: &[trust_ir::Ty]) -> bool {
    returns.is_empty() || matches!(returns, [trust_ir::Ty::Unit])
}

fn profile_shape(ft: &trust_ir::FuncTy) -> Option<HostJitPgoEntryShape> {
    match (ft.params.as_slice(), ft.returns.as_slice()) {
        ([], returns) if is_no_return(returns) => Some(HostJitPgoEntryShape::NoArgsNoReturn),
        ([], [ret]) if is_i64_abi_ty(ret) => Some(HostJitPgoEntryShape::NoArgsI64Return),
        ([trust_ir::Ty::Ptr, trust_ir::Ty::U64, trust_ir::Ty::Ptr], [trust_ir::Ty::U64]) => {
            Some(HostJitPgoEntryShape::TyParentLoopU64Return)
        }
        ([param], returns) if is_i64_abi_ty(param) && is_no_return(returns) => {
            Some(HostJitPgoEntryShape::I64ArgNoReturn)
        }
        ([param], [ret]) if is_i64_abi_ty(param) && is_i64_abi_ty(ret) => {
            Some(HostJitPgoEntryShape::I64ArgI64Return)
        }
        _ => None,
    }
}

fn describe_func_ty(ft: &trust_ir::FuncTy) -> String {
    let params = ft
        .params
        .iter()
        .map(|ty| format!("{ty:?}"))
        .collect::<Vec<_>>()
        .join(", ");
    let returns = ft
        .returns
        .iter()
        .map(|ty| format!("{ty:?}"))
        .collect::<Vec<_>>()
        .join(", ");
    format!("({params}) -> ({returns})")
}

fn invoke_profile_target(
    buffer: &ExecutableBuffer,
    target: &ResolvedHostJitPgoTarget,
) -> Result<HostJitPgoObservation, HostJitPgoRunnerError> {
    let mut observation = HostJitPgoObservation::empty();
    match target.shape {
        HostJitPgoEntryShape::NoArgsNoReturn => {
            let func = unsafe { buffer.get_fn_bound::<extern "C" fn()>(&target.name) }.ok_or_else(
                || HostJitPgoRunnerError::SymbolMissing {
                    entry: target.name.clone(),
                },
            )?;
            (*func.as_ref())();
        }
        HostJitPgoEntryShape::NoArgsI64Return => {
            let func = unsafe { buffer.get_fn_bound::<extern "C" fn() -> u64>(&target.name) }
                .ok_or_else(|| HostJitPgoRunnerError::SymbolMissing {
                    entry: target.name.clone(),
                })?;
            observation.return_value = Some((*func.as_ref())());
        }
        HostJitPgoEntryShape::I64ArgNoReturn => {
            let func = unsafe { buffer.get_fn_bound::<extern "C" fn(u64)>(&target.name) }
                .ok_or_else(|| HostJitPgoRunnerError::SymbolMissing {
                    entry: target.name.clone(),
                })?;
            for input in &target.inputs {
                (*func.as_ref())(*input);
            }
        }
        HostJitPgoEntryShape::I64ArgI64Return => {
            let func = unsafe { buffer.get_fn_bound::<extern "C" fn(u64) -> u64>(&target.name) }
                .ok_or_else(|| HostJitPgoRunnerError::SymbolMissing {
                    entry: target.name.clone(),
                })?;
            for input in &target.inputs {
                observation.return_value = Some((*func.as_ref())(*input));
            }
        }
        HostJitPgoEntryShape::TyParentLoopU64Return => {
            let func = unsafe {
                buffer.get_fn_bound::<extern "C" fn(*const u64, u64, *mut u64) -> u64>(&target.name)
            }
            .ok_or_else(|| HostJitPgoRunnerError::SymbolMissing {
                entry: target.name.clone(),
            })?;
            let mut summary = [u64::MAX; TY_PARENT_SUMMARY_SLOTS];
            observation.return_value = Some((*func.as_ref())(
                target.inputs.as_ptr(),
                target.inputs.len() as u64,
                summary.as_mut_ptr(),
            ));
            observation.ty_summary = Some(TyParentLoopSummary::from(summary));
        }
    }

    Ok(observation)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::jit_diagnostics::sha256_hex;

    #[test]
    fn profile_sha256_from_path_matches_in_memory_digest() {
        let bytes = b"trust-cg pgo profile hash fixture";
        let path = std::env::temp_dir().join(format!(
            "trust-cg-pgo-profile-hash-{}-{}.profdata",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::write(&path, bytes).unwrap();

        let digest = profile_sha256_from_path(&path);
        let _ = fs::remove_file(&path);

        assert_eq!(digest, Some(format!("sha256:{}", sha256_hex(bytes))));
    }
}
