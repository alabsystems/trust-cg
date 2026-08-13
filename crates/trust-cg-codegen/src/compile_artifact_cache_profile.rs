// trust-cg-codegen/compile_artifact_cache_profile.rs - Trust compile artifact cache keys
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Data-only Trust compile artifact cache profile.
//!
//! This module does not install or trust cached native code by itself. It
//! defines the canonical identity that a later filesystem cache backend must
//! bind before replaying compile artifacts into Trust self-build lanes.

use std::{
    env, fs,
    io::{self, Read},
    path::{Path, PathBuf},
    time::{Instant, SystemTime, UNIX_EPOCH},
};

use crate::jit_diagnostics::sha256_hex;
use crate::target::Target;

/// Stable schema tag for Trust compile artifact cache keys.
pub const TRUST_COMPILE_ARTIFACT_CACHE_SCHEMA: &str = "trust-cg.trust_compile_artifact_cache.v1";

/// Stable numeric schema version for Trust compile artifact cache keys.
pub const TRUST_COMPILE_ARTIFACT_CACHE_SCHEMA_VERSION: u32 = 1;

/// Stable profile-use identity for compiles that do not consume `.profdata`.
pub const COMPILE_ARTIFACT_PROFILE_USE_DISABLED_SHA256: &str =
    "sha256:32150b595f3c492559bde18e8bd7e11a59a7a61de3de4032f30db8a7c1571674";

/// Maximum manifest size accepted when replaying a local compile artifact cache entry.
pub const COMPILE_ARTIFACT_CACHE_MAX_MANIFEST_BYTES: u64 = 1024 * 1024;

/// Maximum cached object size accepted when replaying a local compile artifact cache entry.
pub const COMPILE_ARTIFACT_CACHE_MAX_ARTIFACT_BYTES: u64 = 512 * 1024 * 1024;

/// Stable schema tag for compile artifact cache performance telemetry.
pub const COMPILE_ARTIFACT_CACHE_TELEMETRY_SCHEMA: &str =
    "trust-cg.jit.compile_artifact_cache.telemetry.v1";

/// Stable numeric schema version for compile artifact cache performance telemetry.
pub const COMPILE_ARTIFACT_CACHE_TELEMETRY_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for JSON-free compile artifact cache telemetry descriptor manifests.
pub const COMPILE_ARTIFACT_CACHE_TELEMETRY_MANIFEST_SCHEMA: &str =
    "trust-cg.jit.compile_artifact_cache.telemetry.manifest.v1";

/// Stable numeric schema version for compile artifact cache telemetry descriptor manifests.
pub const COMPILE_ARTIFACT_CACHE_TELEMETRY_MANIFEST_SCHEMA_VERSION: u32 = 1;

/// Stable fields every compile artifact cache telemetry row carries.
pub const COMPILE_ARTIFACT_CACHE_TELEMETRY_REQUIRED_FIELDS: &[&str] = &[
    "boundary",
    "status",
    "key_sha256",
    "cache_path",
    "elapsed_micros",
];

/// Optional fields a cache telemetry row may carry.
pub const COMPILE_ARTIFACT_CACHE_TELEMETRY_OPTIONAL_FIELDS: &[&str] =
    &["artifact_sha256", "reason"];

/// Stable cache boundary vocabulary for telemetry rows.
pub const COMPILE_ARTIFACT_CACHE_TELEMETRY_BOUNDARY_CODES: &[&str] = &["pipeline", "service"];

/// Stable cache status vocabulary for telemetry rows.
pub const COMPILE_ARTIFACT_CACHE_TELEMETRY_STATUS_CODES: &[&str] =
    &["hit", "miss", "stored", "rejected_corrupt"];

/// Stable numeric metric fields for compile artifact cache telemetry.
pub const COMPILE_ARTIFACT_CACHE_TELEMETRY_METRIC_FIELDS: &[&str] = &["elapsed_micros"];

/// Stable reproducible identity fields for cache provenance joins.
pub const COMPILE_ARTIFACT_CACHE_TELEMETRY_IDENTITY_FIELDS: &[&str] =
    &["boundary", "status", "key_sha256"];

/// Optional reproducible identity fields that are present on hits/stores/rejections.
pub const COMPILE_ARTIFACT_CACHE_TELEMETRY_OPTIONAL_IDENTITY_FIELDS: &[&str] =
    &["artifact_sha256", "reason"];

/// Digest-bearing fields for cache provenance joins.
pub const COMPILE_ARTIFACT_CACHE_TELEMETRY_DIGEST_FIELDS: &[&str] =
    &["key_sha256", "artifact_sha256"];

/// Status codes that indicate reusable artifact bytes were available or produced.
pub const COMPILE_ARTIFACT_CACHE_TELEMETRY_ARTIFACT_REUSE_STATUS_CODES: &[&str] =
    &["hit", "stored"];

/// Status codes that indicate no reusable artifact bytes are available.
pub const COMPILE_ARTIFACT_CACHE_TELEMETRY_NON_REUSE_STATUS_CODES: &[&str] =
    &["miss", "rejected_corrupt"];

/// Descriptor for downstream JIT performance consumers of compile artifact cache telemetry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CompileArtifactCacheTelemetryDescriptor {
    /// Descriptor schema.
    pub schema: &'static str,
    /// Descriptor schema version.
    pub schema_version: u32,
    /// Required telemetry row fields.
    pub required_fields: &'static [&'static str],
    /// Optional telemetry row fields.
    pub optional_fields: &'static [&'static str],
    /// Stable boundary-code vocabulary.
    pub boundary_codes: &'static [&'static str],
    /// Stable status-code vocabulary.
    pub status_codes: &'static [&'static str],
    /// Numeric metric fields that downstream dashboards can aggregate.
    pub metric_fields: &'static [&'static str],
    /// Reproducible identity fields for cache provenance joins.
    pub identity_fields: &'static [&'static str],
    /// Optional identity fields whose presence depends on cache status.
    pub optional_identity_fields: &'static [&'static str],
    /// Digest-bearing fields for artifact reuse provenance.
    pub digest_fields: &'static [&'static str],
    /// Status codes that make artifact bytes reusable.
    pub artifact_reuse_status_codes: &'static [&'static str],
    /// Status codes that do not provide reusable artifact bytes.
    pub non_reuse_status_codes: &'static [&'static str],
    /// Cache telemetry is data-only and never authorizes useful-native promotion.
    pub authorizes_useful_native: bool,
}

/// Stable typed row kind for compile artifact cache telemetry manifests.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CompileArtifactCacheTelemetryManifestRowKind {
    ManifestSchema,
    ManifestSchemaVersion,
    TelemetrySchema,
    TelemetrySchemaVersion,
    RequiredField,
    OptionalField,
    IdentityField,
    OptionalIdentityField,
    BoundaryCode,
    StatusCode,
    ArtifactReuseStatusCode,
    NonReuseStatusCode,
    DigestField,
    MetricField,
    AuthorizesUsefulNative,
}

impl CompileArtifactCacheTelemetryManifestRowKind {
    /// Return the stable manifest row key for this row kind.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ManifestSchema => "manifest.schema",
            Self::ManifestSchemaVersion => "manifest.schema_version",
            Self::TelemetrySchema => "telemetry.schema",
            Self::TelemetrySchemaVersion => "telemetry.schema_version",
            Self::RequiredField => "telemetry.required_field",
            Self::OptionalField => "telemetry.optional_field",
            Self::IdentityField => "telemetry.identity_field",
            Self::OptionalIdentityField => "telemetry.optional_identity_field",
            Self::BoundaryCode => "telemetry.boundary_code",
            Self::StatusCode => "telemetry.status_code",
            Self::ArtifactReuseStatusCode => "telemetry.artifact_reuse_status_code",
            Self::NonReuseStatusCode => "telemetry.non_reuse_status_code",
            Self::DigestField => "telemetry.digest_field",
            Self::MetricField => "telemetry.metric_field",
            Self::AuthorizesUsefulNative => "telemetry.authorizes_useful_native",
        }
    }
}

/// Stable key/value row for JSON-free cache telemetry descriptor manifests.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompileArtifactCacheTelemetryManifestRow {
    /// Typed row kind for Rust/TY consumers. Custom rows leave this unset.
    pub kind: Option<CompileArtifactCacheTelemetryManifestRowKind>,
    /// Raw manifest key.
    pub key: String,
    /// Raw manifest value.
    pub value: String,
}

impl CompileArtifactCacheTelemetryManifestRow {
    /// Create a manifest row.
    pub fn new(key: impl Into<String>, value: impl Into<String>) -> Self {
        Self {
            kind: None,
            key: key.into(),
            value: value.into(),
        }
    }

    /// Create a typed descriptor manifest row.
    pub fn typed(
        kind: CompileArtifactCacheTelemetryManifestRowKind,
        value: impl Into<String>,
    ) -> Self {
        Self {
            kind: Some(kind),
            key: kind.as_str().to_owned(),
            value: value.into(),
        }
    }

    /// Stable row-kind code for structured downstream emitters.
    pub fn kind_code(&self) -> Option<&'static str> {
        self.kind
            .map(CompileArtifactCacheTelemetryManifestRowKind::as_str)
    }

    /// Escaped key for line-oriented `key=value` manifest output.
    pub fn escaped_key(&self) -> String {
        escape_manifest_component(&self.key)
    }

    /// Escaped value for line-oriented `key=value` manifest output.
    pub fn escaped_value(&self) -> String {
        escape_manifest_component(&self.value)
    }

    /// Stable one-line `key=value` representation.
    pub fn to_key_value_line(&self) -> String {
        format!("{}={}", self.escaped_key(), self.escaped_value())
    }
}

/// Stable typed row kind for compile artifact cache telemetry key/value fields.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CompileArtifactCacheTelemetryRowKind {
    Boundary,
    Status,
    KeySha256,
    CachePath,
    ElapsedMicros,
    ArtifactSha256,
    Reason,
}

impl CompileArtifactCacheTelemetryRowKind {
    /// Return the stable telemetry field key for this row kind.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Boundary => "boundary",
            Self::Status => "status",
            Self::KeySha256 => "key_sha256",
            Self::CachePath => "cache_path",
            Self::ElapsedMicros => "elapsed_micros",
            Self::ArtifactSha256 => "artifact_sha256",
            Self::Reason => "reason",
        }
    }

    fn from_descriptor_field(field: &str) -> Option<Self> {
        match field {
            "boundary" => Some(Self::Boundary),
            "status" => Some(Self::Status),
            "key_sha256" => Some(Self::KeySha256),
            "cache_path" => Some(Self::CachePath),
            "elapsed_micros" => Some(Self::ElapsedMicros),
            "artifact_sha256" => Some(Self::ArtifactSha256),
            "reason" => Some(Self::Reason),
            _ => None,
        }
    }
}

/// Stable JSON-free key/value field row for a compile artifact cache telemetry event.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompileArtifactCacheTelemetryKeyValueRow {
    /// Typed row kind for Rust/TY consumers.
    pub kind: CompileArtifactCacheTelemetryRowKind,
    /// Raw telemetry field key.
    pub key: String,
    /// Raw telemetry field value.
    pub value: String,
}

impl CompileArtifactCacheTelemetryKeyValueRow {
    /// Create a typed telemetry field row.
    pub fn typed(kind: CompileArtifactCacheTelemetryRowKind, value: impl Into<String>) -> Self {
        Self {
            kind,
            key: kind.as_str().to_owned(),
            value: value.into(),
        }
    }

    /// Stable row-kind code for structured downstream emitters.
    pub fn kind_code(&self) -> &'static str {
        self.kind.as_str()
    }

    /// Escaped key for line-oriented `key=value` telemetry output.
    pub fn escaped_key(&self) -> String {
        escape_manifest_component(&self.key)
    }

    /// Escaped value for line-oriented `key=value` telemetry output.
    pub fn escaped_value(&self) -> String {
        escape_manifest_component(&self.value)
    }

    /// Stable one-line `key=value` representation.
    pub fn to_key_value_line(&self) -> String {
        format!("{}={}", self.escaped_key(), self.escaped_value())
    }
}

impl CompileArtifactCacheTelemetryDescriptor {
    /// Emit stable JSON-free key/value rows for schema and MCC sidecar consumers.
    ///
    /// Rows deliberately duplicate the typed descriptor as flat strings so
    /// non-Rust consumers can validate cache telemetry without hardcoding Trust Codegen
    /// status, boundary, or metric vocabularies.
    pub fn manifest_rows(self) -> Vec<CompileArtifactCacheTelemetryManifestRow> {
        let mut rows = Vec::new();
        push_telemetry_manifest_row(
            &mut rows,
            CompileArtifactCacheTelemetryManifestRowKind::ManifestSchema,
            COMPILE_ARTIFACT_CACHE_TELEMETRY_MANIFEST_SCHEMA,
        );
        push_telemetry_manifest_row(
            &mut rows,
            CompileArtifactCacheTelemetryManifestRowKind::ManifestSchemaVersion,
            COMPILE_ARTIFACT_CACHE_TELEMETRY_MANIFEST_SCHEMA_VERSION.to_string(),
        );
        push_telemetry_manifest_row(
            &mut rows,
            CompileArtifactCacheTelemetryManifestRowKind::TelemetrySchema,
            self.schema,
        );
        push_telemetry_manifest_row(
            &mut rows,
            CompileArtifactCacheTelemetryManifestRowKind::TelemetrySchemaVersion,
            self.schema_version.to_string(),
        );
        for field in self.required_fields {
            push_telemetry_manifest_row(
                &mut rows,
                CompileArtifactCacheTelemetryManifestRowKind::RequiredField,
                *field,
            );
        }
        for field in self.optional_fields {
            push_telemetry_manifest_row(
                &mut rows,
                CompileArtifactCacheTelemetryManifestRowKind::OptionalField,
                *field,
            );
        }
        for field in self.identity_fields {
            push_telemetry_manifest_row(
                &mut rows,
                CompileArtifactCacheTelemetryManifestRowKind::IdentityField,
                *field,
            );
        }
        for field in self.optional_identity_fields {
            push_telemetry_manifest_row(
                &mut rows,
                CompileArtifactCacheTelemetryManifestRowKind::OptionalIdentityField,
                *field,
            );
        }
        for boundary in self.boundary_codes {
            push_telemetry_manifest_row(
                &mut rows,
                CompileArtifactCacheTelemetryManifestRowKind::BoundaryCode,
                *boundary,
            );
        }
        for status in self.status_codes {
            push_telemetry_manifest_row(
                &mut rows,
                CompileArtifactCacheTelemetryManifestRowKind::StatusCode,
                *status,
            );
        }
        for status in self.artifact_reuse_status_codes {
            push_telemetry_manifest_row(
                &mut rows,
                CompileArtifactCacheTelemetryManifestRowKind::ArtifactReuseStatusCode,
                *status,
            );
        }
        for status in self.non_reuse_status_codes {
            push_telemetry_manifest_row(
                &mut rows,
                CompileArtifactCacheTelemetryManifestRowKind::NonReuseStatusCode,
                *status,
            );
        }
        for field in self.digest_fields {
            push_telemetry_manifest_row(
                &mut rows,
                CompileArtifactCacheTelemetryManifestRowKind::DigestField,
                *field,
            );
        }
        for metric in self.metric_fields {
            push_telemetry_manifest_row(
                &mut rows,
                CompileArtifactCacheTelemetryManifestRowKind::MetricField,
                *metric,
            );
        }
        push_telemetry_manifest_row(
            &mut rows,
            CompileArtifactCacheTelemetryManifestRowKind::AuthorizesUsefulNative,
            bool_code(self.authorizes_useful_native),
        );
        rows
    }

    /// Emit stable escaped `key=value` manifest lines in [`Self::manifest_rows`] order.
    pub fn manifest_key_value_lines(self) -> Vec<String> {
        self.manifest_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }
}

/// Stable descriptor for compile artifact cache performance telemetry.
pub const COMPILE_ARTIFACT_CACHE_TELEMETRY_DESCRIPTOR: CompileArtifactCacheTelemetryDescriptor =
    CompileArtifactCacheTelemetryDescriptor {
        schema: COMPILE_ARTIFACT_CACHE_TELEMETRY_SCHEMA,
        schema_version: COMPILE_ARTIFACT_CACHE_TELEMETRY_SCHEMA_VERSION,
        required_fields: COMPILE_ARTIFACT_CACHE_TELEMETRY_REQUIRED_FIELDS,
        optional_fields: COMPILE_ARTIFACT_CACHE_TELEMETRY_OPTIONAL_FIELDS,
        boundary_codes: COMPILE_ARTIFACT_CACHE_TELEMETRY_BOUNDARY_CODES,
        status_codes: COMPILE_ARTIFACT_CACHE_TELEMETRY_STATUS_CODES,
        metric_fields: COMPILE_ARTIFACT_CACHE_TELEMETRY_METRIC_FIELDS,
        identity_fields: COMPILE_ARTIFACT_CACHE_TELEMETRY_IDENTITY_FIELDS,
        optional_identity_fields: COMPILE_ARTIFACT_CACHE_TELEMETRY_OPTIONAL_IDENTITY_FIELDS,
        digest_fields: COMPILE_ARTIFACT_CACHE_TELEMETRY_DIGEST_FIELDS,
        artifact_reuse_status_codes: COMPILE_ARTIFACT_CACHE_TELEMETRY_ARTIFACT_REUSE_STATUS_CODES,
        non_reuse_status_codes: COMPILE_ARTIFACT_CACHE_TELEMETRY_NON_REUSE_STATUS_CODES,
        authorizes_useful_native: false,
    };

/// Return the stable compile artifact cache performance telemetry descriptor.
pub const fn compile_artifact_cache_telemetry_descriptor() -> CompileArtifactCacheTelemetryDescriptor
{
    COMPILE_ARTIFACT_CACHE_TELEMETRY_DESCRIPTOR
}

/// Proof policy partition for compile artifact cache keys.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompileArtifactProofPolicy {
    /// No proof evidence is required; not valid for Trust self-verify.
    Unchecked,
    /// Fast smoke proof evidence only.
    Smoke,
    /// Full Trust Proof-TV verification evidence.
    ProofTvFull,
}

impl CompileArtifactProofPolicy {
    /// Return the stable lower-kebab-case policy id.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Unchecked => "unchecked",
            Self::Smoke => "smoke",
            Self::ProofTvFull => "proof-tv-full",
        }
    }

    /// Return true when cache admission requires proof-bundle identity.
    pub const fn requires_proof_bundle_digest(self) -> bool {
        !matches!(self, Self::Unchecked)
    }
}

/// Dependency and toolchain identity that partitions Trust compile artifacts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompileArtifactDependencyIdentity {
    /// Trust Codegen source revision or source-lock digest.
    pub trust_cg_identity: String,
    /// trust_ir source revision or source-lock digest.
    pub trust_ir_identity: String,
    /// ay source revision or source-lock digest.
    pub ay_identity: String,
    /// rustc version or stage2 compiler digest.
    pub rustc_identity: String,
    /// Cargo/tcargo tool identity.
    pub cargo_identity: String,
    /// Dependency mode, for example `upstream` or `trust`.
    pub dependency_mode: String,
}

impl CompileArtifactDependencyIdentity {
    /// Build the dependency identity segment used by artifact cache keys.
    pub fn new(
        trust_cg_identity: impl Into<String>,
        trust_ir_identity: impl Into<String>,
        ay_identity: impl Into<String>,
        rustc_identity: impl Into<String>,
        cargo_identity: impl Into<String>,
        dependency_mode: impl Into<String>,
    ) -> Self {
        Self {
            trust_cg_identity: trust_cg_identity.into(),
            trust_ir_identity: trust_ir_identity.into(),
            ay_identity: ay_identity.into(),
            rustc_identity: rustc_identity.into(),
            cargo_identity: cargo_identity.into(),
            dependency_mode: dependency_mode.into(),
        }
    }

    fn has_required_identity(&self) -> bool {
        !missing_required_text(&self.trust_cg_identity)
            && !missing_required_text(&self.trust_ir_identity)
            && !missing_required_text(&self.ay_identity)
            && !missing_required_text(&self.rustc_identity)
            && !missing_required_text(&self.cargo_identity)
            && matches!(self.dependency_mode.as_str(), "upstream" | "trust")
    }

    fn has_source_lock_identity(&self) -> bool {
        self.has_required_identity()
            && source_lock_identity(&self.trust_cg_identity)
            && source_lock_identity(&self.trust_ir_identity)
            && source_lock_identity(&self.ay_identity)
            && pinned_tool_identity(&self.rustc_identity)
            && pinned_tool_identity(&self.cargo_identity)
    }

    /// Build a production default identity, overridable by Trust self-build
    /// launchers through environment variables.
    pub fn from_env_or_defaults() -> Self {
        Self::new(
            env_or_default(
                "TRUST_CG_COMPILE_ARTIFACT_TRUST_CG_IDENTITY",
                format!("trust-cg:{}", env!("CARGO_PKG_VERSION")),
            ),
            env_or_default(
                "TRUST_CG_COMPILE_ARTIFACT_TRUST_IR_IDENTITY",
                "trust_ir:470508d6a67b07fddda99fcdd43750977a21e0a0",
            ),
            env_or_default(
                "TRUST_CG_COMPILE_ARTIFACT_AY_IDENTITY",
                "ay:d7738f34110cfe0dcd6dba313ed2195faad85569",
            ),
            env_or_default(
                "TRUST_CG_COMPILE_ARTIFACT_RUSTC_IDENTITY",
                format!("rustc:build-env:{}-{}", env::consts::ARCH, env::consts::OS),
            ),
            env_or_default(
                "TRUST_CG_COMPILE_ARTIFACT_CARGO_IDENTITY",
                format!("cargo:build-env:{}", env!("CARGO_PKG_VERSION")),
            ),
            env_or_default("TRUST_CG_COMPILE_ARTIFACT_DEPENDENCY_MODE", "trust"),
        )
    }

    /// Build a production identity for the requested proof policy. Proofed
    /// production cache partitions must be bound to source-lock/toolchain
    /// identities supplied by the launcher; package-version and build-env
    /// defaults are not replacement-grade replay identity.
    pub fn from_env_for_proof_policy(proof_policy: CompileArtifactProofPolicy) -> Self {
        if !proof_policy.requires_proof_bundle_digest() {
            return Self::from_env_or_defaults();
        }

        Self::new(
            env_or_missing("TRUST_CG_COMPILE_ARTIFACT_TRUST_CG_IDENTITY"),
            env_or_missing("TRUST_CG_COMPILE_ARTIFACT_TRUST_IR_IDENTITY"),
            env_or_missing("TRUST_CG_COMPILE_ARTIFACT_AY_IDENTITY"),
            env_or_missing("TRUST_CG_COMPILE_ARTIFACT_RUSTC_IDENTITY"),
            env_or_missing("TRUST_CG_COMPILE_ARTIFACT_CARGO_IDENTITY"),
            env_or_default("TRUST_CG_COMPILE_ARTIFACT_DEPENDENCY_MODE", "trust"),
        )
    }
}

/// Production cache configuration used by compiler, CLI, and service paths.
#[derive(Debug, Clone)]
pub struct CompileArtifactCacheConfig {
    /// Local filesystem cache root.
    pub root: PathBuf,
    /// Boundary to report for lookup/store telemetry.
    pub boundary: CompileArtifactCacheBoundary,
    /// Proof policy partition to use for object artifacts.
    pub proof_policy: CompileArtifactProofPolicy,
    /// Dependency/toolchain identity partition.
    pub dependency_identity: CompileArtifactDependencyIdentity,
}

impl CompileArtifactCacheConfig {
    /// Create an explicit compile artifact cache configuration.
    pub fn new(
        root: impl Into<PathBuf>,
        proof_policy: CompileArtifactProofPolicy,
        dependency_identity: CompileArtifactDependencyIdentity,
    ) -> Self {
        Self {
            root: root.into(),
            boundary: CompileArtifactCacheBoundary::Pipeline,
            proof_policy,
            dependency_identity,
        }
    }

    /// Create a cache configuration using production default dependency
    /// identity values, with Trust launcher env vars taking precedence.
    pub fn production_default(
        root: impl Into<PathBuf>,
        proof_policy: CompileArtifactProofPolicy,
    ) -> Self {
        Self::new(
            root,
            proof_policy,
            CompileArtifactDependencyIdentity::from_env_for_proof_policy(proof_policy),
        )
    }

    /// Return this config with a different proof-policy partition.
    pub fn with_proof_policy(&self, proof_policy: CompileArtifactProofPolicy) -> Self {
        Self {
            proof_policy,
            ..self.clone()
        }
    }

    /// Return this config with a different telemetry boundary.
    pub fn with_boundary(&self, boundary: CompileArtifactCacheBoundary) -> Self {
        Self {
            boundary,
            ..self.clone()
        }
    }

    /// Build a filesystem backend from this config.
    pub fn backend(&self) -> LocalFilesystemCompileArtifactCache {
        LocalFilesystemCompileArtifactCache::new(self.root.clone())
    }
}

/// Canonical Trust compile artifact cache key.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompileArtifactCacheKey {
    /// Source input digest.
    pub source_sha256: String,
    /// Canonical trust_ir input digest.
    pub trust_ir_sha256: String,
    /// Codegen option digest.
    pub codegen_options_sha256: String,
    /// Profile-use input digest, or the stable disabled identity.
    pub profile_use_sha256: String,
    /// Target architecture.
    pub target: Target,
    /// Rust target triple.
    pub target_triple: String,
    /// Target facts digest.
    pub target_facts_sha256: String,
    /// Proof policy partition.
    pub proof_policy: CompileArtifactProofPolicy,
    /// Dependency and toolchain identity.
    pub dependency_identity: CompileArtifactDependencyIdentity,
    /// Canonical key SHA-256.
    pub key_sha256: String,
}

impl CompileArtifactCacheKey {
    /// Build a canonical Trust compile artifact cache key.
    pub fn new(
        source_sha256: impl Into<String>,
        trust_ir_sha256: impl Into<String>,
        codegen_options_sha256: impl Into<String>,
        target: Target,
        target_triple: impl Into<String>,
        target_facts_sha256: impl Into<String>,
        proof_policy: CompileArtifactProofPolicy,
        dependency_identity: CompileArtifactDependencyIdentity,
    ) -> Self {
        let mut key = Self {
            source_sha256: source_sha256.into(),
            trust_ir_sha256: trust_ir_sha256.into(),
            codegen_options_sha256: codegen_options_sha256.into(),
            profile_use_sha256: COMPILE_ARTIFACT_PROFILE_USE_DISABLED_SHA256.to_owned(),
            target,
            target_triple: target_triple.into(),
            target_facts_sha256: target_facts_sha256.into(),
            proof_policy,
            dependency_identity,
            key_sha256: String::new(),
        };
        key.key_sha256 = key.canonical_key_sha256();
        key
    }

    /// Return this key with a profile-use identity and a recomputed key hash.
    pub fn with_profile_use_sha256(mut self, profile_use_sha256: impl Into<String>) -> Self {
        self.profile_use_sha256 = profile_use_sha256.into();
        self.key_sha256 = self.canonical_key_sha256();
        self
    }

    /// Return the stable hash of this cache key.
    pub fn canonical_key_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, TRUST_COMPILE_ARTIFACT_CACHE_SCHEMA);
        put_str(&mut out, &self.source_sha256);
        put_str(&mut out, &self.trust_ir_sha256);
        put_str(&mut out, &self.codegen_options_sha256);
        put_str(&mut out, &self.profile_use_sha256);
        put_str(&mut out, self.target.name());
        put_str(&mut out, &self.target_triple);
        put_str(&mut out, &self.target_facts_sha256);
        put_str(&mut out, self.proof_policy.as_str());
        put_str(&mut out, &self.dependency_identity.trust_cg_identity);
        put_str(&mut out, &self.dependency_identity.trust_ir_identity);
        put_str(&mut out, &self.dependency_identity.ay_identity);
        put_str(&mut out, &self.dependency_identity.rustc_identity);
        put_str(&mut out, &self.dependency_identity.cargo_identity);
        put_str(&mut out, &self.dependency_identity.dependency_mode);
        format!("sha256:{}", sha256_hex(&out))
    }

    /// Return true when all Trust replay identity fields are present and canonical.
    pub fn has_required_identity(&self) -> bool {
        !missing_required_text(&self.source_sha256)
            && !missing_required_text(&self.trust_ir_sha256)
            && !missing_required_text(&self.codegen_options_sha256)
            && !missing_required_text(&self.profile_use_sha256)
            && !missing_required_text(&self.target_triple)
            && !missing_required_text(&self.target_facts_sha256)
            && self.dependency_identity.has_required_identity()
            && (!self.proof_policy.requires_proof_bundle_digest()
                || self.dependency_identity.has_source_lock_identity())
            && self.key_sha256 == self.canonical_key_sha256()
    }
}

/// Compile artifact cache boundary that emitted telemetry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompileArtifactCacheBoundary {
    /// Compiler pipeline lookup/put boundary.
    Pipeline,
    /// Compile service lookup/put boundary.
    Service,
}

impl CompileArtifactCacheBoundary {
    /// Return the stable boundary id.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Pipeline => "pipeline",
            Self::Service => "service",
        }
    }
}

/// Compile artifact cache lookup/write status.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompileArtifactCacheStatus {
    /// Cache contained a valid artifact for the key.
    Hit,
    /// Cache had no entry for the key.
    Miss,
    /// Cache stored a new artifact for the key.
    Stored,
    /// Cache entry existed but failed replay validation.
    RejectedCorrupt,
}

impl CompileArtifactCacheStatus {
    /// Return the stable telemetry status id.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Hit => "hit",
            Self::Miss => "miss",
            Self::Stored => "stored",
            Self::RejectedCorrupt => "rejected_corrupt",
        }
    }
}

/// Hit/miss/replay telemetry emitted by the Trust compile artifact cache.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompileArtifactCacheTelemetry {
    /// Pipeline or service boundary that performed the operation.
    pub boundary: CompileArtifactCacheBoundary,
    /// Cache status.
    pub status: CompileArtifactCacheStatus,
    /// Canonical cache key hash.
    pub key_sha256: String,
    /// Optional artifact digest.
    pub artifact_sha256: Option<String>,
    /// Entry directory touched by the operation.
    pub cache_path: PathBuf,
    /// Stable machine-readable reason for miss/rejection.
    pub reason: Option<String>,
    /// Operation latency in microseconds.
    pub elapsed_micros: u128,
}

impl CompileArtifactCacheTelemetry {
    fn new(
        boundary: CompileArtifactCacheBoundary,
        status: CompileArtifactCacheStatus,
        key: &CompileArtifactCacheKey,
        cache_path: PathBuf,
        started: Instant,
    ) -> Self {
        Self {
            boundary,
            status,
            key_sha256: key.key_sha256.clone(),
            artifact_sha256: None,
            cache_path,
            reason: None,
            elapsed_micros: started.elapsed().as_micros(),
        }
    }

    fn with_artifact_sha256(mut self, artifact_sha256: String) -> Self {
        self.artifact_sha256 = Some(artifact_sha256);
        self
    }

    fn with_reason(mut self, reason: impl Into<String>) -> Self {
        self.reason = Some(reason.into());
        self
    }

    /// Emit producer-owned JSON-free key/value rows for this telemetry event.
    ///
    /// Row order follows [`compile_artifact_cache_telemetry_descriptor`]:
    /// required fields are emitted first, then present optional fields. This
    /// keeps downstream MCC/TY consumers tied to Trust Codegen's descriptor rather
    /// than recreating cache telemetry status or field policy locally.
    pub fn to_key_value_rows(&self) -> Vec<CompileArtifactCacheTelemetryKeyValueRow> {
        let descriptor = compile_artifact_cache_telemetry_descriptor();
        let mut rows =
            Vec::with_capacity(descriptor.required_fields.len() + descriptor.optional_fields.len());
        for field in descriptor.required_fields {
            if let Some(row) = self.required_key_value_row(field) {
                rows.push(row);
            }
        }
        for field in descriptor.optional_fields {
            if let Some(row) = self.optional_key_value_row(field) {
                rows.push(row);
            }
        }
        rows
    }

    /// Emit stable escaped `key=value` lines in [`Self::to_key_value_rows`] order.
    pub fn to_key_value_lines(&self) -> Vec<String> {
        self.to_key_value_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    fn required_key_value_row(
        &self,
        field: &str,
    ) -> Option<CompileArtifactCacheTelemetryKeyValueRow> {
        let row = self.key_value_row(field);
        debug_assert!(
            row.is_some(),
            "unsupported required compile artifact cache telemetry field: {field}"
        );
        row
    }

    fn optional_key_value_row(
        &self,
        field: &str,
    ) -> Option<CompileArtifactCacheTelemetryKeyValueRow> {
        if CompileArtifactCacheTelemetryRowKind::from_descriptor_field(field).is_none() {
            debug_assert!(
                false,
                "unsupported optional compile artifact cache telemetry field: {field}"
            );
            return None;
        }
        self.key_value_row(field)
    }

    fn key_value_row(&self, field: &str) -> Option<CompileArtifactCacheTelemetryKeyValueRow> {
        let kind = CompileArtifactCacheTelemetryRowKind::from_descriptor_field(field)?;
        match kind {
            CompileArtifactCacheTelemetryRowKind::Boundary => Some(
                CompileArtifactCacheTelemetryKeyValueRow::typed(kind, self.boundary.as_str()),
            ),
            CompileArtifactCacheTelemetryRowKind::Status => Some(
                CompileArtifactCacheTelemetryKeyValueRow::typed(kind, self.status.as_str()),
            ),
            CompileArtifactCacheTelemetryRowKind::KeySha256 => Some(
                CompileArtifactCacheTelemetryKeyValueRow::typed(kind, self.key_sha256.clone()),
            ),
            CompileArtifactCacheTelemetryRowKind::CachePath => {
                Some(CompileArtifactCacheTelemetryKeyValueRow::typed(
                    kind,
                    self.cache_path.display().to_string(),
                ))
            }
            CompileArtifactCacheTelemetryRowKind::ElapsedMicros => {
                Some(CompileArtifactCacheTelemetryKeyValueRow::typed(
                    kind,
                    self.elapsed_micros.to_string(),
                ))
            }
            CompileArtifactCacheTelemetryRowKind::ArtifactSha256 => self
                .artifact_sha256
                .as_ref()
                .map(|value| CompileArtifactCacheTelemetryKeyValueRow::typed(kind, value.clone())),
            CompileArtifactCacheTelemetryRowKind::Reason => self
                .reason
                .as_ref()
                .map(|value| CompileArtifactCacheTelemetryKeyValueRow::typed(kind, value.clone())),
        }
    }
}

/// Validated compile artifact loaded from the filesystem cache.
#[derive(Debug, Clone)]
pub struct CompileArtifactCacheEntry {
    /// Cache key used for the replay.
    pub key: CompileArtifactCacheKey,
    /// Cached artifact bytes.
    pub artifact_bytes: Vec<u8>,
    /// Artifact SHA-256 from the validated metadata.
    pub artifact_sha256: String,
    /// Parsed metadata used for audit/replay evidence.
    pub metadata: serde_json::Value,
}

/// Filesystem cache lookup result with telemetry.
#[derive(Debug, Clone)]
pub enum CompileArtifactCacheLookup {
    /// Valid artifact hit.
    Hit {
        /// Validated artifact entry.
        entry: CompileArtifactCacheEntry,
        /// Hit telemetry.
        telemetry: CompileArtifactCacheTelemetry,
    },
    /// No entry for this key.
    Miss {
        /// Miss telemetry.
        telemetry: CompileArtifactCacheTelemetry,
    },
    /// Entry existed but could not be safely replayed.
    Rejected {
        /// Rejection telemetry.
        telemetry: CompileArtifactCacheTelemetry,
    },
}

impl CompileArtifactCacheLookup {
    /// Borrow the telemetry attached to this lookup.
    pub fn telemetry(&self) -> &CompileArtifactCacheTelemetry {
        match self {
            Self::Hit { telemetry, .. }
            | Self::Miss { telemetry }
            | Self::Rejected { telemetry } => telemetry,
        }
    }
}

enum BoundedCacheReadError {
    Io(io::Error),
    TooLarge,
}

fn read_cache_file_bounded(path: &Path, max_bytes: u64) -> Result<Vec<u8>, BoundedCacheReadError> {
    let size = fs::metadata(path).map_err(BoundedCacheReadError::Io)?.len();
    if size > max_bytes {
        return Err(BoundedCacheReadError::TooLarge);
    }

    let file = fs::File::open(path).map_err(BoundedCacheReadError::Io)?;
    let mut bytes = Vec::with_capacity(size as usize);
    let mut bounded = file.take(max_bytes + 1);
    bounded
        .read_to_end(&mut bytes)
        .map_err(BoundedCacheReadError::Io)?;
    if bytes.len() as u64 > max_bytes {
        return Err(BoundedCacheReadError::TooLarge);
    }

    Ok(bytes)
}

/// Offline local filesystem backend for Trust compile artifacts.
#[derive(Debug, Clone)]
pub struct LocalFilesystemCompileArtifactCache {
    root: PathBuf,
}

impl LocalFilesystemCompileArtifactCache {
    /// Create a local filesystem cache rooted at `root`.
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }

    /// Return the cache root.
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Lookup an artifact at the pipeline boundary.
    pub fn lookup_for_pipeline(
        &self,
        key: &CompileArtifactCacheKey,
    ) -> io::Result<CompileArtifactCacheLookup> {
        self.lookup_with_boundary(key, CompileArtifactCacheBoundary::Pipeline, None)
    }

    /// Lookup an artifact at the pipeline boundary with current proof evidence.
    pub fn lookup_for_pipeline_with_expected_proof_bundle_sha256(
        &self,
        key: &CompileArtifactCacheKey,
        expected_proof_bundle_sha256: &str,
    ) -> io::Result<CompileArtifactCacheLookup> {
        self.lookup_with_boundary(
            key,
            CompileArtifactCacheBoundary::Pipeline,
            Some(expected_proof_bundle_sha256),
        )
    }

    /// Lookup an artifact at the compile-service boundary.
    pub fn lookup_for_service(
        &self,
        key: &CompileArtifactCacheKey,
    ) -> io::Result<CompileArtifactCacheLookup> {
        self.lookup_with_boundary(key, CompileArtifactCacheBoundary::Service, None)
    }

    /// Lookup an artifact at the compile-service boundary with current proof evidence.
    pub fn lookup_for_service_with_expected_proof_bundle_sha256(
        &self,
        key: &CompileArtifactCacheKey,
        expected_proof_bundle_sha256: &str,
    ) -> io::Result<CompileArtifactCacheLookup> {
        self.lookup_with_boundary(
            key,
            CompileArtifactCacheBoundary::Service,
            Some(expected_proof_bundle_sha256),
        )
    }

    /// Store an artifact from the pipeline boundary.
    pub fn store_from_pipeline(
        &self,
        key: &CompileArtifactCacheKey,
        artifact_bytes: &[u8],
        producer: &str,
    ) -> io::Result<CompileArtifactCacheTelemetry> {
        self.store_with_boundary(
            key,
            artifact_bytes,
            producer,
            None,
            CompileArtifactCacheBoundary::Pipeline,
        )
    }

    /// Store an artifact from the pipeline boundary with proof-bundle evidence.
    pub fn store_from_pipeline_with_proof_bundle_sha256(
        &self,
        key: &CompileArtifactCacheKey,
        artifact_bytes: &[u8],
        producer: &str,
        proof_bundle_sha256: &str,
    ) -> io::Result<CompileArtifactCacheTelemetry> {
        self.store_with_boundary(
            key,
            artifact_bytes,
            producer,
            Some(proof_bundle_sha256),
            CompileArtifactCacheBoundary::Pipeline,
        )
    }

    /// Store an artifact from the compile-service boundary.
    pub fn store_from_service(
        &self,
        key: &CompileArtifactCacheKey,
        artifact_bytes: &[u8],
        producer: &str,
    ) -> io::Result<CompileArtifactCacheTelemetry> {
        self.store_with_boundary(
            key,
            artifact_bytes,
            producer,
            None,
            CompileArtifactCacheBoundary::Service,
        )
    }

    /// Store an artifact from the compile-service boundary with proof evidence.
    pub fn store_from_service_with_proof_bundle_sha256(
        &self,
        key: &CompileArtifactCacheKey,
        artifact_bytes: &[u8],
        producer: &str,
        proof_bundle_sha256: &str,
    ) -> io::Result<CompileArtifactCacheTelemetry> {
        self.store_with_boundary(
            key,
            artifact_bytes,
            producer,
            Some(proof_bundle_sha256),
            CompileArtifactCacheBoundary::Service,
        )
    }

    fn lookup_with_boundary(
        &self,
        key: &CompileArtifactCacheKey,
        boundary: CompileArtifactCacheBoundary,
        expected_proof_bundle_sha256: Option<&str>,
    ) -> io::Result<CompileArtifactCacheLookup> {
        let started = Instant::now();
        let entry_dir = self.entry_dir(key);
        let manifest_path = entry_dir.join("manifest.json");
        let artifact_path = entry_dir.join("artifact.bin");
        let telemetry = CompileArtifactCacheTelemetry::new(
            boundary,
            CompileArtifactCacheStatus::Miss,
            key,
            entry_dir.clone(),
            started,
        );

        if !entry_dir.exists() {
            return Ok(CompileArtifactCacheLookup::Miss {
                telemetry: telemetry.with_reason("entry_not_found"),
            });
        }

        let manifest_bytes = match read_cache_file_bounded(
            &manifest_path,
            COMPILE_ARTIFACT_CACHE_MAX_MANIFEST_BYTES,
        ) {
            Ok(bytes) => bytes,
            Err(BoundedCacheReadError::Io(error)) if error.kind() == io::ErrorKind::NotFound => {
                return Ok(CompileArtifactCacheLookup::Rejected {
                    telemetry: telemetry
                        .with_status(CompileArtifactCacheStatus::RejectedCorrupt)
                        .with_reason("missing_manifest"),
                });
            }
            Err(BoundedCacheReadError::Io(error)) => return Err(error),
            Err(BoundedCacheReadError::TooLarge) => {
                return Ok(CompileArtifactCacheLookup::Rejected {
                    telemetry: telemetry
                        .with_status(CompileArtifactCacheStatus::RejectedCorrupt)
                        .with_reason("oversized_manifest"),
                });
            }
        };
        let metadata: serde_json::Value = match serde_json::from_slice(&manifest_bytes) {
            Ok(value) => value,
            Err(_) => {
                return Ok(CompileArtifactCacheLookup::Rejected {
                    telemetry: telemetry
                        .with_status(CompileArtifactCacheStatus::RejectedCorrupt)
                        .with_reason("invalid_manifest_json"),
                });
            }
        };

        if metadata
            .pointer("/artifact/size_bytes")
            .and_then(|value| value.as_u64())
            .is_some_and(|size| size > COMPILE_ARTIFACT_CACHE_MAX_ARTIFACT_BYTES)
        {
            return Ok(CompileArtifactCacheLookup::Rejected {
                telemetry: telemetry
                    .with_status(CompileArtifactCacheStatus::RejectedCorrupt)
                    .with_reason("oversized_artifact_manifest"),
            });
        }

        let artifact_bytes = match read_cache_file_bounded(
            &artifact_path,
            COMPILE_ARTIFACT_CACHE_MAX_ARTIFACT_BYTES,
        ) {
            Ok(bytes) => bytes,
            Err(BoundedCacheReadError::Io(error)) if error.kind() == io::ErrorKind::NotFound => {
                return Ok(CompileArtifactCacheLookup::Rejected {
                    telemetry: telemetry
                        .with_status(CompileArtifactCacheStatus::RejectedCorrupt)
                        .with_reason("missing_artifact"),
                });
            }
            Err(BoundedCacheReadError::Io(error)) => return Err(error),
            Err(BoundedCacheReadError::TooLarge) => {
                return Ok(CompileArtifactCacheLookup::Rejected {
                    telemetry: telemetry
                        .with_status(CompileArtifactCacheStatus::RejectedCorrupt)
                        .with_reason("oversized_artifact"),
                });
            }
        };

        let artifact_sha256 = format!("sha256:{}", sha256_hex(&artifact_bytes));
        if let Err(reason) = validate_cache_manifest(
            &metadata,
            key,
            &artifact_sha256,
            artifact_bytes.len(),
            expected_proof_bundle_sha256,
        ) {
            return Ok(CompileArtifactCacheLookup::Rejected {
                telemetry: telemetry
                    .with_status(CompileArtifactCacheStatus::RejectedCorrupt)
                    .with_artifact_sha256(artifact_sha256)
                    .with_reason(reason),
            });
        }

        let hit_telemetry = telemetry
            .with_status(CompileArtifactCacheStatus::Hit)
            .with_artifact_sha256(artifact_sha256.clone());
        Ok(CompileArtifactCacheLookup::Hit {
            entry: CompileArtifactCacheEntry {
                key: key.clone(),
                artifact_bytes,
                artifact_sha256,
                metadata,
            },
            telemetry: hit_telemetry,
        })
    }

    fn store_with_boundary(
        &self,
        key: &CompileArtifactCacheKey,
        artifact_bytes: &[u8],
        producer: &str,
        proof_bundle_sha256: Option<&str>,
        boundary: CompileArtifactCacheBoundary,
    ) -> io::Result<CompileArtifactCacheTelemetry> {
        if !key.has_required_identity() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "compile artifact cache key is missing required replay identity",
            ));
        }
        if artifact_bytes.len() as u64 > COMPILE_ARTIFACT_CACHE_MAX_ARTIFACT_BYTES {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "compile artifact cache object exceeds replay size limit",
            ));
        }
        if key.proof_policy.requires_proof_bundle_digest() {
            let digest = proof_bundle_sha256.filter(|digest| !missing_required_text(digest));
            if digest.is_none() {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "proof-policy compile artifact cache entries require proof_bundle_sha256",
                ));
            }
        }

        let started = Instant::now();
        let entry_dir = self.entry_dir(key);
        fs::create_dir_all(&entry_dir)?;

        let artifact_sha256 = format!("sha256:{}", sha256_hex(artifact_bytes));
        let manifest = cache_manifest_json(
            key,
            &artifact_sha256,
            artifact_bytes.len(),
            producer,
            proof_bundle_sha256,
        );
        let manifest_bytes = serde_json::to_vec_pretty(&manifest)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;

        fs::write(entry_dir.join("artifact.bin"), artifact_bytes)?;
        fs::write(entry_dir.join("manifest.json"), manifest_bytes)?;

        Ok(CompileArtifactCacheTelemetry::new(
            boundary,
            CompileArtifactCacheStatus::Stored,
            key,
            entry_dir,
            started,
        )
        .with_artifact_sha256(artifact_sha256))
    }

    fn entry_dir(&self, key: &CompileArtifactCacheKey) -> PathBuf {
        let key_id = key
            .key_sha256
            .strip_prefix("sha256:")
            .unwrap_or(&key.key_sha256);
        self.root.join(key_id)
    }
}

impl CompileArtifactCacheTelemetry {
    fn with_status(mut self, status: CompileArtifactCacheStatus) -> Self {
        self.status = status;
        self
    }
}

fn cache_manifest_json(
    key: &CompileArtifactCacheKey,
    artifact_sha256: &str,
    artifact_size_bytes: usize,
    producer: &str,
    proof_bundle_sha256: Option<&str>,
) -> serde_json::Value {
    let mut manifest = serde_json::json!({
        "schema": TRUST_COMPILE_ARTIFACT_CACHE_SCHEMA,
        "schema_version": TRUST_COMPILE_ARTIFACT_CACHE_SCHEMA_VERSION,
        "created_unix_millis": now_unix_millis(),
        "producer": producer,
        "key": {
            "key_sha256": &key.key_sha256,
            "source_sha256": &key.source_sha256,
            "trust_ir_sha256": &key.trust_ir_sha256,
            "codegen_options_sha256": &key.codegen_options_sha256,
            "profile_use_sha256": &key.profile_use_sha256,
            "target": key.target.name(),
            "target_triple": &key.target_triple,
            "target_facts_sha256": &key.target_facts_sha256,
            "proof_policy": key.proof_policy.as_str(),
            "dependency_identity": {
                "trust_cg_identity": &key.dependency_identity.trust_cg_identity,
                "trust_ir_identity": &key.dependency_identity.trust_ir_identity,
                "ay_identity": &key.dependency_identity.ay_identity,
                "rustc_identity": &key.dependency_identity.rustc_identity,
                "cargo_identity": &key.dependency_identity.cargo_identity,
                "dependency_mode": &key.dependency_identity.dependency_mode,
            },
        },
        "artifact": {
            "sha256": artifact_sha256,
            "size_bytes": artifact_size_bytes,
        },
        "replay_safety": {
            "requires_key_match": true,
            "requires_artifact_digest_match": true,
            "requires_proof_policy_match": true,
            "requires_proof_bundle_digest": key.proof_policy.requires_proof_bundle_digest(),
            "requires_profile_use_match": true,
            "requires_dependency_identity_match": true,
            "requires_target_facts_match": true,
        },
    });
    if let Some(digest) = proof_bundle_sha256 {
        manifest["proof"] = serde_json::json!({
            "bundle_sha256": digest,
        });
    }
    manifest
}

fn validate_cache_manifest(
    metadata: &serde_json::Value,
    key: &CompileArtifactCacheKey,
    artifact_sha256: &str,
    artifact_size_bytes: usize,
    expected_proof_bundle_sha256: Option<&str>,
) -> Result<(), String> {
    if !key.has_required_identity() {
        return Err("invalid_lookup_key_identity".to_owned());
    }
    expect_string(metadata, "/schema", TRUST_COMPILE_ARTIFACT_CACHE_SCHEMA)?;
    expect_u64(
        metadata,
        "/schema_version",
        u64::from(TRUST_COMPILE_ARTIFACT_CACHE_SCHEMA_VERSION),
    )?;
    expect_string(metadata, "/key/key_sha256", &key.key_sha256)?;
    expect_string(metadata, "/key/source_sha256", &key.source_sha256)?;
    expect_string(metadata, "/key/trust_ir_sha256", &key.trust_ir_sha256)?;
    expect_string(
        metadata,
        "/key/codegen_options_sha256",
        &key.codegen_options_sha256,
    )?;
    expect_string(metadata, "/key/profile_use_sha256", &key.profile_use_sha256)?;
    expect_string(metadata, "/key/target", key.target.name())?;
    expect_string(metadata, "/key/target_triple", &key.target_triple)?;
    expect_string(
        metadata,
        "/key/target_facts_sha256",
        &key.target_facts_sha256,
    )?;
    expect_string(metadata, "/key/proof_policy", key.proof_policy.as_str())?;
    expect_bool(
        metadata,
        "/replay_safety/requires_proof_bundle_digest",
        key.proof_policy.requires_proof_bundle_digest(),
    )?;
    if key.proof_policy.requires_proof_bundle_digest() {
        let proof_bundle_sha256 = metadata
            .pointer("/proof/bundle_sha256")
            .and_then(serde_json::Value::as_str)
            .ok_or_else(|| "missing_string/proof/bundle_sha256".to_owned())?;
        if missing_required_text(proof_bundle_sha256) {
            return Err("missing_string/proof/bundle_sha256".to_owned());
        }
        let expected = expected_proof_bundle_sha256
            .filter(|digest| !missing_required_text(digest))
            .ok_or_else(|| "missing_current/proof/bundle_sha256".to_owned())?;
        if proof_bundle_sha256 != expected {
            return Err("mismatched/proof/bundle_sha256".to_owned());
        }
    }
    expect_string(
        metadata,
        "/key/dependency_identity/trust_cg_identity",
        &key.dependency_identity.trust_cg_identity,
    )?;
    expect_string(
        metadata,
        "/key/dependency_identity/trust_ir_identity",
        &key.dependency_identity.trust_ir_identity,
    )?;
    expect_string(
        metadata,
        "/key/dependency_identity/ay_identity",
        &key.dependency_identity.ay_identity,
    )?;
    expect_string(
        metadata,
        "/key/dependency_identity/rustc_identity",
        &key.dependency_identity.rustc_identity,
    )?;
    expect_string(
        metadata,
        "/key/dependency_identity/cargo_identity",
        &key.dependency_identity.cargo_identity,
    )?;
    expect_string(
        metadata,
        "/key/dependency_identity/dependency_mode",
        &key.dependency_identity.dependency_mode,
    )?;
    expect_string(metadata, "/artifact/sha256", artifact_sha256)?;
    expect_u64(metadata, "/artifact/size_bytes", artifact_size_bytes as u64)?;
    expect_bool(metadata, "/replay_safety/requires_key_match", true)?;
    expect_bool(
        metadata,
        "/replay_safety/requires_artifact_digest_match",
        true,
    )?;
    expect_bool(metadata, "/replay_safety/requires_proof_policy_match", true)?;
    expect_bool(metadata, "/replay_safety/requires_profile_use_match", true)?;
    expect_bool(
        metadata,
        "/replay_safety/requires_dependency_identity_match",
        true,
    )?;
    expect_bool(metadata, "/replay_safety/requires_target_facts_match", true)?;
    Ok(())
}

fn expect_string(
    metadata: &serde_json::Value,
    pointer: &str,
    expected: &str,
) -> Result<(), String> {
    let actual = metadata
        .pointer(pointer)
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| format!("missing_string{}", pointer))?;
    if actual == expected {
        Ok(())
    } else {
        Err(format!("mismatched{}", pointer))
    }
}

fn expect_u64(metadata: &serde_json::Value, pointer: &str, expected: u64) -> Result<(), String> {
    let actual = metadata
        .pointer(pointer)
        .and_then(serde_json::Value::as_u64)
        .ok_or_else(|| format!("missing_u64{}", pointer))?;
    if actual == expected {
        Ok(())
    } else {
        Err(format!("mismatched{}", pointer))
    }
}

fn expect_bool(metadata: &serde_json::Value, pointer: &str, expected: bool) -> Result<(), String> {
    let actual = metadata
        .pointer(pointer)
        .and_then(serde_json::Value::as_bool)
        .ok_or_else(|| format!("missing_bool{}", pointer))?;
    if actual == expected {
        Ok(())
    } else {
        Err(format!("mismatched{}", pointer))
    }
}

fn now_unix_millis() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_millis() as u64)
        .unwrap_or(0)
}

fn put_str(out: &mut Vec<u8>, value: &str) {
    out.extend_from_slice(&(value.len() as u64).to_le_bytes());
    out.extend_from_slice(value.as_bytes());
}

fn push_telemetry_manifest_row(
    rows: &mut Vec<CompileArtifactCacheTelemetryManifestRow>,
    kind: CompileArtifactCacheTelemetryManifestRowKind,
    value: impl Into<String>,
) {
    rows.push(CompileArtifactCacheTelemetryManifestRow::typed(kind, value));
}

fn escape_manifest_component(value: &str) -> String {
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

fn missing_required_text(value: &str) -> bool {
    value.trim().is_empty() || value.starts_with("TODO") || value.starts_with("todo")
}

fn env_or_default(key: &str, default: impl Into<String>) -> String {
    env::var(key)
        .ok()
        .filter(|value| !missing_required_text(value))
        .unwrap_or_else(|| default.into())
}

fn env_or_missing(key: &str) -> String {
    env::var(key)
        .ok()
        .filter(|value| !missing_required_text(value))
        .unwrap_or_else(|| format!("TODO:required-source-lock:{key}"))
}

fn source_lock_identity(value: &str) -> bool {
    let value = value.trim();
    !missing_required_text(value)
        && (value.starts_with("source-lock-sha256:")
            || value.starts_with("source-lock:sha256:")
            || value.starts_with("sha256:"))
        && !value.contains("build-env")
}

fn pinned_tool_identity(value: &str) -> bool {
    let value = value.trim();
    !missing_required_text(value)
        && (value.starts_with("rustc:sha256:")
            || value.starts_with("rustc:stage2-sha256:")
            || value.starts_with("cargo:sha256:")
            || value.starts_with("tcargo:sha256:")
            || value.starts_with("toolchain-sha256:")
            || value.starts_with("sha256:"))
        && !value.contains("build-env")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn identity(mode: &str) -> CompileArtifactDependencyIdentity {
        CompileArtifactDependencyIdentity::new(
            "source-lock-sha256:trust-cg-def0d294",
            "source-lock-sha256:trust-ir-470508d6",
            "source-lock-sha256:ay-d7738f34",
            "rustc:stage2-sha256:abc",
            "tcargo:sha256:def",
            mode,
        )
    }

    fn key(policy: CompileArtifactProofPolicy) -> CompileArtifactCacheKey {
        CompileArtifactCacheKey::new(
            "sha256:source",
            "sha256:trust_ir",
            "sha256:codegen-options",
            Target::Aarch64,
            "aarch64-apple-darwin",
            "sha256:target-facts",
            policy,
            identity("trust"),
        )
    }

    #[test]
    fn proof_policy_partitions_compile_artifact_cache_key() {
        let smoke = key(CompileArtifactProofPolicy::Smoke);
        let full = key(CompileArtifactProofPolicy::ProofTvFull);

        assert_ne!(smoke.key_sha256, full.key_sha256);
        assert!(full.has_required_identity());
    }

    #[test]
    fn dependency_identity_partitions_compile_artifact_cache_key() {
        let trust = key(CompileArtifactProofPolicy::ProofTvFull);
        let mut upstream_identity = identity("upstream");
        upstream_identity.ay_identity = "source-lock-sha256:ay-other".to_owned();
        let upstream = CompileArtifactCacheKey::new(
            "sha256:source",
            "sha256:trust_ir",
            "sha256:codegen-options",
            Target::Aarch64,
            "aarch64-apple-darwin",
            "sha256:target-facts",
            CompileArtifactProofPolicy::ProofTvFull,
            upstream_identity,
        );

        assert_ne!(trust.key_sha256, upstream.key_sha256);
        assert!(upstream.has_required_identity());
    }

    #[test]
    fn profile_use_identity_partitions_compile_artifact_cache_key() {
        let no_profile = key(CompileArtifactProofPolicy::ProofTvFull);
        let with_profile = key(CompileArtifactProofPolicy::ProofTvFull).with_profile_use_sha256(
            "sha256:1111111111111111111111111111111111111111111111111111111111111111",
        );

        assert_ne!(no_profile.key_sha256, with_profile.key_sha256);
        assert_eq!(
            no_profile.profile_use_sha256,
            COMPILE_ARTIFACT_PROFILE_USE_DISABLED_SHA256
        );
        assert!(with_profile.has_required_identity());
    }

    #[test]
    fn compile_artifact_cache_telemetry_descriptor_exposes_jit_performance_vocab() {
        let descriptor = compile_artifact_cache_telemetry_descriptor();

        assert_eq!(descriptor.schema, COMPILE_ARTIFACT_CACHE_TELEMETRY_SCHEMA);
        assert_eq!(
            descriptor.schema_version,
            COMPILE_ARTIFACT_CACHE_TELEMETRY_SCHEMA_VERSION
        );
        assert_eq!(
            descriptor.required_fields,
            COMPILE_ARTIFACT_CACHE_TELEMETRY_REQUIRED_FIELDS
        );
        assert_eq!(
            descriptor.optional_fields,
            COMPILE_ARTIFACT_CACHE_TELEMETRY_OPTIONAL_FIELDS
        );
        assert_eq!(
            descriptor.boundary_codes,
            COMPILE_ARTIFACT_CACHE_TELEMETRY_BOUNDARY_CODES
        );
        assert_eq!(
            descriptor.status_codes,
            COMPILE_ARTIFACT_CACHE_TELEMETRY_STATUS_CODES
        );
        assert_eq!(
            descriptor.metric_fields,
            COMPILE_ARTIFACT_CACHE_TELEMETRY_METRIC_FIELDS
        );
        assert_eq!(
            descriptor.identity_fields,
            COMPILE_ARTIFACT_CACHE_TELEMETRY_IDENTITY_FIELDS
        );
        assert_eq!(
            descriptor.optional_identity_fields,
            COMPILE_ARTIFACT_CACHE_TELEMETRY_OPTIONAL_IDENTITY_FIELDS
        );
        assert_eq!(
            descriptor.digest_fields,
            COMPILE_ARTIFACT_CACHE_TELEMETRY_DIGEST_FIELDS
        );
        assert_eq!(
            descriptor.artifact_reuse_status_codes,
            COMPILE_ARTIFACT_CACHE_TELEMETRY_ARTIFACT_REUSE_STATUS_CODES
        );
        assert_eq!(
            descriptor.non_reuse_status_codes,
            COMPILE_ARTIFACT_CACHE_TELEMETRY_NON_REUSE_STATUS_CODES
        );
        assert_eq!(
            descriptor.boundary_codes,
            [
                CompileArtifactCacheBoundary::Pipeline.as_str(),
                CompileArtifactCacheBoundary::Service.as_str(),
            ]
        );
        assert_eq!(
            descriptor.status_codes,
            [
                CompileArtifactCacheStatus::Hit.as_str(),
                CompileArtifactCacheStatus::Miss.as_str(),
                CompileArtifactCacheStatus::Stored.as_str(),
                CompileArtifactCacheStatus::RejectedCorrupt.as_str(),
            ]
        );
        assert_eq!(descriptor.metric_fields, ["elapsed_micros"]);
        assert!(
            !descriptor.authorizes_useful_native,
            "cache performance telemetry must not authorize native promotion"
        );
    }

    #[test]
    fn compile_artifact_cache_telemetry_manifest_rows_are_mcc_friendly() {
        let descriptor = compile_artifact_cache_telemetry_descriptor();
        let rows = descriptor.manifest_rows();
        let values = |key: &str| {
            rows.iter()
                .filter(|row| row.key == key)
                .map(|row| row.value.as_str())
                .collect::<Vec<_>>()
        };

        assert_eq!(
            values("manifest.schema"),
            vec![COMPILE_ARTIFACT_CACHE_TELEMETRY_MANIFEST_SCHEMA]
        );
        assert_eq!(values("manifest.schema_version"), vec!["1"]);
        assert_eq!(
            values("telemetry.schema"),
            vec![COMPILE_ARTIFACT_CACHE_TELEMETRY_SCHEMA]
        );
        assert_eq!(values("telemetry.schema_version"), vec!["1"]);
        assert_eq!(
            values("telemetry.required_field"),
            COMPILE_ARTIFACT_CACHE_TELEMETRY_REQUIRED_FIELDS
        );
        assert_eq!(
            values("telemetry.optional_field"),
            COMPILE_ARTIFACT_CACHE_TELEMETRY_OPTIONAL_FIELDS
        );
        assert_eq!(
            values("telemetry.identity_field"),
            COMPILE_ARTIFACT_CACHE_TELEMETRY_IDENTITY_FIELDS
        );
        assert_eq!(
            values("telemetry.optional_identity_field"),
            COMPILE_ARTIFACT_CACHE_TELEMETRY_OPTIONAL_IDENTITY_FIELDS
        );
        assert_eq!(
            values("telemetry.boundary_code"),
            COMPILE_ARTIFACT_CACHE_TELEMETRY_BOUNDARY_CODES
        );
        assert_eq!(
            values("telemetry.status_code"),
            COMPILE_ARTIFACT_CACHE_TELEMETRY_STATUS_CODES
        );
        assert_eq!(
            values("telemetry.artifact_reuse_status_code"),
            COMPILE_ARTIFACT_CACHE_TELEMETRY_ARTIFACT_REUSE_STATUS_CODES
        );
        assert_eq!(
            values("telemetry.non_reuse_status_code"),
            COMPILE_ARTIFACT_CACHE_TELEMETRY_NON_REUSE_STATUS_CODES
        );
        assert_eq!(
            values("telemetry.digest_field"),
            COMPILE_ARTIFACT_CACHE_TELEMETRY_DIGEST_FIELDS
        );
        assert_eq!(
            values("telemetry.metric_field"),
            COMPILE_ARTIFACT_CACHE_TELEMETRY_METRIC_FIELDS
        );
        assert_eq!(values("telemetry.authorizes_useful_native"), vec!["false"]);
        assert!(
            rows.iter().all(|row| row.kind.is_some()),
            "descriptor rows should be typed for Rust/TY consumers"
        );
        assert_eq!(
            rows[0].kind_code(),
            Some(CompileArtifactCacheTelemetryManifestRowKind::ManifestSchema.as_str())
        );
    }

    #[test]
    fn compile_artifact_cache_telemetry_manifest_lines_have_stable_order_and_escaping() {
        let descriptor = compile_artifact_cache_telemetry_descriptor();
        let rows = descriptor.manifest_rows();
        let keys: Vec<_> = rows.iter().map(|row| row.key.as_str()).collect();
        let expected_keys = [
            "manifest.schema",
            "manifest.schema_version",
            "telemetry.schema",
            "telemetry.schema_version",
            "telemetry.required_field",
            "telemetry.required_field",
            "telemetry.required_field",
            "telemetry.required_field",
            "telemetry.required_field",
            "telemetry.optional_field",
            "telemetry.optional_field",
            "telemetry.identity_field",
            "telemetry.identity_field",
            "telemetry.identity_field",
            "telemetry.optional_identity_field",
            "telemetry.optional_identity_field",
            "telemetry.boundary_code",
            "telemetry.boundary_code",
            "telemetry.status_code",
            "telemetry.status_code",
            "telemetry.status_code",
            "telemetry.status_code",
            "telemetry.artifact_reuse_status_code",
            "telemetry.artifact_reuse_status_code",
            "telemetry.non_reuse_status_code",
            "telemetry.non_reuse_status_code",
            "telemetry.digest_field",
            "telemetry.digest_field",
            "telemetry.metric_field",
            "telemetry.authorizes_useful_native",
        ];
        assert_eq!(keys.as_slice(), &expected_keys);

        let lines = descriptor.manifest_key_value_lines();
        assert_eq!(lines.len(), rows.len());
        assert_eq!(
            lines.first().map(String::as_str),
            Some("manifest.schema=trust-cg.jit.compile_artifact_cache.telemetry.manifest.v1")
        );
        assert_eq!(
            lines.last().map(String::as_str),
            Some("telemetry.authorizes_useful_native=false")
        );
        for line in &lines {
            assert!(
                !line.contains('\n') && !line.contains('\r') && !line.contains('\t'),
                "manifest line contains raw control whitespace: {line:?}"
            );
        }

        let escaped =
            CompileArtifactCacheTelemetryManifestRow::new("cache=field", "line\n\ttab\\x=y\r\0");
        assert_eq!(escaped.escaped_key(), "cache\\=field");
        assert_eq!(escaped.escaped_value(), "line\\n\\ttab\\\\x\\=y\\r\\u{0}");
        assert_eq!(
            escaped.to_key_value_line(),
            "cache\\=field=line\\n\\ttab\\\\x\\=y\\r\\u{0}"
        );
    }

    #[test]
    fn compile_artifact_cache_telemetry_rows_follow_descriptor_order() {
        let telemetry = CompileArtifactCacheTelemetry {
            boundary: CompileArtifactCacheBoundary::Service,
            status: CompileArtifactCacheStatus::Hit,
            key_sha256: "sha256:key".to_owned(),
            artifact_sha256: Some("sha256:artifact".to_owned()),
            cache_path: PathBuf::from("/tmp/trust-cg-cache/key"),
            reason: Some("validated_manifest".to_owned()),
            elapsed_micros: 42,
        };

        let rows = telemetry.to_key_value_rows();
        let keys: Vec<_> = rows.iter().map(|row| row.key.as_str()).collect();
        let descriptor = compile_artifact_cache_telemetry_descriptor();
        let expected_keys = descriptor
            .required_fields
            .iter()
            .chain(descriptor.optional_fields.iter())
            .copied()
            .collect::<Vec<_>>();
        assert_eq!(keys, expected_keys);

        let values = |key: &str| {
            rows.iter()
                .filter(|row| row.key == key)
                .map(|row| row.value.as_str())
                .collect::<Vec<_>>()
        };
        assert_eq!(values("boundary"), vec!["service"]);
        assert_eq!(values("status"), vec!["hit"]);
        assert_eq!(values("key_sha256"), vec!["sha256:key"]);
        assert_eq!(values("cache_path"), vec!["/tmp/trust-cg-cache/key"]);
        assert_eq!(values("elapsed_micros"), vec!["42"]);
        assert_eq!(values("artifact_sha256"), vec!["sha256:artifact"]);
        assert_eq!(values("reason"), vec!["validated_manifest"]);
        assert_eq!(
            rows[0].kind_code(),
            CompileArtifactCacheTelemetryRowKind::Boundary.as_str()
        );
    }

    #[test]
    fn compile_artifact_cache_telemetry_rows_skip_absent_optional_fields() {
        let telemetry = CompileArtifactCacheTelemetry {
            boundary: CompileArtifactCacheBoundary::Pipeline,
            status: CompileArtifactCacheStatus::Miss,
            key_sha256: "sha256:key".to_owned(),
            artifact_sha256: None,
            cache_path: PathBuf::from("/tmp/trust-cg-cache/key"),
            reason: None,
            elapsed_micros: 7,
        };

        let rows = telemetry.to_key_value_rows();
        let keys = rows.iter().map(|row| row.key.as_str()).collect::<Vec<_>>();
        assert_eq!(
            keys,
            COMPILE_ARTIFACT_CACHE_TELEMETRY_REQUIRED_FIELDS.to_vec()
        );
        assert!(
            rows.iter()
                .all(|row| !row.key.is_empty() && !row.value.is_empty()),
            "required telemetry rows must all carry values"
        );
    }

    #[test]
    fn compile_artifact_cache_telemetry_lines_escape_fields() {
        let telemetry = CompileArtifactCacheTelemetry {
            boundary: CompileArtifactCacheBoundary::Service,
            status: CompileArtifactCacheStatus::RejectedCorrupt,
            key_sha256: "sha256:key=needs\\escape".to_owned(),
            artifact_sha256: Some("sha256:artifact=bad".to_owned()),
            cache_path: PathBuf::from("/tmp/trust-cg-cache/key\nentry"),
            reason: Some("manifest\tbad\r".to_owned()),
            elapsed_micros: 9,
        };

        let lines = telemetry.to_key_value_lines();
        assert_eq!(lines.len(), telemetry.to_key_value_rows().len());
        assert!(lines.contains(&"key_sha256=sha256:key\\=needs\\\\escape".to_owned()));
        assert!(lines.contains(&"cache_path=/tmp/trust-cg-cache/key\\nentry".to_owned()));
        assert!(lines.contains(&"reason=manifest\\tbad\\r".to_owned()));
        assert!(lines.contains(&"artifact_sha256=sha256:artifact\\=bad".to_owned()));
        for line in &lines {
            assert!(
                !line.contains('\n') && !line.contains('\r') && !line.contains('\t'),
                "telemetry line contains raw control whitespace: {line:?}"
            );
        }
    }

    #[test]
    fn missing_identity_rejects_compile_artifact_cache_key() {
        let mut cache_key = key(CompileArtifactProofPolicy::ProofTvFull);
        cache_key.dependency_identity.rustc_identity.clear();
        cache_key.key_sha256 = cache_key.canonical_key_sha256();

        assert!(!cache_key.has_required_identity());
    }

    #[test]
    fn proof_policy_cache_key_rejects_package_version_dependency_identity() {
        let legacy_identity = CompileArtifactDependencyIdentity::new(
            "trust-cg:0.1.0",
            "trust_ir:470508d6a67b07fddda99fcdd43750977a21e0a0",
            "ay:d7738f34110cfe0dcd6dba313ed2195faad85569",
            "rustc:build-env:aarch64-macos",
            "cargo:build-env:0.1.0",
            "trust",
        );
        let legacy_key = CompileArtifactCacheKey::new(
            "sha256:source",
            "sha256:trust_ir",
            "sha256:codegen-options",
            Target::Aarch64,
            "aarch64-apple-darwin",
            "sha256:target-facts",
            CompileArtifactProofPolicy::ProofTvFull,
            legacy_identity,
        );

        assert!(
            !legacy_key.has_required_identity(),
            "proofed production cache keys must not admit package-version/build-env dependency identity"
        );
    }

    #[test]
    fn unchecked_cache_key_keeps_legacy_dependency_identity_for_non_proof_cache() {
        let legacy_identity = CompileArtifactDependencyIdentity::new(
            "trust-cg:0.1.0",
            "trust_ir:470508d6a67b07fddda99fcdd43750977a21e0a0",
            "ay:d7738f34110cfe0dcd6dba313ed2195faad85569",
            "rustc:build-env:aarch64-macos",
            "cargo:build-env:0.1.0",
            "trust",
        );
        let legacy_key = CompileArtifactCacheKey::new(
            "sha256:source",
            "sha256:trust_ir",
            "sha256:codegen-options",
            Target::Aarch64,
            "aarch64-apple-darwin",
            "sha256:target-facts",
            CompileArtifactProofPolicy::Unchecked,
            legacy_identity,
        );

        assert!(legacy_key.has_required_identity());
    }

    #[test]
    fn canonical_key_hash_is_stable_for_equal_inputs() {
        let first = key(CompileArtifactProofPolicy::ProofTvFull);
        let second = key(CompileArtifactProofPolicy::ProofTvFull);

        assert_eq!(first.key_sha256, second.key_sha256);
        assert!(first.key_sha256.starts_with("sha256:"));
    }

    fn temp_cache_root(name: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "trust-cg-compile-artifact-cache-{}-{}-{}",
            name,
            std::process::id(),
            now_unix_millis()
        ))
    }

    const TEST_PROOF_BUNDLE_SHA256: &str =
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

    #[test]
    fn filesystem_cache_reports_miss_store_and_hit_with_audit_metadata() {
        let root = temp_cache_root("hit");
        let cache = LocalFilesystemCompileArtifactCache::new(&root);
        let cache_key = key(CompileArtifactProofPolicy::ProofTvFull);

        let miss = cache.lookup_for_pipeline(&cache_key).unwrap();
        assert_eq!(miss.telemetry().status, CompileArtifactCacheStatus::Miss);
        assert_eq!(
            miss.telemetry().boundary,
            CompileArtifactCacheBoundary::Pipeline
        );

        let stored = cache
            .store_from_pipeline_with_proof_bundle_sha256(
                &cache_key,
                b"mach-o-object",
                "trust-cg-test",
                TEST_PROOF_BUNDLE_SHA256,
            )
            .unwrap();
        assert_eq!(stored.status, CompileArtifactCacheStatus::Stored);
        assert_eq!(stored.boundary, CompileArtifactCacheBoundary::Pipeline);

        let hit = cache
            .lookup_for_pipeline_with_expected_proof_bundle_sha256(
                &cache_key,
                TEST_PROOF_BUNDLE_SHA256,
            )
            .unwrap();
        match hit {
            CompileArtifactCacheLookup::Hit { entry, telemetry } => {
                assert_eq!(telemetry.status, CompileArtifactCacheStatus::Hit);
                assert_eq!(entry.artifact_bytes, b"mach-o-object");
                assert_eq!(
                    entry
                        .metadata
                        .pointer("/key/proof_policy")
                        .and_then(|v| v.as_str()),
                    Some("proof-tv-full")
                );
                assert_eq!(
                    entry
                        .metadata
                        .pointer("/key/profile_use_sha256")
                        .and_then(|v| v.as_str()),
                    Some(COMPILE_ARTIFACT_PROFILE_USE_DISABLED_SHA256)
                );
                assert_eq!(
                    entry
                        .metadata
                        .pointer("/proof/bundle_sha256")
                        .and_then(|v| v.as_str()),
                    Some(TEST_PROOF_BUNDLE_SHA256)
                );
                assert_eq!(
                    entry
                        .metadata
                        .pointer("/replay_safety/requires_proof_bundle_digest")
                        .and_then(|v| v.as_bool()),
                    Some(true)
                );
                assert_eq!(
                    entry
                        .metadata
                        .pointer("/replay_safety/requires_artifact_digest_match")
                        .and_then(|v| v.as_bool()),
                    Some(true)
                );
            }
            other => panic!("expected cache hit, got {:?}", other),
        }

        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn filesystem_cache_exposes_service_boundary_hit_telemetry() {
        let root = temp_cache_root("service");
        let cache = LocalFilesystemCompileArtifactCache::new(&root);
        let cache_key = key(CompileArtifactProofPolicy::ProofTvFull);

        cache
            .store_from_service_with_proof_bundle_sha256(
                &cache_key,
                b"service-object",
                "compile-service",
                TEST_PROOF_BUNDLE_SHA256,
            )
            .unwrap();
        let hit = cache
            .lookup_for_service_with_expected_proof_bundle_sha256(
                &cache_key,
                TEST_PROOF_BUNDLE_SHA256,
            )
            .unwrap();

        assert_eq!(hit.telemetry().status, CompileArtifactCacheStatus::Hit);
        assert_eq!(
            hit.telemetry().boundary,
            CompileArtifactCacheBoundary::Service
        );

        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn proof_policy_change_invalidates_filesystem_cache_key() {
        let root = temp_cache_root("policy");
        let cache = LocalFilesystemCompileArtifactCache::new(&root);
        let full = key(CompileArtifactProofPolicy::ProofTvFull);
        let smoke = key(CompileArtifactProofPolicy::Smoke);

        cache
            .store_from_pipeline_with_proof_bundle_sha256(
                &full,
                b"verified-object",
                "trust-cg-test",
                TEST_PROOF_BUNDLE_SHA256,
            )
            .unwrap();
        let lookup = cache.lookup_for_pipeline(&smoke).unwrap();

        assert_eq!(lookup.telemetry().status, CompileArtifactCacheStatus::Miss);
        assert_eq!(
            lookup.telemetry().reason.as_deref(),
            Some("entry_not_found")
        );

        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn proof_policy_cache_store_requires_proof_bundle_digest() {
        let root = temp_cache_root("proof-bundle-store");
        let cache = LocalFilesystemCompileArtifactCache::new(&root);

        for policy in [
            CompileArtifactProofPolicy::Smoke,
            CompileArtifactProofPolicy::ProofTvFull,
        ] {
            let cache_key = key(policy);
            let error = cache
                .store_from_pipeline(&cache_key, b"object", "trust-cg-test")
                .unwrap_err();
            assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
            assert!(
                error.to_string().contains("proof_bundle_sha256"),
                "unexpected proof bundle store error: {error}"
            );
        }

        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn proof_policy_cache_hit_rejects_manifest_missing_proof_bundle_digest() {
        let root = temp_cache_root("proof-bundle-hit");
        let cache = LocalFilesystemCompileArtifactCache::new(&root);

        for policy in [
            CompileArtifactProofPolicy::Smoke,
            CompileArtifactProofPolicy::ProofTvFull,
        ] {
            let cache_key = key(policy);
            cache
                .store_from_pipeline_with_proof_bundle_sha256(
                    &cache_key,
                    b"object",
                    "trust-cg-test",
                    TEST_PROOF_BUNDLE_SHA256,
                )
                .unwrap();
            let manifest_path = cache.entry_dir(&cache_key).join("manifest.json");
            let mut manifest: serde_json::Value =
                serde_json::from_slice(&std::fs::read(&manifest_path).unwrap()).unwrap();
            manifest.as_object_mut().unwrap().remove("proof");
            std::fs::write(
                &manifest_path,
                serde_json::to_vec_pretty(&manifest).unwrap(),
            )
            .unwrap();

            let lookup = cache
                .lookup_for_pipeline_with_expected_proof_bundle_sha256(
                    &cache_key,
                    TEST_PROOF_BUNDLE_SHA256,
                )
                .unwrap();
            assert_eq!(
                lookup.telemetry().status,
                CompileArtifactCacheStatus::RejectedCorrupt
            );
            assert_eq!(
                lookup.telemetry().reason.as_deref(),
                Some("missing_string/proof/bundle_sha256")
            );
        }

        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn proof_policy_cache_hit_requires_current_proof_bundle_digest() {
        let root = temp_cache_root("proof-bundle-current");
        let cache = LocalFilesystemCompileArtifactCache::new(&root);
        let cache_key = key(CompileArtifactProofPolicy::ProofTvFull);

        cache
            .store_from_pipeline_with_proof_bundle_sha256(
                &cache_key,
                b"object",
                "trust-cg-test",
                TEST_PROOF_BUNDLE_SHA256,
            )
            .unwrap();

        let lookup = cache.lookup_for_pipeline(&cache_key).unwrap();
        assert_eq!(
            lookup.telemetry().status,
            CompileArtifactCacheStatus::RejectedCorrupt
        );
        assert_eq!(
            lookup.telemetry().reason.as_deref(),
            Some("missing_current/proof/bundle_sha256")
        );

        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn proof_policy_cache_hit_rejects_stale_proof_bundle_digest() {
        let root = temp_cache_root("proof-bundle-stale");
        let cache = LocalFilesystemCompileArtifactCache::new(&root);
        let cache_key = key(CompileArtifactProofPolicy::ProofTvFull);
        const CURRENT_PROOF_BUNDLE_SHA256: &str =
            "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

        cache
            .store_from_pipeline_with_proof_bundle_sha256(
                &cache_key,
                b"object",
                "trust-cg-test",
                TEST_PROOF_BUNDLE_SHA256,
            )
            .unwrap();

        let lookup = cache
            .lookup_for_pipeline_with_expected_proof_bundle_sha256(
                &cache_key,
                CURRENT_PROOF_BUNDLE_SHA256,
            )
            .unwrap();
        assert_eq!(
            lookup.telemetry().status,
            CompileArtifactCacheStatus::RejectedCorrupt
        );
        assert_eq!(
            lookup.telemetry().reason.as_deref(),
            Some("mismatched/proof/bundle_sha256")
        );

        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn unchecked_cache_entries_do_not_require_proof_bundle_digest() {
        let root = temp_cache_root("proof-bundle-unchecked");
        let cache = LocalFilesystemCompileArtifactCache::new(&root);
        let cache_key = key(CompileArtifactProofPolicy::Unchecked);

        cache
            .store_from_pipeline(&cache_key, b"unchecked-object", "trust-cg-test")
            .unwrap();

        match cache.lookup_for_pipeline(&cache_key).unwrap() {
            CompileArtifactCacheLookup::Hit { entry, telemetry } => {
                assert_eq!(telemetry.status, CompileArtifactCacheStatus::Hit);
                assert_eq!(entry.artifact_bytes, b"unchecked-object");
                assert!(entry.metadata.pointer("/proof/bundle_sha256").is_none());
                assert_eq!(
                    entry
                        .metadata
                        .pointer("/replay_safety/requires_proof_bundle_digest")
                        .and_then(|v| v.as_bool()),
                    Some(false)
                );
            }
            other => panic!("expected unchecked cache hit, got {other:?}"),
        }

        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn corrupt_artifact_entry_is_rejected_not_replayed() {
        let root = temp_cache_root("corrupt");
        let cache = LocalFilesystemCompileArtifactCache::new(&root);
        let cache_key = key(CompileArtifactProofPolicy::ProofTvFull);

        cache
            .store_from_pipeline_with_proof_bundle_sha256(
                &cache_key,
                b"good-object",
                "trust-cg-test",
                TEST_PROOF_BUNDLE_SHA256,
            )
            .unwrap();
        let entry_dir = cache.entry_dir(&cache_key);
        std::fs::write(entry_dir.join("artifact.bin"), b"tampered-object").unwrap();

        let lookup = cache
            .lookup_for_pipeline_with_expected_proof_bundle_sha256(
                &cache_key,
                TEST_PROOF_BUNDLE_SHA256,
            )
            .unwrap();

        assert_eq!(
            lookup.telemetry().status,
            CompileArtifactCacheStatus::RejectedCorrupt
        );
        assert_eq!(
            lookup.telemetry().reason.as_deref(),
            Some("mismatched/artifact/sha256")
        );

        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn oversized_cache_manifest_is_rejected_before_json_parse() {
        let root = temp_cache_root("oversized-manifest");
        let cache = LocalFilesystemCompileArtifactCache::new(&root);
        let cache_key = key(CompileArtifactProofPolicy::ProofTvFull);
        let entry_dir = cache.entry_dir(&cache_key);
        std::fs::create_dir_all(&entry_dir).unwrap();
        let manifest = std::fs::File::create(entry_dir.join("manifest.json")).unwrap();
        manifest
            .set_len(COMPILE_ARTIFACT_CACHE_MAX_MANIFEST_BYTES + 1)
            .unwrap();
        drop(manifest);
        std::fs::write(entry_dir.join("artifact.bin"), b"object").unwrap();

        let lookup = cache.lookup_for_pipeline(&cache_key).unwrap();

        assert_eq!(
            lookup.telemetry().status,
            CompileArtifactCacheStatus::RejectedCorrupt
        );
        assert_eq!(
            lookup.telemetry().reason.as_deref(),
            Some("oversized_manifest")
        );

        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn oversized_cache_artifact_declared_in_manifest_is_rejected_before_read() {
        let root = temp_cache_root("oversized-artifact-manifest");
        let cache = LocalFilesystemCompileArtifactCache::new(&root);
        let cache_key = key(CompileArtifactProofPolicy::ProofTvFull);
        cache
            .store_from_pipeline_with_proof_bundle_sha256(
                &cache_key,
                b"object",
                "trust-cg-test",
                TEST_PROOF_BUNDLE_SHA256,
            )
            .unwrap();
        let manifest_path = cache.entry_dir(&cache_key).join("manifest.json");
        let mut manifest: serde_json::Value =
            serde_json::from_slice(&std::fs::read(&manifest_path).unwrap()).unwrap();
        manifest
            .pointer_mut("/artifact/size_bytes")
            .unwrap()
            .clone_from(&serde_json::json!(
                COMPILE_ARTIFACT_CACHE_MAX_ARTIFACT_BYTES + 1
            ));
        std::fs::write(
            &manifest_path,
            serde_json::to_vec_pretty(&manifest).unwrap(),
        )
        .unwrap();

        let lookup = cache
            .lookup_for_pipeline_with_expected_proof_bundle_sha256(
                &cache_key,
                TEST_PROOF_BUNDLE_SHA256,
            )
            .unwrap();

        assert_eq!(
            lookup.telemetry().status,
            CompileArtifactCacheStatus::RejectedCorrupt
        );
        assert_eq!(
            lookup.telemetry().reason.as_deref(),
            Some("oversized_artifact_manifest")
        );

        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn oversized_cache_artifact_file_is_rejected_before_hashing() {
        let root = temp_cache_root("oversized-artifact");
        let cache = LocalFilesystemCompileArtifactCache::new(&root);
        let cache_key = key(CompileArtifactProofPolicy::ProofTvFull);
        cache
            .store_from_pipeline_with_proof_bundle_sha256(
                &cache_key,
                b"object",
                "trust-cg-test",
                TEST_PROOF_BUNDLE_SHA256,
            )
            .unwrap();
        let artifact =
            std::fs::File::create(cache.entry_dir(&cache_key).join("artifact.bin")).unwrap();
        artifact
            .set_len(COMPILE_ARTIFACT_CACHE_MAX_ARTIFACT_BYTES + 1)
            .unwrap();
        drop(artifact);

        let lookup = cache
            .lookup_for_pipeline_with_expected_proof_bundle_sha256(
                &cache_key,
                TEST_PROOF_BUNDLE_SHA256,
            )
            .unwrap();

        assert_eq!(
            lookup.telemetry().status,
            CompileArtifactCacheStatus::RejectedCorrupt
        );
        assert_eq!(
            lookup.telemetry().reason.as_deref(),
            Some("oversized_artifact")
        );

        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn missing_replay_safety_metadata_is_rejected_not_replayed() {
        let root = temp_cache_root("replay-safety");
        let cache = LocalFilesystemCompileArtifactCache::new(&root);
        let cache_key = key(CompileArtifactProofPolicy::ProofTvFull);

        cache
            .store_from_pipeline_with_proof_bundle_sha256(
                &cache_key,
                b"verified-object",
                "trust-cg-test",
                TEST_PROOF_BUNDLE_SHA256,
            )
            .unwrap();
        let entry_dir = cache.entry_dir(&cache_key);
        let manifest_path = entry_dir.join("manifest.json");
        let mut manifest: serde_json::Value =
            serde_json::from_slice(&std::fs::read(&manifest_path).unwrap()).unwrap();
        manifest.as_object_mut().unwrap().remove("replay_safety");
        std::fs::write(
            &manifest_path,
            serde_json::to_vec_pretty(&manifest).unwrap(),
        )
        .unwrap();

        let lookup = cache
            .lookup_for_pipeline_with_expected_proof_bundle_sha256(
                &cache_key,
                TEST_PROOF_BUNDLE_SHA256,
            )
            .unwrap();

        assert_eq!(
            lookup.telemetry().status,
            CompileArtifactCacheStatus::RejectedCorrupt
        );
        assert_eq!(
            lookup.telemetry().reason.as_deref(),
            Some("missing_bool/replay_safety/requires_proof_bundle_digest")
        );

        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn cache_store_rejects_incomplete_replay_identity() {
        let root = temp_cache_root("identity");
        let cache = LocalFilesystemCompileArtifactCache::new(&root);
        let mut cache_key = key(CompileArtifactProofPolicy::ProofTvFull);
        cache_key.dependency_identity.ay_identity.clear();
        cache_key.key_sha256 = cache_key.canonical_key_sha256();

        let error = cache
            .store_from_pipeline_with_proof_bundle_sha256(
                &cache_key,
                b"object",
                "trust-cg-test",
                TEST_PROOF_BUNDLE_SHA256,
            )
            .unwrap_err();

        assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
    }
}
