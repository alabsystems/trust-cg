// trust-cg-codegen/compile_policy.rs - Canonical compiler policy identity
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Frontend-neutral, canonical identity for explicit compiler policy.
//!
//! A [`CompilePolicy`] normalizes the effective target ABI and the public
//! [`CompilerConfig`] / [`JitConfig`] controls into four SHA-256 projections:
//! artifact bytes, evidence authority, invocation mechanics, and the complete
//! policy.  The encoding is a bounded, versioned binary TLV rather than a Rust
//! layout or debug string, so it is stable across processes and frontends.
//!
//! The three disjoint projections are classification tools, not independent
//! replay keys.  A target fact recorded in the artifact projection, for
//! example, also constrains target-specific proof evidence.  Consumers must
//! bind every projection relevant to the result they reuse: machine artifacts
//! with install/proof evidence require both Artifact and Evidence; a complete
//! request receipt requires Full.  Invocation may be excluded only when the
//! producer guarantees deterministic output across its invocation mechanics.
//!
//! This module deliberately does not resolve ambient compiler controls.  In
//! particular, the JIT validation field is
//! [`CompilerConfig::jit_validation_mode`] (the deterministic configured
//! policy), never [`CompilerConfig::resolve_jit_validation_mode`] (which may
//! consult the process environment). Raw override presence is retained as a
//! separate evidence field because the legacy ambient resolver treats `None`
//! differently from an explicit default-valued override.
//!
//! Schema v1 has distinct compiler-only, JIT-only, and combined route scopes.
//! The scope is part of the binary domain header, so identical TLV fields from
//! different routes cannot collide.  Route-specific constructors encode only
//! configuration the caller supplied; they never invent a missing config from
//! `Default`.

use std::{error::Error, fmt};

use sha2::{Digest, Sha256};

use crate::{
    compiler::{CompilerConfig, CompilerTraceLevel, JitValidationMode, RelocationModel},
    jit::{JitConfig, JitExternalSymbolResolutionPolicy, ProfileHookMode},
    pipeline::{DispatchVerifyMode, OptLevel},
    target::{Target, TargetEnvironment, TargetOperatingSystem, TargetSpec, TargetVendor},
};

/// Stable schema name for canonical compile-policy encodings.
pub const COMPILE_POLICY_SCHEMA: &str = "trust-cg.compile-policy.v1";

/// Binary schema version written into every canonical policy encoding.
pub const COMPILE_POLICY_SCHEMA_VERSION: u16 = 1;

/// Hard upper bound for one canonical partition encoding.
///
/// Version 1 is below 256 bytes per partition.  Keeping a generous fixed cap
/// prevents a future variable-sized control from silently turning policy-key
/// construction into an unbounded allocation surface.
pub const MAX_COMPILE_POLICY_ENCODING_BYTES: usize = 4096;

const ENCODING_MAGIC: &[u8; 8] = b"TCGCPOL\0";
const ENCODING_HEADER_BYTES: usize = ENCODING_MAGIC.len() + 2 + 1 + 1;
const TLV_HEADER_BYTES: usize = 2 + 2;
/// The largest inline field: a SHA-256 digest (`TAG_COMPILER_NEVER_INLINE`,
/// `TAG_COMPILER_EH_NOUNWIND_CALLEES`, `TAG_COMPILER_LINK_UNIT_DEFINITIONS`).
/// Every other field fits in 9 bytes.
const MAX_POLICY_FIELD_BYTES: usize = 32;

// Target identity.  Tags are global across all partitions so the full-policy
// encoding can merge and sort every field without introducing a second map.
const TAG_TARGET_ARCHITECTURE: u16 = 0x0001;
const TAG_TARGET_VENDOR: u16 = 0x0002;
const TAG_TARGET_OPERATING_SYSTEM: u16 = 0x0003;
const TAG_TARGET_ENVIRONMENT: u16 = 0x0004;
// Present only when the target carries a macOS deployment target (triple OS
// version or a driver-captured MACOSX_DEPLOYMENT_TARGET): absence is the
// canonical default, so every pre-existing digest is unchanged. It sets the
// Mach-O LC_BUILD_VERSION minimum OS, so it is Artifact-affecting.
const TAG_TARGET_APPLE_DEPLOYMENT_TARGET: u16 = 0x0005;

// CompilerConfig fields.  Keep these in struct declaration order.  The target
// field is validated against, then represented by, the normalized TargetSpec.
const TAG_COMPILER_OPT_LEVEL: u16 = 0x1001;
const TAG_COMPILER_EMIT_PROOFS: u16 = 0x1002;
const TAG_COMPILER_TRACE_LEVEL: u16 = 0x1003;
const TAG_COMPILER_EMIT_DEBUG: u16 = 0x1004;
const TAG_COMPILER_PARALLEL: u16 = 0x1005;
const TAG_COMPILER_CEGIS_SUPEROPT_BUDGET: u16 = 0x1006;
const TAG_COMPILER_FSYM_PREFLIGHT: u16 = 0x1007;
const TAG_COMPILER_JIT_FAST_REGALLOC: u16 = 0x1008;
const TAG_COMPILER_CONFIGURED_JIT_VALIDATION: u16 = 0x1009;
const TAG_COMPILER_PANIC_UNWIND: u16 = 0x100a;
const TAG_COMPILER_JIT_VALIDATION_OVERRIDE: u16 = 0x100b;
// A wall-clock-bounded CEGIS pass makes scheduling artifact-affecting. Keep
// the ordinary parallel field in Invocation and add this derived Artifact
// binding only when such a pass is armed.
const TAG_COMPILER_CEGIS_PARALLEL_SCHEDULE: u16 = 0x100c;
const TAG_COMPILER_JIT_EXTERNAL_SYMBOL_RESOLUTION: u16 = 0x100d;
const TAG_COMPILER_RELOCATION_MODEL: u16 = 0x100e;
// Present only when the function-sections object policy is ON: absence is the
// canonical default, so every pre-existing default-policy digest is unchanged.
const TAG_COMPILER_FUNCTION_SECTIONS: u16 = 0x100f;
/// Explicit AArch64 optional-ISA profile (`CompilerConfig::aarch64_isa_profile`),
/// encoded only when configured so every default-policy digest is unchanged.
const TAG_COMPILER_AARCH64_ISA_PROFILE: u16 = 0x1010;
/// The never-inline set (`CompilerConfig::never_inline`) as the SHA-256 of
/// its canonical encoding ([`never_inline_digest`]), encoded only when
/// non-empty so every default-policy digest is unchanged.
const TAG_COMPILER_NEVER_INLINE: u16 = 0x1011;
/// Non-unwinding exception frames (`CompilerConfig::eh_frames_cannot_unwind`),
/// encoded only when ON so every default-policy digest is unchanged.
const TAG_COMPILER_EH_FRAMES_CANNOT_UNWIND: u16 = 0x1012;
/// SHA-256 of the canonical nounwind callee set
/// (`CompilerConfig::eh_nounwind_callees`), encoded exactly when
/// `TAG_COMPILER_EH_FRAMES_CANNOT_UNWIND` is: the set is read only then.
const TAG_COMPILER_EH_NOUNWIND_CALLEES: u16 = 0x1013;
/// SHA-256 of the canonical link-unit definition set
/// (`CompilerConfig::link_unit_definitions`, ruling OD-216), encoded only when
/// non-empty so every default-policy digest is unchanged. It withholds
/// body-theorem credit and changes no emitted byte: Evidence.
const TAG_COMPILER_LINK_UNIT_DEFINITIONS: u16 = 0x1014;
/// Forced AArch64 object frame records, present only when enabled so existing
/// default-policy artifact identities remain unchanged.
const TAG_COMPILER_AARCH64_FORCE_FRAME_POINTERS: u16 = 0x1015;
/// The x86-64 certificate-free allocation request
/// (`CompilerConfig::x86_certificate_free_allocation`), present only when on
/// so every default-policy digest is unchanged. It changes emitted bytes:
/// Artifact.
const TAG_COMPILER_X86_CERTIFICATE_FREE_ALLOCATION: u16 = 0x1016;

// JitConfig fields.  Profile hooks and emit_entry_counters intentionally share
// one effective field: the latter is an ergonomic alias, not a second policy.
const TAG_JIT_OPT_LEVEL: u16 = 0x2001;
const TAG_JIT_VERIFY: u16 = 0x2002;
const TAG_JIT_DISPATCH_VERIFY: u16 = 0x2003;
const TAG_JIT_EFFECTIVE_PROFILE_HOOKS: u16 = 0x2004;
const TAG_JIT_CACHE_CERTIFICATES: u16 = 0x2005;
const TAG_JIT_EXTERNAL_SYMBOL_RESOLUTION: u16 = 0x2006;

/// A canonical compile-policy identity partition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CompilePolicyPartition {
    /// Projection of controls that can affect emitted machine/object bytes.
    Artifact,
    /// Projection of controls that affect verification, proof, certificate
    /// replay, or install authority.
    Evidence,
    /// Projection of controls that affect how compilation is invoked without
    /// changing its artifact/install-evidence contract.
    Invocation,
    /// Every explicit policy field, after semantic normalization.
    Full,
}

impl CompilePolicyPartition {
    const fn encoding_tag(self) -> u8 {
        match self {
            Self::Artifact => 1,
            Self::Evidence => 2,
            Self::Invocation => 3,
            Self::Full => 4,
        }
    }

    /// Stable lowercase label for manifests and diagnostics.
    pub const fn label(self) -> &'static str {
        match self {
            Self::Artifact => "artifact",
            Self::Evidence => "evidence",
            Self::Invocation => "invocation",
            Self::Full => "full",
        }
    }
}

/// Configuration route represented by a canonical compile policy.
///
/// Scope is independent of [`CompilePolicyPartition`]: every route has the
/// artifact/evidence/invocation projections and a full digest, but only fields
/// supplied to that route are encoded.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CompilePolicyScope {
    /// A [`CompilerConfig`] and explicit target ABI, with no invented JIT
    /// configuration.
    Compiler,
    /// A [`JitConfig`] and explicit target ABI, with no invented compiler
    /// configuration.
    Jit,
    /// The compatibility route binding both [`CompilerConfig`] and
    /// [`JitConfig`].
    Combined,
}

impl CompilePolicyScope {
    const fn encoding_tag(self) -> u8 {
        match self {
            Self::Compiler => 1,
            Self::Jit => 2,
            Self::Combined => 3,
        }
    }

    /// Stable lowercase label for manifests and diagnostics.
    pub const fn label(self) -> &'static str {
        match self {
            Self::Compiler => "compiler",
            Self::Jit => "jit",
            Self::Combined => "combined",
        }
    }
}

/// A SHA-256 digest bound to one compile-policy projection.
///
/// Except for [`CompilePolicyPartition::Full`], this is deliberately not a
/// standalone replay key.  Bind all projections relevant to the reused result.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct CompilePolicyDigest {
    scope: CompilePolicyScope,
    partition: CompilePolicyPartition,
    sha256: [u8; 32],
}

impl CompilePolicyDigest {
    fn of(
        scope: CompilePolicyScope,
        partition: CompilePolicyPartition,
        canonical_bytes: &[u8],
    ) -> Self {
        Self {
            scope,
            partition,
            sha256: Sha256::digest(canonical_bytes).into(),
        }
    }

    /// Route scope whose domain-separated encoding produced this digest.
    pub const fn scope(self) -> CompilePolicyScope {
        self.scope
    }

    /// Partition whose domain-separated encoding produced this digest.
    pub const fn partition(self) -> CompilePolicyPartition {
        self.partition
    }

    /// Raw 32-byte SHA-256 digest.
    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.sha256
    }

    /// Lowercase hexadecimal SHA-256 digest without a prefix.
    pub fn to_hex(self) -> String {
        let mut out = String::with_capacity(64);
        for byte in self.sha256 {
            use fmt::Write as _;
            let _ = write!(out, "{byte:02x}");
        }
        out
    }

    /// Conventional `sha256:<hex>` representation for cache manifests.
    pub fn to_prefixed_hex(self) -> String {
        format!("sha256:{}", self.to_hex())
    }
}

impl fmt::Debug for CompilePolicyDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CompilePolicyDigest")
            .field("scope", &self.scope)
            .field("partition", &self.partition)
            .field("sha256", &self.to_prefixed_hex())
            .finish()
    }
}

impl fmt::Display for CompilePolicyDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_prefixed_hex())
    }
}

/// All four canonical policy digests.
///
/// `artifact`, `evidence`, and `invocation` are disjoint projections.  Pair
/// `artifact` and `evidence` for compiled output plus install/proof evidence;
/// use `full` for a complete request/policy receipt.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CompilePolicyDigests {
    /// Identity of controls that can change emitted bytes.
    pub artifact: CompilePolicyDigest,
    /// Identity of verification/proof/diagnostic evidence controls.
    pub evidence: CompilePolicyDigest,
    /// Identity of invocation-only controls.
    pub invocation: CompilePolicyDigest,
    /// Identity of every normalized explicit policy field.
    pub full: CompilePolicyDigest,
}

/// Failure to construct a canonical compile policy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompilePolicyError {
    /// The separately supplied target ABI and the compiler configuration name
    /// different architectures.
    TargetArchitectureMismatch {
        /// Architecture selected by the explicit/normalized target spec.
        policy_target: Target,
        /// Architecture selected by `CompilerConfig`.
        compiler_target: Target,
    },
    /// An explicit AArch64 ISA profile was configured for another
    /// architecture; the policy refuses to encode a control no route honors.
    Aarch64IsaProfileOnNonAarch64Target {
        /// Architecture selected by `CompilerConfig`.
        compiler_target: Target,
    },
    /// Forced AArch64 frame records cannot apply to another architecture.
    Aarch64FramePointersOnNonAarch64Target {
        /// Architecture selected by `CompilerConfig`.
        compiler_target: Target,
    },
    /// A canonical encoding exceeded the public fixed-size bound.
    EncodingTooLarge {
        /// Partition whose encoding exceeded the bound.
        partition: CompilePolicyPartition,
        /// Attempted byte length.
        actual_bytes: usize,
        /// Maximum accepted byte length.
        maximum_bytes: usize,
    },
}

impl fmt::Display for CompilePolicyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TargetArchitectureMismatch {
                policy_target,
                compiler_target,
            } => write!(
                f,
                "compile policy target {policy_target:?} does not match CompilerConfig target {compiler_target:?}"
            ),
            Self::Aarch64IsaProfileOnNonAarch64Target { compiler_target } => write!(
                f,
                "an explicit AArch64 ISA profile cannot apply to CompilerConfig target \
                 {compiler_target:?}"
            ),
            Self::Aarch64FramePointersOnNonAarch64Target { compiler_target } => write!(
                f,
                "forced AArch64 frame pointers cannot apply to CompilerConfig target \
                 {compiler_target:?}"
            ),
            Self::EncodingTooLarge {
                partition,
                actual_bytes,
                maximum_bytes,
            } => write!(
                f,
                "{} compile-policy encoding is {actual_bytes} bytes (maximum {maximum_bytes})",
                partition.label()
            ),
        }
    }
}

impl Error for CompilePolicyError {}

/// Canonical, frontend-neutral identity of one explicit compilation policy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompilePolicy {
    scope: CompilePolicyScope,
    target_spec: TargetSpec,
    artifact_encoding: Vec<u8>,
    evidence_encoding: Vec<u8>,
    invocation_encoding: Vec<u8>,
    full_encoding: Vec<u8>,
    digests: CompilePolicyDigests,
}

impl CompilePolicy {
    /// Normalize and canonically encode a combined compiler/JIT policy.
    ///
    /// `target_spec` is normalized through [`TargetSpec::with_default_os_abi`]
    /// and then rebuilt as an explicit component tuple.  Consequently an
    /// architecture alias and its effective explicit host ABI have identical
    /// identities, while Darwin, GNU, MSVC, and unknown ABIs remain distinct.
    ///
    /// This compatibility constructor is exactly the
    /// [`CompilePolicyScope::Combined`] route.  Use [`Self::from_compiler`] or
    /// [`Self::from_jit`] when only one configuration was supplied.
    pub fn new(
        target_spec: TargetSpec,
        compiler: &CompilerConfig,
        jit: &JitConfig,
    ) -> Result<Self, CompilePolicyError> {
        Self::build(target_spec, PolicyInputs::Combined { compiler, jit })
    }

    /// Canonically encode a compiler-only route without inventing a
    /// `JitConfig`.
    ///
    /// The explicit target ABI must name the same architecture as
    /// `compiler.target`.  Architecture aliases are normalized exactly as in
    /// [`Self::new`].
    pub fn from_compiler(
        target_spec: TargetSpec,
        compiler: &CompilerConfig,
    ) -> Result<Self, CompilePolicyError> {
        Self::build(target_spec, PolicyInputs::Compiler(compiler))
    }

    /// Canonically encode a JIT-only route without inventing a
    /// `CompilerConfig`.
    ///
    /// `JitConfig` has no architecture field, so the supplied `target_spec` is
    /// the sole target/ABI authority for this route.
    pub fn from_jit(target_spec: TargetSpec, jit: &JitConfig) -> Result<Self, CompilePolicyError> {
        Self::build(target_spec, PolicyInputs::Jit(jit))
    }

    fn build(
        target_spec: TargetSpec,
        inputs: PolicyInputs<'_>,
    ) -> Result<Self, CompilePolicyError> {
        let scope = inputs.scope();
        let target_spec = normalize_target_spec(target_spec);
        let mut fields = Vec::with_capacity(inputs.field_capacity());
        push_target_fields(&mut fields, target_spec);
        match inputs {
            PolicyInputs::Compiler(compiler) => {
                push_compiler_fields(&mut fields, target_spec, compiler)?;
            }
            PolicyInputs::Jit(jit) => push_jit_fields(&mut fields, jit),
            PolicyInputs::Combined { compiler, jit } => {
                push_compiler_fields(&mut fields, target_spec, compiler)?;
                push_jit_fields(&mut fields, jit);
            }
        }

        // One in-place sort establishes canonical order for every projection.
        // Encoding filters this shared inline-field array without allocating a
        // second field vector for each digest.
        fields.sort_unstable_by_key(|field| field.tag);
        debug_assert!(fields.windows(2).all(|pair| pair[0].tag != pair[1].tag));

        let artifact_encoding = encode_partition(scope, CompilePolicyPartition::Artifact, &fields)?;
        let evidence_encoding = encode_partition(scope, CompilePolicyPartition::Evidence, &fields)?;
        let invocation_encoding =
            encode_partition(scope, CompilePolicyPartition::Invocation, &fields)?;
        let full_encoding = encode_partition(scope, CompilePolicyPartition::Full, &fields)?;
        let digests = CompilePolicyDigests {
            artifact: CompilePolicyDigest::of(
                scope,
                CompilePolicyPartition::Artifact,
                &artifact_encoding,
            ),
            evidence: CompilePolicyDigest::of(
                scope,
                CompilePolicyPartition::Evidence,
                &evidence_encoding,
            ),
            invocation: CompilePolicyDigest::of(
                scope,
                CompilePolicyPartition::Invocation,
                &invocation_encoding,
            ),
            full: CompilePolicyDigest::of(scope, CompilePolicyPartition::Full, &full_encoding),
        };

        Ok(Self {
            scope,
            target_spec,
            artifact_encoding,
            evidence_encoding,
            invocation_encoding,
            full_encoding,
            digests,
        })
    }

    /// Configuration route represented by this policy.
    pub const fn scope(&self) -> CompilePolicyScope {
        self.scope
    }

    /// Explicit target components after compatibility-default normalization.
    pub const fn target_spec(&self) -> TargetSpec {
        self.target_spec
    }

    /// All canonical partition digests.
    pub const fn digests(&self) -> CompilePolicyDigests {
        self.digests
    }

    /// Digest for one canonical partition.
    pub const fn digest(&self, partition: CompilePolicyPartition) -> CompilePolicyDigest {
        match partition {
            CompilePolicyPartition::Artifact => self.digests.artifact,
            CompilePolicyPartition::Evidence => self.digests.evidence,
            CompilePolicyPartition::Invocation => self.digests.invocation,
            CompilePolicyPartition::Full => self.digests.full,
        }
    }

    /// Versioned canonical TLV bytes for one partition.
    pub fn canonical_bytes(&self, partition: CompilePolicyPartition) -> &[u8] {
        match partition {
            CompilePolicyPartition::Artifact => &self.artifact_encoding,
            CompilePolicyPartition::Evidence => &self.evidence_encoding,
            CompilePolicyPartition::Invocation => &self.invocation_encoding,
            CompilePolicyPartition::Full => &self.full_encoding,
        }
    }
}

#[derive(Clone, Copy)]
enum PolicyInputs<'a> {
    Compiler(&'a CompilerConfig),
    Jit(&'a JitConfig),
    Combined {
        compiler: &'a CompilerConfig,
        jit: &'a JitConfig,
    },
}

impl PolicyInputs<'_> {
    const fn scope(self) -> CompilePolicyScope {
        match self {
            Self::Compiler(_) => CompilePolicyScope::Compiler,
            Self::Jit(_) => CompilePolicyScope::Jit,
            Self::Combined { .. } => CompilePolicyScope::Combined,
        }
    }

    const fn field_capacity(self) -> usize {
        match self {
            Self::Compiler(_) => 18,
            Self::Jit(_) => 10,
            Self::Combined { .. } => 24,
        }
    }
}

fn normalize_target_spec(target_spec: TargetSpec) -> TargetSpec {
    let resolved = target_spec.with_default_os_abi();
    let explicit = TargetSpec::new(
        resolved.architecture,
        resolved.vendor,
        resolved.operating_system,
        resolved.environment,
    );
    match resolved.apple_deployment_target() {
        // `resolved` already carried this version, so re-attaching it to the
        // same explicit Apple components cannot be refused.
        Some(version) => explicit
            .with_apple_deployment_target(
                version,
                crate::apple_deployment::AppleDeploymentTargetSource::TargetTriple,
            )
            .unwrap_or(resolved),
        None => explicit,
    }
}

fn push_target_fields(fields: &mut Vec<PolicyField>, target_spec: TargetSpec) {
    push_field(
        fields,
        CompilePolicyPartition::Artifact,
        TAG_TARGET_ARCHITECTURE,
        &[target_tag(target_spec.architecture)],
    );
    push_field(
        fields,
        CompilePolicyPartition::Artifact,
        TAG_TARGET_VENDOR,
        &[target_vendor_tag(target_spec.vendor)],
    );
    push_field(
        fields,
        CompilePolicyPartition::Artifact,
        TAG_TARGET_OPERATING_SYSTEM,
        &[target_operating_system_tag(target_spec.operating_system)],
    );
    push_field(
        fields,
        CompilePolicyPartition::Artifact,
        TAG_TARGET_ENVIRONMENT,
        &[target_environment_tag(target_spec.environment)],
    );
    if let Some(version) = target_spec.apple_deployment_target() {
        push_field(
            fields,
            CompilePolicyPartition::Artifact,
            TAG_TARGET_APPLE_DEPLOYMENT_TARGET,
            &version.macho_encoding().to_be_bytes(),
        );
    }
}

fn push_compiler_fields(
    fields: &mut Vec<PolicyField>,
    target_spec: TargetSpec,
    compiler: &CompilerConfig,
) -> Result<(), CompilePolicyError> {
    // Deliberately destructure without `..`: adding a public compiler control
    // must fail compilation until its canonical projection and tag are chosen.
    let CompilerConfig {
        opt_level,
        target,
        emit_proofs,
        trace_level,
        emit_debug,
        parallel,
        cegis_superopt_budget_sec,
        enable_fsym_trust_ir_preflight,
        enable_jit_fast_regalloc,
        jit_validation_mode_override,
        jit_external_symbol_resolution,
        panic_unwind,
        relocation_model,
        function_sections,
        aarch64_isa_profile,
        aarch64_force_frame_pointers,
        never_inline,
        eh_frames_cannot_unwind,
        eh_nounwind_callees,
        link_unit_definitions,
        x86_certificate_free_allocation,
    } = compiler;
    if target_spec.architecture != *target {
        return Err(CompilePolicyError::TargetArchitectureMismatch {
            policy_target: target_spec.architecture,
            compiler_target: *target,
        });
    }

    push_field(
        fields,
        CompilePolicyPartition::Artifact,
        TAG_COMPILER_OPT_LEVEL,
        &[opt_level_tag(*opt_level)],
    );
    push_field(
        fields,
        CompilePolicyPartition::Evidence,
        TAG_COMPILER_EMIT_PROOFS,
        &[bool_tag(*emit_proofs)],
    );
    push_field(
        fields,
        CompilePolicyPartition::Invocation,
        TAG_COMPILER_TRACE_LEVEL,
        &[compiler_trace_level_tag(*trace_level)],
    );
    push_field(
        fields,
        CompilePolicyPartition::Artifact,
        TAG_COMPILER_EMIT_DEBUG,
        &[bool_tag(*emit_debug)],
    );
    push_field(
        fields,
        CompilePolicyPartition::Invocation,
        TAG_COMPILER_PARALLEL,
        &[bool_tag(*parallel)],
    );
    push_field(
        fields,
        CompilePolicyPartition::Artifact,
        TAG_COMPILER_CEGIS_SUPEROPT_BUDGET,
        &option_u64_bytes(*cegis_superopt_budget_sec),
    );
    if cegis_superopt_budget_sec.is_some() {
        push_field(
            fields,
            CompilePolicyPartition::Artifact,
            TAG_COMPILER_CEGIS_PARALLEL_SCHEDULE,
            &[bool_tag(*parallel)],
        );
    }
    push_field(
        fields,
        CompilePolicyPartition::Evidence,
        TAG_COMPILER_FSYM_PREFLIGHT,
        &[bool_tag(*enable_fsym_trust_ir_preflight)],
    );
    push_field(
        fields,
        CompilePolicyPartition::Artifact,
        TAG_COMPILER_JIT_FAST_REGALLOC,
        &[bool_tag(*enable_jit_fast_regalloc)],
    );
    // This deterministic query intentionally ignores TCG_JIT_UNCHECKED.
    push_field(
        fields,
        CompilePolicyPartition::Evidence,
        TAG_COMPILER_CONFIGURED_JIT_VALIDATION,
        &[jit_validation_mode_tag(compiler.jit_validation_mode())],
    );
    push_field(
        fields,
        CompilePolicyPartition::Artifact,
        TAG_COMPILER_PANIC_UNWIND,
        &[bool_tag(*panic_unwind)],
    );
    // Preserve raw override presence as well as its configured meaning.  The
    // legacy ambient resolver treats `None` differently from an explicit
    // default-valued override.
    push_field(
        fields,
        CompilePolicyPartition::Evidence,
        TAG_COMPILER_JIT_VALIDATION_OVERRIDE,
        &option_jit_validation_mode_bytes(*jit_validation_mode_override),
    );
    push_field(
        fields,
        CompilePolicyPartition::Artifact,
        TAG_COMPILER_JIT_EXTERNAL_SYMBOL_RESOLUTION,
        &[jit_external_symbol_resolution_policy_tag(
            *jit_external_symbol_resolution,
        )],
    );
    // The relocation model selects GOT-indirect versus PC-relative symbol
    // access and the TLS access models, so it changes the emitted bytes.
    push_field(
        fields,
        CompilePolicyPartition::Artifact,
        TAG_COMPILER_RELOCATION_MODEL,
        &[relocation_model_tag(*relocation_model)],
    );
    // Function sections change the emitted object's section layout, so the
    // control is Artifact-affecting.
    if *function_sections {
        push_field(
            fields,
            CompilePolicyPartition::Artifact,
            TAG_COMPILER_FUNCTION_SECTIONS,
            &[bool_tag(true)],
        );
    }
    // An explicit AArch64 ISA profile widens or narrows which instructions
    // the selector may emit, so it is Artifact-affecting. Encoded as the
    // profile's stable feature bits; absent for the target contract.
    if let Some(profile) = aarch64_isa_profile {
        if *target != Target::Aarch64 {
            return Err(CompilePolicyError::Aarch64IsaProfileOnNonAarch64Target {
                compiler_target: *target,
            });
        }
        push_field(
            fields,
            CompilePolicyPartition::Artifact,
            TAG_COMPILER_AARCH64_ISA_PROFILE,
            &profile.feature_bits().to_be_bytes(),
        );
    }
    if *aarch64_force_frame_pointers {
        if *target != Target::Aarch64 {
            return Err(CompilePolicyError::Aarch64FramePointersOnNonAarch64Target {
                compiler_target: *target,
            });
        }
        push_field(
            fields,
            CompilePolicyPartition::Artifact,
            TAG_COMPILER_AARCH64_FORCE_FRAME_POINTERS,
            &[bool_tag(true)],
        );
    }
    // A never-inline name keeps a call that OPT-4 would otherwise splice, so
    // the set is Artifact-affecting. Absent when empty.
    if !never_inline.is_empty() {
        push_field(
            fields,
            CompilePolicyPartition::Artifact,
            TAG_COMPILER_NEVER_INLINE,
            &never_inline_digest(never_inline),
        );
    }
    // Non-unwinding frames keep a propagation entry only for a region that
    // holds a call which may unwind, decided against the nounwind callee set,
    // so both change the emitted exception tables and are Artifact-affecting.
    // The set is read only under the policy, so it is encoded only with it.
    if *eh_frames_cannot_unwind {
        push_field(
            fields,
            CompilePolicyPartition::Artifact,
            TAG_COMPILER_EH_FRAMES_CANNOT_UNWIND,
            &[bool_tag(true)],
        );
        push_field(
            fields,
            CompilePolicyPartition::Artifact,
            TAG_COMPILER_EH_NOUNWIND_CALLEES,
            &nounwind_callees_sha256(eh_nounwind_callees),
        );
    }
    // OD-216: the routines the link unit's other compile units define decide
    // which body theorems are refused, never an emitted byte, so the set is
    // Evidence-affecting. Absent when empty.
    if !link_unit_definitions.is_empty() {
        push_field(
            fields,
            CompilePolicyPartition::Evidence,
            TAG_COMPILER_LINK_UNIT_DEFINITIONS,
            &link_unit_definitions_sha256(link_unit_definitions),
        );
    }
    // The certificate-free allocation request changes which registers and
    // copies an x86-64 object compile emits. Absent when off.
    if *x86_certificate_free_allocation {
        push_field(
            fields,
            CompilePolicyPartition::Artifact,
            TAG_COMPILER_X86_CERTIFICATE_FREE_ALLOCATION,
            &[bool_tag(true)],
        );
    }
    Ok(())
}

/// The SHA-256 of a link-unit definition set's canonical encoding
/// ([`name_set_sha256`] under its own domain tag).
fn link_unit_definitions_sha256(definitions: &std::collections::BTreeSet<String>) -> [u8; 32] {
    name_set_sha256(b"trust-cg.compiler.link-unit-definitions.v1\0", definitions)
}

/// The SHA-256 of a never-inline set's canonical encoding ([`name_set_sha256`]
/// under its own domain tag).
pub(crate) fn never_inline_digest(never_inline: &std::collections::BTreeSet<String>) -> [u8; 32] {
    name_set_sha256(b"trust-cg.compiler.never-inline.v1\0", never_inline)
}

/// The SHA-256 of a nounwind callee set's canonical encoding ([`name_set_sha256`]
/// under its own domain tag).
fn nounwind_callees_sha256(callees: &std::collections::BTreeSet<String>) -> [u8; 32] {
    name_set_sha256(b"trust-cg.compiler.eh-nounwind-callees.v1\0", callees)
}

/// SHA-256 of a name set: a domain tag, then each name in sorted (`BTreeSet`)
/// order as a big-endian `u64` byte length followed by its UTF-8 bytes, so
/// distinct sets (or one set under two domains) never share an encoding.
fn name_set_sha256(domain: &[u8], names: &std::collections::BTreeSet<String>) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    for name in names {
        hasher.update((name.len() as u64).to_be_bytes());
        hasher.update(name.as_bytes());
    }
    hasher.finalize().into()
}

fn push_jit_fields(fields: &mut Vec<PolicyField>, jit: &JitConfig) {
    // Same exhaustive structural check for the low-level JIT surface.
    let JitConfig {
        opt_level,
        verify,
        verify_dispatch,
        profile_hooks: _,
        emit_entry_counters: _,
        cache_certificates,
        external_symbol_resolution,
    } = jit;

    push_field(
        fields,
        CompilePolicyPartition::Artifact,
        TAG_JIT_OPT_LEVEL,
        &[opt_level_tag(*opt_level)],
    );
    push_field(
        fields,
        CompilePolicyPartition::Evidence,
        TAG_JIT_VERIFY,
        &[bool_tag(*verify)],
    );
    // FallbackOnFailure may replace a heterogeneous dispatch plan with a
    // CPU-only plan, changing downstream emitted bytes.
    push_field(
        fields,
        CompilePolicyPartition::Artifact,
        TAG_JIT_DISPATCH_VERIFY,
        &dispatch_verify_mode_bytes(*verify_dispatch),
    );
    push_field(
        fields,
        CompilePolicyPartition::Artifact,
        TAG_JIT_EFFECTIVE_PROFILE_HOOKS,
        &[profile_hook_mode_tag(jit.effective_profile_hooks())],
    );
    push_field(
        fields,
        CompilePolicyPartition::Evidence,
        TAG_JIT_CACHE_CERTIFICATES,
        &[bool_tag(*cache_certificates)],
    );
    push_field(
        fields,
        CompilePolicyPartition::Artifact,
        TAG_JIT_EXTERNAL_SYMBOL_RESOLUTION,
        &[jit_external_symbol_resolution_policy_tag(
            *external_symbol_resolution,
        )],
    );
}

#[derive(Debug, Clone, Copy)]
struct PolicyField {
    partition: CompilePolicyPartition,
    tag: u16,
    value: [u8; MAX_POLICY_FIELD_BYTES],
    value_len: u8,
}

fn push_field(
    fields: &mut Vec<PolicyField>,
    partition: CompilePolicyPartition,
    tag: u16,
    value: &[u8],
) {
    assert!(
        value.len() <= MAX_POLICY_FIELD_BYTES,
        "compile-policy field {tag:#06x} exceeds its fixed inline payload"
    );
    let mut inline_value = [0; MAX_POLICY_FIELD_BYTES];
    inline_value[..value.len()].copy_from_slice(value);
    fields.push(PolicyField {
        partition,
        tag,
        value: inline_value,
        value_len: value.len() as u8,
    });
}

fn encode_partition(
    scope: CompilePolicyScope,
    partition: CompilePolicyPartition,
    fields: &[PolicyField],
) -> Result<Vec<u8>, CompilePolicyError> {
    let selected = || {
        fields.iter().filter(|field| {
            partition == CompilePolicyPartition::Full || field.partition == partition
        })
    };

    let expected_bytes = ENCODING_HEADER_BYTES
        + selected()
            .map(|field| TLV_HEADER_BYTES + usize::from(field.value_len))
            .sum::<usize>();
    if expected_bytes > MAX_COMPILE_POLICY_ENCODING_BYTES {
        return Err(CompilePolicyError::EncodingTooLarge {
            partition,
            actual_bytes: expected_bytes,
            maximum_bytes: MAX_COMPILE_POLICY_ENCODING_BYTES,
        });
    }

    let mut out = Vec::with_capacity(expected_bytes);
    out.extend_from_slice(ENCODING_MAGIC);
    out.extend_from_slice(&COMPILE_POLICY_SCHEMA_VERSION.to_be_bytes());
    out.push(partition.encoding_tag());
    out.push(scope.encoding_tag());

    let mut previous_tag = None;
    for field in selected() {
        debug_assert_ne!(previous_tag, Some(field.tag), "duplicate policy TLV tag");
        previous_tag = Some(field.tag);
        let value_len = u16::from(field.value_len);
        out.extend_from_slice(&field.tag.to_be_bytes());
        out.extend_from_slice(&value_len.to_be_bytes());
        out.extend_from_slice(&field.value[..usize::from(field.value_len)]);
    }
    debug_assert_eq!(out.len(), expected_bytes);
    Ok(out)
}

const fn bool_tag(value: bool) -> u8 {
    if value { 1 } else { 0 }
}

const fn option_jit_validation_mode_bytes(value: Option<JitValidationMode>) -> [u8; 2] {
    match value {
        Some(mode) => [1, jit_validation_mode_tag(mode)],
        None => [0, 0],
    }
}

const fn option_u64_bytes(value: Option<u64>) -> [u8; 9] {
    let (present, number) = match value {
        Some(number) => (1, number),
        None => (0, 0),
    };
    let bytes = number.to_be_bytes();
    [
        present, bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
    ]
}

const fn target_tag(target: Target) -> u8 {
    match target {
        Target::X86_64 => 1,
        Target::Aarch64 => 2,
        Target::Riscv64 => 3,
    }
}

const fn target_vendor_tag(vendor: TargetVendor) -> u8 {
    match vendor {
        TargetVendor::Unknown => 0,
        TargetVendor::Apple => 1,
        TargetVendor::Pc => 2,
    }
}

const fn target_operating_system_tag(operating_system: TargetOperatingSystem) -> u8 {
    match operating_system {
        TargetOperatingSystem::Unknown => 0,
        TargetOperatingSystem::Linux => 1,
        TargetOperatingSystem::Darwin => 2,
        TargetOperatingSystem::Windows => 3,
    }
}

const fn target_environment_tag(environment: TargetEnvironment) -> u8 {
    match environment {
        TargetEnvironment::Unknown => 0,
        TargetEnvironment::Gnu => 1,
        TargetEnvironment::Msvc => 2,
    }
}

const fn relocation_model_tag(model: RelocationModel) -> u8 {
    match model {
        RelocationModel::Static => 0,
        RelocationModel::Pie => 1,
        RelocationModel::Pic => 2,
    }
}

const fn opt_level_tag(opt_level: OptLevel) -> u8 {
    match opt_level {
        OptLevel::O0 => 0,
        OptLevel::O1 => 1,
        OptLevel::O2 => 2,
        OptLevel::O3 => 3,
    }
}

const fn compiler_trace_level_tag(trace_level: CompilerTraceLevel) -> u8 {
    match trace_level {
        CompilerTraceLevel::None => 0,
        CompilerTraceLevel::Summary => 1,
        CompilerTraceLevel::Full => 2,
    }
}

const fn jit_validation_mode_tag(mode: JitValidationMode) -> u8 {
    match mode {
        JitValidationMode::Unchecked => 0,
        JitValidationMode::CachedVerified => 1,
        JitValidationMode::AlwaysVerify => 2,
    }
}

fn dispatch_verify_mode_bytes(mode: DispatchVerifyMode) -> [u8; 5] {
    let (tag, argument) = match mode {
        DispatchVerifyMode::Off => (0, 0),
        DispatchVerifyMode::FallbackOnFailure => (1, 0),
        DispatchVerifyMode::ErrorOnFailure => (2, 0),
        DispatchVerifyMode::Sampled { modulus } => (3, modulus.get()),
    };
    let bytes = argument.to_be_bytes();
    [tag, bytes[0], bytes[1], bytes[2], bytes[3]]
}

const fn profile_hook_mode_tag(mode: ProfileHookMode) -> u8 {
    match mode {
        ProfileHookMode::None => 0,
        ProfileHookMode::CallCounts => 1,
        ProfileHookMode::CallCountsAndTiming => 2,
        ProfileHookMode::BlockCounts => 3,
        ProfileHookMode::BlockCountsAndTiming => 4,
        ProfileHookMode::EdgeCounts => 5,
        ProfileHookMode::BlockFrequency => 6,
        ProfileHookMode::LoopHeads => 7,
    }
}

const fn jit_external_symbol_resolution_policy_tag(
    policy: JitExternalSymbolResolutionPolicy,
) -> u8 {
    match policy {
        JitExternalSymbolResolutionPolicy::ExplicitThenProcess => 0,
        JitExternalSymbolResolutionPolicy::ExplicitOnly => 1,
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn apple_deployment_target_is_bound_in_the_artifact_projection() {
        use crate::apple_deployment::{AppleDeploymentTargetSource, AppleOsVersion};

        let config = CompilerConfig::default();
        let policy = |spec: TargetSpec| CompilePolicy::from_compiler(spec, &config).unwrap();
        let darwin = TargetSpec::parse("aarch64-apple-darwin").unwrap();
        let twelve = TargetSpec::parse("aarch64-apple-macos12.0").unwrap();
        let thirteen = TargetSpec::parse("aarch64-apple-macos13.0").unwrap();

        let unversioned = policy(darwin);
        let at_twelve = policy(twelve);
        // Exactly one extra TLV (4-byte header, 4-byte encoded version): an
        // unversioned target keeps its pre-existing encoding.
        assert_eq!(
            at_twelve
                .canonical_bytes(CompilePolicyPartition::Artifact)
                .len(),
            unversioned
                .canonical_bytes(CompilePolicyPartition::Artifact)
                .len()
                + TLV_HEADER_BYTES
                + 4
        );
        assert_ne!(
            unversioned.digest(CompilePolicyPartition::Artifact),
            at_twelve.digest(CompilePolicyPartition::Artifact)
        );
        assert_ne!(
            at_twelve.digest(CompilePolicyPartition::Artifact),
            policy(thirteen).digest(CompilePolicyPartition::Artifact)
        );
        // The version affects object bytes only, so it is not evidence.
        assert_eq!(
            unversioned.digest(CompilePolicyPartition::Evidence),
            at_twelve.digest(CompilePolicyPartition::Evidence)
        );
        // A driver-captured version is the same identity as the triple's.
        let captured = darwin
            .with_apple_deployment_target(
                AppleOsVersion::new(12, 0, 0),
                AppleDeploymentTargetSource::Environment,
            )
            .unwrap();
        assert_eq!(policy(captured).digests(), at_twelve.digests());
        assert_eq!(policy(captured).target_spec(), twelve);
    }
    use std::num::NonZeroU32;

    use super::*;

    fn linux_x86_64() -> TargetSpec {
        TargetSpec::new(
            Target::X86_64,
            TargetVendor::Unknown,
            TargetOperatingSystem::Linux,
            TargetEnvironment::Gnu,
        )
    }

    fn baseline() -> (TargetSpec, CompilerConfig, JitConfig) {
        let compiler = CompilerConfig {
            opt_level: OptLevel::O2,
            target: Target::X86_64,
            emit_proofs: false,
            trace_level: CompilerTraceLevel::None,
            emit_debug: false,
            parallel: true,
            cegis_superopt_budget_sec: None,
            enable_fsym_trust_ir_preflight: false,
            enable_jit_fast_regalloc: false,
            jit_validation_mode_override: Some(JitValidationMode::CachedVerified),
            jit_external_symbol_resolution: JitExternalSymbolResolutionPolicy::ExplicitThenProcess,
            panic_unwind: false,
            relocation_model: RelocationModel::Static,
            function_sections: false,
            aarch64_isa_profile: None,
            aarch64_force_frame_pointers: false,
            never_inline: Default::default(),
            eh_frames_cannot_unwind: false,
            eh_nounwind_callees: std::collections::BTreeSet::new(),
            link_unit_definitions: std::collections::BTreeSet::new(),
            x86_certificate_free_allocation: false,
        };
        let jit = JitConfig {
            opt_level: OptLevel::O2,
            verify: true,
            verify_dispatch: DispatchVerifyMode::ErrorOnFailure,
            profile_hooks: ProfileHookMode::None,
            emit_entry_counters: false,
            cache_certificates: true,
            external_symbol_resolution: JitExternalSymbolResolutionPolicy::ExplicitThenProcess,
        };
        (linux_x86_64(), compiler, jit)
    }

    fn policy(target: TargetSpec, compiler: &CompilerConfig, jit: &JitConfig) -> CompilePolicy {
        CompilePolicy::new(target, compiler, jit).expect("policy should be valid")
    }

    fn assert_only_partition_changed(
        before: &CompilePolicy,
        after: &CompilePolicy,
        changed: CompilePolicyPartition,
    ) {
        for partition in [
            CompilePolicyPartition::Artifact,
            CompilePolicyPartition::Evidence,
            CompilePolicyPartition::Invocation,
        ] {
            assert_eq!(
                before.digest(partition) != after.digest(partition),
                partition == changed,
                "unexpected {partition:?} partition response"
            );
        }
        assert_ne!(before.digests().full, after.digests().full);
    }

    fn encoded_tags(policy: &CompilePolicy, partition: CompilePolicyPartition) -> Vec<u16> {
        let bytes = policy.canonical_bytes(partition);
        let mut cursor = ENCODING_HEADER_BYTES;
        let mut tags = Vec::new();
        while cursor < bytes.len() {
            let tag = u16::from_be_bytes([bytes[cursor], bytes[cursor + 1]]);
            let len = usize::from(u16::from_be_bytes([bytes[cursor + 2], bytes[cursor + 3]]));
            tags.push(tag);
            cursor += TLV_HEADER_BYTES + len;
        }
        assert_eq!(cursor, bytes.len());
        tags
    }

    #[test]
    fn route_scopes_encode_only_supplied_configuration() {
        let (target, compiler, jit) = baseline();
        let compiler_only =
            CompilePolicy::from_compiler(target, &compiler).expect("compiler policy");
        let jit_only = CompilePolicy::from_jit(target, &jit).expect("JIT policy");
        let combined = policy(target, &compiler, &jit);

        assert_eq!(compiler_only.scope(), CompilePolicyScope::Compiler);
        assert_eq!(jit_only.scope(), CompilePolicyScope::Jit);
        assert_eq!(combined.scope(), CompilePolicyScope::Combined);
        for partition in [
            CompilePolicyPartition::Artifact,
            CompilePolicyPartition::Evidence,
            CompilePolicyPartition::Invocation,
            CompilePolicyPartition::Full,
        ] {
            assert_eq!(
                compiler_only.digest(partition).scope(),
                compiler_only.scope()
            );
            assert_eq!(jit_only.digest(partition).scope(), jit_only.scope());
            assert_eq!(combined.digest(partition).scope(), combined.scope());
            assert_ne!(compiler_only.digest(partition), combined.digest(partition));
            assert_ne!(jit_only.digest(partition), combined.digest(partition));
            assert_ne!(compiler_only.digest(partition), jit_only.digest(partition));
        }

        let combined_tags = encoded_tags(&combined, CompilePolicyPartition::Full);
        let compiler_tags = encoded_tags(&compiler_only, CompilePolicyPartition::Full);
        let jit_tags = encoded_tags(&jit_only, CompilePolicyPartition::Full);
        assert_eq!(combined_tags.len(), 23);
        assert_eq!(compiler_tags.len(), 17);
        assert_eq!(jit_tags.len(), 10);
        assert_eq!(
            compiler_tags,
            combined_tags
                .iter()
                .copied()
                .filter(|tag| *tag < 0x2000)
                .collect::<Vec<_>>(),
            "compiler-only scope must not synthesize JIT fields"
        );
        assert_eq!(
            jit_tags,
            combined_tags
                .iter()
                .copied()
                .filter(|tag| *tag < 0x1000 || *tag >= 0x2000)
                .collect::<Vec<_>>(),
            "JIT-only scope must not synthesize compiler fields"
        );
    }

    #[test]
    fn every_route_normalizes_target_aliases() {
        let (_, compiler, jit) = baseline();
        let alias = TargetSpec::unknown_for_architecture(Target::X86_64);
        let explicit = TargetSpec::default_for_architecture(Target::X86_64);

        assert_eq!(
            CompilePolicy::from_compiler(alias, &compiler).unwrap(),
            CompilePolicy::from_compiler(explicit, &compiler).unwrap()
        );
        assert_eq!(
            CompilePolicy::from_jit(alias, &jit).unwrap(),
            CompilePolicy::from_jit(explicit, &jit).unwrap()
        );
    }

    #[test]
    fn every_compiler_config_field_has_an_explicit_partition() {
        let (target, compiler, jit) = baseline();
        let base = policy(target, &compiler, &jit);

        let mut changed = compiler.clone();
        changed.opt_level = OptLevel::O3;
        assert_only_partition_changed(
            &base,
            &policy(target, &changed, &jit),
            CompilePolicyPartition::Artifact,
        );

        let mut changed = compiler.clone();
        changed.emit_proofs = true;
        // Pin the configured validation mode so this mutation isolates the
        // emit-proofs evidence field rather than changing two semantic fields.
        changed.jit_validation_mode_override = Some(JitValidationMode::CachedVerified);
        assert_only_partition_changed(
            &base,
            &policy(target, &changed, &jit),
            CompilePolicyPartition::Evidence,
        );

        let mut changed = compiler.clone();
        changed.trace_level = CompilerTraceLevel::Full;
        assert_only_partition_changed(
            &base,
            &policy(target, &changed, &jit),
            CompilePolicyPartition::Invocation,
        );

        let mut changed = compiler.clone();
        changed.emit_debug = true;
        assert_only_partition_changed(
            &base,
            &policy(target, &changed, &jit),
            CompilePolicyPartition::Artifact,
        );

        let mut changed = compiler.clone();
        changed.parallel = false;
        assert_only_partition_changed(
            &base,
            &policy(target, &changed, &jit),
            CompilePolicyPartition::Invocation,
        );

        let mut changed = compiler.clone();
        changed.cegis_superopt_budget_sec = Some(17);
        assert_only_partition_changed(
            &base,
            &policy(target, &changed, &jit),
            CompilePolicyPartition::Artifact,
        );

        let mut changed = compiler.clone();
        changed.enable_fsym_trust_ir_preflight = true;
        assert_only_partition_changed(
            &base,
            &policy(target, &changed, &jit),
            CompilePolicyPartition::Evidence,
        );

        let mut changed = compiler.clone();
        changed.enable_jit_fast_regalloc = true;
        assert_only_partition_changed(
            &base,
            &policy(target, &changed, &jit),
            CompilePolicyPartition::Artifact,
        );

        let mut changed = compiler.clone();
        changed.jit_validation_mode_override = Some(JitValidationMode::AlwaysVerify);
        assert_only_partition_changed(
            &base,
            &policy(target, &changed, &jit),
            CompilePolicyPartition::Evidence,
        );

        let mut changed = compiler.clone();
        changed.jit_external_symbol_resolution = JitExternalSymbolResolutionPolicy::ExplicitOnly;
        assert_only_partition_changed(
            &base,
            &policy(target, &changed, &jit),
            CompilePolicyPartition::Artifact,
        );

        let mut changed = compiler.clone();
        changed.panic_unwind = true;
        assert_only_partition_changed(
            &base,
            &policy(target, &changed, &jit),
            CompilePolicyPartition::Artifact,
        );

        // Each relocation model is a distinct artifact identity.
        let mut seen = std::collections::HashSet::new();
        for model in RelocationModel::ALL {
            let mut changed = compiler.clone();
            changed.relocation_model = model;
            let changed_policy = policy(target, &changed, &jit);
            if model != compiler.relocation_model {
                assert_only_partition_changed(
                    &base,
                    &changed_policy,
                    CompilePolicyPartition::Artifact,
                );
            }
            assert!(seen.insert(changed_policy.digest(CompilePolicyPartition::Artifact)));
        }

        let mut changed = compiler.clone();
        changed.function_sections = true;
        assert_only_partition_changed(
            &base,
            &policy(target, &changed, &jit),
            CompilePolicyPartition::Artifact,
        );

        let mut changed = compiler.clone();
        changed.eh_frames_cannot_unwind = true;
        assert_only_partition_changed(
            &base,
            &policy(target, &changed, &jit),
            CompilePolicyPartition::Artifact,
        );

        // The nounwind callee set changes the enabled policy's Artifact
        // partition only, and is not encoded at all while the policy is off.
        let enabled = policy(target, &changed, &jit);
        let mut callee = changed;
        callee
            .eh_nounwind_callees
            .insert("nounwind_drop".to_owned());
        assert_only_partition_changed(
            &enabled,
            &policy(target, &callee, &jit),
            CompilePolicyPartition::Artifact,
        );
        let mut unused = compiler;
        unused
            .eh_nounwind_callees
            .insert("nounwind_drop".to_owned());
        assert_eq!(
            base.digests().full,
            policy(target, &unused, &jit).digests().full
        );
    }

    /// The non-unwinding exception-frame fields are encoded only when ON, so
    /// the default policy's canonical bytes (and every golden digest) are
    /// unchanged and the enabled policy carries exactly one Artifact TLV for
    /// the control and one for its nounwind callee set.
    #[test]
    fn eh_frames_cannot_unwind_is_present_only_when_enabled() {
        let (target, compiler, _) = baseline();
        for tag in [
            TAG_COMPILER_EH_FRAMES_CANNOT_UNWIND,
            TAG_COMPILER_EH_NOUNWIND_CALLEES,
        ] {
            assert_eh_frame_tag_present_only_when_enabled(target, &compiler, tag);
        }
    }

    fn assert_eh_frame_tag_present_only_when_enabled(
        target: TargetSpec,
        compiler: &CompilerConfig,
        tag: u16,
    ) {
        let tag = tag.to_be_bytes();
        let count_tag = |policy: &CompilePolicy, partition| {
            let bytes = policy.canonical_bytes(partition);
            let mut cursor = ENCODING_HEADER_BYTES;
            let mut found = 0usize;
            while cursor < bytes.len() {
                let len = usize::from(u16::from_be_bytes([bytes[cursor + 2], bytes[cursor + 3]]));
                found += usize::from(bytes[cursor..cursor + 2] == tag);
                cursor += TLV_HEADER_BYTES + len;
            }
            found
        };
        let off = CompilePolicy::from_compiler(target, compiler).unwrap();
        let mut enabled = compiler.clone();
        enabled.eh_frames_cannot_unwind = true;
        let on = CompilePolicy::from_compiler(target, &enabled).unwrap();
        assert_eq!(count_tag(&off, CompilePolicyPartition::Full), 0);
        assert_eq!(count_tag(&on, CompilePolicyPartition::Artifact), 1);
        assert_eq!(count_tag(&on, CompilePolicyPartition::Full), 1);
        assert_eq!(count_tag(&on, CompilePolicyPartition::Evidence), 0);
        assert_eq!(count_tag(&on, CompilePolicyPartition::Invocation), 0);
    }

    /// The function-sections field is encoded only when ON: the default
    /// policy's canonical bytes carry no such tag (so every pre-existing
    /// digest, including the goldens below, is unchanged) and the enabled
    /// policy carries exactly one Artifact TLV for it.
    #[test]
    fn function_sections_is_present_only_when_enabled() {
        let (target, compiler, _) = baseline();
        let tag = TAG_COMPILER_FUNCTION_SECTIONS.to_be_bytes();
        let has_tag = |policy: &CompilePolicy, partition| {
            let bytes = policy.canonical_bytes(partition);
            let mut cursor = ENCODING_HEADER_BYTES;
            let mut found = false;
            while cursor < bytes.len() {
                let len = usize::from(u16::from_be_bytes([bytes[cursor + 2], bytes[cursor + 3]]));
                found |= bytes[cursor..cursor + 2] == tag;
                cursor += TLV_HEADER_BYTES + len;
            }
            found
        };
        let off = CompilePolicy::from_compiler(target, &compiler).unwrap();
        let mut enabled = compiler.clone();
        enabled.function_sections = true;
        let on = CompilePolicy::from_compiler(target, &enabled).unwrap();
        assert!(!has_tag(&off, CompilePolicyPartition::Full));
        assert!(has_tag(&on, CompilePolicyPartition::Artifact));
        assert!(has_tag(&on, CompilePolicyPartition::Full));
        assert!(!has_tag(&on, CompilePolicyPartition::Evidence));
        assert!(!has_tag(&on, CompilePolicyPartition::Invocation));
    }

    /// The never-inline set is encoded only when non-empty, only in the
    /// Artifact partition, and distinct sets (including a name split
    /// differently across entries) are distinct identities.
    #[test]
    fn never_inline_is_an_artifact_field_only_when_non_empty() {
        let (target, compiler, jit) = baseline();
        let tag = TAG_COMPILER_NEVER_INLINE.to_be_bytes();
        let has_tag = |policy: &CompilePolicy, partition| {
            let bytes = policy.canonical_bytes(partition);
            let mut cursor = ENCODING_HEADER_BYTES;
            let mut found = false;
            while cursor < bytes.len() {
                let len = usize::from(u16::from_be_bytes([bytes[cursor + 2], bytes[cursor + 3]]));
                found |= bytes[cursor..cursor + 2] == tag;
                cursor += TLV_HEADER_BYTES + len;
            }
            found
        };
        let base = policy(target, &compiler, &jit);
        assert!(!has_tag(&base, CompilePolicyPartition::Full));
        let with = |names: &[&str]| {
            let mut changed = compiler.clone();
            changed.never_inline = names.iter().map(|name| (*name).to_owned()).collect();
            policy(target, &changed, &jit)
        };
        let one = with(&["helper"]);
        assert!(has_tag(&one, CompilePolicyPartition::Artifact));
        assert!(has_tag(&one, CompilePolicyPartition::Full));
        assert!(!has_tag(&one, CompilePolicyPartition::Evidence));
        assert!(!has_tag(&one, CompilePolicyPartition::Invocation));
        assert_only_partition_changed(&base, &one, CompilePolicyPartition::Artifact);
        let mut seen = std::collections::HashSet::new();
        for names in [
            &["helper"][..],
            &["helper", "other"],
            &["ab", "c"],
            &["a", "bc"],
            &["abc"],
        ] {
            assert!(
                seen.insert(with(names).digest(CompilePolicyPartition::Artifact)),
                "{names:?}"
            );
        }
        assert_eq!(
            with(&["b", "a"]).digest(CompilePolicyPartition::Artifact),
            with(&["a", "b"]).digest(CompilePolicyPartition::Artifact)
        );
    }

    /// The x86-64 certificate-free allocation request is encoded only when on,
    /// only in the Artifact partition (it changes emitted bytes).
    #[test]
    fn x86_certificate_free_allocation_is_an_artifact_field_only_when_on() {
        let (target, compiler, jit) = baseline();
        let tag = TAG_COMPILER_X86_CERTIFICATE_FREE_ALLOCATION.to_be_bytes();
        let has_tag = |policy: &CompilePolicy, partition| {
            let bytes = policy.canonical_bytes(partition);
            let mut cursor = ENCODING_HEADER_BYTES;
            let mut found = false;
            while cursor < bytes.len() {
                let len = usize::from(u16::from_be_bytes([bytes[cursor + 2], bytes[cursor + 3]]));
                found |= bytes[cursor..cursor + 2] == tag;
                cursor += TLV_HEADER_BYTES + len;
            }
            found
        };
        let base = policy(target, &compiler, &jit);
        assert!(!has_tag(&base, CompilePolicyPartition::Full));
        let mut changed = compiler.clone();
        changed.x86_certificate_free_allocation = true;
        let on = policy(target, &changed, &jit);
        assert!(has_tag(&on, CompilePolicyPartition::Artifact));
        assert!(has_tag(&on, CompilePolicyPartition::Full));
        assert!(!has_tag(&on, CompilePolicyPartition::Evidence));
        assert!(!has_tag(&on, CompilePolicyPartition::Invocation));
        assert_only_partition_changed(&base, &on, CompilePolicyPartition::Artifact);
    }

    /// OD-216: the link-unit definition set is encoded only when non-empty,
    /// only in the Evidence partition (it withholds body-theorem credit and
    /// changes no emitted byte), and distinct sets are distinct identities.
    #[test]
    fn link_unit_definitions_is_an_evidence_field_only_when_non_empty() {
        let (target, compiler, jit) = baseline();
        let tag = TAG_COMPILER_LINK_UNIT_DEFINITIONS.to_be_bytes();
        let has_tag = |policy: &CompilePolicy, partition| {
            let bytes = policy.canonical_bytes(partition);
            let mut cursor = ENCODING_HEADER_BYTES;
            let mut found = false;
            while cursor < bytes.len() {
                let len = usize::from(u16::from_be_bytes([bytes[cursor + 2], bytes[cursor + 3]]));
                found |= bytes[cursor..cursor + 2] == tag;
                cursor += TLV_HEADER_BYTES + len;
            }
            found
        };
        let base = policy(target, &compiler, &jit);
        assert!(!has_tag(&base, CompilePolicyPartition::Full));
        let with = |names: &[&str]| {
            let mut changed = compiler.clone();
            changed.link_unit_definitions = names.iter().map(|name| (*name).to_owned()).collect();
            policy(target, &changed, &jit)
        };
        let one = with(&["__udivti3"]);
        assert!(has_tag(&one, CompilePolicyPartition::Evidence));
        assert!(has_tag(&one, CompilePolicyPartition::Full));
        assert!(!has_tag(&one, CompilePolicyPartition::Artifact));
        assert!(!has_tag(&one, CompilePolicyPartition::Invocation));
        assert_only_partition_changed(&base, &one, CompilePolicyPartition::Evidence);
        let mut seen = std::collections::HashSet::new();
        for names in [
            &["__udivti3"][..],
            &["__udivti3", "memcpy"],
            &["memcpy"],
            &["mem", "cpy"],
        ] {
            assert!(
                seen.insert(with(names).digest(CompilePolicyPartition::Evidence)),
                "{names:?}"
            );
        }
    }

    /// An explicit AArch64 ISA profile is encoded only when configured, only
    /// in the Artifact partition, and each profile is a distinct identity.
    #[test]
    fn explicit_aarch64_isa_profile_is_an_artifact_field_only_when_configured() {
        use crate::target::AArch64IsaProfile;
        let (x86_target, x86_compiler, jit) = baseline();
        let mut x86_explicit = x86_compiler.clone();
        x86_explicit.aarch64_isa_profile = Some(AArch64IsaProfile::FP16);
        assert!(matches!(
            CompilePolicy::new(x86_target, &x86_explicit, &jit),
            Err(CompilePolicyError::Aarch64IsaProfileOnNonAarch64Target { .. })
        ));
        let target = TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap();
        let mut compiler = x86_compiler;
        compiler.target = Target::Aarch64;
        let tag = TAG_COMPILER_AARCH64_ISA_PROFILE.to_be_bytes();
        let has_tag = |policy: &CompilePolicy, partition| {
            let bytes = policy.canonical_bytes(partition);
            let mut cursor = ENCODING_HEADER_BYTES;
            let mut found = false;
            while cursor < bytes.len() {
                let len = usize::from(u16::from_be_bytes([bytes[cursor + 2], bytes[cursor + 3]]));
                found |= bytes[cursor..cursor + 2] == tag;
                cursor += TLV_HEADER_BYTES + len;
            }
            found
        };
        let base = policy(target, &compiler, &jit);
        assert!(!has_tag(&base, CompilePolicyPartition::Full));
        let mut seen = std::collections::HashSet::new();
        for profile in [
            AArch64IsaProfile::BASELINE,
            AArch64IsaProfile::FP16,
            AArch64IsaProfile::LSE,
            AArch64IsaProfile::APPLE_ARM64,
        ] {
            let mut changed = compiler.clone();
            changed.aarch64_isa_profile = Some(profile);
            let changed_policy = policy(target, &changed, &jit);
            assert_only_partition_changed(&base, &changed_policy, CompilePolicyPartition::Artifact);
            assert!(has_tag(&changed_policy, CompilePolicyPartition::Artifact));
            assert!(!has_tag(&changed_policy, CompilePolicyPartition::Evidence));
            assert!(seen.insert(changed_policy.digest(CompilePolicyPartition::Artifact)));
        }
    }

    #[test]
    fn time_bounded_cegis_binds_parallel_schedule_to_artifact_projection() {
        let (target, mut parallel, jit) = baseline();
        parallel.cegis_superopt_budget_sec = Some(17);
        parallel.parallel = true;
        let mut serial = parallel.clone();
        serial.parallel = false;
        let parallel = policy(target, &parallel, &jit);
        let serial = policy(target, &serial, &jit);

        assert_ne!(parallel.digests().artifact, serial.digests().artifact);
        assert_eq!(parallel.digests().evidence, serial.digests().evidence);
        assert_ne!(parallel.digests().invocation, serial.digests().invocation);
        assert_ne!(parallel.digests().full, serial.digests().full);
    }

    #[test]
    fn forced_aarch64_frame_pointers_partition_objects_and_refuse_other_targets() {
        let (x86_target, mut compiler, jit) = baseline();
        compiler.aarch64_force_frame_pointers = true;
        assert!(matches!(
            CompilePolicy::new(x86_target, &compiler, &jit),
            Err(CompilePolicyError::Aarch64FramePointersOnNonAarch64Target { .. })
        ));
        let target = TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap();
        compiler.target = Target::Aarch64;
        let forced = policy(target, &compiler, &jit);
        compiler.aarch64_force_frame_pointers = false;
        let default = policy(target, &compiler, &jit);
        assert_only_partition_changed(&default, &forced, CompilePolicyPartition::Artifact);
    }

    #[test]
    fn every_jit_config_field_has_an_explicit_partition() {
        let (target, compiler, jit) = baseline();
        let base = policy(target, &compiler, &jit);

        let mut changed = jit.clone();
        changed.opt_level = OptLevel::O1;
        assert_only_partition_changed(
            &base,
            &policy(target, &compiler, &changed),
            CompilePolicyPartition::Artifact,
        );

        let mut changed = jit.clone();
        changed.verify = false;
        assert_only_partition_changed(
            &base,
            &policy(target, &compiler, &changed),
            CompilePolicyPartition::Evidence,
        );

        let mut changed = jit.clone();
        changed.verify_dispatch = DispatchVerifyMode::Sampled {
            modulus: NonZeroU32::new(7).unwrap(),
        };
        assert_only_partition_changed(
            &base,
            &policy(target, &compiler, &changed),
            CompilePolicyPartition::Artifact,
        );

        let mut changed = jit.clone();
        changed.profile_hooks = ProfileHookMode::BlockCounts;
        assert_only_partition_changed(
            &base,
            &policy(target, &compiler, &changed),
            CompilePolicyPartition::Artifact,
        );

        let mut changed = jit.clone();
        changed.emit_entry_counters = true;
        assert_only_partition_changed(
            &base,
            &policy(target, &compiler, &changed),
            CompilePolicyPartition::Artifact,
        );

        let mut changed = jit.clone();
        changed.external_symbol_resolution = JitExternalSymbolResolutionPolicy::ExplicitOnly;
        assert_only_partition_changed(
            &base,
            &policy(target, &compiler, &changed),
            CompilePolicyPartition::Artifact,
        );

        let mut changed = jit;
        changed.cache_certificates = false;
        assert_only_partition_changed(
            &base,
            &policy(target, &compiler, &changed),
            CompilePolicyPartition::Evidence,
        );
    }

    #[test]
    fn entry_counter_alias_normalizes_to_effective_profile_hook() {
        let (target, compiler, mut alias) = baseline();
        alias.emit_entry_counters = true;
        let mut explicit = alias.clone();
        explicit.emit_entry_counters = false;
        explicit.profile_hooks = ProfileHookMode::CallCounts;
        assert_eq!(
            policy(target, &compiler, &alias),
            policy(target, &compiler, &explicit)
        );

        let mut overridden_false = explicit.clone();
        overridden_false.emit_entry_counters = true;
        overridden_false.profile_hooks = ProfileHookMode::BlockCounts;
        let mut overridden_true = overridden_false.clone();
        overridden_true.emit_entry_counters = false;
        assert_eq!(
            policy(target, &compiler, &overridden_false),
            policy(target, &compiler, &overridden_true),
            "an explicit non-None profile mode must win over the alias"
        );
    }

    #[test]
    fn raw_validation_override_presence_is_evidence() {
        let (target, mut derived, jit) = baseline();
        derived.jit_validation_mode_override = None;
        derived.emit_proofs = false;
        let mut explicit = derived.clone();
        explicit.jit_validation_mode_override = Some(derived.jit_validation_mode());
        let derived = policy(target, &derived, &jit);
        let explicit = policy(target, &explicit, &jit);

        assert_eq!(derived.digests().artifact, explicit.digests().artifact);
        assert_eq!(derived.digests().invocation, explicit.digests().invocation);
        assert_ne!(
            derived.digests().evidence,
            explicit.digests().evidence,
            "legacy ambient validation resolution treats override presence as semantic"
        );
        assert_ne!(derived.digests().full, explicit.digests().full);
    }

    #[test]
    fn target_alias_normalizes_to_explicit_effective_abi() {
        let (_, mut compiler, jit) = baseline();
        compiler.target = Target::X86_64;
        let alias = TargetSpec::unknown_for_architecture(Target::X86_64);
        let explicit = TargetSpec::default_for_architecture(Target::X86_64);
        let alias_policy = policy(alias, &compiler, &jit);
        let explicit_policy = policy(explicit, &compiler, &jit);
        assert_eq!(alias_policy, explicit_policy);
        assert!(alias_policy.target_spec().has_explicit_os_abi());
    }

    #[test]
    fn target_abi_components_partition_artifacts() {
        let (_, compiler, jit) = baseline();
        let darwin = TargetSpec::new(
            Target::X86_64,
            TargetVendor::Apple,
            TargetOperatingSystem::Darwin,
            TargetEnvironment::Unknown,
        );
        let windows = TargetSpec::new(
            Target::X86_64,
            TargetVendor::Pc,
            TargetOperatingSystem::Windows,
            TargetEnvironment::Msvc,
        );
        let linux = policy(linux_x86_64(), &compiler, &jit);
        let darwin = policy(darwin, &compiler, &jit);
        let windows = policy(windows, &compiler, &jit);
        assert_ne!(linux.digests().artifact, darwin.digests().artifact);
        assert_ne!(linux.digests().artifact, windows.digests().artifact);
        assert_ne!(darwin.digests().artifact, windows.digests().artifact);
        assert_eq!(linux.digests().evidence, darwin.digests().evidence);
        assert_eq!(linux.digests().invocation, darwin.digests().invocation);
    }

    #[test]
    fn target_architecture_mismatch_fails_closed() {
        let (_, compiler, jit) = baseline();
        let err = CompilePolicy::new(
            TargetSpec::unknown_for_architecture(Target::Aarch64),
            &compiler,
            &jit,
        )
        .unwrap_err();
        assert_eq!(
            err,
            CompilePolicyError::TargetArchitectureMismatch {
                policy_target: Target::Aarch64,
                compiler_target: Target::X86_64,
            }
        );
        assert_eq!(
            CompilePolicy::from_compiler(
                TargetSpec::unknown_for_architecture(Target::Aarch64),
                &compiler,
            )
            .unwrap_err(),
            CompilePolicyError::TargetArchitectureMismatch {
                policy_target: Target::Aarch64,
                compiler_target: Target::X86_64,
            }
        );
    }

    #[test]
    fn canonical_encoding_is_versioned_bounded_tlv() {
        let (target, compiler, jit) = baseline();
        let policies = [
            CompilePolicy::from_compiler(target, &compiler).unwrap(),
            CompilePolicy::from_jit(target, &jit).unwrap(),
            policy(target, &compiler, &jit),
        ];
        for policy in &policies {
            for partition in [
                CompilePolicyPartition::Artifact,
                CompilePolicyPartition::Evidence,
                CompilePolicyPartition::Invocation,
                CompilePolicyPartition::Full,
            ] {
                let bytes = policy.canonical_bytes(partition);
                assert!(bytes.len() <= MAX_COMPILE_POLICY_ENCODING_BYTES);
                assert_eq!(&bytes[..8], ENCODING_MAGIC);
                assert_eq!(
                    u16::from_be_bytes([bytes[8], bytes[9]]),
                    COMPILE_POLICY_SCHEMA_VERSION
                );
                assert_eq!(bytes[10], partition.encoding_tag());
                assert_eq!(bytes[11], policy.scope().encoding_tag());

                let mut cursor = ENCODING_HEADER_BYTES;
                let mut previous_tag = None;
                while cursor < bytes.len() {
                    let tag = u16::from_be_bytes([bytes[cursor], bytes[cursor + 1]]);
                    let len =
                        usize::from(u16::from_be_bytes([bytes[cursor + 2], bytes[cursor + 3]]));
                    assert!(previous_tag.is_none_or(|previous| previous < tag));
                    previous_tag = Some(tag);
                    cursor += TLV_HEADER_BYTES + len;
                    assert!(cursor <= bytes.len());
                }
                assert_eq!(cursor, bytes.len());
            }
        }
    }

    #[test]
    fn deterministic_full_policy_golden() {
        let (target, compiler, jit) = baseline();
        assert_eq!(
            CompilePolicy::from_compiler(target, &compiler)
                .unwrap()
                .digests()
                .full
                .to_prefixed_hex(),
            "sha256:2b7d23166f275ce82e22015a6b74f1a1465a8eec2a5309d91a08410b74d354bf"
        );
        assert_eq!(
            CompilePolicy::from_jit(target, &jit)
                .unwrap()
                .digests()
                .full
                .to_prefixed_hex(),
            "sha256:a962352e68035483b92ffbac605f17af714e173905a3007f6319448fa983d0d0"
        );
        assert_eq!(
            policy(target, &compiler, &jit)
                .digests()
                .full
                .to_prefixed_hex(),
            "sha256:af7e84536c887fa25188b86ec80e2fa15bc2dc09c1e88dc85dfae2a918264643"
        );
    }
}
