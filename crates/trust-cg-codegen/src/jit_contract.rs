// trust-cg-codegen/jit_contract.rs - Shared JIT artifact contract
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Shared artifact contract types for product-grade JIT consumers.
//!
//! This module is intentionally data-only. It gives downstream users such as
//! TY and ay a common surface for describing target facts, ABI facts, memory
//! layout, invalidation scope, proof policy, typed apply/deopt results, and
//! deterministic artifact manifests. Runtime symbol installation remains owned
//! by the existing JIT and compile-service APIs.

use std::collections::BTreeMap;
use std::fmt;
use std::marker::PhantomData;
use std::ptr::NonNull;

use thiserror::Error;
use trust_cg_opt::cache::StableHasher;

use crate::jit_diagnostics::sha256_hex;
use crate::target::{Target, TargetSpec};

/// Stable schema name for [`DeterministicArtifactManifest`].
pub const JIT_ARTIFACT_MANIFEST_SCHEMA: &str = "trust-cg.artifact/v1";

/// Current schema version for [`DeterministicArtifactManifest`].
pub const JIT_ARTIFACT_MANIFEST_SCHEMA_VERSION: u32 = 1;

/// Stable schema name for [`ProofEvidenceSummary`].
pub const JIT_PROOF_EVIDENCE_SUMMARY_SCHEMA: &str = "trust-cg.proof_evidence_summary/v1";

/// Current schema version for [`ProofEvidenceSummary`].
pub const JIT_PROOF_EVIDENCE_SUMMARY_SCHEMA_VERSION: u32 = 1;

/// Stable schema name for the proof-evidence honesty channel carried inside
/// [`ProofEvidenceSummary`] (`strength` + `accepted_assumptions`).
///
/// The channel is a strictly additive tail on the v1 summary: a summary that
/// leaves both fields at their defaults ([`EvidenceStrength::NotReported`] and
/// no assumptions) encodes byte-for-byte identically to the pre-channel v1
/// encoding, so no existing artifact checksum moves.
pub const JIT_PROOF_EVIDENCE_CHANNEL_SCHEMA: &str = "trust-cg.proof_evidence_channel/v1";

/// Current schema version for the proof-evidence honesty channel.
pub const JIT_PROOF_EVIDENCE_CHANNEL_SCHEMA_VERSION: u32 = 1;

/// Stable schema name for [`KernelArtifactContract`].
pub const KERNEL_ARTIFACT_CONTRACT_SCHEMA: &str = "trust-cg.kernel_artifact_contract/v1";

/// Current schema version for [`KernelArtifactContract`].
pub const KERNEL_ARTIFACT_CONTRACT_SCHEMA_VERSION: u32 = 1;

const TY_NATIVE_FUSED_PARENT_LOOP_MANIFEST_SCHEMA: &str =
    "trust-cg.ty.native_fused_parent_loop_manifest/v1";
const TY_NATIVE_FUSED_PROOF_FACT_VERIFIED: &str = "verified";
const TY_NATIVE_FUSED_REQUIRED_FACT_PREFIX: &str = "required_fact.";

/// trust_ir-owned hardware vector contract manifest schema carried by Trust Codegen
/// artifacts when native product evidence depends on canonical vector rows.
pub const TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA: &str =
    trust_ir::HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA;

/// trust_ir-owned hardware vector contract manifest schema version.
pub const TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA_VERSION: u32 =
    trust_ir::HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA_VERSION;

/// Canonical trust_ir hardware vector contract set currently carried by Trust Codegen.
pub const TRUST_IR_HARDWARE_VECTOR_CONTRACT_SET_NAME: &str =
    trust_ir::CHC_X86_HARDWARE_VECTOR_CONTRACT_SET_NAME;

/// Canonical target family for the carried trust_ir hardware vector contract set.
pub const TRUST_IR_HARDWARE_VECTOR_CONTRACT_TARGET_FAMILY: &str =
    trust_ir::CHC_X86_HARDWARE_VECTOR_CONTRACT_TARGET_FAMILY;

/// Manifest metadata key for the trust_ir hardware vector contract manifest schema.
pub const TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA_KEY: &str =
    "trust_ir.hardware_vector_contract.manifest_schema";

/// Manifest metadata key for the trust_ir hardware vector contract manifest schema version.
pub const TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA_VERSION_KEY: &str =
    "trust_ir.hardware_vector_contract.manifest_schema_version";

/// Manifest metadata key for the trust_ir hardware vector contract set name.
pub const TRUST_IR_HARDWARE_VECTOR_CONTRACT_SET_NAME_KEY: &str =
    "trust_ir.hardware_vector_contract.set_name";

/// Manifest metadata key for the trust_ir hardware vector contract target family.
pub const TRUST_IR_HARDWARE_VECTOR_CONTRACT_TARGET_FAMILY_KEY: &str =
    "trust_ir.hardware_vector_contract.target_family";

/// Manifest metadata key for the trust_ir hardware vector contract row count.
pub const TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_ROW_COUNT_KEY: &str =
    "trust_ir.hardware_vector_contract.manifest_row_count";

/// Manifest metadata key for the trust_ir hardware vector contract row digest.
pub const TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SHA256_KEY: &str =
    "trust_ir.hardware_vector_contract.manifest_sha256";

/// Stable schema tag for host-JIT target-feature profile metadata.
pub const HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA: &str =
    "trust-cg.host_jit.target_feature_profile.v1";

/// Stable numeric version for host-JIT target-feature profile metadata.
pub const HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA_VERSION: u32 = 1;

/// Stable metadata key prefix for host-JIT target-feature profile entries.
pub const HOST_JIT_TARGET_FEATURE_PROFILE_METADATA_PREFIX: &str =
    "trust-cg.host_jit.target_feature_profile.";

/// Manifest metadata key for the host-JIT target-feature profile schema.
pub const HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA_KEY: &str =
    "trust-cg.host_jit.target_feature_profile.schema";

/// Manifest metadata key for the host-JIT target-feature profile schema version.
pub const HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA_VERSION_KEY: &str =
    "trust-cg.host_jit.target_feature_profile.schema_version";

/// Manifest metadata key for the host-JIT target triple covered by the profile.
pub const HOST_JIT_TARGET_FEATURE_PROFILE_TARGET_TRIPLE_KEY: &str =
    "trust-cg.host_jit.target_feature_profile.target_triple";

/// Manifest metadata key for the normalized target-feature set.
pub const HOST_JIT_TARGET_FEATURE_PROFILE_TARGET_FEATURES_KEY: &str =
    "trust-cg.host_jit.target_feature_profile.target_features";

/// Manifest metadata key for the active target-feature policy.
pub const HOST_JIT_TARGET_FEATURE_PROFILE_CURRENT_POLICY_KEY: &str =
    "trust-cg.host_jit.target_feature_profile.current_policy";

/// Manifest metadata key for detected host feature bits.
pub const HOST_JIT_TARGET_FEATURE_PROFILE_DETECTED_HOST_FEATURES_KEY: &str =
    "trust-cg.host_jit.target_feature_profile.detected_host_features";

/// Manifest metadata key for the stable profile SHA-256 digest.
pub const HOST_JIT_TARGET_FEATURE_PROFILE_SHA256_KEY: &str =
    "trust-cg.host_jit.target_feature_profile.sha256";

/// Stable 128-bit checksum used by the artifact contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ArtifactChecksum(u128);

impl ArtifactChecksum {
    /// Create a checksum from its raw 128-bit value.
    pub const fn new(value: u128) -> Self {
        Self(value)
    }

    /// Return the raw 128-bit checksum value.
    pub const fn get(self) -> u128 {
        self.0
    }

    /// Hash canonical bytes into an artifact checksum.
    pub fn for_bytes(bytes: &[u8]) -> Self {
        let mut hasher = StableHasher::new();
        hasher.write_str("trust-cg.jit_contract.checksum.v1");
        hasher.write_framed(bytes);
        Self(hasher.finish128())
    }
}

impl fmt::Display for ArtifactChecksum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "trust-cg-stable128:{:032x}", self.0)
    }
}

/// Target CPU architecture.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TargetArchitecture {
    /// AArch64 / ARM64.
    Aarch64,
    /// x86-64 / AMD64.
    X86_64,
    /// RISC-V 64-bit.
    Riscv64,
    /// Downstream-defined architecture string.
    Other(String),
}

impl TargetArchitecture {
    fn as_str(&self) -> &str {
        match self {
            Self::Aarch64 => "aarch64",
            Self::X86_64 => "x86_64",
            Self::Riscv64 => "riscv64",
            Self::Other(value) => value,
        }
    }
}

/// Target operating system.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TargetOperatingSystem {
    /// Darwin / macOS.
    Macos,
    /// Linux.
    Linux,
    /// Microsoft Windows.
    Windows,
    /// Unknown or intentionally unspecified OS.
    Unknown,
    /// Downstream-defined OS string.
    Other(String),
}

impl TargetOperatingSystem {
    fn as_str(&self) -> &str {
        match self {
            Self::Macos => "macos",
            Self::Linux => "linux",
            Self::Windows => "windows",
            Self::Unknown => "unknown",
            Self::Other(value) => value,
        }
    }

    /// Operating system for in-process host JIT artifacts.
    pub fn host() -> Self {
        if cfg!(target_os = "macos") {
            Self::Macos
        } else if cfg!(target_os = "linux") {
            Self::Linux
        } else if cfg!(target_os = "windows") {
            Self::Windows
        } else {
            Self::Unknown
        }
    }
}

/// Byte order for generated code and data layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Endianness {
    /// Little-endian layout.
    Little,
    /// Big-endian layout.
    Big,
}

impl Endianness {
    fn as_str(self) -> &'static str {
        match self {
            Self::Little => "little",
            Self::Big => "big",
        }
    }
}

/// Product-contract target facts.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TargetDescriptor {
    /// Canonical target triple or downstream target key.
    pub triple: String,
    /// CPU architecture.
    pub architecture: TargetArchitecture,
    /// Operating system.
    pub operating_system: TargetOperatingSystem,
    /// Pointer width in bits.
    pub pointer_width_bits: u16,
    /// Target byte order.
    pub endianness: Endianness,
    /// Optional CPU model.
    pub cpu: Option<String>,
    /// Target feature names. Treated as an unordered set by checksum logic.
    pub features: Vec<String>,
}

impl TargetDescriptor {
    /// Create a target descriptor and normalize feature order.
    pub fn new(
        triple: impl Into<String>,
        architecture: TargetArchitecture,
        operating_system: TargetOperatingSystem,
        pointer_width_bits: u16,
        endianness: Endianness,
    ) -> Self {
        Self {
            triple: triple.into(),
            architecture,
            operating_system,
            pointer_width_bits,
            endianness,
            cpu: None,
            features: Vec::new(),
        }
    }

    /// Create a descriptor from Trust Codegen's built-in target enum.
    pub fn for_trust_cg_target(target: Target, operating_system: TargetOperatingSystem) -> Self {
        let architecture = match target {
            Target::Aarch64 => TargetArchitecture::Aarch64,
            Target::X86_64 => TargetArchitecture::X86_64,
            Target::Riscv64 => TargetArchitecture::Riscv64,
        };
        let os = operating_system.as_str();
        Self::new(
            format!("{}-unknown-{os}", target.name()),
            architecture,
            operating_system,
            (target.pointer_bytes() * 8) as u16,
            Endianness::Little,
        )
    }

    /// Create a descriptor from the exact target specification used by the
    /// compiler.
    ///
    /// Unlike [`Self::for_trust_cg_target`], this preserves the canonical
    /// vendor/OS spelling in [`TargetSpec::triple`] (for example
    /// `aarch64-apple-darwin`). Compile/install authority should use this
    /// constructor so a lossy synthetic triple cannot drift from codegen.
    pub fn for_trust_cg_target_spec(target_spec: TargetSpec) -> Self {
        let operating_system = match target_spec.operating_system {
            crate::target::TargetOperatingSystem::Darwin => TargetOperatingSystem::Macos,
            crate::target::TargetOperatingSystem::Linux => TargetOperatingSystem::Linux,
            crate::target::TargetOperatingSystem::Windows => TargetOperatingSystem::Windows,
            crate::target::TargetOperatingSystem::Unknown => TargetOperatingSystem::Unknown,
        };
        let mut descriptor = Self::for_trust_cg_target(target_spec.architecture, operating_system);
        descriptor.triple = target_spec.triple();
        descriptor
    }

    /// Set the optional CPU model.
    pub fn with_cpu(mut self, cpu: impl Into<String>) -> Self {
        self.cpu = Some(cpu.into());
        self
    }

    /// Set target features. Feature order is normalized for deterministic
    /// checksums and manifests.
    pub fn with_features(mut self, features: impl IntoIterator<Item = impl Into<String>>) -> Self {
        self.features = normalize_string_set(features);
        self
    }

    /// Deterministic checksum for this descriptor.
    pub fn checksum(&self) -> ArtifactChecksum {
        checksum_of(self)
    }

    /// Canonical descriptor bytes for crate-internal cryptographic bindings.
    ///
    /// Product seals must bind these bytes rather than treating the shorter
    /// public [`ArtifactChecksum`] as collision-resistant authority.
    pub(crate) fn canonical_bytes(&self) -> Vec<u8> {
        canonical_bytes_of(self)
    }
}

/// Executable-memory ownership model promised by a JIT artifact.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExecutableMemoryOwner {
    /// Trust Codegen owns executable memory and teardown.
    TrustCg,
    /// The named downstream runtime owns executable memory.
    Downstream(String),
    /// Ownership is intentionally not represented in this Phase-1 contract.
    Unspecified,
}

/// Executable artifact teardown policy.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TeardownPolicy {
    /// The artifact is process-lifetime.
    ProcessLifetime,
    /// The owner may release the artifact when no handles remain.
    RefCounted,
    /// The named downstream policy applies.
    Downstream(String),
    /// Teardown is intentionally unspecified.
    Unspecified,
}

/// Varargs behavior for an ABI descriptor.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AbiVarargsPolicy {
    /// The artifact ABI does not support varargs entrypoints.
    Unsupported,
    /// C ABI varargs rules apply.
    C,
    /// Downstream-defined varargs policy.
    Other(String),
}

/// Product-contract ABI facts for callable JIT symbols.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AbiDescriptor {
    /// Stable ABI descriptor name.
    pub name: String,
    /// Calling convention name, such as `sysv_amd64` or `aapcs64`.
    pub calling_convention: String,
    /// Pointer width in bits.
    pub pointer_width_bits: u16,
    /// Required stack alignment in bytes.
    pub stack_alignment_bytes: u16,
    /// Red-zone size in bytes.
    pub red_zone_bytes: u16,
    /// Shadow/home-space size in bytes.
    pub shadow_space_bytes: u16,
    /// Integer/pointer argument registers in ABI order.
    pub integer_argument_registers: Vec<String>,
    /// Floating-point argument registers in ABI order.
    pub float_argument_registers: Vec<String>,
    /// Integer/pointer return registers in ABI order.
    pub integer_return_registers: Vec<String>,
    /// Floating-point return registers in ABI order.
    pub float_return_registers: Vec<String>,
    /// Callee-saved registers.
    pub callee_saved_registers: Vec<String>,
    /// Executable-memory ownership.
    pub executable_memory_owner: ExecutableMemoryOwner,
    /// Executable-memory teardown policy.
    pub teardown_policy: TeardownPolicy,
    /// Varargs policy.
    pub varargs: AbiVarargsPolicy,
}

impl AbiDescriptor {
    /// Create an ABI descriptor from Trust Codegen's target enum.
    pub fn for_trust_cg_target(target: Target) -> Self {
        let calling_convention = target.calling_convention();
        let (
            integer_argument_registers,
            float_argument_registers,
            integer_return_registers,
            float_return_registers,
            callee_saved_registers,
        ) = match target {
            Target::Aarch64 => (
                strings(["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"]),
                strings(["v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7"]),
                strings(["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"]),
                strings(["v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7"]),
                strings([
                    "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28",
                ]),
            ),
            Target::X86_64 => (
                strings(["rdi", "rsi", "rdx", "rcx", "r8", "r9"]),
                strings([
                    "xmm0", "xmm1", "xmm2", "xmm3", "xmm4", "xmm5", "xmm6", "xmm7",
                ]),
                strings(["rax", "rdx"]),
                strings(["xmm0", "xmm1"]),
                strings(["rbx", "rbp", "r12", "r13", "r14", "r15"]),
            ),
            Target::Riscv64 => (
                strings(["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]),
                strings(["fa0", "fa1", "fa2", "fa3", "fa4", "fa5", "fa6", "fa7"]),
                strings(["a0", "a1"]),
                strings(["fa0", "fa1"]),
                strings([
                    "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11",
                ]),
            ),
        };

        Self {
            name: format!("trust-cg-{}", target.name()),
            calling_convention: calling_convention.name.to_owned(),
            pointer_width_bits: (target.pointer_bytes() * 8) as u16,
            stack_alignment_bytes: target.stack_alignment() as u16,
            red_zone_bytes: calling_convention.red_zone_size as u16,
            shadow_space_bytes: calling_convention.shadow_space as u16,
            integer_argument_registers,
            float_argument_registers,
            integer_return_registers,
            float_return_registers,
            callee_saved_registers,
            executable_memory_owner: ExecutableMemoryOwner::TrustCg,
            teardown_policy: TeardownPolicy::RefCounted,
            varargs: AbiVarargsPolicy::Unsupported,
        }
    }

    /// Create an ABI descriptor from Trust Codegen's target enum and target OS.
    ///
    /// `Target::X86_64` is OS-sensitive: Unix hosts use System V AMD64,
    /// while 64-bit Windows uses the Microsoft x64 ABI.
    pub fn for_trust_cg_target_os(target: Target, operating_system: TargetOperatingSystem) -> Self {
        if target != Target::X86_64 || operating_system != TargetOperatingSystem::Windows {
            return Self::for_trust_cg_target(target);
        }

        Self {
            name: "trust-cg-x86_64-windows".to_owned(),
            calling_convention: "windows_x64".to_owned(),
            pointer_width_bits: (Target::X86_64.pointer_bytes() * 8) as u16,
            stack_alignment_bytes: Target::X86_64.stack_alignment() as u16,
            red_zone_bytes: 0,
            shadow_space_bytes: 32,
            integer_argument_registers: strings(["rcx", "rdx", "r8", "r9"]),
            float_argument_registers: strings(["xmm0", "xmm1", "xmm2", "xmm3"]),
            integer_return_registers: strings(["rax", "rdx"]),
            float_return_registers: strings(["xmm0", "xmm1"]),
            callee_saved_registers: strings([
                "rbx", "rbp", "rdi", "rsi", "r12", "r13", "r14", "r15", "xmm6", "xmm7", "xmm8",
                "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15",
            ]),
            executable_memory_owner: ExecutableMemoryOwner::TrustCg,
            teardown_policy: TeardownPolicy::RefCounted,
            varargs: AbiVarargsPolicy::Unsupported,
        }
    }

    /// Deterministic checksum for this descriptor.
    pub fn checksum(&self) -> ArtifactChecksum {
        checksum_of(self)
    }

    /// Canonical descriptor bytes for crate-internal cryptographic bindings.
    pub(crate) fn canonical_bytes(&self) -> Vec<u8> {
        canonical_bytes_of(self)
    }
}

/// Integer, pointer, float, and aggregate ABI value kinds.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AbiValueKind {
    /// Boolean value.
    I1,
    /// Signed or sign-agnostic 8-bit integer.
    I8,
    /// Signed or sign-agnostic 16-bit integer.
    I16,
    /// Signed or sign-agnostic 32-bit integer.
    I32,
    /// Signed or sign-agnostic 64-bit integer.
    I64,
    /// Native pointer-sized integer.
    USize,
    /// 32-bit floating-point value.
    F32,
    /// 64-bit floating-point value.
    F64,
    /// Native pointer.
    Ptr,
    /// Fixed-size byte aggregate.
    Bytes {
        /// Size in bytes.
        size_bytes: u32,
        /// Alignment in bytes.
        alignment_bytes: u32,
    },
    /// Void marker for no value.
    Void,
    /// Downstream-defined ABI value kind.
    Other(String),
}

/// One ABI value in a symbol signature.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AbiValue {
    /// Value kind.
    pub kind: AbiValueKind,
    /// Whether null is a valid value. Relevant for pointers.
    pub nullable: bool,
}

impl AbiValue {
    /// Create a non-nullable ABI value.
    pub const fn new(kind: AbiValueKind) -> Self {
        Self {
            kind,
            nullable: false,
        }
    }

    /// Mark the value as nullable.
    pub const fn nullable(mut self) -> Self {
        self.nullable = true;
        self
    }
}

/// Canonical callable-symbol signature.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SymbolSignature {
    /// ABI or calling convention this signature expects.
    pub abi: String,
    /// Positional parameter values.
    pub params: Vec<AbiValue>,
    /// Positional return values.
    pub returns: Vec<AbiValue>,
    /// Whether the function is variadic.
    pub variadic: bool,
}

impl SymbolSignature {
    /// Create a non-variadic `extern "C"` signature.
    pub fn extern_c(params: Vec<AbiValue>, returns: Vec<AbiValue>) -> Self {
        Self {
            abi: "extern_c".to_owned(),
            params,
            returns,
            variadic: false,
        }
    }

    /// Deterministic checksum for this signature.
    pub fn checksum(&self) -> ArtifactChecksum {
        checksum_of(self)
    }

    /// Canonical signature bytes for crate-internal cryptographic bindings.
    pub(crate) fn canonical_bytes(&self) -> Vec<u8> {
        canonical_bytes_of(self)
    }
}

/// Concrete field layout inside a record.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FieldLayout {
    /// Field name.
    pub name: String,
    /// Byte offset from the start of the record.
    pub offset_bytes: u64,
    /// Field size in bytes.
    pub size_bytes: u64,
    /// Field alignment in bytes.
    pub alignment_bytes: u32,
}

/// Concrete record layout.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecordLayout {
    /// Record or wrapper type name.
    pub name: String,
    /// Representation name, such as `repr(C)`.
    pub representation: String,
    /// Record size in bytes.
    pub size_bytes: u64,
    /// Record alignment in bytes.
    pub alignment_bytes: u32,
    /// Field layouts.
    pub fields: Vec<FieldLayout>,
}

/// Pointer bounds known to a generated wrapper.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PointerBounds {
    /// No statically known bound.
    Unbounded,
    /// A byte range relative to the downstream-owned object.
    ByteRange {
        /// Start offset in bytes.
        start_bytes: u64,
        /// Length in bytes.
        length_bytes: u64,
    },
    /// Bounds are tied to a named symbol.
    Symbol(String),
}

/// Mutability promised by a wrapper field, pointer, or slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Mutability {
    /// Read-only access.
    Immutable,
    /// Mutable access.
    Mutable,
}

/// Alias policy promised by a wrapper field, pointer, or slice.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AliasPolicy {
    /// No aliasing writes are allowed.
    Exclusive,
    /// Shared read-only aliases are allowed.
    SharedReadOnly,
    /// Shared mutable aliases are possible and must be handled by guards.
    SharedMutable,
    /// Alias behavior is unknown.
    Unknown,
    /// Downstream-defined alias policy.
    Other(String),
}

/// Slice layout used by generated native wrappers.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SliceLayout {
    /// Slice or field name.
    pub name: String,
    /// Element size in bytes.
    pub element_size_bytes: u64,
    /// Element alignment in bytes.
    pub element_alignment_bytes: u32,
    /// Stride in bytes between adjacent elements.
    pub stride_bytes: u64,
    /// Optional fixed length.
    pub length: Option<u64>,
    /// Pointer bounds.
    pub bounds: PointerBounds,
    /// Mutability.
    pub mutability: Mutability,
    /// Alias policy.
    pub alias_policy: AliasPolicy,
}

/// Pointer layout used by generated native wrappers.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PointerLayout {
    /// Pointer or field name.
    pub name: String,
    /// Pointer bounds.
    pub bounds: PointerBounds,
    /// Mutability.
    pub mutability: Mutability,
    /// Alias policy.
    pub alias_policy: AliasPolicy,
}

/// Symbol layout record inside an artifact.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SymbolLayout {
    /// Symbol name.
    pub name: String,
    /// Section name.
    pub section: String,
    /// Optional byte offset in the section or executable allocation.
    pub offset_bytes: Option<u64>,
    /// Symbol size in bytes.
    pub size_bytes: u64,
    /// Symbol alignment in bytes.
    pub alignment_bytes: u32,
}

/// Product-contract layout manifest.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LayoutManifest {
    /// Pointer size in bytes.
    pub pointer_size_bytes: u8,
    /// Pointer alignment in bytes.
    pub pointer_alignment_bytes: u8,
    /// Target byte order.
    pub endianness: Endianness,
    /// Stack alignment in bytes.
    pub stack_alignment_bytes: u16,
    /// Record layouts.
    pub records: Vec<RecordLayout>,
    /// Slice layouts.
    pub slices: Vec<SliceLayout>,
    /// Pointer layouts.
    pub pointers: Vec<PointerLayout>,
    /// Symbol layouts.
    pub symbols: Vec<SymbolLayout>,
    /// Optional generated Rust wrapper identity.
    pub wrapper_identity: Option<String>,
    /// Downstream extension metadata. Keys are deterministic.
    pub metadata: BTreeMap<String, String>,
}

impl LayoutManifest {
    /// Create an LP64 layout manifest for a target.
    pub fn lp64(endianness: Endianness, stack_alignment_bytes: u16) -> Self {
        Self {
            pointer_size_bytes: 8,
            pointer_alignment_bytes: 8,
            endianness,
            stack_alignment_bytes,
            records: Vec::new(),
            slices: Vec::new(),
            pointers: Vec::new(),
            symbols: Vec::new(),
            wrapper_identity: None,
            metadata: BTreeMap::new(),
        }
    }

    /// Deterministic checksum for this layout manifest.
    pub fn checksum(&self) -> ArtifactChecksum {
        checksum_of(self)
    }

    /// Canonical layout bytes for crate-internal cryptographic bindings.
    pub(crate) fn canonical_bytes(&self) -> Vec<u8> {
        canonical_bytes_of(self)
    }
}

/// Artifact invalidation scope.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InvalidationKey {
    /// Source or binding fingerprint owned by the downstream caller.
    pub source_fingerprint: String,
    /// Compiler or profile fingerprint.
    pub compiler_fingerprint: String,
    /// Target descriptor checksum used by the caller.
    pub target_checksum: ArtifactChecksum,
    /// ABI descriptor checksum used by the caller.
    pub abi_checksum: ArtifactChecksum,
    /// Layout manifest checksum used by the caller.
    pub layout_checksum: ArtifactChecksum,
    /// Proof policy checksum used by the caller.
    pub proof_policy_checksum: ArtifactChecksum,
    /// Downstream generation or epoch.
    pub generation: u64,
    /// Additional deterministic invalidation dimensions.
    pub extra: BTreeMap<String, String>,
}

impl InvalidationKey {
    /// Create an invalidation key from the core contract checksums.
    pub fn new(
        source_fingerprint: impl Into<String>,
        compiler_fingerprint: impl Into<String>,
        target_checksum: ArtifactChecksum,
        abi_checksum: ArtifactChecksum,
        layout_checksum: ArtifactChecksum,
        proof_policy_checksum: ArtifactChecksum,
        generation: u64,
    ) -> Self {
        Self {
            source_fingerprint: source_fingerprint.into(),
            compiler_fingerprint: compiler_fingerprint.into(),
            target_checksum,
            abi_checksum,
            layout_checksum,
            proof_policy_checksum,
            generation,
            extra: BTreeMap::new(),
        }
    }

    /// Deterministic checksum for this invalidation key.
    pub fn checksum(&self) -> ArtifactChecksum {
        checksum_of(self)
    }
}

/// How an obligation covered by a [`ProofEvidenceSummary`] was actually
/// discharged.
///
/// This is the *reported* strength, never a claim: a summary whose verdict is
/// [`ProofEvidenceVerdict::MissingEvidence`] carries
/// [`EvidenceStrength::NotRun`], and a summary produced on a route that does
/// not know its own strength carries [`EvidenceStrength::NotReported`]. The
/// distinction between "nothing ran", "ran statistically", and "ran under a
/// solver" is the whole point of the type — a consumer must never have to
/// infer it from an absent field.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum EvidenceStrength {
    /// The producing route did not report a strength.
    ///
    /// This is the encoding-compatible default. It is *not* a claim that
    /// something ran: it means the field carries no information. Routes that
    /// know nothing ran must use [`Self::NotRun`] instead.
    #[default]
    NotReported,
    /// No proof, translation validation, or verifier ran on this route.
    NotRun,
    /// Every input in the obligation's input space was enumerated.
    Exhaustive,
    /// Edge cases plus `sample_count` random trials. High confidence, not a
    /// proof: the obligation holds on the sampled points only.
    Statistical {
        /// Number of random trials that were run (excludes edge cases).
        sample_count: u64,
    },
    /// An SMT solver returned a complete refutation-free result for the whole
    /// input space.
    Formal {
        /// Stable name of the solver that discharged the obligation.
        solver: String,
    },
}

impl EvidenceStrength {
    /// Stable contract string for this strength.
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::NotReported => "not_reported",
            Self::NotRun => "not_run",
            Self::Exhaustive => "exhaustive",
            Self::Statistical { .. } => "statistical",
            Self::Formal { .. } => "formal",
        }
    }

    /// Whether this strength covers the whole input space.
    ///
    /// Statistical discharge is deliberately *not* complete, and neither
    /// `NotRun` nor `NotReported` are.
    pub const fn is_complete(&self) -> bool {
        matches!(self, Self::Exhaustive | Self::Formal { .. })
    }

    /// Whether anything at all ran to produce this strength.
    pub const fn ran(&self) -> bool {
        matches!(
            self,
            Self::Exhaustive | Self::Statistical { .. } | Self::Formal { .. }
        )
    }
}

/// Minimum discharge strength a caller demands before an artifact may carry a
/// certificate.
///
/// The point of the type is refusal: a caller that asks for
/// [`Self::Formal`] on a host with no solver must get a rejected compile, not
/// a quietly-downgraded [`EvidenceStrength::Statistical`] certificate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum RequiredEvidenceStrength {
    /// Any strength is acceptable, including statistical. Current default; it
    /// preserves the historical behaviour of every existing caller.
    #[default]
    Any,
    /// The obligation must be covered completely: exhaustive enumeration or a
    /// solver proof. Statistical sampling is refused.
    Complete,
    /// The obligation must be discharged by an SMT solver. Exhaustive
    /// enumeration over a small input space is refused as well, because the
    /// caller asked specifically for solver authority.
    Formal,
}

impl RequiredEvidenceStrength {
    /// Stable contract string for this requirement.
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::Any => "any",
            Self::Complete => "complete",
            Self::Formal => "formal",
        }
    }

    /// Whether `strength` satisfies this requirement.
    pub const fn admits(&self, strength: &EvidenceStrength) -> bool {
        match self {
            Self::Any => true,
            Self::Complete => strength.is_complete(),
            Self::Formal => matches!(strength, EvidenceStrength::Formal { .. }),
        }
    }

    /// Whether this requirement can only be met by a live SMT solver.
    pub const fn needs_solver(&self) -> bool {
        matches!(self, Self::Formal)
    }
}

/// One fact an artifact is *relying on* rather than checking.
///
/// An accepted assumption is the honest complement of a verdict: the verdict
/// says what was established, the assumption says what was taken on trust to
/// establish it. A consumer reading `verdict: Verified` with
/// `strength: Statistical` and an assumption of
/// [`ASSUMPTION_NO_SOLVER_AVAILABLE`] knows exactly what it is trusting.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AcceptedAssumption {
    /// Stable machine-readable assumption id. Consumers match on this.
    pub id: String,
    /// Human-readable statement of what is being relied on.
    pub detail: String,
}

impl AcceptedAssumption {
    /// Create an accepted assumption from its stable id and detail text.
    pub fn new(id: impl Into<String>, detail: impl Into<String>) -> Self {
        Self {
            id: id.into(),
            detail: detail.into(),
        }
    }
}

/// Obligations above the exhaustive width/arity threshold were discharged by
/// sampling because no SMT solver binary was reachable on this host.
pub const ASSUMPTION_NO_SOLVER_AVAILABLE: &str = "trust-cg.assumption.no_solver_available";

/// Obligations were discharged statistically: edge cases plus N random trials
/// generalize to the full input space.
pub const ASSUMPTION_STATISTICAL_DISCHARGE: &str = "trust-cg.assumption.statistical_discharge";

/// The TV-3 dataflow-integrity validator ran in warn mode rather than enforce
/// mode, so a violation was reported but did not fail the compile closed.
pub const ASSUMPTION_TV3_WARN_NOT_ENFORCE: &str = "trust-cg.assumption.tv3_warn_not_enforce";

/// A conformance/coverage manifest was consulted as a pin instead of being
/// re-derived from the sources it claims to summarize.
pub const ASSUMPTION_MANIFEST_PIN_NOT_REDERIVED: &str =
    "trust-cg.assumption.manifest_pin_not_rederived";

/// Instruction-level verification was disabled for this compile, so no
/// per-instruction lowering proof, TV gate, or function verifier ran.
pub const ASSUMPTION_VERIFICATION_DISABLED: &str = "trust-cg.assumption.verification_disabled";

/// Dispatch-plan verification was switched off for this compile.
pub const ASSUMPTION_DISPATCH_VERIFY_OFF: &str = "trust-cg.assumption.dispatch_verify_off";

/// Proof enforcement mode for installable artifacts.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProofMode {
    /// Proof evidence is not required.
    Disabled,
    /// Keep evidence when available, but do not reject missing evidence.
    AuditOnly,
    /// Require attached proof certificates.
    RequireCertificates,
    /// Require replayable proof evidence.
    RequireReplay,
}

/// Product-contract proof policy.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProofPolicy {
    /// Proof enforcement mode.
    pub mode: ProofMode,
    /// Whether a JIT certificate must be attached.
    pub require_jit_certificate: bool,
    /// Whether layout evidence must be present.
    pub require_layout_evidence: bool,
    /// Whether ABI evidence must be present.
    pub require_abi_evidence: bool,
    /// Accepted proof solver or verifier names. Treated as an unordered set.
    pub accepted_solvers: Vec<String>,
    /// Optional maximum proof replay age in generations.
    pub max_replay_age_generations: Option<u64>,
    /// Minimum discharge strength the caller demands.
    ///
    /// Defaults to [`RequiredEvidenceStrength::Any`], which is exactly the
    /// historical behaviour. Anything stronger is *refusable*: a compile that
    /// cannot reach the requested strength on this host must be rejected
    /// rather than silently certified at a weaker strength.
    pub required_strength: RequiredEvidenceStrength,
}

impl ProofPolicy {
    /// Create a policy that does not require proof evidence.
    pub fn disabled() -> Self {
        Self {
            mode: ProofMode::Disabled,
            require_jit_certificate: false,
            require_layout_evidence: false,
            require_abi_evidence: false,
            accepted_solvers: Vec::new(),
            max_replay_age_generations: None,
            required_strength: RequiredEvidenceStrength::Any,
        }
    }

    /// Create a fail-closed certificate policy.
    pub fn require_certificates(
        accepted_solvers: impl IntoIterator<Item = impl Into<String>>,
    ) -> Self {
        Self {
            mode: ProofMode::RequireCertificates,
            require_jit_certificate: true,
            require_layout_evidence: true,
            require_abi_evidence: true,
            accepted_solvers: normalize_string_set(accepted_solvers),
            max_replay_age_generations: None,
            required_strength: RequiredEvidenceStrength::Any,
        }
    }

    /// Demand a minimum discharge strength for the certificates this policy
    /// requires.
    ///
    /// A host that cannot reach the requested strength must refuse the
    /// compile; see `trust_cg_codegen::proof_evidence`.
    pub const fn with_required_strength(mut self, strength: RequiredEvidenceStrength) -> Self {
        self.required_strength = strength;
        self
    }

    /// Deterministic checksum for this proof policy.
    pub fn checksum(&self) -> ArtifactChecksum {
        checksum_of(self)
    }

    /// Whether this policy requires proof evidence before typed exposure.
    pub fn requires_evidence(&self) -> bool {
        matches!(
            self.mode,
            ProofMode::RequireCertificates | ProofMode::RequireReplay
        )
    }
}

/// Stable verdict carried by a proof or translation-validation evidence summary.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProofEvidenceVerdict {
    /// Proof or translation validation succeeded.
    Verified,
    /// Required evidence was not attached.
    MissingEvidence,
    /// The verifier rejected the artifact.
    VerifierFailure,
    /// Proof replay or verification timed out.
    Timeout,
    /// Verification returned an unknown result.
    Unknown,
    /// Solver execution failed.
    SolverError,
    /// The evidence cannot be produced on this compile route.
    UnsupportedRoute,
    /// The evidence does not support the target.
    UnsupportedTarget,
    /// Evidence is too old for the requested invalidation generation.
    StaleEvidence,
    /// The evidence report could not be parsed or validated.
    MalformedReport,
    /// The evidence report omitted fields required for install authority.
    MissingRequiredFields,
    /// Solver failed or returned an unknown result.
    UnknownSolverError,
}

impl ProofEvidenceVerdict {
    /// Stable contract string for this verdict.
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::Verified => "verified",
            Self::MissingEvidence => "missing_evidence",
            Self::VerifierFailure => "verifier_failure",
            Self::Timeout => "timeout",
            Self::Unknown => "unknown",
            Self::SolverError => "solver_error",
            Self::UnsupportedRoute => "unsupported_route",
            Self::UnsupportedTarget => "unsupported_target",
            Self::StaleEvidence => "stale_evidence",
            Self::MalformedReport => "malformed_report",
            Self::MissingRequiredFields => "missing_required_fields",
            Self::UnknownSolverError => "unknown_solver_error",
        }
    }
}

/// Stable rejection code carried by proof or translation-validation evidence.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProofEvidenceRejectionCode {
    /// Required proof or TV evidence was not attached.
    MissingEvidence,
    /// Verifier rejected the artifact or proof.
    VerifierFailure,
    /// Verification or replay timed out.
    Timeout,
    /// Verification returned unknown.
    Unknown,
    /// Solver execution failed.
    SolverError,
    /// Evidence cannot be produced on this compile route.
    UnsupportedRoute,
    /// Evidence does not cover the requested target.
    UnsupportedTarget,
    /// Evidence is stale for the requested invalidation generation.
    StaleEvidence,
    /// Evidence report was malformed.
    MalformedReport,
    /// Evidence report omitted required fields.
    MissingRequiredFields,
    /// Solver failed or returned unknown.
    UnknownSolverError,
}

impl ProofEvidenceRejectionCode {
    /// Stable contract string for this rejection code.
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::MissingEvidence => "proof_missing_evidence",
            Self::VerifierFailure => "proof_verifier_failure",
            Self::Timeout => "proof_timeout",
            Self::Unknown => "proof_unknown",
            Self::SolverError => "proof_solver_error",
            Self::UnsupportedRoute => "proof_unsupported_route",
            Self::UnsupportedTarget => "proof_unsupported_target",
            Self::StaleEvidence => "proof_stale_evidence",
            Self::MalformedReport => "proof_malformed_report",
            Self::MissingRequiredFields => "proof_missing_required_fields",
            Self::UnknownSolverError => "proof_unknown_solver_error",
        }
    }
}

/// Versioned summary of proof or translation-validation evidence.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProofEvidenceSummary {
    /// Evidence summary schema name.
    pub schema: String,
    /// Evidence summary schema version.
    pub schema_version: u32,
    /// Stable proof or translation-validation engine name.
    pub verifier: String,
    /// Stable proof or translation-validation verdict.
    pub verdict: ProofEvidenceVerdict,
    /// Stable rejection code when the verdict is not verified.
    pub rejection_code: Option<ProofEvidenceRejectionCode>,
    /// Target descriptor checksum covered by this evidence.
    pub target_checksum: ArtifactChecksum,
    /// ABI descriptor checksum covered by this evidence.
    pub abi_checksum: ArtifactChecksum,
    /// Layout manifest checksum covered by this evidence.
    pub layout_checksum: ArtifactChecksum,
    /// Invalidation-key checksum covered by this evidence.
    pub invalidation_checksum: ArtifactChecksum,
    /// Proof-policy checksum covered by this evidence.
    pub proof_policy_checksum: ArtifactChecksum,
    /// Manifest artifact id covered by this evidence.
    pub artifact_id: String,
    /// Whole artifact manifest checksum covered by this evidence.
    pub manifest_checksum: ArtifactChecksum,
    /// Native payload digest covered by this evidence.
    pub native_payload_sha256: String,
    /// Proof report digest covered by this evidence.
    pub proof_report_sha256: String,
    /// Sorted symbol manifest checksum covered by this evidence.
    pub symbol_manifest_checksum: ArtifactChecksum,
    /// How the covered obligations were actually discharged.
    ///
    /// [`EvidenceStrength::NotRun`] on a route where nothing ran;
    /// [`EvidenceStrength::NotReported`] only where the producing route
    /// genuinely does not know.
    pub strength: EvidenceStrength,
    /// What this evidence is *relying on* rather than checking.
    ///
    /// Kept sorted and deduplicated by
    /// [`ProofEvidenceSummary::with_accepted_assumptions`] so the canonical
    /// encoding is order-independent.
    pub accepted_assumptions: Vec<AcceptedAssumption>,
    /// Additional deterministic evidence metadata.
    pub metadata: BTreeMap<String, String>,
}

impl ProofEvidenceSummary {
    /// Create a verified evidence summary bound to the core artifact checksums.
    pub fn verified(
        verifier: impl Into<String>,
        target_checksum: ArtifactChecksum,
        abi_checksum: ArtifactChecksum,
        layout_checksum: ArtifactChecksum,
        invalidation_checksum: ArtifactChecksum,
        proof_policy_checksum: ArtifactChecksum,
    ) -> Self {
        Self {
            schema: JIT_PROOF_EVIDENCE_SUMMARY_SCHEMA.to_owned(),
            schema_version: JIT_PROOF_EVIDENCE_SUMMARY_SCHEMA_VERSION,
            verifier: verifier.into(),
            verdict: ProofEvidenceVerdict::Verified,
            rejection_code: None,
            target_checksum,
            abi_checksum,
            layout_checksum,
            invalidation_checksum,
            proof_policy_checksum,
            artifact_id: String::new(),
            manifest_checksum: ArtifactChecksum::new(0),
            native_payload_sha256: String::new(),
            proof_report_sha256: String::new(),
            symbol_manifest_checksum: ArtifactChecksum::new(0),
            strength: EvidenceStrength::NotReported,
            accepted_assumptions: Vec::new(),
            metadata: BTreeMap::new(),
        }
    }

    /// Create verified evidence bound to the exact native artifact identity.
    pub fn verified_for_artifact(
        verifier: impl Into<String>,
        manifest: &DeterministicArtifactManifest,
        native_payload_sha256: impl Into<String>,
        proof_report_sha256: impl Into<String>,
    ) -> Self {
        let mut evidence = Self::verified(
            verifier,
            manifest.target.checksum(),
            manifest.abi.checksum(),
            manifest.layout.checksum(),
            manifest.invalidation.checksum(),
            manifest.proof_policy.checksum(),
        );
        evidence.artifact_id = manifest.artifact_id.clone();
        evidence.manifest_checksum = manifest.checksum();
        evidence.native_payload_sha256 = native_payload_sha256.into();
        evidence.proof_report_sha256 = proof_report_sha256.into();
        evidence.symbol_manifest_checksum = manifest.symbol_manifest_checksum();
        evidence
    }

    /// Create a rejected evidence summary bound to the core artifact checksums.
    pub fn rejected(
        verifier: impl Into<String>,
        verdict: ProofEvidenceVerdict,
        rejection_code: ProofEvidenceRejectionCode,
        target_checksum: ArtifactChecksum,
        abi_checksum: ArtifactChecksum,
        layout_checksum: ArtifactChecksum,
        invalidation_checksum: ArtifactChecksum,
        proof_policy_checksum: ArtifactChecksum,
    ) -> Self {
        Self {
            schema: JIT_PROOF_EVIDENCE_SUMMARY_SCHEMA.to_owned(),
            schema_version: JIT_PROOF_EVIDENCE_SUMMARY_SCHEMA_VERSION,
            verifier: verifier.into(),
            verdict,
            rejection_code: Some(rejection_code),
            target_checksum,
            abi_checksum,
            layout_checksum,
            invalidation_checksum,
            proof_policy_checksum,
            artifact_id: String::new(),
            manifest_checksum: ArtifactChecksum::new(0),
            native_payload_sha256: String::new(),
            proof_report_sha256: String::new(),
            symbol_manifest_checksum: ArtifactChecksum::new(0),
            strength: EvidenceStrength::NotReported,
            accepted_assumptions: Vec::new(),
            metadata: BTreeMap::new(),
        }
    }

    /// Create rejected evidence bound to the exact native artifact identity.
    pub fn rejected_for_artifact(
        verifier: impl Into<String>,
        verdict: ProofEvidenceVerdict,
        rejection_code: ProofEvidenceRejectionCode,
        manifest: &DeterministicArtifactManifest,
        native_payload_sha256: impl Into<String>,
        proof_report_sha256: impl Into<String>,
    ) -> Self {
        let mut evidence = Self::rejected(
            verifier,
            verdict,
            rejection_code,
            manifest.target.checksum(),
            manifest.abi.checksum(),
            manifest.layout.checksum(),
            manifest.invalidation.checksum(),
            manifest.proof_policy.checksum(),
        );
        evidence.artifact_id = manifest.artifact_id.clone();
        evidence.manifest_checksum = manifest.checksum();
        evidence.native_payload_sha256 = native_payload_sha256.into();
        evidence.proof_report_sha256 = proof_report_sha256.into();
        evidence.symbol_manifest_checksum = manifest.symbol_manifest_checksum();
        evidence
    }

    /// Create the explicit "nothing ran on this route" evidence summary.
    ///
    /// This is the whole point of WP-0: a compile route on which no proof, no
    /// translation-validation gate, and no verifier executed must emit an
    /// explicit [`ProofEvidenceVerdict::MissingEvidence`] at
    /// [`EvidenceStrength::NotRun`] rather than emitting nothing at all. An
    /// absent field is indistinguishable from a passing one; a negative field
    /// is not.
    pub fn missing(verifier: impl Into<String>) -> Self {
        Self {
            schema: JIT_PROOF_EVIDENCE_SUMMARY_SCHEMA.to_owned(),
            schema_version: JIT_PROOF_EVIDENCE_SUMMARY_SCHEMA_VERSION,
            verifier: verifier.into(),
            verdict: ProofEvidenceVerdict::MissingEvidence,
            rejection_code: Some(ProofEvidenceRejectionCode::MissingEvidence),
            target_checksum: ArtifactChecksum::new(0),
            abi_checksum: ArtifactChecksum::new(0),
            layout_checksum: ArtifactChecksum::new(0),
            invalidation_checksum: ArtifactChecksum::new(0),
            proof_policy_checksum: ArtifactChecksum::new(0),
            artifact_id: String::new(),
            manifest_checksum: ArtifactChecksum::new(0),
            native_payload_sha256: String::new(),
            proof_report_sha256: String::new(),
            symbol_manifest_checksum: ArtifactChecksum::new(0),
            strength: EvidenceStrength::NotRun,
            accepted_assumptions: Vec::new(),
            metadata: BTreeMap::new(),
        }
    }

    /// Create "nothing ran" evidence bound to the checksums of a manifest.
    ///
    /// Binding the checksums keeps the negative statement attributable: a
    /// consumer can tell *which* artifact nothing ran on.
    pub fn missing_for_manifest(
        verifier: impl Into<String>,
        manifest: &DeterministicArtifactManifest,
    ) -> Self {
        let mut evidence = Self::missing(verifier);
        evidence.target_checksum = manifest.target.checksum();
        evidence.abi_checksum = manifest.abi.checksum();
        evidence.layout_checksum = manifest.layout.checksum();
        evidence.invalidation_checksum = manifest.invalidation.checksum();
        evidence.proof_policy_checksum = manifest.proof_policy.checksum();
        evidence.artifact_id = manifest.artifact_id.clone();
        evidence.manifest_checksum = manifest.checksum();
        evidence.symbol_manifest_checksum = manifest.symbol_manifest_checksum();
        evidence
    }

    /// Report the discharge strength this evidence was produced at.
    pub fn with_strength(mut self, strength: EvidenceStrength) -> Self {
        self.strength = strength;
        self
    }

    /// Restate the verdict once the producing route knows the real outcome.
    ///
    /// Used by routes that build the strength/assumption channel first (which
    /// depends only on the configuration) and learn the verdict afterwards.
    pub fn with_verdict(
        mut self,
        verdict: ProofEvidenceVerdict,
        rejection_code: Option<ProofEvidenceRejectionCode>,
    ) -> Self {
        self.verdict = verdict;
        self.rejection_code = rejection_code;
        self
    }

    /// Record what this evidence relies on rather than checks.
    ///
    /// Assumptions are sorted by id and deduplicated, so the canonical
    /// encoding does not depend on the order the producer discovered them.
    pub fn with_accepted_assumptions(
        mut self,
        assumptions: impl IntoIterator<Item = AcceptedAssumption>,
    ) -> Self {
        self.accepted_assumptions.extend(assumptions);
        self.accepted_assumptions.sort();
        self.accepted_assumptions.dedup_by(|a, b| a.id == b.id);
        self
    }

    /// Stable ids of every assumption this evidence accepted.
    pub fn accepted_assumption_ids(&self) -> Vec<&str> {
        self.accepted_assumptions
            .iter()
            .map(|assumption| assumption.id.as_str())
            .collect()
    }

    /// Whether this evidence explicitly states that nothing ran.
    pub fn is_missing_evidence(&self) -> bool {
        self.verdict == ProofEvidenceVerdict::MissingEvidence
    }

    /// Whether the reported strength satisfies `required`.
    pub fn satisfies_required_strength(&self, required: RequiredEvidenceStrength) -> bool {
        required.admits(&self.strength)
    }

    /// Deterministic checksum for this evidence summary.
    pub fn checksum(&self) -> ArtifactChecksum {
        checksum_of(self)
    }
}

/// Native apply status code shared by product JIT consumers.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ApplyStatusCode {
    /// Native call completed successfully.
    Ok,
    /// Arithmetic overflow.
    Overflow,
    /// Bounds check failed.
    Bounds,
    /// Required variable was missing.
    MissingVar,
    /// Artifact generation is stale.
    StaleGeneration,
    /// Runtime shape is unsupported by this artifact.
    UnsupportedShape,
    /// Runtime target is unsupported by this artifact.
    UnsupportedTarget,
    /// Verification or proof policy failed.
    VerifierFailure,
    /// Compile, verification, or apply timeout.
    Timeout,
    /// Internal error.
    InternalError,
    /// Downstream-defined status code.
    Other(String),
}

/// Typed deopt reason.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DeoptReason {
    /// Artifact was stale for the caller's generation.
    StaleArtifact,
    /// Proof policy rejected the artifact.
    ProofPolicyRejected,
    /// ABI descriptor or checksum did not match.
    AbiMismatch,
    /// Layout manifest or checksum did not match.
    LayoutMismatch,
    /// Callable symbol was not present.
    MissingSymbol,
    /// Symbol signature did not match the typed wrapper.
    SignatureMismatch,
    /// Artifact checksum did not match.
    ChecksumMismatch,
    /// Native code trapped or reported an internal failure.
    BackendTrap,
    /// Downstream-defined deopt reason.
    Other(String),
}

/// Typed deopt record returned instead of exposing a callable handle or result.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypedDeopt {
    /// Apply status code associated with the deopt.
    pub status: ApplyStatusCode,
    /// Deopt reason.
    pub reason: DeoptReason,
    /// Optional symbol involved in the deopt.
    pub symbol: Option<String>,
    /// Optional expected signature.
    pub expected_signature: Option<SymbolSignature>,
    /// Optional actual signature.
    pub actual_signature: Option<SymbolSignature>,
    /// Human-readable detail for logs.
    pub detail: Option<String>,
}

/// Terminal apply failure record.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ApplyFailure {
    /// Apply status code.
    pub status: ApplyStatusCode,
    /// Human-readable detail for logs.
    pub detail: Option<String>,
}

/// Typed apply result shell for downstream wrappers.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypedApplyStatus<T> {
    /// Native call or install operation succeeded.
    Applied {
        /// Typed value returned by the wrapper.
        value: T,
        /// Artifact checksum used by the wrapper.
        artifact_checksum: ArtifactChecksum,
    },
    /// Operation deoptimized to the interpreter or safe fallback path.
    Deoptimized(TypedDeopt),
    /// Operation failed without a fallback result.
    Failed(ApplyFailure),
}

/// Product-facing alias for native apply results.
pub type NativeApplyStatus<T> = TypedApplyStatus<T>;

/// Product-facing alias for native deopt reasons.
pub type NativeDeoptReason = DeoptReason;

/// Artifact payload category.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum JitArtifactKind {
    /// Relocatable object bytes.
    Object,
    /// Executable memory.
    ExecutableMemory,
    /// Downstream-defined artifact kind.
    Other(String),
}

/// Symbol visibility in the deterministic manifest.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SymbolVisibility {
    /// Public exported symbol.
    Exported,
    /// Internal symbol.
    Internal,
    /// Imported external symbol.
    Imported,
}

/// Manifest symbol entry.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArtifactSymbol {
    /// Symbol name.
    pub name: String,
    /// Symbol visibility.
    pub visibility: SymbolVisibility,
    /// Callable signature.
    pub signature: SymbolSignature,
    /// Optional byte offset in the executable allocation.
    pub offset_bytes: Option<u64>,
    /// Optional symbol-byte checksum.
    pub checksum: Option<ArtifactChecksum>,
}

/// Artifact section category.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArtifactSectionKind {
    /// Executable text.
    Text,
    /// Read-only data.
    Rodata,
    /// Writable data.
    Data,
    /// Unwind or exception metadata.
    Unwind,
    /// Downstream-defined section kind.
    Other(String),
}

/// Manifest section entry.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArtifactSection {
    /// Section name.
    pub name: String,
    /// Section kind.
    pub kind: ArtifactSectionKind,
    /// Section size in bytes.
    pub size_bytes: u64,
    /// Section alignment in bytes.
    pub alignment_bytes: u32,
    /// Optional section-byte checksum.
    pub checksum: Option<ArtifactChecksum>,
}

/// Expected contract facts for exposing one typed callable symbol.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SymbolLookupContract {
    /// Symbol name requested by the generated wrapper.
    pub symbol: String,
    /// Signature expected by the generated wrapper.
    pub signature: SymbolSignature,
    /// Target descriptor checksum expected by the generated wrapper.
    pub target_checksum: ArtifactChecksum,
    /// ABI descriptor checksum expected by the generated wrapper.
    pub abi_checksum: ArtifactChecksum,
    /// Layout manifest checksum expected by the generated wrapper.
    pub layout_checksum: ArtifactChecksum,
    /// Optional invalidation-key checksum expected by the caller.
    pub invalidation_checksum: Option<ArtifactChecksum>,
    /// Whether proof evidence is required even for disabled/audit-only policies.
    pub require_proof_evidence: bool,
    /// Optional proof or translation-validation evidence for typed exposure.
    pub proof_evidence: Option<ProofEvidenceSummary>,
    /// Optional full manifest checksum expected by the caller.
    pub manifest_checksum: Option<ArtifactChecksum>,
}

impl SymbolLookupContract {
    /// Create a symbol lookup contract from descriptor checksums.
    pub fn new(
        symbol: impl Into<String>,
        signature: SymbolSignature,
        target_checksum: ArtifactChecksum,
        abi_checksum: ArtifactChecksum,
        layout_checksum: ArtifactChecksum,
    ) -> Self {
        Self {
            symbol: symbol.into(),
            signature,
            target_checksum,
            abi_checksum,
            layout_checksum,
            invalidation_checksum: None,
            require_proof_evidence: false,
            proof_evidence: None,
            manifest_checksum: None,
        }
    }

    /// Require the invalidation key to match a known checksum.
    pub const fn with_invalidation_checksum(mut self, checksum: ArtifactChecksum) -> Self {
        self.invalidation_checksum = Some(checksum);
        self
    }

    /// Require the whole manifest to match a known checksum.
    pub const fn with_manifest_checksum(mut self, checksum: ArtifactChecksum) -> Self {
        self.manifest_checksum = Some(checksum);
        self
    }

    /// Require proof evidence even when the manifest policy is disabled or audit-only.
    pub const fn with_required_proof_evidence(mut self) -> Self {
        self.require_proof_evidence = true;
        self
    }

    /// Attach proof or translation-validation evidence for typed exposure.
    pub fn with_proof_evidence(mut self, evidence: ProofEvidenceSummary) -> Self {
        self.proof_evidence = Some(evidence);
        self
    }
}

/// Product-facing kernel intent for artifacts shared with TY-like consumers.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum KernelArtifactKind {
    /// Native successor enumeration or expansion kernel.
    SuccessorKernel,
    /// Native state predicate or invariant/filter kernel.
    PredicateKernel,
    /// Downstream-defined kernel kind.
    Other(String),
}

impl KernelArtifactKind {
    /// Stable contract string for this kernel kind.
    pub fn as_str(&self) -> &str {
        match self {
            Self::SuccessorKernel => "successor_kernel",
            Self::PredicateKernel => "predicate_kernel",
            Self::Other(value) => value.as_str(),
        }
    }
}

/// Finite-domain facts for native kernel artifacts.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum KernelStateDomain {
    /// State space is finite with a known upper bound.
    Finite {
        /// Number of state variables encoded by the kernel.
        variable_count: u32,
        /// Optional upper bound on distinct states.
        max_state_count: Option<u64>,
    },
    /// State space is bounded by a named downstream invariant.
    BoundedByInvariant {
        /// Stable invariant or proof fact name.
        invariant: String,
    },
    /// Domain evidence is intentionally not exposed yet.
    Unknown,
}

/// Data-only contract for a native successor or predicate kernel artifact.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct KernelArtifactContract {
    /// Kernel contract schema name.
    pub schema: String,
    /// Kernel contract schema version.
    pub schema_version: u32,
    /// Downstream consumer, such as `ty`.
    pub consumer: String,
    /// Kernel kind.
    pub kind: KernelArtifactKind,
    /// Callable entry symbol in the artifact manifest.
    pub entry_symbol: String,
    /// Expected callable signature.
    pub signature: SymbolSignature,
    /// Target descriptor checksum expected by the consumer.
    pub target_checksum: ArtifactChecksum,
    /// ABI descriptor checksum expected by the consumer.
    pub abi_checksum: ArtifactChecksum,
    /// Layout manifest checksum expected by the consumer.
    pub layout_checksum: ArtifactChecksum,
    /// Proof policy checksum expected by the consumer.
    pub proof_policy_checksum: ArtifactChecksum,
    /// Finite-domain or bounded-domain evidence for safe state exploration.
    pub state_domain: KernelStateDomain,
    /// Stable checksum for the transition relation or predicate source.
    pub semantic_checksum: ArtifactChecksum,
    /// Manifest metadata keys that must be present before consumer adoption.
    pub required_manifest_metadata: Vec<String>,
    /// Downstream extension metadata. Keys are deterministic.
    pub metadata: BTreeMap<String, String>,
}

impl KernelArtifactContract {
    /// Create a successor-kernel contract bound to artifact descriptor checksums.
    pub fn successor_kernel(
        consumer: impl Into<String>,
        entry_symbol: impl Into<String>,
        signature: SymbolSignature,
        manifest: &DeterministicArtifactManifest,
        state_domain: KernelStateDomain,
        transition_relation_checksum: ArtifactChecksum,
    ) -> Self {
        Self::new(
            consumer,
            KernelArtifactKind::SuccessorKernel,
            entry_symbol,
            signature,
            manifest,
            state_domain,
            transition_relation_checksum,
        )
    }

    /// Create a predicate-kernel contract bound to artifact descriptor checksums.
    pub fn predicate_kernel(
        consumer: impl Into<String>,
        entry_symbol: impl Into<String>,
        signature: SymbolSignature,
        manifest: &DeterministicArtifactManifest,
        state_domain: KernelStateDomain,
        predicate_checksum: ArtifactChecksum,
    ) -> Self {
        Self::new(
            consumer,
            KernelArtifactKind::PredicateKernel,
            entry_symbol,
            signature,
            manifest,
            state_domain,
            predicate_checksum,
        )
    }

    fn new(
        consumer: impl Into<String>,
        kind: KernelArtifactKind,
        entry_symbol: impl Into<String>,
        signature: SymbolSignature,
        manifest: &DeterministicArtifactManifest,
        state_domain: KernelStateDomain,
        semantic_checksum: ArtifactChecksum,
    ) -> Self {
        Self {
            schema: KERNEL_ARTIFACT_CONTRACT_SCHEMA.to_owned(),
            schema_version: KERNEL_ARTIFACT_CONTRACT_SCHEMA_VERSION,
            consumer: consumer.into(),
            kind,
            entry_symbol: entry_symbol.into(),
            signature,
            target_checksum: manifest.target.checksum(),
            abi_checksum: manifest.abi.checksum(),
            layout_checksum: manifest.layout.checksum(),
            proof_policy_checksum: manifest.proof_policy.checksum(),
            state_domain,
            semantic_checksum,
            required_manifest_metadata: Vec::new(),
            metadata: BTreeMap::new(),
        }
    }

    /// Require a manifest metadata key before this kernel can be adopted.
    pub fn with_required_manifest_metadata(mut self, key: impl Into<String>) -> Self {
        self.required_manifest_metadata.push(key.into());
        self.required_manifest_metadata = normalize_string_set(self.required_manifest_metadata);
        self
    }

    /// Deterministic checksum for this kernel contract.
    pub fn checksum(&self) -> ArtifactChecksum {
        checksum_of(self)
    }

    /// Validate this kernel contract against an artifact manifest.
    pub fn validate_manifest(
        &self,
        manifest: &DeterministicArtifactManifest,
    ) -> Result<(), ArtifactContractError> {
        if self.schema != KERNEL_ARTIFACT_CONTRACT_SCHEMA
            || self.schema_version != KERNEL_ARTIFACT_CONTRACT_SCHEMA_VERSION
        {
            return Err(ArtifactContractError::SchemaMismatch {
                expected_schema: KERNEL_ARTIFACT_CONTRACT_SCHEMA.to_owned(),
                expected_version: KERNEL_ARTIFACT_CONTRACT_SCHEMA_VERSION,
                actual_schema: self.schema.clone(),
                actual_version: self.schema_version,
            });
        }

        manifest.verify_schema()?;
        manifest.verify_target_checksum(self.target_checksum)?;
        manifest.verify_abi_checksum(self.abi_checksum)?;
        manifest.verify_layout_checksum(self.layout_checksum)?;
        let actual_policy = manifest.proof_policy.checksum();
        if actual_policy != self.proof_policy_checksum {
            return Err(ArtifactContractError::ChecksumMismatch {
                component: "proof_policy".to_owned(),
                expected: self.proof_policy_checksum,
                actual: actual_policy,
            });
        }
        manifest.verify_symbol_signature(&self.entry_symbol, &self.signature)?;

        for key in &self.required_manifest_metadata {
            if !manifest.metadata.contains_key(key) {
                return Err(ArtifactContractError::MissingManifestMetadata { key: key.clone() });
            }
        }

        Ok(())
    }
}

/// Typed callable symbol handle returned only after contract validation.
pub struct TypedSymbol<'artifact, F: Copy> {
    ptr: NonNull<()>,
    symbol: String,
    signature: SymbolSignature,
    artifact_checksum: ArtifactChecksum,
    _marker: PhantomData<&'artifact F>,
}

impl<'artifact, F: Copy> fmt::Debug for TypedSymbol<'artifact, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TypedSymbol")
            .field("ptr", &self.as_ptr())
            .field("symbol", &self.symbol)
            .field("signature", &self.signature)
            .field("artifact_checksum", &self.artifact_checksum)
            .finish()
    }
}

impl<'artifact, F: Copy> Clone for TypedSymbol<'artifact, F> {
    fn clone(&self) -> Self {
        Self {
            ptr: self.ptr,
            symbol: self.symbol.clone(),
            signature: self.signature.clone(),
            artifact_checksum: self.artifact_checksum,
            _marker: PhantomData,
        }
    }
}

impl<'artifact, F: Copy> TypedSymbol<'artifact, F> {
    /// Symbol name validated by the manifest.
    pub fn symbol(&self) -> &str {
        &self.symbol
    }

    /// Signature validated by the manifest.
    pub fn signature(&self) -> &SymbolSignature {
        &self.signature
    }

    /// Manifest checksum validated when the handle was constructed.
    pub const fn artifact_checksum(&self) -> ArtifactChecksum {
        self.artifact_checksum
    }

    /// Return the validated raw code pointer.
    pub fn as_ptr(&self) -> *const u8 {
        self.ptr.as_ptr().cast::<u8>()
    }

    /// Convert the validated code pointer into the typed function pointer.
    ///
    /// # Safety
    ///
    /// `F` must be a function-pointer type matching the validated
    /// [`SymbolSignature`], and the executable allocation must outlive this
    /// handle. Generated wrappers should keep this conversion below the
    /// manifest-validated boundary and expose typed calls above it.
    pub unsafe fn into_fn(self) -> F {
        assert_eq!(
            std::mem::size_of::<F>(),
            std::mem::size_of::<*const u8>(),
            "TypedSymbol<F>: F must be pointer-sized (expected {} bytes, got {} bytes)",
            std::mem::size_of::<*const u8>(),
            std::mem::size_of::<F>(),
        );
        let raw = self.as_ptr();
        // SAFETY: documented on this method; contract validation has already
        // checked schema, ABI/layout/target checksums, and symbol signature.
        unsafe { std::mem::transmute_copy(&raw) }
    }
}

/// Deterministic shared JIT artifact manifest.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DeterministicArtifactManifest {
    /// Manifest schema name.
    pub schema: String,
    /// Manifest schema version.
    pub schema_version: u32,
    /// Caller-visible artifact id.
    pub artifact_id: String,
    /// Artifact payload kind.
    pub kind: JitArtifactKind,
    /// Target descriptor.
    pub target: TargetDescriptor,
    /// ABI descriptor.
    pub abi: AbiDescriptor,
    /// Layout manifest.
    pub layout: LayoutManifest,
    /// Invalidation key.
    pub invalidation: InvalidationKey,
    /// Proof policy.
    pub proof_policy: ProofPolicy,
    /// Callable and non-callable symbols. Encoded sorted by symbol name.
    pub symbols: Vec<ArtifactSymbol>,
    /// Artifact sections. Encoded sorted by section name.
    pub sections: Vec<ArtifactSection>,
    /// Downstream extension metadata. Keys are deterministic.
    pub metadata: BTreeMap<String, String>,
}

impl DeterministicArtifactManifest {
    /// Create a manifest with the current schema version.
    pub fn new(
        artifact_id: impl Into<String>,
        kind: JitArtifactKind,
        target: TargetDescriptor,
        abi: AbiDescriptor,
        layout: LayoutManifest,
        invalidation: InvalidationKey,
        proof_policy: ProofPolicy,
    ) -> Self {
        let mut manifest = Self {
            schema: JIT_ARTIFACT_MANIFEST_SCHEMA.to_owned(),
            schema_version: JIT_ARTIFACT_MANIFEST_SCHEMA_VERSION,
            artifact_id: artifact_id.into(),
            kind,
            target,
            abi,
            layout,
            invalidation,
            proof_policy,
            symbols: Vec::new(),
            sections: Vec::new(),
            metadata: BTreeMap::new(),
        };
        bind_trust_ir_hardware_vector_contract_metadata(&mut manifest.metadata);
        bind_host_jit_target_feature_profile_metadata(&mut manifest);
        manifest
    }

    /// Return canonical binary bytes for deterministic persistence or hashing.
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        self.encode(&mut out);
        out
    }

    /// Deterministic checksum for this manifest.
    pub fn checksum(&self) -> ArtifactChecksum {
        ArtifactChecksum::for_bytes(&self.canonical_bytes())
    }

    /// Deterministic checksum for just the sorted symbol manifest.
    pub fn symbol_manifest_checksum(&self) -> ArtifactChecksum {
        let mut out = Vec::new();
        put_label(&mut out, "DeterministicArtifactManifest.symbols.v1");
        let mut symbols = self.symbols.iter().collect::<Vec<_>>();
        symbols.sort_by(|left, right| {
            left.name
                .cmp(&right.name)
                .then_with(|| left.offset_bytes.cmp(&right.offset_bytes))
        });
        put_u64(&mut out, symbols.len() as u64);
        for symbol in symbols {
            symbol.encode(&mut out);
        }
        ArtifactChecksum::for_bytes(&out)
    }

    /// Bind the current trust_ir hardware vector contract row digest into the
    /// manifest metadata carried by install-gate and release artifacts.
    pub fn with_trust_ir_hardware_vector_contract_metadata(mut self) -> Self {
        bind_trust_ir_hardware_vector_contract_metadata(&mut self.metadata);
        self
    }

    /// Bind host-JIT target-feature profile metadata when this manifest targets
    /// the in-process x86_64 host JIT.
    pub fn with_host_jit_target_feature_profile_metadata(mut self) -> Self {
        bind_host_jit_target_feature_profile_metadata(&mut self);
        self
    }

    /// Verify the manifest schema name and numeric version.
    pub fn verify_schema(&self) -> Result<(), ArtifactContractError> {
        if self.schema == JIT_ARTIFACT_MANIFEST_SCHEMA
            && self.schema_version == JIT_ARTIFACT_MANIFEST_SCHEMA_VERSION
        {
            Ok(())
        } else {
            Err(ArtifactContractError::SchemaMismatch {
                expected_schema: JIT_ARTIFACT_MANIFEST_SCHEMA.to_owned(),
                expected_version: JIT_ARTIFACT_MANIFEST_SCHEMA_VERSION,
                actual_schema: self.schema.clone(),
                actual_version: self.schema_version,
            })
        }
    }

    /// Verify that this manifest matches an expected checksum.
    pub fn verify_checksum(&self, expected: ArtifactChecksum) -> Result<(), ArtifactContractError> {
        let actual = self.checksum();
        if actual == expected {
            Ok(())
        } else {
            Err(ArtifactContractError::ChecksumMismatch {
                component: "artifact_manifest".to_owned(),
                expected,
                actual,
            })
        }
    }

    /// Verify that the embedded target descriptor matches an expected checksum.
    pub fn verify_target_checksum(
        &self,
        expected: ArtifactChecksum,
    ) -> Result<(), ArtifactContractError> {
        let actual = self.target.checksum();
        if actual == expected {
            Ok(())
        } else {
            Err(ArtifactContractError::ChecksumMismatch {
                component: "target".to_owned(),
                expected,
                actual,
            })
        }
    }

    /// Verify that the embedded ABI descriptor matches an expected checksum.
    pub fn verify_abi_checksum(
        &self,
        expected: ArtifactChecksum,
    ) -> Result<(), ArtifactContractError> {
        let actual = self.abi.checksum();
        if actual == expected {
            Ok(())
        } else {
            Err(ArtifactContractError::ChecksumMismatch {
                component: "abi".to_owned(),
                expected,
                actual,
            })
        }
    }

    /// Verify that the embedded layout manifest matches an expected checksum.
    pub fn verify_layout_checksum(
        &self,
        expected: ArtifactChecksum,
    ) -> Result<(), ArtifactContractError> {
        let actual = self.layout.checksum();
        if actual == expected {
            Ok(())
        } else {
            Err(ArtifactContractError::ChecksumMismatch {
                component: "layout".to_owned(),
                expected,
                actual,
            })
        }
    }

    /// Verify that the embedded invalidation key matches an expected checksum.
    pub fn verify_invalidation_checksum(
        &self,
        expected: ArtifactChecksum,
    ) -> Result<(), ArtifactContractError> {
        let actual = self.invalidation.checksum();
        if actual == expected {
            Ok(())
        } else {
            Err(ArtifactContractError::ChecksumMismatch {
                component: "invalidation".to_owned(),
                expected,
                actual,
            })
        }
    }

    /// Return a symbol signature by name.
    pub fn symbol_signature(&self, symbol: &str) -> Option<&SymbolSignature> {
        self.symbols
            .iter()
            .find(|entry| entry.name == symbol)
            .map(|entry| &entry.signature)
    }

    /// Verify a typed wrapper's expected symbol signature.
    pub fn verify_symbol_signature(
        &self,
        symbol: &str,
        expected: &SymbolSignature,
    ) -> Result<(), ArtifactContractError> {
        match self.symbol_signature(symbol) {
            Some(actual) if actual == expected => Ok(()),
            Some(actual) => Err(ArtifactContractError::SignatureMismatch {
                symbol: symbol.to_owned(),
                expected: expected.clone(),
                actual: Some(actual.clone()),
            }),
            None => Err(ArtifactContractError::SignatureMismatch {
                symbol: symbol.to_owned(),
                expected: expected.clone(),
                actual: None,
            }),
        }
    }

    /// Verify proof or translation-validation evidence for typed symbol exposure.
    pub fn verify_proof_evidence(
        &self,
        evidence: &ProofEvidenceSummary,
    ) -> Result<(), ArtifactContractError> {
        if evidence.schema != JIT_PROOF_EVIDENCE_SUMMARY_SCHEMA
            || evidence.schema_version != JIT_PROOF_EVIDENCE_SUMMARY_SCHEMA_VERSION
        {
            return Err(ArtifactContractError::ProofEvidenceRejected {
                verifier: evidence.verifier.clone(),
                verdict: evidence.verdict.clone(),
                rejection_code: evidence.rejection_code.clone(),
                detail: format!(
                    "proof evidence schema mismatch: expected {} version {}, actual {} version {}",
                    JIT_PROOF_EVIDENCE_SUMMARY_SCHEMA,
                    JIT_PROOF_EVIDENCE_SUMMARY_SCHEMA_VERSION,
                    evidence.schema,
                    evidence.schema_version
                ),
            });
        }

        if evidence.verdict != ProofEvidenceVerdict::Verified || evidence.rejection_code.is_some() {
            return Err(ArtifactContractError::ProofEvidenceRejected {
                verifier: evidence.verifier.clone(),
                verdict: evidence.verdict.clone(),
                rejection_code: evidence.rejection_code.clone(),
                detail: "proof evidence was not verified".to_owned(),
            });
        }

        if !self.proof_policy.accepted_solvers.is_empty()
            && !self
                .proof_policy
                .accepted_solvers
                .iter()
                .any(|solver| solver == &evidence.verifier)
        {
            return Err(ArtifactContractError::ProofEvidenceRejected {
                verifier: evidence.verifier.clone(),
                verdict: ProofEvidenceVerdict::UnknownSolverError,
                rejection_code: Some(ProofEvidenceRejectionCode::UnknownSolverError),
                detail: format!(
                    "proof evidence verifier {} is not accepted by policy",
                    evidence.verifier
                ),
            });
        }

        self.verify_evidence_checksum("target", evidence.target_checksum, self.target.checksum())?;
        self.verify_evidence_checksum("abi", evidence.abi_checksum, self.abi.checksum())?;
        self.verify_evidence_checksum("layout", evidence.layout_checksum, self.layout.checksum())?;
        self.verify_evidence_checksum(
            "invalidation",
            evidence.invalidation_checksum,
            self.invalidation.checksum(),
        )?;
        self.verify_evidence_checksum(
            "proof_policy",
            evidence.proof_policy_checksum,
            self.proof_policy.checksum(),
        )?;
        self.verify_evidence_artifact_identity(evidence)?;
        self.verify_ty_native_fused_required_fact_metadata(evidence)
    }

    fn verify_evidence_artifact_identity(
        &self,
        evidence: &ProofEvidenceSummary,
    ) -> Result<(), ArtifactContractError> {
        if evidence.artifact_id.trim().is_empty()
            || evidence.native_payload_sha256.trim().is_empty()
            || evidence.proof_report_sha256.trim().is_empty()
            || !evidence.native_payload_sha256.starts_with("sha256:")
            || !evidence.proof_report_sha256.starts_with("sha256:")
            || evidence.manifest_checksum == ArtifactChecksum::new(0)
            || evidence.symbol_manifest_checksum == ArtifactChecksum::new(0)
        {
            return Err(ArtifactContractError::ProofEvidenceRejected {
                verifier: evidence.verifier.clone(),
                verdict: evidence.verdict.clone(),
                rejection_code: Some(ProofEvidenceRejectionCode::MissingRequiredFields),
                detail: "proof evidence is missing artifact identity fields".to_owned(),
            });
        }

        if evidence.artifact_id != self.artifact_id {
            return Err(ArtifactContractError::ProofEvidenceRejected {
                verifier: evidence.verifier.clone(),
                verdict: evidence.verdict.clone(),
                rejection_code: Some(ProofEvidenceRejectionCode::StaleEvidence),
                detail: format!(
                    "proof evidence artifact id mismatch: expected {}, actual {}",
                    evidence.artifact_id, self.artifact_id
                ),
            });
        }
        self.verify_evidence_checksum(
            "artifact_manifest",
            evidence.manifest_checksum,
            self.checksum(),
        )?;
        self.verify_evidence_checksum(
            "symbol_manifest",
            evidence.symbol_manifest_checksum,
            self.symbol_manifest_checksum(),
        )?;

        let Some(native_payload_sha256) = self.metadata.get("native_payload_sha256") else {
            return Err(ArtifactContractError::MissingManifestMetadata {
                key: "native_payload_sha256".to_owned(),
            });
        };
        if native_payload_sha256 != &evidence.native_payload_sha256 {
            return Err(ArtifactContractError::ProofEvidenceRejected {
                verifier: evidence.verifier.clone(),
                verdict: evidence.verdict.clone(),
                rejection_code: Some(ProofEvidenceRejectionCode::StaleEvidence),
                detail: format!(
                    "proof evidence native payload digest mismatch: expected {}, actual {}",
                    evidence.native_payload_sha256, native_payload_sha256
                ),
            });
        }

        Ok(())
    }

    fn verify_evidence_checksum(
        &self,
        component: &'static str,
        expected: ArtifactChecksum,
        actual: ArtifactChecksum,
    ) -> Result<(), ArtifactContractError> {
        if expected == actual {
            Ok(())
        } else {
            Err(ArtifactContractError::ProofEvidenceChecksumMismatch {
                component: component.to_owned(),
                expected,
                actual,
            })
        }
    }

    fn verify_ty_native_fused_required_fact_metadata(
        &self,
        evidence: &ProofEvidenceSummary,
    ) -> Result<(), ArtifactContractError> {
        if self.metadata.get("ty_manifest_schema").map(String::as_str)
            != Some(TY_NATIVE_FUSED_PARENT_LOOP_MANIFEST_SCHEMA)
        {
            return Ok(());
        }

        let mut saw_required_fact = false;
        for (manifest_key, evidence_key) in self
            .metadata
            .iter()
            .filter(|(key, _)| key.starts_with(TY_NATIVE_FUSED_REQUIRED_FACT_PREFIX))
        {
            saw_required_fact = true;
            let fact = manifest_key
                .strip_prefix(TY_NATIVE_FUSED_REQUIRED_FACT_PREFIX)
                .unwrap_or(manifest_key.as_str());
            if evidence_key.trim().is_empty()
                || evidence.metadata.get(evidence_key).map(String::as_str)
                    != Some(TY_NATIVE_FUSED_PROOF_FACT_VERIFIED)
            {
                return Err(ArtifactContractError::ProofEvidenceRejected {
                    verifier: evidence.verifier.clone(),
                    verdict: evidence.verdict.clone(),
                    rejection_code: Some(ProofEvidenceRejectionCode::MissingEvidence),
                    detail: format!(
                        "missing required TY native-fused proof fact {fact} ({evidence_key})"
                    ),
                });
            }
        }

        if !saw_required_fact {
            return Err(ArtifactContractError::ProofEvidenceRejected {
                verifier: evidence.verifier.clone(),
                verdict: evidence.verdict.clone(),
                rejection_code: Some(ProofEvidenceRejectionCode::MissingEvidence),
                detail: "TY native-fused manifest has no required proof fact metadata".to_owned(),
            });
        }

        Ok(())
    }

    /// Validate all descriptor checks required for a typed symbol lookup.
    pub fn validate_symbol_lookup(
        &self,
        contract: &SymbolLookupContract,
    ) -> Result<(), ArtifactContractError> {
        self.verify_schema()?;
        if self.proof_policy.requires_evidence() || contract.require_proof_evidence {
            let expected =
                contract
                    .manifest_checksum
                    .ok_or(ArtifactContractError::MissingProofEvidence {
                        rejection_code: ProofEvidenceRejectionCode::MissingRequiredFields,
                    })?;
            self.verify_checksum(expected)?;
        } else if let Some(expected) = contract.manifest_checksum {
            self.verify_checksum(expected)?;
        }
        self.verify_target_checksum(contract.target_checksum)?;
        self.verify_abi_checksum(contract.abi_checksum)?;
        self.verify_layout_checksum(contract.layout_checksum)?;
        if let Some(expected) = contract.invalidation_checksum {
            self.verify_invalidation_checksum(expected)?;
        }
        if self.proof_policy.requires_evidence() || contract.require_proof_evidence {
            match &contract.proof_evidence {
                Some(evidence) => self.verify_proof_evidence(evidence)?,
                None => {
                    return Err(ArtifactContractError::MissingProofEvidence {
                        rejection_code: ProofEvidenceRejectionCode::MissingEvidence,
                    });
                }
            }
        }
        self.verify_symbol_signature(&contract.symbol, &contract.signature)
    }

    /// Validate a symbol lookup and return a typed handle for a non-null code pointer.
    pub fn typed_symbol<'artifact, F: Copy>(
        &'artifact self,
        contract: &SymbolLookupContract,
        ptr: *const u8,
    ) -> Result<TypedSymbol<'artifact, F>, ArtifactContractError> {
        self.validate_symbol_lookup(contract)?;
        let ptr = NonNull::new(ptr.cast_mut()).ok_or_else(|| {
            ArtifactContractError::NullSymbolPointer {
                symbol: contract.symbol.clone(),
            }
        })?;
        Ok(TypedSymbol {
            ptr: ptr.cast(),
            symbol: contract.symbol.clone(),
            signature: contract.signature.clone(),
            artifact_checksum: self.checksum(),
            _marker: PhantomData,
        })
    }
}

/// Return deterministic manifest metadata for the current trust_ir hardware vector
/// contract rows used by Trust Codegen product artifacts.
pub fn trust_ir_hardware_vector_contract_metadata_entries() -> BTreeMap<String, String> {
    BTreeMap::from([
        (
            TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA_KEY.to_owned(),
            TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA.to_owned(),
        ),
        (
            TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA_VERSION_KEY.to_owned(),
            TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA_VERSION.to_string(),
        ),
        (
            TRUST_IR_HARDWARE_VECTOR_CONTRACT_SET_NAME_KEY.to_owned(),
            TRUST_IR_HARDWARE_VECTOR_CONTRACT_SET_NAME.to_owned(),
        ),
        (
            TRUST_IR_HARDWARE_VECTOR_CONTRACT_TARGET_FAMILY_KEY.to_owned(),
            TRUST_IR_HARDWARE_VECTOR_CONTRACT_TARGET_FAMILY.to_owned(),
        ),
        (
            TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_ROW_COUNT_KEY.to_owned(),
            trust_ir::chc_x86_hardware_vector_contract_manifest_row_count().to_string(),
        ),
        (
            TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SHA256_KEY.to_owned(),
            trust_ir::chc_x86_hardware_vector_contract_manifest_sha256(),
        ),
    ])
}

/// Return the pinned trust_ir CHC x86 hardware-vector manifest row count.
pub fn trust_ir_hardware_vector_contract_manifest_row_count() -> usize {
    trust_ir::chc_x86_hardware_vector_contract_manifest_row_count()
}

/// Return the pinned trust_ir CHC x86 hardware-vector manifest digest.
pub fn trust_ir_hardware_vector_contract_manifest_sha256() -> String {
    trust_ir::chc_x86_hardware_vector_contract_manifest_sha256()
}

/// Insert current trust_ir hardware vector contract metadata into a manifest map.
pub fn bind_trust_ir_hardware_vector_contract_metadata(metadata: &mut BTreeMap<String, String>) {
    metadata.extend(trust_ir_hardware_vector_contract_metadata_entries());
}

/// Return true when a manifest target is the in-process x86_64 host JIT target.
pub fn target_descriptor_is_x86_64_host_jit(target: &TargetDescriptor) -> bool {
    cfg!(target_arch = "x86_64")
        && target.architecture == TargetArchitecture::X86_64
        && target.operating_system == TargetOperatingSystem::host()
        && target.pointer_width_bits == 64
}

/// Return deterministic host-JIT target-feature profile metadata for an x86_64
/// host manifest.
pub fn host_jit_target_feature_profile_metadata_entries(
    manifest: &DeterministicArtifactManifest,
) -> Option<BTreeMap<String, String>> {
    if !target_descriptor_is_x86_64_host_jit(&manifest.target) {
        return None;
    }

    let target_features = join_metadata_list(&manifest.target.features);
    let detected_host_features = join_metadata_list(&detected_x86_64_host_features());
    let current_policy = if manifest.target.features.is_empty() {
        "generic-baseline"
    } else {
        "manifest-target-features"
    };
    let host_policy = if detected_host_features.is_empty() {
        "unavailable"
    } else {
        "detected-host-bits"
    };

    let mut entries = BTreeMap::from([
        (
            HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA_KEY.to_owned(),
            HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA.to_owned(),
        ),
        (
            HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA_VERSION_KEY.to_owned(),
            HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA_VERSION.to_string(),
        ),
        (
            HOST_JIT_TARGET_FEATURE_PROFILE_TARGET_TRIPLE_KEY.to_owned(),
            manifest.target.triple.clone(),
        ),
        (
            "trust-cg.host_jit.target_feature_profile.target_architecture".to_owned(),
            manifest.target.architecture.as_str().to_owned(),
        ),
        (
            "trust-cg.host_jit.target_feature_profile.target_operating_system".to_owned(),
            manifest.target.operating_system.as_str().to_owned(),
        ),
        (
            "trust-cg.host_jit.target_feature_profile.target_pointer_width_bits".to_owned(),
            manifest.target.pointer_width_bits.to_string(),
        ),
        (
            "trust-cg.host_jit.target_feature_profile.target_cpu".to_owned(),
            manifest
                .target
                .cpu
                .clone()
                .unwrap_or_else(|| "unspecified".to_owned()),
        ),
        (
            HOST_JIT_TARGET_FEATURE_PROFILE_TARGET_FEATURES_KEY.to_owned(),
            target_features,
        ),
        (
            "trust-cg.host_jit.target_feature_profile.generic_policy".to_owned(),
            "x86_64-v1-baseline".to_owned(),
        ),
        (
            HOST_JIT_TARGET_FEATURE_PROFILE_CURRENT_POLICY_KEY.to_owned(),
            current_policy.to_owned(),
        ),
        (
            "trust-cg.host_jit.target_feature_profile.host_policy".to_owned(),
            host_policy.to_owned(),
        ),
        (
            HOST_JIT_TARGET_FEATURE_PROFILE_DETECTED_HOST_FEATURES_KEY.to_owned(),
            detected_host_features,
        ),
        (
            "trust-cg.host_jit.target_feature_profile.target_checksum".to_owned(),
            manifest.target.checksum().to_string(),
        ),
        (
            "trust-cg.host_jit.target_feature_profile.compiler_crate_version".to_owned(),
            env!("CARGO_PKG_VERSION").to_owned(),
        ),
        (
            "trust-cg.host_jit.target_feature_profile.compiler_profile".to_owned(),
            option_env!("PROFILE").unwrap_or("unknown").to_owned(),
        ),
        (
            "trust-cg.host_jit.target_feature_profile.compiler_opt_level".to_owned(),
            option_env!("OPT_LEVEL").unwrap_or("unknown").to_owned(),
        ),
        (
            "trust-cg.host_jit.target_feature_profile.source_fingerprint".to_owned(),
            manifest.invalidation.source_fingerprint.clone(),
        ),
        (
            "trust-cg.host_jit.target_feature_profile.compiler_fingerprint".to_owned(),
            manifest.invalidation.compiler_fingerprint.clone(),
        ),
    ]);
    let digest = host_jit_target_feature_profile_sha256(&entries);
    entries.insert(
        HOST_JIT_TARGET_FEATURE_PROFILE_SHA256_KEY.to_owned(),
        digest,
    );
    Some(entries)
}

/// Insert host-JIT target-feature profile metadata into a manifest when it is in
/// scope for x86_64 host JIT evidence.
pub fn bind_host_jit_target_feature_profile_metadata(manifest: &mut DeterministicArtifactManifest) {
    if let Some(entries) = host_jit_target_feature_profile_metadata_entries(manifest) {
        manifest.metadata.extend(entries);
    }
}

fn host_jit_target_feature_profile_sha256(entries: &BTreeMap<String, String>) -> String {
    let mut out = Vec::new();
    put_str(&mut out, HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA);
    put_u32(&mut out, HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA_VERSION);
    for (key, value) in entries {
        put_str(&mut out, key);
        put_str(&mut out, value);
    }
    format!("sha256:{}", sha256_hex(&out))
}

fn join_metadata_list(values: &[String]) -> String {
    values.join(",")
}

fn detected_x86_64_host_features() -> Vec<String> {
    #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
    let features = Vec::new();

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    let mut features = Vec::new();

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    {
        if std::arch::is_x86_feature_detected!("sse2") {
            features.push("sse2".to_owned());
        }
        if std::arch::is_x86_feature_detected!("sse3") {
            features.push("sse3".to_owned());
        }
        if std::arch::is_x86_feature_detected!("ssse3") {
            features.push("ssse3".to_owned());
        }
        if std::arch::is_x86_feature_detected!("sse4.1") {
            features.push("sse4.1".to_owned());
        }
        if std::arch::is_x86_feature_detected!("sse4.2") {
            features.push("sse4.2".to_owned());
        }
        if std::arch::is_x86_feature_detected!("popcnt") {
            features.push("popcnt".to_owned());
        }
        if std::arch::is_x86_feature_detected!("aes") {
            features.push("aes".to_owned());
        }
        if std::arch::is_x86_feature_detected!("pclmulqdq") {
            features.push("pclmulqdq".to_owned());
        }
        if std::arch::is_x86_feature_detected!("avx") {
            features.push("avx".to_owned());
        }
        if std::arch::is_x86_feature_detected!("avx2") {
            features.push("avx2".to_owned());
        }
        if std::arch::is_x86_feature_detected!("fma") {
            features.push("fma".to_owned());
        }
        if std::arch::is_x86_feature_detected!("bmi1") {
            features.push("bmi1".to_owned());
        }
        if std::arch::is_x86_feature_detected!("bmi2") {
            features.push("bmi2".to_owned());
        }
    }

    features
}

/// Versioned artifact manifest name used by product integrations.
pub type ArtifactManifestV1 = DeterministicArtifactManifest;

/// Product-facing ABI descriptor alias.
pub type ArtifactAbiDescriptor = AbiDescriptor;

/// Product-facing target descriptor alias.
pub type ArtifactTargetDescriptor = TargetDescriptor;

/// Product-facing layout manifest alias.
pub type ArtifactLayoutManifest = LayoutManifest;

/// Product-facing invalidation key alias.
pub type ArtifactInvalidationKey = InvalidationKey;

/// Product-facing proof policy alias.
pub type ArtifactProofPolicy = ProofPolicy;

/// Typed mismatch errors returned by artifact contract validation.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum ArtifactContractError {
    /// The manifest schema name or version did not match the supported contract.
    #[error(
        "artifact contract schema mismatch: expected {expected_schema} version {expected_version}, actual {actual_schema} version {actual_version}"
    )]
    SchemaMismatch {
        /// Expected schema name.
        expected_schema: String,
        /// Expected schema version.
        expected_version: u32,
        /// Actual schema name.
        actual_schema: String,
        /// Actual schema version.
        actual_version: u32,
    },
    /// A checksum did not match for a named manifest component.
    #[error(
        "artifact contract checksum mismatch for {component}: expected {expected}, actual {actual}"
    )]
    ChecksumMismatch {
        /// Component that failed validation.
        component: String,
        /// Expected checksum.
        expected: ArtifactChecksum,
        /// Actual checksum.
        actual: ArtifactChecksum,
    },
    /// A callable symbol signature did not match the typed wrapper.
    #[error(
        "artifact contract signature mismatch for symbol {symbol}: expected {expected:?}, actual {actual:?}"
    )]
    SignatureMismatch {
        /// Symbol that failed validation.
        symbol: String,
        /// Expected signature.
        expected: SymbolSignature,
        /// Actual signature, or `None` when the symbol was absent.
        actual: Option<SymbolSignature>,
    },
    /// A typed symbol lookup was asked to expose a null code pointer.
    #[error("artifact contract null symbol pointer for {symbol}")]
    NullSymbolPointer {
        /// Symbol whose validated pointer was null.
        symbol: String,
    },
    /// Required proof or translation-validation evidence was not attached.
    #[error("artifact contract missing proof evidence: {}", rejection_code.as_str())]
    MissingProofEvidence {
        /// Stable rejection code for missing proof evidence.
        rejection_code: ProofEvidenceRejectionCode,
    },
    /// Proof or translation-validation evidence did not verify.
    #[error(
        "artifact contract proof evidence rejected by {verifier}: verdict {}, rejection {rejection_code:?}: {detail}",
        verdict.as_str()
    )]
    ProofEvidenceRejected {
        /// Verifier or translation-validation engine name.
        verifier: String,
        /// Stable evidence verdict.
        verdict: ProofEvidenceVerdict,
        /// Stable rejection code.
        rejection_code: Option<ProofEvidenceRejectionCode>,
        /// Human-readable detail for logs.
        detail: String,
    },
    /// Proof evidence was verified for a different artifact component.
    #[error(
        "artifact contract proof evidence checksum mismatch for {component}: expected {expected}, actual {actual}"
    )]
    ProofEvidenceChecksumMismatch {
        /// Component that failed evidence validation.
        component: String,
        /// Checksum carried by the evidence.
        expected: ArtifactChecksum,
        /// Actual manifest component checksum.
        actual: ArtifactChecksum,
    },
    /// Required manifest metadata for a typed kernel contract was absent.
    #[error("artifact contract missing manifest metadata key {key}")]
    MissingManifestMetadata {
        /// Missing metadata key.
        key: String,
    },
    /// The compiler-derived installed-payload binding was missing, malformed,
    /// or did not match the live executable image presented for callable
    /// exposure.
    #[error("artifact contract installed payload binding mismatch: {detail}")]
    InstalledPayloadBindingMismatch {
        /// Exact fail-closed mismatch detail.
        detail: String,
    },
}

trait CanonicalEncode {
    fn encode(&self, out: &mut Vec<u8>);
}

fn checksum_of<T: CanonicalEncode>(value: &T) -> ArtifactChecksum {
    ArtifactChecksum::for_bytes(&canonical_bytes_of(value))
}

fn canonical_bytes_of<T: CanonicalEncode>(value: &T) -> Vec<u8> {
    let mut out = Vec::new();
    value.encode(&mut out);
    out
}

fn strings<const N: usize>(items: [&str; N]) -> Vec<String> {
    items.into_iter().map(str::to_owned).collect()
}

fn normalize_string_set(items: impl IntoIterator<Item = impl Into<String>>) -> Vec<String> {
    let mut values = items.into_iter().map(Into::into).collect::<Vec<_>>();
    values.sort();
    values.dedup();
    values
}

fn put_u8(out: &mut Vec<u8>, value: u8) {
    out.push(value);
}

fn put_u16(out: &mut Vec<u8>, value: u16) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_u128(out: &mut Vec<u8>, value: u128) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_bool(out: &mut Vec<u8>, value: bool) {
    put_u8(out, u8::from(value));
}

fn put_str(out: &mut Vec<u8>, value: &str) {
    put_u64(out, value.len() as u64);
    out.extend_from_slice(value.as_bytes());
}

fn put_label(out: &mut Vec<u8>, label: &str) {
    put_str(out, label);
}

fn put_option_u64(out: &mut Vec<u8>, value: Option<u64>) {
    match value {
        Some(value) => {
            put_bool(out, true);
            put_u64(out, value);
        }
        None => put_bool(out, false),
    }
}

fn put_option_string(out: &mut Vec<u8>, value: &Option<String>) {
    match value {
        Some(value) => {
            put_bool(out, true);
            put_str(out, value);
        }
        None => put_bool(out, false),
    }
}

fn put_option_checksum(out: &mut Vec<u8>, value: Option<ArtifactChecksum>) {
    match value {
        Some(value) => {
            put_bool(out, true);
            value.encode(out);
        }
        None => put_bool(out, false),
    }
}

fn put_strings(out: &mut Vec<u8>, values: &[String]) {
    put_u64(out, values.len() as u64);
    for value in values {
        put_str(out, value);
    }
}

fn put_string_set(out: &mut Vec<u8>, values: &[String]) {
    let values = normalize_string_set(values.iter().cloned());
    put_strings(out, &values);
}

fn put_metadata(out: &mut Vec<u8>, metadata: &BTreeMap<String, String>) {
    put_u64(out, metadata.len() as u64);
    for (key, value) in metadata {
        put_str(out, key);
        put_str(out, value);
    }
}

impl CanonicalEncode for ArtifactChecksum {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "ArtifactChecksum");
        put_u128(out, self.0);
    }
}

impl CanonicalEncode for TargetArchitecture {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "TargetArchitecture");
        match self {
            Self::Aarch64 | Self::X86_64 | Self::Riscv64 => put_str(out, self.as_str()),
            Self::Other(value) => {
                put_str(out, "other");
                put_str(out, value);
            }
        }
    }
}

impl CanonicalEncode for TargetOperatingSystem {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "TargetOperatingSystem");
        match self {
            Self::Macos | Self::Linux | Self::Windows | Self::Unknown => {
                put_str(out, self.as_str())
            }
            Self::Other(value) => {
                put_str(out, "other");
                put_str(out, value);
            }
        }
    }
}

impl CanonicalEncode for Endianness {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "Endianness");
        put_str(out, self.as_str());
    }
}

impl CanonicalEncode for TargetDescriptor {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "TargetDescriptor.v1");
        put_str(out, &self.triple);
        self.architecture.encode(out);
        self.operating_system.encode(out);
        put_u16(out, self.pointer_width_bits);
        self.endianness.encode(out);
        put_option_string(out, &self.cpu);
        put_string_set(out, &self.features);
    }
}

impl CanonicalEncode for ExecutableMemoryOwner {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "ExecutableMemoryOwner");
        match self {
            Self::TrustCg => put_str(out, "trust-cg"),
            Self::Downstream(value) => {
                put_str(out, "downstream");
                put_str(out, value);
            }
            Self::Unspecified => put_str(out, "unspecified"),
        }
    }
}

impl CanonicalEncode for TeardownPolicy {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "TeardownPolicy");
        match self {
            Self::ProcessLifetime => put_str(out, "process_lifetime"),
            Self::RefCounted => put_str(out, "ref_counted"),
            Self::Downstream(value) => {
                put_str(out, "downstream");
                put_str(out, value);
            }
            Self::Unspecified => put_str(out, "unspecified"),
        }
    }
}

impl CanonicalEncode for AbiVarargsPolicy {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "AbiVarargsPolicy");
        match self {
            Self::Unsupported => put_str(out, "unsupported"),
            Self::C => put_str(out, "c"),
            Self::Other(value) => {
                put_str(out, "other");
                put_str(out, value);
            }
        }
    }
}

impl CanonicalEncode for AbiDescriptor {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "AbiDescriptor.v1");
        put_str(out, &self.name);
        put_str(out, &self.calling_convention);
        put_u16(out, self.pointer_width_bits);
        put_u16(out, self.stack_alignment_bytes);
        put_u16(out, self.red_zone_bytes);
        put_u16(out, self.shadow_space_bytes);
        put_strings(out, &self.integer_argument_registers);
        put_strings(out, &self.float_argument_registers);
        put_strings(out, &self.integer_return_registers);
        put_strings(out, &self.float_return_registers);
        put_strings(out, &self.callee_saved_registers);
        self.executable_memory_owner.encode(out);
        self.teardown_policy.encode(out);
        self.varargs.encode(out);
    }
}

impl CanonicalEncode for AbiValueKind {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "AbiValueKind");
        match self {
            Self::I1 => put_str(out, "i1"),
            Self::I8 => put_str(out, "i8"),
            Self::I16 => put_str(out, "i16"),
            Self::I32 => put_str(out, "i32"),
            Self::I64 => put_str(out, "i64"),
            Self::USize => put_str(out, "usize"),
            Self::F32 => put_str(out, "f32"),
            Self::F64 => put_str(out, "f64"),
            Self::Ptr => put_str(out, "ptr"),
            Self::Bytes {
                size_bytes,
                alignment_bytes,
            } => {
                put_str(out, "bytes");
                put_u32(out, *size_bytes);
                put_u32(out, *alignment_bytes);
            }
            Self::Void => put_str(out, "void"),
            Self::Other(value) => {
                put_str(out, "other");
                put_str(out, value);
            }
        }
    }
}

impl CanonicalEncode for AbiValue {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "AbiValue");
        self.kind.encode(out);
        put_bool(out, self.nullable);
    }
}

impl CanonicalEncode for SymbolSignature {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "SymbolSignature.v1");
        put_str(out, &self.abi);
        put_u64(out, self.params.len() as u64);
        for param in &self.params {
            param.encode(out);
        }
        put_u64(out, self.returns.len() as u64);
        for value in &self.returns {
            value.encode(out);
        }
        put_bool(out, self.variadic);
    }
}

impl CanonicalEncode for FieldLayout {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "FieldLayout");
        put_str(out, &self.name);
        put_u64(out, self.offset_bytes);
        put_u64(out, self.size_bytes);
        put_u32(out, self.alignment_bytes);
    }
}

impl CanonicalEncode for RecordLayout {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "RecordLayout");
        put_str(out, &self.name);
        put_str(out, &self.representation);
        put_u64(out, self.size_bytes);
        put_u32(out, self.alignment_bytes);
        let mut fields = self.fields.iter().collect::<Vec<_>>();
        fields.sort_by(|left, right| {
            left.offset_bytes
                .cmp(&right.offset_bytes)
                .then_with(|| left.name.cmp(&right.name))
        });
        put_u64(out, fields.len() as u64);
        for field in fields {
            field.encode(out);
        }
    }
}

impl CanonicalEncode for PointerBounds {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "PointerBounds");
        match self {
            Self::Unbounded => put_str(out, "unbounded"),
            Self::ByteRange {
                start_bytes,
                length_bytes,
            } => {
                put_str(out, "byte_range");
                put_u64(out, *start_bytes);
                put_u64(out, *length_bytes);
            }
            Self::Symbol(value) => {
                put_str(out, "symbol");
                put_str(out, value);
            }
        }
    }
}

impl CanonicalEncode for Mutability {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "Mutability");
        match self {
            Self::Immutable => put_str(out, "immutable"),
            Self::Mutable => put_str(out, "mutable"),
        }
    }
}

impl CanonicalEncode for AliasPolicy {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "AliasPolicy");
        match self {
            Self::Exclusive => put_str(out, "exclusive"),
            Self::SharedReadOnly => put_str(out, "shared_read_only"),
            Self::SharedMutable => put_str(out, "shared_mutable"),
            Self::Unknown => put_str(out, "unknown"),
            Self::Other(value) => {
                put_str(out, "other");
                put_str(out, value);
            }
        }
    }
}

impl CanonicalEncode for SliceLayout {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "SliceLayout");
        put_str(out, &self.name);
        put_u64(out, self.element_size_bytes);
        put_u32(out, self.element_alignment_bytes);
        put_u64(out, self.stride_bytes);
        put_option_u64(out, self.length);
        self.bounds.encode(out);
        self.mutability.encode(out);
        self.alias_policy.encode(out);
    }
}

impl CanonicalEncode for PointerLayout {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "PointerLayout");
        put_str(out, &self.name);
        self.bounds.encode(out);
        self.mutability.encode(out);
        self.alias_policy.encode(out);
    }
}

impl CanonicalEncode for SymbolLayout {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "SymbolLayout");
        put_str(out, &self.name);
        put_str(out, &self.section);
        put_option_u64(out, self.offset_bytes);
        put_u64(out, self.size_bytes);
        put_u32(out, self.alignment_bytes);
    }
}

impl CanonicalEncode for LayoutManifest {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "LayoutManifest.v1");
        put_u8(out, self.pointer_size_bytes);
        put_u8(out, self.pointer_alignment_bytes);
        self.endianness.encode(out);
        put_u16(out, self.stack_alignment_bytes);

        let mut records = self.records.iter().collect::<Vec<_>>();
        records.sort_by(|left, right| left.name.cmp(&right.name));
        put_u64(out, records.len() as u64);
        for record in records {
            record.encode(out);
        }

        let mut slices = self.slices.iter().collect::<Vec<_>>();
        slices.sort_by(|left, right| left.name.cmp(&right.name));
        put_u64(out, slices.len() as u64);
        for slice in slices {
            slice.encode(out);
        }

        let mut pointers = self.pointers.iter().collect::<Vec<_>>();
        pointers.sort_by(|left, right| left.name.cmp(&right.name));
        put_u64(out, pointers.len() as u64);
        for pointer in pointers {
            pointer.encode(out);
        }

        let mut symbols = self.symbols.iter().collect::<Vec<_>>();
        symbols.sort_by(|left, right| left.name.cmp(&right.name));
        put_u64(out, symbols.len() as u64);
        for symbol in symbols {
            symbol.encode(out);
        }

        put_option_string(out, &self.wrapper_identity);
        put_metadata(out, &self.metadata);
    }
}

impl CanonicalEncode for InvalidationKey {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "InvalidationKey.v1");
        put_str(out, &self.source_fingerprint);
        put_str(out, &self.compiler_fingerprint);
        self.target_checksum.encode(out);
        self.abi_checksum.encode(out);
        self.layout_checksum.encode(out);
        self.proof_policy_checksum.encode(out);
        put_u64(out, self.generation);
        put_metadata(out, &self.extra);
    }
}

impl CanonicalEncode for ProofMode {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "ProofMode");
        match self {
            Self::Disabled => put_str(out, "disabled"),
            Self::AuditOnly => put_str(out, "audit_only"),
            Self::RequireCertificates => put_str(out, "require_certificates"),
            Self::RequireReplay => put_str(out, "require_replay"),
        }
    }
}

impl CanonicalEncode for ProofPolicy {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "ProofPolicy.v1");
        self.mode.encode(out);
        put_bool(out, self.require_jit_certificate);
        put_bool(out, self.require_layout_evidence);
        put_bool(out, self.require_abi_evidence);
        put_string_set(out, &self.accepted_solvers);
        put_option_u64(out, self.max_replay_age_generations);
        // Strictly additive tail. A policy that leaves `required_strength` at
        // its default encodes exactly as it did before the field existed, so
        // every previously-computed policy checksum — and every invalidation
        // key and manifest checksum derived from one — is unchanged.
        if self.required_strength != RequiredEvidenceStrength::Any {
            put_label(out, "ProofPolicy.required_strength.v1");
            put_str(out, self.required_strength.as_str());
        }
    }
}

impl CanonicalEncode for EvidenceStrength {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "EvidenceStrength");
        put_str(out, self.as_str());
        match self {
            Self::Statistical { sample_count } => put_u64(out, *sample_count),
            Self::Formal { solver } => put_str(out, solver),
            Self::NotReported | Self::NotRun | Self::Exhaustive => {}
        }
    }
}

impl CanonicalEncode for AcceptedAssumption {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "AcceptedAssumption");
        put_str(out, &self.id);
        put_str(out, &self.detail);
    }
}

impl CanonicalEncode for ProofEvidenceVerdict {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "ProofEvidenceVerdict");
        put_str(out, self.as_str());
    }
}

impl CanonicalEncode for ProofEvidenceRejectionCode {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "ProofEvidenceRejectionCode");
        put_str(out, self.as_str());
    }
}

impl CanonicalEncode for ProofEvidenceSummary {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "ProofEvidenceSummary.v1");
        put_str(out, &self.schema);
        put_u32(out, self.schema_version);
        put_str(out, &self.verifier);
        self.verdict.encode(out);
        match &self.rejection_code {
            Some(code) => {
                put_bool(out, true);
                code.encode(out);
            }
            None => put_bool(out, false),
        }
        self.target_checksum.encode(out);
        self.abi_checksum.encode(out);
        self.layout_checksum.encode(out);
        self.invalidation_checksum.encode(out);
        self.proof_policy_checksum.encode(out);
        put_str(out, &self.artifact_id);
        self.manifest_checksum.encode(out);
        put_str(out, &self.native_payload_sha256);
        put_str(out, &self.proof_report_sha256);
        self.symbol_manifest_checksum.encode(out);
        put_metadata(out, &self.metadata);
        // Strictly additive tail (see JIT_PROOF_EVIDENCE_CHANNEL_SCHEMA): a
        // summary that reports neither a strength nor an assumption encodes
        // byte-for-byte as it did before the channel existed, so no existing
        // evidence checksum moves.
        if self.strength != EvidenceStrength::NotReported || !self.accepted_assumptions.is_empty() {
            put_label(out, JIT_PROOF_EVIDENCE_CHANNEL_SCHEMA);
            put_u32(out, JIT_PROOF_EVIDENCE_CHANNEL_SCHEMA_VERSION);
            self.strength.encode(out);
            let mut assumptions = self.accepted_assumptions.iter().collect::<Vec<_>>();
            assumptions.sort();
            put_u64(out, assumptions.len() as u64);
            for assumption in assumptions {
                assumption.encode(out);
            }
        }
    }
}

impl CanonicalEncode for JitArtifactKind {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "JitArtifactKind");
        match self {
            Self::Object => put_str(out, "object"),
            Self::ExecutableMemory => put_str(out, "executable_memory"),
            Self::Other(value) => {
                put_str(out, "other");
                put_str(out, value);
            }
        }
    }
}

impl CanonicalEncode for SymbolVisibility {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "SymbolVisibility");
        match self {
            Self::Exported => put_str(out, "exported"),
            Self::Internal => put_str(out, "internal"),
            Self::Imported => put_str(out, "imported"),
        }
    }
}

impl CanonicalEncode for ArtifactSymbol {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "ArtifactSymbol");
        put_str(out, &self.name);
        self.visibility.encode(out);
        self.signature.encode(out);
        put_option_u64(out, self.offset_bytes);
        put_option_checksum(out, self.checksum);
    }
}

impl CanonicalEncode for ArtifactSectionKind {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "ArtifactSectionKind");
        match self {
            Self::Text => put_str(out, "text"),
            Self::Rodata => put_str(out, "rodata"),
            Self::Data => put_str(out, "data"),
            Self::Unwind => put_str(out, "unwind"),
            Self::Other(value) => {
                put_str(out, "other");
                put_str(out, value);
            }
        }
    }
}

impl CanonicalEncode for ArtifactSection {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "ArtifactSection");
        put_str(out, &self.name);
        self.kind.encode(out);
        put_u64(out, self.size_bytes);
        put_u32(out, self.alignment_bytes);
        put_option_checksum(out, self.checksum);
    }
}

impl CanonicalEncode for KernelArtifactKind {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "KernelArtifactKind");
        match self {
            Self::SuccessorKernel | Self::PredicateKernel => put_str(out, self.as_str()),
            Self::Other(value) => {
                put_str(out, "other");
                put_str(out, value);
            }
        }
    }
}

impl CanonicalEncode for KernelStateDomain {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "KernelStateDomain");
        match self {
            Self::Finite {
                variable_count,
                max_state_count,
            } => {
                put_str(out, "finite");
                put_u32(out, *variable_count);
                put_option_u64(out, *max_state_count);
            }
            Self::BoundedByInvariant { invariant } => {
                put_str(out, "bounded_by_invariant");
                put_str(out, invariant);
            }
            Self::Unknown => put_str(out, "unknown"),
        }
    }
}

impl CanonicalEncode for KernelArtifactContract {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "KernelArtifactContract.v1");
        put_str(out, &self.schema);
        put_u32(out, self.schema_version);
        put_str(out, &self.consumer);
        self.kind.encode(out);
        put_str(out, &self.entry_symbol);
        self.signature.encode(out);
        self.target_checksum.encode(out);
        self.abi_checksum.encode(out);
        self.layout_checksum.encode(out);
        self.proof_policy_checksum.encode(out);
        self.state_domain.encode(out);
        self.semantic_checksum.encode(out);
        put_string_set(out, &self.required_manifest_metadata);
        put_metadata(out, &self.metadata);
    }
}

impl CanonicalEncode for DeterministicArtifactManifest {
    fn encode(&self, out: &mut Vec<u8>) {
        put_label(out, "DeterministicArtifactManifest.v1");
        put_str(out, &self.schema);
        put_u32(out, self.schema_version);
        put_str(out, &self.artifact_id);
        self.kind.encode(out);
        self.target.encode(out);
        self.abi.encode(out);
        self.layout.encode(out);
        self.invalidation.encode(out);
        self.proof_policy.encode(out);

        let mut symbols = self.symbols.iter().collect::<Vec<_>>();
        symbols.sort_by(|left, right| {
            left.name
                .cmp(&right.name)
                .then_with(|| left.offset_bytes.cmp(&right.offset_bytes))
        });
        put_u64(out, symbols.len() as u64);
        for symbol in symbols {
            symbol.encode(out);
        }

        let mut sections = self.sections.iter().collect::<Vec<_>>();
        sections.sort_by(|left, right| left.name.cmp(&right.name));
        put_u64(out, sections.len() as u64);
        for section in sections {
            section.encode(out);
        }

        put_metadata(out, &self.metadata);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_microsoft_x64_abi(abi: &AbiDescriptor) {
        assert_eq!(abi.name, "trust-cg-x86_64-windows");
        assert_eq!(abi.calling_convention, "windows_x64");
        assert_eq!(abi.red_zone_bytes, 0);
        assert_eq!(abi.shadow_space_bytes, 32);
        assert_eq!(
            abi.integer_argument_registers,
            strings(["rcx", "rdx", "r8", "r9"])
        );
        assert_eq!(
            abi.float_argument_registers,
            strings(["xmm0", "xmm1", "xmm2", "xmm3"])
        );
        assert!(abi.callee_saved_registers.contains(&"rdi".to_owned()));
        assert!(abi.callee_saved_registers.contains(&"xmm15".to_owned()));
    }

    fn assert_sysv_amd64_abi(abi: &AbiDescriptor) {
        assert_eq!(abi.calling_convention, "sysv_amd64");
        assert_eq!(abi.red_zone_bytes, 128);
        assert_eq!(abi.shadow_space_bytes, 0);
        assert_eq!(
            abi.integer_argument_registers,
            strings(["rdi", "rsi", "rdx", "rcx", "r8", "r9"])
        );
    }

    #[test]
    fn windows_x86_64_abi_descriptor_uses_microsoft_x64() {
        let abi =
            AbiDescriptor::for_trust_cg_target_os(Target::X86_64, TargetOperatingSystem::Windows);

        assert_microsoft_x64_abi(&abi);
    }

    #[test]
    fn unix_x86_64_abi_descriptor_remains_sysv() {
        let abi =
            AbiDescriptor::for_trust_cg_target_os(Target::X86_64, TargetOperatingSystem::Linux);

        assert_sysv_amd64_abi(&abi);
    }

    #[test]
    fn host_operating_system_matches_compiled_host() {
        let host_os = TargetOperatingSystem::host();

        #[cfg(target_os = "windows")]
        assert_eq!(host_os, TargetOperatingSystem::Windows);

        #[cfg(target_os = "linux")]
        assert_eq!(host_os, TargetOperatingSystem::Linux);

        #[cfg(target_os = "macos")]
        assert_eq!(host_os, TargetOperatingSystem::Macos);

        #[cfg(not(any(target_os = "windows", target_os = "linux", target_os = "macos")))]
        assert_eq!(host_os, TargetOperatingSystem::Unknown);
    }

    #[test]
    fn host_x86_64_abi_descriptor_uses_host_operating_system_contract() {
        let host_os = TargetOperatingSystem::host();
        let abi = AbiDescriptor::for_trust_cg_target_os(Target::X86_64, host_os.clone());

        if cfg!(target_os = "windows") {
            assert_eq!(host_os, TargetOperatingSystem::Windows);
            assert_microsoft_x64_abi(&abi);
        } else {
            assert_ne!(host_os, TargetOperatingSystem::Windows);
            assert_sysv_amd64_abi(&abi);
            assert_eq!(abi, AbiDescriptor::for_trust_cg_target(Target::X86_64));
        }
    }
}
