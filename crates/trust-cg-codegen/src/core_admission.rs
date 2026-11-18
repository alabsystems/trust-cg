// trust-cg-codegen/core_admission.rs - identity-only CoreTrustIR admission
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Closed, identity-only admission contracts for Core TrustIR.
//!
//! This module deliberately separates three claims that are easy to conflate:
//!
//! * TrustIR validation establishes structural/type/proof-replay validity;
//! * Core admission establishes that one exact module passes full validation,
//!   exact target/declared-import closure, and strict TrustIR-to-LIR
//!   translation without a TrustIR rewrite;
//! * source-language refinement and machine-code preservation require their
//!   own receipts and are **not** established here.
//!
//! The first Core profile is intentionally identity-only.  Its open and Core
//! structural digests are equal, and every target/import fact is explicit.
//! A later legalizer may transport IDs and proofs, but it must use a different
//! policy and independently checked transform receipt rather than weakening
//! this boundary.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsString;
use std::sync::Arc;

use serde::Serialize;
use thiserror::Error;
use trust_cg_ir::NativeDependencyId;
use trust_cg_lower::{
    AdapterNamedCallSemantics, ModuleLocalFunctionIdentityCensus, TlsDialect,
    classify_adapter_named_call,
};
use trust_ir::inst::Inst;
use trust_ir::proof::{ProofCertificateRef, ProofDigest, ProofDigestAlgorithm, ProofStatus};
use trust_ir::{
    CallingConv, Constant, FuncAttrs, FuncId, FuncTy, Linkage, Module, ModuleFunctionCatalog,
    ParamAttrs, StructPassingPolicy, TargetInfo, TlsModel, Ty,
};
use trust_ir_build::ValidationError;

use crate::jit_contract::{
    AbiDescriptor, AbiVarargsPolicy, Endianness as ContractEndianness, ExecutableMemoryOwner,
    TargetArchitecture, TargetDescriptor, TargetOperatingSystem as ContractOperatingSystem,
    TeardownPolicy,
};
use crate::strict_adapter::{
    StrictCoreAdapterError, StrictCoreAdapterResult, StrictCoreAdapterTarget,
    StrictCoreObjectFormat, translate_validated_core_module_under_core_qualification,
};
use crate::target::{
    AArch64IsaProfile, Target, TargetEnvironment, TargetOperatingSystem, TargetSpec, TargetVendor,
};
use crate::x86_64::X86TargetFeatures;

/// Stable identity of the only Core policy admitted by this module today.
pub const IDENTITY_CORE_POLICY_SCHEMA: &str = "trust-cg.core-admission.identity.v1";
/// Wire/schema version of [`IdentityTransformReceipt`].
pub const IDENTITY_CORE_POLICY_SCHEMA_VERSION: u32 = 2;
/// Schema of [`CoreDeclaredImportManifest`].
pub const CORE_DECLARED_IMPORT_MANIFEST_SCHEMA: &str = "trust-cg.core-declared-import-manifest.v1";
/// Wire/schema version of [`CoreDeclaredImportManifest`].
pub const CORE_DECLARED_IMPORT_MANIFEST_SCHEMA_VERSION: u32 = 1;
/// Schema of the planning-time native runtime catalog.
pub const CORE_NATIVE_RUNTIME_CATALOG_SCHEMA: &str = "trust-cg.core-native-runtime-catalog.v1";
/// Wire/schema version of [`CoreNativeRuntimeCatalog`].
pub const CORE_NATIVE_RUNTIME_CATALOG_SCHEMA_VERSION: u32 = 1;
/// Schema of the planning-time source-to-native dependency reference map.
pub const CORE_NATIVE_DEPENDENCY_REFERENCE_MAP_SCHEMA: &str =
    "trust-cg.core-native-dependency-reference-map.v1";
/// Wire/schema version of [`CoreNativeDependencyReferenceMap`].
pub const CORE_NATIVE_DEPENDENCY_REFERENCE_MAP_SCHEMA_VERSION: u32 = 1;
/// Schema of the strict-LIR imported-call binding receipt.
pub const CORE_LIR_NATIVE_DEPENDENCY_BINDINGS_SCHEMA: &str =
    "trust-cg.core-lir-native-dependency-bindings.v2";
/// Wire/schema version of [`CoreLirNativeDependencyBindings`].
pub const CORE_LIR_NATIVE_DEPENDENCY_BINDINGS_SCHEMA_VERSION: u32 = 2;
/// Digest domain for the exact Core target/ABI/optional-ISA contract.
///
/// V2 separates AArch64 DarwinPCS from Linux AAPCS64 and forbids carrying
/// Darwin's below-SP red-zone permission into Linux code generation.
pub const CORE_TARGET_CONTRACT_SCHEMA: &str = "trust-cg.core-target-contract.v2";
/// Wire/schema version of [`CoreTargetContract`].
pub const CORE_TARGET_CONTRACT_SCHEMA_VERSION: u32 = 2;

const MAX_CONTRACT_TEXT_BYTES: usize = 4096;

/// Only native pipeline allowed to consume a Core admission v1 owner.
///
/// This is permission to attempt the named downstream pipeline, not evidence
/// that ISel, register allocation, machine validation, linking, or installation
/// succeeded.  Relocatable object/AOT emission can introduce preemptible symbol
/// resolution not covered by the strict adapter's exact-module-call replay.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CorePermittedNativeMode {
    /// Only a later closed host-JIT pipeline may consume this owner.  That
    /// pipeline must independently compile, resolve, validate, and install the
    /// complete image before minting executable authority.
    ClosedHostJit,
}

/// Typed optional-ISA policy snapshot that a later compiler must consume and
/// re-bind in its machine-code receipt.
///
/// This is not evidence that strict TrustIR-to-LIR lowering consumed these
/// features—it does not.  Capturing the host profile here prevents a later JIT
/// compile from silently probing a different machine policy after admission.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CoreHostJitMachineProfile {
    AArch64(AArch64IsaProfile),
    X86_64(X86TargetFeatures),
}

impl CoreHostJitMachineProfile {
    /// Architecture whose in-process JIT policy was captured.
    #[must_use]
    pub const fn architecture(self) -> Target {
        match self {
            Self::AArch64(_) => Target::Aarch64,
            Self::X86_64(_) => Target::X86_64,
        }
    }

    /// Exact AArch64 policy, when this is an AArch64 host profile.
    #[must_use]
    pub const fn aarch64(self) -> Option<AArch64IsaProfile> {
        match self {
            Self::AArch64(profile) => Some(profile),
            Self::X86_64(_) => None,
        }
    }

    /// Exact x86-64 policy, when this is an x86-64 host profile.
    #[must_use]
    pub const fn x86_64(self) -> Option<X86TargetFeatures> {
        match self {
            Self::AArch64(_) => None,
            Self::X86_64(profile) => Some(profile),
        }
    }
}

/// One fail-closed snapshot of the exact current-host Core JIT target.
///
/// This is the sole public authority for pairing TrustCG's target/optional-ISA
/// selection with the [`TargetInfo`] a frontend must bind into TrustIR.  Its
/// fields are deliberately private and it has no caller-configurable
/// constructor: a frontend may inspect or clone the resolved facts, but cannot
/// assemble a target token from independently maintained ABI tables.
///
/// Optional ISA features intentionally do not appear in [`TargetInfo`].  They
/// affect the later machine artifact rather than the source module's ABI, so
/// this owner retains them separately for the admission receipt and consuming
/// compiler.  Callers should detect this value once, reuse its
/// [`Self::trust_ir_target_info`] while building a module, and pass the same
/// owner to [`admit_identity_core_module_for_host_jit`].
///
/// ```compile_fail
/// use trust_cg_codegen::{CoreHostJitMachineProfile, CoreHostJitTarget};
/// use trust_cg_codegen::target::TargetSpec;
/// use trust_ir::TargetInfo;
///
/// fn forge_target(
///     target_spec: TargetSpec,
///     machine_profile: CoreHostJitMachineProfile,
///     target_info: TargetInfo,
/// ) -> CoreHostJitTarget {
///     CoreHostJitTarget {
///         target_spec,
///         machine_profile,
///         trust_ir_target_info: target_info,
///     }
/// }
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct CoreHostJitTarget {
    target_spec: TargetSpec,
    machine_profile: CoreHostJitMachineProfile,
    trust_ir_target_info: TargetInfo,
}

impl CoreHostJitTarget {
    /// Detect and validate the only exact host target this process may execute.
    ///
    /// This never inherits [`Target::host`]'s compatibility fallback.  Unknown
    /// architectures, unsupported architecture/OS combinations, non-64-bit
    /// pointer layouts, and non-little-endian hosts all fail before a target
    /// owner is minted.  The optional-ISA profile is probed exactly once and is
    /// retained in the returned owner rather than re-probed during admission.
    pub fn detect() -> Result<Self, CoreTargetContractError> {
        let architecture = Target::try_host().ok_or(
            CoreTargetContractError::BuildHostArchitectureNotRepresentable {
                architecture: std::env::consts::ARCH,
            },
        )?;
        if architecture == Target::Riscv64 {
            return Err(CoreTargetContractError::HostJitArchitectureUnsupported {
                target: architecture,
            });
        }
        let operating_system = TargetOperatingSystem::host();
        let vendor = if cfg!(target_vendor = "apple") {
            TargetVendor::Apple
        } else if cfg!(target_vendor = "unknown") {
            TargetVendor::Unknown
        } else if cfg!(target_vendor = "pc") {
            TargetVendor::Pc
        } else {
            return Err(CoreTargetContractError::HostJitVendorNotRepresentable);
        };
        let environment = if cfg!(target_env = "gnu") {
            TargetEnvironment::Gnu
        } else if cfg!(target_env = "msvc") {
            TargetEnvironment::Msvc
        } else if cfg!(target_env = "musl") {
            return Err(CoreTargetContractError::HostJitEnvironmentUnsupported {
                environment: "musl",
            });
        } else if cfg!(target_env = "") {
            // Rust's supported Darwin targets use an empty target_env,
            // represented by TargetEnvironment::Unknown in TrustCG's exact
            // target tuple.  The tuple check below rejects this value for
            // Linux and Windows rather than guessing their ABI.
            TargetEnvironment::Unknown
        } else {
            return Err(CoreTargetContractError::HostJitEnvironmentNotRepresentable);
        };
        if !cfg!(target_abi = "") {
            // TargetSpec has no independent Rust target_abi component.  Never
            // erase a nonempty host ABI suffix when minting an executable
            // target owner.
            return Err(CoreTargetContractError::HostJitTargetAbiNotRepresentable);
        }
        let endianness = match (cfg!(target_endian = "little"), cfg!(target_endian = "big")) {
            (true, false) => trust_ir::Endianness::Little,
            (false, true) => trust_ir::Endianness::Big,
            _ => {
                return Err(CoreTargetContractError::HostJitEndiannessNotRepresentable);
            }
        };
        let (target_spec, trust_ir_target_info) = resolve_host_target_abi_and_layout(
            architecture,
            vendor,
            operating_system,
            environment,
            std::mem::size_of::<usize>(),
            endianness,
        )?;

        // Optional ISA probing is deliberately last: an unsupported host must
        // fail before any machine-policy snapshot is taken.
        let machine_profile = match architecture {
            Target::Aarch64 => {
                CoreHostJitMachineProfile::AArch64(AArch64IsaProfile::for_host_jit())
            }
            Target::X86_64 => CoreHostJitMachineProfile::X86_64(X86TargetFeatures::host()),
            Target::Riscv64 => {
                return Err(CoreTargetContractError::HostJitArchitectureUnsupported {
                    target: architecture,
                });
            }
        };
        Ok(Self {
            target_spec,
            machine_profile,
            trust_ir_target_info,
        })
    }

    /// Exact explicit compiler target, including OS and ABI environment.
    #[must_use]
    pub const fn target_spec(&self) -> TargetSpec {
        self.target_spec
    }

    /// Optional host ISA policy captured by [`Self::detect`].
    #[must_use]
    pub const fn machine_profile(&self) -> CoreHostJitMachineProfile {
        self.machine_profile
    }

    /// Exact TrustIR target metadata frontends must bind before validation.
    #[must_use]
    pub const fn trust_ir_target_info(&self) -> &TargetInfo {
        &self.trust_ir_target_info
    }

    /// Bind this owner's exact target to an as-yet targetless module in place.
    /// An existing target must pass the unchanged, exact target check; it is
    /// never replaced, including on refusal. No module body, table or identity
    /// is cloned, and the optional ISA profile is not detected again.
    ///
    /// Producers should do this before emission/source custody is finalized.
    /// Adding target metadata changes the module's digest-bearing meaning; it
    /// is not an identity transform of an already retained targetless module.
    /// This operation establishes only target correspondence, not module
    /// validation, aggregate/caller ABI correctness, proof or native admission.
    /// The normal identity-admission entry still refuses an unbound module.
    ///
    /// # Errors
    ///
    /// Returns the specific target mismatch without changing a pre-targeted
    /// module. A targetless module receives the metadata already validated by
    /// this privately constructed owner, then undergoes the same strict check.
    pub fn bind_module_target(&self, module: &mut Module) -> Result<(), CoreTargetContractError> {
        if module.target_info.is_none() {
            module.target_info = Some(self.trust_ir_target_info.clone());
        }
        self.check_module(module)
    }

    #[cfg(test)]
    pub(crate) fn try_from_detected_facts(
        architecture: Target,
        vendor: TargetVendor,
        operating_system: TargetOperatingSystem,
        environment: TargetEnvironment,
        target_abi_is_empty: bool,
        actual_pointer_bytes: usize,
        actual_endianness: trust_ir::Endianness,
        machine_profile: CoreHostJitMachineProfile,
    ) -> Result<Self, CoreTargetContractError> {
        if architecture == Target::Riscv64 {
            return Err(CoreTargetContractError::HostJitArchitectureUnsupported {
                target: architecture,
            });
        }
        if machine_profile.architecture() != architecture {
            return Err(CoreTargetContractError::HostJitMachineProfileMismatch {
                expected: architecture,
                actual: machine_profile.architecture(),
            });
        }
        if !target_abi_is_empty {
            return Err(CoreTargetContractError::HostJitTargetAbiNotRepresentable);
        }
        let (target_spec, trust_ir_target_info) = resolve_host_target_abi_and_layout(
            architecture,
            vendor,
            operating_system,
            environment,
            actual_pointer_bytes,
            actual_endianness,
        )?;

        Ok(Self {
            target_spec,
            machine_profile,
            trust_ir_target_info,
        })
    }

    fn check_module(&self, module: &Module) -> Result<(), CoreTargetContractError> {
        let actual = module
            .target_info
            .as_ref()
            .ok_or(CoreTargetContractError::ModuleTargetMissing)?;
        let expected = &self.trust_ir_target_info;
        if actual.triple != expected.triple {
            return Err(CoreTargetContractError::TrustIrTripleMismatch {
                expected: expected.triple.clone(),
                actual: actual.triple.clone(),
            });
        }
        if actual.pointer_size != expected.pointer_size {
            return Err(CoreTargetContractError::TrustIrPointerWidthMismatch {
                expected: expected.pointer_size,
                actual: actual.pointer_size,
            });
        }
        if actual.endianness != expected.endianness {
            return Err(CoreTargetContractError::UnsupportedTrustIrEndianness {
                actual: actual.endianness,
            });
        }
        let actual_abi = actual
            .abi
            .as_deref()
            .ok_or(CoreTargetContractError::TrustIrAbiMissing)?;
        validate_contract_text("TrustIR ABI", actual_abi)?;
        let expected_abi = expected
            .abi
            .as_deref()
            .ok_or(CoreTargetContractError::TrustIrAbiMissing)?;
        if actual_abi != expected_abi {
            return Err(CoreTargetContractError::TrustIrAbiMismatch {
                expected: expected_abi.to_owned(),
                actual: actual_abi.to_owned(),
            });
        }
        if actual.struct_passing != StructPassingPolicy::NativeC {
            return Err(CoreTargetContractError::TrustIrStructPassingUnsupported {
                actual: actual.struct_passing,
            });
        }
        if actual != expected {
            return Err(CoreTargetContractError::ModuleTargetMismatch {
                expected: expected.clone(),
                actual: actual.clone(),
            });
        }
        Ok(())
    }
}

fn exact_host_target_spec(
    architecture: Target,
    vendor: TargetVendor,
    operating_system: TargetOperatingSystem,
    environment: TargetEnvironment,
) -> Result<TargetSpec, CoreTargetContractError> {
    let (expected_vendor, expected_environment) = match operating_system {
        TargetOperatingSystem::Darwin => (TargetVendor::Apple, TargetEnvironment::Unknown),
        TargetOperatingSystem::Linux => (TargetVendor::Unknown, TargetEnvironment::Gnu),
        TargetOperatingSystem::Windows => (TargetVendor::Pc, TargetEnvironment::Msvc),
        TargetOperatingSystem::Unknown => {
            return Err(CoreTargetContractError::HostJitOperatingSystemUnsupported {
                operating_system,
            });
        }
    };
    if vendor != expected_vendor {
        return Err(CoreTargetContractError::HostJitVendorUnsupported {
            operating_system,
            expected: expected_vendor,
            actual: vendor,
        });
    }
    if environment != expected_environment {
        return Err(CoreTargetContractError::HostJitEnvironmentMismatch {
            operating_system,
            expected: expected_environment,
            actual: environment,
        });
    }
    if !matches!(
        (architecture, operating_system),
        (
            Target::Aarch64 | Target::X86_64,
            TargetOperatingSystem::Linux | TargetOperatingSystem::Darwin
        ) | (Target::X86_64, TargetOperatingSystem::Windows)
    ) {
        return Err(
            CoreTargetContractError::HostJitArchitectureOperatingSystemUnsupported {
                architecture,
                operating_system,
            },
        );
    }

    let target_spec = TargetSpec::new(architecture, vendor, operating_system, environment);

    let target = target_spec.triple();
    let reparsed = TargetSpec::parse(&target).map_err(|error| {
        CoreTargetContractError::HostJitTargetUnsupported {
            target: target.clone(),
            reason: error.reason().to_owned(),
        }
    })?;
    if reparsed != target_spec {
        return Err(CoreTargetContractError::HostJitTargetUnsupported {
            target,
            reason: "canonical target triple did not round-trip".to_owned(),
        });
    }
    Ok(target_spec)
}

fn resolve_host_target_abi_and_layout(
    architecture: Target,
    vendor: TargetVendor,
    operating_system: TargetOperatingSystem,
    environment: TargetEnvironment,
    actual_pointer_bytes: usize,
    actual_endianness: trust_ir::Endianness,
) -> Result<(TargetSpec, TargetInfo), CoreTargetContractError> {
    let target_spec = exact_host_target_spec(architecture, vendor, operating_system, environment)?;
    let expected_pointer_bytes = architecture.pointer_bytes();
    if actual_pointer_bytes != expected_pointer_bytes as usize {
        return Err(CoreTargetContractError::HostJitPointerWidthMismatch {
            expected: expected_pointer_bytes,
            actual: actual_pointer_bytes,
        });
    }
    if actual_endianness != trust_ir::Endianness::Little {
        return Err(CoreTargetContractError::HostJitEndiannessUnsupported {
            actual: actual_endianness,
        });
    }

    let descriptor = TargetDescriptor::for_trust_cg_target_spec(target_spec);
    let abi =
        AbiDescriptor::for_trust_cg_target_os(architecture, descriptor.operating_system.clone());
    let expected_pointer_bits = architecture.pointer_bits();
    if descriptor.pointer_width_bits != expected_pointer_bits {
        return Err(CoreTargetContractError::DescriptorPointerWidthMismatch {
            expected: expected_pointer_bits,
            actual: descriptor.pointer_width_bits,
        });
    }
    if descriptor.endianness != ContractEndianness::Little {
        return Err(CoreTargetContractError::UnsupportedDescriptorEndianness {
            actual: descriptor.endianness,
        });
    }
    if abi.pointer_width_bits != descriptor.pointer_width_bits {
        return Err(CoreTargetContractError::AbiPointerWidthMismatch {
            expected: descriptor.pointer_width_bits,
            actual: abi.pointer_width_bits,
        });
    }
    validate_contract_text("ABI descriptor name", &abi.name)?;
    validate_contract_text("ABI calling convention", &abi.calling_convention)?;

    Ok((
        target_spec,
        TargetInfo {
            triple: descriptor.triple,
            pointer_size: expected_pointer_bytes,
            endianness: actual_endianness,
            abi: Some(abi.calling_convention),
            struct_passing: StructPassingPolicy::NativeC,
        },
    ))
}

/// The sealed Core policy.  There are no configurable escape hatches in v1.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IdentityCorePolicy {
    _private: (),
}

impl IdentityCorePolicy {
    /// Select the identity/no-TrustIR-rewrite Core profile.
    #[must_use]
    pub const fn v1() -> Self {
        Self { _private: () }
    }

    /// Stable policy digest bound into every admission receipt.
    #[must_use]
    pub fn digest(self) -> ProofDigest {
        ProofDigest::sha256_domain(
            "trust-cg.core-admission.policy.v1",
            IDENTITY_CORE_POLICY_SCHEMA.as_bytes(),
        )
    }
}

/// One explicit adapter-target contract shared by Core admission and JIT
/// compilation.
///
/// The strict adapter target and TrustIR `TargetInfo` are retained because
/// neither is a lossless replacement for the other.  Construction accepts the
/// adapter's sealed target object directly and checks every overlapping field.
/// Its `TargetDescriptor::features` field is not a selected-ISA contract. Core
/// admission instead captures the host JIT machine profile separately and
/// includes it in this contract's digest. The strict lowering primitive does
/// not consume optional CPU features; a later compiler must consume the
/// captured profile and bind evidence for its actual machine feature policy.
#[derive(Debug, Clone, PartialEq)]
pub struct CoreTargetContract {
    adapter_target: StrictCoreAdapterTarget,
    host_target: CoreHostJitTarget,
    digest: ProofDigest,
}

impl CoreTargetContract {
    /// Validate the indivisible target facts returned by the strict adapter.
    /// There is intentionally no constructor accepting a separate descriptor
    /// or ABI: those could drift from the target actually used for lowering.
    fn try_from_strict_target(
        adapter_target: StrictCoreAdapterTarget,
        host_target: &CoreHostJitTarget,
    ) -> Result<Self, CoreTargetContractError> {
        let target_spec = adapter_target.target_spec();
        let descriptor = adapter_target.target_descriptor();
        let abi = adapter_target.abi_descriptor();
        if target_spec != host_target.target_spec() {
            return Err(CoreTargetContractError::HostJitTargetMismatch {
                expected: host_target.target_spec().triple(),
                actual: target_spec.triple(),
            });
        }
        let host_jit_machine_profile = host_target.machine_profile();
        let target_info = host_target.trust_ir_target_info();
        if host_jit_machine_profile.architecture() != target_spec.architecture {
            return Err(CoreTargetContractError::HostJitMachineProfileMismatch {
                expected: target_spec.architecture,
                actual: host_jit_machine_profile.architecture(),
            });
        }
        if !target_spec.has_explicit_os_abi() {
            return Err(CoreTargetContractError::ImplicitTargetSpec {
                target: target_spec.triple(),
            });
        }

        let exact_triple = target_spec.triple();
        if descriptor.triple != exact_triple {
            return Err(CoreTargetContractError::DescriptorTripleMismatch {
                expected: exact_triple,
                actual: descriptor.triple.clone(),
            });
        }
        let expected_architecture = descriptor_architecture(target_spec.architecture);
        if descriptor.architecture != expected_architecture {
            return Err(CoreTargetContractError::DescriptorArchitectureMismatch {
                expected: expected_architecture,
                actual: descriptor.architecture.clone(),
            });
        }
        let expected_os = descriptor_operating_system(target_spec.operating_system);
        if descriptor.operating_system != expected_os {
            return Err(CoreTargetContractError::DescriptorOperatingSystemMismatch {
                expected: expected_os,
                actual: descriptor.operating_system.clone(),
            });
        }
        let expected_pointer_bits = target_spec.architecture.pointer_bits();
        if descriptor.pointer_width_bits != expected_pointer_bits {
            return Err(CoreTargetContractError::DescriptorPointerWidthMismatch {
                expected: expected_pointer_bits,
                actual: descriptor.pointer_width_bits,
            });
        }
        if descriptor.endianness != ContractEndianness::Little {
            return Err(CoreTargetContractError::UnsupportedDescriptorEndianness {
                actual: descriptor.endianness,
            });
        }
        if abi.pointer_width_bits != descriptor.pointer_width_bits {
            return Err(CoreTargetContractError::AbiPointerWidthMismatch {
                expected: descriptor.pointer_width_bits,
                actual: abi.pointer_width_bits,
            });
        }
        validate_contract_text("ABI descriptor name", &abi.name)?;
        validate_contract_text("ABI calling convention", &abi.calling_convention)?;

        if target_info.triple != descriptor.triple {
            return Err(CoreTargetContractError::TrustIrTripleMismatch {
                expected: descriptor.triple.clone(),
                actual: target_info.triple.clone(),
            });
        }
        let expected_pointer_bytes = u32::from(descriptor.pointer_width_bits / 8);
        if target_info.pointer_size != expected_pointer_bytes {
            return Err(CoreTargetContractError::TrustIrPointerWidthMismatch {
                expected: expected_pointer_bytes,
                actual: target_info.pointer_size,
            });
        }
        if target_info.endianness != trust_ir::Endianness::Little {
            return Err(CoreTargetContractError::UnsupportedTrustIrEndianness {
                actual: target_info.endianness,
            });
        }
        let trust_ir_abi = target_info
            .abi
            .as_deref()
            .ok_or(CoreTargetContractError::TrustIrAbiMissing)?;
        validate_contract_text("TrustIR ABI", trust_ir_abi)?;
        if trust_ir_abi != abi.calling_convention {
            return Err(CoreTargetContractError::TrustIrAbiMismatch {
                expected: abi.calling_convention.clone(),
                actual: trust_ir_abi.to_owned(),
            });
        }
        if target_info.struct_passing != StructPassingPolicy::NativeC {
            return Err(CoreTargetContractError::TrustIrStructPassingUnsupported {
                actual: target_info.struct_passing,
            });
        }

        let digest =
            core_target_contract_digest(&adapter_target, host_jit_machine_profile, target_info)?;
        Ok(Self {
            adapter_target,
            host_target: host_target.clone(),
            digest,
        })
    }

    /// Exact compiler target spec; callers must reuse it rather than resolve a
    /// host default after admission.
    #[must_use]
    pub const fn target_spec(&self) -> TargetSpec {
        self.adapter_target.target_spec()
    }

    /// Product-facing architecture/OS facts returned by the adapter.
    ///
    /// The descriptor's feature list is not the selected optional-ISA policy;
    /// use [`Self::host_jit_machine_profile`] for the profile captured and
    /// digested during admission.
    #[must_use]
    pub const fn descriptor(&self) -> &TargetDescriptor {
        self.adapter_target.target_descriptor()
    }

    /// ABI descriptor selected by the strict adapter from the exact target.
    ///
    /// This binds the declared ABI name/register contract only.  Strict
    /// TrustIR-to-LIR translation does not prove aggregate register/stack
    /// realization; a later machine compiler must validate that separately.
    #[must_use]
    pub const fn abi(&self) -> &AbiDescriptor {
        self.adapter_target.abi_descriptor()
    }

    /// Object container implied by the exact target spec.
    #[must_use]
    pub const fn object_format(&self) -> StrictCoreObjectFormat {
        self.adapter_target.object_format()
    }

    /// Adapter TLS dialect implied by the exact target spec.
    ///
    /// Core admission v1 still rejects every TLS global.  Retaining this fact
    /// prevents a later target consumer from independently guessing it.
    #[must_use]
    pub const fn tls_dialect(&self) -> TlsDialect {
        self.adapter_target.tls_dialect()
    }

    /// Host optional-ISA policy that the later machine compiler must reuse and
    /// prove it selected.  This is a required policy snapshot, not compiled
    /// machine-code evidence.
    #[must_use]
    pub const fn host_jit_machine_profile(&self) -> CoreHostJitMachineProfile {
        self.host_target.machine_profile()
    }

    /// Exact TrustIR target metadata required on the admitted module.
    #[must_use]
    pub const fn target_info(&self) -> &TargetInfo {
        self.host_target.trust_ir_target_info()
    }

    /// Cryptographic identity of the adapter target, captured host JIT machine
    /// profile, and exact TrustIR metadata.
    #[must_use]
    pub const fn digest(&self) -> ProofDigest {
        self.digest
    }

    /// Reauthenticate the retained target/profile tuple behind its cached
    /// digest. This is intentionally stronger than comparing the digest field
    /// to another sidecar that may have drifted with it.
    pub(crate) fn is_intact(&self) -> bool {
        Self::try_from_strict_target(self.adapter_target.clone(), &self.host_target)
            .is_ok_and(|rebuilt| rebuilt == *self)
    }

    pub(crate) fn check_module(&self, module: &Module) -> Result<(), CoreTargetContractError> {
        self.host_target.check_module(module)
    }
}

/// Failure to establish an explicit, internally coherent target contract.
#[derive(Debug, Clone, PartialEq, Error)]
pub enum CoreTargetContractError {
    #[error(transparent)]
    IdentityEncoding(#[from] CoreIdentityEncodingError),
    /// The Rust build host has no exact representation in [`Target`].  Core
    /// admission must not inherit [`Target::host`]'s compatibility fallback.
    #[error("Core closed-JIT admission cannot represent build host architecture {architecture:?}")]
    BuildHostArchitectureNotRepresentable { architecture: &'static str },
    #[error("Core closed-JIT admission does not support host architecture {target:?}")]
    HostJitArchitectureUnsupported { target: Target },
    #[error(
        "Core closed-JIT admission does not support host operating system {operating_system:?}"
    )]
    HostJitOperatingSystemUnsupported {
        operating_system: TargetOperatingSystem,
    },
    #[error("Core closed-JIT admission cannot represent the build host target vendor")]
    HostJitVendorNotRepresentable,
    #[error(
        "Core closed-JIT admission requires vendor {expected:?} for {operating_system:?}, got {actual:?}"
    )]
    HostJitVendorUnsupported {
        operating_system: TargetOperatingSystem,
        expected: TargetVendor,
        actual: TargetVendor,
    },
    #[error("Core closed-JIT admission does not support host environment {environment:?}")]
    HostJitEnvironmentUnsupported { environment: &'static str },
    #[error("Core closed-JIT admission cannot represent the build host environment")]
    HostJitEnvironmentNotRepresentable,
    #[error(
        "Core closed-JIT admission requires environment {expected:?} for {operating_system:?}, got {actual:?}"
    )]
    HostJitEnvironmentMismatch {
        operating_system: TargetOperatingSystem,
        expected: TargetEnvironment,
        actual: TargetEnvironment,
    },
    #[error("Core closed-JIT admission cannot represent a nonempty build host target ABI suffix")]
    HostJitTargetAbiNotRepresentable,
    #[error(
        "Core closed-JIT admission does not support host architecture {architecture:?} on {operating_system:?}"
    )]
    HostJitArchitectureOperatingSystemUnsupported {
        architecture: Target,
        operating_system: TargetOperatingSystem,
    },
    #[error("Core closed-JIT admission does not support host target {target:?}: {reason}")]
    HostJitTargetUnsupported { target: String, reason: String },
    #[error(
        "Core closed-JIT host pointer width mismatch: target requires {expected} bytes, process uses {actual}"
    )]
    HostJitPointerWidthMismatch { expected: u32, actual: usize },
    #[error("Core closed-JIT admission requires a little-endian host, got {actual}")]
    HostJitEndiannessUnsupported { actual: trust_ir::Endianness },
    #[error("Core closed-JIT admission cannot represent the build host endianness")]
    HostJitEndiannessNotRepresentable,
    #[error("Core closed-JIT target mismatch: expected host {expected:?}, got {actual:?}")]
    HostJitTargetMismatch { expected: String, actual: String },
    #[error(
        "host-JIT machine profile architecture mismatch: expected {expected:?}, got {actual:?}"
    )]
    HostJitMachineProfileMismatch { expected: Target, actual: Target },
    #[error("Core admission requires an explicit target OS/ABI, not alias {target:?}")]
    ImplicitTargetSpec { target: String },
    #[error("target descriptor triple mismatch: expected {expected:?}, got {actual:?}")]
    DescriptorTripleMismatch { expected: String, actual: String },
    #[error("target descriptor architecture mismatch: expected {expected:?}, got {actual:?}")]
    DescriptorArchitectureMismatch {
        expected: TargetArchitecture,
        actual: TargetArchitecture,
    },
    #[error("target descriptor operating-system mismatch: expected {expected:?}, got {actual:?}")]
    DescriptorOperatingSystemMismatch {
        expected: ContractOperatingSystem,
        actual: ContractOperatingSystem,
    },
    #[error("target descriptor pointer width mismatch: expected {expected}, got {actual}")]
    DescriptorPointerWidthMismatch { expected: u16, actual: u16 },
    #[error("ABI descriptor pointer width mismatch: expected {expected}, got {actual}")]
    AbiPointerWidthMismatch { expected: u16, actual: u16 },
    #[error("Core admission does not support target descriptor endianness {actual:?}")]
    UnsupportedDescriptorEndianness { actual: ContractEndianness },
    #[error("{field} must be nonempty, bounded, trimmed, and control-free")]
    InvalidContractText { field: &'static str },
    #[error("TrustIR target triple mismatch: expected {expected:?}, got {actual:?}")]
    TrustIrTripleMismatch { expected: String, actual: String },
    #[error("TrustIR pointer width mismatch: expected {expected} bytes, got {actual}")]
    TrustIrPointerWidthMismatch { expected: u32, actual: u32 },
    #[error("Core admission does not support TrustIR endianness {actual}")]
    UnsupportedTrustIrEndianness { actual: trust_ir::Endianness },
    #[error("Core admission requires an explicit TrustIR ABI identifier")]
    TrustIrAbiMissing,
    #[error("TrustIR ABI mismatch: expected {expected:?}, got {actual:?}")]
    TrustIrAbiMismatch { expected: String, actual: String },
    #[error(
        "Core admission requires NativeC aggregate passing until JIT consumes another policy explicitly, got {actual:?}"
    )]
    TrustIrStructPassingUnsupported { actual: StructPassingPolicy },
    #[error("the module has no explicit TrustIR target information")]
    ModuleTargetMissing,
    #[error("the module target does not equal the admitted target contract")]
    ModuleTargetMismatch {
        expected: TargetInfo,
        actual: TargetInfo,
    },
}

/// Runtime implementation identity for one imported symbol.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CoreRuntimeIdentity {
    provider: String,
    binary_digest: ProofDigest,
}

impl CoreRuntimeIdentity {
    /// Bind a named provider and its exact runtime binary/image digest.
    pub fn try_new(
        provider: impl Into<String>,
        binary_digest: ProofDigest,
    ) -> Result<Self, CoreDeclaredImportManifestError> {
        let provider = provider.into();
        validate_host_contract_text("runtime provider", &provider)?;
        if binary_digest.algorithm != ProofDigestAlgorithm::Sha256 || binary_digest.is_zero() {
            return Err(CoreDeclaredImportManifestError::InvalidRuntimeDigest { provider });
        }
        Ok(Self {
            provider,
            binary_digest,
        })
    }

    #[must_use]
    pub fn provider(&self) -> &str {
        &self.provider
    }

    #[must_use]
    pub const fn binary_digest(&self) -> ProofDigest {
        self.binary_digest
    }
}

/// Memory behavior promised by a function import's implementation contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum CoreHostMemoryEffect {
    /// Reads and writes no memory (`readnone`).
    None,
    /// May read but does not write memory (`readonly`).
    ReadOnly,
    /// May read and write memory.
    ReadWrite,
}

/// Determinism promised by a host function contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum CoreHostDeterminism {
    Deterministic,
    Nondeterministic,
}

/// Typed behavior contract for one imported function.
///
/// Core admission binds this claim to the module and runtime identity; it does
/// not inspect the implementation binary and therefore does not prove that the
/// implementation satisfies the claim.  Publication must join independent
/// runtime-contract authority.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub struct CoreHostFunctionEffects {
    pub memory: CoreHostMemoryEffect,
    pub may_unwind: bool,
    pub may_not_return: bool,
    pub determinism: CoreHostDeterminism,
}

impl CoreHostFunctionEffects {
    #[must_use]
    pub const fn deterministic(memory: CoreHostMemoryEffect) -> Self {
        Self {
            memory,
            may_unwind: false,
            may_not_return: false,
            determinism: CoreHostDeterminism::Deterministic,
        }
    }
}

/// Exact ABI and runtime contract for one bodyless function declaration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CoreHostFunctionImport {
    symbol: String,
    signature: FuncTy,
    calling_conv: CallingConv,
    parameter_attrs: Vec<ParamAttrs>,
    effects: CoreHostFunctionEffects,
    implementation_contract_version: String,
    runtime: CoreRuntimeIdentity,
}

impl CoreHostFunctionImport {
    #[allow(clippy::too_many_arguments)]
    pub fn try_new(
        symbol: impl Into<String>,
        signature: FuncTy,
        calling_conv: CallingConv,
        parameter_attrs: Vec<ParamAttrs>,
        effects: CoreHostFunctionEffects,
        implementation_contract_version: impl Into<String>,
        runtime: CoreRuntimeIdentity,
    ) -> Result<Self, CoreDeclaredImportManifestError> {
        let symbol = symbol.into();
        let implementation_contract_version = implementation_contract_version.into();
        validate_host_contract_text("function import symbol", &symbol)?;
        validate_host_contract_text(
            "function implementation contract version",
            &implementation_contract_version,
        )?;
        if parameter_attrs.len() != signature.params.len() {
            return Err(CoreDeclaredImportManifestError::ParameterAttributeArity {
                symbol,
                expected: signature.params.len(),
                actual: parameter_attrs.len(),
            });
        }
        Ok(Self {
            symbol,
            signature,
            calling_conv,
            parameter_attrs,
            effects,
            implementation_contract_version,
            runtime,
        })
    }

    #[must_use]
    pub fn symbol(&self) -> &str {
        &self.symbol
    }

    #[must_use]
    pub const fn signature(&self) -> &FuncTy {
        &self.signature
    }

    #[must_use]
    pub const fn calling_conv(&self) -> CallingConv {
        self.calling_conv
    }

    #[must_use]
    pub fn parameter_attrs(&self) -> &[ParamAttrs] {
        &self.parameter_attrs
    }

    #[must_use]
    pub const fn effects(&self) -> CoreHostFunctionEffects {
        self.effects
    }

    #[must_use]
    pub fn implementation_contract_version(&self) -> &str {
        &self.implementation_contract_version
    }

    #[must_use]
    pub const fn runtime(&self) -> &CoreRuntimeIdentity {
        &self.runtime
    }
}

/// Exact declared storage/runtime contract for one initializer-less global.
///
/// This row is reserved for the future JIT data-image/binding boundary.  Core
/// admission v1 rejects every module global, so constructing a row does not
/// make a global admissible today.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CoreHostGlobalImport {
    symbol: String,
    ty: Ty,
    mutable: bool,
    tls: Option<TlsModel>,
    align: Option<u32>,
    implementation_contract_version: String,
    runtime: CoreRuntimeIdentity,
}

impl CoreHostGlobalImport {
    pub fn try_new(
        symbol: impl Into<String>,
        ty: Ty,
        mutable: bool,
        tls: Option<TlsModel>,
        align: Option<u32>,
        implementation_contract_version: impl Into<String>,
        runtime: CoreRuntimeIdentity,
    ) -> Result<Self, CoreDeclaredImportManifestError> {
        let symbol = symbol.into();
        let implementation_contract_version = implementation_contract_version.into();
        validate_host_contract_text("global import symbol", &symbol)?;
        validate_host_contract_text(
            "global implementation contract version",
            &implementation_contract_version,
        )?;
        Ok(Self {
            symbol,
            ty,
            mutable,
            tls,
            align,
            implementation_contract_version,
            runtime,
        })
    }

    #[must_use]
    pub fn symbol(&self) -> &str {
        &self.symbol
    }

    #[must_use]
    pub const fn ty(&self) -> &Ty {
        &self.ty
    }

    #[must_use]
    pub const fn mutable(&self) -> bool {
        self.mutable
    }

    #[must_use]
    pub const fn tls(&self) -> Option<TlsModel> {
        self.tls
    }

    #[must_use]
    pub const fn align(&self) -> Option<u32> {
        self.align
    }

    #[must_use]
    pub fn implementation_contract_version(&self) -> &str {
        &self.implementation_contract_version
    }

    #[must_use]
    pub const fn runtime(&self) -> &CoreRuntimeIdentity {
        &self.runtime
    }
}

/// One typed function or data import.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum CoreHostImport {
    Function(CoreHostFunctionImport),
    Global(CoreHostGlobalImport),
}

impl CoreHostImport {
    fn key(&self) -> (u8, &str) {
        match self {
            Self::Function(import) => (0, import.symbol()),
            Self::Global(import) => (1, import.symbol()),
        }
    }

    #[must_use]
    pub fn symbol(&self) -> &str {
        self.key().1
    }
}

/// Canonical exact closure over imports declared by one TrustIR module.
///
/// This is deliberately not a complete native runtime-requirements manifest:
/// instruction selection may introduce compiler-runtime or allocator symbols
/// that do not exist as TrustIR declarations.  A later machine compilation
/// receipt must inventory every emitted native fixup and join its exact binding
/// set before installation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoreDeclaredImportManifest {
    imports: Vec<CoreHostImport>,
    digest: ProofDigest,
}

/// Completeness state of a native runtime catalog.
///
/// V1 deliberately seals only imports already declared by the admitted
/// TrustIR module. Instruction selection may add compiler-runtime helpers, so
/// this state must not be used as a final native-fixup closure receipt.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum CoreNativeRuntimeCatalogCoverage {
    DeclaredImportsOnly,
}

/// Provenance class of one native dependency entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum CoreNativeDependencyOrigin {
    DeclaredTrustIrImport,
    /// Test-only stand-in for any future origin that is not admitted by the
    /// `DeclaredImportsOnly` planning catalog.
    #[cfg(test)]
    TestOnlyNonDeclared,
}

/// One typed catalog entry addressed by [`NativeDependencyId`].
///
/// The ID is meaningful only together with the digest of the enclosing
/// [`CoreNativeRuntimeCatalog`]. This entry contains no address, provider
/// lease, executable-memory handle, or runtime-contract proof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CoreNativeRuntimeEntry {
    id: NativeDependencyId,
    origin: CoreNativeDependencyOrigin,
    import: CoreHostImport,
}

impl CoreNativeRuntimeEntry {
    #[must_use]
    pub const fn id(&self) -> NativeDependencyId {
        self.id
    }

    #[must_use]
    pub const fn origin(&self) -> CoreNativeDependencyOrigin {
        self.origin
    }

    #[must_use]
    pub const fn import(&self) -> &CoreHostImport {
        &self.import
    }

    #[must_use]
    pub fn symbol(&self) -> &str {
        self.import.symbol()
    }
}

/// Deterministic typed native-runtime catalog sealed into a Core JIT plan.
///
/// V1 is a planning seed, not the final machine dependency inventory. IDs are
/// assigned from the canonical declared-import order and the catalog digest
/// binds that order, every typed contract, and the source manifest digest.
/// A future compile-only transition must preserve these entries, add typed
/// compiler-synthesized dependencies, and emit a new complete catalog before
/// binding or installation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoreNativeRuntimeCatalog {
    schema_version: u32,
    coverage: CoreNativeRuntimeCatalogCoverage,
    declared_import_manifest_digest: ProofDigest,
    entries: Vec<CoreNativeRuntimeEntry>,
    digest: ProofDigest,
}

impl CoreNativeRuntimeCatalog {
    /// Derive one canonical, address-free catalog from an admitted import
    /// manifest.
    pub fn try_from_declared_import_manifest(
        manifest: &CoreDeclaredImportManifest,
    ) -> Result<Self, CoreNativeRuntimeCatalogError> {
        let dependency_count = u32::try_from(manifest.imports.len()).map_err(|_| {
            CoreNativeRuntimeCatalogError::DependencyCountOverflow {
                count: manifest.imports.len(),
            }
        })?;
        let entries = manifest
            .imports
            .iter()
            .zip(0..dependency_count)
            .map(|(import, index)| CoreNativeRuntimeEntry {
                id: NativeDependencyId::new(index),
                origin: CoreNativeDependencyOrigin::DeclaredTrustIrImport,
                import: import.clone(),
            })
            .collect();
        let mut catalog = Self {
            schema_version: CORE_NATIVE_RUNTIME_CATALOG_SCHEMA_VERSION,
            coverage: CoreNativeRuntimeCatalogCoverage::DeclaredImportsOnly,
            declared_import_manifest_digest: manifest.digest(),
            entries,
            digest: ProofDigest::zero(),
        };
        catalog.digest = catalog.compute_digest()?;
        Ok(catalog)
    }

    #[must_use]
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    #[must_use]
    pub const fn coverage(&self) -> CoreNativeRuntimeCatalogCoverage {
        self.coverage
    }

    #[must_use]
    pub const fn declared_import_manifest_digest(&self) -> ProofDigest {
        self.declared_import_manifest_digest
    }

    #[must_use]
    pub fn entries(&self) -> &[CoreNativeRuntimeEntry] {
        &self.entries
    }

    #[must_use]
    pub fn get(&self, id: NativeDependencyId) -> Option<&CoreNativeRuntimeEntry> {
        let index = usize::try_from(id.index()).ok()?;
        self.entries.get(index).filter(|entry| entry.id == id)
    }

    #[must_use]
    pub const fn digest(&self) -> ProofDigest {
        self.digest
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    #[must_use]
    pub fn is_intact(&self) -> bool {
        self.schema_version == CORE_NATIVE_RUNTIME_CATALOG_SCHEMA_VERSION
            && self.coverage == CoreNativeRuntimeCatalogCoverage::DeclaredImportsOnly
            && self.entries.iter().enumerate().all(|(index, entry)| {
                u32::try_from(index).is_ok_and(|index| {
                    entry.id == NativeDependencyId::new(index)
                        && matches!(
                            entry.origin,
                            CoreNativeDependencyOrigin::DeclaredTrustIrImport
                        )
                })
            })
            && self
                .compute_digest()
                .is_ok_and(|digest| self.digest == digest)
    }

    fn compute_digest(&self) -> Result<ProofDigest, CoreIdentityEncodingError> {
        let bytes = serialize_core_identity(
            &CoreNativeRuntimeCatalogDigestPayload {
                schema: CORE_NATIVE_RUNTIME_CATALOG_SCHEMA,
                schema_version: self.schema_version,
                coverage: self.coverage,
                declared_import_manifest_digest: self.declared_import_manifest_digest,
                entries: &self.entries,
            },
            "native-runtime catalog",
        )?;
        Ok(ProofDigest::sha256_domain(
            "trust-cg.core-native-runtime-catalog.v1",
            &bytes,
        ))
    }
}

#[derive(Serialize)]
struct CoreNativeRuntimeCatalogDigestPayload<'a> {
    schema: &'static str,
    schema_version: u32,
    coverage: CoreNativeRuntimeCatalogCoverage,
    declared_import_manifest_digest: ProofDigest,
    entries: &'a [CoreNativeRuntimeEntry],
}

/// Failure to construct a compact catalog-local native dependency namespace.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum CoreNativeRuntimeCatalogError {
    #[error(transparent)]
    IdentityEncoding(#[from] CoreIdentityEncodingError),
    #[error("Core native runtime catalog has {count} entries, exceeding the u32 ID space")]
    DependencyCountOverflow { count: usize },
}

/// Completeness state of a source-to-native dependency reference map.
///
/// V1 maps every imported TrustIR function identity admitted by Core to its
/// catalog-local dependency ID. It does not claim that individual LIR call
/// sites or backend-synthesized fixups carry those IDs yet. Core v1 rejects
/// every global, so imported-global identities are intentionally absent.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum CoreNativeDependencyReferenceCoverage {
    DeclaredTrustIrFunctionIdentitiesOnly,
}

/// One module-local imported function identity mapped into one catalog.
///
/// `function` and `dependency` occupy distinct namespaces. The former is
/// meaningful only in the exact TrustIR module bound by the enclosing map;
/// the latter is meaningful only in its exact native-runtime catalog. This
/// row contains neither a symbol name nor runtime binding authority.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CoreNativeDependencyReference {
    function: FuncId,
    dependency: NativeDependencyId,
}

impl CoreNativeDependencyReference {
    #[must_use]
    pub const fn function(&self) -> FuncId {
        self.function
    }

    #[must_use]
    pub const fn dependency(&self) -> NativeDependencyId {
        self.dependency
    }
}

/// Digest-bound address-free map carried beside the retained strict LIR.
///
/// Admission records the exact typed declaration-to-manifest relationship in
/// its existing single module walk. Planning then translates the retained
/// manifest ordinals directly to [`NativeDependencyId`] values; it never
/// recovers authority from an LIR symbol name. The digest binds both otherwise
/// local namespaces through the exact Core module, identity-admission receipt,
/// and catalog digests. The receipt is only the existing in-process retained
/// lowering seal; this map does not claim a canonical LIR digest.
///
/// This map is one input to the atomic strict-LIR binding transition, not final
/// fixup closure. Core planning places these IDs on authenticated imported-call
/// carriers and seals a separate exhaustive receipt. A later compiler stage
/// must carry them through ISel/MachIR/fixups while adding every synthesized
/// native dependency before it may claim complete coverage.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoreNativeDependencyReferenceMap {
    schema_version: u32,
    coverage: CoreNativeDependencyReferenceCoverage,
    core_module_digest: ProofDigest,
    identity_transform_receipt_digest: ProofDigest,
    native_runtime_catalog_digest: ProofDigest,
    entries: Vec<CoreNativeDependencyReference>,
    digest: ProofDigest,
}

impl CoreNativeDependencyReferenceMap {
    fn try_from_admitted_seed(
        core_module_digest: ProofDigest,
        identity_transform_receipt_digest: ProofDigest,
        declared_import_manifest: &CoreDeclaredImportManifest,
        native_runtime_catalog: &CoreNativeRuntimeCatalog,
        seed: &CoreDeclaredImportReferenceSeed,
    ) -> Result<Self, CoreNativeDependencyReferenceMapError> {
        if !seed.is_intact(declared_import_manifest.digest()) {
            return Err(CoreNativeDependencyReferenceMapError::AdmissionReferenceSeedNotIntact);
        }
        if native_runtime_catalog.declared_import_manifest_digest()
            != declared_import_manifest.digest()
        {
            return Err(CoreNativeDependencyReferenceMapError::CatalogManifestDigestMismatch);
        }

        let expected_function_count = declared_import_manifest
            .imports
            .iter()
            .filter(|import| matches!(import, CoreHostImport::Function(_)))
            .count();
        if seed.functions.len() != expected_function_count {
            return Err(
                CoreNativeDependencyReferenceMapError::ImportedFunctionCountMismatch {
                    expected: expected_function_count,
                    actual: seed.functions.len(),
                },
            );
        }

        let mut entries = Vec::with_capacity(seed.functions.len());
        for reference in &seed.functions {
            let dependency_index = u32::try_from(reference.manifest_index).map_err(|_| {
                CoreNativeDependencyReferenceMapError::ManifestIndexNotRepresentable {
                    index: reference.manifest_index,
                }
            })?;
            let dependency = NativeDependencyId::new(dependency_index);
            let manifest_import = declared_import_manifest
                .imports
                .get(reference.manifest_index)
                .ok_or(
                    CoreNativeDependencyReferenceMapError::ManifestEntryMissing {
                        index: reference.manifest_index,
                    },
                )?;
            if !matches!(manifest_import, CoreHostImport::Function(_)) {
                return Err(
                    CoreNativeDependencyReferenceMapError::ManifestEntryKindMismatch {
                        index: reference.manifest_index,
                    },
                );
            }
            let catalog_entry = native_runtime_catalog
                .get(dependency)
                .ok_or(CoreNativeDependencyReferenceMapError::CatalogEntryMissing { dependency })?;
            if catalog_entry.import() != manifest_import {
                return Err(
                    CoreNativeDependencyReferenceMapError::CatalogEntryManifestMismatch {
                        dependency,
                    },
                );
            }
            entries.push(CoreNativeDependencyReference {
                function: reference.function,
                dependency,
            });
        }
        entries.sort_unstable_by_key(|entry| entry.function.index());
        for adjacent in entries.windows(2) {
            if adjacent[0].function == adjacent[1].function {
                return Err(
                    CoreNativeDependencyReferenceMapError::DuplicateImportedFunctionIdentity {
                        function: adjacent[0].function.index(),
                    },
                );
            }
        }

        let mut map = Self {
            schema_version: CORE_NATIVE_DEPENDENCY_REFERENCE_MAP_SCHEMA_VERSION,
            coverage: CoreNativeDependencyReferenceCoverage::DeclaredTrustIrFunctionIdentitiesOnly,
            core_module_digest,
            identity_transform_receipt_digest,
            native_runtime_catalog_digest: native_runtime_catalog.digest(),
            entries,
            digest: ProofDigest::zero(),
        };
        map.digest = map.compute_digest();
        Ok(map)
    }

    #[must_use]
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    #[must_use]
    pub const fn coverage(&self) -> CoreNativeDependencyReferenceCoverage {
        self.coverage
    }

    #[must_use]
    pub const fn core_module_digest(&self) -> ProofDigest {
        self.core_module_digest
    }

    /// Receipt that binds this map to the in-process retained strict lowering.
    ///
    /// The identity receipt is not a canonical LIR digest and this field does
    /// not upgrade it into one. It prevents this sidecar from being silently
    /// transplanted across different admitted target/policy/receipt states.
    #[must_use]
    pub const fn identity_transform_receipt_digest(&self) -> ProofDigest {
        self.identity_transform_receipt_digest
    }

    #[must_use]
    pub const fn native_runtime_catalog_digest(&self) -> ProofDigest {
        self.native_runtime_catalog_digest
    }

    #[must_use]
    pub fn entries(&self) -> &[CoreNativeDependencyReference] {
        &self.entries
    }

    /// Resolve an exact module-local imported function identity.
    ///
    /// No name lookup is provided: callers must retain the authenticated
    /// `FuncId` until the next ID-bearing LIR transition exists.
    #[must_use]
    pub fn dependency_for_function(&self, function: FuncId) -> Option<NativeDependencyId> {
        self.entries
            .binary_search_by_key(&function.index(), |entry| entry.function.index())
            .ok()
            .map(|index| self.entries[index].dependency)
    }

    #[must_use]
    pub const fn digest(&self) -> ProofDigest {
        self.digest
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    #[must_use]
    pub fn is_intact(&self) -> bool {
        self.schema_version == CORE_NATIVE_DEPENDENCY_REFERENCE_MAP_SCHEMA_VERSION
            && self.coverage
                == CoreNativeDependencyReferenceCoverage::DeclaredTrustIrFunctionIdentitiesOnly
            && self
                .entries
                .windows(2)
                .all(|pair| pair[0].function.index() < pair[1].function.index())
            && self.digest == self.compute_digest()
    }

    fn compute_digest(&self) -> ProofDigest {
        let mut bytes = Vec::new();
        push_bytes(
            &mut bytes,
            CORE_NATIVE_DEPENDENCY_REFERENCE_MAP_SCHEMA.as_bytes(),
        );
        push_u32(&mut bytes, self.schema_version);
        bytes.push(match self.coverage {
            CoreNativeDependencyReferenceCoverage::DeclaredTrustIrFunctionIdentitiesOnly => 0,
        });
        push_digest(&mut bytes, self.core_module_digest);
        push_digest(&mut bytes, self.identity_transform_receipt_digest);
        push_digest(&mut bytes, self.native_runtime_catalog_digest);
        push_usize(&mut bytes, self.entries.len());
        for entry in &self.entries {
            push_u32(&mut bytes, entry.function.index());
            push_u32(&mut bytes, entry.dependency.index());
        }
        ProofDigest::sha256_domain(CORE_NATIVE_DEPENDENCY_REFERENCE_MAP_SCHEMA, &bytes)
    }
}

/// Internal drift detected while sealing module-local references into the
/// catalog-local dependency namespace.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum CoreNativeDependencyReferenceMapError {
    #[error("the admission-time import-reference seed is not intact for this manifest")]
    AdmissionReferenceSeedNotIntact,
    #[error("the native runtime catalog is bound to a different declared-import manifest")]
    CatalogManifestDigestMismatch,
    #[error("the admitted import-reference seed contains {actual} functions, expected {expected}")]
    ImportedFunctionCountMismatch { expected: usize, actual: usize },
    #[error("declared-import manifest index {index} is not representable as a dependency ID")]
    ManifestIndexNotRepresentable { index: usize },
    #[error("declared-import manifest entry {index} is missing")]
    ManifestEntryMissing { index: usize },
    #[error("declared-import manifest entry {index} is not a function import")]
    ManifestEntryKindMismatch { index: usize },
    #[error("native runtime catalog entry {dependency} is missing")]
    CatalogEntryMissing { dependency: NativeDependencyId },
    #[error("native runtime catalog entry {dependency} differs from its manifest entry")]
    CatalogEntryManifestMismatch { dependency: NativeDependencyId },
    #[error("imported TrustIR function identity FuncId({function}) appears more than once")]
    DuplicateImportedFunctionIdentity { function: u32 },
}

/// Exact coverage claimed by the strict-LIR imported-call binding receipt.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum CoreLirNativeDependencyBindingCoverage {
    /// Every strict LIR call originating from a declared TrustIR function
    /// import, excluding backend-synthesized helper calls.
    DeclaredTrustIrDirectCallsOnly,
}

/// One source-authenticated strict-LIR call edge sealed to a catalog-local ID.
///
/// The row deliberately contains no symbol name, address, provider handle, or
/// executable authority. Its coordinates and edge digest make it replayable
/// against the retained LIR; both IDs remain scoped by the enclosing module,
/// reference-map, and catalog digests.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CoreLirNativeDependencyBinding {
    lir_function: usize,
    caller: FuncId,
    block: u32,
    instruction: usize,
    source_origin: trust_cg_ir::TrustIrInstId,
    imported_function: FuncId,
    dependency: NativeDependencyId,
    edge_digest: ProofDigest,
}

impl CoreLirNativeDependencyBinding {
    #[must_use]
    pub const fn lir_function(&self) -> usize {
        self.lir_function
    }

    #[must_use]
    pub const fn caller(&self) -> FuncId {
        self.caller
    }

    #[must_use]
    pub const fn block(&self) -> u32 {
        self.block
    }

    #[must_use]
    pub const fn instruction(&self) -> usize {
        self.instruction
    }

    #[must_use]
    pub const fn source_origin(&self) -> trust_cg_ir::TrustIrInstId {
        self.source_origin
    }

    #[must_use]
    pub const fn imported_function(&self) -> FuncId {
        self.imported_function
    }

    #[must_use]
    pub const fn dependency(&self) -> NativeDependencyId {
        self.dependency
    }

    #[must_use]
    pub const fn edge_digest(&self) -> ProofDigest {
        self.edge_digest
    }
}

/// Digest-bound proof that every authenticated declared-import call in strict
/// LIR carries the exact ID selected by the sealed source-to-catalog map.
///
/// This is a verifier/cache identity component, not final native-fixup closure:
/// instruction selection may later introduce compiler helpers. Existing
/// compatibility caches remain non-authoritative and do not consume this type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoreLirNativeDependencyBindings {
    schema_version: u32,
    coverage: CoreLirNativeDependencyBindingCoverage,
    core_module_digest: ProofDigest,
    identity_transform_receipt_digest: ProofDigest,
    native_runtime_catalog_digest: ProofDigest,
    native_dependency_reference_map_digest: ProofDigest,
    entries: Vec<CoreLirNativeDependencyBinding>,
    digest: ProofDigest,
}

impl CoreLirNativeDependencyBindings {
    #[must_use]
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    #[must_use]
    pub const fn coverage(&self) -> CoreLirNativeDependencyBindingCoverage {
        self.coverage
    }

    #[must_use]
    pub const fn core_module_digest(&self) -> ProofDigest {
        self.core_module_digest
    }

    #[must_use]
    pub const fn identity_transform_receipt_digest(&self) -> ProofDigest {
        self.identity_transform_receipt_digest
    }

    #[must_use]
    pub const fn native_runtime_catalog_digest(&self) -> ProofDigest {
        self.native_runtime_catalog_digest
    }

    #[must_use]
    pub const fn native_dependency_reference_map_digest(&self) -> ProofDigest {
        self.native_dependency_reference_map_digest
    }

    #[must_use]
    pub fn entries(&self) -> &[CoreLirNativeDependencyBinding] {
        &self.entries
    }

    #[must_use]
    pub const fn digest(&self) -> ProofDigest {
        self.digest
    }

    #[must_use]
    pub fn is_intact(&self) -> bool {
        self.schema_version == CORE_LIR_NATIVE_DEPENDENCY_BINDINGS_SCHEMA_VERSION
            && self.coverage
                == CoreLirNativeDependencyBindingCoverage::DeclaredTrustIrDirectCallsOnly
            && self.entries.windows(2).all(|pair| {
                (pair[0].lir_function, pair[0].block, pair[0].instruction)
                    < (pair[1].lir_function, pair[1].block, pair[1].instruction)
            })
            && self.digest == self.compute_digest()
    }

    fn compute_digest(&self) -> ProofDigest {
        let mut bytes = Vec::new();
        push_bytes(
            &mut bytes,
            CORE_LIR_NATIVE_DEPENDENCY_BINDINGS_SCHEMA.as_bytes(),
        );
        push_u32(&mut bytes, self.schema_version);
        bytes.push(match self.coverage {
            CoreLirNativeDependencyBindingCoverage::DeclaredTrustIrDirectCallsOnly => 0,
        });
        push_digest(&mut bytes, self.core_module_digest);
        push_digest(&mut bytes, self.identity_transform_receipt_digest);
        push_digest(&mut bytes, self.native_runtime_catalog_digest);
        push_digest(&mut bytes, self.native_dependency_reference_map_digest);
        push_usize(&mut bytes, self.entries.len());
        for entry in &self.entries {
            push_usize(&mut bytes, entry.lir_function);
            push_u32(&mut bytes, entry.caller.index());
            push_u32(&mut bytes, entry.block);
            push_usize(&mut bytes, entry.instruction);
            push_u32(&mut bytes, entry.source_origin.0);
            push_u32(&mut bytes, entry.imported_function.index());
            push_u32(&mut bytes, entry.dependency.index());
            push_digest(&mut bytes, entry.edge_digest);
        }
        ProofDigest::sha256_domain(CORE_LIR_NATIVE_DEPENDENCY_BINDINGS_SCHEMA, &bytes)
    }
}

/// A strict imported-call carrier could not be joined to exactly one sealed
/// native dependency without broadening authority.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum CoreLirNativeDependencyBindingError {
    #[error(transparent)]
    IdentityEncoding(#[from] CoreIdentityEncodingError),
    #[error("the native runtime catalog is not intact")]
    CatalogNotIntact,
    #[error("the native dependency reference map is not intact")]
    ReferenceMapNotIntact,
    #[error("the native runtime catalog is bound to a different manifest")]
    CatalogManifestMismatch,
    #[error("the native dependency reference map is bound to a different Core module")]
    ReferenceMapModuleMismatch,
    #[error("the native dependency reference map is bound to a different identity receipt")]
    ReferenceMapReceiptMismatch,
    #[error("the native dependency reference map is bound to a different catalog")]
    ReferenceMapCatalogMismatch,
    #[error("strict LIR function {lir_function} has no admitted caller FuncId")]
    MissingCallerIdentity { lir_function: usize },
    #[error(
        "strict LIR imported call at function {lir_function}, block {block}, instruction {instruction} has no source provenance"
    )]
    MissingSourceOrigin {
        lir_function: usize,
        block: u32,
        instruction: usize,
    },
    #[error("imported FuncId({function}) has no sealed native dependency mapping")]
    MissingImportedFunctionMapping { function: u32 },
    #[error("mapped native dependency {dependency} is missing from the exact catalog")]
    MissingCatalogDependency { dependency: NativeDependencyId },
    #[error("mapped native dependency {dependency} is not a function import")]
    CatalogDependencyKindMismatch { dependency: NativeDependencyId },
    #[error(
        "strict LIR already contains native dependency {dependency} for FuncId({function}); pre-bound or foreign IDs are forbidden"
    )]
    PreboundOrForeignDependency {
        function: u32,
        dependency: NativeDependencyId,
    },
    #[error(
        "strict LIR contains {actual} authenticated declared-import calls, but admission records {expected}"
    )]
    CarrierCountMismatch { expected: usize, actual: usize },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CoreDeclaredFunctionReferenceSeed {
    function: FuncId,
    manifest_index: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CoreDeclaredImportReferenceSeed {
    functions: Vec<CoreDeclaredFunctionReferenceSeed>,
    declared_import_manifest_digest: ProofDigest,
    digest: ProofDigest,
}

impl Default for CoreDeclaredImportReferenceSeed {
    fn default() -> Self {
        Self {
            functions: Vec::new(),
            declared_import_manifest_digest: ProofDigest::zero(),
            digest: ProofDigest::zero(),
        }
    }
}

impl CoreDeclaredImportReferenceSeed {
    fn seal(mut self, declared_import_manifest_digest: ProofDigest) -> Self {
        self.declared_import_manifest_digest = declared_import_manifest_digest;
        self.digest = self.compute_digest();
        self
    }

    fn is_intact(&self, declared_import_manifest_digest: ProofDigest) -> bool {
        self.declared_import_manifest_digest == declared_import_manifest_digest
            && self.digest == self.compute_digest()
    }

    fn compute_digest(&self) -> ProofDigest {
        let mut bytes = Vec::new();
        push_digest(&mut bytes, self.declared_import_manifest_digest);
        push_usize(&mut bytes, self.functions.len());
        for reference in &self.functions {
            push_u32(&mut bytes, reference.function.index());
            push_usize(&mut bytes, reference.manifest_index);
        }
        ProofDigest::sha256_domain("trust-cg.core-declared-import-reference-seed.v1", &bytes)
    }
}

impl CoreDeclaredImportManifest {
    /// Validate, sort, and seal a typed import list.  Function and global
    /// symbols share one namespace and may appear at most once.
    pub fn try_new(
        mut imports: Vec<CoreHostImport>,
    ) -> Result<Self, CoreDeclaredImportManifestError> {
        imports.sort_by(|left, right| left.key().cmp(&right.key()));
        let mut symbols = BTreeSet::new();
        for import in &imports {
            if !symbols.insert(import.symbol()) {
                return Err(CoreDeclaredImportManifestError::DuplicateSymbol {
                    symbol: import.symbol().to_owned(),
                });
            }
        }
        let digest = core_declared_import_manifest_digest(&imports)?;
        Ok(Self { imports, digest })
    }

    /// Empty import closure for a self-contained module.
    #[must_use]
    pub fn empty() -> Self {
        // This fixed schema payload has no caller-controlled fields to encode.
        // The canonical-empty regression checks it against the general encoder.
        let bytes = br#"{"schema":"trust-cg.core-declared-import-manifest.v1","schema_version":1,"imports":[]}"#;
        Self {
            imports: Vec::new(),
            digest: ProofDigest::sha256_domain(CORE_DECLARED_IMPORT_MANIFEST_SCHEMA, bytes),
        }
    }

    #[must_use]
    pub fn imports(&self) -> &[CoreHostImport] {
        &self.imports
    }

    #[must_use]
    pub const fn digest(&self) -> ProofDigest {
        self.digest
    }

    /// Whether this manifest still has its canonical order, unique symbol
    /// namespace, and content digest.
    ///
    /// Planning identities include the stored digest, so a later consuming
    /// boundary must reauthenticate the content behind that digest rather
    /// than treating the cached value as authority.
    #[must_use]
    pub fn is_intact(&self) -> bool {
        self.imports
            .windows(2)
            .all(|pair| pair[0].key() < pair[1].key())
            && {
                let mut symbols = BTreeSet::new();
                self.imports
                    .iter()
                    .all(|import| symbols.insert(import.symbol()))
            }
            && core_declared_import_manifest_digest(&self.imports)
                .is_ok_and(|digest| self.digest == digest)
    }

    fn find(&self, kind: u8, symbol: &str) -> Option<usize> {
        self.imports
            .binary_search_by(|entry| entry.key().cmp(&(kind, symbol)))
            .ok()
    }

    #[cfg(test)]
    fn check_module(&self, module: &Module) -> Result<(), CoreModuleClosureError> {
        capture_module_inventory(module, self).map(|_| ())
    }
}

fn core_declared_import_manifest_digest(
    imports: &[CoreHostImport],
) -> Result<ProofDigest, CoreIdentityEncodingError> {
    let bytes = serialize_core_identity(
        &DeclaredImportManifestDigestPayload {
            schema: CORE_DECLARED_IMPORT_MANIFEST_SCHEMA,
            schema_version: CORE_DECLARED_IMPORT_MANIFEST_SCHEMA_VERSION,
            imports,
        },
        "declared-import manifest",
    )?;
    Ok(ProofDigest::sha256_domain(
        CORE_DECLARED_IMPORT_MANIFEST_SCHEMA,
        &bytes,
    ))
}

#[derive(Serialize)]
struct DeclaredImportManifestDigestPayload<'a> {
    schema: &'static str,
    schema_version: u32,
    imports: &'a [CoreHostImport],
}

/// Malformed host-manifest construction.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum CoreDeclaredImportManifestError {
    #[error(transparent)]
    IdentityEncoding(#[from] CoreIdentityEncodingError),
    #[error("{field} must be nonempty, bounded, trimmed, and control-free")]
    InvalidContractText { field: &'static str },
    #[error("runtime provider {provider:?} must carry a nonzero SHA-256 binary digest")]
    InvalidRuntimeDigest { provider: String },
    #[error(
        "function import {symbol:?} has {actual} parameter-attribute rows, expected {expected}"
    )]
    ParameterAttributeArity {
        symbol: String,
        expected: usize,
        actual: usize,
    },
    #[error("duplicate Core host import symbol {symbol:?}")]
    DuplicateSymbol { symbol: String },
}

/// Failure of the exact module/import/closed-JIT surface closure.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum CoreModuleClosureError {
    #[error("bodyless function {symbol:?} must have External linkage, got {actual:?}")]
    InvalidFunctionImportLinkage { symbol: String, actual: Linkage },
    #[error("initializer-less global {symbol:?} must have External linkage, got {actual:?}")]
    InvalidGlobalImportLinkage { symbol: String, actual: Linkage },
    #[error("bodyless import {symbol:?} references missing function type #{function_type}")]
    InvalidFunctionType { symbol: String, function_type: u32 },
    #[error("bodyless function import {symbol:?} is absent from the declared-import manifest")]
    MissingFunction { symbol: String },
    #[error(
        "initializer-less global import {symbol:?} is absent from the declared-import manifest"
    )]
    MissingGlobal { symbol: String },
    #[error("bodyless function import {symbol:?} disagrees with its typed host contract")]
    FunctionContractMismatch { symbol: String },
    #[error(
        "closed host-JIT Core v1 rejects unwind-capable function import {symbol:?} until the install owner proves complete unwind behavior"
    )]
    UnwindCapableFunctionImportUnsupported { symbol: String },
    #[error("initializer-less global import {symbol:?} disagrees with its typed host contract")]
    GlobalContractMismatch { symbol: String },
    #[error("declared-import manifest entry {symbol:?} is not an import of the exact module")]
    UnusedManifestEntry { symbol: String },
    #[error("module contains more than one import named {symbol:?}")]
    DuplicateModuleImport { symbol: String },
    #[error(
        "closed-JIT Core admission rejects every TLS global, including unreferenced global {symbol:?}"
    )]
    ThreadLocalGlobalUnsupported { symbol: String },
    #[error("Core v1 rejects imported global {symbol:?} until JIT binds a typed extern pointer")]
    ImportedGlobalUnsupported { symbol: String },
    #[error("Core v1 rejects module-defined global {symbol:?} until JIT owns an exact data image")]
    DefinedGlobalUnsupported { symbol: String },
    #[error(
        "closed-JIT Core admission rejects exception-handling instruction {instruction} in function {function:?}"
    )]
    ExceptionHandlingUnsupported {
        function: String,
        instruction: &'static str,
    },
    #[error(
        "closed host-JIT Core v1 rejects indirect call in function {function:?} until a finite typed callable-capability receipt exists"
    )]
    IndirectCallUnsupported { function: String },
    #[error("identity-Core v1 rejects dialect instruction in function {function:?}")]
    DialectOperationUnsupported { function: String },
    /// A trust-ir v47/v48/v53/v54/v55/v56 instruction whose meaning no lane
    /// of this backend models: `Inst::Drop` (a destructor), a WEAK
    /// `Inst::CmpXchg` (spurious failure), a v53 non-propagating call boundary
    /// (`Inst::CallCannotUnwind` / `Inst::CallIndirectCannotUnwind`: enforce or
    /// refuse), a v54 panic site (a sited `Inst::Assert`,
    /// `Inst::AssertInvoke`), or a v55 / v56 unwinding twin
    /// (`Inst::DropInvoke`, `Inst::InvokeIndirect`). The native adapter's
    /// shared floor refuses all of them too.
    #[error("identity-Core v1 rejects {instruction} in function {function:?}: no lane models it")]
    UnmodeledInstruction {
        function: String,
        instruction: &'static str,
    },
    /// A v43 nominal opaque runtime handle. Core v1 refuses it for the reason
    /// it refuses an indirect call: the handle's guarantee is that every word
    /// came from a PINNED external runtime declaration, and that runtime is a
    /// trusted-base row this closure holds no receipt for. The native lane
    /// admits the transport (`trust_cg_lower::handle_transport`); Core does
    /// not, until a typed capability receipt for the runtime exists.
    #[error(
        "identity-Core v1 rejects opaque runtime handle handle<{name:?}, {runtime:?}> until a finite typed receipt for its runtime exists"
    )]
    HandleTypeUnsupported { name: String, runtime: String },
    #[error("identity-Core v1 requires legalization of dialect type {namespace}.{name}@{version}")]
    DialectTypeUnsupported {
        namespace: String,
        name: String,
        version: u32,
    },
    #[error("closed host-JIT Core v1 rejects variadic function type #{function_type}")]
    VarArgsUnsupported { function_type: usize },
    #[error("direct call in {caller:?} names missing or ambiguous function id {callee}")]
    InvalidDirectCallTarget { caller: String, callee: u32 },
    #[error(
        "direct call in {caller:?} to bodied function {callee:?} has interposable linkage {linkage:?}"
    )]
    InterposableDefinedFunctionCall {
        caller: String,
        callee: String,
        linkage: Linkage,
    },
    #[error(
        "function identity materialized in {function:?} names bodied target {target:?} with unsupported linkage {linkage:?}"
    )]
    MaterializedDefinedFunctionIdentityUnsupported {
        function: String,
        target: String,
        linkage: Linkage,
    },
    #[error(
        "function identity materialized in {function:?} names missing or ambiguous function id {target}"
    )]
    InvalidMaterializedFunctionTarget { function: String, target: u32 },
    #[error(
        "identity-Core v1 rejects nominal Constant::FnItem({target}) in function {function:?}; nominal identity is not a materialized code address"
    )]
    NominalFunctionItemUnsupported { function: String, target: u32 },
    #[error("identity-Core v1 rejects raw SymbolAddr {symbol:?} in function {function:?}")]
    SymbolAddressUnsupported { function: String, symbol: String },
    #[error("module symbol {symbol:?} must be nonempty, bounded, trimmed, and control-free")]
    InvalidModuleSymbolText { symbol: String },
    #[error("module symbol {symbol:?} occurs more than once in the shared native namespace")]
    DuplicateModuleSymbol { symbol: String },
    #[error(
        "direct call in {caller:?} to {callee:?} would activate undeclared adapter name semantics {semantics:?}"
    )]
    NameDependentCallSemanticsUnsupported {
        caller: String,
        callee: String,
        semantics: AdapterNamedCallSemantics,
    },
}

/// Exact occurrence of faith-stamped certificate evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoreTrustedEvidenceOccurrence {
    certificate_index: usize,
    certificate: ProofCertificateRef,
}

impl CoreTrustedEvidenceOccurrence {
    #[must_use]
    pub const fn certificate_index(&self) -> usize {
        self.certificate_index
    }

    #[must_use]
    pub const fn certificate(&self) -> &ProofCertificateRef {
        &self.certificate
    }
}

/// Exact proof-status and replay census observed during Core admission.
///
/// Status vectors are reporting facts, not proof authority.  Only
/// `replayed_certificate_refs` names evidence actually replayed by the full
/// TrustIR validation pass.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoreProofCensus {
    pending: Vec<trust_ir::ProofId>,
    discharged: Vec<trust_ir::ProofId>,
    failed: Vec<trust_ir::ProofId>,
    trusted: Vec<trust_ir::ProofId>,
    certified: Vec<trust_ir::ProofId>,
    certificate_count: usize,
    trusted_evidence_occurrences: Vec<CoreTrustedEvidenceOccurrence>,
    replayed_certificate_refs: Vec<ProofCertificateRef>,
}

impl CoreProofCensus {
    pub(crate) fn capture(
        module: &Module,
        replayed_certificate_refs: impl IntoIterator<Item = ProofCertificateRef>,
    ) -> Self {
        let mut census = Self {
            pending: Vec::new(),
            discharged: Vec::new(),
            failed: Vec::new(),
            trusted: Vec::new(),
            certified: Vec::new(),
            certificate_count: module.proof_certificates.len(),
            trusted_evidence_occurrences: module
                .proof_certificates
                .iter()
                .enumerate()
                .filter(|(_, certificate)| certificate.uses_trusted_evidence())
                .map(
                    |(certificate_index, certificate)| CoreTrustedEvidenceOccurrence {
                        certificate_index,
                        certificate: certificate.lineage_ref(),
                    },
                )
                .collect(),
            replayed_certificate_refs: replayed_certificate_refs.into_iter().collect(),
        };
        for obligation in &module.proof_obligations {
            match obligation.status {
                ProofStatus::Pending => census.pending.push(obligation.id),
                ProofStatus::Discharged => census.discharged.push(obligation.id),
                ProofStatus::Failed => census.failed.push(obligation.id),
                ProofStatus::Trusted => census.trusted.push(obligation.id),
                ProofStatus::Certified => census.certified.push(obligation.id),
            }
        }
        census.replayed_certificate_refs.sort();
        census
    }

    #[must_use]
    pub fn pending(&self) -> &[trust_ir::ProofId] {
        &self.pending
    }

    #[must_use]
    pub fn discharged(&self) -> &[trust_ir::ProofId] {
        &self.discharged
    }

    #[must_use]
    pub fn failed(&self) -> &[trust_ir::ProofId] {
        &self.failed
    }

    #[must_use]
    pub fn trusted(&self) -> &[trust_ir::ProofId] {
        &self.trusted
    }

    #[must_use]
    pub fn certified(&self) -> &[trust_ir::ProofId] {
        &self.certified
    }

    #[must_use]
    pub const fn certificate_count(&self) -> usize {
        self.certificate_count
    }

    #[must_use]
    pub fn trusted_evidence_occurrences(&self) -> &[CoreTrustedEvidenceOccurrence] {
        &self.trusted_evidence_occurrences
    }

    #[must_use]
    pub fn replayed_certificate_refs(&self) -> &[ProofCertificateRef] {
        &self.replayed_certificate_refs
    }
}

/// Compact arena sizes bound by an identity transform receipt.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct CoreArenaCensus {
    pub functions: usize,
    pub blocks: usize,
    pub block_parameters: usize,
    pub instructions: usize,
    pub instruction_results: usize,
    pub instruction_proof_annotations: usize,
    pub function_proof_annotations: usize,
    pub structs: usize,
    pub enums: usize,
    pub records: usize,
    pub closure_types: usize,
    pub globals: usize,
    pub function_types: usize,
    pub types: usize,
    pub proof_obligations: usize,
    pub proof_certificates: usize,
    pub files: usize,
    pub obligation_diagnostics: usize,
    pub spec_modules: usize,
    pub universes: usize,
    pub predicates: usize,
}

/// Cached executable/call/effect surface from the one admission walk.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoreExecutableSurface {
    defined_functions: Vec<FuncId>,
    imported_functions: Vec<FuncId>,
    defined_globals: Vec<usize>,
    imported_globals: Vec<usize>,
    direct_calls: usize,
    indirect_calls: usize,
    invokes: usize,
    memory_reads: usize,
    memory_writes: usize,
    atomic_operations: usize,
    allocations: usize,
    dialect_operations: usize,
}

impl CoreExecutableSurface {
    #[must_use]
    pub fn defined_functions(&self) -> &[FuncId] {
        &self.defined_functions
    }

    #[must_use]
    pub fn imported_functions(&self) -> &[FuncId] {
        &self.imported_functions
    }

    #[must_use]
    pub fn defined_globals(&self) -> &[usize] {
        &self.defined_globals
    }

    #[must_use]
    pub fn imported_globals(&self) -> &[usize] {
        &self.imported_globals
    }

    #[must_use]
    pub const fn direct_calls(&self) -> usize {
        self.direct_calls
    }

    #[must_use]
    pub const fn indirect_calls(&self) -> usize {
        self.indirect_calls
    }

    #[must_use]
    pub const fn invokes(&self) -> usize {
        self.invokes
    }

    #[must_use]
    pub const fn memory_reads(&self) -> usize {
        self.memory_reads
    }

    #[must_use]
    pub const fn memory_writes(&self) -> usize {
        self.memory_writes
    }

    #[must_use]
    pub const fn atomic_operations(&self) -> usize {
        self.atomic_operations
    }

    #[must_use]
    pub const fn allocations(&self) -> usize {
        self.allocations
    }

    #[must_use]
    pub const fn dialect_operations(&self) -> usize {
        self.dialect_operations
    }
}

/// Receipt for the v1 identity transformation from open to Core TrustIR.
///
/// Equal endpoint digests prove structural identity only.  They do not prove a
/// source refinement theorem or TrustCG machine-code preservation.  The
/// receipt does not contain a canonical digest of retained LIR, so by itself it
/// is not replayable or cross-process strict-lowering authority.  Its strict
/// translation fact is valid only while attached to the opaque in-process
/// [`CoreAdmittedModule`].  Persistent reuse requires a future canonical-LIR
/// identity or deterministic re-lowering identity bound to the complete
/// toolchain and compile profile.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdentityTransformReceipt {
    schema_version: u32,
    permitted_native_mode: CorePermittedNativeMode,
    policy_digest: ProofDigest,
    open_module_digest: ProofDigest,
    core_module_digest: ProofDigest,
    target_contract_digest: ProofDigest,
    declared_import_manifest_digest: ProofDigest,
    arena_census: CoreArenaCensus,
    executable_surface: CoreExecutableSurface,
    module_local_function_identity_census: ModuleLocalFunctionIdentityCensus,
    proof_census: CoreProofCensus,
    lowered_function_count: usize,
    exact_module_call_count: usize,
    declared_external_call_count: usize,
    receipt_digest: ProofDigest,
}

impl IdentityTransformReceipt {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        policy: IdentityCorePolicy,
        module_digest: ProofDigest,
        target_contract_digest: ProofDigest,
        declared_import_manifest_digest: ProofDigest,
        arena_census: CoreArenaCensus,
        executable_surface: CoreExecutableSurface,
        module_local_function_identity_census: ModuleLocalFunctionIdentityCensus,
        proof_census: CoreProofCensus,
        lowered_function_count: usize,
        exact_module_call_count: usize,
        declared_external_call_count: usize,
    ) -> Self {
        let mut receipt = Self {
            schema_version: IDENTITY_CORE_POLICY_SCHEMA_VERSION,
            permitted_native_mode: CorePermittedNativeMode::ClosedHostJit,
            policy_digest: policy.digest(),
            open_module_digest: module_digest,
            core_module_digest: module_digest,
            target_contract_digest,
            declared_import_manifest_digest,
            arena_census,
            executable_surface,
            module_local_function_identity_census,
            proof_census,
            lowered_function_count,
            exact_module_call_count,
            declared_external_call_count,
            receipt_digest: ProofDigest::zero(),
        };
        receipt.receipt_digest = receipt.compute_digest();
        receipt
    }

    #[must_use]
    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    /// The only native consumer permitted by identity admission v1.
    ///
    /// This is not evidence that native compilation or installation succeeded.
    #[must_use]
    pub const fn permitted_native_mode(&self) -> CorePermittedNativeMode {
        self.permitted_native_mode
    }

    #[must_use]
    pub const fn policy_digest(&self) -> ProofDigest {
        self.policy_digest
    }

    #[must_use]
    pub const fn open_module_digest(&self) -> ProofDigest {
        self.open_module_digest
    }

    #[must_use]
    pub const fn core_module_digest(&self) -> ProofDigest {
        self.core_module_digest
    }

    #[must_use]
    pub const fn target_contract_digest(&self) -> ProofDigest {
        self.target_contract_digest
    }

    #[must_use]
    pub const fn declared_import_manifest_digest(&self) -> ProofDigest {
        self.declared_import_manifest_digest
    }

    #[must_use]
    pub const fn arena_census(&self) -> CoreArenaCensus {
        self.arena_census
    }

    #[must_use]
    pub const fn executable_surface(&self) -> &CoreExecutableSurface {
        &self.executable_surface
    }

    /// Source census of identities whose binding depends on this exact module.
    #[must_use]
    pub const fn module_local_function_identity_census(&self) -> ModuleLocalFunctionIdentityCensus {
        self.module_local_function_identity_census
    }

    #[must_use]
    pub const fn proof_census(&self) -> &CoreProofCensus {
        &self.proof_census
    }

    #[must_use]
    pub const fn lowered_function_count(&self) -> usize {
        self.lowered_function_count
    }

    #[must_use]
    pub const fn exact_module_call_count(&self) -> usize {
        self.exact_module_call_count
    }

    #[must_use]
    pub const fn declared_external_call_count(&self) -> usize {
        self.declared_external_call_count
    }

    #[must_use]
    pub const fn receipt_digest(&self) -> ProofDigest {
        self.receipt_digest
    }

    #[must_use]
    pub fn is_intact(&self) -> bool {
        self.schema_version == IDENTITY_CORE_POLICY_SCHEMA_VERSION
            && self.policy_digest == IdentityCorePolicy::v1().digest()
            && self.open_module_digest == self.core_module_digest
            && self.receipt_digest == self.compute_digest()
    }

    fn compute_digest(&self) -> ProofDigest {
        let mut bytes = Vec::new();
        push_u32(&mut bytes, self.schema_version);
        bytes.push(match self.permitted_native_mode {
            CorePermittedNativeMode::ClosedHostJit => 0,
        });
        push_digest(&mut bytes, self.policy_digest);
        push_digest(&mut bytes, self.open_module_digest);
        push_digest(&mut bytes, self.core_module_digest);
        push_digest(&mut bytes, self.target_contract_digest);
        push_digest(&mut bytes, self.declared_import_manifest_digest);
        push_arena_census(&mut bytes, self.arena_census);
        push_executable_surface(&mut bytes, &self.executable_surface);
        push_usize(
            &mut bytes,
            self.module_local_function_identity_census.direct_edges,
        );
        push_usize(
            &mut bytes,
            self.module_local_function_identity_census
                .materialized_identities,
        );
        push_proof_census(&mut bytes, &self.proof_census);
        push_usize(&mut bytes, self.lowered_function_count);
        push_usize(&mut bytes, self.exact_module_call_count);
        push_usize(&mut bytes, self.declared_external_call_count);
        ProofDigest::sha256_domain("trust-cg.core-admission.identity-receipt.v2", &bytes)
    }
}

/// Immutable owner of one validated, identity-lowered Core TrustIR module.
///
/// This owner establishes validated identity-Core plus retained strict LIR.
/// It is not end-to-end JIT lowerability or executable authority: ISel,
/// register allocation, machine validation, link resolution, and installation
/// remain checked downstream.  It also does not authorize a source-language
/// refinement.  The strict adapter result stays sealed so downstream code
/// cannot detach its LIR from the target selected during admission.
///
/// ```compile_fail
/// use trust_cg_codegen::CoreAdmittedModule;
///
/// fn detach_raw_lir(core: CoreAdmittedModule) {
///     // Only the crate-private checked consumer can split this owner.
///     let _ = core.into_consumable_parts();
/// }
/// ```
#[derive(Debug)]
pub struct CoreAdmittedModule {
    module: Arc<Module>,
    target_contract: CoreTargetContract,
    declared_import_manifest: CoreDeclaredImportManifest,
    declared_import_references: CoreDeclaredImportReferenceSeed,
    receipt: IdentityTransformReceipt,
    strict_adapter: StrictCoreAdapterResult,
}

/// Recoverable failure to admit one exact TrustIR module and import manifest.
///
/// Core admission performs validation and strict lowering but does not need to
/// mutate either input. This owner therefore returns both original allocations
/// on every rejection instead of forcing a frontend to clone them before the
/// consuming boundary.
pub struct CoreAdmissionFailure {
    error: CoreAdmissionError,
    module: Module,
    declared_import_manifest: CoreDeclaredImportManifest,
}

impl std::fmt::Debug for CoreAdmissionFailure {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CoreAdmissionFailure")
            .field("error", &self.error)
            .field("module_name", &self.module.name)
            .field("function_count", &self.module.functions.len())
            .field(
                "declared_import_manifest_digest",
                &self.declared_import_manifest.digest(),
            )
            .finish_non_exhaustive()
    }
}

impl std::fmt::Display for CoreAdmissionFailure {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.error, formatter)
    }
}

impl std::error::Error for CoreAdmissionFailure {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.error)
    }
}

impl CoreAdmissionFailure {
    /// Borrow the exact admission diagnostic.
    #[must_use]
    pub const fn reason(&self) -> &CoreAdmissionError {
        &self.error
    }

    /// Borrow the exact rejected TrustIR module.
    #[must_use]
    pub const fn module(&self) -> &Module {
        &self.module
    }

    /// Borrow the exact rejected import manifest.
    #[must_use]
    pub const fn declared_import_manifest(&self) -> &CoreDeclaredImportManifest {
        &self.declared_import_manifest
    }

    /// Recover the diagnostic and both original move-only inputs.
    #[must_use]
    pub fn into_parts(self) -> (CoreAdmissionError, Module, CoreDeclaredImportManifest) {
        (self.error, self.module, self.declared_import_manifest)
    }
}

/// Recoverable failure to admit an immutable shared TrustIR module.
///
/// The exact input share and import manifest are retained without cloning the
/// module graph. Shared ownership conveys no source-language proof standing;
/// the same complete Core admission checks apply to owned and shared inputs.
pub struct CoreSharedAdmissionFailure {
    error: CoreAdmissionError,
    module: Arc<Module>,
    declared_import_manifest: CoreDeclaredImportManifest,
}

impl std::fmt::Debug for CoreSharedAdmissionFailure {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CoreSharedAdmissionFailure")
            .field("error", &self.error)
            .field("module_name", &self.module.name)
            .field("function_count", &self.module.functions.len())
            .field(
                "declared_import_manifest_digest",
                &self.declared_import_manifest.digest(),
            )
            .finish_non_exhaustive()
    }
}

impl std::fmt::Display for CoreSharedAdmissionFailure {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.error, formatter)
    }
}

impl std::error::Error for CoreSharedAdmissionFailure {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.error)
    }
}

impl CoreSharedAdmissionFailure {
    /// Borrow the exact admission diagnostic.
    #[must_use]
    pub const fn reason(&self) -> &CoreAdmissionError {
        &self.error
    }

    /// Borrow the exact rejected module share.
    #[must_use]
    pub const fn module(&self) -> &Arc<Module> {
        &self.module
    }

    /// Borrow the exact rejected import manifest.
    #[must_use]
    pub const fn declared_import_manifest(&self) -> &CoreDeclaredImportManifest {
        &self.declared_import_manifest
    }

    /// Recover the diagnostic, original module share and original manifest.
    #[must_use]
    pub fn into_parts(self) -> (CoreAdmissionError, Arc<Module>, CoreDeclaredImportManifest) {
        (self.error, self.module, self.declared_import_manifest)
    }
}

/// Failure to preserve the sealed in-process Core owner at its one consuming
/// compiler boundary.
///
/// These checks intentionally avoid revalidating or retranslating TrustIR.
/// They join the immutable objects already held by [`CoreAdmittedModule`] and
/// reject internal drift before its retained LIR can be detached.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum CoreConsumptionIntegrityError {
    #[error("the Core identity-transform receipt is not intact")]
    ReceiptNotIntact,
    #[error("the Core receipt does not permit the closed host-JIT consumer")]
    NativeModeMismatch,
    #[error("the Core receipt target digest differs from its attached target contract")]
    TargetContractDigestMismatch,
    #[error("the Core receipt import digest differs from its attached declared-import manifest")]
    DeclaredImportManifestDigestMismatch,
    #[error("the retained strict-adapter target differs from the attached target contract")]
    StrictTargetMismatch,
    #[error(
        "the retained strict LIR contains {actual} functions, but its receipt records {expected}"
    )]
    RetainedFunctionCountMismatch { expected: usize, actual: usize },
    #[error(
        "the retained strict LIR records {actual} exact module calls, but its receipt records {expected}"
    )]
    RetainedExactModuleCallCountMismatch { expected: usize, actual: usize },
    #[error(
        "the retained strict LIR records {actual} declared external calls, but its receipt records {expected}"
    )]
    RetainedDeclaredExternalCallCountMismatch { expected: usize, actual: usize },
    #[error(
        "the retained import-reference seed contains {actual} function identities, but its receipt records {expected}"
    )]
    RetainedImportedFunctionCountMismatch { expected: usize, actual: usize },
    #[error(
        "the retained import-reference seed names FuncId({actual}), but its receipt records FuncId({expected}) at row {index}"
    )]
    RetainedImportedFunctionIdentityMismatch {
        index: usize,
        expected: u32,
        actual: u32,
    },
    #[error("the retained import-reference seed is not intact for its attached manifest")]
    RetainedImportReferenceSeedNotIntact,
}

/// Exact owned inputs detached only by the closed Core compiler boundary.
///
/// This type is crate-private so no public raw-LIR compilation route can skip
/// the target, receipt, and policy checks performed by that consumer.
pub(crate) struct CoreConsumableParts {
    pub(crate) module: Arc<Module>,
    pub(crate) target_contract: CoreTargetContract,
    pub(crate) declared_import_manifest: CoreDeclaredImportManifest,
    pub(crate) receipt: IdentityTransformReceipt,
    pub(crate) lir_functions: Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
}

/// Drift detected while reauthenticating the currently sealed Core planning
/// identities at its proof-grade qualification boundary.
///
/// Qualification authenticates the complete retained strict LIR and every
/// paired [`trust_cg_lower::ProofContext`] against a structured address-free
/// digest. It also replays the source origin, callee name, and `FuncId` of every
/// direct-call carrier; declared-import/native edges additionally replay their
/// sealed coordinates and dependency identity against the dedicated binding
/// receipt.
#[derive(Debug, Error)]
pub enum CoreJitPlanIntegrityError {
    #[error(transparent)]
    IdentityEncoding(#[from] CoreIdentityEncodingError),
    #[error(transparent)]
    RetainedIdentity(#[from] trust_cg_lower::RetainedIdentityError),
    #[error("the Core identity-transform receipt is not intact")]
    ReceiptNotIntact,
    #[error("the Core receipt does not permit the closed host-JIT consumer")]
    NativeModeMismatch,
    #[error("the retained Core module digest is {actual}, but admission records {expected}")]
    ModuleDigestMismatch {
        expected: ProofDigest,
        actual: ProofDigest,
    },
    #[error(
        "the retained strict-LIR/proof-context digest is {actual}, but planning records {expected}"
    )]
    RetainedLirProofContextDigestMismatch {
        expected: ProofDigest,
        actual: ProofDigest,
    },
    #[error("the retained Core target contract is not internally intact")]
    TargetContractNotIntact,
    #[error("the Core receipt target digest differs from its attached target contract")]
    TargetContractDigestMismatch,
    #[error(transparent)]
    TargetContract(#[from] CoreTargetContractError),
    #[error("the retained declared-import manifest is not internally intact")]
    DeclaredImportManifestNotIntact,
    #[error("the Core receipt import digest differs from its attached declared-import manifest")]
    DeclaredImportManifestDigestMismatch,
    #[error("the retained native-runtime catalog is not internally intact")]
    NativeRuntimeCatalogNotIntact,
    #[error("the native-runtime catalog is bound to a different declared-import manifest")]
    NativeRuntimeCatalogManifestMismatch,
    #[error(
        "the native-runtime catalog contains {actual} entries, but the manifest contains {expected}"
    )]
    NativeRuntimeCatalogEntryCountMismatch { expected: usize, actual: usize },
    #[error("native-runtime catalog dependency {dependency} differs from its manifest entry")]
    NativeRuntimeCatalogEntryMismatch { dependency: NativeDependencyId },
    #[error("the retained native-dependency reference map is not internally intact")]
    NativeDependencyReferenceMapNotIntact,
    #[error("the native-dependency reference map is bound to a different Core module")]
    NativeDependencyReferenceMapModuleMismatch,
    #[error("the native-dependency reference map is bound to a different admission receipt")]
    NativeDependencyReferenceMapReceiptMismatch,
    #[error("the native-dependency reference map is bound to a different runtime catalog")]
    NativeDependencyReferenceMapCatalogMismatch,
    #[error(
        "the native-dependency reference map contains {actual} entries, but admission records {expected} imported functions"
    )]
    NativeDependencyReferenceCountMismatch { expected: usize, actual: usize },
    #[error("admitted imported FuncId({function}) has no exact native-dependency reference")]
    NativeDependencyReferenceMissing { function: u32 },
    #[error("native-dependency reference for FuncId({function}) names an invalid source import")]
    NativeDependencyReferenceSourceMismatch { function: u32 },
    #[error(
        "native-dependency reference for FuncId({function}) points to invalid catalog dependency {dependency}"
    )]
    NativeDependencyReferenceCatalogMismatch {
        function: u32,
        dependency: NativeDependencyId,
    },
    #[error("the retained strict-LIR dependency bindings are not internally intact")]
    LirNativeDependencyBindingsNotIntact,
    #[error("the strict-LIR dependency bindings are bound to a different Core module")]
    LirNativeDependencyBindingsModuleMismatch,
    #[error("the strict-LIR dependency bindings are bound to a different admission receipt")]
    LirNativeDependencyBindingsReceiptMismatch,
    #[error("the strict-LIR dependency bindings are bound to a different runtime catalog")]
    LirNativeDependencyBindingsCatalogMismatch,
    #[error("the strict-LIR dependency bindings are bound to a different reference map")]
    LirNativeDependencyBindingsReferenceMapMismatch,
    #[error(
        "the strict-LIR dependency receipt contains {actual} rows, but admission records {expected} imported call carriers"
    )]
    LirNativeDependencyBindingCountMismatch { expected: usize, actual: usize },
    #[error(
        "the retained strict LIR contains {actual} functions, but its receipt records {expected}"
    )]
    RetainedFunctionCountMismatch { expected: usize, actual: usize },
    #[error(
        "the retained strict LIR has {actual} caller identities, but its receipt records {expected} functions"
    )]
    RetainedCallerCountMismatch { expected: usize, actual: usize },
    #[error(
        "strict LIR function {lir_function} has no unique bodied source caller FuncId({caller})"
    )]
    RetainedCallerIdentityMismatch { lir_function: usize, caller: u32 },
    #[error(
        "strict LIR function {lir_function} is named {actual:?}, but source caller FuncId({caller}) is named {expected:?}"
    )]
    RetainedCallerNameMismatch {
        lir_function: usize,
        caller: u32,
        expected: String,
        actual: String,
    },
    #[error(
        "source caller FuncId({caller}) has more instructions than TrustIrInstId can represent"
    )]
    SourceInstructionIdentityOverflow { caller: u32 },
    #[error(
        "source caller FuncId({caller}) instruction {instruction} carries {kind}, a non-propagating call boundary (trust-ir v53) Core does not model; replaying it as an ordinary call would let an unwind cross it"
    )]
    UnsupportedSourceCallUnwindBoundary {
        caller: u32,
        instruction: u32,
        kind: &'static str,
    },
    #[error(
        "strict LIR call at function {lir_function}, block {block}, instruction {instruction} has no source origin"
    )]
    LirCallMissingSourceOrigin {
        lir_function: usize,
        block: u32,
        instruction: usize,
    },
    #[error(
        "strict LIR call at function {lir_function}, block {block}, instruction {instruction} refers to source origin {source_origin}, which is not a direct source call"
    )]
    LirCallSourceOriginMismatch {
        lir_function: usize,
        block: u32,
        instruction: usize,
        source_origin: u32,
    },
    #[error(
        "strict LIR function {lir_function} carries source call origin {source_origin} more than once"
    )]
    DuplicateLirCallSourceOrigin {
        lir_function: usize,
        source_origin: u32,
    },
    #[error(
        "strict LIR call at function {lir_function}, block {block}, instruction {instruction} is named {actual:?}, expected {expected:?}"
    )]
    LirCallNameMismatch {
        lir_function: usize,
        block: u32,
        instruction: usize,
        expected: String,
        actual: String,
    },
    #[error(
        "strict LIR call at function {lir_function}, block {block}, instruction {instruction} has {actual} binding, expected {expected}"
    )]
    LirCallBindingMismatch {
        lir_function: usize,
        block: u32,
        instruction: usize,
        expected: &'static str,
        actual: &'static str,
    },
    #[error(
        "strict LIR call at function {lir_function}, block {block}, instruction {instruction} carries FuncId({actual}), expected FuncId({expected})"
    )]
    LirCallFunctionIdentityMismatch {
        lir_function: usize,
        block: u32,
        instruction: usize,
        expected: u32,
        actual: u32,
    },
    #[error(
        "strict LIR native call at function {lir_function}, block {block}, instruction {instruction} carries dependency {actual}, expected {expected}"
    )]
    LirCallDependencyIdentityMismatch {
        lir_function: usize,
        block: u32,
        instruction: usize,
        expected: NativeDependencyId,
        actual: NativeDependencyId,
    },
    #[error(
        "strict LIR contains an unsupported {kind} call carrier at function {lir_function}, block {block}, instruction {instruction}"
    )]
    UnexpectedLirCallCarrier {
        lir_function: usize,
        block: u32,
        instruction: usize,
        kind: &'static str,
    },
    #[error(
        "strict LIR native call at function {lir_function}, block {block}, instruction {instruction} has no matching binding row"
    )]
    NativeDependencyBindingMissing {
        lir_function: usize,
        block: u32,
        instruction: usize,
    },
    #[error(
        "strict LIR native call at function {lir_function}, block {block}, instruction {instruction} differs from its binding row in {field}"
    )]
    NativeDependencyBindingMismatch {
        lir_function: usize,
        block: u32,
        instruction: usize,
        field: &'static str,
    },
    #[error(
        "strict LIR native call at function {lir_function}, block {block}, instruction {instruction} has a stale edge digest"
    )]
    NativeDependencyEdgeDigestMismatch {
        lir_function: usize,
        block: u32,
        instruction: usize,
    },
    #[error(
        "source caller FuncId({caller}) direct call at origin {source_origin} has no retained strict-LIR carrier"
    )]
    SourceCallCarrierMissing { caller: u32, source_origin: u32 },
    #[error("the strict-LIR dependency receipt has an unconsumed row at index {index}")]
    NativeDependencyBindingRowUnconsumed { index: usize },
    #[error("retained strict LIR has {actual} direct calls, but admission records {expected}")]
    RetainedDirectCallCountMismatch { expected: usize, actual: usize },
    #[error(
        "retained strict LIR has {actual} exact-module calls, but admission records {expected}"
    )]
    RetainedExactModuleCallCountMismatch { expected: usize, actual: usize },
    #[error(
        "retained strict LIR has {actual} native-dependency calls, but admission records {expected}"
    )]
    RetainedNativeDependencyCallCountMismatch { expected: usize, actual: usize },
}

impl CoreConsumableParts {
    /// Authenticate every retained strict-LIR byte of meaning and its paired
    /// proof context before constructing a proof-grade compilation owner.
    pub(crate) fn check_retained_lir_proof_context_integrity(
        &self,
        expected: ProofDigest,
    ) -> Result<(), CoreJitPlanIntegrityError> {
        let actual = trust_cg_lower::retained_lir_proof_context_digest(&self.lir_functions)?;
        if actual != expected {
            return Err(
                CoreJitPlanIntegrityError::RetainedLirProofContextDigestMismatch {
                    expected,
                    actual,
                },
            );
        }
        Ok(())
    }

    /// Reauthenticate the retained module, target, manifest, sidecars, and
    /// dedicated direct-call receipts without consulting process state or
    /// constructing compilation authority. The companion whole-payload check
    /// authenticates all LIR and proof-context fields; this method additionally
    /// replays their semantic joins to the source and native catalog.
    pub(crate) fn check_planned_integrity(
        &self,
        native_runtime_catalog: &CoreNativeRuntimeCatalog,
        native_dependency_references: &CoreNativeDependencyReferenceMap,
        lir_native_dependency_bindings: &CoreLirNativeDependencyBindings,
    ) -> Result<(), CoreJitPlanIntegrityError> {
        if !self.receipt.is_intact() {
            return Err(CoreJitPlanIntegrityError::ReceiptNotIntact);
        }
        if self.receipt.permitted_native_mode() != CorePermittedNativeMode::ClosedHostJit {
            return Err(CoreJitPlanIntegrityError::NativeModeMismatch);
        }

        let module_digest = self.module.stable_digest();
        if module_digest != self.receipt.core_module_digest() {
            return Err(CoreJitPlanIntegrityError::ModuleDigestMismatch {
                expected: self.receipt.core_module_digest(),
                actual: module_digest,
            });
        }
        if !self.target_contract.is_intact() {
            return Err(CoreJitPlanIntegrityError::TargetContractNotIntact);
        }
        if self.receipt.target_contract_digest() != self.target_contract.digest() {
            return Err(CoreJitPlanIntegrityError::TargetContractDigestMismatch);
        }
        self.target_contract.check_module(&self.module)?;
        if !self.declared_import_manifest.is_intact() {
            return Err(CoreJitPlanIntegrityError::DeclaredImportManifestNotIntact);
        }
        if self.receipt.declared_import_manifest_digest() != self.declared_import_manifest.digest()
        {
            return Err(CoreJitPlanIntegrityError::DeclaredImportManifestDigestMismatch);
        }

        if !native_runtime_catalog.is_intact() {
            return Err(CoreJitPlanIntegrityError::NativeRuntimeCatalogNotIntact);
        }
        if native_runtime_catalog.declared_import_manifest_digest()
            != self.declared_import_manifest.digest()
        {
            return Err(CoreJitPlanIntegrityError::NativeRuntimeCatalogManifestMismatch);
        }
        if native_runtime_catalog.entries().len() != self.declared_import_manifest.imports().len() {
            return Err(
                CoreJitPlanIntegrityError::NativeRuntimeCatalogEntryCountMismatch {
                    expected: self.declared_import_manifest.imports().len(),
                    actual: native_runtime_catalog.entries().len(),
                },
            );
        }
        for (entry, import) in native_runtime_catalog
            .entries()
            .iter()
            .zip(self.declared_import_manifest.imports())
        {
            if entry.import() != import {
                return Err(
                    CoreJitPlanIntegrityError::NativeRuntimeCatalogEntryMismatch {
                        dependency: entry.id(),
                    },
                );
            }
        }

        if !native_dependency_references.is_intact() {
            return Err(CoreJitPlanIntegrityError::NativeDependencyReferenceMapNotIntact);
        }
        if native_dependency_references.core_module_digest() != module_digest {
            return Err(CoreJitPlanIntegrityError::NativeDependencyReferenceMapModuleMismatch);
        }
        if native_dependency_references.identity_transform_receipt_digest()
            != self.receipt.receipt_digest()
        {
            return Err(CoreJitPlanIntegrityError::NativeDependencyReferenceMapReceiptMismatch);
        }
        if native_dependency_references.native_runtime_catalog_digest()
            != native_runtime_catalog.digest()
        {
            return Err(CoreJitPlanIntegrityError::NativeDependencyReferenceMapCatalogMismatch);
        }

        let source_functions = ModuleFunctionCatalog::new(&self.module);
        let imported_functions = self.receipt.executable_surface().imported_functions();
        if native_dependency_references.entries().len() != imported_functions.len() {
            return Err(
                CoreJitPlanIntegrityError::NativeDependencyReferenceCountMismatch {
                    expected: imported_functions.len(),
                    actual: native_dependency_references.entries().len(),
                },
            );
        }
        for imported_function in imported_functions {
            let dependency = native_dependency_references
                .dependency_for_function(*imported_function)
                .ok_or(
                    CoreJitPlanIntegrityError::NativeDependencyReferenceMissing {
                        function: imported_function.index(),
                    },
                )?;
            let source = source_functions.unique(*imported_function).ok_or(
                CoreJitPlanIntegrityError::NativeDependencyReferenceSourceMismatch {
                    function: imported_function.index(),
                },
            )?;
            if !source.blocks.is_empty() || source.linkage != Linkage::External {
                return Err(
                    CoreJitPlanIntegrityError::NativeDependencyReferenceSourceMismatch {
                        function: imported_function.index(),
                    },
                );
            }
            let catalog_entry = native_runtime_catalog.get(dependency).ok_or(
                CoreJitPlanIntegrityError::NativeDependencyReferenceCatalogMismatch {
                    function: imported_function.index(),
                    dependency,
                },
            )?;
            let CoreHostImport::Function(catalog_import) = catalog_entry.import() else {
                return Err(
                    CoreJitPlanIntegrityError::NativeDependencyReferenceCatalogMismatch {
                        function: imported_function.index(),
                        dependency,
                    },
                );
            };
            if catalog_import.symbol() != source.name {
                return Err(
                    CoreJitPlanIntegrityError::NativeDependencyReferenceCatalogMismatch {
                        function: imported_function.index(),
                        dependency,
                    },
                );
            }
        }

        if !lir_native_dependency_bindings.is_intact() {
            return Err(CoreJitPlanIntegrityError::LirNativeDependencyBindingsNotIntact);
        }
        if lir_native_dependency_bindings.core_module_digest() != module_digest {
            return Err(CoreJitPlanIntegrityError::LirNativeDependencyBindingsModuleMismatch);
        }
        if lir_native_dependency_bindings.identity_transform_receipt_digest()
            != self.receipt.receipt_digest()
        {
            return Err(CoreJitPlanIntegrityError::LirNativeDependencyBindingsReceiptMismatch);
        }
        if lir_native_dependency_bindings.native_runtime_catalog_digest()
            != native_runtime_catalog.digest()
        {
            return Err(CoreJitPlanIntegrityError::LirNativeDependencyBindingsCatalogMismatch);
        }
        if lir_native_dependency_bindings.native_dependency_reference_map_digest()
            != native_dependency_references.digest()
        {
            return Err(CoreJitPlanIntegrityError::LirNativeDependencyBindingsReferenceMapMismatch);
        }
        if lir_native_dependency_bindings.entries().len()
            != self.receipt.declared_external_call_count()
        {
            return Err(
                CoreJitPlanIntegrityError::LirNativeDependencyBindingCountMismatch {
                    expected: self.receipt.declared_external_call_count(),
                    actual: lir_native_dependency_bindings.entries().len(),
                },
            );
        }

        if self.lir_functions.len() != self.receipt.lowered_function_count() {
            return Err(CoreJitPlanIntegrityError::RetainedFunctionCountMismatch {
                expected: self.receipt.lowered_function_count(),
                actual: self.lir_functions.len(),
            });
        }
        let callers = self.receipt.executable_surface().defined_functions();
        if callers.len() != self.lir_functions.len() {
            return Err(CoreJitPlanIntegrityError::RetainedCallerCountMismatch {
                expected: self.lir_functions.len(),
                actual: callers.len(),
            });
        }

        let mut binding_rows = lir_native_dependency_bindings.entries().iter().enumerate();
        let mut direct_call_count = 0usize;
        let mut exact_module_call_count = 0usize;
        let mut native_dependency_call_count = 0usize;
        for (lir_function, (function, _)) in self.lir_functions.iter().enumerate() {
            let encoded_signature =
                serialize_core_identity(&function.signature, "strict-LIR signature")?;
            let caller = callers[lir_function];
            let source_caller = source_functions.unique(caller).ok_or(
                CoreJitPlanIntegrityError::RetainedCallerIdentityMismatch {
                    lir_function,
                    caller: caller.index(),
                },
            )?;
            if source_caller.blocks.is_empty() {
                return Err(CoreJitPlanIntegrityError::RetainedCallerIdentityMismatch {
                    lir_function,
                    caller: caller.index(),
                });
            }
            if function.name != source_caller.name {
                return Err(CoreJitPlanIntegrityError::RetainedCallerNameMismatch {
                    lir_function,
                    caller: caller.index(),
                    expected: source_caller.name.clone(),
                    actual: function.name.clone(),
                });
            }

            let source_calls = retained_source_direct_calls(source_caller)?;
            let mut seen_source_calls = vec![false; source_calls.len()];

            let mut block_ids: Vec<_> = function.blocks.keys().copied().collect();
            block_ids.sort_unstable();
            for block_id in block_ids {
                let block = &function.blocks[&block_id];
                for (instruction_index, instruction) in block.instructions.iter().enumerate() {
                    let (name, binding) = match &instruction.opcode {
                        trust_cg_lower::instructions::Opcode::Call { name, binding } => {
                            (name, binding)
                        }
                        trust_cg_lower::instructions::Opcode::CallIndirect => {
                            return Err(CoreJitPlanIntegrityError::UnexpectedLirCallCarrier {
                                lir_function,
                                block: block_id.0,
                                instruction: instruction_index,
                                kind: "indirect",
                            });
                        }
                        trust_cg_lower::instructions::Opcode::CallVariadic { .. } => {
                            return Err(CoreJitPlanIntegrityError::UnexpectedLirCallCarrier {
                                lir_function,
                                block: block_id.0,
                                instruction: instruction_index,
                                kind: "variadic",
                            });
                        }
                        trust_cg_lower::instructions::Opcode::Invoke { .. } => {
                            return Err(CoreJitPlanIntegrityError::UnexpectedLirCallCarrier {
                                lir_function,
                                block: block_id.0,
                                instruction: instruction_index,
                                kind: "invoke",
                            });
                        }
                        _ => continue,
                    };
                    direct_call_count += 1;
                    let source_origin = function
                        .trust_ir_origins
                        .get(&block_id)
                        .and_then(|origins| origins.get(instruction_index))
                        .copied()
                        .flatten()
                        .ok_or(CoreJitPlanIntegrityError::LirCallMissingSourceOrigin {
                            lir_function,
                            block: block_id.0,
                            instruction: instruction_index,
                        })?;
                    let source_call_index = source_calls
                        .binary_search_by_key(&source_origin.0, |(origin, _)| origin.0)
                        .map_err(|_| CoreJitPlanIntegrityError::LirCallSourceOriginMismatch {
                            lir_function,
                            block: block_id.0,
                            instruction: instruction_index,
                            source_origin: source_origin.0,
                        })?;
                    if std::mem::replace(&mut seen_source_calls[source_call_index], true) {
                        return Err(CoreJitPlanIntegrityError::DuplicateLirCallSourceOrigin {
                            lir_function,
                            source_origin: source_origin.0,
                        });
                    }
                    let imported_or_local_function = source_calls[source_call_index].1;
                    let source_callee = source_functions.unique(imported_or_local_function).ok_or(
                        CoreJitPlanIntegrityError::LirCallSourceOriginMismatch {
                            lir_function,
                            block: block_id.0,
                            instruction: instruction_index,
                            source_origin: source_origin.0,
                        },
                    )?;
                    if *name != source_callee.name {
                        return Err(CoreJitPlanIntegrityError::LirCallNameMismatch {
                            lir_function,
                            block: block_id.0,
                            instruction: instruction_index,
                            expected: source_callee.name.clone(),
                            actual: name.clone(),
                        });
                    }

                    let expects_exact =
                        !source_callee.blocks.is_empty() && source_callee.linkage.is_module_local();
                    let expects_native = source_callee.blocks.is_empty()
                        && source_callee.linkage == Linkage::External;
                    match binding {
                        trust_cg_lower::instructions::DirectCallBinding::ExactModuleFunction {
                            function: actual_function,
                        } if expects_exact => {
                            if *actual_function != imported_or_local_function.index() {
                                return Err(
                                    CoreJitPlanIntegrityError::LirCallFunctionIdentityMismatch {
                                        lir_function,
                                        block: block_id.0,
                                        instruction: instruction_index,
                                        expected: imported_or_local_function.index(),
                                        actual: *actual_function,
                                    },
                                );
                            }
                            exact_module_call_count += 1;
                        }
                        trust_cg_lower::instructions::DirectCallBinding::NativeDependency {
                            function: actual_function,
                            dependency: actual_dependency,
                        } if expects_native => {
                            if *actual_function != imported_or_local_function.index() {
                                return Err(
                                    CoreJitPlanIntegrityError::LirCallFunctionIdentityMismatch {
                                        lir_function,
                                        block: block_id.0,
                                        instruction: instruction_index,
                                        expected: imported_or_local_function.index(),
                                        actual: *actual_function,
                                    },
                                );
                            }
                            let expected_dependency = native_dependency_references
                                .dependency_for_function(imported_or_local_function)
                                .ok_or(
                                    CoreJitPlanIntegrityError::NativeDependencyReferenceMissing {
                                        function: imported_or_local_function.index(),
                                    },
                                )?;
                            if *actual_dependency != expected_dependency {
                                return Err(
                                    CoreJitPlanIntegrityError::LirCallDependencyIdentityMismatch {
                                        lir_function,
                                        block: block_id.0,
                                        instruction: instruction_index,
                                        expected: expected_dependency,
                                        actual: *actual_dependency,
                                    },
                                );
                            }
                            let (binding_index, binding_row) = binding_rows.next().ok_or(
                                CoreJitPlanIntegrityError::NativeDependencyBindingMissing {
                                    lir_function,
                                    block: block_id.0,
                                    instruction: instruction_index,
                                },
                            )?;
                            let coordinate = (lir_function, block_id.0, instruction_index);
                            if (
                                binding_row.lir_function(),
                                binding_row.block(),
                                binding_row.instruction(),
                            ) != coordinate
                            {
                                let _ = binding_index;
                                return Err(
                                    CoreJitPlanIntegrityError::NativeDependencyBindingMismatch {
                                        lir_function,
                                        block: block_id.0,
                                        instruction: instruction_index,
                                        field: "coordinate",
                                    },
                                );
                            }
                            for (matches, field) in [
                                (binding_row.caller() == caller, "caller"),
                                (
                                    binding_row.source_origin() == source_origin,
                                    "source origin",
                                ),
                                (
                                    binding_row.imported_function() == imported_or_local_function,
                                    "imported function",
                                ),
                                (
                                    binding_row.dependency() == expected_dependency,
                                    "dependency",
                                ),
                            ] {
                                if !matches {
                                    return Err(
                                        CoreJitPlanIntegrityError::NativeDependencyBindingMismatch {
                                            lir_function,
                                            block: block_id.0,
                                            instruction: instruction_index,
                                            field,
                                        },
                                    );
                                }
                            }
                            let expected_edge_digest = core_lir_native_dependency_edge_digest(
                                caller,
                                lir_function,
                                block_id.0,
                                instruction_index,
                                source_origin,
                                imported_or_local_function,
                                expected_dependency,
                                function,
                                &encoded_signature,
                                instruction,
                            )?;
                            if binding_row.edge_digest() != expected_edge_digest {
                                return Err(
                                    CoreJitPlanIntegrityError::NativeDependencyEdgeDigestMismatch {
                                        lir_function,
                                        block: block_id.0,
                                        instruction: instruction_index,
                                    },
                                );
                            }
                            native_dependency_call_count += 1;
                        }
                        actual => {
                            return Err(CoreJitPlanIntegrityError::LirCallBindingMismatch {
                                lir_function,
                                block: block_id.0,
                                instruction: instruction_index,
                                expected: if expects_exact {
                                    "exact-module"
                                } else if expects_native {
                                    "native-dependency"
                                } else {
                                    "admissible Core direct"
                                },
                                actual: direct_call_binding_name(actual),
                            });
                        }
                    }
                }
            }
            if let Some((index, _)) = seen_source_calls
                .iter()
                .enumerate()
                .find(|(_, seen)| !**seen)
            {
                return Err(CoreJitPlanIntegrityError::SourceCallCarrierMissing {
                    caller: caller.index(),
                    source_origin: source_calls[index].0.0,
                });
            }
        }
        if let Some((index, _)) = binding_rows.next() {
            return Err(CoreJitPlanIntegrityError::NativeDependencyBindingRowUnconsumed { index });
        }
        if direct_call_count != self.receipt.executable_surface().direct_calls() {
            return Err(CoreJitPlanIntegrityError::RetainedDirectCallCountMismatch {
                expected: self.receipt.executable_surface().direct_calls(),
                actual: direct_call_count,
            });
        }
        if exact_module_call_count != self.receipt.exact_module_call_count() {
            return Err(
                CoreJitPlanIntegrityError::RetainedExactModuleCallCountMismatch {
                    expected: self.receipt.exact_module_call_count(),
                    actual: exact_module_call_count,
                },
            );
        }
        if native_dependency_call_count != self.receipt.declared_external_call_count() {
            return Err(
                CoreJitPlanIntegrityError::RetainedNativeDependencyCallCountMismatch {
                    expected: self.receipt.declared_external_call_count(),
                    actual: native_dependency_call_count,
                },
            );
        }
        Ok(())
    }
}

/// Replay actual stored source sites, including disconnected blocks. This is
/// an independent backstop, not a reinterpretation of the boundary as a plain
/// LIR call, an effect claim, or a new receipt issuer.
fn retained_source_direct_calls(
    source_caller: &trust_ir::Function,
) -> Result<Vec<(trust_cg_ir::TrustIrInstId, FuncId)>, CoreJitPlanIntegrityError> {
    let mut source_calls = Vec::new();
    for (index, node) in source_caller.instructions().enumerate() {
        let index = u32::try_from(index).map_err(|_| {
            CoreJitPlanIntegrityError::SourceInstructionIdentityOverflow {
                caller: source_caller.id.index(),
            }
        })?;
        let kind = match &node.inst {
            Inst::Call { callee, .. } => {
                source_calls.push((trust_cg_ir::TrustIrInstId(index), *callee));
                continue;
            }
            Inst::CallCannotUnwind { .. } => "Inst::CallCannotUnwind",
            Inst::CallIndirectCannotUnwind { .. } => "Inst::CallIndirectCannotUnwind",
            _ => continue,
        };
        return Err(
            CoreJitPlanIntegrityError::UnsupportedSourceCallUnwindBoundary {
                caller: source_caller.id.index(),
                instruction: index,
                kind,
            },
        );
    }
    Ok(source_calls)
}

fn direct_call_binding_name(
    binding: &trust_cg_lower::instructions::DirectCallBinding,
) -> &'static str {
    match binding {
        trust_cg_lower::instructions::DirectCallBinding::Interposable => "interposable",
        trust_cg_lower::instructions::DirectCallBinding::ExactModuleFunction { .. } => {
            "exact-module"
        }
        trust_cg_lower::instructions::DirectCallBinding::DeclaredExternalFunction { .. } => {
            "declared-external-pending"
        }
        trust_cg_lower::instructions::DirectCallBinding::NativeDependency { .. } => {
            "native-dependency"
        }
    }
}

impl CoreAdmittedModule {
    pub(crate) fn retained_lir_proof_context_digest(
        &self,
    ) -> Result<ProofDigest, trust_cg_lower::RetainedIdentityError> {
        trust_cg_lower::retained_lir_proof_context_digest(self.strict_adapter.functions())
    }

    /// Exact stable digest computed from the owned TrustIR module at admission.
    #[must_use]
    pub const fn module_digest(&self) -> ProofDigest {
        self.receipt.core_module_digest()
    }

    /// Name of the exact owned TrustIR module.
    #[must_use]
    pub fn module_name(&self) -> &str {
        &self.module.name
    }

    /// The exact owned TrustIR module, for a consumer that must re-decide a
    /// policy on it AFTER admission (the Core JIT plan re-runs the compiler's
    /// trust-ir v41 codegen license, which admission applied only at its
    /// default floor). Read-only: the receipt's digest stays authoritative.
    #[must_use]
    pub(crate) fn admitted_module(&self) -> &Module {
        &self.module
    }

    /// Closed target facts derived from the retained strict adapter result.
    #[must_use]
    pub const fn target_contract(&self) -> &CoreTargetContract {
        &self.target_contract
    }

    /// Exact typed TrustIR import declarations bound at admission.
    ///
    /// These rows are declared contracts.  Admission does not inspect the
    /// runtime image and does not prove that its implementations satisfy them.
    /// Backend-synthesized helpers are inventoried only after machine
    /// compilation and are not covered here.
    #[must_use]
    pub const fn declared_import_manifest(&self) -> &CoreDeclaredImportManifest {
        &self.declared_import_manifest
    }

    /// Identity/strict-adapter receipt for the exact module.
    #[must_use]
    pub const fn receipt(&self) -> &IdentityTransformReceipt {
        &self.receipt
    }

    /// Cached proof-status and replay summary from the successful full
    /// TrustIR validation report.
    #[must_use]
    pub const fn proof_census(&self) -> &CoreProofCensus {
        self.receipt.proof_census()
    }

    /// Cached executable/import/effect summary from the admission walk.
    #[must_use]
    pub const fn executable_surface(&self) -> &CoreExecutableSurface {
        self.receipt.executable_surface()
    }

    /// Only native pipeline allowed to consume this owner.  V1 can never
    /// return an AOT mode.
    #[must_use]
    pub const fn permitted_native_mode(&self) -> CorePermittedNativeMode {
        self.receipt.permitted_native_mode()
    }

    /// Number of complete LIR functions retained in the sealed strict result.
    #[must_use]
    pub fn retained_strict_function_count(&self) -> usize {
        self.strict_adapter.functions().len()
    }

    /// Number of exact module-call carriers exhaustively replayed before the
    /// strict result was sealed.
    #[must_use]
    pub const fn retained_exact_module_call_count(&self) -> usize {
        self.strict_adapter.exact_module_call_count()
    }

    /// Number of authenticated pending imported calls retained in strict LIR.
    #[must_use]
    pub const fn retained_declared_external_call_count(&self) -> usize {
        self.strict_adapter.declared_external_call_count()
    }

    /// Check that the exact module/LIR pair is still intact for its only
    /// permitted native consumer.
    ///
    /// This is deliberately crate-private and borrowed. It does not rerun
    /// TrustIR validation, recompute the module digest, or invoke an adapter;
    /// the admitted owner has already done those whole-module operations. The
    /// compiler performs every other fallible preflight before the subsequent
    /// infallible consuming split.
    pub(crate) fn check_consumption_integrity(&self) -> Result<(), CoreConsumptionIntegrityError> {
        if !self.receipt.is_intact() {
            return Err(CoreConsumptionIntegrityError::ReceiptNotIntact);
        }
        if self.receipt.permitted_native_mode() != CorePermittedNativeMode::ClosedHostJit {
            return Err(CoreConsumptionIntegrityError::NativeModeMismatch);
        }
        if self.receipt.target_contract_digest() != self.target_contract.digest() {
            return Err(CoreConsumptionIntegrityError::TargetContractDigestMismatch);
        }
        if self.receipt.declared_import_manifest_digest() != self.declared_import_manifest.digest()
        {
            return Err(CoreConsumptionIntegrityError::DeclaredImportManifestDigestMismatch);
        }
        if self.strict_adapter.target() != &self.target_contract.adapter_target {
            return Err(CoreConsumptionIntegrityError::StrictTargetMismatch);
        }
        let actual_functions = self.strict_adapter.functions().len();
        let expected_functions = self.receipt.lowered_function_count();
        if actual_functions != expected_functions {
            return Err(
                CoreConsumptionIntegrityError::RetainedFunctionCountMismatch {
                    expected: expected_functions,
                    actual: actual_functions,
                },
            );
        }
        let actual_calls = self.strict_adapter.exact_module_call_count();
        let expected_calls = self.receipt.exact_module_call_count();
        if actual_calls != expected_calls {
            return Err(
                CoreConsumptionIntegrityError::RetainedExactModuleCallCountMismatch {
                    expected: expected_calls,
                    actual: actual_calls,
                },
            );
        }
        let actual_external_calls = self.strict_adapter.declared_external_call_count();
        let expected_external_calls = self.receipt.declared_external_call_count();
        if actual_external_calls != expected_external_calls {
            return Err(
                CoreConsumptionIntegrityError::RetainedDeclaredExternalCallCountMismatch {
                    expected: expected_external_calls,
                    actual: actual_external_calls,
                },
            );
        }
        let imported_functions = self.receipt.executable_surface().imported_functions();
        let actual_imported_functions = self.declared_import_references.functions.len();
        if actual_imported_functions != imported_functions.len() {
            return Err(
                CoreConsumptionIntegrityError::RetainedImportedFunctionCountMismatch {
                    expected: imported_functions.len(),
                    actual: actual_imported_functions,
                },
            );
        }
        for (index, (expected, actual)) in imported_functions
            .iter()
            .zip(&self.declared_import_references.functions)
            .enumerate()
        {
            if *expected != actual.function {
                return Err(
                    CoreConsumptionIntegrityError::RetainedImportedFunctionIdentityMismatch {
                        index,
                        expected: expected.index(),
                        actual: actual.function.index(),
                    },
                );
            }
        }
        if !self
            .declared_import_references
            .is_intact(self.declared_import_manifest.digest())
        {
            return Err(CoreConsumptionIntegrityError::RetainedImportReferenceSeedNotIntact);
        }

        Ok(())
    }

    /// Seal the admission-time typed import join into the catalog namespace.
    ///
    /// The private seed was captured while the manifest contract was checked;
    /// this does not rescan source or recover identities from LIR names.
    pub(crate) fn native_dependency_reference_map(
        &self,
        native_runtime_catalog: &CoreNativeRuntimeCatalog,
    ) -> Result<CoreNativeDependencyReferenceMap, CoreNativeDependencyReferenceMapError> {
        CoreNativeDependencyReferenceMap::try_from_admitted_seed(
            self.module_digest(),
            self.receipt.receipt_digest(),
            &self.declared_import_manifest,
            native_runtime_catalog,
            &self.declared_import_references,
        )
    }

    /// Atomically join every strict imported-call `FuncId` to its sealed
    /// catalog-local dependency ID.
    ///
    /// The first pass is read-only and validates the complete carrier census,
    /// provenance, map, and catalog. Only after every possible error has been
    /// ruled out does the second pass replace pending carriers in place. Thus
    /// an error returns the caller's original sealed owner unchanged.
    pub(crate) fn bind_declared_external_calls(
        &mut self,
        native_runtime_catalog: &CoreNativeRuntimeCatalog,
        native_dependency_references: &CoreNativeDependencyReferenceMap,
    ) -> Result<CoreLirNativeDependencyBindings, CoreLirNativeDependencyBindingError> {
        if !native_runtime_catalog.is_intact() {
            return Err(CoreLirNativeDependencyBindingError::CatalogNotIntact);
        }
        if !native_dependency_references.is_intact() {
            return Err(CoreLirNativeDependencyBindingError::ReferenceMapNotIntact);
        }
        if native_runtime_catalog.declared_import_manifest_digest()
            != self.declared_import_manifest.digest()
        {
            return Err(CoreLirNativeDependencyBindingError::CatalogManifestMismatch);
        }
        if native_dependency_references.core_module_digest() != self.module_digest() {
            return Err(CoreLirNativeDependencyBindingError::ReferenceMapModuleMismatch);
        }
        if native_dependency_references.identity_transform_receipt_digest()
            != self.receipt.receipt_digest()
        {
            return Err(CoreLirNativeDependencyBindingError::ReferenceMapReceiptMismatch);
        }
        if native_dependency_references.native_runtime_catalog_digest()
            != native_runtime_catalog.digest()
        {
            return Err(CoreLirNativeDependencyBindingError::ReferenceMapCatalogMismatch);
        }

        let callers = self.receipt.executable_surface().defined_functions();
        let mut entries = Vec::with_capacity(self.receipt.declared_external_call_count());
        for (lir_function, (function, _)) in self.strict_adapter.functions().iter().enumerate() {
            let encoded_signature =
                serialize_core_identity(&function.signature, "strict-LIR signature")?;
            let caller = callers.get(lir_function).copied().ok_or(
                CoreLirNativeDependencyBindingError::MissingCallerIdentity { lir_function },
            )?;
            let mut block_ids: Vec<_> = function.blocks.keys().copied().collect();
            block_ids.sort_unstable();
            for block_id in block_ids {
                let block = &function.blocks[&block_id];
                for (instruction_index, instruction) in block.instructions.iter().enumerate() {
                    let imported_function = match &instruction.opcode {
                        trust_cg_lower::instructions::Opcode::Call {
                            binding:
                                trust_cg_lower::instructions::DirectCallBinding::DeclaredExternalFunction {
                                    function,
                                },
                            ..
                        } => FuncId::new(*function),
                        trust_cg_lower::instructions::Opcode::Call {
                            binding:
                                trust_cg_lower::instructions::DirectCallBinding::NativeDependency {
                                    function,
                                    dependency,
                                },
                            ..
                        } => {
                            return Err(
                                CoreLirNativeDependencyBindingError::PreboundOrForeignDependency {
                                    function: *function,
                                    dependency: *dependency,
                                },
                            );
                        }
                        _ => continue,
                    };
                    let source_origin = function
                        .trust_ir_origins
                        .get(&block_id)
                        .and_then(|origins| origins.get(instruction_index))
                        .copied()
                        .flatten()
                        .ok_or(CoreLirNativeDependencyBindingError::MissingSourceOrigin {
                            lir_function,
                            block: block_id.0,
                            instruction: instruction_index,
                        })?;
                    let dependency = native_dependency_references
                        .dependency_for_function(imported_function)
                        .ok_or(
                            CoreLirNativeDependencyBindingError::MissingImportedFunctionMapping {
                                function: imported_function.index(),
                            },
                        )?;
                    let catalog_entry = native_runtime_catalog.get(dependency).ok_or(
                        CoreLirNativeDependencyBindingError::MissingCatalogDependency {
                            dependency,
                        },
                    )?;
                    if !matches!(catalog_entry.import(), CoreHostImport::Function(_)) {
                        return Err(
                            CoreLirNativeDependencyBindingError::CatalogDependencyKindMismatch {
                                dependency,
                            },
                        );
                    }
                    entries.push(CoreLirNativeDependencyBinding {
                        lir_function,
                        caller,
                        block: block_id.0,
                        instruction: instruction_index,
                        source_origin,
                        imported_function,
                        dependency,
                        edge_digest: core_lir_native_dependency_edge_digest(
                            caller,
                            lir_function,
                            block_id.0,
                            instruction_index,
                            source_origin,
                            imported_function,
                            dependency,
                            function,
                            &encoded_signature,
                            instruction,
                        )?,
                    });
                }
            }
        }
        let expected = self.receipt.declared_external_call_count();
        if entries.len() != expected {
            return Err(CoreLirNativeDependencyBindingError::CarrierCountMismatch {
                expected,
                actual: entries.len(),
            });
        }

        let mut bindings = CoreLirNativeDependencyBindings {
            schema_version: CORE_LIR_NATIVE_DEPENDENCY_BINDINGS_SCHEMA_VERSION,
            coverage: CoreLirNativeDependencyBindingCoverage::DeclaredTrustIrDirectCallsOnly,
            core_module_digest: self.module_digest(),
            identity_transform_receipt_digest: self.receipt.receipt_digest(),
            native_runtime_catalog_digest: native_runtime_catalog.digest(),
            native_dependency_reference_map_digest: native_dependency_references.digest(),
            entries,
            digest: ProofDigest::zero(),
        };
        bindings.digest = bindings.compute_digest();

        // Resolve every mutation target before applying any rewrite. Holding
        // these disjoint mutable references makes disappearance or opcode drift
        // during the commit structurally impossible, without partial mutation
        // if a future validation change leaves a binding coordinate unmatched.
        let coordinates: BTreeMap<_, _> = bindings
            .entries
            .iter()
            .map(|entry| ((entry.lir_function, entry.block, entry.instruction), entry))
            .collect();
        let mut rewrites = Vec::with_capacity(bindings.entries.len());
        for (lir_function, (function, _)) in
            self.strict_adapter.functions_mut().iter_mut().enumerate()
        {
            for (block_id, block) in &mut function.blocks {
                for (instruction_index, instruction) in block.instructions.iter_mut().enumerate() {
                    let Some(entry) =
                        coordinates.get(&(lir_function, block_id.0, instruction_index))
                    else {
                        continue;
                    };
                    if let trust_cg_lower::instructions::Opcode::Call { binding, .. } =
                        &mut instruction.opcode
                        && *binding == (trust_cg_lower::instructions::DirectCallBinding::DeclaredExternalFunction {
                            function: entry.imported_function.index(),
                        })
                    {
                        rewrites.push((binding, *entry));
                    }
                }
            }
        }
        if rewrites.len() != bindings.entries.len() {
            return Err(CoreLirNativeDependencyBindingError::CarrierCountMismatch {
                expected: bindings.entries.len(),
                actual: rewrites.len(),
            });
        }
        for (binding, entry) in rewrites {
            *binding = trust_cg_lower::instructions::DirectCallBinding::NativeDependency {
                function: entry.imported_function.index(),
                dependency: entry.dependency,
            };
        }
        Ok(bindings)
    }

    /// Detach the exact module/LIR pair after a successful borrowed integrity
    /// check and all other planning preflights.
    ///
    /// Keeping the final move infallible makes planning success-atomic: no
    /// recoverable configuration or integrity error destroys the admitted
    /// owner after its retained LIR has been detached.
    pub(crate) fn into_consumable_parts(self) -> CoreConsumableParts {
        let CoreAdmittedModule {
            module,
            target_contract,
            declared_import_manifest,
            declared_import_references: _,
            receipt,
            strict_adapter,
        } = self;
        let lir_functions = strict_adapter.into_functions();
        CoreConsumableParts {
            module,
            target_contract,
            declared_import_manifest,
            receipt,
            lir_functions,
        }
    }

    /// Internal access for the closed-JIT compiler pipeline.  Keeping this
    /// crate-private prevents consumers from treating raw TrustIR as a source
    /// authorization receipt.
    #[cfg(test)]
    fn module(&self) -> &Module {
        &self.module
    }

    /// Internal access to the complete, still-sealed adapter result.
    #[cfg(test)]
    const fn strict_adapter(&self) -> &StrictCoreAdapterResult {
        &self.strict_adapter
    }
}

/// Fail-closed identity-Core admission errors.
#[derive(Debug, Error)]
pub enum CoreAdmissionError {
    #[error("identity-Core admission refuses unkeyed ambient compiler controls: {controls:?}")]
    UnkeyedAmbientCompilerControlsDuringAdmission { controls: Vec<OsString> },

    #[error("identity-Core admission could not acquire a stable compiler-environment permit")]
    AdmissionEnvironmentPermitUnavailable,

    #[error("identity-Core admission observed compiler-control drift during strict translation")]
    AdmissionEnvironmentChanged,

    /// Complete TrustIR validation failed.  No partially replayed evidence is
    /// exposed through a `CoreAdmittedModule`.
    #[error("full TrustIR validation failed: {errors:?}")]
    TrustIrValidation { errors: Vec<ValidationError> },

    /// A successful validation report failed to expose one of its guaranteed
    /// exact-module authority accessors.  This is an internal contract breach.
    #[error("successful TrustIR validation report withheld exact-module authority")]
    ValidationAuthorityUnavailable,

    #[error(transparent)]
    Target(#[from] CoreTargetContractError),

    #[error(transparent)]
    ModuleClosure(#[from] CoreModuleClosureError),

    #[error("closed-JIT Core admission requires at least one defined function")]
    NoDefinedFunctions,

    #[error(
        "closed-JIT Core admission rejects {count} materialized module-local function identities until an exact-reference carrier exists"
    )]
    MaterializedModuleLocalFunctionIdentityUnsupported { count: usize },

    #[error(transparent)]
    StrictAdapter(#[from] StrictCoreAdapterError),

    #[error("strict adapter returned {actual} functions for {expected} defined TrustIR functions")]
    LoweredFunctionCountMismatch { expected: usize, actual: usize },

    #[error(
        "strict adapter retained {actual} declared external calls, expected {expected} from the admitted direct-call surface"
    )]
    DeclaredExternalCallCountMismatch { expected: usize, actual: usize },
}

impl CoreAdmissionError {
    /// Exact errors from the complete TrustIR validation pass, when that pass
    /// was the failing boundary.
    #[must_use]
    pub fn validation_errors(&self) -> Option<&[ValidationError]> {
        match self {
            Self::TrustIrValidation { errors } => Some(errors),
            _ => None,
        }
    }
}

/// Admit one exact TrustIR module into the identity-only, closed-JIT Core
/// profile and retain its strict LIR lowering.
///
/// The function computes [`Module::stable_digest`] exactly once, performs one
/// complete TrustIR validation pass, reuses that report's exact-module and
/// replayed-certificate authority, captures import/effect/census facts in one
/// walk, and invokes the strict adapter once. The caller-supplied opaque target
/// must exactly equal the module metadata; admission reuses its already-captured
/// machine profile and never probes host target facts again. It refuses unkeyed ambient
/// compiler controls and holds a local environment permit across this work so
/// a transient override cannot taint retained LIR and then disappear before
/// publication. The permit is dropped before return to keep the admitted
/// owner movable across threads. The function never clones or rewrites the
/// TrustIR module.
pub fn admit_identity_core_module_for_host_jit(
    module: Module,
    target: &CoreHostJitTarget,
    declared_import_manifest: CoreDeclaredImportManifest,
) -> Result<CoreAdmittedModule, CoreAdmissionError> {
    match try_admit_identity_core_module_for_host_jit(module, target, declared_import_manifest) {
        Ok(admitted) => Ok(admitted),
        Err(failure) => {
            let (error, _module, _declared_import_manifest) = failure.into_parts();
            Err(error)
        }
    }
}

/// Recoverably admit one exact TrustIR module into closed-host-JIT Core.
///
/// This is the ownership-preserving form of
/// [`admit_identity_core_module_for_host_jit`]. It performs the same single
/// digest, validation, inventory, and strict-lowering passes. On every error,
/// [`CoreAdmissionFailure::into_parts`] returns the exact input module and
/// import manifest without a defensive clone.
///
/// ```compile_fail
/// use trust_cg_codegen::{
///     CoreDeclaredImportManifest, CoreHostJitTarget,
///     try_admit_identity_core_module_for_host_jit,
/// };
/// use trust_ir::Module;
///
/// fn cannot_consume_twice(module: Module, target: &CoreHostJitTarget) {
///     let manifest = CoreDeclaredImportManifest::empty();
///     let _first = try_admit_identity_core_module_for_host_jit(module, target, manifest);
///     let _second = try_admit_identity_core_module_for_host_jit(module, target, manifest);
/// }
/// ```
pub fn try_admit_identity_core_module_for_host_jit(
    module: Module,
    target: &CoreHostJitTarget,
    declared_import_manifest: CoreDeclaredImportManifest,
) -> Result<CoreAdmittedModule, CoreAdmissionFailure> {
    match prepare_identity_core_module_for_host_jit(&module, target, &declared_import_manifest) {
        Ok(prepared) => Ok(prepared.into_admitted(Arc::new(module), declared_import_manifest)),
        Err(error) => Err(CoreAdmissionFailure {
            error,
            module,
            declared_import_manifest,
        }),
    }
}

/// Recoverably admit the exact immutable shared module into closed-host-JIT Core.
///
/// This performs the same digest, validation, inventory and strict-lowering
/// passes as [`try_admit_identity_core_module_for_host_jit`]. It does not clone
/// the module graph, detach its contents or accept a substitute from a callback.
/// Every rejection returns the original share and manifest. On success the
/// existing opaque Core owner retains that share through planning and machine
/// compilation; dropping the backend's share does not release a frontend's
/// retained share.
///
/// An `Arc` is only immutable storage custody. Admission grants neither source
/// refinement, machine-code preservation nor permission to execute. A frontend
/// must retain its own checked source/module association across this boundary.
pub fn try_admit_shared_identity_core_module_for_host_jit(
    module: Arc<Module>,
    target: &CoreHostJitTarget,
    declared_import_manifest: CoreDeclaredImportManifest,
) -> Result<CoreAdmittedModule, CoreSharedAdmissionFailure> {
    match prepare_identity_core_module_for_host_jit(&module, target, &declared_import_manifest) {
        Ok(prepared) => Ok(prepared.into_admitted(module, declared_import_manifest)),
        Err(error) => Err(CoreSharedAdmissionFailure {
            error,
            module,
            declared_import_manifest,
        }),
    }
}

struct PreparedCoreAdmission {
    target_contract: CoreTargetContract,
    declared_import_references: CoreDeclaredImportReferenceSeed,
    receipt: IdentityTransformReceipt,
    strict_adapter: StrictCoreAdapterResult,
}

impl PreparedCoreAdmission {
    fn into_admitted(
        self,
        module: Arc<Module>,
        declared_import_manifest: CoreDeclaredImportManifest,
    ) -> CoreAdmittedModule {
        CoreAdmittedModule {
            module,
            target_contract: self.target_contract,
            declared_import_manifest,
            declared_import_references: self.declared_import_references,
            receipt: self.receipt,
            strict_adapter: self.strict_adapter,
        }
    }
}

/// Inventory every type-bearing location, including unused table entries.
/// A nominal semantic type has no Core representation until legalization has
/// discharged its semantic contract. Looking only at live signatures or LIR
/// types would miss pointees erased by pointer lowering.
fn reject_unlegalized_dialect_types(module: &Module) -> Result<(), CoreModuleClosureError> {
    let mut rejection = None;
    module.visit_types(|ty| {
        if rejection.is_none()
            && let Ty::Dialect(ty) = ty
        {
            rejection = Some(CoreModuleClosureError::DialectTypeUnsupported {
                namespace: ty.namespace.clone(),
                name: ty.name.clone(),
                version: ty.version,
            });
        }
    });
    rejection.map_or(Ok(()), Err)
}

/// The same inventory as [`reject_unlegalized_dialect_types`], for the OTHER
/// nominal type: a v43 opaque runtime handle. Unused table entries and
/// pointees erased by pointer lowering are covered for the same reason.
fn reject_opaque_runtime_handle_types(module: &Module) -> Result<(), CoreModuleClosureError> {
    let mut rejection = None;
    module.visit_types(|ty| {
        if rejection.is_none()
            && let Some(handle) = ty.handle_ty()
        {
            rejection = Some(CoreModuleClosureError::HandleTypeUnsupported {
                name: handle.name.clone(),
                runtime: handle.runtime.clone(),
            });
        }
    });
    rejection.map_or(Ok(()), Err)
}

/// Core admission's strict translation of the module `report` authenticates.
/// It skips the adapter's backend-symbol refusal, which Core's own checks
/// replace, and is private to Core admission.
fn translate_validated_core_module_for_target(
    report: &trust_ir_build::ModuleValidationReport<'_>,
    target_spec: TargetSpec,
) -> Result<StrictCoreAdapterResult, StrictCoreAdapterError> {
    // SAFETY: the translated functions stay inside the admitted module. Only
    // `CoreAdmittedModule::into_consumable_parts` (crate-private) releases
    // them, to Core's JIT plan, which emits machine code only through
    // `PolicyQualifiedCoreJitCompilationPlan::compile_to_address_free_machine`
    // after `qualify_for_proof_grade_compilation`. Qualification refuses a
    // retained LIR call without a source call origin, and address-free
    // compilation refuses a machine call without a retained LIR call
    // occurrence (`core_jit_planning` pins both).
    let core_qualification =
        unsafe { trust_cg_lower::CoreQualificationFollows::caller_runs_core_qualification() };
    translate_validated_core_module_under_core_qualification(
        report,
        target_spec,
        core_qualification,
    )
}

fn prepare_identity_core_module_for_host_jit(
    module: &Module,
    target: &CoreHostJitTarget,
    declared_import_manifest: &CoreDeclaredImportManifest,
) -> Result<PreparedCoreAdmission, CoreAdmissionError> {
    let environment = trust_cg_process_env::artifact_reuse_environment_safety();
    if !environment.is_reuse_safe() {
        return Err(
            CoreAdmissionError::UnkeyedAmbientCompilerControlsDuringAdmission {
                controls: environment.unkeyed_controls().to_vec(),
            },
        );
    }
    let environment_permit = trust_cg_process_env::artifact_reuse_permit()
        .ok_or(CoreAdmissionError::AdmissionEnvironmentPermitUnavailable)?;

    target.check_module(module)?;
    reject_unlegalized_dialect_types(module)?;
    reject_opaque_runtime_handle_types(module)?;
    // The receipt is keyed by the module's canonical wire digest, and a
    // construct still ahead of its wire tag (trust-ir's `Inst::binary_wire_gap`:
    // `MakeAggregate`, the WS3.20 bulk-memory pair and bit / copySign sub-ops,
    // an inlining-chain scope link) has none: `stable_digest` would panic on
    // it. Refuse it by name first, as trust-ir's own digest-keyed entry points
    // do.
    if let Some(blocker) = trust_ir_build::wire_identity_blocker(module) {
        return Err(CoreAdmissionError::TrustIrValidation {
            errors: vec![blocker],
        });
    }
    let module_digest = module.stable_digest();

    let report = trust_ir_build::validate_module_report(module);
    if !report.is_ok() {
        return Err(CoreAdmissionError::TrustIrValidation {
            errors: report.into_errors(),
        });
    }
    let validated = report
        .validated_module()
        .ok_or(CoreAdmissionError::ValidationAuthorityUnavailable)?;
    let replayed_certificate_refs = report
        .replayed_certificate_refs()
        .ok_or(CoreAdmissionError::ValidationAuthorityUnavailable)?;

    let proof_census =
        CoreProofCensus::capture(validated, replayed_certificate_refs.iter().cloned());
    let module_local_function_identity_census =
        trust_cg_lower::module_local_function_identity_census(validated);
    if module_local_function_identity_census.materialized_identities != 0 {
        return Err(
            CoreAdmissionError::MaterializedModuleLocalFunctionIdentityUnsupported {
                count: module_local_function_identity_census.materialized_identities,
            },
        );
    }
    let (arena_census, executable_surface, declared_import_references) =
        capture_module_inventory(validated, declared_import_manifest)?;
    if executable_surface.defined_functions.is_empty() {
        return Err(CoreAdmissionError::NoDefinedFunctions);
    }

    let strict_adapter = translate_validated_core_module_for_target(&report, target.target_spec())?;
    let expected_function_count = executable_surface.defined_functions.len();
    let actual_function_count = strict_adapter.functions().len();
    if actual_function_count != expected_function_count {
        return Err(CoreAdmissionError::LoweredFunctionCountMismatch {
            expected: expected_function_count,
            actual: actual_function_count,
        });
    }
    let expected_declared_external_calls = executable_surface
        .direct_calls()
        .checked_sub(strict_adapter.exact_module_call_count())
        .ok_or(CoreAdmissionError::DeclaredExternalCallCountMismatch {
            expected: executable_surface.direct_calls(),
            actual: strict_adapter.exact_module_call_count(),
        })?;
    if strict_adapter.declared_external_call_count() != expected_declared_external_calls {
        return Err(CoreAdmissionError::DeclaredExternalCallCountMismatch {
            expected: expected_declared_external_calls,
            actual: strict_adapter.declared_external_call_count(),
        });
    }

    let target_contract =
        CoreTargetContract::try_from_strict_target(strict_adapter.target().clone(), target)?;
    target_contract.check_module(validated)?;

    let receipt = IdentityTransformReceipt::new(
        IdentityCorePolicy::v1(),
        module_digest,
        target_contract.digest(),
        declared_import_manifest.digest(),
        arena_census,
        executable_surface,
        module_local_function_identity_census,
        proof_census,
        actual_function_count,
        strict_adapter.exact_module_call_count(),
        strict_adapter.declared_external_call_count(),
    );
    drop(report);

    // Do not let a short-lived thread-local compiler control disappear between
    // the initial check and publication of retained strict LIR. The permit is
    // deliberately not stored, so CoreAdmittedModule remains Send.
    if !environment_permit.is_valid() {
        return Err(CoreAdmissionError::AdmissionEnvironmentChanged);
    }

    Ok(PreparedCoreAdmission {
        target_contract,
        declared_import_references,
        receipt,
        strict_adapter,
    })
}

fn capture_module_inventory(
    module: &Module,
    declared_import_manifest: &CoreDeclaredImportManifest,
) -> Result<
    (
        CoreArenaCensus,
        CoreExecutableSurface,
        CoreDeclaredImportReferenceSeed,
    ),
    CoreModuleClosureError,
> {
    let mut census = CoreArenaCensus {
        functions: module.functions.len(),
        structs: module.structs.len(),
        enums: module.enums.len(),
        records: module.records.len(),
        closure_types: module.closure_types.len(),
        globals: module.globals.len(),
        function_types: module.func_types.len(),
        types: module.types.len(),
        proof_obligations: module.proof_obligations.len(),
        proof_certificates: module.proof_certificates.len(),
        files: module.files.len(),
        obligation_diagnostics: module.obligation_diagnostics.len(),
        spec_modules: module.spec_modules.len(),
        universes: module.universes.len(),
        predicates: module.predicates.len(),
        ..CoreArenaCensus::default()
    };
    let mut declared_import_references = CoreDeclaredImportReferenceSeed::default();
    let mut surface = CoreExecutableSurface {
        defined_functions: Vec::new(),
        imported_functions: Vec::new(),
        defined_globals: Vec::new(),
        imported_globals: Vec::new(),
        direct_calls: 0,
        indirect_calls: 0,
        invokes: 0,
        memory_reads: 0,
        memory_writes: 0,
        atomic_operations: 0,
        allocations: 0,
        dialect_operations: 0,
    };
    let mut matched_imports = vec![false; declared_import_manifest.imports.len()];
    let function_catalog = ModuleFunctionCatalog::new(module);
    let mut module_symbols = BTreeSet::new();

    for import in &declared_import_manifest.imports {
        if let CoreHostImport::Function(function) = import
            && function.effects.may_unwind
        {
            return Err(
                CoreModuleClosureError::UnwindCapableFunctionImportUnsupported {
                    symbol: function.symbol.clone(),
                },
            );
        }
    }

    if let Some((function_type, _)) = module
        .func_types
        .iter()
        .enumerate()
        .find(|(_, signature)| signature.is_vararg)
    {
        return Err(CoreModuleClosureError::VarArgsUnsupported { function_type });
    }

    for function in &module.functions {
        if !valid_contract_text(&function.name) {
            return Err(CoreModuleClosureError::InvalidModuleSymbolText {
                symbol: function.name.clone(),
            });
        }
        if !module_symbols.insert(function.name.as_str()) {
            return Err(CoreModuleClosureError::DuplicateModuleSymbol {
                symbol: function.name.clone(),
            });
        }
        census.function_proof_annotations += function.proofs.len();
        if function.blocks.is_empty() {
            if function.linkage != Linkage::External {
                return Err(CoreModuleClosureError::InvalidFunctionImportLinkage {
                    symbol: function.name.clone(),
                    actual: function.linkage,
                });
            }
            surface.imported_functions.push(function.id);
            let signature = module
                .func_types
                .get(function.ty.as_usize())
                .ok_or_else(|| CoreModuleClosureError::InvalidFunctionType {
                    symbol: function.name.clone(),
                    function_type: function.ty.index(),
                })?;
            let index = declared_import_manifest
                .find(0, &function.name)
                .ok_or_else(|| CoreModuleClosureError::MissingFunction {
                    symbol: function.name.clone(),
                })?;
            if matched_imports[index] {
                return Err(CoreModuleClosureError::DuplicateModuleImport {
                    symbol: function.name.clone(),
                });
            }
            let CoreHostImport::Function(import) = &declared_import_manifest.imports[index] else {
                return Err(CoreModuleClosureError::FunctionContractMismatch {
                    symbol: function.name.clone(),
                });
            };
            let parameter_attrs =
                normalized_parameter_attrs(&function.attrs, signature.params.len());
            if import.signature != *signature
                || import.calling_conv != function.calling_conv
                || import.parameter_attrs != parameter_attrs
                || import.effects.memory != declared_memory_effect(&function.attrs)
            {
                return Err(CoreModuleClosureError::FunctionContractMismatch {
                    symbol: function.name.clone(),
                });
            }
            matched_imports[index] = true;
            declared_import_references
                .functions
                .push(CoreDeclaredFunctionReferenceSeed {
                    function: function.id,
                    manifest_index: index,
                });
        } else {
            surface.defined_functions.push(function.id);
        }
        census.blocks += function.blocks.len();
        for block in &function.blocks {
            census.block_parameters += block.params.len();
            census.instructions += block.body.len();
            for node in &block.body {
                census.instruction_results += node.results.len();
                census.instruction_proof_annotations += node.proofs.len();
                match &node.inst {
                    Inst::Call { callee, .. } => {
                        let target = function_catalog.unique(*callee).ok_or_else(|| {
                            CoreModuleClosureError::InvalidDirectCallTarget {
                                caller: function.name.clone(),
                                callee: callee.index(),
                            }
                        })?;
                        let requires_exact_module_binding =
                            !target.blocks.is_empty() && target.linkage.is_module_local();
                        if !requires_exact_module_binding {
                            let semantics = classify_adapter_named_call(&target.name);
                            if semantics != AdapterNamedCallSemantics::Ordinary {
                                return Err(
                                    CoreModuleClosureError::NameDependentCallSemanticsUnsupported {
                                        caller: function.name.clone(),
                                        callee: target.name.clone(),
                                        semantics,
                                    },
                                );
                            }
                        }
                        if !target.blocks.is_empty() && !requires_exact_module_binding {
                            return Err(CoreModuleClosureError::InterposableDefinedFunctionCall {
                                caller: function.name.clone(),
                                callee: target.name.clone(),
                                linkage: target.linkage,
                            });
                        }
                        surface.direct_calls += 1;
                    }
                    Inst::CallIndirect { .. } => {
                        return Err(CoreModuleClosureError::IndirectCallUnsupported {
                            function: function.name.clone(),
                        });
                    }
                    Inst::Invoke { .. } => {
                        return Err(CoreModuleClosureError::ExceptionHandlingUnsupported {
                            function: function.name.clone(),
                            instruction: "invoke",
                        });
                    }
                    Inst::LandingPad { .. } => {
                        return Err(CoreModuleClosureError::ExceptionHandlingUnsupported {
                            function: function.name.clone(),
                            instruction: "landingpad",
                        });
                    }
                    Inst::Resume { .. } => {
                        return Err(CoreModuleClosureError::ExceptionHandlingUnsupported {
                            function: function.name.clone(),
                            instruction: "resume",
                        });
                    }
                    Inst::Load { .. } => surface.memory_reads += 1,
                    Inst::Store { .. } => surface.memory_writes += 1,
                    // trust-ir WS3.20 bulk memory: a copy reads its source and
                    // writes its destination; a fill only writes.
                    Inst::MemCopy { .. } => {
                        surface.memory_reads += 1;
                        surface.memory_writes += 1;
                    }
                    Inst::MemSet { .. } => surface.memory_writes += 1,
                    Inst::AtomicLoad { .. } => {
                        surface.memory_reads += 1;
                        surface.atomic_operations += 1;
                    }
                    Inst::AtomicStore { .. } => {
                        surface.memory_writes += 1;
                        surface.atomic_operations += 1;
                    }
                    Inst::Drop { .. } => {
                        return Err(CoreModuleClosureError::UnmodeledInstruction {
                            function: function.name.clone(),
                            instruction: "Inst::Drop",
                        });
                    }
                    // v53: no lane enforces a non-propagating call boundary,
                    // and counting it as an ordinary call would erase it.
                    Inst::CallCannotUnwind { .. } => {
                        return Err(CoreModuleClosureError::UnmodeledInstruction {
                            function: function.name.clone(),
                            instruction: "Inst::CallCannotUnwind",
                        });
                    }
                    Inst::CallIndirectCannotUnwind { .. } => {
                        return Err(CoreModuleClosureError::UnmodeledInstruction {
                            function: function.name.clone(),
                            instruction: "Inst::CallIndirectCannotUnwind",
                        });
                    }
                    Inst::CmpXchg { weak: true, .. } => {
                        return Err(CoreModuleClosureError::UnmodeledInstruction {
                            function: function.name.clone(),
                            instruction: "Inst::CmpXchg { weak: true }",
                        });
                    }
                    // v54 (amendment P): a sited check's failure calls its
                    // panic entry with its location; no lane lowers that call,
                    // and counting the site as a plain check would erase its
                    // entry and location edges.
                    Inst::Assert { site: Some(_), .. } => {
                        return Err(CoreModuleClosureError::UnmodeledInstruction {
                            function: function.name.clone(),
                            instruction: "Inst::Assert { site: Some(_) }",
                        });
                    }
                    Inst::AssertInvoke { .. } => {
                        return Err(CoreModuleClosureError::UnmodeledInstruction {
                            function: function.name.clone(),
                            instruction: "Inst::AssertInvoke",
                        });
                    }
                    // v55 (amendment D): a drop with an unwind edge runs the
                    // type's glue; no lane lowers a drop, and the census's
                    // wildcard would otherwise count it as no effect.
                    Inst::DropInvoke { .. } => {
                        return Err(CoreModuleClosureError::UnmodeledInstruction {
                            function: function.name.clone(),
                            instruction: "Inst::DropInvoke",
                        });
                    }
                    // v56: an indirect call with an unwind edge; Core admits
                    // neither an indirect call nor an exception edge.
                    Inst::InvokeIndirect { .. } => {
                        return Err(CoreModuleClosureError::UnmodeledInstruction {
                            function: function.name.clone(),
                            instruction: "Inst::InvokeIndirect",
                        });
                    }
                    Inst::MakeClosure { .. } => {
                        return Err(CoreModuleClosureError::UnmodeledInstruction {
                            function: function.name.clone(),
                            instruction: "Inst::MakeClosure",
                        });
                    }
                    Inst::AtomicRMW { .. } | Inst::CmpXchg { weak: false, .. } => {
                        surface.memory_reads += 1;
                        surface.memory_writes += 1;
                        surface.atomic_operations += 1;
                    }
                    Inst::Fence { .. } => surface.atomic_operations += 1,
                    Inst::Alloca { .. } | Inst::HeapAlloc { .. } => surface.allocations += 1,
                    Inst::DialectOp(_) => {
                        return Err(CoreModuleClosureError::DialectOperationUnsupported {
                            function: function.name.clone(),
                        });
                    }
                    Inst::Const { value, .. } => {
                        validate_core_constant_binding(value, function, &function_catalog)?
                    }
                    // trust-ir v50: `n` copies of one SSA value, a pure value
                    // construction like `MakeAggregate`. It reads and writes
                    // no memory and allocates nothing the program can
                    // observe (the lowering fills a frame slot it owns), and
                    // its one operand is an SSA value, not a materialized
                    // constant, so the census records no effect for it.
                    Inst::ArraySplat { .. } => {}
                    _ => {}
                }
            }
        }
    }

    // This admission path rejects every global until JIT data ownership is
    // implemented. Inspect the first one to preserve the specific diagnostic;
    // there is no successful iteration to continue to a later global.
    if let Some(global) = module.globals.first() {
        if !valid_contract_text(&global.name) {
            return Err(CoreModuleClosureError::InvalidModuleSymbolText {
                symbol: global.name.clone(),
            });
        }
        if !module_symbols.insert(global.name.as_str()) {
            return Err(CoreModuleClosureError::DuplicateModuleSymbol {
                symbol: global.name.clone(),
            });
        }
        if global.tls.is_some() {
            return Err(CoreModuleClosureError::ThreadLocalGlobalUnsupported {
                symbol: global.name.clone(),
            });
        }
        if global.initializer.is_none() {
            if global.linkage != Linkage::External {
                return Err(CoreModuleClosureError::InvalidGlobalImportLinkage {
                    symbol: global.name.clone(),
                    actual: global.linkage,
                });
            }
            return Err(CoreModuleClosureError::ImportedGlobalUnsupported {
                symbol: global.name.clone(),
            });
        } else {
            return Err(CoreModuleClosureError::DefinedGlobalUnsupported {
                symbol: global.name.clone(),
            });
        }
    }

    if let Some((_, unused)) = matched_imports
        .iter()
        .zip(&declared_import_manifest.imports)
        .find(|(matched, _)| !**matched)
    {
        return Err(CoreModuleClosureError::UnusedManifestEntry {
            symbol: unused.symbol().to_owned(),
        });
    }
    let declared_import_references =
        declared_import_references.seal(declared_import_manifest.digest());
    Ok((census, surface, declared_import_references))
}

fn validate_core_constant_binding(
    constant: &Constant,
    function: &trust_ir::Function,
    functions: &ModuleFunctionCatalog<'_>,
) -> Result<(), CoreModuleClosureError> {
    let validate_function_target = |target: FuncId| {
        let target_function = functions.unique(target).ok_or_else(|| {
            CoreModuleClosureError::InvalidMaterializedFunctionTarget {
                function: function.name.clone(),
                target: target.index(),
            }
        })?;
        if !target_function.blocks.is_empty() {
            return Err(
                CoreModuleClosureError::MaterializedDefinedFunctionIdentityUnsupported {
                    function: function.name.clone(),
                    target: target_function.name.clone(),
                    linkage: target_function.linkage,
                },
            );
        }
        Ok(())
    };

    match constant {
        Constant::Ext(e) => e.unreachable(),
        Constant::FnDef(target) => validate_function_target(*target),
        Constant::FnItem(target) => Err(CoreModuleClosureError::NominalFunctionItemUnsupported {
            function: function.name.clone(),
            target: target.index(),
        }),
        Constant::Closure { func, captures } => {
            validate_function_target(*func)?;
            for capture in captures {
                validate_core_constant_binding(capture, function, functions)?;
            }
            Ok(())
        }
        Constant::Aggregate(elements)
        | Constant::Array(elements)
        | Constant::Vector(elements)
        | Constant::Sequence(elements)
        | Constant::Set(elements) => {
            for element in elements {
                validate_core_constant_binding(element, function, functions)?;
            }
            Ok(())
        }
        // trust-ir v50: every lane is the one element, checked once.
        Constant::Splat { elem, .. } => validate_core_constant_binding(elem, function, functions),
        Constant::Record(fields) => {
            for (_, value) in fields {
                validate_core_constant_binding(value, function, functions)?;
            }
            Ok(())
        }
        Constant::SymbolAddr { symbol, .. } => {
            Err(CoreModuleClosureError::SymbolAddressUnsupported {
                function: function.name.clone(),
                symbol: symbol.clone(),
            })
        }
        // v49 Uninit names no function; the adapter floor refuses it. A v70
        // weight blob names bytes by digest, never a function.
        Constant::Int(_)
        | Constant::U128(_)
        | Constant::Bytes { .. }
        | Constant::Float(_)
        | Constant::Bool(_)
        | Constant::TensorBlob { .. }
        | Constant::PhantomData
        | Constant::Uninit => Ok(()),
    }
}

fn normalized_parameter_attrs(attrs: &FuncAttrs, arity: usize) -> Vec<ParamAttrs> {
    (0..arity)
        .map(|index| attrs.params.get(index).cloned().unwrap_or_default())
        .collect()
}

fn declared_memory_effect(attrs: &FuncAttrs) -> CoreHostMemoryEffect {
    if attrs.readnone {
        CoreHostMemoryEffect::None
    } else if attrs.readonly {
        CoreHostMemoryEffect::ReadOnly
    } else {
        CoreHostMemoryEffect::ReadWrite
    }
}

fn descriptor_architecture(target: Target) -> TargetArchitecture {
    match target {
        Target::Aarch64 => TargetArchitecture::Aarch64,
        Target::X86_64 => TargetArchitecture::X86_64,
        Target::Riscv64 => TargetArchitecture::Riscv64,
    }
}

fn descriptor_operating_system(target: TargetOperatingSystem) -> ContractOperatingSystem {
    match target {
        TargetOperatingSystem::Darwin => ContractOperatingSystem::Macos,
        TargetOperatingSystem::Linux => ContractOperatingSystem::Linux,
        TargetOperatingSystem::Windows => ContractOperatingSystem::Windows,
        TargetOperatingSystem::Unknown => ContractOperatingSystem::Unknown,
    }
}

fn validate_contract_text(field: &'static str, value: &str) -> Result<(), CoreTargetContractError> {
    if !valid_contract_text(value) {
        return Err(CoreTargetContractError::InvalidContractText { field });
    }
    Ok(())
}

fn validate_host_contract_text(
    field: &'static str,
    value: &str,
) -> Result<(), CoreDeclaredImportManifestError> {
    if !valid_contract_text(value) {
        return Err(CoreDeclaredImportManifestError::InvalidContractText { field });
    }
    Ok(())
}

fn valid_contract_text(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= MAX_CONTRACT_TEXT_BYTES
        && value.trim() == value
        && !value.chars().any(char::is_control)
}

fn core_target_contract_digest(
    adapter_target: &StrictCoreAdapterTarget,
    host_jit_machine_profile: CoreHostJitMachineProfile,
    target_info: &TargetInfo,
) -> Result<ProofDigest, CoreIdentityEncodingError> {
    let mut bytes = Vec::new();
    push_bytes(&mut bytes, adapter_target.target_spec().triple().as_bytes());
    push_bytes(
        &mut bytes,
        &adapter_target.target_descriptor().canonical_bytes(),
    );
    push_abi_descriptor(&mut bytes, adapter_target.abi_descriptor());
    bytes.push(match adapter_target.object_format() {
        StrictCoreObjectFormat::Elf => 0,
        StrictCoreObjectFormat::MachO => 1,
        StrictCoreObjectFormat::Coff => 2,
    });
    bytes.push(match adapter_target.tls_dialect() {
        TlsDialect::MachOTlv => 0,
        TlsDialect::ElfLocalExec => 1,
        TlsDialect::ElfInitialExec => 2,
        TlsDialect::RejectThreadLocals => 3,
        TlsDialect::ElfExecutable => 4,
        TlsDialect::ElfSharedObject => 5,
    });
    match host_jit_machine_profile {
        CoreHostJitMachineProfile::AArch64(profile) => {
            bytes.push(0);
            bytes.extend_from_slice(&profile.feature_bits().to_be_bytes());
        }
        CoreHostJitMachineProfile::X86_64(profile) => {
            bytes.push(1);
            let features = profile.enabled_feature_names();
            push_usize(&mut bytes, features.len());
            for feature in features {
                push_bytes(&mut bytes, feature.as_bytes());
            }
        }
    }
    let target_info = serialize_core_identity(target_info, "TrustIR target metadata")?;
    push_bytes(&mut bytes, &target_info);
    Ok(ProofDigest::sha256_domain(
        CORE_TARGET_CONTRACT_SCHEMA,
        &bytes,
    ))
}

fn push_abi_descriptor(bytes: &mut Vec<u8>, abi: &AbiDescriptor) {
    push_bytes(bytes, abi.name.as_bytes());
    push_bytes(bytes, abi.calling_convention.as_bytes());
    bytes.extend_from_slice(&abi.pointer_width_bits.to_be_bytes());
    bytes.extend_from_slice(&abi.stack_alignment_bytes.to_be_bytes());
    bytes.extend_from_slice(&abi.red_zone_bytes.to_be_bytes());
    bytes.extend_from_slice(&abi.shadow_space_bytes.to_be_bytes());
    for values in [
        abi.integer_argument_registers.as_slice(),
        abi.float_argument_registers.as_slice(),
        abi.integer_return_registers.as_slice(),
        abi.float_return_registers.as_slice(),
        abi.callee_saved_registers.as_slice(),
    ] {
        push_usize(bytes, values.len());
        for value in values {
            push_bytes(bytes, value.as_bytes());
        }
    }
    match &abi.executable_memory_owner {
        ExecutableMemoryOwner::TrustCg => bytes.push(0),
        ExecutableMemoryOwner::Downstream(owner) => {
            bytes.push(1);
            push_bytes(bytes, owner.as_bytes());
        }
        ExecutableMemoryOwner::Unspecified => bytes.push(2),
    }
    match &abi.teardown_policy {
        TeardownPolicy::ProcessLifetime => bytes.push(0),
        TeardownPolicy::RefCounted => bytes.push(1),
        TeardownPolicy::Downstream(policy) => {
            bytes.push(2);
            push_bytes(bytes, policy.as_bytes());
        }
        TeardownPolicy::Unspecified => bytes.push(3),
    }
    match &abi.varargs {
        AbiVarargsPolicy::Unsupported => bytes.push(0),
        AbiVarargsPolicy::C => bytes.push(1),
        AbiVarargsPolicy::Other(policy) => {
            bytes.push(2);
            push_bytes(bytes, policy.as_bytes());
        }
    }
}

fn push_arena_census(bytes: &mut Vec<u8>, census: CoreArenaCensus) {
    for value in [
        census.functions,
        census.blocks,
        census.block_parameters,
        census.instructions,
        census.instruction_results,
        census.instruction_proof_annotations,
        census.function_proof_annotations,
        census.structs,
        census.enums,
        census.records,
        census.closure_types,
        census.globals,
        census.function_types,
        census.types,
        census.proof_obligations,
        census.proof_certificates,
        census.files,
        census.obligation_diagnostics,
        census.spec_modules,
        census.universes,
        census.predicates,
    ] {
        push_usize(bytes, value);
    }
}

fn push_executable_surface(bytes: &mut Vec<u8>, surface: &CoreExecutableSurface) {
    push_usize(bytes, surface.defined_functions.len());
    for function in &surface.defined_functions {
        push_u32(bytes, function.index());
    }
    push_usize(bytes, surface.imported_functions.len());
    for function in &surface.imported_functions {
        push_u32(bytes, function.index());
    }
    push_usize(bytes, surface.defined_globals.len());
    for global in &surface.defined_globals {
        push_usize(bytes, *global);
    }
    push_usize(bytes, surface.imported_globals.len());
    for global in &surface.imported_globals {
        push_usize(bytes, *global);
    }
    for value in [
        surface.direct_calls,
        surface.indirect_calls,
        surface.invokes,
        surface.memory_reads,
        surface.memory_writes,
        surface.atomic_operations,
        surface.allocations,
        surface.dialect_operations,
    ] {
        push_usize(bytes, value);
    }
}

fn push_proof_census(bytes: &mut Vec<u8>, census: &CoreProofCensus) {
    for ids in [
        census.pending.as_slice(),
        census.discharged.as_slice(),
        census.failed.as_slice(),
        census.trusted.as_slice(),
        census.certified.as_slice(),
    ] {
        push_usize(bytes, ids.len());
        for id in ids {
            push_u32(bytes, id.index());
        }
    }
    push_usize(bytes, census.certificate_count);
    push_usize(bytes, census.trusted_evidence_occurrences.len());
    for occurrence in &census.trusted_evidence_occurrences {
        push_usize(bytes, occurrence.certificate_index);
        push_u32(bytes, occurrence.certificate.obligation.index());
        push_bytes(bytes, occurrence.certificate.prover.as_bytes());
        push_digest(bytes, occurrence.certificate.evidence_digest);
    }
    push_usize(bytes, census.replayed_certificate_refs.len());
    for certificate in &census.replayed_certificate_refs {
        push_u32(bytes, certificate.obligation.index());
        push_bytes(bytes, certificate.prover.as_bytes());
        push_digest(bytes, certificate.evidence_digest);
    }
}

fn push_digest(bytes: &mut Vec<u8>, digest: ProofDigest) {
    bytes.push(match digest.algorithm {
        ProofDigestAlgorithm::Sha256 => 0,
        ProofDigestAlgorithm::TrustIrStableV1 => 1,
    });
    bytes.extend_from_slice(&digest.bytes);
}

#[allow(clippy::too_many_arguments)]
fn core_lir_native_dependency_edge_digest(
    caller: FuncId,
    lir_function: usize,
    block: u32,
    instruction_index: usize,
    source_origin: trust_cg_ir::TrustIrInstId,
    imported_function: FuncId,
    dependency: NativeDependencyId,
    function: &trust_cg_lower::Function,
    encoded_signature: &[u8],
    instruction: &trust_cg_lower::instructions::Instruction,
) -> Result<ProofDigest, CoreIdentityEncodingError> {
    let mut bytes = Vec::new();
    push_u32(&mut bytes, caller.index());
    push_usize(&mut bytes, lir_function);
    push_u32(&mut bytes, block);
    push_usize(&mut bytes, instruction_index);
    push_u32(&mut bytes, source_origin.0);
    push_u32(&mut bytes, imported_function.index());
    push_u32(&mut bytes, dependency.index());
    push_bytes(&mut bytes, function.name.as_bytes());
    push_bytes(&mut bytes, encoded_signature);
    match &instruction.opcode {
        trust_cg_lower::instructions::Opcode::Call { name, .. } => {
            bytes.push(1);
            push_bytes(&mut bytes, name.as_bytes());
        }
        _ => bytes.push(0),
    }
    match function
        .blocks
        .get(&trust_cg_lower::instructions::Block(block))
        .and_then(|block| block.source_locs.get(instruction_index))
        .copied()
        .flatten()
    {
        Some(source_loc) => {
            bytes.push(1);
            push_u32(&mut bytes, source_loc.file);
            push_u32(&mut bytes, source_loc.line);
            push_u32(&mut bytes, source_loc.col);
        }
        None => bytes.push(0),
    }
    push_usize(&mut bytes, instruction.args.len());
    for value in &instruction.args {
        push_u32(&mut bytes, value.0);
        push_lir_value_type(&mut bytes, function, *value)?;
    }
    push_usize(&mut bytes, instruction.results.len());
    for value in &instruction.results {
        push_u32(&mut bytes, value.0);
        push_lir_value_type(&mut bytes, function, *value)?;
    }
    Ok(ProofDigest::sha256_domain(
        "trust-cg.core-lir-native-dependency-edge.v2",
        &bytes,
    ))
}

fn push_lir_value_type(
    bytes: &mut Vec<u8>,
    function: &trust_cg_lower::Function,
    value: trust_cg_lower::instructions::Value,
) -> Result<(), CoreIdentityEncodingError> {
    // Match the effective default used by both instruction selectors. An
    // absent type hint and an explicit I64 hint are semantically identical;
    // any different selected call value type changes this edge identity.
    let value_type = function
        .value_types
        .get(&value)
        .cloned()
        .unwrap_or(trust_cg_lower::types::Type::I64);
    let encoded = serialize_core_identity(&value_type, "strict-LIR value type")?;
    push_bytes(bytes, &encoded);
    Ok(())
}

fn push_bytes(bytes: &mut Vec<u8>, value: &[u8]) {
    push_usize(bytes, value.len());
    bytes.extend_from_slice(value);
}

fn push_usize(bytes: &mut Vec<u8>, value: usize) {
    // The canonical format admits every host-sized count on supported builds.
    // Refuse compilation on a wider host instead of truncating an identity.
    const {
        assert!(usize::BITS <= u64::BITS);
    }
    let value = value as u64;
    bytes.extend_from_slice(&value.to_be_bytes());
}

/// A canonical identity payload could not be serialized. No digest is issued
/// for partial or missing bytes; ownership remains at the rejecting boundary.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[error("could not encode Core {context} identity: {reason}")]
pub struct CoreIdentityEncodingError {
    context: &'static str,
    reason: String,
}

fn serialize_core_identity<T: Serialize + ?Sized>(
    value: &T,
    context: &'static str,
) -> Result<Vec<u8>, CoreIdentityEncodingError> {
    serde_json::to_vec(value).map_err(|error| CoreIdentityEncodingError {
        context,
        reason: error.to_string(),
    })
}

fn push_u32(bytes: &mut Vec<u8>, value: u32) {
    bytes.extend_from_slice(&value.to_be_bytes());
}

#[cfg(test)]
#[path = "core_shared_admission_tests.rs"]
mod shared_custody_tests;

#[cfg(test)]
#[path = "core_admission_target_binding_tests.rs"]
mod target_binding_tests;

#[cfg(test)]
mod tests {
    use super::*;

    /// This file's fixtures are hand-built and carry no codegen license
    /// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
    /// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
    /// them passes because it was silently refused.
    fn permit_unlicensed() -> crate::CodegenLicensePolicy {
        crate::CodegenLicensePolicy::default().with_unlicensed(crate::UnlicensedBodyPolicy::Permit)
    }
    use trust_ir::{Block, Constant, FuncTyId, Function, Global, InstrNode, ValueId};

    #[test]
    fn canonical_empty_manifest_matches_the_general_encoder() {
        let empty = CoreDeclaredImportManifest::empty();
        assert!(empty.is_intact());
        assert_eq!(
            empty,
            CoreDeclaredImportManifest::try_new(Vec::new()).unwrap()
        );
    }

    #[test]
    fn identity_encoding_refuses_partial_serialization() {
        struct RejectedPayload;
        impl Serialize for RejectedPayload {
            fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                use serde::ser::{Error, SerializeSeq};
                let mut sequence = serializer.serialize_seq(Some(2))?;
                sequence.serialize_element("partial identity")?;
                Err(S::Error::custom("injected payload refusal"))
            }
        }
        let error = serialize_core_identity(&RejectedPayload, "test payload").unwrap_err();
        assert_eq!(error.context, "test payload");
        assert!(error.reason.contains("injected payload refusal"));
    }

    #[test]
    fn canonical_count_encoding_covers_the_supported_host_domain() {
        let mut bytes = Vec::new();
        push_usize(&mut bytes, usize::MAX);
        assert_eq!(bytes, (usize::MAX as u64).to_be_bytes());
    }

    const EXACT_CORE_HOST_SUPPORTED: bool = cfg!(any(
        all(
            target_arch = "aarch64",
            target_vendor = "apple",
            target_os = "macos",
            target_env = "",
            target_abi = "",
            target_pointer_width = "64",
            target_endian = "little"
        ),
        all(
            target_arch = "aarch64",
            target_vendor = "unknown",
            target_os = "linux",
            target_env = "gnu",
            target_abi = "",
            target_pointer_width = "64",
            target_endian = "little"
        ),
        all(
            target_arch = "x86_64",
            target_vendor = "apple",
            target_os = "macos",
            target_env = "",
            target_abi = "",
            target_pointer_width = "64",
            target_endian = "little"
        ),
        all(
            target_arch = "x86_64",
            target_vendor = "unknown",
            target_os = "linux",
            target_env = "gnu",
            target_abi = "",
            target_pointer_width = "64",
            target_endian = "little"
        ),
        all(
            target_arch = "x86_64",
            target_vendor = "pc",
            target_os = "windows",
            target_env = "msvc",
            target_abi = "",
            target_pointer_width = "64",
            target_endian = "little"
        )
    ));

    pub(super) fn core_host_target() -> CoreHostJitTarget {
        CoreHostJitTarget::try_from_detected_facts(
            Target::Aarch64,
            TargetVendor::Unknown,
            TargetOperatingSystem::Linux,
            TargetEnvironment::Gnu,
            true,
            8,
            trust_ir::Endianness::Little,
            CoreHostJitMachineProfile::AArch64(AArch64IsaProfile::BASELINE),
        )
        .expect("fixed test target must remain supported")
    }

    fn exact_spec() -> TargetSpec {
        core_host_target().target_spec()
    }

    fn self_contained_module_for_target(
        target: &CoreHostJitTarget,
        name: impl Into<String>,
    ) -> Module {
        let mut module = Module::new(name);
        module.target_info = Some(target.trust_ir_target_info().clone());
        let function_type = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(
            FuncId::new(0),
            "entry",
            function_type,
            trust_ir::BlockId::new(0),
        );
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
        module
    }

    pub(super) fn self_contained_module() -> Module {
        let target = core_host_target();
        self_contained_module_for_target(&target, "self-contained-core-fixture")
    }

    fn semantic_type() -> Ty {
        Ty::Dialect(Box::new(trust_ir::DialectTy::new("tla", "Value", 1)))
    }

    #[test]
    fn dialect_type_gate_covers_unused_tables_and_instruction_types() {
        type InsertType = fn(&mut Module, Ty);
        let locations: &[(&str, InsertType)] = &[
            ("unused parameter", |module, ty| {
                module
                    .add_func_type(FuncTy {
                        params: vec![ty],
                        returns: vec![],
                        abi: None,
                        is_vararg: false,
                    })
                    .expect("Module::add_func_type: test fixture");
            }),
            ("unused return", |module, ty| {
                module
                    .add_func_type(FuncTy {
                        params: vec![],
                        returns: vec![ty],
                        abi: None,
                        is_vararg: false,
                    })
                    .expect("Module::add_func_type: test fixture");
            }),
            ("unused type table", |module, ty| module.types.push(ty)),
            ("unused struct", |module, ty| {
                module.structs.push(trust_ir::StructDef {
                    origin: None,
                    id: trust_ir::StructId::new(0),
                    name: "Unused".into(),
                    fields: vec![trust_ir::FieldDef {
                        name: "value".into(),
                        ty,
                        offset: None,
                    }],
                    size: None,
                    align: None,
                    repr: trust_ir::StructRepr::Rust,
                });
            }),
            ("unused enum", |module, ty| {
                module.enums.push(trust_ir::EnumDef::new(
                    trust_ir::EnumId::new(0),
                    "Unused",
                    vec![trust_ir::EnumVariant {
                        name: "Value".into(),
                        fields: vec![ty],
                        field_names: vec![],
                    }],
                ));
            }),
            ("unused record", |module, ty| {
                module.records.push(trust_ir::RecordDef {
                    id: trust_ir::RecordId::new(0),
                    name: "Unused".into(),
                    fields: vec![trust_ir::FieldDef {
                        name: "value".into(),
                        ty,
                        offset: None,
                    }],
                });
            }),
            ("unused closure capture", |module, ty| {
                module.closure_types.push(trust_ir::ClosureTy {
                    func: FuncTyId::new(0),
                    captures: vec![ty],
                });
            }),
            ("unused global", |module, ty| {
                module.globals.push(Global {
                    section: None,
                    visibility: trust_ir::Visibility::Default,
                    retained: false,
                    name: "unused".into(),
                    ty,
                    mutable: false,
                    initializer: None,
                    linkage: Linkage::External,
                    tls: None,
                    align: None,
                });
            }),
            ("block parameter", |module, ty| {
                module.functions[0].blocks[0]
                    .params
                    .push((ValueId::new(0), ty));
            }),
            ("cast source", |module, ty| {
                module.functions[0].blocks[0].body.insert(
                    0,
                    InstrNode::new(Inst::Cast {
                        op: trust_ir::CastOp::Bitcast,
                        src_ty: ty,
                        dst_ty: Ty::I64,
                        operand: ValueId::new(0),
                    }),
                );
            }),
            ("cast destination", |module, ty| {
                module.functions[0].blocks[0].body.insert(
                    0,
                    InstrNode::new(Inst::Cast {
                        op: trust_ir::CastOp::Bitcast,
                        src_ty: Ty::I64,
                        dst_ty: ty,
                        operand: ValueId::new(0),
                    }),
                );
            }),
            ("binding frame", |module, ty| {
                module.functions[0].blocks[0].body.insert(
                    0,
                    InstrNode::new(Inst::OpenFrame {
                        def: trust_ir::inst::BindingFrameDef::new(
                            trust_ir::value::BindingFrameId::new(0),
                            "frame",
                            vec![trust_ir::inst::BindingSlot::new("slot", ty)],
                        ),
                    }),
                );
            }),
            ("dialect result", |module, ty| {
                module.functions[0].blocks[0].body.insert(
                    0,
                    InstrNode::new(Inst::DialectOp(Box::new(
                        trust_ir::DialectInst::new("tla", "value").with_result_ty(ty),
                    ))),
                );
            }),
            ("dialect type attribute", |module, ty| {
                module.functions[0].blocks[0].body.insert(
                    0,
                    InstrNode::new(Inst::DialectOp(Box::new(
                        trust_ir::DialectInst::new("tla", "value")
                            .with_attr("type", trust_ir::dialect::AttrValue::Ty(ty)),
                    ))),
                );
            }),
        ];
        for (location, insert) in locations {
            let mut module = self_contained_module();
            // An unrelated cyclic type table must not cause graph recursion.
            module.types.push(Ty::Array(trust_ir::TyId::new(0), 1));
            insert(
                &mut module,
                Ty::PtrConst(Box::new(Ty::Tuple(vec![Ty::I64, semantic_type()]))),
            );
            assert!(
                matches!(
                    reject_unlegalized_dialect_types(&module),
                    Err(CoreModuleClosureError::DialectTypeUnsupported { namespace, name, version: 1 })
                        if namespace == "tla" && name == "Value"
                ),
                "unlegalized type escaped from {location}"
            );
        }
    }

    #[test]
    fn dialect_type_gate_covers_every_inline_type_wrapper() {
        let wrappers: &[fn(Ty) -> Ty] = &[
            |ty| ty,
            |ty| Ty::Ref(Box::new(ty)),
            |ty| Ty::RefMut(Box::new(ty)),
            |ty| Ty::PtrConst(Box::new(ty)),
            |ty| Ty::PtrMut(Box::new(ty)),
            |ty| Ty::Rc(Box::new(ty)),
            |ty| Ty::Vector(Box::new(ty), 2),
            |ty| Ty::Tuple(vec![Ty::I64, ty]),
        ];
        for wrap in wrappers {
            let mut module = self_contained_module();
            module.types.push(wrap(semantic_type()));
            assert!(matches!(
                reject_unlegalized_dialect_types(&module),
                Err(CoreModuleClosureError::DialectTypeUnsupported { .. })
            ));
        }
        assert!(reject_unlegalized_dialect_types(&self_contained_module()).is_ok());
    }

    #[test]
    fn opaque_handle_type_gate_covers_unused_tables_and_inline_wrappers() {
        // identity-Core v1 refuses a v43 handle for the reason it refuses an
        // indirect call: the guarantee behind the word is a trusted-base row
        // (the runtime) this closure holds no receipt for. Unused table
        // entries count, exactly as they do for a dialect type.
        let handle = Ty::handle("Nat", "trust_bignum::Nat");
        let wrappers: &[fn(Ty) -> Ty] = &[
            |ty| ty,
            |ty| Ty::Ref(Box::new(ty)),
            |ty| Ty::PtrConst(Box::new(ty)),
            |ty| Ty::Vector(Box::new(ty), 2),
            |ty| Ty::Tuple(vec![Ty::I64, ty]),
        ];
        for wrap in wrappers {
            let mut module = self_contained_module();
            module.types.push(wrap(handle.clone()));
            assert!(matches!(
                reject_opaque_runtime_handle_types(&module),
                Err(CoreModuleClosureError::HandleTypeUnsupported { ref name, ref runtime })
                    if name == "Nat" && runtime == "trust_bignum::Nat"
            ));
        }
        assert!(reject_opaque_runtime_handle_types(&self_contained_module()).is_ok());
    }

    #[test]
    fn opaque_handle_type_admission_rejection_returns_exact_owners() {
        let target = core_host_target();
        let mut module = module_with_import();
        let manifest = import_manifest(&module);
        let handle = Ty::handle("Nat", "trust_bignum::Nat");
        module.types.push(handle.clone());
        let functions = module.functions.as_ptr();
        let failure = try_admit_identity_core_module_for_host_jit(module, &target, manifest)
            .expect_err("an unused opaque runtime handle must fail Core admission");
        let (error, module, _manifest) = failure.into_parts();
        assert!(matches!(
            error,
            CoreAdmissionError::ModuleClosure(CoreModuleClosureError::HandleTypeUnsupported { .. })
        ));
        assert_eq!(module.functions.as_ptr(), functions);
        assert_eq!(module.types.last(), Some(&handle));
    }

    #[test]
    fn dialect_type_admission_rejection_returns_exact_owners() {
        let target = core_host_target();
        let mut module = module_with_import();
        let manifest = import_manifest(&module);
        module.types.push(semantic_type());
        let functions = module.functions.as_ptr();
        let types = module.types.as_ptr();
        let imports = manifest.imports.as_ptr();
        let failure = try_admit_identity_core_module_for_host_jit(module, &target, manifest)
            .expect_err("unused semantic type must fail Core admission");
        let (error, module, manifest) = failure.into_parts();
        assert!(matches!(
            error,
            CoreAdmissionError::ModuleClosure(
                CoreModuleClosureError::DialectTypeUnsupported { .. }
            )
        ));
        assert_eq!(module.functions.as_ptr(), functions);
        assert_eq!(module.types.as_ptr(), types);
        assert_eq!(manifest.imports.as_ptr(), imports);
        assert_eq!(module.types.last(), Some(&semantic_type()));
    }

    fn target_contract() -> CoreTargetContract {
        let target = core_host_target();
        let module = self_contained_module();
        let report = trust_ir_build::validate_module_report(&module);
        let strict = translate_validated_core_module_for_target(&report, target.target_spec())
            .expect("fixture must strict-lower");
        CoreTargetContract::try_from_strict_target(strict.target().clone(), &target).unwrap()
    }

    pub(super) fn module_with_import() -> Module {
        let target = core_host_target();
        let mut module = Module::new("core-fixture");
        module.target_info = Some(target.trust_ir_target_info().clone());
        let imported_ty = module
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut imported = Function::new(
            FuncId::new(0),
            "runtime_inc",
            imported_ty,
            trust_ir::BlockId::new(0),
        );
        imported.attrs.readnone = true;
        imported.linkage = Linkage::External;
        module
            .try_add_function(imported)
            .expect("Module::try_add_function: test fixture");

        let body_ty = module
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut body = Function::new(FuncId::new(1), "entry", body_ty, trust_ir::BlockId::new(0));
        body.linkage = Linkage::Internal;
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.params.push((ValueId::new(0), Ty::I64));
        block.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(1)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }));
        body.blocks.push(block);
        module
            .try_add_function(body)
            .expect("Module::try_add_function: test fixture");
        module
    }

    pub(super) fn module_with_exact_call() -> Module {
        let target = core_host_target();
        let mut module = Module::new("core-exact-call-fixture");
        module.target_info = Some(target.trust_ir_target_info().clone());
        let signature = module
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

        let mut local = Function::new(
            FuncId::new(0),
            "local_inc",
            signature,
            trust_ir::BlockId::new(0),
        );
        local.linkage = Linkage::Internal;
        let mut local_block = Block::new(trust_ir::BlockId::new(0));
        local_block.params.push((ValueId::new(0), Ty::I64));
        local_block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        local.blocks.push(local_block);
        module
            .try_add_function(local)
            .expect("Module::try_add_function: test fixture");

        let mut entry = Function::new(
            FuncId::new(1),
            "entry",
            signature,
            trust_ir::BlockId::new(0),
        );
        entry.linkage = Linkage::Internal;
        let mut entry_block = Block::new(trust_ir::BlockId::new(0));
        entry_block.params.push((ValueId::new(0), Ty::I64));
        entry_block.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(1)),
        );
        entry_block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }));
        entry.blocks.push(entry_block);
        module
            .try_add_function(entry)
            .expect("Module::try_add_function: test fixture");
        module
    }

    fn runtime() -> CoreRuntimeIdentity {
        CoreRuntimeIdentity::try_new(
            "ty-runtime-v1",
            ProofDigest::sha256_domain("test.runtime", b"exact runtime bytes"),
        )
        .unwrap()
    }

    #[test]
    fn closed_jit_profile_binds_the_exact_detected_host() {
        if !EXACT_CORE_HOST_SUPPORTED {
            assert!(CoreHostJitTarget::detect().is_err());
            return;
        }
        let detected = Target::try_host().expect("cfg-supported Core host must be represented");
        let target = CoreHostJitTarget::detect()
            .expect("AArch64 and x86-64 hosts are admitted by the Core JIT profile");
        assert_eq!(target.target_spec().architecture, detected);
        assert_eq!(target.machine_profile().architecture(), detected);
        assert!(target.target_spec().has_explicit_os_abi());
        assert_eq!(
            target.trust_ir_target_info().triple,
            target.target_spec().triple()
        );
        assert_eq!(
            target.trust_ir_target_info().pointer_size as usize,
            std::mem::size_of::<usize>()
        );
        assert_eq!(
            target.trust_ir_target_info().struct_passing,
            StructPassingPolicy::NativeC
        );
    }

    #[test]
    fn core_host_jit_target_is_send_sync_and_clone() {
        fn assert_send_sync_clone<T: Send + Sync + Clone>() {}
        assert_send_sync_clone::<CoreHostJitTarget>();
    }

    fn baseline_profile(architecture: Target) -> CoreHostJitMachineProfile {
        match architecture {
            Target::Aarch64 => CoreHostJitMachineProfile::AArch64(AArch64IsaProfile::BASELINE),
            Target::X86_64 => {
                CoreHostJitMachineProfile::X86_64(X86TargetFeatures::generic_x86_64())
            }
            Target::Riscv64 => CoreHostJitMachineProfile::AArch64(AArch64IsaProfile::BASELINE),
        }
    }

    #[test]
    fn core_host_target_matrix_derives_exact_triple_and_abi() {
        for (architecture, vendor, operating_system, environment, expected_triple, expected_abi) in [
            (
                Target::Aarch64,
                TargetVendor::Apple,
                TargetOperatingSystem::Darwin,
                TargetEnvironment::Unknown,
                "aarch64-apple-darwin",
                "darwinpcs",
            ),
            (
                Target::Aarch64,
                TargetVendor::Unknown,
                TargetOperatingSystem::Linux,
                TargetEnvironment::Gnu,
                "aarch64-unknown-linux-gnu",
                "aapcs64",
            ),
            (
                Target::X86_64,
                TargetVendor::Apple,
                TargetOperatingSystem::Darwin,
                TargetEnvironment::Unknown,
                "x86_64-apple-darwin",
                "sysv_amd64",
            ),
            (
                Target::X86_64,
                TargetVendor::Unknown,
                TargetOperatingSystem::Linux,
                TargetEnvironment::Gnu,
                "x86_64-unknown-linux-gnu",
                "sysv_amd64",
            ),
            (
                Target::X86_64,
                TargetVendor::Pc,
                TargetOperatingSystem::Windows,
                TargetEnvironment::Msvc,
                "x86_64-pc-windows-msvc",
                "windows_x64",
            ),
        ] {
            let target = CoreHostJitTarget::try_from_detected_facts(
                architecture,
                vendor,
                operating_system,
                environment,
                true,
                8,
                trust_ir::Endianness::Little,
                baseline_profile(architecture),
            )
            .unwrap();
            assert_eq!(target.target_spec().triple(), expected_triple);
            assert!(target.target_spec().has_explicit_os_abi());
            assert_eq!(
                TargetSpec::parse(expected_triple).unwrap(),
                target.target_spec(),
                "explicit-origin target must survive canonical parse round-trip"
            );
            assert_eq!(target.trust_ir_target_info().triple, expected_triple);
            assert_eq!(target.trust_ir_target_info().pointer_size, 8);
            assert_eq!(
                target.trust_ir_target_info().endianness,
                trust_ir::Endianness::Little
            );
            assert_eq!(
                target.trust_ir_target_info().abi.as_deref(),
                Some(expected_abi)
            );
        }
    }

    #[test]
    fn core_host_target_rejects_unsupported_matrix_and_layouts() {
        assert!(matches!(
            CoreHostJitTarget::try_from_detected_facts(
                Target::Aarch64,
                TargetVendor::Pc,
                TargetOperatingSystem::Windows,
                TargetEnvironment::Msvc,
                true,
                8,
                trust_ir::Endianness::Little,
                baseline_profile(Target::Aarch64),
            ),
            Err(
                CoreTargetContractError::HostJitArchitectureOperatingSystemUnsupported {
                    architecture: Target::Aarch64,
                    operating_system: TargetOperatingSystem::Windows,
                }
            )
        ));
        assert!(matches!(
            CoreHostJitTarget::try_from_detected_facts(
                Target::X86_64,
                TargetVendor::Unknown,
                TargetOperatingSystem::Unknown,
                TargetEnvironment::Unknown,
                true,
                8,
                trust_ir::Endianness::Little,
                baseline_profile(Target::X86_64),
            ),
            Err(CoreTargetContractError::HostJitOperatingSystemUnsupported {
                operating_system: TargetOperatingSystem::Unknown,
            })
        ));
        assert!(matches!(
            CoreHostJitTarget::try_from_detected_facts(
                Target::Riscv64,
                TargetVendor::Unknown,
                TargetOperatingSystem::Linux,
                TargetEnvironment::Gnu,
                true,
                8,
                trust_ir::Endianness::Little,
                baseline_profile(Target::Riscv64),
            ),
            Err(CoreTargetContractError::HostJitArchitectureUnsupported {
                target: Target::Riscv64,
            })
        ));
        assert!(matches!(
            CoreHostJitTarget::try_from_detected_facts(
                Target::Aarch64,
                TargetVendor::Unknown,
                TargetOperatingSystem::Linux,
                TargetEnvironment::Gnu,
                true,
                4,
                trust_ir::Endianness::Little,
                baseline_profile(Target::Aarch64),
            ),
            Err(CoreTargetContractError::HostJitPointerWidthMismatch {
                expected: 8,
                actual: 4,
            })
        ));
        assert!(matches!(
            CoreHostJitTarget::try_from_detected_facts(
                Target::X86_64,
                TargetVendor::Unknown,
                TargetOperatingSystem::Linux,
                TargetEnvironment::Gnu,
                true,
                8,
                trust_ir::Endianness::Big,
                baseline_profile(Target::X86_64),
            ),
            Err(CoreTargetContractError::HostJitEndiannessUnsupported {
                actual: trust_ir::Endianness::Big,
            })
        ));
        assert!(matches!(
            CoreHostJitTarget::try_from_detected_facts(
                Target::X86_64,
                TargetVendor::Apple,
                TargetOperatingSystem::Linux,
                TargetEnvironment::Gnu,
                true,
                8,
                trust_ir::Endianness::Little,
                baseline_profile(Target::X86_64),
            ),
            Err(CoreTargetContractError::HostJitVendorUnsupported {
                operating_system: TargetOperatingSystem::Linux,
                expected: TargetVendor::Unknown,
                actual: TargetVendor::Apple,
            })
        ));
        assert!(matches!(
            CoreHostJitTarget::try_from_detected_facts(
                Target::X86_64,
                TargetVendor::Unknown,
                TargetOperatingSystem::Linux,
                TargetEnvironment::Unknown,
                true,
                8,
                trust_ir::Endianness::Little,
                baseline_profile(Target::X86_64),
            ),
            Err(CoreTargetContractError::HostJitEnvironmentMismatch {
                operating_system: TargetOperatingSystem::Linux,
                expected: TargetEnvironment::Gnu,
                actual: TargetEnvironment::Unknown,
            })
        ));
        assert!(matches!(
            CoreHostJitTarget::try_from_detected_facts(
                Target::X86_64,
                TargetVendor::Unknown,
                TargetOperatingSystem::Linux,
                TargetEnvironment::Gnu,
                false,
                8,
                trust_ir::Endianness::Little,
                baseline_profile(Target::X86_64),
            ),
            Err(CoreTargetContractError::HostJitTargetAbiNotRepresentable)
        ));
    }

    #[test]
    fn admission_rejects_transient_unkeyed_compiler_controls_before_strict_translation() {
        let target = core_host_target();
        let error = crate::env_lock::with_env_overrides(
            &[("TCG_CORE_ADMISSION_FUTURE_UNKNOWN", "1")],
            || {
                admit_identity_core_module_for_host_jit(
                    self_contained_module(),
                    &target,
                    CoreDeclaredImportManifest::empty(),
                )
                .expect_err("admission under an unkeyed override must not retain strict LIR")
            },
        );
        assert!(matches!(
            error,
            CoreAdmissionError::UnkeyedAmbientCompilerControlsDuringAdmission { controls }
                if controls
                    .iter()
                    .any(|name| name == "TCG_CORE_ADMISSION_FUTURE_UNKNOWN")
        ));
    }

    #[test]
    fn recoverable_admission_returns_exact_module_and_manifest_allocations() {
        let target = core_host_target();
        let mut module = module_with_import();
        let manifest = import_manifest(&module);
        let module_name = module.name.as_ptr();
        let module_functions = module.functions.as_ptr();
        let manifest_imports = manifest.imports.as_ptr();

        module.target_info = None;
        let failure = try_admit_identity_core_module_for_host_jit(module, &target, manifest)
            .expect_err("a targetless module must fail recoverably");
        assert!(matches!(
            failure.reason(),
            CoreAdmissionError::Target(CoreTargetContractError::ModuleTargetMissing)
        ));
        assert_eq!(failure.module().name.as_ptr(), module_name);
        assert_eq!(failure.module().functions.as_ptr(), module_functions);
        assert_eq!(
            failure.declared_import_manifest().imports.as_ptr(),
            manifest_imports
        );

        let (error, recovered_module, recovered_manifest) = failure.into_parts();
        assert!(matches!(
            error,
            CoreAdmissionError::Target(CoreTargetContractError::ModuleTargetMissing)
        ));
        assert_eq!(recovered_module.name.as_ptr(), module_name);
        assert_eq!(recovered_module.functions.as_ptr(), module_functions);
        assert_eq!(recovered_manifest.imports.as_ptr(), manifest_imports);
    }

    pub(super) fn import_manifest(module: &Module) -> CoreDeclaredImportManifest {
        let function = &module.functions[0];
        let signature = module.func_types[function.ty.as_usize()].clone();
        let import = CoreHostFunctionImport::try_new(
            function.name.clone(),
            signature.clone(),
            function.calling_conv,
            normalized_parameter_attrs(&function.attrs, signature.params.len()),
            CoreHostFunctionEffects::deterministic(CoreHostMemoryEffect::None),
            "ty.runtime.inc.v1",
            runtime(),
        )
        .unwrap();
        CoreDeclaredImportManifest::try_new(vec![CoreHostImport::Function(import)]).unwrap()
    }

    #[test]
    fn target_contract_binds_all_target_info_fields() {
        let contract = target_contract();
        let mut module = module_with_import();
        assert!(contract.check_module(&module).is_ok());
        module.target_info.as_mut().unwrap().struct_passing = StructPassingPolicy::AlwaysMemory;
        assert!(matches!(
            contract.check_module(&module),
            Err(CoreTargetContractError::TrustIrStructPassingUnsupported {
                actual: StructPassingPolicy::AlwaysMemory,
            })
        ));
    }

    #[test]
    fn one_host_target_owner_binds_frontend_admission_and_receipt() {
        let target = core_host_target();
        let mut module = self_contained_module();
        module.target_info = Some(target.trust_ir_target_info().clone());

        let admitted = admit_identity_core_module_for_host_jit(
            module,
            &target,
            CoreDeclaredImportManifest::empty(),
        )
        .expect("the exact frontend-bound target owner must admit its module");
        assert_eq!(
            admitted.target_contract().target_spec(),
            target.target_spec()
        );
        assert_eq!(
            admitted.target_contract().target_info(),
            target.trust_ir_target_info()
        );
        assert_eq!(
            admitted.target_contract().host_jit_machine_profile(),
            target.machine_profile()
        );
    }

    #[test]
    fn equivalent_target_facts_match_independent_v2_digest_goldens() {
        let x86_profile = X86TargetFeatures::generic_x86_64()
            .with_feature(crate::x86_64::X86TargetFeature::Popcnt)
            .with_feature(crate::x86_64::X86TargetFeature::Sse41)
            .with_feature(crate::x86_64::X86TargetFeature::Avx2);
        let cases = [
            (
                Target::Aarch64,
                TargetVendor::Apple,
                TargetOperatingSystem::Darwin,
                TargetEnvironment::Unknown,
                CoreHostJitMachineProfile::AArch64(AArch64IsaProfile::BASELINE),
                [
                    133, 177, 99, 48, 8, 234, 57, 245, 51, 233, 119, 239, 48, 130, 120, 175, 16,
                    31, 38, 224, 62, 212, 120, 156, 129, 16, 132, 201, 44, 169, 139, 97,
                ],
            ),
            (
                Target::Aarch64,
                TargetVendor::Unknown,
                TargetOperatingSystem::Linux,
                TargetEnvironment::Gnu,
                CoreHostJitMachineProfile::AArch64(AArch64IsaProfile::BASELINE),
                [
                    171, 186, 253, 226, 9, 227, 107, 195, 85, 146, 127, 162, 51, 243, 84, 34, 186,
                    162, 84, 213, 69, 186, 97, 158, 147, 45, 114, 118, 96, 151, 160, 151,
                ],
            ),
            (
                Target::X86_64,
                TargetVendor::Apple,
                TargetOperatingSystem::Darwin,
                TargetEnvironment::Unknown,
                CoreHostJitMachineProfile::X86_64(x86_profile),
                [
                    172, 207, 108, 120, 182, 231, 136, 131, 139, 146, 205, 237, 120, 51, 2, 175,
                    216, 34, 21, 33, 153, 251, 62, 157, 138, 64, 239, 89, 118, 209, 114, 5,
                ],
            ),
            (
                Target::X86_64,
                TargetVendor::Unknown,
                TargetOperatingSystem::Linux,
                TargetEnvironment::Gnu,
                CoreHostJitMachineProfile::X86_64(x86_profile),
                [
                    90, 27, 16, 218, 110, 209, 202, 127, 68, 185, 47, 36, 129, 239, 47, 241, 110,
                    233, 54, 182, 48, 226, 66, 50, 32, 239, 32, 218, 220, 223, 230, 45,
                ],
            ),
            (
                Target::X86_64,
                TargetVendor::Pc,
                TargetOperatingSystem::Windows,
                TargetEnvironment::Msvc,
                CoreHostJitMachineProfile::X86_64(x86_profile),
                [
                    35, 144, 191, 196, 218, 210, 132, 214, 137, 178, 7, 0, 7, 242, 35, 103, 41,
                    211, 16, 102, 203, 178, 174, 215, 229, 171, 3, 180, 32, 194, 15, 200,
                ],
            ),
        ];
        let mut observed = Vec::new();

        for (architecture, vendor, operating_system, environment, profile, expected) in cases {
            let make_target = || {
                CoreHostJitTarget::try_from_detected_facts(
                    architecture,
                    vendor,
                    operating_system,
                    environment,
                    true,
                    8,
                    trust_ir::Endianness::Little,
                    profile,
                )
                .unwrap()
            };
            let first_target = make_target();
            let second_target = make_target();
            let triple = first_target.target_spec().triple();
            let module = self_contained_module_for_target(
                &first_target,
                format!("stable-v2-target-{triple}"),
            );
            let report = trust_ir_build::validate_module_report(&module);
            let strict =
                translate_validated_core_module_for_target(&report, first_target.target_spec())
                    .expect("fixture must strict-lower");
            let first =
                CoreTargetContract::try_from_strict_target(strict.target().clone(), &first_target)
                    .unwrap();
            let second =
                CoreTargetContract::try_from_strict_target(strict.target().clone(), &second_target)
                    .unwrap();
            let admitted = admit_identity_core_module_for_host_jit(
                self_contained_module_for_target(
                    &first_target,
                    format!("stable-v2-receipt-{triple}"),
                ),
                &first_target,
                CoreDeclaredImportManifest::empty(),
            )
            .unwrap();

            assert_eq!(first.digest(), second.digest());
            assert_eq!(admitted.receipt().target_contract_digest(), first.digest());
            assert_eq!(first.digest().algorithm, ProofDigestAlgorithm::Sha256);
            observed.push((triple, first.digest().bytes, expected));
        }

        for (triple, actual, expected) in &observed {
            assert_eq!(actual, expected, "{triple}");
        }
        let baseline_x86_linux = CoreHostJitTarget::try_from_detected_facts(
            Target::X86_64,
            TargetVendor::Unknown,
            TargetOperatingSystem::Linux,
            TargetEnvironment::Gnu,
            true,
            8,
            trust_ir::Endianness::Little,
            CoreHostJitMachineProfile::X86_64(X86TargetFeatures::generic_x86_64()),
        )
        .unwrap();
        let baseline_module = self_contained_module_for_target(
            &baseline_x86_linux,
            "stable-v2-x86-linux-baseline-profile",
        );
        let baseline_report = trust_ir_build::validate_module_report(&baseline_module);
        let baseline_strict = translate_validated_core_module_for_target(
            &baseline_report,
            baseline_x86_linux.target_spec(),
        )
        .unwrap();
        let baseline_contract = CoreTargetContract::try_from_strict_target(
            baseline_strict.target().clone(),
            &baseline_x86_linux,
        )
        .unwrap();
        assert_ne!(
            baseline_contract.digest().bytes,
            observed[3].1,
            "the same x86 Linux tuple with a different optional-ISA profile must not alias"
        );
        for left in 0..observed.len() {
            for right in (left + 1)..observed.len() {
                assert_ne!(
                    observed[left].1, observed[right].1,
                    "changing the target ABI or optional-ISA facts must change the digest"
                );
            }
        }
    }

    #[test]
    fn one_detected_target_owner_admits_a_batch_without_reprobe() {
        let Ok(target) = CoreHostJitTarget::detect() else {
            // Same cross-check in the failure arm: detection must only fail off the
            // cfg-supported host domain; constant to clippy, meaningful at run time.
            #[allow(clippy::assertions_on_constants)]
            {
                assert!(!EXACT_CORE_HOST_SUPPORTED);
            }
            return;
        };
        // Constant only in clippy's view: this pairs a runtime `detect()` outcome with the
        // cfg-derived support domain, so it must stay a runtime check, not a const block.
        #[allow(clippy::assertions_on_constants)]
        {
            assert!(EXACT_CORE_HOST_SUPPORTED);
        }
        let first = admit_identity_core_module_for_host_jit(
            self_contained_module_for_target(&target, "batch-first"),
            &target,
            CoreDeclaredImportManifest::empty(),
        )
        .unwrap();
        let second = admit_identity_core_module_for_host_jit(
            self_contained_module_for_target(&target, "batch-second"),
            &target,
            CoreDeclaredImportManifest::empty(),
        )
        .unwrap();

        assert_eq!(
            first.receipt().target_contract_digest(),
            first.target_contract().digest()
        );
        assert_eq!(
            second.receipt().target_contract_digest(),
            second.target_contract().digest()
        );
        assert_eq!(
            first.receipt().target_contract_digest(),
            second.receipt().target_contract_digest()
        );
        assert_eq!(
            first.target_contract().host_jit_machine_profile(),
            target.machine_profile()
        );
        assert_eq!(
            second.target_contract().host_jit_machine_profile(),
            target.machine_profile()
        );
    }

    #[test]
    fn declared_manifest_checks_exact_typed_import_closure() {
        let module = module_with_import();
        let manifest = import_manifest(&module);
        assert!(manifest.check_module(&module).is_ok());

        let mut wrong = manifest.clone();
        let CoreHostImport::Function(import) = &mut wrong.imports[0] else {
            unreachable!()
        };
        import.signature.returns[0] = Ty::I32;
        assert!(matches!(
            wrong.check_module(&module),
            Err(CoreModuleClosureError::FunctionContractMismatch { .. })
        ));
        assert!(matches!(
            CoreDeclaredImportManifest::empty().check_module(&module),
            Err(CoreModuleClosureError::MissingFunction { .. })
        ));
    }

    #[test]
    fn native_runtime_catalog_is_deterministic_typed_and_catalog_scoped() {
        let module = module_with_import();
        let manifest = import_manifest(&module);
        let first = CoreNativeRuntimeCatalog::try_from_declared_import_manifest(&manifest).unwrap();
        let second =
            CoreNativeRuntimeCatalog::try_from_declared_import_manifest(&manifest.clone()).unwrap();

        assert_eq!(first, second);
        assert_eq!(
            first.schema_version(),
            CORE_NATIVE_RUNTIME_CATALOG_SCHEMA_VERSION
        );
        assert_eq!(
            first.coverage(),
            CoreNativeRuntimeCatalogCoverage::DeclaredImportsOnly
        );
        assert_eq!(first.declared_import_manifest_digest(), manifest.digest());
        assert_eq!(first.entries().len(), 1);
        let id = NativeDependencyId::new(0);
        let entry = first
            .get(id)
            .expect("canonical first import must have ID zero");
        assert_eq!(entry.id(), id);
        assert_eq!(
            entry.origin(),
            CoreNativeDependencyOrigin::DeclaredTrustIrImport
        );
        assert_eq!(entry.symbol(), "runtime_inc");
        assert!(first.get(NativeDependencyId::new(1)).is_none());
        assert!(!first.digest().is_zero());
        assert!(first.is_intact());

        // A content-consistent catalog still cannot broaden the provenance
        // admitted by DeclaredImportsOnly. The test-only variant stands in for
        // any future origin added to the public non-exhaustive enum.
        let mut wrong_origin = first.clone();
        wrong_origin.entries[0].origin = CoreNativeDependencyOrigin::TestOnlyNonDeclared;
        wrong_origin.digest = wrong_origin.compute_digest().unwrap();
        assert!(
            !wrong_origin.is_intact(),
            "a non-declared origin must fail even when its cached digest is self-consistent"
        );

        let function = &module.functions[0];
        let signature = module.func_types[function.ty.as_usize()].clone();
        let changed_import = CoreHostFunctionImport::try_new(
            function.name.clone(),
            signature.clone(),
            function.calling_conv,
            normalized_parameter_attrs(&function.attrs, signature.params.len()),
            CoreHostFunctionEffects::deterministic(CoreHostMemoryEffect::None),
            "ty.runtime.inc.v2",
            runtime(),
        )
        .unwrap();
        let changed_manifest =
            CoreDeclaredImportManifest::try_new(vec![CoreHostImport::Function(changed_import)])
                .unwrap();
        let changed =
            CoreNativeRuntimeCatalog::try_from_declared_import_manifest(&changed_manifest).unwrap();
        assert_ne!(first.digest(), changed.digest());

        let make_import = |symbol: &str, provider: &str, image: &[u8]| {
            CoreHostImport::Function(
                CoreHostFunctionImport::try_new(
                    symbol,
                    signature.clone(),
                    function.calling_conv,
                    normalized_parameter_attrs(&function.attrs, signature.params.len()),
                    CoreHostFunctionEffects::deterministic(CoreHostMemoryEffect::None),
                    "ty.runtime.inc.v1",
                    CoreRuntimeIdentity::try_new(
                        provider,
                        ProofDigest::sha256_domain("test.runtime.variant", image),
                    )
                    .unwrap(),
                )
                .unwrap(),
            )
        };
        let reverse_manifest = CoreDeclaredImportManifest::try_new(vec![
            make_import("z_runtime", "provider-z", b"image-z"),
            make_import("a_runtime", "provider-a", b"image-a"),
        ])
        .unwrap();
        let ordered =
            CoreNativeRuntimeCatalog::try_from_declared_import_manifest(&reverse_manifest).unwrap();
        assert_eq!(ordered.entries()[0].id(), NativeDependencyId::new(0));
        assert_eq!(ordered.entries()[0].symbol(), "a_runtime");
        assert_eq!(ordered.entries()[1].id(), NativeDependencyId::new(1));
        assert_eq!(ordered.entries()[1].symbol(), "z_runtime");

        let provider_changed = CoreDeclaredImportManifest::try_new(vec![make_import(
            "runtime_inc",
            "different-provider",
            b"exact runtime bytes",
        )])
        .unwrap();
        let image_changed = CoreDeclaredImportManifest::try_new(vec![make_import(
            "runtime_inc",
            "ty-runtime-v1",
            b"different runtime bytes",
        )])
        .unwrap();
        assert_ne!(
            first.digest(),
            CoreNativeRuntimeCatalog::try_from_declared_import_manifest(&provider_changed)
                .unwrap()
                .digest()
        );
        assert_ne!(
            first.digest(),
            CoreNativeRuntimeCatalog::try_from_declared_import_manifest(&image_changed)
                .unwrap()
                .digest()
        );
    }

    #[test]
    fn native_dependency_reference_map_binds_module_and_catalog_namespaces() {
        let mut module = module_with_import();
        let signature_id = module.functions[0].ty;
        let mut alphabetically_first_import = Function::new(
            FuncId::new(7),
            "a_runtime",
            signature_id,
            trust_ir::BlockId::new(0),
        );
        alphabetically_first_import.attrs.readnone = true;
        alphabetically_first_import.linkage = Linkage::External;
        module
            .try_add_function(alphabetically_first_import)
            .expect("Module::try_add_function: test fixture");

        let original_manifest = import_manifest(&module);
        let function = &module.functions[2];
        let signature = module.func_types[function.ty.as_usize()].clone();
        let additional_import = CoreHostFunctionImport::try_new(
            function.name.clone(),
            signature,
            function.calling_conv,
            normalized_parameter_attrs(&function.attrs, 1),
            CoreHostFunctionEffects::deterministic(CoreHostMemoryEffect::None),
            "ty.runtime.a.v1",
            runtime(),
        )
        .unwrap();
        let manifest = CoreDeclaredImportManifest::try_new(vec![
            original_manifest.imports()[0].clone(),
            CoreHostImport::Function(additional_import),
        ])
        .unwrap();
        let (_, surface, seed) = capture_module_inventory(&module, &manifest).unwrap();
        let catalog =
            CoreNativeRuntimeCatalog::try_from_declared_import_manifest(&manifest).unwrap();
        let receipt_digest =
            ProofDigest::sha256_domain("test.identity-receipt", b"retained strict lowering");
        let map = CoreNativeDependencyReferenceMap::try_from_admitted_seed(
            module.stable_digest(),
            receipt_digest,
            &manifest,
            &catalog,
            &seed,
        )
        .unwrap();

        assert_eq!(
            surface.imported_functions(),
            &[FuncId::new(0), FuncId::new(7)]
        );
        assert_eq!(catalog.entries()[0].symbol(), "a_runtime");
        assert_eq!(catalog.entries()[1].symbol(), "runtime_inc");
        assert_eq!(map.entries().len(), 2);
        assert_eq!(map.entries()[0].function(), FuncId::new(0));
        assert_eq!(map.entries()[0].dependency(), NativeDependencyId::new(1));
        assert_eq!(map.entries()[1].function(), FuncId::new(7));
        assert_eq!(map.entries()[1].dependency(), NativeDependencyId::new(0));
        assert_eq!(map.core_module_digest(), module.stable_digest());
        assert_eq!(map.identity_transform_receipt_digest(), receipt_digest);
        assert_eq!(map.native_runtime_catalog_digest(), catalog.digest());
        assert!(map.is_intact());

        let different_module_map = CoreNativeDependencyReferenceMap::try_from_admitted_seed(
            ProofDigest::sha256_domain("test.other-core-module", b"different module"),
            receipt_digest,
            &manifest,
            &catalog,
            &seed,
        )
        .unwrap();
        assert_ne!(map.digest(), different_module_map.digest());

        let different_receipt_map = CoreNativeDependencyReferenceMap::try_from_admitted_seed(
            module.stable_digest(),
            ProofDigest::sha256_domain("test.other-identity-receipt", b"other lowering seal"),
            &manifest,
            &catalog,
            &seed,
        )
        .unwrap();
        assert_ne!(map.digest(), different_receipt_map.digest());

        let mut foreign_catalog = catalog;
        foreign_catalog.declared_import_manifest_digest =
            ProofDigest::sha256_domain("test.other-import-manifest", b"different manifest");
        assert!(matches!(
            CoreNativeDependencyReferenceMap::try_from_admitted_seed(
                module.stable_digest(),
                receipt_digest,
                &manifest,
                &foreign_catalog,
                &seed,
            ),
            Err(CoreNativeDependencyReferenceMapError::CatalogManifestDigestMismatch)
        ));
    }

    #[test]
    fn admission_rejects_unwind_capable_function_imports() {
        let module = module_with_import();
        let function = &module.functions[0];
        let signature = module.func_types[function.ty.as_usize()].clone();
        let mut effects = CoreHostFunctionEffects::deterministic(CoreHostMemoryEffect::None);
        effects.may_unwind = true;
        let import = CoreHostFunctionImport::try_new(
            function.name.clone(),
            signature.clone(),
            function.calling_conv,
            normalized_parameter_attrs(&function.attrs, signature.params.len()),
            effects,
            "ty.runtime.inc.v1",
            runtime(),
        )
        .unwrap();
        let manifest =
            CoreDeclaredImportManifest::try_new(vec![CoreHostImport::Function(import)]).unwrap();

        assert!(matches!(
            admit_identity_core_module_for_host_jit(module, &core_host_target(), manifest),
            Err(CoreAdmissionError::ModuleClosure(
                CoreModuleClosureError::UnwindCapableFunctionImportUnsupported { symbol }
            )) if symbol == "runtime_inc"
        ));
    }

    #[test]
    fn admission_rejects_indirect_calls_without_typed_capability_closure() {
        let target = core_host_target();
        let mut module = Module::new("indirect-core-fixture");
        module.target_info = Some(target.trust_ir_target_info().clone());
        let callee_ty = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let entry_ty = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut entry = Function::new(FuncId::new(0), "entry", entry_ty, trust_ir::BlockId::new(0));
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block.params.push((ValueId::new(0), Ty::Ptr));
        block.body.push(InstrNode::new(Inst::CallIndirect {
            callee: ValueId::new(0),
            sig: callee_ty,
            args: vec![],
            calling_conv: CallingConv::C,
        }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        entry.blocks.push(block);
        module
            .try_add_function(entry)
            .expect("Module::try_add_function: test fixture");

        assert!(matches!(
            admit_identity_core_module_for_host_jit(
                module,
                &target,
                CoreDeclaredImportManifest::empty(),
            ),
            Err(CoreAdmissionError::ModuleClosure(
                CoreModuleClosureError::IndirectCallUnsupported { function }
            )) if function == "entry"
        ));
    }

    /// trust-ir v54 (amendment P): the Core surface census refuses a sited
    /// check and `AssertInvoke` by name, rather than count either as a plain
    /// check and lose its panic-entry and location edges.
    #[test]
    fn admission_rejects_v54_panic_sites_by_name() {
        let target = core_host_target();
        let site = trust_ir::PanicSite {
            entry: FuncId::new(1),
            location: trust_ir::PanicLocation::Value(ValueId::new(0)),
        };
        let module_with = |blocks: Vec<Block>| {
            let mut module = Module::new("panic-site-core-fixture");
            module.target_info = Some(target.trust_ir_target_info().clone());
            let entry_ty = module
                .add_func_type(FuncTy {
                    params: vec![Ty::Ptr, Ty::I64],
                    returns: vec![],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let panic_ty = module
                .add_func_type(FuncTy {
                    params: vec![Ty::Ptr],
                    returns: vec![],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut entry =
                Function::new(FuncId::new(0), "entry", entry_ty, trust_ir::BlockId::new(0));
            entry.blocks = blocks;
            module
                .try_add_function(entry)
                .expect("Module::try_add_function: test fixture");
            let mut panic_entry = Function::new(
                FuncId::new(1),
                "panic_const_div_by_zero",
                panic_ty,
                trust_ir::BlockId::new(0),
            );
            let mut block = Block::new(trust_ir::BlockId::new(0));
            block.params.push((ValueId::new(0), Ty::Ptr));
            block.body.push(InstrNode::new(Inst::Unreachable));
            panic_entry.blocks.push(block);
            module
                .try_add_function(panic_entry)
                .expect("Module::try_add_function: test fixture");
            module
        };
        let head = |terminal: Inst| {
            let mut block = Block::new(trust_ir::BlockId::new(0));
            block.params.push((ValueId::new(0), Ty::Ptr));
            block.params.push((ValueId::new(1), Ty::I64));
            block.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::Bool,
                    value: trust_ir::Constant::Bool(true),
                })
                .with_result(ValueId::new(2)),
            );
            block.body.push(InstrNode::new(terminal));
            block
        };
        let mut sited = head(Inst::Assert {
            cond: ValueId::new(2),
            kind: trust_ir::AssertKind::DivByZero,
            site: Some(site),
        });
        sited
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        let invoke = head(Inst::AssertInvoke {
            cond: ValueId::new(2),
            kind: trust_ir::AssertKind::DivByZero,
            site,
            normal_dest: trust_ir::BlockId::new(1),
            normal_args: vec![],
            unwind_dest: trust_ir::BlockId::new(2),
        });
        let mut normal = Block::new(trust_ir::BlockId::new(1));
        normal
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        let mut pad = Block::new(trust_ir::BlockId::new(2));
        pad.body.push(
            InstrNode::new(Inst::LandingPad {
                is_cleanup: true,
                catch_type_indices: vec![],
            })
            .with_results([ValueId::new(3), ValueId::new(4)]),
        );
        pad.body.push(InstrNode::new(Inst::Resume {
            exn: ValueId::new(3),
        }));
        for (blocks, expected) in [
            (vec![sited], "Inst::Assert { site: Some(_) }"),
            (vec![invoke, normal, pad], "Inst::AssertInvoke"),
        ] {
            let outcome = admit_identity_core_module_for_host_jit(
                module_with(blocks),
                &target,
                CoreDeclaredImportManifest::empty(),
            );
            assert!(
                matches!(
                    &outcome,
                    Err(CoreAdmissionError::ModuleClosure(
                        CoreModuleClosureError::UnmodeledInstruction { function, instruction }
                    )) if function == "entry" && *instruction == expected
                ),
                "{expected}: {:?}",
                outcome.err()
            );
        }
    }

    /// trust-ir v55: a struct `struct.0` (not trivially droppable), so a drop
    /// of it is the one spelling of a drop (an UNRESOLVED one: there is no
    /// drop-glue row, which trust-ir's structural validator accepts).
    fn add_owner_struct(module: &mut Module) {
        module.add_struct(trust_ir::StructDef {
            origin: None,
            id: trust_ir::StructId::new(0),
            name: "Owner".to_string(),
            fields: vec![trust_ir::FieldDef {
                name: "handle".to_string(),
                ty: Ty::I64,
                offset: None,
            }],
            size: None,
            align: None,
            repr: trust_ir::StructRepr::default(),
        });
    }

    /// trust-ir v55 / v56 (amendment D): the Core surface census refuses the
    /// unwinding twins of a drop and of an indirect call by name; its trailing
    /// wildcard would otherwise count either as no effect.
    #[test]
    fn admission_rejects_v55_v56_unwinding_twins_by_name() {
        let target = core_host_target();
        let module_with = |terminal: Inst| {
            let mut module = Module::new("unwinding-twin-core-fixture");
            module.target_info = Some(target.trust_ir_target_info().clone());
            add_owner_struct(&mut module);
            let entry_ty = module
                .add_func_type(FuncTy {
                    params: vec![Ty::Ptr],
                    returns: vec![],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut entry =
                Function::new(FuncId::new(0), "entry", entry_ty, trust_ir::BlockId::new(0));
            let mut head = Block::new(trust_ir::BlockId::new(0));
            head.params.push((ValueId::new(0), Ty::Ptr));
            head.body.push(InstrNode::new(terminal));
            let mut normal = Block::new(trust_ir::BlockId::new(1));
            normal
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            let mut pad = Block::new(trust_ir::BlockId::new(2));
            pad.body.push(
                InstrNode::new(Inst::LandingPad {
                    is_cleanup: true,
                    catch_type_indices: vec![],
                })
                .with_results([ValueId::new(1), ValueId::new(2)]),
            );
            pad.body.push(InstrNode::new(Inst::Resume {
                exn: ValueId::new(1),
            }));
            entry.blocks = vec![head, normal, pad];
            module
                .try_add_function(entry)
                .expect("Module::try_add_function: test fixture");
            module
        };
        for (terminal, expected) in [
            (
                Inst::DropInvoke {
                    ty: Ty::Struct(trust_ir::StructId::new(0)),
                    ptr: ValueId::new(0),
                    normal_dest: trust_ir::BlockId::new(1),
                    normal_args: vec![],
                    unwind_dest: trust_ir::BlockId::new(2),
                },
                "Inst::DropInvoke",
            ),
            (
                Inst::InvokeIndirect {
                    callee: ValueId::new(0),
                    sig: trust_ir::FuncTyId::new(0),
                    args: vec![ValueId::new(0)],
                    calling_conv: trust_ir::CallingConv::default(),
                    normal_dest: trust_ir::BlockId::new(1),
                    normal_args: vec![],
                    unwind_dest: trust_ir::BlockId::new(2),
                },
                "Inst::InvokeIndirect",
            ),
        ] {
            let outcome = admit_identity_core_module_for_host_jit(
                module_with(terminal),
                &target,
                CoreDeclaredImportManifest::empty(),
            );
            assert!(
                matches!(
                    &outcome,
                    Err(CoreAdmissionError::ModuleClosure(
                        CoreModuleClosureError::UnmodeledInstruction { function, instruction }
                    )) if function == "entry" && *instruction == expected
                ),
                "{expected}: {:?}",
                outcome.err()
            );
        }
    }

    /// trust-ir v47/v48: the Core surface census refuses a drop and a WEAK
    /// compare-exchange by name, rather than count the drop as no effect or
    /// the weak CAS as the strong one; the strong CAS stays admissible there.
    #[test]
    fn admission_rejects_drop_and_weak_cmpxchg_by_name() {
        let target = core_host_target();
        let cmpxchg = |weak| Inst::CmpXchg {
            ty: Ty::I64,
            ptr: ValueId::new(0),
            expected: ValueId::new(1),
            desired: ValueId::new(1),
            success: trust_ir::Ordering::SeqCst,
            failure: trust_ir::Ordering::SeqCst,
            weak,
        };
        let module_with = |inst: Inst, results: u32| {
            let mut module = Module::new("unmodeled-core-fixture");
            module.target_info = Some(target.trust_ir_target_info().clone());
            add_owner_struct(&mut module);
            let entry_ty = module
                .add_func_type(FuncTy {
                    params: vec![Ty::Ptr, Ty::I64],
                    returns: vec![],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut entry =
                Function::new(FuncId::new(0), "entry", entry_ty, trust_ir::BlockId::new(0));
            let mut block = Block::new(trust_ir::BlockId::new(0));
            block.params.push((ValueId::new(0), Ty::Ptr));
            block.params.push((ValueId::new(1), Ty::I64));
            block
                .body
                .push(InstrNode::new(inst).with_results((0..results).map(|i| ValueId::new(2 + i))));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            entry.blocks.push(block);
            module
                .try_add_function(entry)
                .expect("Module::try_add_function: test fixture");
            module
        };
        // Since trust-ir v55 a drop of the trivially droppable `i64` is not
        // the one spelling of a drop (trust-ir's validator refuses it before
        // the census): drop the struct, as a producer would.
        let drop = Inst::Drop {
            ty: Ty::Struct(trust_ir::StructId::new(0)),
            ptr: ValueId::new(0),
        };
        // v53: a non-propagating call boundary (the entry calling itself
        // with its own parameters, so the module validates).
        let boundary = Inst::CallCannotUnwind {
            callee: FuncId::new(0),
            args: vec![ValueId::new(0), ValueId::new(1)],
        };
        for (inst, results, expected) in [
            (drop, 0, "Inst::Drop"),
            (cmpxchg(true), 2, "Inst::CmpXchg { weak: true }"),
            (boundary, 0, "Inst::CallCannotUnwind"),
        ] {
            let outcome = admit_identity_core_module_for_host_jit(
                module_with(inst, results),
                &target,
                CoreDeclaredImportManifest::empty(),
            );
            assert!(
                matches!(
                    &outcome,
                    Err(CoreAdmissionError::ModuleClosure(
                        CoreModuleClosureError::UnmodeledInstruction { function, instruction }
                    )) if function == "entry" && *instruction == expected
                ),
                "{expected}: {:?}",
                outcome.err()
            );
        }
        // The strong CAS is not refused by the census: whatever later stage
        // decides it, it is never this refusal.
        let strong = admit_identity_core_module_for_host_jit(
            module_with(cmpxchg(false), 2),
            &target,
            CoreDeclaredImportManifest::empty(),
        );
        assert!(
            !matches!(
                &strong,
                Err(CoreAdmissionError::ModuleClosure(
                    CoreModuleClosureError::UnmodeledInstruction { .. }
                ))
            ),
            "strong CmpXchg: {:?}",
            strong.err()
        );
    }

    fn call_boundary_fixture(indirect: bool, result: bool, nonexecuted: bool) -> Module {
        let target = core_host_target();
        let mut module = Module::new("core-call-boundary-fixture");
        module.target_info = Some(target.trust_ir_target_info().clone());
        let returns = if result { vec![Ty::I64] } else { vec![] };
        let callee_ty = module
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: returns.clone(),
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let caller_ty = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::I64],
                returns,
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut callee = Function::new(
            FuncId::new(0),
            "callee",
            callee_ty,
            trust_ir::BlockId::new(0),
        );
        callee.linkage = Linkage::Internal;
        let mut callee_block = Block::new(trust_ir::BlockId::new(0));
        callee_block.params.push((ValueId::new(0), Ty::I64));
        callee_block.body.push(InstrNode::new(Inst::Return {
            values: if result {
                vec![ValueId::new(0)]
            } else {
                vec![]
            },
        }));
        callee.blocks.push(callee_block);
        let mut caller = Function::new(
            FuncId::new(1),
            "caller",
            caller_ty,
            trust_ir::BlockId::new(0),
        );
        caller.linkage = Linkage::Internal;
        let mut entry = Block::new(trust_ir::BlockId::new(0));
        entry.params = vec![(ValueId::new(0), Ty::Ptr), (ValueId::new(1), Ty::I64)];
        let (mut call_block, pointer, argument, destination) = if nonexecuted {
            entry.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::Bool,
                    value: trust_ir::Constant::Bool(false),
                })
                .with_result(ValueId::new(6)),
            );
            entry.body.push(InstrNode::new(Inst::CondBr {
                cond: ValueId::new(6),
                then_target: trust_ir::BlockId::new(1),
                then_args: vec![ValueId::new(0), ValueId::new(1)],
                else_target: trust_ir::BlockId::new(2),
                else_args: vec![],
            }));
            let mut untaken = Block::new(trust_ir::BlockId::new(1));
            untaken.params = vec![(ValueId::new(3), Ty::Ptr), (ValueId::new(4), Ty::I64)];
            (untaken, ValueId::new(3), ValueId::new(4), ValueId::new(5))
        } else {
            (
                entry.clone(),
                ValueId::new(0),
                ValueId::new(1),
                ValueId::new(2),
            )
        };
        let call = if indirect {
            Inst::CallIndirectCannotUnwind {
                callee: pointer,
                sig: callee_ty,
                args: vec![argument],
                calling_conv: CallingConv::C,
            }
        } else {
            Inst::CallCannotUnwind {
                callee: callee.id,
                args: vec![argument],
            }
        };
        let mut node = InstrNode::new(call);
        if result {
            node.results.push(destination);
        }
        call_block.body.push(node);
        call_block.body.push(InstrNode::new(Inst::Return {
            values: if result { vec![destination] } else { vec![] },
        }));
        if nonexecuted {
            caller.blocks.push(entry);
        }
        caller.blocks.push(call_block);
        if nonexecuted {
            let mut exit = Block::new(trust_ir::BlockId::new(2));
            exit.body.push(InstrNode::new(Inst::Return {
                values: if result {
                    vec![ValueId::new(1)]
                } else {
                    vec![]
                },
            }));
            caller.blocks.push(exit);
        }
        module.functions = vec![callee, caller];
        let errors = trust_ir_build::validate_module(&module);
        assert!(
            errors.is_empty(),
            "boundary fixture must be valid IR: {errors:#?}"
        );
        assert!(!module.instructions().any(|node| matches!(
            node.inst,
            Inst::Invoke { .. } | Inst::LandingPad { .. } | Inst::Resume { .. }
        )));
        module
    }

    #[test]
    fn call_boundary_owned_and_shared_admission_refuse_every_stored_shape() {
        let target = core_host_target();
        for indirect in [false, true] {
            let kind = if indirect {
                "Inst::CallIndirectCannotUnwind"
            } else {
                "Inst::CallCannotUnwind"
            };
            for result in [false, true] {
                for nonexecuted in [false, true] {
                    let module = call_boundary_fixture(indirect, result, nonexecuted);
                    let digest = module.stable_digest();
                    let failure = try_admit_identity_core_module_for_host_jit(
                        module,
                        &target,
                        CoreDeclaredImportManifest::empty(),
                    )
                    .expect_err("unsupported boundary must be refused before lowering");
                    assert!(
                        matches!(&failure.error,
                            CoreAdmissionError::ModuleClosure(CoreModuleClosureError::UnmodeledInstruction { function, instruction })
                            if function == "caller" && *instruction == kind
                        ),
                        "{kind}, result={result}, nonexecuted={nonexecuted}: {}",
                        failure.error
                    );
                    assert_eq!(failure.module.stable_digest(), digest);

                    let shared = Arc::new(call_boundary_fixture(indirect, result, nonexecuted));
                    let failure = try_admit_shared_identity_core_module_for_host_jit(
                        Arc::clone(&shared),
                        &target,
                        CoreDeclaredImportManifest::empty(),
                    )
                    .expect_err("shared custody is not boundary enforcement authority");
                    assert!(Arc::ptr_eq(&shared, &failure.module));
                    assert!(
                        matches!(&failure.error,
                            CoreAdmissionError::ModuleClosure(CoreModuleClosureError::UnmodeledInstruction { function, instruction })
                            if function == "caller" && *instruction == kind
                        ),
                        "shared {kind}: {}",
                        failure.error
                    );
                }
            }
        }
    }

    #[test]
    fn call_boundary_source_replay_refuses_erasure_including_nonexecuted_sites() {
        for indirect in [false, true] {
            let expected_kind = if indirect {
                "Inst::CallIndirectCannotUnwind"
            } else {
                "Inst::CallCannotUnwind"
            };
            for result in [false, true] {
                for nonexecuted in [false, true] {
                    let module = call_boundary_fixture(indirect, result, nonexecuted);
                    assert!(matches!(retained_source_direct_calls(&module.functions[1]),
                        Err(CoreJitPlanIntegrityError::UnsupportedSourceCallUnwindBoundary { caller: 1, instruction, kind })
                        if kind == expected_kind && instruction == 2 * u32::from(nonexecuted)
                    ));
                }
            }
        }
        let ordinary = module_with_exact_call();
        assert_eq!(
            retained_source_direct_calls(&ordinary.functions[1]).unwrap(),
            vec![(trust_cg_ir::TrustIrInstId(0), FuncId::new(0))]
        );
        let (parts, catalog, references, bindings) = planned_exact_call_fixture();
        parts
            .check_planned_integrity(&catalog, &references, &bindings)
            .expect("ordinary call retains its actual valid source/LIR join");
    }

    #[test]
    fn call_boundary_disconnected_source_is_malformed_and_replay_does_not_erase_it() {
        let target = core_host_target();
        for indirect in [false, true] {
            for result in [false, true] {
                let mut module = call_boundary_fixture(indirect, result, true);
                let caller = &mut module.functions[1];
                caller.blocks[0].body = vec![InstrNode::new(Inst::Return {
                    values: if result {
                        vec![ValueId::new(1)]
                    } else {
                        vec![]
                    },
                })];
                caller
                    .blocks
                    .retain(|block| block.id != trust_ir::BlockId::new(2));
                let errors = trust_ir_build::validate_module(&module);
                assert_eq!(
                    errors,
                    vec![trust_ir_build::ValidationError::UnreachableBlock(1)]
                );
                // The standalone census/replay backstops inspect the actual
                // stored body. This deliberately malformed source acquires no
                // validation report, receipt, or admitted compilation owner.
                assert!(
                    matches!(capture_module_inventory(&module, &CoreDeclaredImportManifest::empty()),
                        Err(CoreModuleClosureError::UnmodeledInstruction { instruction, .. })
                        if instruction == if indirect {
                            "Inst::CallIndirectCannotUnwind"
                        } else {
                            "Inst::CallCannotUnwind"
                        }
                    )
                );
                assert!(matches!(
                    retained_source_direct_calls(&module.functions[1]),
                    Err(
                        CoreJitPlanIntegrityError::UnsupportedSourceCallUnwindBoundary {
                            instruction: 1,
                            ..
                        }
                    )
                ));
                let owned = try_admit_identity_core_module_for_host_jit(
                    module.clone(),
                    &target,
                    CoreDeclaredImportManifest::empty(),
                )
                .expect_err("disconnected IR is not admissible");
                assert!(
                    matches!(&owned.error, CoreAdmissionError::TrustIrValidation { errors }
                    if errors.contains(&trust_ir_build::ValidationError::UnreachableBlock(1)))
                );
                let shared = Arc::new(module);
                let failure = try_admit_shared_identity_core_module_for_host_jit(
                    Arc::clone(&shared),
                    &target,
                    CoreDeclaredImportManifest::empty(),
                )
                .expect_err("shared ownership does not waive CFG validation");
                assert!(Arc::ptr_eq(&shared, &failure.module));
                assert!(
                    matches!(&failure.error, CoreAdmissionError::TrustIrValidation { errors }
                    if errors.contains(&trust_ir_build::ValidationError::UnreachableBlock(1)))
                );
            }
        }
    }

    #[test]
    fn declared_manifest_digest_is_canonical_and_runtime_bound() {
        let module = module_with_import();
        let first = import_manifest(&module);
        let second = import_manifest(&module);
        assert_eq!(first.digest(), second.digest());

        let function = &module.functions[0];
        let signature = module.func_types[function.ty.as_usize()].clone();
        let changed_runtime = CoreRuntimeIdentity::try_new(
            "ty-runtime-v1",
            ProofDigest::sha256_domain("test.runtime", b"different runtime bytes"),
        )
        .unwrap();
        let changed = CoreHostFunctionImport::try_new(
            function.name.clone(),
            signature.clone(),
            function.calling_conv,
            normalized_parameter_attrs(&function.attrs, signature.params.len()),
            CoreHostFunctionEffects::deterministic(CoreHostMemoryEffect::None),
            "ty.runtime.inc.v1",
            changed_runtime,
        )
        .unwrap();
        let changed =
            CoreDeclaredImportManifest::try_new(vec![CoreHostImport::Function(changed)]).unwrap();
        assert_ne!(first.digest(), changed.digest());
    }

    mod runtime_closure_fixture {
        include!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../trust-cg-lower/tests/common/runtime_closure.rs"
        ));
    }

    #[test]
    fn runtime_closure_census_refuses_the_unused_constructor_by_name() {
        let module = runtime_closure_fixture::runtime_closure_module(true);
        assert!(trust_ir_build::validate_module(&module).is_empty());
        let error =
            capture_module_inventory(&module, &CoreDeclaredImportManifest::empty()).unwrap_err();
        assert!(
            matches!(error, CoreModuleClosureError::UnmodeledInstruction {
            function, instruction: "Inst::MakeClosure"
        } if function == "host")
        );
        let scalar = runtime_closure_fixture::runtime_closure_module(false);
        capture_module_inventory(&scalar, &CoreDeclaredImportManifest::empty()).unwrap();
    }

    #[test]
    fn census_and_surface_are_exact_module_summaries() {
        let module = module_with_import();
        let (arena, surface, _) =
            capture_module_inventory(&module, &import_manifest(&module)).unwrap();
        assert_eq!(arena.functions, 2);
        assert_eq!(arena.blocks, 1);
        assert_eq!(arena.instructions, 2);
        assert_eq!(surface.defined_functions(), &[FuncId::new(1)]);
        assert_eq!(surface.imported_functions(), &[FuncId::new(0)]);
        assert_eq!(surface.direct_calls(), 1);
        assert_eq!(surface.indirect_calls(), 0);
    }

    /// trust-ir v50 `ArraySplat` is pure value construction: the census
    /// counts the instruction and records no memory effect or allocation for
    /// it, the same for two lanes as for 2^40.
    #[test]
    fn array_splat_census_is_pure_whatever_its_lane_count() {
        for lanes in [2u64, 1 << 40] {
            let mut module = module_with_import();
            let elem = module
                .add_type(Ty::I64)
                .expect("Module::add_type: test fixture");
            module.functions[1].blocks[0].body.insert(
                0,
                InstrNode::new(Inst::ArraySplat {
                    ty: Ty::Array(elem, lanes),
                    value: ValueId::new(0),
                })
                .with_result(ValueId::new(10)),
            );
            let (arena, surface, _) =
                capture_module_inventory(&module, &import_manifest(&module)).unwrap();
            assert_eq!(arena.instructions, 3, "{lanes} lanes");
            assert_eq!(arena.instruction_results, 2, "{lanes} lanes");
            assert_eq!(surface.memory_reads(), 0, "{lanes} lanes");
            assert_eq!(surface.memory_writes(), 0, "{lanes} lanes");
            assert_eq!(surface.allocations(), 0, "{lanes} lanes");
            assert_eq!(surface.atomic_operations(), 0, "{lanes} lanes");
            assert_eq!(surface.direct_calls(), 1, "{lanes} lanes");
        }
    }

    #[test]
    fn identity_receipt_detects_mutation_and_never_claims_source_authority() {
        let module = module_with_import();
        let digest = module.stable_digest();
        let manifest = import_manifest(&module);
        let (arena, surface, _) = capture_module_inventory(&module, &manifest).unwrap();
        let receipt = IdentityTransformReceipt::new(
            IdentityCorePolicy::v1(),
            digest,
            target_contract().digest(),
            manifest.digest(),
            arena,
            surface,
            trust_cg_lower::module_local_function_identity_census(&module),
            CoreProofCensus::capture(&module, Vec::new()),
            1,
            0,
            1,
        );
        assert!(receipt.is_intact());
        assert_eq!(receipt.open_module_digest(), receipt.core_module_digest());

        let mut wrong_policy = receipt.clone();
        wrong_policy.policy_digest =
            ProofDigest::sha256_domain("test.foreign-core-policy", b"not identity Core v1");
        wrong_policy.receipt_digest = wrong_policy.compute_digest();
        assert!(
            !wrong_policy.is_intact(),
            "a self-consistent receipt for a non-v1 policy must fail reauthentication"
        );

        let mut corrupt = receipt;
        corrupt.lowered_function_count += 1;
        assert!(!corrupt.is_intact());
    }

    #[test]
    fn admission_owns_exact_validated_module_and_sealed_lowering() {
        let target = core_host_target();
        let module = module_with_import();
        let module_digest = module.stable_digest();
        let manifest = import_manifest(&module);
        let admitted = admit_identity_core_module_for_host_jit(module, &target, manifest.clone())
            .expect("valid identity-Core fixture must be admitted");

        assert_eq!(
            admitted.permitted_native_mode(),
            CorePermittedNativeMode::ClosedHostJit
        );
        assert_eq!(admitted.module_digest(), module_digest);
        assert_eq!(admitted.receipt().open_module_digest(), module_digest);
        assert_eq!(admitted.receipt().core_module_digest(), module_digest);
        assert_eq!(
            admitted.declared_import_manifest().digest(),
            manifest.digest()
        );
        assert_eq!(admitted.strict_adapter().functions().len(), 1);
        assert_eq!(admitted.executable_surface().defined_functions().len(), 1);
        assert_eq!(
            admitted
                .receipt()
                .module_local_function_identity_census()
                .materialized_identities,
            0
        );
        assert!(
            admitted
                .proof_census()
                .replayed_certificate_refs()
                .is_empty()
        );
        assert!(admitted.receipt().is_intact());
        assert_eq!(admitted.module().stable_digest(), module_digest);
    }

    #[test]
    fn lir_native_dependency_binding_fails_closed_on_missing_map_row_without_mutation() {
        let target = core_host_target();
        let module = module_with_import();
        let manifest = import_manifest(&module);
        let mut admitted =
            admit_identity_core_module_for_host_jit(module, &target, manifest).unwrap();
        let catalog = CoreNativeRuntimeCatalog::try_from_declared_import_manifest(
            admitted.declared_import_manifest(),
        )
        .unwrap();
        let mut references = admitted.native_dependency_reference_map(&catalog).unwrap();
        references.entries.clear();
        references.digest = references.compute_digest();

        let error = admitted
            .bind_declared_external_calls(&catalog, &references)
            .unwrap_err();
        assert_eq!(
            error,
            CoreLirNativeDependencyBindingError::MissingImportedFunctionMapping { function: 0 }
        );
        assert!(admitted
            .strict_adapter
            .functions()
            .iter()
            .flat_map(|(function, _)| function.blocks.values())
            .flat_map(|block| &block.instructions)
            .any(|instruction| matches!(instruction.opcode,
                trust_cg_lower::instructions::Opcode::Call {
                    binding: trust_cg_lower::instructions::DirectCallBinding::DeclaredExternalFunction { function: 0 },
                    ..
                })));
    }

    #[test]
    fn lir_native_dependency_binding_rewrites_the_authenticated_carrier_only_after_validation() {
        let target = core_host_target();
        let module = module_with_import();
        let manifest = import_manifest(&module);
        let mut admitted =
            admit_identity_core_module_for_host_jit(module, &target, manifest).unwrap();
        let catalog = CoreNativeRuntimeCatalog::try_from_declared_import_manifest(
            admitted.declared_import_manifest(),
        )
        .unwrap();
        let references = admitted.native_dependency_reference_map(&catalog).unwrap();
        let bindings = admitted
            .bind_declared_external_calls(&catalog, &references)
            .unwrap();

        assert!(bindings.is_intact());
        assert_eq!(bindings.entries.len(), 1);
        assert_eq!(bindings.entries[0].imported_function, FuncId::new(0));
        assert_eq!(bindings.entries[0].dependency, NativeDependencyId::new(0));
        assert!(
            admitted
                .strict_adapter
                .functions()
                .iter()
                .flat_map(|(function, _)| function.blocks.values())
                .flat_map(|block| &block.instructions)
                .any(|instruction| matches!(instruction.opcode,
                trust_cg_lower::instructions::Opcode::Call {
                    binding: trust_cg_lower::instructions::DirectCallBinding::NativeDependency {
                        function: 0,
                        dependency,
                    },
                    ..
                } if dependency == NativeDependencyId::new(0)))
        );
    }

    fn planned_import_fixture() -> (
        CoreConsumableParts,
        CoreNativeRuntimeCatalog,
        CoreNativeDependencyReferenceMap,
        CoreLirNativeDependencyBindings,
    ) {
        let target = core_host_target();
        let module = module_with_import();
        let manifest = import_manifest(&module);
        let mut admitted =
            admit_identity_core_module_for_host_jit(module, &target, manifest).unwrap();
        let catalog = CoreNativeRuntimeCatalog::try_from_declared_import_manifest(
            admitted.declared_import_manifest(),
        )
        .unwrap();
        let references = admitted.native_dependency_reference_map(&catalog).unwrap();
        let bindings = admitted
            .bind_declared_external_calls(&catalog, &references)
            .unwrap();
        let parts = admitted.into_consumable_parts();
        (parts, catalog, references, bindings)
    }

    fn planned_exact_call_fixture() -> (
        CoreConsumableParts,
        CoreNativeRuntimeCatalog,
        CoreNativeDependencyReferenceMap,
        CoreLirNativeDependencyBindings,
    ) {
        let target = core_host_target();
        let mut admitted = admit_identity_core_module_for_host_jit(
            module_with_exact_call(),
            &target,
            CoreDeclaredImportManifest::empty(),
        )
        .unwrap();
        let catalog = CoreNativeRuntimeCatalog::try_from_declared_import_manifest(
            admitted.declared_import_manifest(),
        )
        .unwrap();
        let references = admitted.native_dependency_reference_map(&catalog).unwrap();
        let bindings = admitted
            .bind_declared_external_calls(&catalog, &references)
            .unwrap();
        let parts = admitted.into_consumable_parts();
        (parts, catalog, references, bindings)
    }

    #[test]
    fn planned_integrity_reauthenticates_the_complete_imported_call_tuple() {
        let (parts, catalog, references, bindings) = planned_import_fixture();
        parts
            .check_planned_integrity(&catalog, &references, &bindings)
            .expect("freshly planned call carriers and sidecars must replay");

        let (mut parts, catalog, references, bindings) = planned_import_fixture();
        Arc::get_mut(&mut parts.module)
            .expect("unique test fixture")
            .functions[1]
            .blocks[0]
            .body
            .pop();
        assert!(matches!(
            parts.check_planned_integrity(&catalog, &references, &bindings),
            Err(CoreJitPlanIntegrityError::ModuleDigestMismatch { .. })
        ));

        let (mut parts, catalog, references, bindings) = planned_import_fixture();
        parts.declared_import_manifest.digest = ProofDigest::zero();
        assert!(matches!(
            parts.check_planned_integrity(&catalog, &references, &bindings),
            Err(CoreJitPlanIntegrityError::DeclaredImportManifestNotIntact)
        ));

        let (mut parts, catalog, references, bindings) = planned_import_fixture();
        let CoreHostImport::Function(import) = &mut parts.declared_import_manifest.imports[0]
        else {
            unreachable!()
        };
        import.implementation_contract_version.push_str("-drift");
        parts.declared_import_manifest.digest =
            core_declared_import_manifest_digest(&parts.declared_import_manifest.imports).unwrap();
        assert!(parts.declared_import_manifest.is_intact());
        assert!(matches!(
            parts.check_planned_integrity(&catalog, &references, &bindings),
            Err(CoreJitPlanIntegrityError::DeclaredImportManifestDigestMismatch)
        ));

        let (parts, mut catalog, references, bindings) = planned_import_fixture();
        catalog.digest = ProofDigest::zero();
        assert!(matches!(
            parts.check_planned_integrity(&catalog, &references, &bindings),
            Err(CoreJitPlanIntegrityError::NativeRuntimeCatalogNotIntact)
        ));

        let (parts, mut catalog, references, bindings) = planned_import_fixture();
        let CoreHostImport::Function(import) = &mut catalog.entries[0].import else {
            unreachable!()
        };
        import.implementation_contract_version.push_str("-drift");
        catalog.digest = catalog.compute_digest().unwrap();
        assert!(catalog.is_intact());
        assert!(matches!(
            parts.check_planned_integrity(&catalog, &references, &bindings),
            Err(CoreJitPlanIntegrityError::NativeRuntimeCatalogEntryMismatch { .. })
        ));

        let (parts, catalog, mut references, bindings) = planned_import_fixture();
        references.digest = ProofDigest::zero();
        assert!(matches!(
            parts.check_planned_integrity(&catalog, &references, &bindings),
            Err(CoreJitPlanIntegrityError::NativeDependencyReferenceMapNotIntact)
        ));

        let (parts, catalog, references, mut bindings) = planned_import_fixture();
        bindings.digest = ProofDigest::zero();
        assert!(matches!(
            parts.check_planned_integrity(&catalog, &references, &bindings),
            Err(CoreJitPlanIntegrityError::LirNativeDependencyBindingsNotIntact)
        ));

        let (parts, catalog, references, mut bindings) = planned_import_fixture();
        bindings.entries[0].caller = FuncId::new(99);
        bindings.digest = bindings.compute_digest();
        assert!(bindings.is_intact());
        assert!(matches!(
            parts.check_planned_integrity(&catalog, &references, &bindings),
            Err(CoreJitPlanIntegrityError::NativeDependencyBindingMismatch {
                field: "caller",
                ..
            })
        ));

        let (parts, catalog, references, mut bindings) = planned_import_fixture();
        bindings.entries[0].edge_digest = ProofDigest::zero();
        bindings.digest = bindings.compute_digest();
        assert!(bindings.is_intact());
        assert!(matches!(
            parts.check_planned_integrity(&catalog, &references, &bindings),
            Err(CoreJitPlanIntegrityError::NativeDependencyEdgeDigestMismatch { .. })
        ));
    }

    #[test]
    fn planned_integrity_replays_actual_lir_edge_content() {
        let (mut parts, catalog, references, bindings) = planned_import_fixture();
        let function = &mut parts.lir_functions[0].0;
        let call = function
            .blocks
            .values_mut()
            .flat_map(|block| &mut block.instructions)
            .find(|instruction| {
                matches!(
                    instruction.opcode,
                    trust_cg_lower::instructions::Opcode::Call { .. }
                )
            })
            .expect("fixture has one native call");
        call.args[0] = trust_cg_lower::instructions::Value(99);
        assert!(matches!(
            parts.check_planned_integrity(&catalog, &references, &bindings),
            Err(CoreJitPlanIntegrityError::NativeDependencyEdgeDigestMismatch { .. })
        ));

        let (mut parts, catalog, references, bindings) = planned_import_fixture();
        let function = &mut parts.lir_functions[0].0;
        let call = function
            .blocks
            .values_mut()
            .flat_map(|block| &mut block.instructions)
            .find(|instruction| {
                matches!(
                    instruction.opcode,
                    trust_cg_lower::instructions::Opcode::Call { .. }
                )
            })
            .expect("fixture has one native call");
        let trust_cg_lower::instructions::Opcode::Call { name, .. } = &mut call.opcode else {
            unreachable!()
        };
        name.push_str("-drift");
        assert!(matches!(
            parts.check_planned_integrity(&catalog, &references, &bindings),
            Err(CoreJitPlanIntegrityError::LirCallNameMismatch { .. })
        ));

        let (mut parts, catalog, references, bindings) = planned_import_fixture();
        let function = &mut parts.lir_functions[0].0;
        let call = function
            .blocks
            .values_mut()
            .flat_map(|block| &mut block.instructions)
            .find(|instruction| {
                matches!(
                    instruction.opcode,
                    trust_cg_lower::instructions::Opcode::Call { .. }
                )
            })
            .expect("fixture has one native call");
        let argument = call.args[0];
        function
            .value_types
            .insert(argument, trust_cg_lower::types::Type::F64);
        assert!(matches!(
            parts.check_planned_integrity(&catalog, &references, &bindings),
            Err(CoreJitPlanIntegrityError::NativeDependencyEdgeDigestMismatch { .. })
        ));
    }

    #[test]
    fn planned_integrity_replays_exact_call_identity_without_overclaiming_edge_identity() {
        let (parts, catalog, references, bindings) = planned_exact_call_fixture();
        parts
            .check_planned_integrity(&catalog, &references, &bindings)
            .expect("fresh exact-call identities must replay");

        let (mut parts, catalog, references, bindings) = planned_exact_call_fixture();
        let call = parts
            .lir_functions
            .iter_mut()
            .flat_map(|(function, _)| function.blocks.values_mut())
            .flat_map(|block| &mut block.instructions)
            .find(|instruction| {
                matches!(
                    instruction.opcode,
                    trust_cg_lower::instructions::Opcode::Call { .. }
                )
            })
            .expect("fixture has one exact call");
        let trust_cg_lower::instructions::Opcode::Call { binding, .. } = &mut call.opcode else {
            unreachable!()
        };
        *binding =
            trust_cg_lower::instructions::DirectCallBinding::ExactModuleFunction { function: 99 };
        assert!(matches!(
            parts.check_planned_integrity(&catalog, &references, &bindings),
            Err(CoreJitPlanIntegrityError::LirCallFunctionIdentityMismatch {
                expected: 0,
                actual: 99,
                ..
            })
        ));

        let (mut parts, catalog, references, bindings) = planned_exact_call_fixture();
        let function = parts
            .lir_functions
            .iter_mut()
            .map(|(function, _)| function)
            .find(|function| function.name == "entry")
            .expect("fixture retains the source caller");
        let (block_id, instruction_index) = function
            .blocks
            .iter()
            .find_map(|(block_id, block)| {
                block
                    .instructions
                    .iter()
                    .position(|instruction| {
                        matches!(
                            instruction.opcode,
                            trust_cg_lower::instructions::Opcode::Call { .. }
                        )
                    })
                    .map(|index| (*block_id, index))
            })
            .unwrap();
        function.trust_ir_origins.get_mut(&block_id).unwrap()[instruction_index] = None;
        assert!(matches!(
            parts.check_planned_integrity(&catalog, &references, &bindings),
            Err(CoreJitPlanIntegrityError::LirCallMissingSourceOrigin { .. })
        ));
    }

    #[test]
    fn planned_integrity_rejects_paired_reference_binding_and_lir_drift() {
        let (mut parts, catalog, mut references, mut bindings) = planned_import_fixture();
        let forged_function = FuncId::new(99);
        references.entries[0].function = forged_function;
        references.digest = references.compute_digest();

        let function = &mut parts.lir_functions[0].0;
        let (block_id, instruction_index) = function
            .blocks
            .iter_mut()
            .find_map(|(block_id, block)| {
                block
                    .instructions
                    .iter_mut()
                    .enumerate()
                    .find_map(|(index, instruction)| match &mut instruction.opcode {
                        trust_cg_lower::instructions::Opcode::Call {
                            binding:
                                trust_cg_lower::instructions::DirectCallBinding::NativeDependency {
                                    function,
                                    ..
                                },
                            ..
                        } => {
                            *function = forged_function.index();
                            Some((*block_id, index))
                        }
                        _ => None,
                    })
            })
            .expect("fixture has one native call");
        bindings.entries[0].imported_function = forged_function;
        let encoded_signature = serde_json::to_vec(&function.signature).unwrap();
        bindings.entries[0].edge_digest = core_lir_native_dependency_edge_digest(
            bindings.entries[0].caller,
            0,
            block_id.0,
            instruction_index,
            bindings.entries[0].source_origin,
            forged_function,
            bindings.entries[0].dependency,
            function,
            &encoded_signature,
            &function.blocks[&block_id].instructions[instruction_index],
        )
        .unwrap();
        bindings.native_dependency_reference_map_digest = references.digest();
        bindings.digest = bindings.compute_digest();

        assert!(references.is_intact());
        assert!(bindings.is_intact());
        assert!(matches!(
            parts.check_planned_integrity(&catalog, &references, &bindings),
            Err(CoreJitPlanIntegrityError::NativeDependencyReferenceMissing { function: 0 })
        ));
    }

    #[test]
    fn lir_native_dependency_binding_rejects_prebound_or_foreign_id() {
        let target = core_host_target();
        let module = module_with_import();
        let manifest = import_manifest(&module);
        let mut admitted =
            admit_identity_core_module_for_host_jit(module, &target, manifest).unwrap();
        let catalog = CoreNativeRuntimeCatalog::try_from_declared_import_manifest(
            admitted.declared_import_manifest(),
        )
        .unwrap();
        let references = admitted.native_dependency_reference_map(&catalog).unwrap();
        let binding = admitted
            .strict_adapter
            .functions_mut()
            .iter_mut()
            .flat_map(|(function, _)| function.blocks.values_mut())
            .flat_map(|block| &mut block.instructions)
            .find_map(|instruction| match &mut instruction.opcode {
                trust_cg_lower::instructions::Opcode::Call { binding, .. } => Some(binding),
                _ => None,
            })
            .unwrap();
        *binding = trust_cg_lower::instructions::DirectCallBinding::NativeDependency {
            function: 0,
            dependency: NativeDependencyId::new(99),
        };

        assert_eq!(
            admitted
                .bind_declared_external_calls(&catalog, &references)
                .unwrap_err(),
            CoreLirNativeDependencyBindingError::PreboundOrForeignDependency {
                function: 0,
                dependency: NativeDependencyId::new(99),
            }
        );
    }

    #[test]
    fn consumption_integrity_rechecks_attached_receipts_before_moving_lir() {
        let module = self_contained_module();
        let mut admitted = admit_identity_core_module_for_host_jit(
            module,
            &core_host_target(),
            CoreDeclaredImportManifest::empty(),
        )
        .unwrap();
        admitted.receipt.receipt_digest =
            ProofDigest::sha256_domain("test.corrupt-receipt", b"not an intact receipt");
        assert!(matches!(
            admitted.check_consumption_integrity(),
            Err(CoreConsumptionIntegrityError::ReceiptNotIntact)
        ));

        let module = self_contained_module();
        let mut admitted = admit_identity_core_module_for_host_jit(
            module,
            &core_host_target(),
            CoreDeclaredImportManifest::empty(),
        )
        .unwrap();
        admitted.receipt.target_contract_digest =
            ProofDigest::sha256_domain("test.wrong-target-contract", b"not the attached contract");
        admitted.receipt.receipt_digest = admitted.receipt.compute_digest();
        assert!(matches!(
            admitted.check_consumption_integrity(),
            Err(CoreConsumptionIntegrityError::TargetContractDigestMismatch)
        ));
        assert_eq!(admitted.retained_strict_function_count(), 1);

        let module = self_contained_module();
        let mut admitted = admit_identity_core_module_for_host_jit(
            module,
            &core_host_target(),
            CoreDeclaredImportManifest::empty(),
        )
        .unwrap();
        admitted.receipt.declared_import_manifest_digest = ProofDigest::sha256_domain(
            "test.wrong-declared-import-manifest",
            b"not the attached manifest",
        );
        admitted.receipt.receipt_digest = admitted.receipt.compute_digest();
        assert!(matches!(
            admitted.check_consumption_integrity(),
            Err(CoreConsumptionIntegrityError::DeclaredImportManifestDigestMismatch)
        ));

        let module = self_contained_module();
        let mut admitted = admit_identity_core_module_for_host_jit(
            module,
            &core_host_target(),
            CoreDeclaredImportManifest::empty(),
        )
        .unwrap();
        let host_architecture = core_host_target().target_spec().architecture;
        let foreign_target = match host_architecture {
            Target::Aarch64 => TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap(),
            Target::X86_64 => TargetSpec::parse("x86_64-unknown-linux-gnu").unwrap(),
            Target::Riscv64 => unreachable!("Core admission rejects this host"),
        };
        let foreign_target = if foreign_target == exact_spec() {
            match host_architecture {
                Target::Aarch64 => TargetSpec::parse("aarch64-apple-darwin").unwrap(),
                Target::X86_64 => TargetSpec::parse("x86_64-apple-darwin").unwrap(),
                Target::Riscv64 => unreachable!("Core admission rejects this host"),
            }
        } else {
            foreign_target
        };
        let foreign_module = self_contained_module();
        let foreign_strict =
            crate::strict_adapter::translate_core_module_for_target_with_validation_and_license(
                &foreign_module,
                foreign_target,
                &permit_unlicensed(),
            )
            .unwrap();
        admitted.target_contract.adapter_target = foreign_strict.target().clone();
        assert!(matches!(
            admitted.check_consumption_integrity(),
            Err(CoreConsumptionIntegrityError::StrictTargetMismatch)
        ));

        let module = self_contained_module();
        let mut admitted = admit_identity_core_module_for_host_jit(
            module,
            &core_host_target(),
            CoreDeclaredImportManifest::empty(),
        )
        .unwrap();
        admitted.receipt.lowered_function_count += 1;
        admitted.receipt.receipt_digest = admitted.receipt.compute_digest();
        assert!(matches!(
            admitted.check_consumption_integrity(),
            Err(
                CoreConsumptionIntegrityError::RetainedFunctionCountMismatch {
                    expected: 2,
                    actual: 1,
                }
            )
        ));

        let module = self_contained_module();
        let mut admitted = admit_identity_core_module_for_host_jit(
            module,
            &core_host_target(),
            CoreDeclaredImportManifest::empty(),
        )
        .unwrap();
        admitted.receipt.exact_module_call_count += 1;
        admitted.receipt.receipt_digest = admitted.receipt.compute_digest();
        assert!(matches!(
            admitted.check_consumption_integrity(),
            Err(
                CoreConsumptionIntegrityError::RetainedExactModuleCallCountMismatch {
                    expected: 1,
                    actual: 0,
                }
            )
        ));

        let module = module_with_import();
        let manifest = import_manifest(&module);
        let mut admitted =
            admit_identity_core_module_for_host_jit(module, &core_host_target(), manifest).unwrap();
        admitted.declared_import_references.functions.clear();
        assert!(matches!(
            admitted.check_consumption_integrity(),
            Err(
                CoreConsumptionIntegrityError::RetainedImportedFunctionCountMismatch {
                    expected: 1,
                    actual: 0,
                }
            )
        ));

        let module = module_with_import();
        let manifest = import_manifest(&module);
        let mut admitted =
            admit_identity_core_module_for_host_jit(module, &core_host_target(), manifest).unwrap();
        admitted.declared_import_references.functions[0].function = FuncId::new(99);
        assert!(matches!(
            admitted.check_consumption_integrity(),
            Err(
                CoreConsumptionIntegrityError::RetainedImportedFunctionIdentityMismatch {
                    index: 0,
                    expected: 0,
                    actual: 99,
                }
            )
        ));

        let module = module_with_import();
        let manifest = import_manifest(&module);
        let mut admitted =
            admit_identity_core_module_for_host_jit(module, &core_host_target(), manifest).unwrap();
        admitted.declared_import_references.functions[0].manifest_index = 99;
        assert!(matches!(
            admitted.check_consumption_integrity(),
            Err(CoreConsumptionIntegrityError::RetainedImportReferenceSeedNotIntact)
        ));
    }

    #[test]
    fn admission_requires_explicit_abi_and_native_c_aggregate_passing() {
        let mut missing_abi = self_contained_module();
        missing_abi.target_info.as_mut().unwrap().abi = None;
        assert!(matches!(
            admit_identity_core_module_for_host_jit(
                missing_abi,
                &core_host_target(),
                CoreDeclaredImportManifest::empty(),
            ),
            Err(CoreAdmissionError::Target(
                CoreTargetContractError::TrustIrAbiMissing
            ))
        ));

        let mut unclassified = self_contained_module();
        unclassified.target_info.as_mut().unwrap().struct_passing =
            StructPassingPolicy::Unclassified;
        assert!(matches!(
            admit_identity_core_module_for_host_jit(
                unclassified,
                &core_host_target(),
                CoreDeclaredImportManifest::empty(),
            ),
            Err(CoreAdmissionError::Target(
                CoreTargetContractError::TrustIrStructPassingUnsupported {
                    actual: StructPassingPolicy::Unclassified
                }
            ))
        ));

        let mut always_memory = self_contained_module();
        always_memory.target_info.as_mut().unwrap().struct_passing =
            StructPassingPolicy::AlwaysMemory;
        assert!(matches!(
            admit_identity_core_module_for_host_jit(
                always_memory,
                &core_host_target(),
                CoreDeclaredImportManifest::empty(),
            ),
            Err(CoreAdmissionError::Target(
                CoreTargetContractError::TrustIrStructPassingUnsupported {
                    actual: StructPassingPolicy::AlwaysMemory
                }
            ))
        ));
    }

    #[test]
    fn admission_rejects_tls_globals_module_wide() {
        let mut module = self_contained_module();
        module.globals.push(Global {
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
            name: "unreferenced_tls".to_owned(),
            ty: Ty::I64,
            mutable: true,
            initializer: Some(Constant::Int(0)),
            linkage: Linkage::Internal,
            tls: Some(TlsModel::LocalExec),
            align: Some(8),
        });
        assert!(matches!(
            admit_identity_core_module_for_host_jit(
                module,
                &core_host_target(),
                CoreDeclaredImportManifest::empty(),
            ),
            Err(CoreAdmissionError::ModuleClosure(
                CoreModuleClosureError::ThreadLocalGlobalUnsupported { symbol }
            )) if symbol == "unreferenced_tls"
        ));
    }

    #[test]
    fn admission_requires_the_exact_host_jit_target() {
        let target = core_host_target();
        let mut module = self_contained_module();
        module.target_info.as_mut().unwrap().triple = "foreign-unknown-target".to_owned();
        assert!(matches!(
            admit_identity_core_module_for_host_jit(
                module,
                &target,
                CoreDeclaredImportManifest::empty(),
            ),
            Err(CoreAdmissionError::Target(
                CoreTargetContractError::TrustIrTripleMismatch { .. }
            ))
        ));
    }

    #[test]
    fn admission_rejects_every_module_global_until_jit_owns_data() {
        let mut defined = self_contained_module();
        defined.globals.push(Global {
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
            name: "defined_data".to_owned(),
            ty: Ty::I64,
            mutable: false,
            initializer: Some(Constant::Int(7)),
            linkage: Linkage::Internal,
            tls: None,
            align: Some(8),
        });
        assert!(matches!(
            admit_identity_core_module_for_host_jit(
                defined,
                &core_host_target(),
                CoreDeclaredImportManifest::empty(),
            ),
            Err(CoreAdmissionError::ModuleClosure(
                CoreModuleClosureError::DefinedGlobalUnsupported { symbol }
            )) if symbol == "defined_data"
        ));

        let mut imported = self_contained_module();
        imported.globals.push(Global {
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
            name: "imported_data".to_owned(),
            ty: Ty::I64,
            mutable: true,
            initializer: None,
            linkage: Linkage::External,
            tls: None,
            align: Some(8),
        });
        assert!(matches!(
            admit_identity_core_module_for_host_jit(
                imported,
                &core_host_target(),
                CoreDeclaredImportManifest::empty(),
            ),
            Err(CoreAdmissionError::ModuleClosure(
                CoreModuleClosureError::ImportedGlobalUnsupported { symbol }
            )) if symbol == "imported_data"
        ));
    }

    #[test]
    fn admission_rejects_interposable_bodied_call_target() {
        let mut module = self_contained_module();
        let signature = module.functions[0].ty;
        module.functions[0].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![],
            }),
        );
        let mut target = Function::new(
            FuncId::new(1),
            "interposable_target",
            signature,
            trust_ir::BlockId::new(0),
        );
        target.linkage = Linkage::External;
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        target.blocks.push(block);
        module
            .try_add_function(target)
            .expect("Module::try_add_function: test fixture");

        assert!(matches!(
            admit_identity_core_module_for_host_jit(
                module,
                &core_host_target(),
                CoreDeclaredImportManifest::empty(),
            ),
            Err(CoreAdmissionError::ModuleClosure(
                CoreModuleClosureError::InterposableDefinedFunctionCall { callee, .. }
            )) if callee == "interposable_target"
        ));
    }

    #[test]
    fn admission_rejects_raw_symbol_address_constants() {
        let mut module = self_contained_module();
        module.functions[0].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::Const {
                ty: Ty::Ptr,
                value: Constant::SymbolAddr {
                    symbol: "undeclared_native_symbol".to_owned(),
                    addend: 0,
                },
            })
            .with_result(ValueId::new(0)),
        );
        assert!(matches!(
            admit_identity_core_module_for_host_jit(
                module,
                &core_host_target(),
                CoreDeclaredImportManifest::empty(),
            ),
            Err(CoreAdmissionError::ModuleClosure(
                CoreModuleClosureError::SymbolAddressUnsupported { symbol, .. }
            )) if symbol == "undeclared_native_symbol"
        ));
    }

    #[test]
    fn inventory_rejects_varargs_and_nonexternal_declarations_explicitly() {
        let mut varargs = self_contained_module();
        varargs
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![],
                abi: None,
                is_vararg: true,
            })
            .expect("Module::add_func_type: test fixture");
        assert!(matches!(
            capture_module_inventory(&varargs, &CoreDeclaredImportManifest::empty()),
            Err(CoreModuleClosureError::VarArgsUnsupported { .. })
        ));

        let mut declaration = module_with_import();
        declaration.functions[0].linkage = Linkage::Private;
        assert!(matches!(
            capture_module_inventory(&declaration, &import_manifest(&declaration)),
            Err(CoreModuleClosureError::InvalidFunctionImportLinkage { symbol, .. })
                if symbol == "runtime_inc"
        ));
    }

    #[test]
    fn inventory_rejects_undeclared_name_based_adapter_semantics() {
        let mut module = module_with_import();
        module.functions[0].name = "memcpy".to_owned();
        let manifest = import_manifest(&module);
        assert!(matches!(
            capture_module_inventory(&module, &manifest),
            Err(CoreModuleClosureError::NameDependentCallSemanticsUnsupported {
                callee,
                semantics: AdapterNamedCallSemantics::Memcpy,
                ..
            }) if callee == "memcpy"
        ));
    }

    #[test]
    fn admission_honors_exact_internal_definition_before_name_semantics() {
        let mut module = self_contained_module();
        let signature = module.functions[0].ty;
        module.functions[0].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![],
            }),
        );
        let mut target = Function::new(
            FuncId::new(1),
            "memcpy",
            signature,
            trust_ir::BlockId::new(0),
        );
        target.linkage = Linkage::Internal;
        let mut block = Block::new(trust_ir::BlockId::new(0));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        target.blocks.push(block);
        module
            .try_add_function(target)
            .expect("Module::try_add_function: test fixture");

        let admitted = admit_identity_core_module_for_host_jit(
            module,
            &core_host_target(),
            CoreDeclaredImportManifest::empty(),
        )
        .expect("an exact internal body owns its semantics regardless of symbol spelling");
        assert_eq!(admitted.executable_surface().direct_calls(), 1);
        assert_eq!(admitted.receipt().exact_module_call_count(), 1);
    }

    #[test]
    fn admission_rejects_materialized_local_function_identity() {
        let mut module = self_contained_module();
        let target_ty = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let entry_block = &mut module.functions[0].blocks[0];
        entry_block.body.insert(
            0,
            InstrNode::new(Inst::Const {
                ty: Ty::Func(target_ty),
                value: Constant::FnDef(FuncId::new(1)),
            })
            .with_result(ValueId::new(0)),
        );
        let mut target = Function::new(
            FuncId::new(1),
            "local_target",
            target_ty,
            trust_ir::BlockId::new(0),
        );
        target.linkage = Linkage::Internal;
        let mut target_block = Block::new(trust_ir::BlockId::new(0));
        target_block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        target.blocks.push(target_block);
        module
            .try_add_function(target)
            .expect("Module::try_add_function: test fixture");

        assert!(matches!(
            admit_identity_core_module_for_host_jit(
                module,
                &core_host_target(),
                CoreDeclaredImportManifest::empty(),
            ),
            Err(
                CoreAdmissionError::MaterializedModuleLocalFunctionIdentityUnsupported { count: 1 }
            )
        ));
    }

    #[test]
    fn core_constant_binding_keeps_nominal_items_distinct_from_external_code_addresses() {
        let mut module = self_contained_module();
        let id = FuncId::new(1);
        module.functions.push(Function::new(
            id,
            "external_target",
            FuncTyId::new(0),
            trust_ir::BlockId::new(0),
        ));
        let functions = ModuleFunctionCatalog::new(&module);
        let owner = &module.functions[0];
        validate_core_constant_binding(&Constant::FnDef(id), owner, &functions).unwrap();
        for value in [
            Constant::FnItem(id),
            Constant::Aggregate(vec![Constant::Int(7), Constant::FnItem(id)]),
            Constant::Splat {
                elem: Box::new(Constant::FnItem(id)),
                len: u64::MAX,
            },
            Constant::Closure {
                func: id,
                captures: vec![Constant::FnItem(id)],
            },
        ] {
            assert!(matches!(
                validate_core_constant_binding(&value, owner, &functions),
                Err(CoreModuleClosureError::NominalFunctionItemUnsupported { target: 1, .. })
            ));
        }
    }

    #[test]
    fn failed_full_validation_never_mints_an_owner() {
        let mut module = self_contained_module();
        module.functions[0].blocks[0].body.clear();
        let error = admit_identity_core_module_for_host_jit(
            module,
            &core_host_target(),
            CoreDeclaredImportManifest::empty(),
        )
        .expect_err("invalid TrustIR must be rejected before strict lowering");
        assert!(matches!(
            error,
            CoreAdmissionError::TrustIrValidation { .. }
        ));
        assert!(!error.validation_errors().unwrap().is_empty());
    }

    #[test]
    fn function_type_id_fixture_is_registered() {
        let module = module_with_import();
        assert_eq!(module.functions[0].ty, FuncTyId::new(0));
    }
}
