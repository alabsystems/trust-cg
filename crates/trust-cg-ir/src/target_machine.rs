// trust-cg-ir - Immutable target-machine capability contract
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Shared target identity and feature-admission primitives.
//!
//! A [`TargetMachine`] captures two facts that must not drift during a
//! compilation:
//!
//! - the immutable target identity selected by the caller; and
//! - the typed optional features that machine-code production may use.
//!
//! Machine-code owners derive [`OutputTargetFeatures`] from the instructions
//! they actually produced and validate that set against the admitted set. The
//! distinct admitted/output types make the safety relation explicit and keep
//! callers from accidentally checking the subset in the wrong direction.

use std::{error::Error, fmt, hash::Hash, marker::PhantomData};

use crate::{aarch64_regs, riscv_regs, x86_64_regs};

/// Supported register-machine target architectures.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Target {
    /// x86-64 (AMD64).
    X86_64,
    /// AArch64 (ARM64).
    Aarch64,
    /// RISC-V 64-bit.
    Riscv64,
}

impl Target {
    /// Returns the pointer size in bytes for this target.
    pub fn pointer_bytes(self) -> u32 {
        match self {
            Self::X86_64 | Self::Aarch64 | Self::Riscv64 => 8,
        }
    }

    /// Returns the canonical architecture name.
    pub fn name(self) -> &'static str {
        match self {
            Self::X86_64 => "x86_64",
            Self::Aarch64 => "aarch64",
            Self::Riscv64 => "riscv64",
        }
    }

    /// Returns the required stack alignment in bytes.
    pub fn stack_alignment(self) -> u32 {
        match self {
            Self::X86_64 | Self::Aarch64 | Self::Riscv64 => 16,
        }
    }

    /// Returns the number of integer argument-passing registers.
    pub fn num_arg_gprs(self) -> usize {
        match self {
            Self::X86_64 => x86_64_regs::X86_ARG_GPRS.len(),
            Self::Aarch64 => aarch64_regs::ARG_GPRS.len(),
            Self::Riscv64 => riscv_regs::RISCV_ARG_GPRS.len(),
        }
    }

    /// Returns the number of floating-point argument-passing registers.
    pub fn num_arg_fprs(self) -> usize {
        match self {
            Self::X86_64 => x86_64_regs::X86_ARG_XMMS.len(),
            Self::Aarch64 => aarch64_regs::ARG_FPRS.len(),
            Self::Riscv64 => riscv_regs::RISCV_ARG_FPRS.len(),
        }
    }

    /// Returns the number of callee-saved GPRs.
    pub fn num_callee_saved_gprs(self) -> usize {
        match self {
            Self::X86_64 => x86_64_regs::X86_CALLEE_SAVED_GPRS.len(),
            Self::Aarch64 => aarch64_regs::CALLEE_SAVED_GPRS.len(),
            Self::Riscv64 => riscv_regs::RISCV_CALLEE_SAVED_GPRS.len(),
        }
    }

    /// Returns the number of allocatable GPRs.
    pub fn num_allocatable_gprs(self) -> usize {
        match self {
            Self::X86_64 => x86_64_regs::X86_ALLOCATABLE_GPRS.len(),
            Self::Aarch64 => aarch64_regs::ALLOCATABLE_GPRS.len(),
            Self::Riscv64 => riscv_regs::RISCV_ALLOCATABLE_GPRS.len(),
        }
    }

    /// Returns whether this target requires a frame pointer by default.
    pub fn requires_frame_pointer(self) -> bool {
        match self {
            Self::Aarch64 => true,
            Self::X86_64 | Self::Riscv64 => false,
        }
    }

    /// Returns the target architecture of the host process.
    ///
    /// Unknown host architectures retain Trust Codegen's historical AArch64
    /// fallback. This is a compatibility default, not optional-ISA authority.
    pub fn host() -> Self {
        #[cfg(target_arch = "x86_64")]
        {
            Self::X86_64
        }
        #[cfg(target_arch = "aarch64")]
        {
            Self::Aarch64
        }
        #[cfg(target_arch = "riscv64")]
        {
            Self::Riscv64
        }
        #[cfg(not(any(
            target_arch = "x86_64",
            target_arch = "aarch64",
            target_arch = "riscv64",
        )))]
        {
            Self::Aarch64
        }
    }

    /// Returns the calling-convention description for this target.
    pub fn calling_convention(self) -> CallingConvention {
        match self {
            Self::Aarch64 => CallingConvention {
                name: "aapcs64",
                num_arg_gprs: 8,
                num_arg_fprs: 8,
                num_ret_gprs: 8,
                num_ret_fprs: 8,
                red_zone_size: 128,
                shadow_space: 0,
            },
            Self::X86_64 => CallingConvention {
                name: "sysv_amd64",
                num_arg_gprs: 6,
                num_arg_fprs: 8,
                num_ret_gprs: 2,
                num_ret_fprs: 2,
                red_zone_size: 128,
                shadow_space: 0,
            },
            Self::Riscv64 => CallingConvention {
                name: "riscv_lp64d",
                num_arg_gprs: 8,
                num_arg_fprs: 8,
                num_ret_gprs: 2,
                num_ret_fprs: 2,
                red_zone_size: 0,
                shadow_space: 0,
            },
        }
    }
}

/// Target-generic calling-convention parameters.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CallingConvention {
    /// Calling-convention name.
    pub name: &'static str,
    /// Number of integer/pointer argument-passing registers.
    pub num_arg_gprs: usize,
    /// Number of floating-point argument-passing registers.
    pub num_arg_fprs: usize,
    /// Number of integer return-value registers.
    pub num_ret_gprs: usize,
    /// Number of floating-point return-value registers.
    pub num_ret_fprs: usize,
    /// Red-zone size in bytes.
    pub red_zone_size: u32,
    /// Required shadow/home space in bytes.
    pub shadow_space: u32,
}

/// Immutable target identity accepted by [`TargetMachine`].
///
/// Implementations should include every ABI/object-format component in their
/// equality and hash identity. [`TargetMachine`] owns the identity and exposes
/// it only through a shared reference.
pub trait TargetIdentity: Eq + Hash + fmt::Debug {
    /// Architecture selected by this identity.
    fn architecture(&self) -> Target;
}

impl TargetIdentity for Target {
    fn architecture(&self) -> Target {
        *self
    }
}

/// A closed, architecture-specific optional machine-feature domain.
///
/// Stable feature bits are persistent artifact identity. Existing bits must
/// never be renumbered, and [`Self::ALL`] must contain every feature exactly
/// once in canonical manifest order.
pub trait TargetFeature: Copy + Eq + Hash + fmt::Debug + 'static {
    /// Architecture to which this feature domain belongs.
    const ARCHITECTURE: Target;
    /// Complete feature domain in canonical external order.
    const ALL: &'static [Self];

    /// One stable, non-zero, power-of-two identity bit.
    fn stable_bit(self) -> u64;
    /// Canonical manifest and diagnostic name.
    fn name(self) -> &'static str;
}

/// A validated bitset over one typed target-feature domain.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct TargetFeatureSet<F: TargetFeature> {
    bits: u64,
    feature: PhantomData<fn() -> F>,
}

impl<F: TargetFeature> TargetFeatureSet<F> {
    /// Empty feature set.
    pub const EMPTY: Self = Self {
        bits: 0,
        feature: PhantomData,
    };

    /// Stable feature bits for artifact identities.
    pub const fn bits(self) -> u64 {
        self.bits
    }

    /// Whether the set is empty.
    pub const fn is_empty(self) -> bool {
        self.bits == 0
    }

    /// Whether every feature in `self` is present in `other`.
    pub const fn is_subset_of(self, other: Self) -> bool {
        self.bits & !other.bits == 0
    }

    /// Set union.
    pub const fn union(self, other: Self) -> Self {
        Self {
            bits: self.bits | other.bits,
            feature: PhantomData,
        }
    }

    /// Features present in `self` but absent from `other`.
    pub const fn difference(self, other: Self) -> Self {
        Self {
            bits: self.bits & !other.bits,
            feature: PhantomData,
        }
    }
}

impl<F: TargetFeature> TargetFeatureSet<F> {
    /// Build a validated set from typed features.
    pub fn try_from_features(
        features: impl IntoIterator<Item = F>,
    ) -> Result<Self, TargetFeatureSetError<F>> {
        Self::validate_domain()?;
        let mut set = Self::EMPTY;
        for feature in features {
            set.bits |= Self::declared_bit(feature)?;
        }
        Ok(set)
    }

    /// Return a copy with one typed feature present.
    pub fn with_feature(self, feature: F) -> Result<Self, TargetFeatureSetError<F>> {
        Self::validate_domain()?;
        Ok(Self {
            bits: self.bits | Self::declared_bit(feature)?,
            feature: PhantomData,
        })
    }

    /// Whether this set contains `feature`.
    pub fn contains(self, feature: F) -> bool {
        let bit = feature.stable_bit();
        bit.is_power_of_two() && F::ALL.contains(&feature) && self.bits & bit != 0
    }

    /// Enabled features in canonical [`TargetFeature::ALL`] order.
    pub fn enabled(self) -> impl Iterator<Item = F> {
        F::ALL
            .iter()
            .copied()
            .filter(move |feature| self.contains(*feature))
    }

    fn declared_bit(feature: F) -> Result<u64, TargetFeatureSetError<F>> {
        if F::ALL.contains(&feature) {
            Ok(feature.stable_bit())
        } else {
            Err(TargetFeatureSetError::UndeclaredFeature { feature })
        }
    }

    fn validate_domain() -> Result<(), TargetFeatureSetError<F>> {
        let mut seen = 0_u64;
        for (index, &feature) in F::ALL.iter().enumerate() {
            let bit = feature.stable_bit();
            if !bit.is_power_of_two() {
                return Err(TargetFeatureSetError::InvalidStableBit { feature, bit });
            }
            if seen & bit != 0 {
                return Err(TargetFeatureSetError::DuplicateStableBit { feature, bit });
            }
            seen |= bit;

            let name = feature.name();
            if F::ALL[..index]
                .iter()
                .any(|declared| declared.name() == name)
            {
                return Err(TargetFeatureSetError::DuplicateCanonicalName { feature, name });
            }
        }
        Ok(())
    }
}

impl<F: TargetFeature> Default for TargetFeatureSet<F> {
    fn default() -> Self {
        Self::EMPTY
    }
}

impl<F: TargetFeature> fmt::Debug for TargetFeatureSet<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set()
            .entries((*self).enabled().map(TargetFeature::name))
            .finish()
    }
}

/// Invalid declaration or use of a typed target-feature domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TargetFeatureSetError<F: TargetFeature> {
    /// A feature was used but omitted from the domain's closed `ALL` list.
    UndeclaredFeature { feature: F },
    /// A stable feature bit was zero or contained more than one bit.
    InvalidStableBit { feature: F, bit: u64 },
    /// Two declared features share one persistent identity bit.
    DuplicateStableBit { feature: F, bit: u64 },
    /// Two declared features share one external manifest/diagnostic name.
    DuplicateCanonicalName { feature: F, name: &'static str },
}

impl<F: TargetFeature> fmt::Display for TargetFeatureSetError<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UndeclaredFeature { feature } => {
                write!(
                    f,
                    "target feature `{}` is absent from its closed domain",
                    feature.name()
                )
            }
            Self::InvalidStableBit { feature, bit } => write!(
                f,
                "target feature `{}` has invalid stable bit {bit:#x}",
                feature.name()
            ),
            Self::DuplicateStableBit { feature, bit } => write!(
                f,
                "target feature `{}` reuses stable bit {bit:#x}",
                feature.name()
            ),
            Self::DuplicateCanonicalName { name, .. } => {
                write!(f, "target feature canonical name `{name}` is not unique")
            }
        }
    }
}

impl<F: TargetFeature> Error for TargetFeatureSetError<F> {}

/// Typed optional features admitted for machine-code production.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AdmittedTargetFeatures<F: TargetFeature>(TargetFeatureSet<F>);

impl<F: TargetFeature> AdmittedTargetFeatures<F> {
    /// Admit no optional features.
    pub const NONE: Self = Self(TargetFeatureSet::EMPTY);

    /// Stable admitted-feature bits for artifact identities.
    pub const fn bits(self) -> u64 {
        self.0.bits()
    }

    /// Borrow the role-neutral validated set.
    pub const fn as_set(self) -> TargetFeatureSet<F> {
        self.0
    }
}

impl<F: TargetFeature> AdmittedTargetFeatures<F> {
    /// Build an admitted set from typed features.
    pub fn try_from_features(
        features: impl IntoIterator<Item = F>,
    ) -> Result<Self, TargetFeatureSetError<F>> {
        TargetFeatureSet::try_from_features(features).map(Self)
    }

    /// Whether production may use `feature`.
    pub fn admits(self, feature: F) -> bool {
        self.0.contains(feature)
    }
}

impl<F: TargetFeature> Default for AdmittedTargetFeatures<F> {
    fn default() -> Self {
        Self::NONE
    }
}

/// Typed optional features derived from actual machine output.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OutputTargetFeatures<F: TargetFeature>(TargetFeatureSet<F>);

impl<F: TargetFeature> OutputTargetFeatures<F> {
    /// Output requiring no optional features.
    pub const NONE: Self = Self(TargetFeatureSet::EMPTY);

    /// Stable output-required feature bits for manifests and diagnostics.
    pub const fn bits(self) -> u64 {
        self.0.bits()
    }

    /// Borrow the role-neutral validated set.
    pub const fn as_set(self) -> TargetFeatureSet<F> {
        self.0
    }

    /// Merge requirements derived from multiple output fragments.
    pub const fn union(self, other: Self) -> Self {
        Self(self.0.union(other.0))
    }
}

impl<F: TargetFeature> OutputTargetFeatures<F> {
    /// Build requirements from a scan of produced machine output.
    pub fn try_from_output(
        features: impl IntoIterator<Item = F>,
    ) -> Result<Self, TargetFeatureSetError<F>> {
        TargetFeatureSet::try_from_features(features).map(Self)
    }

    /// Add one requirement discovered while scanning output.
    pub fn require(self, feature: F) -> Result<Self, TargetFeatureSetError<F>> {
        self.0.with_feature(feature).map(Self)
    }

    /// Whether output requires `feature`.
    pub fn requires(self, feature: F) -> bool {
        self.0.contains(feature)
    }
}

impl<F: TargetFeature> Default for OutputTargetFeatures<F> {
    fn default() -> Self {
        Self::NONE
    }
}

/// Immutable target identity plus its admitted optional machine features.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TargetMachine<I, F: TargetFeature> {
    identity: I,
    admitted: AdmittedTargetFeatures<F>,
}

impl<I: TargetIdentity, F: TargetFeature> TargetMachine<I, F> {
    /// Capture an immutable identity and admitted feature set.
    pub fn try_new(
        identity: I,
        admitted: AdmittedTargetFeatures<F>,
    ) -> Result<Self, TargetMachineError<F>> {
        TargetFeatureSet::<F>::validate_domain().map_err(TargetMachineError::FeatureDomain)?;
        let identity_architecture = identity.architecture();
        if identity_architecture != F::ARCHITECTURE {
            return Err(TargetMachineError::ArchitectureMismatch {
                identity: identity_architecture,
                feature_domain: F::ARCHITECTURE,
            });
        }
        Ok(Self { identity, admitted })
    }

    /// Captured target identity.
    pub const fn identity(&self) -> &I {
        &self.identity
    }

    /// Captured admitted features.
    pub const fn admitted_features(&self) -> AdmittedTargetFeatures<F> {
        self.admitted
    }

    /// Validate that every output-derived requirement was admitted.
    pub fn validate_output_features(
        &self,
        required: OutputTargetFeatures<F>,
    ) -> Result<(), TargetMachineError<F>> {
        let missing = required.as_set().difference(self.admitted.as_set());
        if missing.is_empty() {
            Ok(())
        } else {
            Err(TargetMachineError::MissingOutputFeatures {
                architecture: self.identity.architecture(),
                missing,
            })
        }
    }
}

/// Failure to construct or satisfy a target-machine capability contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TargetMachineError<F: TargetFeature> {
    /// The feature implementation violates its closed-domain contract.
    FeatureDomain(TargetFeatureSetError<F>),
    /// Identity and typed feature domain name different architectures.
    ArchitectureMismatch {
        identity: Target,
        feature_domain: Target,
    },
    /// Produced output requires features not admitted by the machine.
    MissingOutputFeatures {
        architecture: Target,
        missing: TargetFeatureSet<F>,
    },
}

impl<F: TargetFeature> fmt::Display for TargetMachineError<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FeatureDomain(error) => error.fmt(f),
            Self::ArchitectureMismatch {
                identity,
                feature_domain,
            } => write!(
                f,
                "target identity architecture `{}` does not match feature domain `{}`",
                identity.name(),
                feature_domain.name()
            ),
            Self::MissingOutputFeatures {
                architecture,
                missing,
            } => {
                write!(
                    f,
                    "{} output requires unadmitted features",
                    architecture.name()
                )?;
                for feature in (*missing).enabled() {
                    write!(f, " +{}", feature.name())?;
                }
                Ok(())
            }
        }
    }
}

impl<F: TargetFeature> Error for TargetMachineError<F> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    enum Aarch64TestFeature {
        DotProd,
        Fp16,
        Lse,
        Undeclared,
    }

    impl TargetFeature for Aarch64TestFeature {
        const ARCHITECTURE: Target = Target::Aarch64;
        const ALL: &'static [Self] = &[Self::DotProd, Self::Fp16, Self::Lse];

        fn stable_bit(self) -> u64 {
            match self {
                Self::Lse => 1 << 0,
                Self::DotProd => 1 << 1,
                Self::Fp16 => 1 << 2,
                Self::Undeclared => 1 << 3,
            }
        }

        fn name(self) -> &'static str {
            match self {
                Self::DotProd => "dotprod",
                Self::Fp16 => "fp16",
                Self::Lse => "lse",
                Self::Undeclared => "undeclared",
            }
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    enum InvalidFeature {
        First,
        Duplicate,
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    enum DuplicateNameFeature {
        First,
        Alias,
    }

    impl TargetFeature for DuplicateNameFeature {
        const ARCHITECTURE: Target = Target::Aarch64;
        const ALL: &'static [Self] = &[Self::First, Self::Alias];

        fn stable_bit(self) -> u64 {
            match self {
                Self::First => 1,
                Self::Alias => 2,
            }
        }

        fn name(self) -> &'static str {
            "duplicate"
        }
    }

    impl TargetFeature for InvalidFeature {
        const ARCHITECTURE: Target = Target::Aarch64;
        const ALL: &'static [Self] = &[Self::First, Self::Duplicate];

        fn stable_bit(self) -> u64 {
            1
        }

        fn name(self) -> &'static str {
            match self {
                Self::First => "first",
                Self::Duplicate => "duplicate",
            }
        }
    }

    #[derive(Debug, PartialEq, Eq, Hash)]
    struct OwnedIdentity {
        architecture: Target,
        abi: String,
    }

    impl TargetIdentity for OwnedIdentity {
        fn architecture(&self) -> Target {
            self.architecture
        }
    }

    #[test]
    fn output_requirements_must_be_a_subset_of_admitted_features() {
        let admitted = AdmittedTargetFeatures::try_from_features([
            Aarch64TestFeature::Fp16,
            Aarch64TestFeature::Lse,
        ])
        .unwrap();
        let machine = TargetMachine::try_new(Target::Aarch64, admitted).unwrap();

        let fp16_output =
            OutputTargetFeatures::try_from_output([Aarch64TestFeature::Fp16]).unwrap();
        machine.validate_output_features(fp16_output).unwrap();

        let dotprod_output =
            OutputTargetFeatures::try_from_output([Aarch64TestFeature::DotProd]).unwrap();
        let error = machine
            .validate_output_features(dotprod_output)
            .unwrap_err();
        assert!(matches!(
            error,
            TargetMachineError::MissingOutputFeatures { missing, .. }
                if missing.contains(Aarch64TestFeature::DotProd)
                    && !missing.contains(Aarch64TestFeature::Fp16)
        ));
    }

    #[test]
    fn identity_and_typed_feature_domain_must_match() {
        let error = TargetMachine::try_new(
            Target::X86_64,
            AdmittedTargetFeatures::<Aarch64TestFeature>::NONE,
        )
        .unwrap_err();
        assert_eq!(
            error,
            TargetMachineError::ArchitectureMismatch {
                identity: Target::X86_64,
                feature_domain: Target::Aarch64,
            }
        );
    }

    #[test]
    fn target_machine_owns_richer_non_copy_identity() {
        let machine = TargetMachine::try_new(
            OwnedIdentity {
                architecture: Target::Aarch64,
                abi: "aapcs64".to_owned(),
            },
            AdmittedTargetFeatures::<Aarch64TestFeature>::NONE,
        )
        .unwrap();

        assert_eq!(machine.identity().abi, "aapcs64");
    }

    #[test]
    fn output_requirements_union_is_monotone_and_stable() {
        let fp16 = OutputTargetFeatures::try_from_output([Aarch64TestFeature::Fp16]).unwrap();
        let lse = OutputTargetFeatures::try_from_output([Aarch64TestFeature::Lse]).unwrap();
        let combined = fp16.union(lse);
        assert_eq!(combined.bits(), 0b101);
        assert!(combined.requires(Aarch64TestFeature::Fp16));
        assert!(combined.requires(Aarch64TestFeature::Lse));
    }

    #[test]
    fn undeclared_and_aliased_features_fail_closed() {
        assert!(matches!(
            OutputTargetFeatures::try_from_output([Aarch64TestFeature::Undeclared]),
            Err(TargetFeatureSetError::UndeclaredFeature {
                feature: Aarch64TestFeature::Undeclared
            })
        ));
        assert!(matches!(
            AdmittedTargetFeatures::<InvalidFeature>::try_from_features([InvalidFeature::First]),
            Err(TargetFeatureSetError::DuplicateStableBit {
                feature: InvalidFeature::Duplicate,
                bit: 1
            })
        ));
        assert!(matches!(
            AdmittedTargetFeatures::<DuplicateNameFeature>::try_from_features([
                DuplicateNameFeature::First,
            ]),
            Err(TargetFeatureSetError::DuplicateCanonicalName {
                feature: DuplicateNameFeature::Alias,
                name: "duplicate"
            })
        ));
    }

    #[test]
    fn shared_target_metadata_preserves_existing_values() {
        assert_eq!(Target::X86_64.pointer_bytes(), 8);
        assert_eq!(Target::Aarch64.stack_alignment(), 16);
        assert_eq!(Target::Riscv64.num_arg_gprs(), 8);
        assert_eq!(Target::Aarch64.calling_convention().name, "aapcs64");
    }
}
