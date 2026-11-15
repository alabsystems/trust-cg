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
    /// Returns the pointer size in bits for this target.
    pub fn pointer_bits(self) -> u16 {
        match self {
            Self::X86_64 | Self::Aarch64 | Self::Riscv64 => 64,
        }
    }

    /// Returns the pointer size in bytes for this target.
    pub fn pointer_bytes(self) -> u32 {
        u32::from(self.pointer_bits()) / 8
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

    /// Returns the target architecture selected when compiling this process,
    /// when that architecture is represented by [`Target`].
    ///
    /// Unlike [`Self::host`], this function never guesses. Authority-bearing
    /// host pipelines should use this API and fail closed on `None`.
    #[must_use]
    pub fn try_host() -> Option<Self> {
        #[cfg(target_arch = "x86_64")]
        {
            Some(Self::X86_64)
        }
        #[cfg(target_arch = "aarch64")]
        {
            Some(Self::Aarch64)
        }
        #[cfg(target_arch = "riscv64")]
        {
            Some(Self::Riscv64)
        }
        #[cfg(not(any(
            target_arch = "x86_64",
            target_arch = "aarch64",
            target_arch = "riscv64",
        )))]
        {
            None
        }
    }

    /// Returns the target architecture of the host process.
    ///
    /// Unknown host architectures retain Trust Codegen's historical AArch64
    /// fallback. This compatibility API is not authority for host execution;
    /// authority-bearing paths must use [`Self::try_host`] and reject `None`.
    #[must_use]
    pub fn host() -> Self {
        Self::try_host().unwrap_or(Self::Aarch64)
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

/// Optional AArch64 capabilities with stable persistent-identity bits.
///
/// The closed domain lives beside its validated set representation so typed
/// profile construction does not need a runtime domain-validation assertion.
/// Append features without renumbering the existing discriminants.
///
/// Names are rustc's AArch64 `target_feature` spellings (the strings a
/// producer states in trust-ir `FuncAttrs.target_features`). Each feature
/// names the Arm architecture feature(s) it stands for and the Darwin
/// `hw.optional.arm.*` sysctl key(s) whose conjunction reports it
/// ([`Self::darwin_sysctl_keys`]); the host truth on the qualifying Apple M4
/// Max is recorded in `docs/darwin-aarch64-completion.md`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum AArch64IsaFeature {
    /// FEAT_DotProd vector dot-product instructions.
    DotProd = 1,
    /// FEAT_FP16 scalar half-precision data-processing instructions.
    Fp16 = 2,
    /// FEAT_LSE atomic read-modify-write instructions.
    Lse = 0,
    /// FEAT_LSE2 atomicity rules: an aligned `LDP`/`STP` pair is SINGLE-COPY
    /// ATOMIC, which is what makes a 128-bit atomic load expressible as one
    /// paired access rather than an LL/SC retry loop.
    ///
    /// Distinct from [`Self::Lse`] (ARMv8.1-A read-modify-write instructions);
    /// this is the ARMv8.4-A atomicity guarantee, and a target may have one
    /// without the other. Appended rather than renumbered, per this enum's
    /// contract.
    Lse2 = 3,
    /// FEAT_AES and FEAT_PMULL (rustc's `aes` enables both): `AESE`/`AESD`/
    /// `AESMC`/`AESIMC` and 64-bit polynomial `PMULL`.
    Aes = 4,
    /// FEAT_BF16 BFloat16 conversion and dot-product instructions.
    Bf16 = 5,
    /// FEAT_CRC32 `CRC32{B,H,W,X}` / `CRC32C{B,H,W,X}` checksum instructions.
    Crc = 6,
    /// FEAT_DIT data-independent-timing `PSTATE.DIT` control.
    Dit = 7,
    /// FEAT_DPB `DC CVAP` (clean to the point of persistence).
    Dpb = 8,
    /// FEAT_DPB2 `DC CVADP` (clean to the point of deep persistence).
    Dpb2 = 9,
    /// FEAT_FCMA complex-number `FCMLA`/`FCADD`.
    Fcma = 10,
    /// FEAT_FHM half-precision `FMLAL`/`FMLSL` widening multiply-accumulate.
    Fhm = 11,
    /// FEAT_FlagM condition-flag manipulation (`CFINV`, `RMIF`, `SETF8/16`).
    FlagM = 12,
    /// FEAT_FlagM2 `AXFLAG`/`XAFLAG`.
    FlagM2 = 13,
    /// FEAT_FRINTTS `FRINT32Z`/`FRINT32X`/`FRINT64Z`/`FRINT64X`.
    Frintts = 14,
    /// FEAT_I8MM int8 matrix multiply (`SMMLA`, `UMMLA`, `USMMLA`, `USDOT`).
    I8mm = 15,
    /// FEAT_JSCVT `FJCVTZS` JavaScript conversion.
    Jsconv = 16,
    /// FEAT_LRCPC load-acquire RCpc `LDAPR`.
    Rcpc = 17,
    /// FEAT_LRCPC2 unscaled-offset `LDAPUR`/`STLUR`.
    Rcpc2 = 18,
    /// FEAT_RDM rounding doubling multiply-accumulate `SQRDMLAH`/`SQRDMLSH`.
    Rdm = 19,
    /// FEAT_SB speculation barrier `SB`.
    Sb = 20,
    /// FEAT_SHA1 and FEAT_SHA256 (rustc's `sha2` enables both).
    Sha2 = 21,
    /// FEAT_SHA3 and FEAT_SHA512 (rustc's `sha3` enables both).
    Sha3 = 22,
}

impl AArch64IsaFeature {
    /// Complete feature domain in canonical lexical-name order.
    pub const ALL: [Self; 23] = [
        Self::Aes,
        Self::Bf16,
        Self::Crc,
        Self::Dit,
        Self::DotProd,
        Self::Dpb,
        Self::Dpb2,
        Self::Fcma,
        Self::Fhm,
        Self::FlagM,
        Self::FlagM2,
        Self::Fp16,
        Self::Frintts,
        Self::I8mm,
        Self::Jsconv,
        Self::Lse,
        Self::Lse2,
        Self::Rcpc,
        Self::Rcpc2,
        Self::Rdm,
        Self::Sb,
        Self::Sha2,
        Self::Sha3,
    ];

    /// Stable feature name used by manifests and artifact identities.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Aes => "aes",
            Self::Bf16 => "bf16",
            Self::Crc => "crc",
            Self::Dit => "dit",
            Self::DotProd => "dotprod",
            Self::Dpb => "dpb",
            Self::Dpb2 => "dpb2",
            Self::Fcma => "fcma",
            Self::Fhm => "fhm",
            Self::FlagM => "flagm",
            Self::FlagM2 => "flagm2",
            Self::Fp16 => "fp16",
            Self::Frintts => "frintts",
            Self::I8mm => "i8mm",
            Self::Jsconv => "jsconv",
            Self::Lse => "lse",
            Self::Lse2 => "lse2",
            Self::Rcpc => "rcpc",
            Self::Rcpc2 => "rcpc2",
            Self::Rdm => "rdm",
            Self::Sb => "sb",
            Self::Sha2 => "sha2",
            Self::Sha3 => "sha3",
        }
    }

    /// The feature spelled exactly `name`, if this closed domain models it.
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|feature| feature.name() == name)
    }

    /// Darwin `sysctl` keys whose conjunction reports this feature on the
    /// running CPU (each reads `1` when the architecture feature is
    /// implemented). A feature that bundles two architecture features, like
    /// rustc's `aes` (FEAT_AES + FEAT_PMULL), lists both.
    pub const fn darwin_sysctl_keys(self) -> &'static [&'static str] {
        match self {
            Self::Aes => &["hw.optional.arm.FEAT_AES", "hw.optional.arm.FEAT_PMULL"],
            Self::Bf16 => &["hw.optional.arm.FEAT_BF16"],
            Self::Crc => &["hw.optional.arm.FEAT_CRC32"],
            Self::Dit => &["hw.optional.arm.FEAT_DIT"],
            Self::DotProd => &["hw.optional.arm.FEAT_DotProd"],
            Self::Dpb => &["hw.optional.arm.FEAT_DPB"],
            Self::Dpb2 => &["hw.optional.arm.FEAT_DPB2"],
            Self::Fcma => &["hw.optional.arm.FEAT_FCMA"],
            Self::Fhm => &["hw.optional.arm.FEAT_FHM"],
            Self::FlagM => &["hw.optional.arm.FEAT_FlagM"],
            Self::FlagM2 => &["hw.optional.arm.FEAT_FlagM2"],
            Self::Fp16 => &["hw.optional.arm.FEAT_FP16"],
            Self::Frintts => &["hw.optional.arm.FEAT_FRINTTS"],
            Self::I8mm => &["hw.optional.arm.FEAT_I8MM"],
            Self::Jsconv => &["hw.optional.arm.FEAT_JSCVT"],
            Self::Lse => &["hw.optional.arm.FEAT_LSE"],
            Self::Lse2 => &["hw.optional.arm.FEAT_LSE2"],
            Self::Rcpc => &["hw.optional.arm.FEAT_LRCPC"],
            Self::Rcpc2 => &["hw.optional.arm.FEAT_LRCPC2"],
            Self::Rdm => &["hw.optional.arm.FEAT_RDM"],
            Self::Sb => &["hw.optional.arm.FEAT_SB"],
            Self::Sha2 => &["hw.optional.arm.FEAT_SHA1", "hw.optional.arm.FEAT_SHA256"],
            Self::Sha3 => &["hw.optional.arm.FEAT_SHA3", "hw.optional.arm.FEAT_SHA512"],
        }
    }

    /// Stable single-bit identity, shared with compatibility profiles.
    pub const fn mask(self) -> u32 {
        1_u32 << (self as u8)
    }
}

/// Target-feature names every AArch64 body may assume (the AAPCS64 hard-float
/// baseline): a function stating them adds nothing to its admission.
pub const AARCH64_BASELINE_TARGET_FEATURES: [&str; 2] = ["neon", "fp-armv8"];

/// Every AArch64 target-feature name this backend models: the baseline names
/// followed by [`AArch64IsaFeature::ALL`] in canonical order. A function's
/// stated feature outside this list is refused by name.
pub const AARCH64_KNOWN_TARGET_FEATURES: [&str; 2 + AArch64IsaFeature::ALL.len()] = {
    let mut names = [""; 2 + AArch64IsaFeature::ALL.len()];
    names[0] = AARCH64_BASELINE_TARGET_FEATURES[0];
    names[1] = AARCH64_BASELINE_TARGET_FEATURES[1];
    let mut index = 0;
    while index < AArch64IsaFeature::ALL.len() {
        names[2 + index] = AArch64IsaFeature::ALL[index].name();
        index += 1;
    }
    names
};

/// The optional AArch64 features a function states (trust-ir
/// `FuncAttrs.target_features`, rustc spellings). Baseline names contribute
/// nothing; the first name outside [`AARCH64_KNOWN_TARGET_FEATURES`] is
/// returned as the error, so a caller refuses it by name.
///
/// No implication closure is applied: rustc states the closed set it
/// enables (`sha3` arrives with `sha2`), and a body that relies on a feature
/// it did not state fails closed at the output-feature check.
pub fn aarch64_function_target_features<'a>(
    names: impl IntoIterator<Item = &'a str>,
) -> Result<TargetFeatureSet<AArch64IsaFeature>, &'a str> {
    let mut features = Vec::new();
    for name in names {
        if AARCH64_BASELINE_TARGET_FEATURES.contains(&name) {
            continue;
        }
        features.push(AArch64IsaFeature::from_name(name).ok_or(name)?);
    }
    Ok(TargetFeatureSet::from_aarch64_features(features))
}

impl TargetFeature for AArch64IsaFeature {
    const ARCHITECTURE: Target = Target::Aarch64;
    const ALL: &'static [Self] = &Self::ALL;

    fn stable_bit(self) -> u64 {
        u64::from(self.mask())
    }

    fn name(self) -> &'static str {
        Self::name(self)
    }
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

impl TargetFeatureSet<AArch64IsaFeature> {
    /// A set over the built-in closed AArch64 domain. Infallible: that
    /// domain's names and bits are exhaustive and distinct by construction
    /// (checked by this module's tests), unlike an arbitrary external domain.
    pub fn from_aarch64_features(features: impl IntoIterator<Item = AArch64IsaFeature>) -> Self {
        let mut set = Self::EMPTY;
        for feature in features {
            set.bits |= u64::from(feature.mask());
        }
        set
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

impl AdmittedTargetFeatures<AArch64IsaFeature> {
    /// Admit one member of the built-in closed AArch64 feature domain.
    ///
    /// Unlike an arbitrary external [`TargetFeature`] implementation, this
    /// domain has exhaustive names and distinct enum-discriminant bits defined
    /// in this module. The API accepts neither raw bits nor unchecked domains.
    pub const fn with_aarch64_feature(mut self, feature: AArch64IsaFeature) -> Self {
        self.0.bits |= feature.mask() as u64;
        self
    }

    /// Every member of the closed AArch64 feature domain.
    pub const ALL_AARCH64: Self = {
        let mut admitted = Self::NONE;
        let mut index = 0;
        while index < AArch64IsaFeature::ALL.len() {
            admitted = admitted.with_aarch64_feature(AArch64IsaFeature::ALL[index]);
            index += 1;
        }
        admitted
    };
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
///
/// `admitted` is the target profile: the features every function compiled for
/// this machine may assume. A function's own source attribute (trust-ir
/// `FuncAttrs.target_features`, rustc's `#[target_feature(enable = ...)]`)
/// may add features for THAT function alone, and only within
/// `function_ceiling`, the features this target identity can have at all;
/// [`Self::for_function`] derives the function's machine. The caller of such a
/// function guarantees the features at run time (runtime dispatch), exactly
/// as the producer's language does; nothing here observes the executing CPU.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TargetMachine<I, F: TargetFeature> {
    identity: I,
    admitted: AdmittedTargetFeatures<F>,
    function_ceiling: AdmittedTargetFeatures<F>,
}

impl<I: TargetIdentity, F: TargetFeature> TargetMachine<I, F> {
    /// Capture an immutable identity and admitted feature set. No function
    /// may add a feature beyond `admitted` (its ceiling is `admitted`).
    pub fn try_new(
        identity: I,
        admitted: AdmittedTargetFeatures<F>,
    ) -> Result<Self, TargetMachineError<F>> {
        Self::try_new_with_function_ceiling(identity, admitted, admitted)
    }

    /// Capture an identity, its profile, and the ceiling that per-function
    /// target features may reach. The profile must lie within the ceiling.
    pub fn try_new_with_function_ceiling(
        identity: I,
        admitted: AdmittedTargetFeatures<F>,
        function_ceiling: AdmittedTargetFeatures<F>,
    ) -> Result<Self, TargetMachineError<F>> {
        TargetFeatureSet::<F>::validate_domain().map_err(TargetMachineError::FeatureDomain)?;
        let identity_architecture = identity.architecture();
        if identity_architecture != F::ARCHITECTURE {
            return Err(TargetMachineError::ArchitectureMismatch {
                identity: identity_architecture,
                feature_domain: F::ARCHITECTURE,
            });
        }
        let missing = admitted.as_set().difference(function_ceiling.as_set());
        if !missing.is_empty() {
            return Err(TargetMachineError::ProfileOutsideFunctionCeiling {
                architecture: identity_architecture,
                missing,
            });
        }
        Ok(Self {
            identity,
            admitted,
            function_ceiling,
        })
    }

    /// Captured target identity.
    pub const fn identity(&self) -> &I {
        &self.identity
    }

    /// Captured admitted features.
    pub const fn admitted_features(&self) -> AdmittedTargetFeatures<F> {
        self.admitted
    }

    /// Features a per-function target-feature attribute may add to
    /// [`Self::admitted_features`] for that function.
    pub const fn function_ceiling(&self) -> AdmittedTargetFeatures<F> {
        self.function_ceiling
    }

    /// The part of `admitted` a function adds beyond this machine's profile,
    /// provided the whole set lies within the function ceiling and includes
    /// the profile. This is how an evidence or install layer recovers a
    /// function's own features from its recorded admission.
    pub fn function_extension_of(
        &self,
        admitted: AdmittedTargetFeatures<F>,
    ) -> Option<TargetFeatureSet<F>> {
        let profile = self.admitted.as_set();
        let set = admitted.as_set();
        (profile.is_subset_of(set)
            && set.is_subset_of(profile.union(self.function_ceiling.as_set())))
        .then(|| set.difference(profile))
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

impl<I: TargetIdentity + Clone, F: TargetFeature> TargetMachine<I, F> {
    /// The machine one function compiles under: this identity and ceiling,
    /// admitting the profile plus the function's own `function_features`.
    ///
    /// A feature outside the function ceiling is refused
    /// ([`TargetMachineError::FunctionFeaturesOutsideCeiling`]); an empty set
    /// returns an identical machine, so a function without target-feature
    /// attributes compiles exactly as the profile says.
    pub fn for_function(
        &self,
        function_features: TargetFeatureSet<F>,
    ) -> Result<Self, TargetMachineError<F>> {
        let missing = function_features.difference(self.function_ceiling.as_set());
        if !missing.is_empty() {
            return Err(TargetMachineError::FunctionFeaturesOutsideCeiling {
                architecture: self.identity.architecture(),
                missing,
            });
        }
        Ok(Self {
            identity: self.identity.clone(),
            admitted: AdmittedTargetFeatures(self.admitted.as_set().union(function_features)),
            function_ceiling: self.function_ceiling,
        })
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
    /// The target profile admits features its own function ceiling excludes.
    ProfileOutsideFunctionCeiling {
        architecture: Target,
        missing: TargetFeatureSet<F>,
    },
    /// A function's own target-feature attribute names features this target
    /// cannot have (outside its function ceiling).
    FunctionFeaturesOutsideCeiling {
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
            Self::ProfileOutsideFunctionCeiling {
                architecture,
                missing,
            } => {
                write!(
                    f,
                    "{} profile admits features outside its function ceiling",
                    architecture.name()
                )?;
                for feature in (*missing).enabled() {
                    write!(f, " +{}", feature.name())?;
                }
                Ok(())
            }
            Self::FunctionFeaturesOutsideCeiling {
                architecture,
                missing,
            } => {
                write!(
                    f,
                    "function target features are outside the {} target's function ceiling:",
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

    #[cfg(any(
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "riscv64"
    ))]
    #[test]
    fn supported_build_host_is_detected_without_fallback() {
        let detected = Target::try_host().expect("cfg-supported host must have an exact target");
        assert_eq!(Target::host(), detected);

        #[cfg(target_arch = "x86_64")]
        assert_eq!(detected, Target::X86_64);
        #[cfg(target_arch = "aarch64")]
        assert_eq!(detected, Target::Aarch64);
        #[cfg(target_arch = "riscv64")]
        assert_eq!(detected, Target::Riscv64);
    }

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
        for target in [Target::X86_64, Target::Aarch64, Target::Riscv64] {
            assert_eq!(target.pointer_bits(), 64);
            assert_eq!(target.pointer_bytes(), 8);
            assert_eq!(u32::from(target.pointer_bits()), target.pointer_bytes() * 8);
        }
        assert_eq!(Target::Aarch64.stack_alignment(), 16);
        assert_eq!(Target::Riscv64.num_arg_gprs(), 8);
        assert_eq!(Target::Aarch64.calling_convention().name, "aapcs64");
    }

    /// The closed AArch64 domain: canonical lexical order, unique names and
    /// bits, the four original features keep their persistent bits, names
    /// round-trip, and every feature names at least one Darwin sysctl key.
    #[test]
    fn aarch64_feature_domain_is_ordered_unique_and_stable() {
        let names: Vec<_> = AArch64IsaFeature::ALL.map(AArch64IsaFeature::name).to_vec();
        let mut sorted = names.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(names, sorted, "ALL must be in strict lexical-name order");
        assert_eq!(AArch64IsaFeature::ALL.len(), 23);
        let mut seen = 0_u32;
        for feature in AArch64IsaFeature::ALL {
            assert_eq!(seen & feature.mask(), 0, "{feature:?} reuses a bit");
            seen |= feature.mask();
            assert_eq!(AArch64IsaFeature::from_name(feature.name()), Some(feature));
            let keys = feature.darwin_sysctl_keys();
            assert!(!keys.is_empty(), "{feature:?}");
            assert!(
                keys.iter()
                    .all(|key| key.starts_with("hw.optional.arm.FEAT_")),
                "{feature:?}: {keys:?}"
            );
        }
        assert_eq!(seen, (1 << 23) - 1, "bits are dense 0..23");
        assert_eq!(AArch64IsaFeature::Lse.mask(), 1);
        assert_eq!(AArch64IsaFeature::DotProd.mask(), 2);
        assert_eq!(AArch64IsaFeature::Fp16.mask(), 4);
        assert_eq!(AArch64IsaFeature::Lse2.mask(), 8);
        assert_eq!(AdmittedTargetFeatures::ALL_AARCH64.bits(), u64::from(seen));
        for unmodeled in [
            "neon", "fp-armv8", "sve", "sve2", "bti", "paca", "CRC", "crc32",
        ] {
            assert_eq!(AArch64IsaFeature::from_name(unmodeled), None, "{unmodeled}");
        }
        assert_eq!(AARCH64_KNOWN_TARGET_FEATURES.len(), 25);
        assert_eq!(
            AARCH64_KNOWN_TARGET_FEATURES[..2],
            AARCH64_BASELINE_TARGET_FEATURES
        );
        assert_eq!(
            AARCH64_KNOWN_TARGET_FEATURES[2..],
            AArch64IsaFeature::ALL.map(AArch64IsaFeature::name)
        );
    }

    /// Stated features parse to exactly the modeled optional set; baseline
    /// names add nothing; the first unmodeled name is the error.
    #[test]
    fn function_target_features_parse_exactly_and_refuse_by_name() {
        assert_eq!(
            aarch64_function_target_features(["neon", "fp-armv8"]),
            Ok(TargetFeatureSet::EMPTY)
        );
        let set = aarch64_function_target_features(["neon", "crc", "lse", "crc"]).unwrap();
        assert_eq!(
            set.enabled().collect::<Vec<_>>(),
            [AArch64IsaFeature::Crc, AArch64IsaFeature::Lse]
        );
        assert_eq!(
            aarch64_function_target_features(["crc", "sve2", "bti"]),
            Err("sve2")
        );
        assert_eq!(
            aarch64_function_target_features(["avx512f"]),
            Err("avx512f")
        );
        assert_eq!(aarch64_function_target_features(["+crc"]), Err("+crc"));
    }

    /// A function may add features only within the ceiling; an empty
    /// extension is the identical machine; the profile must lie within the
    /// ceiling; and an evidence layer recovers a function's extension exactly.
    #[test]
    fn function_features_extend_the_profile_only_within_the_ceiling() {
        let profile =
            AdmittedTargetFeatures::try_from_features([Aarch64TestFeature::Fp16]).unwrap();
        let ceiling = AdmittedTargetFeatures::try_from_features([
            Aarch64TestFeature::Fp16,
            Aarch64TestFeature::Lse,
        ])
        .unwrap();
        let machine =
            TargetMachine::try_new_with_function_ceiling(Target::Aarch64, profile, ceiling)
                .unwrap();
        assert_eq!(machine.function_ceiling(), ceiling);
        assert_eq!(
            machine.for_function(TargetFeatureSet::EMPTY).unwrap(),
            machine
        );

        let lse = TargetFeatureSet::try_from_features([Aarch64TestFeature::Lse]).unwrap();
        let function = machine.for_function(lse).unwrap();
        assert!(function.admitted_features().admits(Aarch64TestFeature::Lse));
        assert!(
            function
                .admitted_features()
                .admits(Aarch64TestFeature::Fp16)
        );
        assert_eq!(function.function_ceiling(), ceiling);
        assert_eq!(
            machine.function_extension_of(function.admitted_features()),
            Some(lse)
        );
        assert_eq!(
            machine.function_extension_of(machine.admitted_features()),
            Some(TargetFeatureSet::EMPTY)
        );
        // Output that needs LSE fails on the profile and passes on the
        // function's own machine.
        let lse_output = OutputTargetFeatures::try_from_output([Aarch64TestFeature::Lse]).unwrap();
        assert!(machine.validate_output_features(lse_output).is_err());
        function.validate_output_features(lse_output).unwrap();

        let dotprod = TargetFeatureSet::try_from_features([Aarch64TestFeature::DotProd]).unwrap();
        assert!(matches!(
            machine.for_function(dotprod),
            Err(TargetMachineError::FunctionFeaturesOutsideCeiling { missing, .. })
                if missing == dotprod
        ));
        let beyond = AdmittedTargetFeatures::try_from_features([
            Aarch64TestFeature::Fp16,
            Aarch64TestFeature::DotProd,
        ])
        .unwrap();
        assert_eq!(machine.function_extension_of(beyond), None);
        assert_eq!(
            machine.function_extension_of(AdmittedTargetFeatures::NONE),
            None,
            "an admission that drops the profile is not a function extension"
        );
        assert!(matches!(
            TargetMachine::try_new_with_function_ceiling(Target::Aarch64, ceiling, profile),
            Err(TargetMachineError::ProfileOutsideFunctionCeiling { .. })
        ));
        // `try_new` keeps the historical contract: no function extension.
        let closed = TargetMachine::try_new(Target::Aarch64, profile).unwrap();
        assert!(closed.for_function(lse).is_err());
    }

    #[test]
    fn built_in_aarch64_admission_matches_checked_domain_for_every_subset() {
        for bits in 0..8 {
            let features = AArch64IsaFeature::ALL
                .into_iter()
                .filter(|feature| bits & feature.mask() != 0);
            let admitted = features.clone().fold(
                AdmittedTargetFeatures::NONE,
                AdmittedTargetFeatures::with_aarch64_feature,
            );
            assert_eq!(admitted.bits(), u64::from(bits));
            assert_eq!(
                admitted,
                AdmittedTargetFeatures::try_from_features(features).unwrap()
            );
        }
    }
}
