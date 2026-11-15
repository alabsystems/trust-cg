// trust-cg-codegen/target.rs - Target architectures and target-generic info
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Target architecture definitions with per-target register info and calling conventions.
//!
//! This module provides a unified [`Target`] enum and per-target accessors for
//! register allocation constraints, calling convention details, and stack layout
//! parameters. The design is extensible: adding a new target requires adding an
//! enum variant and implementing the per-target methods.

use std::{error::Error, fmt, str::FromStr};

use crate::apple_deployment::{
    AppleDeploymentTargetError, AppleDeploymentTargetSource, AppleOsVersion, MachOBuildVersion,
};

pub use trust_cg_ir::{
    AArch64IsaFeature, AdmittedTargetFeatures, CallingConvention, OutputTargetFeatures, Target,
    TargetFeature, TargetFeatureSet, TargetFeatureSetError, TargetIdentity, TargetMachine,
    TargetMachineError,
};

/// Optional RISC-V instruction-set capabilities understood by codegen today.
///
/// The current backend exposes no optional RISC-V admission knobs, so its
/// closed feature domain is empty. Keeping that as a typed domain lets all
/// supported register-machine targets use [`TargetMachine`] without borrowing
/// another architecture's feature type; future capabilities can be appended
/// with stable bits as their lowering and output scans land.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RiscVIsaFeature {}

impl TargetFeature for RiscVIsaFeature {
    const ARCHITECTURE: Target = Target::Riscv64;
    const ALL: &'static [Self] = &[];

    fn stable_bit(self) -> u64 {
        match self {}
    }

    fn name(self) -> &'static str {
        match self {}
    }
}

/// Resolved AArch64 instruction-set profile used by machine-code lowering.
///
/// This is intentionally separate from [`TargetSpec`]: a target triple names
/// an ABI and object format, but does not prove that the execution CPU supports
/// optional ISA extensions. A bitset avoids the combinatorial enum growth that
/// otherwise occurs as independent capabilities are added. Any persistent
/// machine-code identity must bind [`Self::feature_bits`] (and its schema), not
/// re-derive features from the host later.
#[derive(Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AArch64IsaProfile {
    feature_bits: u32,
}

impl AArch64IsaProfile {
    /// Generic AArch64: no optional instruction family is admitted.
    pub const BASELINE: Self = Self { feature_bits: 0 };
    /// Profile admitting only FEAT_LSE.
    pub const LSE: Self = Self::BASELINE.with_feature(AArch64IsaFeature::Lse, true);
    /// Profile admitting only FEAT_DotProd.
    pub const DOTPROD: Self = Self::BASELINE.with_feature(AArch64IsaFeature::DotProd, true);
    /// Profile admitting only FEAT_FP16.
    pub const FP16: Self = Self::BASELINE.with_feature(AArch64IsaFeature::Fp16, true);
    /// Profile admitting LSE and DotProd, but not FP16.
    pub const LSE_DOTPROD: Self = Self::LSE.with_feature(AArch64IsaFeature::DotProd, true);
    /// Capabilities guaranteed by Trust Codegen's Apple arm64 target contract.
    ///
    /// Includes FEAT_LSE2 (ARMv8.4-A atomicity rules): every Apple arm64 part
    /// this target contract covers is ARMv8.4-A or later — rustc reports
    /// `target_feature="lse2"` and `v8.4a` for `aarch64-apple-darwin`, whose
    /// spec sets `cpu: "apple-m1"`. That guarantee is what lets an aligned
    /// 128-bit atomic load lower to ONE paired access.
    ///
    /// NOTE — this ADMISSION MOVES THIS PROFILE'S IDENTITY: `feature_bits`
    /// 7 -> 15 and `canonical_name` gains `+lse2`. `feature_bits` is bound into
    /// cache and provenance identity, so artifacts recorded under the old
    /// identity are distinct from new ones. The pinned assertions in this file's
    /// tests exist to make exactly that visible, and are updated with it.
    pub const APPLE_ARM64: Self = Self::LSE_DOTPROD
        .with_feature(AArch64IsaFeature::Fp16, true)
        .with_feature(AArch64IsaFeature::Lse2, true);

    /// Return a copy with one optional capability admitted or removed.
    pub const fn with_feature(mut self, feature: AArch64IsaFeature, enabled: bool) -> Self {
        if enabled {
            self.feature_bits |= feature.mask();
        } else {
            self.feature_bits &= !feature.mask();
        }
        self
    }

    /// Stable artifact-identity bits. The surrounding identity must also bind
    /// its own schema version so future semantic changes cannot alias v1.
    pub const fn feature_bits(self) -> u32 {
        self.feature_bits
    }

    /// Whether this profile authorizes one optional instruction family.
    pub const fn permits(self, feature: AArch64IsaFeature) -> bool {
        self.feature_bits & feature.mask() != 0
    }

    /// Whether this profile authorizes emitting LSE instructions.
    pub const fn permits_lse(self) -> bool {
        self.permits(AArch64IsaFeature::Lse)
    }

    /// Whether this profile authorizes the FEAT_LSE2 atomicity rules — i.e.
    /// whether an ALIGNED `LDP`/`STP` may be relied on as SINGLE-COPY ATOMIC.
    ///
    /// Distinct from [`Self::permits_lse`]: that is the ARMv8.1-A RMW
    /// instruction set, this is the ARMv8.4-A atomicity guarantee.
    pub const fn permits_lse2(self) -> bool {
        self.permits(AArch64IsaFeature::Lse2)
    }

    /// Whether this profile authorizes FEAT_DotProd instructions.
    pub const fn permits_dotprod(self) -> bool {
        self.permits(AArch64IsaFeature::DotProd)
    }

    /// Whether this profile authorizes FEAT_FP16 scalar data processing.
    pub const fn permits_fp16(self) -> bool {
        self.permits(AArch64IsaFeature::Fp16)
    }

    /// Canonical enabled-feature names for manifests and diagnostic surfaces.
    /// The iterator is allocation-free and follows [`AArch64IsaFeature::ALL`].
    pub fn enabled_feature_names(self) -> impl Iterator<Item = &'static str> {
        AArch64IsaFeature::ALL
            .into_iter()
            .filter(move |feature| self.permits(*feature))
            .map(AArch64IsaFeature::name)
    }

    /// Convert this compatibility profile into the shared typed admission set.
    pub fn admitted_target_features(self) -> AdmittedTargetFeatures<AArch64IsaFeature> {
        AArch64IsaFeature::ALL
            .into_iter()
            .filter(move |feature| self.permits(*feature))
            .fold(
                AdmittedTargetFeatures::NONE,
                AdmittedTargetFeatures::with_aarch64_feature,
            )
    }

    /// Reconstruct the compatibility profile from shared typed admission.
    pub const fn from_admitted_target_features(
        admitted: AdmittedTargetFeatures<AArch64IsaFeature>,
    ) -> Self {
        // AArch64IsaFeature's stable bits are defined by this compatibility
        // profile's u32 mask and typed admission has already validated them.
        Self {
            feature_bits: admitted.bits() as u32,
        }
    }

    /// Stable human-readable identity used in diagnostics and certificates.
    pub fn canonical_name(self) -> String {
        let mut name = String::from("aarch64-isa-v1");
        for feature in self.enabled_feature_names() {
            name.push('+');
            name.push_str(feature);
        }
        name
    }

    /// Resolve the in-process JIT profile from the current host once.
    ///
    /// The result is suitable for capture in a compile request and artifact
    /// identity. It never assumes that every AArch64 CPU has LSE.
    pub fn for_host_jit() -> Self {
        resolve_aarch64_host_jit_profile(
            cfg!(target_arch = "aarch64"),
            host_has_aarch64_lse(),
            host_has_aarch64_dotprod(),
            host_has_aarch64_fp16(),
            host_has_aarch64_lse2(),
        )
    }

    /// Resolve the ISA profile guaranteed by an AOT target specification.
    ///
    /// Apple's arm64 Darwin deployment contract includes LSE, DotProd, and
    /// scalar FP16; generic Linux and unknown AArch64 targets do not. A future
    /// explicit target-feature API can admit any subset without weakening this
    /// conservative default.
    pub const fn for_aot_target(target: TargetSpec) -> Self {
        if matches!(target.architecture, Target::Aarch64)
            && matches!(target.vendor, TargetVendor::Apple)
            && matches!(target.operating_system, TargetOperatingSystem::Darwin)
        {
            Self::APPLE_ARM64
        } else {
            Self::BASELINE
        }
    }

    /// Whether the current process can execute code requiring this profile:
    /// every admitted feature is one the executing CPU implements
    /// ([`crate::aarch64_dispatch::aarch64_host_features`]).
    pub fn is_supported_by_host(self) -> bool {
        cfg!(target_arch = "aarch64")
            && crate::aarch64_dispatch::aarch64_host_features()
                .implements_all(self.admitted_target_features().as_set())
    }

    /// The features a function's own target-feature attribute may add to the
    /// profile of `target`: every modeled feature for an AArch64 identity,
    /// nothing for another architecture.
    ///
    /// A per-function feature is the producer's run-time contract (the caller
    /// dispatches on the executing CPU, as rustc's `#[target_feature]`
    /// requires), so the ceiling is what the architecture can have, not what a
    /// deployment guarantees. An in-process JIT additionally refuses, at
    /// install, a function whose features the executing CPU lacks.
    pub const fn function_feature_ceiling(
        target: TargetSpec,
    ) -> AdmittedTargetFeatures<AArch64IsaFeature> {
        if matches!(target.architecture, Target::Aarch64) {
            AdmittedTargetFeatures::ALL_AARCH64
        } else {
            AdmittedTargetFeatures::NONE
        }
    }
}

impl From<AArch64IsaProfile> for AdmittedTargetFeatures<AArch64IsaFeature> {
    fn from(profile: AArch64IsaProfile) -> Self {
        profile.admitted_target_features()
    }
}

impl From<AdmittedTargetFeatures<AArch64IsaFeature>> for AArch64IsaProfile {
    fn from(admitted: AdmittedTargetFeatures<AArch64IsaFeature>) -> Self {
        Self::from_admitted_target_features(admitted)
    }
}

impl fmt::Debug for AArch64IsaProfile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("AArch64IsaProfile")
            .field(&self.canonical_name())
            .finish()
    }
}

impl fmt::Display for AArch64IsaProfile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.canonical_name())
    }
}

/// Why an explicit AArch64 feature list did not name a profile.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AArch64IsaProfileParseError {
    /// A list entry names no [`AArch64IsaFeature`].
    UnknownFeature(String),
    /// A feature appears twice.
    DuplicateFeature(&'static str),
    /// The list has an empty entry (`"fp16,,lse"`, or an empty string, which
    /// must be spelled `none`).
    EmptyEntry,
}

impl fmt::Display for AArch64IsaProfileParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let known = AArch64IsaFeature::ALL
            .map(AArch64IsaFeature::name)
            .join(", ");
        match self {
            Self::UnknownFeature(name) => write!(
                f,
                "unknown AArch64 ISA feature `{name}` (known: {known}; `none` for the baseline)"
            ),
            Self::DuplicateFeature(name) => {
                write!(f, "AArch64 ISA feature `{name}` is listed twice")
            }
            Self::EmptyEntry => write!(
                f,
                "empty AArch64 ISA feature entry (spell the baseline profile `none`)"
            ),
        }
    }
}

impl Error for AArch64IsaProfileParseError {}

impl FromStr for AArch64IsaProfile {
    type Err = AArch64IsaProfileParseError;

    /// Parse an explicit profile as a comma-separated list of exactly the
    /// admitted feature names (`fp16`, `lse,dotprod`), or `none` for the
    /// baseline. The list is the whole admission, never added to a target
    /// contract.
    fn from_str(list: &str) -> Result<Self, Self::Err> {
        if list == "none" {
            return Ok(Self::BASELINE);
        }
        let mut profile = Self::BASELINE;
        for entry in list.split(',') {
            if entry.is_empty() {
                return Err(AArch64IsaProfileParseError::EmptyEntry);
            }
            let feature = AArch64IsaFeature::ALL
                .into_iter()
                .find(|feature| feature.name() == entry)
                .ok_or_else(|| AArch64IsaProfileParseError::UnknownFeature(entry.to_owned()))?;
            if profile.permits(feature) {
                return Err(AArch64IsaProfileParseError::DuplicateFeature(
                    feature.name(),
                ));
            }
            profile = profile.with_feature(feature, true);
        }
        Ok(profile)
    }
}

/// Runtime admission check for AArch64 LSE on the current host.
///
/// Returns `false` on non-AArch64 builds. Keeping this query centralized makes
/// host-JIT lowering and raw executable publication share one authority.
pub fn host_has_aarch64_lse() -> bool {
    #[cfg(target_arch = "aarch64")]
    {
        std::arch::is_aarch64_feature_detected!("lse")
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        false
    }
}

/// Runtime admission check for AArch64 FEAT_DotProd on the current host.
pub fn host_has_aarch64_dotprod() -> bool {
    #[cfg(target_arch = "aarch64")]
    {
        std::arch::is_aarch64_feature_detected!("dotprod")
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        false
    }
}

/// Runtime admission check for AArch64 FEAT_LSE2 on the current host.
///
/// LSE2 is what makes a 16-byte-aligned `LDP`/`STP` single-copy atomic, so the
/// 128-bit atomic lowering is gated on it. It must be OBSERVED, never inferred
/// from the presence of LSE: FEAT_LSE is ARMv8.1 (the RMW instructions) and
/// FEAT_LSE2 is ARMv8.4 (the atomicity rules), and a CPU can have the first
/// without the second.
pub fn host_has_aarch64_lse2() -> bool {
    #[cfg(target_arch = "aarch64")]
    {
        std::arch::is_aarch64_feature_detected!("lse2")
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        false
    }
}

/// Runtime admission check for AArch64 FEAT_FP16 scalar data processing.
pub fn host_has_aarch64_fp16() -> bool {
    #[cfg(target_arch = "aarch64")]
    {
        std::arch::is_aarch64_feature_detected!("fp16")
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        false
    }
}

const fn resolve_aarch64_host_jit_profile(
    host_is_aarch64: bool,
    host_has_lse: bool,
    host_has_dotprod: bool,
    host_has_fp16: bool,
    host_has_lse2: bool,
) -> AArch64IsaProfile {
    if !host_is_aarch64 {
        return AArch64IsaProfile::BASELINE;
    }
    AArch64IsaProfile::BASELINE
        .with_feature(AArch64IsaFeature::Lse, host_has_lse)
        .with_feature(AArch64IsaFeature::DotProd, host_has_dotprod)
        .with_feature(AArch64IsaFeature::Fp16, host_has_fp16)
        .with_feature(AArch64IsaFeature::Lse2, host_has_lse2)
}

/// Target triple vendor component for targets Trust Codegen understands today.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TargetVendor {
    /// Unknown or intentionally unspecified vendor.
    Unknown,
    /// Apple platform vendor.
    Apple,
    /// PC platform vendor, used by the MSVC Windows target.
    Pc,
}

impl TargetVendor {
    /// Returns the canonical target-triple component.
    pub fn triple_component(self) -> &'static str {
        match self {
            TargetVendor::Unknown => "unknown",
            TargetVendor::Apple => "apple",
            TargetVendor::Pc => "pc",
        }
    }
}

/// Target operating-system component for targets Trust Codegen understands today.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TargetOperatingSystem {
    /// Unknown or intentionally unspecified operating system.
    Unknown,
    /// Linux.
    Linux,
    /// Darwin / macOS.
    Darwin,
    /// Microsoft Windows.
    Windows,
}

impl TargetOperatingSystem {
    /// Returns the canonical target-triple component.
    pub fn triple_component(self) -> &'static str {
        match self {
            TargetOperatingSystem::Unknown => "unknown",
            TargetOperatingSystem::Linux => "linux",
            TargetOperatingSystem::Darwin => "darwin",
            TargetOperatingSystem::Windows => "windows",
        }
    }

    /// Operating system for the host process, when it maps to a supported spec.
    pub fn host() -> Self {
        if cfg!(target_os = "linux") {
            TargetOperatingSystem::Linux
        } else if cfg!(target_os = "macos") {
            TargetOperatingSystem::Darwin
        } else if cfg!(target_os = "windows") {
            TargetOperatingSystem::Windows
        } else {
            TargetOperatingSystem::Unknown
        }
    }
}

/// Target ABI/environment component for targets Trust Codegen understands today.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TargetEnvironment {
    /// Unknown or intentionally unspecified ABI environment.
    Unknown,
    /// GNU ABI environment.
    Gnu,
    /// Microsoft Visual C++ ABI environment.
    Msvc,
}

impl TargetEnvironment {
    /// Returns the canonical target-triple component.
    pub fn triple_component(self) -> &'static str {
        match self {
            TargetEnvironment::Unknown => "unknown",
            TargetEnvironment::Gnu => "gnu",
            TargetEnvironment::Msvc => "msvc",
        }
    }
}

/// Architecture plus target OS/ABI information requested by a caller.
///
/// The legacy [`Target`] enum remains the backend architecture selector.
/// `TargetSpec` carries the extra triple components needed for x86-64
/// multi-OS object and ABI selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TargetSpec {
    /// Target architecture.
    pub architecture: Target,
    /// Target triple vendor component.
    pub vendor: TargetVendor,
    /// Target operating system.
    pub operating_system: TargetOperatingSystem,
    /// Target ABI/environment.
    pub environment: TargetEnvironment,
    /// Whether the all-unknown components came from an architecture alias or
    /// were explicitly supplied by the caller. This is authority metadata:
    /// only aliases may inherit the host OS/ABI compatibility default.
    origin: TargetSpecOrigin,
    /// macOS deployment target (the minimum OS every Mach-O object for this
    /// target records), from the triple's OS version (`macos12.0`) or
    /// attached by a driver from `MACOSX_DEPLOYMENT_TARGET`. `None` on every
    /// non-Apple target and when neither was given; Mach-O emission then
    /// records [`AppleOsVersion::DEFAULT_MACOS_MINIMUM`]. Part of the spec's
    /// identity: it renders into [`Self::triple`] and the compile policy.
    apple_deployment_target: Option<AppleOsVersion>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum TargetSpecOrigin {
    ArchitectureAlias,
    ExplicitComponents,
}

impl TargetSpec {
    /// Create a target spec from explicit triple components.
    pub fn new(
        architecture: Target,
        vendor: TargetVendor,
        operating_system: TargetOperatingSystem,
        environment: TargetEnvironment,
    ) -> Self {
        Self {
            architecture,
            vendor,
            operating_system,
            environment,
            origin: TargetSpecOrigin::ExplicitComponents,
            apple_deployment_target: None,
        }
    }

    /// Legacy architecture-only target spec.
    pub fn unknown_for_architecture(architecture: Target) -> Self {
        Self {
            architecture,
            vendor: TargetVendor::Unknown,
            operating_system: TargetOperatingSystem::Unknown,
            environment: TargetEnvironment::Unknown,
            origin: TargetSpecOrigin::ArchitectureAlias,
            apple_deployment_target: None,
        }
    }

    /// Host target spec for the host architecture.
    pub fn host() -> Self {
        Self::host_for_architecture(Target::host())
    }

    /// Host OS/ABI spec for a requested architecture.
    pub fn host_for_architecture(architecture: Target) -> Self {
        match TargetOperatingSystem::host() {
            TargetOperatingSystem::Linux => Self::new(
                architecture,
                TargetVendor::Unknown,
                TargetOperatingSystem::Linux,
                TargetEnvironment::Gnu,
            ),
            TargetOperatingSystem::Darwin => Self::new(
                architecture,
                TargetVendor::Apple,
                TargetOperatingSystem::Darwin,
                TargetEnvironment::Unknown,
            ),
            TargetOperatingSystem::Windows => Self::new(
                architecture,
                TargetVendor::Pc,
                TargetOperatingSystem::Windows,
                TargetEnvironment::Msvc,
            ),
            TargetOperatingSystem::Unknown => Self::unknown_for_architecture(architecture),
        }
    }

    /// Trust Codegen's compatibility default for an architecture-only request.
    ///
    /// x86-64 and AArch64 public AOT/JIT now resolve the host OS to select
    /// object format (ELF/Mach-O) and calling convention, matching the
    /// fail-closed object-emission contract that rejects unspecified
    /// `aarch64-unknown-unknown` triples. RISC-V keeps the historical
    /// `*-unknown-unknown` identity until its OS-sensitive paths are wired.
    pub fn default_for_architecture(architecture: Target) -> Self {
        match architecture {
            Target::X86_64 | Target::Aarch64 => Self::host_for_architecture(architecture),
            Target::Riscv64 => Self::unknown_for_architecture(architecture),
        }
    }

    /// Applies Trust Codegen compatibility defaults when OS/ABI was not explicit.
    ///
    /// A macOS deployment target attached to an architecture alias (see
    /// [`Self::with_apple_deployment_target`]) carries over to the resolved
    /// spec when that spec is Apple Darwin.
    pub fn with_default_os_abi(self) -> Self {
        if self.has_explicit_os_abi() {
            return self;
        }
        let resolved = Self::default_for_architecture(self.architecture);
        if resolved.is_apple_darwin() {
            Self {
                apple_deployment_target: self.apple_deployment_target,
                ..resolved
            }
        } else {
            resolved
        }
    }

    fn is_apple_darwin(self) -> bool {
        self.operating_system == TargetOperatingSystem::Darwin && self.vendor == TargetVendor::Apple
    }

    /// Whether the caller provided OS/ABI/vendor information beyond an arch alias.
    pub fn has_explicit_os_abi(self) -> bool {
        self.origin == TargetSpecOrigin::ExplicitComponents
    }

    /// macOS deployment target this spec carries, if any (see the field).
    pub const fn apple_deployment_target(self) -> Option<AppleOsVersion> {
        self.apple_deployment_target
    }

    /// Attach a macOS deployment target to a spec that resolves to Apple
    /// Darwin: an explicit Apple triple, or an architecture alias whose
    /// compatibility default is the Apple host (the alias keeps its
    /// host-derived origin).
    ///
    /// Refused for any other target, and for a version older than the
    /// architecture's first macOS release (`[TCG-MACHO-DEPLOYMENT]`). The
    /// version becomes part of the spec's identity and canonical triple
    /// (`aarch64-apple-macos12.0`).
    pub fn with_apple_deployment_target(
        self,
        version: AppleOsVersion,
        origin: AppleDeploymentTargetSource,
    ) -> Result<Self, AppleDeploymentTargetError> {
        let resolved = self.with_default_os_abi();
        if !resolved.is_apple_darwin() {
            return Err(AppleDeploymentTargetError::NotAnAppleTarget {
                triple: resolved.triple(),
            });
        }
        MachOBuildVersion::macos(self.architecture.name(), version, origin)?;
        Ok(Self {
            apple_deployment_target: Some(version),
            ..self
        })
    }

    /// Capture `MACOSX_DEPLOYMENT_TARGET` into an Apple spec that names no
    /// deployment target, the way Apple's compiler drivers do.
    ///
    /// Returns the spec unchanged when it is not an Apple Darwin spec, when
    /// its triple already names a version (the explicit triple wins, as in
    /// clang) or when the variable is unset. A set value that is malformed or
    /// below the architecture floor is refused, never replaced by the
    /// default. Drivers call this once at their boundary; the compiler
    /// library never reads the process environment for it.
    pub fn with_macos_deployment_target_from_environment(
        self,
    ) -> Result<Self, AppleDeploymentTargetError> {
        if !self.with_default_os_abi().is_apple_darwin() || self.apple_deployment_target.is_some() {
            return Ok(self);
        }
        match crate::apple_deployment::capture_macosx_deployment_target()? {
            Some(version) => {
                self.with_apple_deployment_target(version, AppleDeploymentTargetSource::Environment)
            }
            None => Ok(self),
        }
    }

    /// This spec without its macOS deployment target.
    ///
    /// For comparisons that concern only architecture, OS and ABI -- a
    /// host-JIT admission check, for example -- where the Mach-O minimum OS
    /// of an object never emitted does not apply.
    pub const fn without_apple_deployment_target(self) -> Self {
        Self {
            apple_deployment_target: None,
            ..self
        }
    }

    /// Canonical target triple for this spec.
    ///
    /// An Apple spec with a deployment target spells its OS as
    /// `macos<version>`, so the triple round-trips through [`Self::parse`]
    /// and every triple-keyed identity binds the version.
    pub fn triple(self) -> String {
        let arch = self.architecture.name();
        let vendor = self.vendor.triple_component();
        let os = match self.apple_deployment_target {
            Some(version) if self.operating_system == TargetOperatingSystem::Darwin => {
                format!("macos{version}")
            }
            _ => self.operating_system.triple_component().to_owned(),
        };
        let env = self.environment.triple_component();

        if self.environment == TargetEnvironment::Unknown {
            format!("{arch}-{vendor}-{os}")
        } else {
            format!("{arch}-{vendor}-{os}-{env}")
        }
    }

    /// Parse a supported Trust Codegen target spec.
    pub fn parse(input: &str) -> Result<Self, TargetSpecParseError> {
        input.parse()
    }
}

impl TargetIdentity for TargetSpec {
    fn architecture(&self) -> Target {
        self.architecture
    }
}

/// Shared immutable AArch64 target identity and optional-ISA admission.
pub type AArch64TargetMachine = TargetMachine<TargetSpec, AArch64IsaFeature>;

/// Target-feature facts derived from one final AArch64 machine-code stream.
///
/// Construction validates that the output-required features are a subset of
/// the features admitted by the captured target machine. Artifact and install
/// layers can therefore bind both what codegen was allowed to emit and what it
/// actually emitted without rescanning instructions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AArch64MachineCodeEvidence {
    target: TargetSpec,
    admitted_features: AdmittedTargetFeatures<AArch64IsaFeature>,
    required_features: OutputTargetFeatures<AArch64IsaFeature>,
}

impl AArch64MachineCodeEvidence {
    /// Validate and capture evidence for one final machine-code stream.
    pub fn try_new(
        machine: &AArch64TargetMachine,
        required_features: OutputTargetFeatures<AArch64IsaFeature>,
    ) -> Result<Self, TargetMachineError<AArch64IsaFeature>> {
        machine.validate_output_features(required_features)?;
        Ok(Self {
            target: *machine.identity(),
            admitted_features: machine.admitted_features(),
            required_features,
        })
    }

    /// Immutable target identity captured for this compilation.
    pub const fn target(self) -> TargetSpec {
        self.target
    }

    /// Optional features codegen was authorized to emit.
    pub const fn admitted_features(self) -> AdmittedTargetFeatures<AArch64IsaFeature> {
        self.admitted_features
    }

    /// Optional features found in the final emitted instruction stream.
    pub const fn required_features(self) -> OutputTargetFeatures<AArch64IsaFeature> {
        self.required_features
    }
}

impl fmt::Display for TargetSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.triple())
    }
}

/// Machine-readable target parse failure category.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TargetSpecParseErrorKind {
    /// The target string was empty after trimming.
    Empty,
    /// The target was neither a known alias nor a 3/4-component triple.
    InvalidShape,
    /// The input requested a 32-bit x86/i686 target, which Trust Codegen does not implement.
    UnsupportedX86ThirtyTwo,
    /// The architecture component is not supported.
    UnsupportedArchitecture,
    /// The vendor component is not supported.
    UnsupportedVendor,
    /// The operating-system component is not supported.
    UnsupportedOperatingSystem,
    /// The ABI/environment component is not supported.
    UnsupportedEnvironment,
    /// The individual triple components are known, but the combination is unsupported.
    UnsupportedTargetCombination,
    /// The operating-system version component is malformed or predates the
    /// architecture's first release on that OS.
    InvalidOperatingSystemVersion,
}

/// Error returned when parsing a target spec fails.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TargetSpecParseError {
    input: String,
    kind: TargetSpecParseErrorKind,
    reason: &'static str,
}

impl TargetSpecParseError {
    fn new(input: impl Into<String>, kind: TargetSpecParseErrorKind, reason: &'static str) -> Self {
        Self {
            input: input.into(),
            kind,
            reason,
        }
    }

    /// The original target string that failed to parse.
    pub fn input(&self) -> &str {
        &self.input
    }

    /// Machine-readable parse failure category.
    pub fn kind(&self) -> TargetSpecParseErrorKind {
        self.kind
    }

    /// Human-readable parse failure reason.
    pub fn reason(&self) -> &'static str {
        self.reason
    }
}

impl fmt::Display for TargetSpecParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let label = match self.kind {
            TargetSpecParseErrorKind::UnsupportedX86ThirtyTwo
            | TargetSpecParseErrorKind::UnsupportedTargetCombination
            | TargetSpecParseErrorKind::InvalidOperatingSystemVersion => "unsupported target",
            TargetSpecParseErrorKind::Empty
            | TargetSpecParseErrorKind::InvalidShape
            | TargetSpecParseErrorKind::UnsupportedArchitecture
            | TargetSpecParseErrorKind::UnsupportedVendor
            | TargetSpecParseErrorKind::UnsupportedOperatingSystem
            | TargetSpecParseErrorKind::UnsupportedEnvironment => "unknown target",
        };
        write!(f, "{label} '{}': {}", self.input, self.reason)
    }
}

impl Error for TargetSpecParseError {}

const UNSUPPORTED_X86_32_REASON: &str = "unsupported 32-bit x86 target; x86 support is x86_64 only";

fn unsupported_x86_32_error(input: &str) -> TargetSpecParseError {
    TargetSpecParseError::new(
        input,
        TargetSpecParseErrorKind::UnsupportedX86ThirtyTwo,
        UNSUPPORTED_X86_32_REASON,
    )
}

fn is_unsupported_x86_32_arch(component: &str) -> bool {
    matches!(component, "x86" | "i386" | "i486" | "i586" | "i686")
}

impl FromStr for TargetSpec {
    type Err = TargetSpecParseError;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        let normalized = input.trim().to_ascii_lowercase();
        if normalized.is_empty() {
            return Err(TargetSpecParseError::new(
                input,
                TargetSpecParseErrorKind::Empty,
                "target cannot be empty",
            ));
        }
        if is_unsupported_x86_32_arch(normalized.as_str()) {
            return Err(unsupported_x86_32_error(input));
        }

        match normalized.as_str() {
            "aarch64" | "arm64" => return Ok(Self::unknown_for_architecture(Target::Aarch64)),
            "x86_64" | "x86-64" | "x64" => {
                return Ok(Self::unknown_for_architecture(Target::X86_64));
            }
            "riscv64" | "riscv" => return Ok(Self::unknown_for_architecture(Target::Riscv64)),
            _ => {}
        }

        let parts: Vec<&str> = normalized.split('-').collect();
        if parts.len() != 3 && parts.len() != 4 {
            return Err(TargetSpecParseError::new(
                input,
                TargetSpecParseErrorKind::InvalidShape,
                "expected an arch alias or a 3/4-component target triple",
            ));
        }

        let architecture = parse_target_architecture(parts[0], input)?;
        let vendor = parse_target_vendor(parts[1], input)?;
        let (operating_system, os_version) = parse_target_operating_system(parts[2], input)?;
        let environment = if parts.len() == 4 {
            parse_target_environment(parts[3], input)?
        } else {
            TargetEnvironment::Unknown
        };
        let spec = Self::new(architecture, vendor, operating_system, environment);
        validate_target_spec(spec, input)?;
        match os_version {
            None => Ok(spec),
            Some(version) => spec
                .with_apple_deployment_target(version, AppleDeploymentTargetSource::TargetTriple)
                .map_err(|_| {
                    TargetSpecParseError::new(
                        input,
                        TargetSpecParseErrorKind::InvalidOperatingSystemVersion,
                        "the macOS version predates the architecture's first macOS release \
                         (arm64 requires 11.0 or later)",
                    )
                }),
        }
    }
}

fn parse_target_architecture(component: &str, input: &str) -> Result<Target, TargetSpecParseError> {
    match component {
        "aarch64" | "arm64" => Ok(Target::Aarch64),
        "x86_64" | "x64" => Ok(Target::X86_64),
        "riscv64" | "riscv" => Ok(Target::Riscv64),
        // wasm32 is a stack machine — routed to the wasm backend
        // (`trust_cg_codegen::wasm::compile_module`) at the dispatch boundary
        // via `wasm::is_wasm32_target`, and deliberately not represented in this
        // register-machine `Target` enum.
        "wasm32" => Err(TargetSpecParseError::new(
            input,
            TargetSpecParseErrorKind::UnsupportedArchitecture,
            "wasm32 is handled by the trust-cg wasm backend (trust_cg_codegen::wasm), \
             not the register-machine Target enum; route via wasm::is_wasm32_target",
        )),
        arch if is_unsupported_x86_32_arch(arch) => Err(unsupported_x86_32_error(input)),
        _ => Err(TargetSpecParseError::new(
            input,
            TargetSpecParseErrorKind::UnsupportedArchitecture,
            "unsupported architecture; supported architectures are aarch64, x86_64, riscv64",
        )),
    }
}

fn parse_target_vendor(component: &str, input: &str) -> Result<TargetVendor, TargetSpecParseError> {
    match component {
        "unknown" => Ok(TargetVendor::Unknown),
        "apple" => Ok(TargetVendor::Apple),
        "pc" => Ok(TargetVendor::Pc),
        _ => Err(TargetSpecParseError::new(
            input,
            TargetSpecParseErrorKind::UnsupportedVendor,
            "unsupported vendor; supported vendors are unknown, apple, pc",
        )),
    }
}

/// The OS component and, for `macos<version>`/`macosx<version>`, its
/// deployment-target version.
fn parse_target_operating_system(
    component: &str,
    input: &str,
) -> Result<(TargetOperatingSystem, Option<AppleOsVersion>), TargetSpecParseError> {
    match component {
        "unknown" => return Ok((TargetOperatingSystem::Unknown, None)),
        "linux" => return Ok((TargetOperatingSystem::Linux, None)),
        "darwin" | "macos" | "macosx" => return Ok((TargetOperatingSystem::Darwin, None)),
        "windows" => return Ok((TargetOperatingSystem::Windows, None)),
        _ => {}
    }
    if let Some(version) = component
        .strip_prefix("macosx")
        .or_else(|| component.strip_prefix("macos"))
    {
        return AppleOsVersion::parse(version)
            .map(|version| (TargetOperatingSystem::Darwin, Some(version)))
            .map_err(|_| {
                TargetSpecParseError::new(
                    input,
                    TargetSpecParseErrorKind::InvalidOperatingSystemVersion,
                    "malformed macOS version; expected macos<major>[.<minor>[.<patch>]] with \
                     decimal components",
                )
            });
    }
    if component
        .strip_prefix("darwin")
        .is_some_and(|version| !version.is_empty())
    {
        return Err(TargetSpecParseError::new(
            input,
            TargetSpecParseErrorKind::UnsupportedOperatingSystem,
            "a Darwin kernel version is not mapped to a macOS deployment target; spell the \
             target as <arch>-apple-macos<version>",
        ));
    }
    Err(TargetSpecParseError::new(
        input,
        TargetSpecParseErrorKind::UnsupportedOperatingSystem,
        "unsupported operating system; supported OS values are unknown, linux, darwin, \
         macos[<version>], windows",
    ))
}

fn parse_target_environment(
    component: &str,
    input: &str,
) -> Result<TargetEnvironment, TargetSpecParseError> {
    match component {
        "unknown" => Ok(TargetEnvironment::Unknown),
        "gnu" => Ok(TargetEnvironment::Gnu),
        "msvc" => Ok(TargetEnvironment::Msvc),
        _ => Err(TargetSpecParseError::new(
            input,
            TargetSpecParseErrorKind::UnsupportedEnvironment,
            "unsupported ABI environment; supported environments are unknown, gnu, msvc",
        )),
    }
}

fn validate_target_spec(spec: TargetSpec, input: &str) -> Result<(), TargetSpecParseError> {
    let supported = match spec.architecture {
        Target::X86_64 => matches!(
            (spec.vendor, spec.operating_system, spec.environment),
            (
                TargetVendor::Unknown,
                TargetOperatingSystem::Unknown,
                TargetEnvironment::Unknown
            ) | (
                TargetVendor::Unknown,
                TargetOperatingSystem::Linux,
                TargetEnvironment::Gnu
            ) | (
                TargetVendor::Apple,
                TargetOperatingSystem::Darwin,
                TargetEnvironment::Unknown
            ) | (
                TargetVendor::Pc,
                TargetOperatingSystem::Windows,
                TargetEnvironment::Msvc
            )
        ),
        Target::Aarch64 => matches!(
            (spec.vendor, spec.operating_system, spec.environment),
            (
                TargetVendor::Unknown,
                TargetOperatingSystem::Unknown,
                TargetEnvironment::Unknown
            ) | (
                TargetVendor::Unknown,
                TargetOperatingSystem::Linux,
                TargetEnvironment::Gnu
            ) | (
                TargetVendor::Apple,
                TargetOperatingSystem::Darwin,
                TargetEnvironment::Unknown
            )
        ),
        Target::Riscv64 => matches!(
            (spec.vendor, spec.operating_system, spec.environment),
            (
                TargetVendor::Unknown,
                TargetOperatingSystem::Unknown,
                TargetEnvironment::Unknown
            ) | (
                TargetVendor::Unknown,
                TargetOperatingSystem::Linux,
                TargetEnvironment::Gnu
            )
        ),
    };

    if supported {
        Ok(())
    } else {
        Err(TargetSpecParseError::new(
            input,
            TargetSpecParseErrorKind::UnsupportedTargetCombination,
            "unsupported target triple combination",
        ))
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use crate::apple_deployment::{
        AppleDeploymentTargetError, AppleDeploymentTargetSource, AppleOsVersion,
        MACOSX_DEPLOYMENT_TARGET,
    };

    #[test]
    fn versioned_macos_triples_round_trip_with_their_deployment_target() {
        for (input, canonical, version) in [
            (
                "aarch64-apple-macos12.0",
                "aarch64-apple-macos12.0",
                AppleOsVersion::new(12, 0, 0),
            ),
            (
                "arm64-apple-macosx13.3.1",
                "aarch64-apple-macos13.3.1",
                AppleOsVersion::new(13, 3, 1),
            ),
            (
                "aarch64-apple-macos15",
                "aarch64-apple-macos15.0",
                AppleOsVersion::new(15, 0, 0),
            ),
            (
                "x86_64-apple-macos10.15",
                "x86_64-apple-macos10.15",
                AppleOsVersion::new(10, 15, 0),
            ),
        ] {
            let spec = TargetSpec::parse(input).unwrap();
            assert_eq!(
                spec.operating_system,
                TargetOperatingSystem::Darwin,
                "{input}"
            );
            assert_eq!(spec.vendor, TargetVendor::Apple, "{input}");
            assert_eq!(spec.apple_deployment_target(), Some(version), "{input}");
            assert_eq!(spec.triple(), canonical, "{input}");
            assert_eq!(TargetSpec::parse(&spec.triple()).unwrap(), spec, "{input}");
            assert!(spec.has_explicit_os_abi());
            assert_ne!(spec, spec.without_apple_deployment_target());
        }
        for unversioned in [
            "aarch64-apple-darwin",
            "aarch64-apple-macos",
            "arm64-apple-macosx",
        ] {
            let spec = TargetSpec::parse(unversioned).unwrap();
            assert_eq!(spec.apple_deployment_target(), None, "{unversioned}");
            assert_eq!(spec.triple(), "aarch64-apple-darwin");
        }
    }

    #[test]
    fn malformed_or_unmodeled_macos_versions_are_refused() {
        for (input, kind) in [
            (
                "aarch64-apple-macos14..0",
                TargetSpecParseErrorKind::InvalidOperatingSystemVersion,
            ),
            (
                "aarch64-apple-macos1x",
                TargetSpecParseErrorKind::InvalidOperatingSystemVersion,
            ),
            (
                "aarch64-apple-macos0",
                TargetSpecParseErrorKind::InvalidOperatingSystemVersion,
            ),
            (
                "aarch64-apple-macos14.256",
                TargetSpecParseErrorKind::InvalidOperatingSystemVersion,
            ),
            (
                "aarch64-apple-macos10.15",
                TargetSpecParseErrorKind::InvalidOperatingSystemVersion,
            ),
            (
                "aarch64-apple-darwin23",
                TargetSpecParseErrorKind::UnsupportedOperatingSystem,
            ),
            (
                "aarch64-apple-darwin23.1.0",
                TargetSpecParseErrorKind::UnsupportedOperatingSystem,
            ),
            (
                "aarch64-apple-ios17.0",
                TargetSpecParseErrorKind::UnsupportedOperatingSystem,
            ),
            (
                "aarch64-unknown-macos12.0",
                TargetSpecParseErrorKind::UnsupportedTargetCombination,
            ),
        ] {
            let error = TargetSpec::parse(input).unwrap_err();
            assert_eq!(error.kind(), kind, "{input}: {error}");
        }
    }

    #[test]
    fn deployment_targets_attach_only_to_apple_specs() {
        let linux = TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap();
        assert!(matches!(
            linux.with_apple_deployment_target(
                AppleOsVersion::new(12, 0, 0),
                AppleDeploymentTargetSource::Environment,
            ),
            Err(AppleDeploymentTargetError::NotAnAppleTarget { .. })
        ));
        let darwin = TargetSpec::parse("aarch64-apple-darwin").unwrap();
        assert!(matches!(
            darwin.with_apple_deployment_target(
                AppleOsVersion::new(10, 15, 0),
                AppleDeploymentTargetSource::Environment,
            ),
            Err(AppleDeploymentTargetError::BelowArchitectureFloor { .. })
        ));
        let twelve = darwin
            .with_apple_deployment_target(
                AppleOsVersion::new(12, 0, 0),
                AppleDeploymentTargetSource::Environment,
            )
            .unwrap();
        assert_eq!(
            twelve,
            TargetSpec::parse("aarch64-apple-macos12.0").unwrap()
        );
    }

    #[test]
    fn environment_capture_is_explicit_and_refuses_malformed_values() {
        let darwin = TargetSpec::parse("aarch64-apple-darwin").unwrap();
        let linux = TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap();
        let versioned = TargetSpec::parse("aarch64-apple-macos13.0").unwrap();
        trust_cg_process_env::with_env_overrides(&[(MACOSX_DEPLOYMENT_TARGET, "12.4")], || {
            let captured = darwin
                .with_macos_deployment_target_from_environment()
                .unwrap();
            assert_eq!(
                captured.apple_deployment_target(),
                Some(AppleOsVersion::new(12, 4, 0))
            );
            assert_eq!(captured.triple(), "aarch64-apple-macos12.4");
            // The explicit triple version wins; a non-Apple target is untouched.
            assert_eq!(
                versioned
                    .with_macos_deployment_target_from_environment()
                    .unwrap(),
                versioned
            );
            assert_eq!(
                linux
                    .with_macos_deployment_target_from_environment()
                    .unwrap(),
                linux
            );
        });
        for malformed in ["", "12.", "twelve", "10.15"] {
            trust_cg_process_env::with_env_overrides(
                &[(MACOSX_DEPLOYMENT_TARGET, malformed)],
                || {
                    assert!(
                        darwin
                            .with_macos_deployment_target_from_environment()
                            .is_err(),
                        "{malformed:?} must be refused"
                    );
                },
            );
        }
        trust_cg_process_env::with_env_overrides_removed(&[MACOSX_DEPLOYMENT_TARGET], || {
            assert_eq!(
                darwin
                    .with_macos_deployment_target_from_environment()
                    .unwrap(),
                darwin
            );
        });
    }

    /// An architecture alias resolved to the Apple host keeps its host-derived
    /// origin and carries the captured version through the default.
    #[cfg(target_os = "macos")]
    #[test]
    fn alias_capture_carries_the_version_to_the_resolved_host_spec() {
        let alias = TargetSpec::parse("aarch64").unwrap();
        trust_cg_process_env::with_env_overrides(&[(MACOSX_DEPLOYMENT_TARGET, "13.1")], || {
            let captured = alias
                .with_macos_deployment_target_from_environment()
                .unwrap();
            assert!(!captured.has_explicit_os_abi());
            let resolved = captured.with_default_os_abi();
            assert_eq!(resolved.triple(), "aarch64-apple-macos13.1");
            assert_eq!(
                resolved.apple_deployment_target(),
                Some(AppleOsVersion::new(13, 1, 0))
            );
        });
    }
    use super::*;

    /// An explicit feature list names exactly its profile; `none` is the
    /// baseline; unknown, duplicate and empty entries are refused by name.
    #[test]
    fn explicit_isa_feature_lists_parse_exactly() {
        let parse = |list: &str| list.parse::<AArch64IsaProfile>();
        assert_eq!(parse("none"), Ok(AArch64IsaProfile::BASELINE));
        assert_eq!(parse("fp16"), Ok(AArch64IsaProfile::FP16));
        assert_eq!(parse("lse"), Ok(AArch64IsaProfile::LSE));
        // `APPLE_ARM64` admits FEAT_LSE2 (see its doc), so its explicit list
        // names `lse2`; the same three without it are LSE_DOTPROD plus FP16.
        assert_eq!(
            parse("fp16,lse,lse2,dotprod"),
            Ok(AArch64IsaProfile::APPLE_ARM64)
        );
        assert_ne!(
            parse("fp16,lse,dotprod"),
            Ok(AArch64IsaProfile::APPLE_ARM64)
        );
        for profile in [
            AArch64IsaProfile::BASELINE,
            AArch64IsaProfile::FP16,
            AArch64IsaProfile::LSE_DOTPROD,
            AArch64IsaProfile::APPLE_ARM64,
        ] {
            let names: Vec<_> = profile.enabled_feature_names().collect();
            let list = if names.is_empty() {
                "none".to_owned()
            } else {
                names.join(",")
            };
            assert_eq!(parse(&list), Ok(profile), "{list}");
        }
        assert_eq!(
            parse("fp17"),
            Err(AArch64IsaProfileParseError::UnknownFeature("fp17".into()))
        );
        assert_eq!(
            parse("fp16,fp16"),
            Err(AArch64IsaProfileParseError::DuplicateFeature("fp16"))
        );
        assert_eq!(parse(""), Err(AArch64IsaProfileParseError::EmptyEntry));
        assert_eq!(
            parse("lse,,fp16"),
            Err(AArch64IsaProfileParseError::EmptyEntry)
        );
        assert!(parse("FP16").is_err(), "feature names are exact");
    }

    #[test]
    fn test_target_names() {
        assert_eq!(Target::X86_64.name(), "x86_64");
        assert_eq!(Target::Aarch64.name(), "aarch64");
        assert_eq!(Target::Riscv64.name(), "riscv64");
    }

    #[test]
    fn test_pointer_bytes() {
        assert_eq!(Target::X86_64.pointer_bytes(), 8);
        assert_eq!(Target::Aarch64.pointer_bytes(), 8);
        assert_eq!(Target::Riscv64.pointer_bytes(), 8);
    }

    #[test]
    fn test_stack_alignment() {
        assert_eq!(Target::X86_64.stack_alignment(), 16);
        assert_eq!(Target::Aarch64.stack_alignment(), 16);
        assert_eq!(Target::Riscv64.stack_alignment(), 16);
    }

    #[test]
    fn test_arg_register_counts() {
        // System V: 6 GPR args, 8 XMM args
        assert_eq!(Target::X86_64.num_arg_gprs(), 6);
        assert_eq!(Target::X86_64.num_arg_fprs(), 8);

        // AAPCS64: 8 GPR args, 8 FPR args
        assert_eq!(Target::Aarch64.num_arg_gprs(), 8);
        assert_eq!(Target::Aarch64.num_arg_fprs(), 8);
    }

    #[test]
    fn test_callee_saved_counts() {
        // System V: RBX, RBP, R12-R15 = 6
        assert_eq!(Target::X86_64.num_callee_saved_gprs(), 6);
        // AAPCS64: X19-X28 = 10
        assert_eq!(Target::Aarch64.num_callee_saved_gprs(), 10);
    }

    #[test]
    fn test_allocatable_gprs() {
        // x86-64: 16 GPRs - RSP - RBP = 14
        assert_eq!(Target::X86_64.num_allocatable_gprs(), 14);
        // AArch64: 25 (excludes X8, X16-X18, X29, X30)
        assert_eq!(Target::Aarch64.num_allocatable_gprs(), 25);
    }

    #[test]
    fn test_frame_pointer_requirement() {
        // Apple AArch64 requires frame pointer
        assert!(Target::Aarch64.requires_frame_pointer());
        // x86-64 does not require it
        assert!(!Target::X86_64.requires_frame_pointer());
    }

    #[test]
    fn test_calling_convention_aarch64() {
        let cc = Target::Aarch64.calling_convention();
        assert_eq!(cc.name, "aapcs64");
        assert_eq!(cc.num_arg_gprs, 8);
        assert_eq!(cc.num_arg_fprs, 8);
        assert_eq!(cc.num_ret_gprs, 8);
        assert_eq!(cc.num_ret_fprs, 8);
        assert_eq!(cc.red_zone_size, 128);
        assert_eq!(cc.shadow_space, 0);
    }

    #[test]
    fn test_calling_convention_x86_64() {
        let cc = Target::X86_64.calling_convention();
        assert_eq!(cc.name, "sysv_amd64");
        assert_eq!(cc.num_arg_gprs, 6);
        assert_eq!(cc.num_arg_fprs, 8);
        assert_eq!(cc.num_ret_gprs, 2);
        assert_eq!(cc.num_ret_fprs, 2);
        assert_eq!(cc.red_zone_size, 128);
        assert_eq!(cc.shadow_space, 0);
    }

    #[test]
    fn test_calling_convention_riscv64() {
        let cc = Target::Riscv64.calling_convention();
        assert_eq!(cc.name, "riscv_lp64d");
        assert_eq!(cc.num_arg_gprs, 8);
        assert_eq!(cc.red_zone_size, 0);
    }

    #[test]
    fn test_riscv64_arg_register_counts() {
        // RISC-V LP64D: 8 GPR args (a0-a7), 8 FPR args (fa0-fa7)
        assert_eq!(Target::Riscv64.num_arg_gprs(), 8);
        assert_eq!(Target::Riscv64.num_arg_fprs(), 8);
    }

    #[test]
    fn test_riscv64_callee_saved_count() {
        // RISC-V: s0-s11 = 12
        assert_eq!(Target::Riscv64.num_callee_saved_gprs(), 12);
    }

    #[test]
    fn test_riscv64_allocatable_gprs() {
        // RISC-V: 32 GPRs - x0/zero - x2/sp - x3/gp - x4/tp = 28
        assert_eq!(Target::Riscv64.num_allocatable_gprs(), 28);
    }

    #[test]
    fn test_riscv64_frame_pointer() {
        assert!(!Target::Riscv64.requires_frame_pointer());
    }

    #[test]
    fn test_target_equality() {
        assert_eq!(Target::X86_64, Target::X86_64);
        assert_ne!(Target::X86_64, Target::Aarch64);
        assert_ne!(Target::Riscv64, Target::Aarch64);
    }

    #[test]
    fn test_host_target_is_known() {
        // The host() helper must return one of the known targets; which one
        // depends on the compiler's target_arch. We assert it's consistent
        // with cfg().
        let host = Target::host();
        #[cfg(target_arch = "x86_64")]
        assert_eq!(host, Target::X86_64);
        #[cfg(target_arch = "aarch64")]
        assert_eq!(host, Target::Aarch64);
        #[cfg(target_arch = "riscv64")]
        assert_eq!(host, Target::Riscv64);

        // Sanity: host() is one of the enum variants we know.
        assert!(matches!(
            host,
            Target::X86_64 | Target::Aarch64 | Target::Riscv64
        ));
    }

    #[test]
    fn aarch64_isa_profile_has_stable_cache_identity() {
        assert_eq!(AArch64IsaProfile::BASELINE.feature_bits(), 0);
        assert_eq!(AArch64IsaProfile::LSE.feature_bits(), 1);
        assert_eq!(AArch64IsaProfile::DOTPROD.feature_bits(), 2);
        assert_eq!(AArch64IsaProfile::FP16.feature_bits(), 4);
        assert_eq!(AArch64IsaProfile::LSE_DOTPROD.feature_bits(), 3);
        // 15 = LSE|DotProd|FP16|LSE2. Was 7 before LSE2 was admitted; this pin is
        // what makes that identity move deliberate rather than silent.
        assert_eq!(AArch64IsaProfile::APPLE_ARM64.feature_bits(), 15);
        assert_eq!(
            AArch64IsaProfile::BASELINE.canonical_name(),
            "aarch64-isa-v1"
        );
        assert_eq!(
            AArch64IsaProfile::LSE.canonical_name(),
            "aarch64-isa-v1+lse"
        );
        assert_eq!(
            AArch64IsaProfile::APPLE_ARM64.canonical_name(),
            "aarch64-isa-v1+dotprod+fp16+lse+lse2"
        );
        assert!(!AArch64IsaProfile::BASELINE.permits_lse());
        assert!(AArch64IsaProfile::LSE.permits_lse());
        assert!(!AArch64IsaProfile::LSE.permits_dotprod());
        assert!(AArch64IsaProfile::DOTPROD.permits_dotprod());
        assert!(AArch64IsaProfile::FP16.permits_fp16());
        assert_eq!(
            AArch64IsaProfile::APPLE_ARM64
                .enabled_feature_names()
                .collect::<Vec<_>>(),
            vec!["dotprod", "fp16", "lse", "lse2"]
        );
    }

    #[test]
    fn aarch64_target_machine_contract_accepts_real_identity_and_features() {
        let identity = TargetSpec::parse("aarch64-apple-darwin").unwrap();
        let admitted = AArch64IsaProfile::APPLE_ARM64.admitted_target_features();
        let machine: crate::TargetMachine<TargetSpec, AArch64IsaFeature> =
            TargetMachine::try_new(identity, admitted).unwrap();

        assert_eq!(machine.identity(), &identity);
        assert_eq!(
            machine.admitted_features().bits(),
            u64::from(AArch64IsaProfile::APPLE_ARM64.feature_bits())
        );
        let required = OutputTargetFeatures::try_from_output([
            AArch64IsaFeature::DotProd,
            AArch64IsaFeature::Fp16,
        ])
        .unwrap();
        machine.validate_output_features(required).unwrap();
        let evidence = AArch64MachineCodeEvidence::try_new(&machine, required).unwrap();
        assert_eq!(evidence.target(), identity);
        assert_eq!(evidence.admitted_features(), admitted);
        assert_eq!(evidence.required_features(), required);

        for feature_bits in 0_u32..=7 {
            let profile = AArch64IsaFeature::ALL.into_iter().fold(
                AArch64IsaProfile::BASELINE,
                |profile, feature| {
                    profile.with_feature(feature, feature_bits & feature.mask() != 0)
                },
            );
            assert_eq!(
                AArch64IsaProfile::from(profile.admitted_target_features()),
                profile,
                "typed admission must preserve AArch64 profile bits {feature_bits:#05b}"
            );
        }
    }

    #[test]
    fn riscv_target_machine_uses_an_explicit_empty_feature_domain() {
        let identity = TargetSpec::parse("riscv64-unknown-unknown").unwrap();
        let machine: TargetMachine<TargetSpec, RiscVIsaFeature> =
            TargetMachine::try_new(identity, AdmittedTargetFeatures::NONE).unwrap();

        assert_eq!(machine.identity(), &identity);
        assert!(machine.admitted_features().as_set().is_empty());
        machine
            .validate_output_features(OutputTargetFeatures::NONE)
            .unwrap();
    }

    #[test]
    fn aarch64_aot_profile_is_conservative_except_for_apple_arm64() {
        let apple_arm64 = TargetSpec::parse("aarch64-apple-darwin").unwrap();
        assert_eq!(
            AArch64IsaProfile::for_aot_target(apple_arm64),
            AArch64IsaProfile::APPLE_ARM64
        );

        let generic_linux = TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap();
        assert_eq!(
            AArch64IsaProfile::for_aot_target(generic_linux),
            AArch64IsaProfile::BASELINE
        );

        let generic = TargetSpec::unknown_for_architecture(Target::Aarch64);
        assert_eq!(
            AArch64IsaProfile::for_aot_target(generic),
            AArch64IsaProfile::BASELINE
        );

        let non_aarch64 = TargetSpec::parse("x86_64-apple-darwin").unwrap();
        assert_eq!(
            AArch64IsaProfile::for_aot_target(non_aarch64),
            AArch64IsaProfile::BASELINE
        );
    }

    #[test]
    fn aarch64_host_profile_never_invents_features() {
        assert_eq!(
            resolve_aarch64_host_jit_profile(false, false, false, false, false),
            AArch64IsaProfile::BASELINE
        );
        assert_eq!(
            resolve_aarch64_host_jit_profile(false, true, true, true, true),
            AArch64IsaProfile::BASELINE,
            "feature observations cannot authorize AArch64 code on a non-AArch64 host"
        );
        assert_eq!(
            resolve_aarch64_host_jit_profile(true, false, false, false, false),
            AArch64IsaProfile::BASELINE
        );
        assert_eq!(
            resolve_aarch64_host_jit_profile(true, true, false, false, false),
            AArch64IsaProfile::LSE
        );
        assert_eq!(
            resolve_aarch64_host_jit_profile(true, false, true, false, false),
            AArch64IsaProfile::DOTPROD
        );
        assert_eq!(
            resolve_aarch64_host_jit_profile(true, true, true, false, false),
            AArch64IsaProfile::LSE_DOTPROD
        );
        assert_eq!(
            resolve_aarch64_host_jit_profile(true, true, true, true, true),
            AArch64IsaProfile::APPLE_ARM64
        );
        // LSE without LSE2 is a REAL configuration (FEAT_LSE is ARMv8.1, FEAT_LSE2
        // is ARMv8.4), and the profile must not promote one to the other: with
        // lse2 unobserved the result is NOT APPLE_ARM64, so the 128-bit atomic
        // lowering stays unadmitted on such a host.
        assert_ne!(
            resolve_aarch64_host_jit_profile(true, true, true, true, false),
            AArch64IsaProfile::APPLE_ARM64,
            "an unobserved FEAT_LSE2 must never be invented from FEAT_LSE"
        );
        assert!(!resolve_aarch64_host_jit_profile(true, true, true, true, false).permits_lse2());
    }

    #[test]
    fn aarch64_host_profile_matches_runtime_admission() {
        let profile = AArch64IsaProfile::for_host_jit();
        assert_eq!(
            profile,
            resolve_aarch64_host_jit_profile(
                cfg!(target_arch = "aarch64"),
                host_has_aarch64_lse(),
                host_has_aarch64_dotprod(),
                host_has_aarch64_fp16(),
                host_has_aarch64_lse2(),
            )
        );
        assert!(!cfg!(target_arch = "aarch64") || profile.is_supported_by_host());
    }

    #[test]
    fn test_target_spec_parse_x86_requested_triples() {
        let windows = TargetSpec::parse("x86_64-pc-windows-msvc").unwrap();
        assert_eq!(windows.architecture, Target::X86_64);
        assert_eq!(windows.vendor, TargetVendor::Pc);
        assert_eq!(windows.operating_system, TargetOperatingSystem::Windows);
        assert_eq!(windows.environment, TargetEnvironment::Msvc);
        assert_eq!(windows.triple(), "x86_64-pc-windows-msvc");

        let linux = TargetSpec::parse("x86_64-unknown-linux-gnu").unwrap();
        assert_eq!(linux.architecture, Target::X86_64);
        assert_eq!(linux.vendor, TargetVendor::Unknown);
        assert_eq!(linux.operating_system, TargetOperatingSystem::Linux);
        assert_eq!(linux.environment, TargetEnvironment::Gnu);
        assert_eq!(linux.triple(), "x86_64-unknown-linux-gnu");

        let darwin = TargetSpec::parse("x86_64-apple-darwin").unwrap();
        assert_eq!(darwin.architecture, Target::X86_64);
        assert_eq!(darwin.vendor, TargetVendor::Apple);
        assert_eq!(darwin.operating_system, TargetOperatingSystem::Darwin);
        assert_eq!(darwin.environment, TargetEnvironment::Unknown);
        assert_eq!(darwin.triple(), "x86_64-apple-darwin");

        assert_ne!(windows, linux);
        assert_ne!(linux, darwin);
        assert_ne!(windows, darwin);
    }

    #[test]
    fn test_target_spec_arch_aliases_preserve_legacy_unknown_spec() {
        let x86_64 = TargetSpec::parse("x86_64").unwrap();
        assert_eq!(x86_64, TargetSpec::unknown_for_architecture(Target::X86_64));
        assert!(!x86_64.has_explicit_os_abi());
        assert_eq!(x86_64.triple(), "x86_64-unknown-unknown");

        let x86 = TargetSpec::parse("x86-64").unwrap();
        assert_eq!(x86, TargetSpec::unknown_for_architecture(Target::X86_64));
        assert!(!x86.has_explicit_os_abi());
        assert_eq!(x86.triple(), "x86_64-unknown-unknown");

        let aarch64 = TargetSpec::parse("arm64").unwrap();
        assert_eq!(
            aarch64,
            TargetSpec::unknown_for_architecture(Target::Aarch64)
        );
        assert_eq!(aarch64.triple(), "aarch64-unknown-unknown");
    }

    #[test]
    fn test_explicit_unknown_triple_does_not_inherit_host_os_abi() {
        let explicit = TargetSpec::parse("aarch64-unknown-unknown").unwrap();
        let alias = TargetSpec::parse("aarch64").unwrap();

        assert!(explicit.has_explicit_os_abi());
        assert!(!alias.has_explicit_os_abi());
        assert_eq!(explicit.with_default_os_abi(), explicit);
        assert_ne!(explicit, alias);
        assert_eq!(explicit.triple(), alias.triple());
    }

    #[test]
    fn test_target_spec_rejects_unsupported_x86_32_aliases_and_triples() {
        let cases = [
            "x86",
            "i386",
            "i486",
            "i586",
            "i686",
            "i686-unknown-linux-gnu",
            "i686-pc-windows-msvc",
            "i386-apple-darwin",
        ];

        for input in cases {
            let err = match TargetSpec::parse(input) {
                Ok(spec) => panic!("{input} unexpectedly parsed as {spec}"),
                Err(err) => err,
            };
            assert_eq!(
                err.kind(),
                TargetSpecParseErrorKind::UnsupportedX86ThirtyTwo,
                "{input} produced wrong target parse error: {err}"
            );
            assert_eq!(err.input(), input);
            assert!(err.reason().contains("32-bit x86"));
            assert!(
                err.to_string().contains("x86_64 only"),
                "{input} error should name the x86_64-only boundary: {err}"
            );
        }
    }

    #[test]
    fn test_target_spec_rejects_unsupported_x86_abi_mix() {
        let err = TargetSpec::parse("x86_64-unknown-linux-msvc").unwrap_err();
        assert_eq!(
            err.kind(),
            TargetSpecParseErrorKind::UnsupportedTargetCombination
        );
        assert!(
            err.to_string()
                .contains("unsupported target triple combination"),
            "unexpected parse error: {err}"
        );
    }

    #[test]
    fn test_target_spec_default_preserves_non_x86_legacy_identity() {
        // AArch64 now mirrors x86-64: the default OS/ABI resolves to the host triple.
        assert_eq!(
            TargetSpec::unknown_for_architecture(Target::Aarch64).with_default_os_abi(),
            TargetSpec::host_for_architecture(Target::Aarch64)
        );
        assert_eq!(
            TargetSpec::unknown_for_architecture(Target::Riscv64).with_default_os_abi(),
            TargetSpec::unknown_for_architecture(Target::Riscv64)
        );
    }
}
