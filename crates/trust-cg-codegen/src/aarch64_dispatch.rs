// trust-cg-codegen/aarch64_dispatch.rs - AArch64 host features and runtime dispatch
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! AArch64 host feature resolution and runtime feature dispatch.
//!
//! A function compiled with its own target features (trust-ir
//! `FuncAttrs.target_features`, rustc's `#[target_feature(enable = ...)]`)
//! may execute only on a CPU that implements them, and choosing such a
//! function at run time is the caller's job. This module is that choice for
//! code this crate installs or links:
//!
//! * [`resolve_aarch64_features`] turns a feature probe into the modeled
//!   feature set. [`darwin_hw_optional`] is the Darwin probe
//!   (`sysctlbyname` on the `hw.optional.arm.FEAT_*` keys each
//!   [`AArch64IsaFeature::darwin_sysctl_keys`] names), and
//!   [`aarch64_host_features`] resolves the executing host once per process
//!   (Darwin: those sysctls; another AArch64 OS: the standard library's
//!   runtime detection; any other architecture: nothing).
//! * [`AArch64FeatureDispatch`] names feature-gated variants and one baseline
//!   and selects the first variant whose required features the resolved set
//!   covers, else the baseline.
//!   [`AArch64FeatureDispatch::from_trust_ir_module`] reads each variant's
//!   requirement from the function's own stated features, so the dispatch and
//!   the compiled function cannot disagree about what the fast path needs.
//!
//! This is a run-time selection: it trusts the operating system's report of
//! the CPU, and proves nothing about the variants' agreement (the native
//! tests compare them).

use std::fmt;
use std::sync::OnceLock;

use trust_cg_ir::{AArch64IsaFeature, TargetFeatureSet, aarch64_function_target_features};

/// A set over the closed AArch64 feature domain.
pub type AArch64FeatureSet = TargetFeatureSet<AArch64IsaFeature>;

/// Read one integer Darwin `sysctl` by name (`hw.optional.arm.FEAT_CRC32`).
///
/// `None` when the key does not exist on this kernel, when its value is not a
/// 4- or 8-byte integer, and on every non-Darwin host.
#[cfg(target_os = "macos")]
pub fn darwin_hw_optional(key: &str) -> Option<u64> {
    let name = std::ffi::CString::new(key).ok()?;
    let mut value = [0_u8; 8];
    let mut len = value.len();
    // SAFETY: `name` is NUL-terminated and outlives the call; `value` and
    // `len` describe one writable 8-byte buffer the kernel fills and resizes;
    // no new value is written (null `newp`, zero `newlen`).
    let status = unsafe {
        sysctlbyname(
            name.as_ptr(),
            value.as_mut_ptr().cast(),
            &mut len,
            std::ptr::null_mut(),
            0,
        )
    };
    if status != 0 {
        return None;
    }
    match len {
        4 => Some(u64::from(u32::from_ne_bytes([
            value[0], value[1], value[2], value[3],
        ]))),
        8 => Some(u64::from_ne_bytes(value)),
        _ => None,
    }
}

/// Read one integer Darwin `sysctl` by name: always `None` off Darwin.
#[cfg(not(target_os = "macos"))]
pub fn darwin_hw_optional(_key: &str) -> Option<u64> {
    None
}

#[cfg(target_os = "macos")]
unsafe extern "C" {
    fn sysctlbyname(
        name: *const std::ffi::c_char,
        oldp: *mut std::ffi::c_void,
        oldlenp: *mut usize,
        newp: *mut std::ffi::c_void,
        newlen: usize,
    ) -> i32;
}

/// The modeled features `probe` reports: a feature is present when every
/// sysctl key it names reads a nonzero value. A missing key is absence, so an
/// older kernel that does not know a feature fails closed.
pub fn resolve_aarch64_features(probe: impl Fn(&str) -> Option<u64>) -> AArch64FeatureSet {
    AArch64FeatureSet::from_aarch64_features(AArch64IsaFeature::ALL.into_iter().filter(|feature| {
        feature
            .darwin_sysctl_keys()
            .iter()
            .all(|key| probe(key).is_some_and(|value| value != 0))
    }))
}

/// The modeled features the Rust standard library's runtime detection
/// reports on this AArch64 host.
///
/// `flagm2` has no stable detection name and is reported absent (fail
/// closed); Darwin resolves it through its sysctl instead.
#[cfg(target_arch = "aarch64")]
pub fn std_detected_aarch64_features() -> AArch64FeatureSet {
    use std::arch::is_aarch64_feature_detected as detected;
    AArch64FeatureSet::from_aarch64_features(AArch64IsaFeature::ALL.into_iter().filter(|feature| {
        match feature {
            AArch64IsaFeature::Aes => detected!("aes"),
            AArch64IsaFeature::Bf16 => detected!("bf16"),
            AArch64IsaFeature::Crc => detected!("crc"),
            AArch64IsaFeature::Dit => detected!("dit"),
            AArch64IsaFeature::DotProd => detected!("dotprod"),
            AArch64IsaFeature::Dpb => detected!("dpb"),
            AArch64IsaFeature::Dpb2 => detected!("dpb2"),
            AArch64IsaFeature::Fcma => detected!("fcma"),
            AArch64IsaFeature::Fhm => detected!("fhm"),
            AArch64IsaFeature::FlagM => detected!("flagm"),
            AArch64IsaFeature::FlagM2 => false,
            AArch64IsaFeature::Fp16 => detected!("fp16"),
            AArch64IsaFeature::Frintts => detected!("frintts"),
            AArch64IsaFeature::I8mm => detected!("i8mm"),
            AArch64IsaFeature::Jsconv => detected!("jsconv"),
            AArch64IsaFeature::Lse => detected!("lse"),
            AArch64IsaFeature::Lse2 => detected!("lse2"),
            AArch64IsaFeature::Rcpc => detected!("rcpc"),
            AArch64IsaFeature::Rcpc2 => detected!("rcpc2"),
            AArch64IsaFeature::Rdm => detected!("rdm"),
            AArch64IsaFeature::Sb => detected!("sb"),
            AArch64IsaFeature::Sha2 => detected!("sha2"),
            AArch64IsaFeature::Sha3 => detected!("sha3"),
        }
    }))
}

/// Where the executing host's feature set came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AArch64FeatureSource {
    /// Darwin `hw.optional.arm.FEAT_*` sysctls ([`darwin_hw_optional`]).
    DarwinSysctl,
    /// The standard library's runtime detection (an AArch64 host other than
    /// Darwin).
    StdDetect,
    /// The host is not AArch64: no AArch64 feature executes here.
    NotAarch64,
}

/// The modeled AArch64 features the executing CPU implements.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AArch64HostFeatures {
    features: AArch64FeatureSet,
    source: AArch64FeatureSource,
}

impl AArch64HostFeatures {
    /// A report from an explicit resolution: a probe other than the live one,
    /// or a host view with features masked off (a dispatch or install control
    /// for a CPU this process does not run on).
    pub const fn new(features: AArch64FeatureSet, source: AArch64FeatureSource) -> Self {
        Self { features, source }
    }

    /// The implemented features.
    pub const fn features(self) -> AArch64FeatureSet {
        self.features
    }

    /// How they were resolved.
    pub const fn source(self) -> AArch64FeatureSource {
        self.source
    }

    /// Whether the host implements `feature`.
    pub fn implements(self, feature: AArch64IsaFeature) -> bool {
        self.features.contains(feature)
    }

    /// Whether the host implements every feature of `required`.
    pub fn implements_all(self, required: AArch64FeatureSet) -> bool {
        required.is_subset_of(self.features)
    }

    /// Implemented feature names in canonical order.
    pub fn names(self) -> Vec<&'static str> {
        self.features
            .enabled()
            .map(AArch64IsaFeature::name)
            .collect()
    }
}

/// The executing host's features, resolved on first use and then fixed for
/// the process (a CPU does not gain or lose features while it runs).
pub fn aarch64_host_features() -> AArch64HostFeatures {
    static HOST: OnceLock<AArch64HostFeatures> = OnceLock::new();
    *HOST.get_or_init(detect_aarch64_host_features)
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn detect_aarch64_host_features() -> AArch64HostFeatures {
    AArch64HostFeatures {
        features: resolve_aarch64_features(darwin_hw_optional),
        source: AArch64FeatureSource::DarwinSysctl,
    }
}

#[cfg(all(target_arch = "aarch64", not(target_os = "macos")))]
fn detect_aarch64_host_features() -> AArch64HostFeatures {
    AArch64HostFeatures {
        features: std_detected_aarch64_features(),
        source: AArch64FeatureSource::StdDetect,
    }
}

#[cfg(not(target_arch = "aarch64"))]
fn detect_aarch64_host_features() -> AArch64HostFeatures {
    AArch64HostFeatures {
        features: AArch64FeatureSet::EMPTY,
        source: AArch64FeatureSource::NotAarch64,
    }
}

/// One feature-gated variant of a dispatched function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AArch64DispatchVariant {
    symbol: String,
    required: AArch64FeatureSet,
}

impl AArch64DispatchVariant {
    /// The variant's symbol.
    pub fn symbol(&self) -> &str {
        &self.symbol
    }

    /// The features it requires.
    pub const fn required(&self) -> AArch64FeatureSet {
        self.required
    }
}

/// The variant [`AArch64FeatureDispatch::select`] chose.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AArch64DispatchChoice<'a> {
    /// The chosen symbol.
    pub symbol: &'a str,
    /// The features it requires (empty for the baseline).
    pub required: AArch64FeatureSet,
    /// The index of the chosen variant, `None` for the baseline.
    pub variant: Option<usize>,
}

impl AArch64DispatchChoice<'_> {
    /// Whether the baseline fallback was chosen.
    pub const fn is_baseline(&self) -> bool {
        self.variant.is_none()
    }
}

/// Why a dispatch could not be built from a module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AArch64DispatchError {
    /// No function with this name (or it has no body).
    MissingFunction { symbol: String },
    /// A function states a feature this backend does not model.
    UnmodeledFeature { symbol: String, feature: String },
    /// The baseline states optional features, so it is not a fallback.
    BaselineStatesFeatures {
        symbol: String,
        features: Vec<&'static str>,
    },
    /// A variant states no optional feature, so it gates nothing.
    VariantStatesNoFeature { symbol: String },
    /// A symbol is named twice.
    DuplicateSymbol { symbol: String },
}

impl fmt::Display for AArch64DispatchError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingFunction { symbol } => {
                write!(f, "[TCG-DISPATCH] no function body named `{symbol}`")
            }
            Self::UnmodeledFeature { symbol, feature } => write!(
                f,
                "[TCG-DISPATCH] function `{symbol}` states target feature `{feature}`, which is \
                 not an AArch64 feature this backend models"
            ),
            Self::BaselineStatesFeatures { symbol, features } => write!(
                f,
                "[TCG-DISPATCH] baseline `{symbol}` states optional features {features:?}; a \
                 fallback must run on every AArch64 CPU"
            ),
            Self::VariantStatesNoFeature { symbol } => write!(
                f,
                "[TCG-DISPATCH] variant `{symbol}` states no optional feature, so it gates nothing"
            ),
            Self::DuplicateSymbol { symbol } => {
                write!(f, "[TCG-DISPATCH] `{symbol}` is named twice")
            }
        }
    }
}

impl std::error::Error for AArch64DispatchError {}

/// A runtime choice among feature-gated variants and one baseline fallback.
///
/// Variants are tried in the order given (put the most demanding first); the
/// first whose required features the resolved set covers wins, else the
/// baseline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AArch64FeatureDispatch {
    variants: Vec<AArch64DispatchVariant>,
    baseline: String,
}

impl AArch64FeatureDispatch {
    /// A dispatch whose only choice is `baseline`.
    pub fn new(baseline: impl Into<String>) -> Self {
        Self {
            variants: Vec::new(),
            baseline: baseline.into(),
        }
    }

    /// Add a variant requiring `required`, tried after those already added.
    pub fn with_variant(mut self, symbol: impl Into<String>, required: AArch64FeatureSet) -> Self {
        self.variants.push(AArch64DispatchVariant {
            symbol: symbol.into(),
            required,
        });
        self
    }

    /// Build a dispatch over functions of `module`: each variant requires
    /// exactly the optional features its body states, and the baseline must
    /// state none.
    pub fn from_trust_ir_module(
        module: &trust_ir::Module,
        variants: &[&str],
        baseline: &str,
    ) -> Result<Self, AArch64DispatchError> {
        let stated = |symbol: &str| -> Result<AArch64FeatureSet, AArch64DispatchError> {
            let function = module
                .functions
                .iter()
                .find(|function| function.name == symbol && !function.blocks.is_empty())
                .ok_or_else(|| AArch64DispatchError::MissingFunction {
                    symbol: symbol.to_owned(),
                })?;
            aarch64_function_target_features(
                function.attrs.target_features.iter().map(String::as_str),
            )
            .map_err(|feature| AArch64DispatchError::UnmodeledFeature {
                symbol: symbol.to_owned(),
                feature: feature.to_owned(),
            })
        };
        let mut seen = std::collections::BTreeSet::new();
        for symbol in variants.iter().copied().chain([baseline]) {
            if !seen.insert(symbol) {
                return Err(AArch64DispatchError::DuplicateSymbol {
                    symbol: symbol.to_owned(),
                });
            }
        }
        let baseline_features = stated(baseline)?;
        if !baseline_features.is_empty() {
            return Err(AArch64DispatchError::BaselineStatesFeatures {
                symbol: baseline.to_owned(),
                features: baseline_features
                    .enabled()
                    .map(AArch64IsaFeature::name)
                    .collect(),
            });
        }
        let mut dispatch = Self::new(baseline);
        for &symbol in variants {
            let required = stated(symbol)?;
            if required.is_empty() {
                return Err(AArch64DispatchError::VariantStatesNoFeature {
                    symbol: symbol.to_owned(),
                });
            }
            dispatch = dispatch.with_variant(symbol, required);
        }
        Ok(dispatch)
    }

    /// The variants, in trial order.
    pub fn variants(&self) -> &[AArch64DispatchVariant] {
        &self.variants
    }

    /// The baseline fallback's symbol.
    pub fn baseline(&self) -> &str {
        &self.baseline
    }

    /// The first variant `available` covers, else the baseline.
    pub fn select(&self, available: AArch64FeatureSet) -> AArch64DispatchChoice<'_> {
        self.variants
            .iter()
            .enumerate()
            .find(|(_, variant)| variant.required.is_subset_of(available))
            .map_or(
                AArch64DispatchChoice {
                    symbol: &self.baseline,
                    required: AArch64FeatureSet::EMPTY,
                    variant: None,
                },
                |(index, variant)| AArch64DispatchChoice {
                    symbol: &variant.symbol,
                    required: variant.required,
                    variant: Some(index),
                },
            )
    }

    /// [`Self::select`] against the executing host ([`aarch64_host_features`]).
    pub fn select_for_host(&self) -> AArch64DispatchChoice<'_> {
        self.select(aarch64_host_features().features())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn set(features: &[AArch64IsaFeature]) -> AArch64FeatureSet {
        AArch64FeatureSet::from_aarch64_features(features.iter().copied())
    }

    /// A feature is present only when every key it names reads nonzero; an
    /// unknown key is absence.
    #[test]
    fn resolution_requires_every_named_key() {
        let probe = |key: &str| match key {
            "hw.optional.arm.FEAT_CRC32" => Some(1),
            "hw.optional.arm.FEAT_AES" => Some(1),
            "hw.optional.arm.FEAT_PMULL" => Some(0),
            "hw.optional.arm.FEAT_SHA1" | "hw.optional.arm.FEAT_SHA256" => Some(1),
            "hw.optional.arm.FEAT_LSE" => Some(2),
            _ => None,
        };
        assert_eq!(
            resolve_aarch64_features(probe),
            set(&[
                AArch64IsaFeature::Crc,
                AArch64IsaFeature::Lse,
                AArch64IsaFeature::Sha2
            ])
        );
        assert_eq!(resolve_aarch64_features(|_| None), AArch64FeatureSet::EMPTY);
    }

    #[test]
    fn dispatch_selects_the_first_covered_variant_else_the_baseline() {
        let dispatch = AArch64FeatureDispatch::new("base")
            .with_variant(
                "crc_lse",
                set(&[AArch64IsaFeature::Crc, AArch64IsaFeature::Lse]),
            )
            .with_variant("crc", set(&[AArch64IsaFeature::Crc]));
        let all = set(&[AArch64IsaFeature::Crc, AArch64IsaFeature::Lse]);
        assert_eq!(dispatch.select(all).symbol, "crc_lse");
        assert_eq!(dispatch.select(all).variant, Some(0));
        let crc_only = set(&[AArch64IsaFeature::Crc]);
        assert_eq!(dispatch.select(crc_only).symbol, "crc");
        let none = dispatch.select(AArch64FeatureSet::EMPTY);
        assert_eq!(none.symbol, "base");
        assert!(none.is_baseline());
        assert!(none.required.is_empty());
    }

    #[test]
    fn host_resolution_is_stable_and_names_its_source() {
        let first = aarch64_host_features();
        assert_eq!(first, aarch64_host_features());
        let expected = if cfg!(all(target_arch = "aarch64", target_os = "macos")) {
            AArch64FeatureSource::DarwinSysctl
        } else if cfg!(target_arch = "aarch64") {
            AArch64FeatureSource::StdDetect
        } else {
            AArch64FeatureSource::NotAarch64
        };
        assert_eq!(first.source(), expected);
        if !cfg!(target_arch = "aarch64") {
            assert!(first.features().is_empty());
        }
    }
}
