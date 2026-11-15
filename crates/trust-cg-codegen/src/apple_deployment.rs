// trust-cg-codegen/apple_deployment.rs - Apple deployment target and Mach-O build version
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Apple deployment target of a Mach-O object and its `LC_BUILD_VERSION`.
//!
//! Every Mach-O object names the platform and the minimum OS version it was
//! built for. `ld64` compares each object's minimum with the link's own
//! deployment target and warns when an object claims a newer one, and the
//! loader refuses an executable whose minimum exceeds the running OS. The
//! value therefore has to come from the compilation target, not from a
//! constant:
//!
//! 1. the target triple's OS version (`aarch64-apple-macos12.0`,
//!    `arm64-apple-macosx13.3.1`), which a [`crate::target::TargetSpec`]
//!    carries as its Apple deployment target;
//! 2. otherwise `MACOSX_DEPLOYMENT_TARGET`, which drivers capture into the
//!    target spec (see [`capture_macosx_deployment_target`]) so the compile
//!    policy and artifact identity bind it -- the library never reads the
//!    process environment on its own;
//! 3. otherwise macOS 14.0, the value every object carried before the
//!    deployment target was modeled.
//!
//! Only the macOS platform is admitted. iOS, tvOS, watchOS, visionOS and
//! their simulators have different platform identifiers and SDK contracts
//! that no test here exercises, so their triples are refused rather than
//! stamped as macOS. A Darwin kernel version (`darwin23`) is refused too:
//! its mapping to a macOS release is not modeled.

use std::fmt;

/// Environment variable Apple toolchains read for the macOS deployment target.
pub const MACOSX_DEPLOYMENT_TARGET: &str = "MACOSX_DEPLOYMENT_TARGET";

/// `LC_BUILD_VERSION` platform identifier for macOS (`PLATFORM_MACOS`).
pub const MACHO_PLATFORM_MACOS: u32 = 1;

/// An Apple OS version `major.minor.patch`.
///
/// The Mach-O encoding packs it as `xxxx.yy.zz` nibbles
/// (`major << 16 | minor << 8 | patch`), so the major version is bounded by
/// 16 bits and the minor and patch versions by 8 bits each; a value outside
/// those bounds is refused at parse time rather than truncated.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AppleOsVersion {
    major: u16,
    minor: u8,
    patch: u8,
}

impl AppleOsVersion {
    /// macOS 11.0, the first release for Apple silicon (arm64).
    pub const MACOS_ARM64_FLOOR: Self = Self::new(11, 0, 0);
    /// macOS 10.0, the floor admitted for x86-64 Mach-O.
    pub const MACOS_X86_64_FLOOR: Self = Self::new(10, 0, 0);
    /// The minimum OS every Mach-O object carried before the deployment
    /// target was modeled; still the default when none is given.
    pub const DEFAULT_MACOS_MINIMUM: Self = Self::new(14, 0, 0);

    /// A version from its components.
    #[must_use]
    pub const fn new(major: u16, minor: u8, patch: u8) -> Self {
        Self {
            major,
            minor,
            patch,
        }
    }

    /// Major version.
    #[must_use]
    pub const fn major(self) -> u16 {
        self.major
    }

    /// Minor version.
    #[must_use]
    pub const fn minor(self) -> u8 {
        self.minor
    }

    /// Patch version.
    #[must_use]
    pub const fn patch(self) -> u8 {
        self.patch
    }

    /// The `LC_BUILD_VERSION` / `LC_VERSION_MIN_*` nibble encoding.
    #[must_use]
    pub const fn macho_encoding(self) -> u32 {
        ((self.major as u32) << 16) | ((self.minor as u32) << 8) | self.patch as u32
    }

    /// Decode the Mach-O nibble encoding.
    #[must_use]
    pub const fn from_macho_encoding(encoded: u32) -> Self {
        Self::new(
            (encoded >> 16) as u16,
            ((encoded >> 8) & 0xff) as u8,
            (encoded & 0xff) as u8,
        )
    }

    /// Parse `major[.minor[.patch]]`, each component ASCII decimal digits.
    ///
    /// Empty text, an empty or non-decimal component, a sign, surrounding
    /// whitespace, more than three components and a component outside the
    /// Mach-O encoding's range are refused. A zero major version is refused:
    /// no Apple OS has one.
    pub fn parse(text: &str) -> Result<Self, &'static str> {
        if text.is_empty() {
            return Err("the version is empty");
        }
        let components: Vec<&str> = text.split('.').collect();
        if components.len() > 3 {
            return Err("a version has at most three components (major.minor.patch)");
        }
        let mut values = [0u32; 3];
        for (slot, component) in values.iter_mut().zip(&components) {
            if component.is_empty() || !component.bytes().all(|byte| byte.is_ascii_digit()) {
                return Err("every version component must be one or more ASCII decimal digits");
            }
            // Six digits bound the value far below u32::MAX before the
            // component-specific range checks below.
            if component.len() > 6 {
                return Err("a version component is out of range");
            }
            *slot = component
                .parse()
                .map_err(|_| "a version component is out of range")?;
        }
        let [major, minor, patch] = values;
        let major = u16::try_from(major)
            .map_err(|_| "the major version exceeds the Mach-O encoding (65535)")?;
        let minor = u8::try_from(minor)
            .map_err(|_| "the minor version exceeds the Mach-O encoding (255)")?;
        let patch = u8::try_from(patch)
            .map_err(|_| "the patch version exceeds the Mach-O encoding (255)")?;
        if major == 0 {
            return Err("the major version is zero");
        }
        Ok(Self::new(major, minor, patch))
    }
}

impl fmt::Display for AppleOsVersion {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.patch == 0 {
            write!(formatter, "{}.{}", self.major, self.minor)
        } else {
            write!(formatter, "{}.{}.{}", self.major, self.minor, self.patch)
        }
    }
}

/// Where a Mach-O minimum OS version came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AppleDeploymentTargetSource {
    /// The target triple's OS version component.
    TargetTriple,
    /// `MACOSX_DEPLOYMENT_TARGET`, captured by a driver.
    Environment,
    /// Neither was given: [`AppleOsVersion::DEFAULT_MACOS_MINIMUM`].
    Default,
}

impl AppleDeploymentTargetSource {
    /// Stable lowercase label for diagnostics.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            Self::TargetTriple => "target triple",
            Self::Environment => MACOSX_DEPLOYMENT_TARGET,
            Self::Default => "default",
        }
    }
}

/// A refused Apple deployment target. Every variant carries the
/// `[TCG-MACHO-DEPLOYMENT]` tag.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum AppleDeploymentTargetError {
    /// The version text does not parse.
    #[error(
        "[TCG-MACHO-DEPLOYMENT] malformed macOS deployment target `{value}` from {}: {reason}",
        .origin.label()
    )]
    Malformed {
        /// Where the text came from.
        origin: AppleDeploymentTargetSource,
        /// The refused text.
        value: String,
        /// Why it was refused.
        reason: &'static str,
    },
    /// The version predates the architecture's first macOS release.
    #[error(
        "[TCG-MACHO-DEPLOYMENT] macOS deployment target {version} from {} predates {architecture} \
         macOS support ({floor}); a Mach-O object cannot claim it",
        .origin.label()
    )]
    BelowArchitectureFloor {
        /// Where the version came from.
        origin: AppleDeploymentTargetSource,
        /// The refused version.
        version: AppleOsVersion,
        /// The architecture's first supported release.
        floor: AppleOsVersion,
        /// Mach-O architecture name.
        architecture: &'static str,
    },
    /// The triple names an Apple platform other than macOS, or a Darwin
    /// kernel version whose macOS release is not modeled.
    #[error(
        "[TCG-MACHO-DEPLOYMENT] target triple `{triple}` names OS `{os}`: only macOS Mach-O \
         objects are emitted (spell the target as <arch>-apple-darwin or \
         <arch>-apple-macos<version>)"
    )]
    UnsupportedPlatform {
        /// The refused triple.
        triple: String,
        /// Its OS component.
        os: String,
    },
    /// A deployment target was attached to a non-Apple target.
    #[error(
        "[TCG-MACHO-DEPLOYMENT] target `{triple}` is not an Apple target; it has no macOS deployment target"
    )]
    NotAnAppleTarget {
        /// The target triple.
        triple: String,
    },
}

/// The `LC_BUILD_VERSION` contents of one Mach-O object.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MachOBuildVersion {
    minimum_os: AppleOsVersion,
    source: AppleDeploymentTargetSource,
}

impl MachOBuildVersion {
    /// The build version every object carried before the deployment target
    /// was modeled: macOS 14.0. Object emission uses no SDK.
    pub const DEFAULT: Self = Self {
        minimum_os: AppleOsVersion::DEFAULT_MACOS_MINIMUM,
        source: AppleDeploymentTargetSource::Default,
    };

    /// A macOS build version after checking the architecture floor.
    ///
    /// `architecture` is the triple's architecture component (`aarch64`,
    /// `arm64` or `x86_64`); any other architecture has no Mach-O floor here
    /// and is refused as a platform the Mach-O writers do not emit.
    pub fn macos(
        architecture: &str,
        minimum_os: AppleOsVersion,
        source: AppleDeploymentTargetSource,
    ) -> Result<Self, AppleDeploymentTargetError> {
        let (floor, name) = match architecture {
            "aarch64" | "arm64" => (AppleOsVersion::MACOS_ARM64_FLOOR, "arm64"),
            "x86_64" => (AppleOsVersion::MACOS_X86_64_FLOOR, "x86_64"),
            other => {
                return Err(AppleDeploymentTargetError::UnsupportedPlatform {
                    triple: format!("{other}-apple-macos"),
                    os: "macos".to_owned(),
                });
            }
        };
        if minimum_os < floor {
            return Err(AppleDeploymentTargetError::BelowArchitectureFloor {
                origin: source,
                version: minimum_os,
                floor,
                architecture: name,
            });
        }
        Ok(Self { minimum_os, source })
    }

    /// The build version a Mach-O object for `target_triple` carries.
    ///
    /// The OS component decides: `darwin`, `macos` and `macosx` without a
    /// version take [`Self::DEFAULT`]; `macos<version>`/`macosx<version>`
    /// take that version. Any other Apple OS (iOS, tvOS, watchOS, visionOS,
    /// a Darwin kernel version) and a malformed version are refused. The
    /// process environment is not consulted: drivers capture
    /// `MACOSX_DEPLOYMENT_TARGET` into the target spec, whose canonical
    /// triple then carries the version.
    pub fn for_target_triple(target_triple: &str) -> Result<Self, AppleDeploymentTargetError> {
        let mut components = target_triple.trim().split('-');
        let architecture = components.next().unwrap_or_default();
        let _vendor = components.next();
        let os = components.next().unwrap_or_default().to_ascii_lowercase();
        if matches!(os.as_str(), "darwin" | "macos" | "macosx") {
            return Self::macos(
                architecture,
                AppleOsVersion::DEFAULT_MACOS_MINIMUM,
                AppleDeploymentTargetSource::Default,
            );
        }
        let versioned = os
            .strip_prefix("macosx")
            .or_else(|| os.strip_prefix("macos"));
        let Some(version_text) = versioned else {
            return Err(AppleDeploymentTargetError::UnsupportedPlatform {
                triple: target_triple.to_owned(),
                os,
            });
        };
        let version = AppleOsVersion::parse(version_text).map_err(|reason| {
            AppleDeploymentTargetError::Malformed {
                origin: AppleDeploymentTargetSource::TargetTriple,
                value: version_text.to_owned(),
                reason,
            }
        })?;
        Self::macos(
            architecture,
            version,
            AppleDeploymentTargetSource::TargetTriple,
        )
    }

    /// Platform identifier (`PLATFORM_MACOS`).
    #[must_use]
    pub const fn platform(self) -> u32 {
        MACHO_PLATFORM_MACOS
    }

    /// Minimum OS version.
    #[must_use]
    pub const fn minimum_os(self) -> AppleOsVersion {
        self.minimum_os
    }

    /// Recorded SDK version: zero, because object emission uses no SDK.
    ///
    /// A deployment minimum is not an SDK identity. Do not turn it into an
    /// invented SDK version or retain the historical 14.0 placeholder. This
    /// matches LLVM's object field when no SDK version was supplied; final
    /// linking and any SDK selection there remain the link driver's job.
    #[must_use]
    pub const fn sdk(self) -> AppleOsVersion {
        AppleOsVersion::new(0, 0, 0)
    }

    /// Where the minimum OS version came from.
    #[must_use]
    pub const fn source(self) -> AppleDeploymentTargetSource {
        self.source
    }
}

impl Default for MachOBuildVersion {
    fn default() -> Self {
        Self::DEFAULT
    }
}

/// Parse a captured `MACOSX_DEPLOYMENT_TARGET` value.
///
/// `None` (unset) yields `Ok(None)`. A set value must parse, including when
/// it is empty or not valid UTF-8; there is no silent fallback to the
/// default. The architecture floor is checked when the version is attached
/// to a target spec.
pub fn parse_macosx_deployment_target(
    value: Option<&std::ffi::OsStr>,
) -> Result<Option<AppleOsVersion>, AppleDeploymentTargetError> {
    let Some(value) = value else {
        return Ok(None);
    };
    let text = value
        .to_str()
        .ok_or_else(|| AppleDeploymentTargetError::Malformed {
            origin: AppleDeploymentTargetSource::Environment,
            value: value.to_string_lossy().into_owned(),
            reason: "the value is not valid UTF-8",
        })?;
    AppleOsVersion::parse(text)
        .map(Some)
        .map_err(|reason| AppleDeploymentTargetError::Malformed {
            origin: AppleDeploymentTargetSource::Environment,
            value: text.to_owned(),
            reason,
        })
}

/// Read `MACOSX_DEPLOYMENT_TARGET` (through the thread-local override layer
/// of `trust_cg_process_env`) and parse it for a driver to capture.
///
/// Drivers call this once and attach the result to the target spec with
/// [`crate::target::TargetSpec::with_macos_deployment_target_from_environment`];
/// the compiler library itself never reads the variable.
pub fn capture_macosx_deployment_target()
-> Result<Option<AppleOsVersion>, AppleDeploymentTargetError> {
    parse_macosx_deployment_target(
        trust_cg_process_env::var_os(MACOSX_DEPLOYMENT_TARGET).as_deref(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn versions_parse_and_encode_as_macho_nibbles() {
        for (text, expected, encoded) in [
            ("14", AppleOsVersion::new(14, 0, 0), 0x000E_0000),
            ("14.0", AppleOsVersion::new(14, 0, 0), 0x000E_0000),
            ("12.3", AppleOsVersion::new(12, 3, 0), 0x000C_0300),
            ("13.3.1", AppleOsVersion::new(13, 3, 1), 0x000D_0301),
            ("10.15", AppleOsVersion::new(10, 15, 0), 0x000A_0F00),
            ("26.0", AppleOsVersion::new(26, 0, 0), 0x001A_0000),
        ] {
            let version = AppleOsVersion::parse(text).unwrap();
            assert_eq!(version, expected, "{text}");
            assert_eq!(version.macho_encoding(), encoded, "{text}");
            assert_eq!(AppleOsVersion::from_macho_encoding(encoded), expected);
        }
        assert_eq!(AppleOsVersion::new(13, 3, 1).to_string(), "13.3.1");
        assert_eq!(AppleOsVersion::new(12, 0, 0).to_string(), "12.0");
    }

    #[test]
    fn malformed_versions_are_refused() {
        for text in [
            "", ".", "14.", ".1", "14..0", "14.0.0.0", "+14", "-14", " 14", "14 ", "14.x", "0",
            "0.9", "65536", "14.256", "14.0.256", "1e3", "１４", "9999999",
        ] {
            assert!(
                AppleOsVersion::parse(text).is_err(),
                "{text:?} must be refused"
            );
        }
        assert_eq!(
            AppleOsVersion::parse("65535.255.255").unwrap(),
            AppleOsVersion::new(65535, 255, 255)
        );
    }

    #[test]
    fn build_version_follows_the_triple_version() {
        let default = MachOBuildVersion::for_target_triple("aarch64-apple-darwin").unwrap();
        assert_eq!(default, MachOBuildVersion::DEFAULT);
        assert_eq!(default.minimum_os(), AppleOsVersion::new(14, 0, 0));
        assert_eq!(default.sdk(), AppleOsVersion::new(0, 0, 0));
        assert_eq!(default.platform(), MACHO_PLATFORM_MACOS);

        let twelve = MachOBuildVersion::for_target_triple("aarch64-apple-macos12.0").unwrap();
        assert_eq!(twelve.minimum_os(), AppleOsVersion::new(12, 0, 0));
        assert_eq!(twelve.sdk(), AppleOsVersion::new(0, 0, 0));
        assert_eq!(twelve.source(), AppleDeploymentTargetSource::TargetTriple);

        let fifteen = MachOBuildVersion::for_target_triple("arm64-apple-macosx15.2.1").unwrap();
        assert_eq!(fifteen.minimum_os(), AppleOsVersion::new(15, 2, 1));
        assert_eq!(fifteen.sdk(), AppleOsVersion::new(0, 0, 0));

        let intel = MachOBuildVersion::for_target_triple("x86_64-apple-macos10.15").unwrap();
        assert_eq!(intel.minimum_os(), AppleOsVersion::new(10, 15, 0));
    }

    #[test]
    fn build_version_refuses_other_platforms_and_bad_versions() {
        for triple in [
            "arm64-apple-ios17.0",
            "arm64-apple-ios",
            "arm64-apple-tvos",
            "arm64-apple-watchos",
            "arm64-apple-xros",
            "aarch64-apple-darwin23",
            "aarch64-apple-darwin23.1.0",
            "aarch64-unknown-linux-gnu",
            "",
        ] {
            let error = MachOBuildVersion::for_target_triple(triple).unwrap_err();
            assert!(
                matches!(
                    error,
                    AppleDeploymentTargetError::UnsupportedPlatform { .. }
                ),
                "{triple}: {error}"
            );
            assert!(error.to_string().contains("[TCG-MACHO-DEPLOYMENT]"));
        }
        for triple in [
            "aarch64-apple-macos14..0",
            "aarch64-apple-macosx1x",
            "aarch64-apple-macos0",
        ] {
            assert!(matches!(
                MachOBuildVersion::for_target_triple(triple),
                Err(AppleDeploymentTargetError::Malformed { .. })
            ));
        }
        let below = MachOBuildVersion::for_target_triple("aarch64-apple-macos10.15").unwrap_err();
        assert!(matches!(
            below,
            AppleDeploymentTargetError::BelowArchitectureFloor {
                architecture: "arm64",
                ..
            }
        ));
    }

    #[test]
    fn environment_values_must_parse_when_set() {
        use std::ffi::OsStr;

        assert_eq!(parse_macosx_deployment_target(None).unwrap(), None);
        assert_eq!(
            parse_macosx_deployment_target(Some(OsStr::new("13.1"))).unwrap(),
            Some(AppleOsVersion::new(13, 1, 0))
        );
        for bad in ["", "13,1", "latest"] {
            let error = parse_macosx_deployment_target(Some(OsStr::new(bad))).unwrap_err();
            assert!(
                matches!(
                    error,
                    AppleDeploymentTargetError::Malformed {
                        origin: AppleDeploymentTargetSource::Environment,
                        ..
                    }
                ),
                "{bad:?}: {error}"
            );
        }
        trust_cg_process_env::with_env_overrides(&[(MACOSX_DEPLOYMENT_TARGET, "12.4")], || {
            assert_eq!(
                capture_macosx_deployment_target().unwrap(),
                Some(AppleOsVersion::new(12, 4, 0))
            );
        });
        trust_cg_process_env::with_env_overrides(&[(MACOSX_DEPLOYMENT_TARGET, "12.")], || {
            assert!(capture_macosx_deployment_target().is_err());
        });
        trust_cg_process_env::with_env_overrides_removed(&[MACOSX_DEPLOYMENT_TARGET], || {
            assert_eq!(capture_macosx_deployment_target().unwrap(), None);
        });
    }
}
