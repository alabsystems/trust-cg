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

use trust_cg_ir::aarch64_regs;
use trust_cg_ir::riscv_regs;
use trust_cg_ir::x86_64_regs;

/// Supported target architectures.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Target {
    /// x86-64 (AMD64)
    X86_64,
    /// AArch64 (ARM64)
    Aarch64,
    /// RISC-V 64-bit
    Riscv64,
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
    pub fn with_default_os_abi(self) -> Self {
        if self.has_explicit_os_abi() {
            self
        } else {
            Self::default_for_architecture(self.architecture)
        }
    }

    /// Whether the caller provided OS/ABI/vendor information beyond an arch alias.
    pub fn has_explicit_os_abi(self) -> bool {
        self.origin == TargetSpecOrigin::ExplicitComponents
    }

    /// Canonical target triple for this spec.
    pub fn triple(self) -> String {
        let arch = self.architecture.name();
        let vendor = self.vendor.triple_component();
        let os = self.operating_system.triple_component();
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
            | TargetSpecParseErrorKind::UnsupportedTargetCombination => "unsupported target",
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
        let operating_system = parse_target_operating_system(parts[2], input)?;
        let environment = if parts.len() == 4 {
            parse_target_environment(parts[3], input)?
        } else {
            TargetEnvironment::Unknown
        };
        let spec = Self::new(architecture, vendor, operating_system, environment);
        validate_target_spec(spec, input)?;
        Ok(spec)
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

fn parse_target_operating_system(
    component: &str,
    input: &str,
) -> Result<TargetOperatingSystem, TargetSpecParseError> {
    match component {
        "unknown" => Ok(TargetOperatingSystem::Unknown),
        "linux" => Ok(TargetOperatingSystem::Linux),
        "darwin" | "macos" => Ok(TargetOperatingSystem::Darwin),
        "windows" => Ok(TargetOperatingSystem::Windows),
        _ => Err(TargetSpecParseError::new(
            input,
            TargetSpecParseErrorKind::UnsupportedOperatingSystem,
            "unsupported operating system; supported OS values are unknown, linux, darwin, windows",
        )),
    }
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

impl Target {
    /// Returns the pointer size in bytes for this target.
    pub fn pointer_bytes(self) -> u32 {
        match self {
            Target::X86_64 | Target::Aarch64 | Target::Riscv64 => 8,
        }
    }

    /// Returns the name of this target.
    pub fn name(self) -> &'static str {
        match self {
            Target::X86_64 => "x86_64",
            Target::Aarch64 => "aarch64",
            Target::Riscv64 => "riscv64",
        }
    }

    /// Returns the required stack alignment in bytes.
    pub fn stack_alignment(self) -> u32 {
        match self {
            // Both x86-64 System V and AArch64 require 16-byte stack alignment.
            Target::X86_64 | Target::Aarch64 => 16,
            // RISC-V: 16-byte alignment for RV64.
            Target::Riscv64 => 16,
        }
    }

    /// Returns the number of integer argument-passing registers.
    pub fn num_arg_gprs(self) -> usize {
        match self {
            Target::X86_64 => x86_64_regs::X86_ARG_GPRS.len(), // 6 (RDI,RSI,RDX,RCX,R8,R9)
            Target::Aarch64 => aarch64_regs::ARG_GPRS.len(),   // 8 (X0-X7)
            Target::Riscv64 => riscv_regs::RISCV_ARG_GPRS.len(), // a0-a7
        }
    }

    /// Returns the number of floating-point argument-passing registers.
    pub fn num_arg_fprs(self) -> usize {
        match self {
            Target::X86_64 => x86_64_regs::X86_ARG_XMMS.len(), // 8 (XMM0-XMM7)
            Target::Aarch64 => aarch64_regs::ARG_FPRS.len(),   // 8 (V0-V7)
            Target::Riscv64 => riscv_regs::RISCV_ARG_FPRS.len(), // fa0-fa7
        }
    }

    /// Returns the number of callee-saved GPRs.
    pub fn num_callee_saved_gprs(self) -> usize {
        match self {
            Target::X86_64 => x86_64_regs::X86_CALLEE_SAVED_GPRS.len(), // 6 (RBX,RBP,R12-R15)
            Target::Aarch64 => aarch64_regs::CALLEE_SAVED_GPRS.len(),   // 10 (X19-X28)
            Target::Riscv64 => riscv_regs::RISCV_CALLEE_SAVED_GPRS.len(), // s0-s11
        }
    }

    /// Returns the number of allocatable GPRs.
    pub fn num_allocatable_gprs(self) -> usize {
        match self {
            Target::X86_64 => x86_64_regs::X86_ALLOCATABLE_GPRS.len(), // 14
            Target::Aarch64 => aarch64_regs::ALLOCATABLE_GPRS.len(),   // 25
            Target::Riscv64 => riscv_regs::RISCV_ALLOCATABLE_GPRS.len(),
        }
    }

    /// Returns true if this target uses a frame pointer by default.
    ///
    /// Apple AArch64 always requires a frame pointer. x86-64 can omit it
    /// with -fomit-frame-pointer but we default to using it.
    pub fn requires_frame_pointer(self) -> bool {
        match self {
            Target::Aarch64 => true, // Apple AArch64 mandate
            Target::X86_64 => false, // Optional, but recommended
            Target::Riscv64 => false,
        }
    }

    /// Returns the target architecture of the host process.
    ///
    /// This is determined at compile time via `cfg(target_arch = ...)`.
    /// Used by front-end APIs (e.g. `tla-trust-cg`) to default to host codegen
    /// without hard-coding a specific target.
    ///
    /// Returns `Target::Aarch64` on unknown architectures as a safe default,
    /// since AArch64 is Trust Codegen's primary/most-tested backend.
    pub fn host() -> Self {
        #[cfg(target_arch = "x86_64")]
        {
            Target::X86_64
        }
        #[cfg(target_arch = "aarch64")]
        {
            Target::Aarch64
        }
        #[cfg(target_arch = "riscv64")]
        {
            Target::Riscv64
        }
        #[cfg(not(any(
            target_arch = "x86_64",
            target_arch = "aarch64",
            target_arch = "riscv64",
        )))]
        {
            Target::Aarch64
        }
    }

    /// Returns the calling convention description for this target.
    pub fn calling_convention(self) -> CallingConvention {
        match self {
            Target::Aarch64 => CallingConvention {
                name: "aapcs64",
                num_arg_gprs: 8,
                num_arg_fprs: 8,
                num_ret_gprs: 8,
                num_ret_fprs: 8,
                red_zone_size: 128,
                shadow_space: 0,
            },
            Target::X86_64 => CallingConvention {
                name: "sysv_amd64",
                num_arg_gprs: 6,
                num_arg_fprs: 8,
                num_ret_gprs: 2,
                num_ret_fprs: 2,
                red_zone_size: 128, // System V AMD64 has a 128-byte red zone
                shadow_space: 0,    // No shadow space in System V (Windows x64 has 32 bytes)
            },
            Target::Riscv64 => CallingConvention {
                name: "riscv_lp64d",
                num_arg_gprs: 8,
                num_arg_fprs: 8,
                num_ret_gprs: 2,
                num_ret_fprs: 2,
                red_zone_size: 0, // RISC-V has no red zone
                shadow_space: 0,
            },
        }
    }
}

/// Describes a calling convention's key parameters.
///
/// This is a target-generic description that captures the essential
/// constraints for ABI lowering, without being tied to specific register types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CallingConvention {
    /// Name of the calling convention (e.g., "sysv_amd64", "aapcs64").
    pub name: &'static str,
    /// Number of integer/pointer argument-passing registers.
    pub num_arg_gprs: usize,
    /// Number of floating-point argument-passing registers.
    pub num_arg_fprs: usize,
    /// Number of integer return-value registers.
    pub num_ret_gprs: usize,
    /// Number of floating-point return-value registers.
    pub num_ret_fprs: usize,
    /// Red zone size in bytes (area below SP that leaf functions may use).
    pub red_zone_size: u32,
    /// Shadow space / home space required above return address (Windows x64 = 32, others = 0).
    pub shadow_space: u32,
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

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
