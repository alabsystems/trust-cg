// trust-cg-codegen/runtime_deps.rs - Per-object runtime-dependency manifest
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Per-object runtime-dependency manifest.
//!
//! A manifest lists every named undefined symbol an emitted relocatable object
//! references, read back from the object bytes (ELF through the reparse gate's
//! independent reader, Mach-O through the in-crate parser), and groups each
//! symbol by the runtime component expected to define it: the memory
//! intrinsics, the C library, the math library, the compiler support library
//! (libgcc or compiler-rt builtins), the unwinder, an exception-handling
//! personality routine, or the thread-local-storage runtime.
//!
//! Classification is an explicit name table. A name the table does not know is
//! [`RuntimeProvider::External`]: another object, a user-named library or the
//! program itself. The table records the conventional provider of each name; it
//! is not a claim that a particular installed library exports the symbol. The
//! native link controls in `tests/e2e_aarch64_link_runtime.rs` check the
//! manifest against the symbols a real `-nostdlib` link reports missing.

use std::collections::BTreeSet;
use std::fmt;

/// The container format of an object read by [`RuntimeDependencyManifest`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ObjectFormat {
    /// ELF64 relocatable object.
    Elf,
    /// Mach-O 64-bit `MH_OBJECT`.
    MachO,
}

impl ObjectFormat {
    /// Stable lowercase name used in manifests.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Elf => "elf",
            Self::MachO => "macho",
        }
    }
}

/// The runtime component conventionally defining an undefined symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RuntimeProvider {
    /// `memcpy`, `memmove`, `memset`, `memcmp`, `bcmp`: required even by
    /// freestanding (`-nostdlib`) links, where the program must supply them.
    MemoryIntrinsics,
    /// C library routines: allocation, process exit, the stack-protector
    /// guard and failure routine, and basic I/O.
    Libc,
    /// C math library routines (`fmod`, `fmodf`, `sin`, ...).
    Libm,
    /// Compiler support library helpers (libgcc or compiler-rt builtins):
    /// 128-bit division and conversions, `__powi*`, half-precision
    /// conversions, binary128 arithmetic and the `__aarch64_*` outline atomics.
    CompilerRuntime,
    /// Itanium-ABI unwinder entry points (`_Unwind_*`).
    Unwinder,
    /// Exception-handling personality routines.
    EhPersonality,
    /// Thread-local-storage runtime (`__tls_get_addr`, Darwin
    /// `_tlv_bootstrap`).
    TlsRuntime,
    /// Not a recognized runtime symbol.
    External,
}

impl RuntimeProvider {
    /// Every provider, in manifest order.
    pub const ALL: [Self; 8] = [
        Self::MemoryIntrinsics,
        Self::Libc,
        Self::Libm,
        Self::CompilerRuntime,
        Self::Unwinder,
        Self::EhPersonality,
        Self::TlsRuntime,
        Self::External,
    ];

    /// Stable snake-case name used in manifests.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::MemoryIntrinsics => "memory_intrinsics",
            Self::Libc => "libc",
            Self::Libm => "libm",
            Self::CompilerRuntime => "compiler_runtime",
            Self::Unwinder => "unwinder",
            Self::EhPersonality => "eh_personality",
            Self::TlsRuntime => "tls_runtime",
            Self::External => "external",
        }
    }

    /// The library that conventionally supplies this provider's symbols for
    /// objects of `format` (ELF: GNU/Linux; Mach-O: Darwin).
    pub fn library_hint(self, format: ObjectFormat) -> &'static str {
        match (self, format) {
            (Self::MemoryIntrinsics, ObjectFormat::Elf) => {
                "C library (glibc libc.so.6 or musl libc); a -nostdlib link must supply them"
            }
            (Self::Libc, ObjectFormat::Elf) => {
                "C library (glibc libc.so.6, whose loader ld-linux-aarch64.so.1 defines __stack_chk_guard, or musl libc)"
            }
            (Self::Libm, ObjectFormat::Elf) => "C math library (libm, -lm)",
            (Self::CompilerRuntime, ObjectFormat::Elf) => {
                "compiler support library (libgcc.a or compiler-rt builtins)"
            }
            (Self::Unwinder, ObjectFormat::Elf) => {
                "unwinder (libgcc_s/libgcc_eh or LLVM libunwind)"
            }
            (Self::EhPersonality, ObjectFormat::Elf) => {
                "language runtime defining the personality (libgcc for __gcc_personality_v0, libstdc++ or libc++abi for __gxx_personality_v0, Rust std for rust_eh_personality)"
            }
            (Self::TlsRuntime, ObjectFormat::Elf) => {
                "dynamic loader TLS runtime (ld-linux-aarch64.so.1) or static libc"
            }
            (Self::MemoryIntrinsics | Self::Libc | Self::Libm, ObjectFormat::MachO) => "libSystem",
            (Self::CompilerRuntime, ObjectFormat::MachO) => "libSystem (libcompiler_rt builtins)",
            (Self::Unwinder, ObjectFormat::MachO) => "libSystem (libunwind)",
            (Self::EhPersonality, ObjectFormat::MachO) => {
                "language runtime defining the personality (libc++abi for __gxx_personality_v0, Rust std for rust_eh_personality)"
            }
            (Self::TlsRuntime, ObjectFormat::MachO) => "dyld TLV runtime (libSystem)",
            (Self::External, _) => "another object, a named library or the program",
        }
    }

    /// Classify a C-level symbol name (no Mach-O underscore prefix).
    pub fn classify(c_name: &str) -> Self {
        if MEMORY_INTRINSICS.contains(&c_name) {
            Self::MemoryIntrinsics
        } else if LIBC.contains(&c_name) {
            Self::Libc
        } else if LIBM.contains(&c_name) {
            Self::Libm
        } else if COMPILER_RUNTIME.contains(&c_name) || c_name.starts_with("__aarch64_") {
            Self::CompilerRuntime
        } else if c_name.starts_with("_Unwind_") {
            Self::Unwinder
        } else if EH_PERSONALITY.contains(&c_name) {
            Self::EhPersonality
        } else if TLS_RUNTIME.contains(&c_name) {
            Self::TlsRuntime
        } else {
            Self::External
        }
    }
}

impl fmt::Display for RuntimeProvider {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

const MEMORY_INTRINSICS: &[&str] = &["memcpy", "memmove", "memset", "memcmp", "bcmp"];

const LIBC: &[&str] = &[
    "malloc",
    "calloc",
    "realloc",
    "free",
    "posix_memalign",
    "aligned_alloc",
    "abort",
    "exit",
    "_exit",
    "__stack_chk_fail",
    "__stack_chk_guard",
    "strlen",
    "write",
    "puts",
    "putchar",
    "printf",
    "fprintf",
    "__errno_location",
    "__error",
];

const LIBM: &[&str] = &[
    "fmod",
    "fmodf",
    "sin",
    "sinf",
    "cos",
    "cosf",
    "tan",
    "tanf",
    "asin",
    "asinf",
    "acos",
    "acosf",
    "atan",
    "atanf",
    "atan2",
    "atan2f",
    "sinh",
    "sinhf",
    "cosh",
    "coshf",
    "tanh",
    "tanhf",
    "exp",
    "expf",
    "exp2",
    "exp2f",
    "expm1",
    "expm1f",
    "log",
    "logf",
    "log2",
    "log2f",
    "log10",
    "log10f",
    "log1p",
    "log1pf",
    "pow",
    "powf",
    "sqrt",
    "sqrtf",
    "cbrt",
    "cbrtf",
    "hypot",
    "hypotf",
    "fma",
    "fmaf",
    "floor",
    "floorf",
    "ceil",
    "ceilf",
    "trunc",
    "truncf",
    "round",
    "roundf",
    "rint",
    "rintf",
    "nearbyint",
    "nearbyintf",
    "fmin",
    "fminf",
    "fmax",
    "fmaxf",
    "fabs",
    "fabsf",
    "copysign",
    "copysignf",
    "ldexp",
    "ldexpf",
    "frexp",
    "frexpf",
];

const COMPILER_RUNTIME: &[&str] = &[
    "__divti3",
    "__udivti3",
    "__modti3",
    "__umodti3",
    "__divmodti4",
    "__udivmodti4",
    "__multi3",
    "__muloti4",
    "__mulodi4",
    "__ashlti3",
    "__ashrti3",
    "__lshrti3",
    "__powidf2",
    "__powisf2",
    "__powitf2",
    "__floattidf",
    "__floattisf",
    "__floattitf",
    "__floatuntidf",
    "__floatuntisf",
    "__floatuntitf",
    "__fixdfti",
    "__fixsfti",
    "__fixtfti",
    "__fixunsdfti",
    "__fixunssfti",
    "__fixunstfti",
    "__clzti2",
    "__ctzti2",
    "__popcountti2",
    "__popcountdi2",
    "__bswapdi2",
    "__extendhfsf2",
    "__truncsfhf2",
    "__truncdfhf2",
    "__gnu_h2f_ieee",
    "__gnu_f2h_ieee",
    "__addtf3",
    "__subtf3",
    "__multf3",
    "__divtf3",
    "__extenddftf2",
    "__extendsftf2",
    "__trunctfdf2",
    "__trunctfsf2",
    "__eqtf2",
    "__netf2",
    "__lttf2",
    "__letf2",
    "__gttf2",
    "__getf2",
    "__unordtf2",
    "__clear_cache",
];

const EH_PERSONALITY: &[&str] = &[
    "__gcc_personality_v0",
    "__gxx_personality_v0",
    "__objc_personality_v0",
    "rust_eh_personality",
];

const TLS_RUNTIME: &[&str] = &["__tls_get_addr", "_tlv_bootstrap"];

/// One undefined symbol and its classification.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct RuntimeDependency {
    /// Provider group (first so the derived order groups by provider).
    pub provider: RuntimeProvider,
    /// The symbol name exactly as the object's symbol table spells it.
    pub symbol: String,
    /// The C-level name used for classification (Mach-O drops one leading
    /// underscore; ELF names are unchanged).
    pub c_name: String,
    /// A weak reference (ELF `STB_WEAK` undefined, Mach-O `N_WEAK_REF`)
    /// resolves to zero when no definition is linked, so it is not a hard
    /// link requirement.
    pub weak: bool,
}

/// Failure to read an object's symbol table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeDependencyError {
    /// The bytes start with neither the ELF magic nor the 64-bit Mach-O magic.
    UnrecognizedObject,
    /// The independent ELF reader rejected the object.
    Elf(String),
    /// The Mach-O parser rejected the object.
    MachO(String),
}

impl fmt::Display for RuntimeDependencyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnrecognizedObject => {
                f.write_str("runtime-dependency manifest: object is neither ELF64 nor Mach-O 64")
            }
            Self::Elf(detail) => {
                write!(f, "runtime-dependency manifest: ELF read failed: {detail}")
            }
            Self::MachO(detail) => {
                write!(
                    f,
                    "runtime-dependency manifest: Mach-O read failed: {detail}"
                )
            }
        }
    }
}

impl std::error::Error for RuntimeDependencyError {}

/// Every named undefined symbol of one object, grouped by provider.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeDependencyManifest {
    /// Container format of the object that was read.
    pub format: ObjectFormat,
    /// Sorted by provider, then symbol name; one row per distinct symbol.
    pub dependencies: Vec<RuntimeDependency>,
}

/// Manifest schema identifier written into JSON output.
pub const RUNTIME_DEPENDENCY_SCHEMA: &str = "trust-cg.runtime-dependencies.v1";

const MH_MAGIC_64_LE: [u8; 4] = [0xcf, 0xfa, 0xed, 0xfe];
const ELF_MAGIC: [u8; 4] = [0x7f, b'E', b'L', b'F'];

impl RuntimeDependencyManifest {
    /// Read `bytes` (an ELF64 or Mach-O 64 relocatable object) and classify
    /// every named undefined symbol.
    pub fn from_object(bytes: &[u8]) -> Result<Self, RuntimeDependencyError> {
        let (format, undefined) = if bytes.starts_with(&ELF_MAGIC) {
            let records = crate::elf::reparse::read_object_records(bytes)
                .map_err(|error| RuntimeDependencyError::Elf(error.to_string()))?;
            let undefined: Vec<(String, bool)> = records
                .symbols
                .iter()
                .filter(|symbol| symbol.is_undefined_reference())
                .map(|symbol| {
                    (
                        symbol.name.clone(),
                        symbol.binding == crate::elf::constants::STB_WEAK,
                    )
                })
                .collect();
            (ObjectFormat::Elf, undefined)
        } else if bytes.starts_with(&MH_MAGIC_64_LE) {
            let parsed = crate::macho::linker::MachOParser::parse(bytes)
                .map_err(|error| RuntimeDependencyError::MachO(error.to_string()))?;
            let undefined: Vec<(String, bool)> = parsed
                .symbols
                .iter()
                .filter(|symbol| symbol.is_undefined() && !symbol.name.is_empty())
                .map(|symbol| (symbol.name.to_string(), symbol.is_weak_ref()))
                .collect();
            (ObjectFormat::MachO, undefined)
        } else {
            return Err(RuntimeDependencyError::UnrecognizedObject);
        };

        let mut seen = BTreeSet::new();
        let mut dependencies = Vec::new();
        for (symbol, weak) in undefined {
            if !seen.insert(symbol.clone()) {
                continue;
            }
            let c_name = match format {
                ObjectFormat::MachO => symbol.strip_prefix('_').unwrap_or(&symbol).to_string(),
                ObjectFormat::Elf => symbol.clone(),
            };
            dependencies.push(RuntimeDependency {
                provider: RuntimeProvider::classify(&c_name),
                symbol,
                c_name,
                weak,
            });
        }
        dependencies.sort();
        Ok(Self {
            format,
            dependencies,
        })
    }

    /// Object-level names of the symbols grouped under `provider`.
    pub fn symbols_for(&self, provider: RuntimeProvider) -> Vec<&str> {
        self.dependencies
            .iter()
            .filter(|dependency| dependency.provider == provider)
            .map(|dependency| dependency.symbol.as_str())
            .collect()
    }

    /// Providers with at least one dependency.
    pub fn providers(&self) -> BTreeSet<RuntimeProvider> {
        self.dependencies
            .iter()
            .map(|dependency| dependency.provider)
            .collect()
    }

    /// Object-level names of every non-weak (hard) undefined symbol.
    pub fn required_symbols(&self) -> BTreeSet<&str> {
        self.dependencies
            .iter()
            .filter(|dependency| !dependency.weak)
            .map(|dependency| dependency.symbol.as_str())
            .collect()
    }

    /// Render the manifest as JSON (schema [`RUNTIME_DEPENDENCY_SCHEMA`]).
    /// Providers with no symbol are omitted; symbol order is stable.
    pub fn to_json(&self) -> serde_json::Value {
        let providers: Vec<serde_json::Value> = RuntimeProvider::ALL
            .iter()
            .filter_map(|provider| {
                let symbols: Vec<serde_json::Value> = self
                    .dependencies
                    .iter()
                    .filter(|dependency| dependency.provider == *provider)
                    .map(|dependency| {
                        serde_json::json!({
                            "name": dependency.symbol,
                            "c_name": dependency.c_name,
                            "weak": dependency.weak,
                        })
                    })
                    .collect();
                (!symbols.is_empty()).then(|| {
                    serde_json::json!({
                        "provider": provider.as_str(),
                        "library_hint": provider.library_hint(self.format),
                        "symbols": symbols,
                    })
                })
            })
            .collect();
        serde_json::json!({
            "schema": RUNTIME_DEPENDENCY_SCHEMA,
            "format": self.format.as_str(),
            "undefined_symbol_count": self.dependencies.len(),
            "providers": providers,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classification_table_names_each_runtime_family() {
        let cases = [
            ("memcpy", RuntimeProvider::MemoryIntrinsics),
            ("bcmp", RuntimeProvider::MemoryIntrinsics),
            ("malloc", RuntimeProvider::Libc),
            ("__stack_chk_guard", RuntimeProvider::Libc),
            ("__stack_chk_fail", RuntimeProvider::Libc),
            ("fmodf", RuntimeProvider::Libm),
            ("__divti3", RuntimeProvider::CompilerRuntime),
            ("__umodti3", RuntimeProvider::CompilerRuntime),
            ("__powidf2", RuntimeProvider::CompilerRuntime),
            ("__floattidf", RuntimeProvider::CompilerRuntime),
            ("__aarch64_cas8_acq_rel", RuntimeProvider::CompilerRuntime),
            ("_Unwind_Resume", RuntimeProvider::Unwinder),
            ("__gxx_personality_v0", RuntimeProvider::EhPersonality),
            ("rust_eh_personality", RuntimeProvider::EhPersonality),
            ("__tls_get_addr", RuntimeProvider::TlsRuntime),
            ("_tlv_bootstrap", RuntimeProvider::TlsRuntime),
            ("user_function", RuntimeProvider::External),
            // Near misses stay External: the table is exact, not a pattern.
            ("__divti4", RuntimeProvider::External),
            ("memcpy_chk", RuntimeProvider::External),
            ("Unwind_Resume", RuntimeProvider::External),
        ];
        for (name, provider) in cases {
            assert_eq!(RuntimeProvider::classify(name), provider, "{name}");
        }
    }

    #[test]
    fn unrecognized_bytes_fail_closed() {
        assert_eq!(
            RuntimeDependencyManifest::from_object(b"not an object"),
            Err(RuntimeDependencyError::UnrecognizedObject)
        );
        assert!(matches!(
            RuntimeDependencyManifest::from_object(&ELF_MAGIC),
            Err(RuntimeDependencyError::Elf(_))
        ));
        assert!(matches!(
            RuntimeDependencyManifest::from_object(&MH_MAGIC_64_LE),
            Err(RuntimeDependencyError::MachO(_))
        ));
    }

    #[test]
    fn every_provider_has_hints_for_both_formats() {
        for provider in RuntimeProvider::ALL {
            for format in [ObjectFormat::Elf, ObjectFormat::MachO] {
                assert!(!provider.library_hint(format).is_empty());
            }
        }
    }
}
