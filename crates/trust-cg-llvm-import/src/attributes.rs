// trust-cg-llvm-import / attributes.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The function attributes the importer reads, and the ones it refuses by
// name because llc builds code for them that the importer does not.

use crate::lexical::{Kind, Token, string_text};

/// Function attributes LLVM 22 spells by keyword (`Attributes.td`) that the
/// importer reads and drops. None changes what a correct program computes in
/// the code the importer builds:
///
/// * facts about the function and permissions or restrictions on
///   optimization (`memory`, `nounwind`, `noinline`, `optnone`, `cold`, ...):
///   llc may build different code for them, but not code that computes
///   something else;
/// * requests llc builds no code for: sanitizer markers (the
///   instrumentation is an `opt` pass, already in the text when it ran),
///   profiling markers, `nocf_check` (the backend emits no `endbr64` for it
///   to omit), `nonlazybind` (llc calls through the GOT, to the same callee)
///   and `uwtable` (unwind tables, read only by unwinders);
/// * `ssp`, `sspstrong` and `sspreq`, which the importer reads.
///
/// An AArch64 and x86-64 llc 22 survey of one function with and without
/// each keyword (scratch `attr_llc_effect.py`) found that only `cold`, `hot`,
/// `minsize`, `optsize`, `optnone`, `optforfuzzing` and `nounwind` of these
/// change llc's instructions, by layout or frame shape. `nobuiltin` is not
/// among them: it is refused ([`REFUSED_KEYWORDS`]).
const READ_KEYWORDS: [&str; 55] = [
    "allockind",
    "allocsize",
    "alwaysinline",
    "builtin",
    "cold",
    "convergent",
    "coro_elide_safe",
    "coro_only_destroy_when_complete",
    "denormal_fpenv",
    "disable_sanitizer_instrumentation",
    "hot",
    "inlinehint",
    "jumptable",
    "memory",
    "minsize",
    "mustprogress",
    "nocallback",
    "nocf_check",
    "nocreateundeforpoison",
    "noduplicate",
    "nofree",
    "noinline",
    "nomerge",
    "nonlazybind",
    "noprofile",
    "norecurse",
    "noreturn",
    "nosanitize_bounds",
    "nosanitize_coverage",
    "nosync",
    "nounwind",
    "optdebug",
    "optforfuzzing",
    "optnone",
    "optsize",
    "readnone",
    "readonly",
    "sanitize_address",
    "sanitize_alloc_token",
    "sanitize_hwaddress",
    "sanitize_memory",
    "sanitize_numerical_stability",
    "sanitize_realtime",
    "sanitize_realtime_blocking",
    "sanitize_thread",
    "sanitize_type",
    "skipprofile",
    "speculatable",
    "ssp",
    "sspreq",
    "sspstrong",
    "uwtable",
    "vscale_range",
    "willreturn",
    "writeonly",
];

/// Function attributes LLVM 22 spells by keyword for which llc builds code,
/// a frame or a promise the importer does not, each refused by name with
/// the reason.
const REFUSED_KEYWORDS: [(&str, &str); 15] = [
    (
        "alignstack",
        "llc realigns the stack pointer in the prologue; this importer's backend does not",
    ),
    (
        "fn_ret_thunk_extern",
        "llc returns through `__x86_return_thunk`; this importer's backend returns directly",
    ),
    (
        "hybrid_patchable",
        "llc builds arm64ec patchable entry thunks; this importer's backend builds none",
    ),
    (
        "naked",
        "llc emits no prologue or epilogue; this importer's backend always emits them",
    ),
    (
        // `CallBase::isNoBuiltin`: on a call, or on the function it calls.
        "nobuiltin",
        "llc 22 reads a call it marks (the call's own, or the called function's) as no call of \
         the C library function of its name, and keeps it as a call; this importer's backend \
         reads a call of a library function by its name (a call of a declared `memcpy` or \
         `memset` with a constant count may become loads and stores, calling nothing)",
    ),
    (
        "noimplicitfloat",
        "llc keeps floating-point and vector registers out of code that does not name them; \
         this importer's backend may use them",
    ),
    (
        "noredzone",
        "llc writes nothing below the stack pointer; this importer does not pass that \
         restriction to its backend",
    ),
    (
        "null_pointer_is_valid",
        "address 0 may hold an object; this importer does not tell its backend's optimizer so",
    ),
    (
        "presplitcoroutine",
        "the function is an unsplit coroutine, which LLVM's coroutine passes must still lower",
    ),
    (
        "returns_twice",
        "a call may return a second time (`setjmp`); llc keeps the caller's frame valid for \
         that return, and this importer's backend keeps nothing safe across it",
    ),
    (
        "safestack",
        "llc moves unsafe stack objects to a separate stack; this importer's backend does not",
    ),
    (
        "sanitize_memtag",
        "llc tags stack objects with MTE instructions; this importer's backend does not",
    ),
    (
        "shadowcallstack",
        "llc saves the return address on the shadow call stack (x18); this importer's \
         backend does not",
    ),
    (
        "speculative_load_hardening",
        "llc hardens loads against speculative execution; this importer's backend does not",
    ),
    (
        "strictfp",
        "the function may change the floating-point environment; this importer's backend \
         folds and moves floating-point operations as if it never changes",
    ),
];

/// Why the keyword attribute `word` is refused, or `None` when it is read.
/// A word that is no LLVM 22 function attribute is refused too.
pub(crate) fn keyword_attribute_refusal(word: &str) -> Option<String> {
    if READ_KEYWORDS.contains(&word) {
        return None;
    }
    Some(
        REFUSED_KEYWORDS
            .iter()
            .find(|(keyword, _)| *keyword == word)
            .map_or_else(
                || "not an LLVM 22 function attribute this importer reads".to_string(),
                |(_, why)| (*why).to_string(),
            ),
    )
}

/// Whether `word` is a function attribute keyword the importer knows
/// (read or refused), as opposed to a clause keyword or an unknown word.
pub(crate) fn is_function_attribute_keyword(word: &str) -> bool {
    READ_KEYWORDS.contains(&word) || REFUSED_KEYWORDS.iter().any(|(keyword, _)| *keyword == word)
}

/// Target features that are not instruction-set extensions but change how
/// llc builds code: register reservations and callee-saved sets (an ABI),
/// alignment and execute-only restrictions, global address tagging, the TLS
/// base register, speculation mitigations, and x86 modes. Matched as a
/// prefix of the feature name.
const MODE_FEATURE_PREFIXES: [&str; 14] = [
    "strict-align",
    "reserve-",
    "call-saved-",
    "tagged-globals",
    "execute-only",
    "harden-sls-",
    "tpidr",
    "16bit-mode",
    "32bit-mode",
    "x32",
    "soft-float",
    "retpoline",
    "lvi-",
    "seses",
];

/// The subtarget features LLVM 22.1.2 defines that are not themselves among
/// [`MODE_FEATURE_PREFIXES`] but imply one that is, with that feature. llc
/// sets every feature a `+feature` implies (`ApplyFeatureFlag`, closed under
/// `Implies`), so `+thunderx3t110` (the AArch64 tuning feature
/// `TuneThunderX3T110`, `AArch64Processors.td`) sets `strict-align`: llc
/// 22.1.2 loads an `align 1` `i64` byte by byte for it on AArch64 Linux and
/// Apple, as for `+strict-align`. Derived from the `Implies` closure of
/// every feature of LLVM 22.1.2's AArch64, RISCV and X86 tables (349, 348
/// and 199 features; `tests/fixtures/llvm22_subtarget_features.json`,
/// written by `scripts/extract_llvm_subtarget_features.py`), which
/// `mode_implying_tables_are_the_closure_of_llvms_tables` re-derives. llc
/// matches a feature name exactly.
const MODE_IMPLYING_FEATURES: [(&str, &str); 1] = [("thunderx3t110", "strict-align")];

/// The processor names LLVM 22.1.2 defines whose features imply one this
/// importer refuses as a `+feature` ([`MODE_FEATURE_PREFIXES`]), with that
/// feature. `"target-cpu"` sets a processor's feature list and its tuning
/// list (`ProcessorModel`), `"tune-cpu"` its tuning list, and llc builds
/// code for every feature they imply. Derived, like
/// [`MODE_IMPLYING_FEATURES`], from the `Implies` closure of the feature and
/// tuning lists of every processor and alias of the same tables (99, 51 and
/// 131 names): only `thunderx3t110` implies one, through its tuning list
/// (`+thunderx3t110`, which sets `strict-align`). An llc 22.1.2 sweep of
/// every AArch64 name as a key of either attribute on AArch64 Linux and
/// Apple found byte loads for that name only. A name LLVM 22 does not define
/// for the compile target is no generic processor: llc ignores it (with a
/// warning) and sets none of a processor's features, so it is refused too
/// ([`ProcessorTable`]).
const MODE_IMPLYING_PROCESSORS: [(&str, &str); 1] = [("thunderx3t110", "strict-align")];

/// The processor names LLVM 22.1.2's AArch64 target defines, sorted: its
/// `Processor` records and its `ProcessorAlias`es (`AArch64Processors.td`),
/// which its generated subtarget resolves before the lookup
/// (`AArch64::resolveCPUAlias`). The `Implies` closure of every one's
/// feature list holds `fp-armv8` and `neon`, so llc builds a function for
/// any of them with the hard-float AAPCS this importer's backend builds.
/// Derived from the committed extract by `processor_name_tables_are_llvms`.
const AARCH64_PROCESSOR_NAMES: [&str; 99] = [
    "a64fx",
    "ampere1",
    "ampere1a",
    "ampere1b",
    "ampere1c",
    "apple-a10",
    "apple-a11",
    "apple-a12",
    "apple-a13",
    "apple-a14",
    "apple-a15",
    "apple-a16",
    "apple-a17",
    "apple-a18",
    "apple-a19",
    "apple-a7",
    "apple-a8",
    "apple-a9",
    "apple-latest",
    "apple-m1",
    "apple-m2",
    "apple-m3",
    "apple-m4",
    "apple-m5",
    "apple-s10",
    "apple-s4",
    "apple-s5",
    "apple-s6",
    "apple-s7",
    "apple-s8",
    "apple-s9",
    "c1-nano",
    "c1-premium",
    "c1-pro",
    "c1-ultra",
    "carmel",
    "cobalt-100",
    "cortex-a320",
    "cortex-a34",
    "cortex-a35",
    "cortex-a510",
    "cortex-a520",
    "cortex-a520ae",
    "cortex-a53",
    "cortex-a55",
    "cortex-a57",
    "cortex-a65",
    "cortex-a65ae",
    "cortex-a710",
    "cortex-a715",
    "cortex-a72",
    "cortex-a720",
    "cortex-a720ae",
    "cortex-a725",
    "cortex-a73",
    "cortex-a75",
    "cortex-a76",
    "cortex-a76ae",
    "cortex-a77",
    "cortex-a78",
    "cortex-a78ae",
    "cortex-a78c",
    "cortex-r82",
    "cortex-r82ae",
    "cortex-x1",
    "cortex-x1c",
    "cortex-x2",
    "cortex-x3",
    "cortex-x4",
    "cortex-x925",
    "cyclone",
    "exynos-m3",
    "exynos-m4",
    "exynos-m5",
    "falkor",
    "fujitsu-monaka",
    "gb10",
    "generic",
    "grace",
    "kryo",
    "neoverse-512tvb",
    "neoverse-e1",
    "neoverse-n1",
    "neoverse-n2",
    "neoverse-n3",
    "neoverse-v1",
    "neoverse-v2",
    "neoverse-v3",
    "neoverse-v3ae",
    "olympus",
    "oryon-1",
    "saphira",
    "thunderx",
    "thunderx2t99",
    "thunderx3t110",
    "thunderxt81",
    "thunderxt83",
    "thunderxt88",
    "tsv110",
];

/// The processor names LLVM 22.1.2's RISCV target defines (it has no
/// aliases), sorted; derived as [`AARCH64_PROCESSOR_NAMES`] is.
const RISCV_PROCESSOR_NAMES: [&str; 51] = [
    "andes-45-series",
    "andes-a25",
    "andes-a45",
    "andes-ax25",
    "andes-ax45",
    "andes-ax45mpv",
    "andes-n45",
    "andes-nx45",
    "generic",
    "generic-ooo",
    "generic-rv32",
    "generic-rv64",
    "mips-p8700",
    "rocket",
    "rocket-rv32",
    "rocket-rv64",
    "rp2350-hazard3",
    "sifive-7-series",
    "sifive-e20",
    "sifive-e21",
    "sifive-e24",
    "sifive-e31",
    "sifive-e34",
    "sifive-e76",
    "sifive-p450",
    "sifive-p470",
    "sifive-p550",
    "sifive-p670",
    "sifive-p870",
    "sifive-s21",
    "sifive-s51",
    "sifive-s54",
    "sifive-s76",
    "sifive-u54",
    "sifive-u74",
    "sifive-x280",
    "sifive-x390",
    "spacemit-x60",
    "syntacore-scr1-base",
    "syntacore-scr1-max",
    "syntacore-scr3-rv32",
    "syntacore-scr3-rv64",
    "syntacore-scr4-rv32",
    "syntacore-scr4-rv64",
    "syntacore-scr5-rv32",
    "syntacore-scr5-rv64",
    "syntacore-scr7",
    "tt-ascalon-d8",
    "veyron-v1",
    "xiangshan-kunminghu",
    "xiangshan-nanhu",
];

/// The processor names LLVM 22.1.2's X86 target defines (it has no
/// aliases), sorted; derived as [`AARCH64_PROCESSOR_NAMES`] is.
const X86_PROCESSOR_NAMES: [&str; 131] = [
    "alderlake",
    "amdfam10",
    "arrowlake",
    "arrowlake-s",
    "arrowlake_s",
    "athlon",
    "athlon-4",
    "athlon-fx",
    "athlon-mp",
    "athlon-tbird",
    "athlon-xp",
    "athlon64",
    "athlon64-sse3",
    "atom",
    "atom_sse4_2",
    "atom_sse4_2_movbe",
    "barcelona",
    "bdver1",
    "bdver2",
    "bdver3",
    "bdver4",
    "bonnell",
    "broadwell",
    "btver1",
    "btver2",
    "c3",
    "c3-2",
    "cannonlake",
    "cascadelake",
    "clearwaterforest",
    "cooperlake",
    "core-avx-i",
    "core-avx2",
    "core2",
    "core_2_duo_sse4_1",
    "core_2_duo_ssse3",
    "core_2nd_gen_avx",
    "core_3rd_gen_avx",
    "core_4th_gen_avx",
    "core_4th_gen_avx_tsx",
    "core_5th_gen_avx",
    "core_5th_gen_avx_tsx",
    "core_aes_pclmulqdq",
    "core_i7_sse4_2",
    "corei7",
    "corei7-avx",
    "diamondrapids",
    "emeraldrapids",
    "generic",
    "geode",
    "goldmont",
    "goldmont-plus",
    "goldmont_plus",
    "gracemont",
    "grandridge",
    "graniterapids",
    "graniterapids-d",
    "graniterapids_d",
    "haswell",
    "i386",
    "i486",
    "i586",
    "i686",
    "icelake-client",
    "icelake-server",
    "icelake_client",
    "icelake_server",
    "ivybridge",
    "k6",
    "k6-2",
    "k6-3",
    "k8",
    "k8-sse3",
    "knl",
    "knm",
    "lakemont",
    "lunarlake",
    "meteorlake",
    "mic_avx512",
    "nehalem",
    "nocona",
    "novalake",
    "opteron",
    "opteron-sse3",
    "pantherlake",
    "penryn",
    "pentium",
    "pentium-m",
    "pentium-mmx",
    "pentium2",
    "pentium3",
    "pentium3m",
    "pentium4",
    "pentium4m",
    "pentium_4",
    "pentium_4_sse3",
    "pentium_ii",
    "pentium_iii",
    "pentium_iii_no_xmm_regs",
    "pentium_m",
    "pentium_mmx",
    "pentium_pro",
    "pentiumpro",
    "prescott",
    "raptorlake",
    "rocketlake",
    "sandybridge",
    "sapphirerapids",
    "sierraforest",
    "silvermont",
    "skx",
    "skylake",
    "skylake-avx512",
    "skylake_avx512",
    "slm",
    "tigerlake",
    "tremont",
    "westmere",
    "wildcatlake",
    "winchip-c6",
    "winchip2",
    "x86-64",
    "x86-64-v2",
    "x86-64-v3",
    "x86-64-v4",
    "yonah",
    "znver1",
    "znver2",
    "znver3",
    "znver4",
    "znver5",
];

/// The processor names a `"target-cpu"` or `"tune-cpu"` value is read
/// against: those LLVM 22.1.2 defines for the compile target's architecture
/// (`Parser::target`: the caller's triple, else the module's `target
/// triple`). llc looks a function's name up exactly (case and every byte,
/// `MCSubtargetInfo`'s `Find`) in that target's table, and a name it does
/// not find is no generic processor: llc ignores it (with a warning) and
/// sets none of a processor's features. On AArch64 that builds the function
/// without `fp-armv8` or `neon`, with the soft-float calling convention (a
/// `double` passed in `x0`, floating-point arithmetic in library calls),
/// where this importer's backend builds the hard-float one; llc 22.1.2 did
/// so for `native`, `armv8-a`, `Cortex-A57`, `generic ` and `generic\0`,
/// and for each of the 180 X86 and RISCV names AArch64 does not define.
/// The AArch64, X86 and RISCV subtargets read an empty name as `generic`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ProcessorTable {
    /// `aarch64` or `arm64` ([`crate::triple::TargetTriple::aarch64`]):
    /// [`AARCH64_PROCESSOR_NAMES`].
    Aarch64,
    /// A RISC-V architecture ([`crate::triple::TargetTriple::riscv_xlen`]):
    /// [`RISCV_PROCESSOR_NAMES`].
    Riscv,
    /// `x86` or `x86_64` ([`crate::triple::TargetTriple::x86`]):
    /// [`X86_PROCESSOR_NAMES`].
    X86,
    /// No target is known (no triple given or stated): the module may be
    /// compiled for any of the three, so a name is read only when all three
    /// tables define it (`generic`, in LLVM 22.1.2).
    NoTarget,
    /// A known target of another architecture, the other AArch64 names
    /// (`arm64e`, `aarch64_be`, `aarch64_32`, ...) among them: no table is
    /// read and every name is refused, the empty one included.
    Other,
}

impl ProcessorTable {
    /// The table for the compile target `target` (`None`: none known).
    pub(crate) fn of(target: Option<crate::triple::TargetTriple>) -> Self {
        match target {
            None => Self::NoTarget,
            Some(target) if target.aarch64 => Self::Aarch64,
            Some(target) if target.riscv_xlen.is_some() => Self::Riscv,
            Some(target) if target.x86 => Self::X86,
            Some(_) => Self::Other,
        }
    }

    /// The tables a name must be in: one, all three, or none.
    fn tables(self) -> &'static [&'static [&'static str]] {
        match self {
            Self::Aarch64 => &[&AARCH64_PROCESSOR_NAMES],
            Self::Riscv => &[&RISCV_PROCESSOR_NAMES],
            Self::X86 => &[&X86_PROCESSOR_NAMES],
            Self::NoTarget => &[
                &AARCH64_PROCESSOR_NAMES,
                &RISCV_PROCESSOR_NAMES,
                &X86_PROCESSOR_NAMES,
            ],
            Self::Other => &[],
        }
    }

    /// Whether `name` is read: in every table [`Self::tables`] names (the
    /// empty name as `generic`), and there is one.
    fn reads(self, name: &str) -> bool {
        let name = if name.is_empty() { "generic" } else { name };
        let tables = self.tables();
        !tables.is_empty()
            && tables
                .iter()
                .all(|table| table.binary_search(&name).is_ok())
    }

    /// The compile target, in a refusal.
    fn describe(self) -> &'static str {
        match self {
            Self::Aarch64 => "the compile target's architecture, AArch64",
            Self::Riscv => "the compile target's architecture, RISC-V",
            Self::X86 => "the compile target's architecture, x86",
            Self::NoTarget => {
                "every architecture a module with no known target may be compiled for \
                 (of the names AArch64, RISC-V and x86 define, only `generic` is common to \
                 all three)"
            }
            Self::Other => {
                "the compile target's architecture, whose processor table this importer does \
                 not read (it reads AArch64's as `aarch64` or `arm64`, RISC-V's and x86's)"
            }
        }
    }
}

/// The RISC-V features LLVM 22.1.2 defines whose `Implies` closure holds
/// `d`, the extension that, without `e`, makes llc 22's calling convention
/// for a function `lp64d` (`RISCVABI::computeTargetABI`, below). Derived,
/// like [`MODE_IMPLYING_FEATURES`], from the committed extract of LLVM's
/// RISCV table by `riscv_calling_convention_tables_are_the_closure_of_llvms_tables`.
const RISCV_D_FEATURES: [&str; 16] = [
    "d",
    "q",
    "rva20s64",
    "rva20u64",
    "rva22s64",
    "rva22u64",
    "rva23s64",
    "rva23u64",
    "rvb23s64",
    "rvb23u64",
    "v",
    "xsfmm64a64f",
    "xsfvfexpa64e",
    "xtheadvdot",
    "zcd",
    "zve64d",
];

/// The RISC-V features LLVM 22.1.2 defines whose `Implies` closure holds
/// `e`, which makes llc 22's calling convention `lp64e` whatever else is
/// set. Derived as [`RISCV_D_FEATURES`] is.
const RISCV_E_FEATURES: [&str; 1] = ["e"];

/// The RISC-V features LLVM 22.1.2 defines whose `Implies` closure holds
/// `f` ([`RISCV_D_FEATURES`] among them: `d` implies `f`), the extension
/// that, without `d` or `e`, makes llc 22's calling convention `lp64f`.
/// With [`RISCV_E_FEATURES`], the features that select a RISC-V calling
/// convention other than the soft-float default, read when no compile
/// target is known ([`SubtargetSelection::riscv_refusal_without_target`]).
/// Derived as [`RISCV_D_FEATURES`] is.
const RISCV_F_FEATURES: [&str; 42] = [
    "d",
    "experimental-zvfbfa",
    "experimental-zvfofp8min",
    "f",
    "q",
    "rva20s64",
    "rva20u64",
    "rva22s64",
    "rva22u64",
    "rva23s64",
    "rva23u64",
    "rvb23s64",
    "rvb23u64",
    "v",
    "xandesbfhcvt",
    "xandesvbfhcvt",
    "xandesvpackfph",
    "xsfmm32a16f",
    "xsfmm32a32f",
    "xsfmm32a8f",
    "xsfmm64a64f",
    "xsfvfexp16e",
    "xsfvfexp32e",
    "xsfvfexpa",
    "xsfvfexpa64e",
    "xsfvfnrclipxfqf",
    "xsfvfwmaccqqq",
    "xsmtvdot",
    "xtheadvdot",
    "zcd",
    "zcf",
    "zfa",
    "zfbfmin",
    "zfh",
    "zfhmin",
    "zve32f",
    "zve64d",
    "zve64f",
    "zvfbfmin",
    "zvfbfwma",
    "zvfh",
    "zvfhmin",
];

/// The RISC-V processors LLVM 22.1.2 defines whose feature list's `Implies`
/// closure holds `64bit` (the ones llc 22 accepts as the `"target-cpu"` of
/// a function for a `riscv64` triple: `RISCVFeatures::validate` rejects any
/// other, "RV64 target requires an RV64 CPU", unless the function's own
/// features add `64bit`), each with whether that closure holds `d`. No
/// processor's closure holds `e`, and no tuning list (`"tune-cpu"`) holds
/// `e`, `d` or `f`. Derived as [`RISCV_D_FEATURES`] is.
const RISCV64_PROCESSORS: [(&str, bool); 29] = [
    ("andes-ax25", true),
    ("andes-ax45", true),
    ("andes-ax45mpv", true),
    ("andes-nx45", true),
    ("generic-rv64", false),
    ("mips-p8700", true),
    ("rocket-rv64", false),
    ("sifive-p450", true),
    ("sifive-p470", true),
    ("sifive-p550", true),
    ("sifive-p670", true),
    ("sifive-p870", true),
    ("sifive-s21", false),
    ("sifive-s51", false),
    ("sifive-s54", true),
    ("sifive-s76", true),
    ("sifive-u54", true),
    ("sifive-u74", true),
    ("sifive-x280", true),
    ("sifive-x390", true),
    ("spacemit-x60", true),
    ("syntacore-scr3-rv64", false),
    ("syntacore-scr4-rv64", true),
    ("syntacore-scr5-rv64", true),
    ("syntacore-scr7", true),
    ("tt-ascalon-d8", true),
    ("veyron-v1", true),
    ("xiangshan-kunminghu", true),
    ("xiangshan-nanhu", true),
];

/// The `"target-cpu"` and `"target-features"` values one function's
/// attributes state, inline and through its groups, every one of them
/// (decoded as LLVM decodes them), for the RISC-V calling-convention check
/// ([`SubtargetSelection::riscv_refusal`]). [`string_attribute_refusal`]
/// reads each value alone; this reads them together.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct SubtargetSelection {
    cpus: Vec<String>,
    features: Vec<String>,
}

impl SubtargetSelection {
    /// Note the string attribute whose key is `tokens[at]` of `text`, with
    /// its value when `="value"` follows (no value reads as LLVM's empty
    /// one). A key or value that is not UTF-8 after LLVM's escapes is
    /// refused where the attribute is read and is not noted.
    pub(crate) fn note(&mut self, text: &str, tokens: &[Token], at: usize) {
        let value = match (tokens.get(at + 1), tokens.get(at + 2)) {
            (Some(equal), Some(value))
                if equal.kind == Kind::Punct(b'=') && value.kind == Kind::Str =>
            {
                string_text(value.text(text))
            }
            _ => Some(String::new()),
        };
        let Some(value) = value else {
            return;
        };
        match string_text(tokens[at].text(text)).as_deref() {
            Some("target-cpu") => self.cpus.push(value),
            Some("target-features") => self.features.push(value),
            _ => {}
        }
    }

    /// The values an attribute group's body `text` (lexed as `tokens`)
    /// states; every bracketed group is skipped.
    pub(crate) fn scan(text: &str, tokens: &[Token]) -> Self {
        let mut selection = Self::default();
        let mut index = 0;
        while let Some(token) = tokens.get(index) {
            match token.kind {
                Kind::Punct(b'(' | b'[' | b'{' | b'<') => {
                    index = skip_bracket_group(tokens, index);
                    continue;
                }
                Kind::Str => {
                    selection.note(text, tokens, index);
                    if tokens
                        .get(index + 1)
                        .is_some_and(|equal| equal.kind == Kind::Punct(b'='))
                    {
                        index += 2;
                    }
                }
                _ => {}
            }
            index += 1;
        }
        selection
    }

    /// The values of `self` and `other` together (a function's inline
    /// attributes and a group's).
    pub(crate) fn union(&self, other: &Self) -> Self {
        let mut union = self.clone();
        union.cpus.extend(other.cpus.iter().cloned());
        union.features.extend(other.features.iter().cloned());
        union
    }

    /// Why a function DEFINITION with these values is refused when compiled
    /// for a RISC-V target of `xlen` bits (the compile target, or else the
    /// module's `target triple`), or
    /// `None`; `floating` says whether a floating-point or vector type
    /// appears in the definition's text or in a named type the module
    /// defines. llc 22 builds each function with
    /// the calling convention its own features select (read in LLVM
    /// 22.1.2's source; this host's llc has no RISC-V target): with no
    /// `target-abi` (the module flag is refused, `metadata.rs`),
    /// `RISCVSubtarget` calls `RISCVABI::computeTargetABI`, which takes
    /// `RISCVISAInfo::computeDefaultABI`: `lp64e` with `e`, otherwise
    /// `lp64d` with `d`, `lp64f` with `f`, and the soft-float `lp64` with
    /// neither (`ilp32*` for 32 bits). `e` beside the `i` every 64-bit
    /// processor implies is no error: `RISCVISAInfo::updateImplication`
    /// erases `i` when `e` is set, before `checkDependency` would reject the
    /// pair (LLVM 22.1.2's TargetParser library gives `lp64e` for `+e,+i`,
    /// and LLVM's own `rv64e.ll` test builds it). The features are the processor's
    /// (`"target-cpu"`; none or `generic` is `generic-rv64`, which holds no
    /// `d`; a name outside [`RISCV64_PROCESSORS`] adds none here) and the
    /// function's `"target-features"`, closed under `Implies`. This
    /// importer's backend builds `lp64d` on RISC-V (`riscv_lp64d`) whatever
    /// they select. `lp64`, `lp64f` and `lp64d` place integer and pointer
    /// arguments and results alike (`a0`-`a7`, then the stack;
    /// `RISCVCallingConv.cpp`) and differ where a floating-point value is
    /// passed (and, by what they lower to, a vector), while `lp64e` passes
    /// only six arguments in registers. So a definition is refused when its
    /// convention is `lp64e`, or when it is not `lp64d` and its text names a
    /// floating-point or vector type anywhere (an over-refusal where no such
    /// value crosses a call boundary), for any value its attributes state;
    /// and every definition of a 32-bit module is refused (`ilp32*`; the
    /// backend builds 64-bit code).
    pub(crate) fn riscv_refusal(&self, xlen: u32, floating: bool) -> Option<String> {
        const RULE: &str = "llc 22 selects a RISC-V function's calling convention from its \
                            features (`RISCVABI::computeTargetABI` without `target-abi`: `e` \
                            gives `lp64e`, otherwise `d` gives `lp64d`, `f` `lp64f`, and \
                            neither the soft-float `lp64`), and this importer's backend builds \
                            `lp64d` whatever they select";
        if xlen != 64 {
            return Some(format!(
                "a function definition for a {xlen}-bit RISC-V target, which llc builds with \
                 an `ilp32` calling convention ({RULE})"
            ));
        }
        let cpus: Vec<&str> = if self.cpus.is_empty() {
            vec![""]
        } else {
            self.cpus.iter().map(String::as_str).collect()
        };
        let features: Vec<&str> = if self.features.is_empty() {
            vec![""]
        } else {
            self.features.iter().map(String::as_str).collect()
        };
        for cpu in cpus {
            let processor_d = RISCV64_PROCESSORS
                .iter()
                .any(|&(processor, d)| d && processor == cpu);
            for list in &features {
                let names = || list.split(',').filter_map(|entry| entry.strip_prefix('+'));
                if let Some(e) = names().find(|name| RISCV_E_FEATURES.contains(name)) {
                    return Some(format!(
                        "target feature `+{e}` selects llc's `lp64e` calling convention, which \
                         passes six arguments in registers where `lp64d` passes eight ({RULE})"
                    ));
                }
                if floating && !processor_d && !names().any(|name| RISCV_D_FEATURES.contains(&name))
                {
                    let cpu = if cpu.is_empty() { "generic" } else { cpu };
                    let features = if list.is_empty() {
                        "a target feature".to_string()
                    } else {
                        format!("a target feature among `{list}`")
                    };
                    return Some(format!(
                        "neither processor `{cpu}` nor {features} implies `d`, so llc builds \
                         the function with `lp64f` or the soft-float `lp64`, which place a \
                         floating-point value where `lp64d` does not, and the definition names \
                         a floating-point or vector type ({RULE})"
                    ));
                }
            }
        }
        None
    }

    /// Why a function DEFINITION with these values is refused when no
    /// compile target is known (no triple given or stated, so it may be
    /// compiled for RISC-V), or `None`. When any `"target-features"` value
    /// states a feature that selects a RISC-V calling convention other than
    /// the soft-float default (one whose closure holds `e` or `f`:
    /// [`RISCV_E_FEATURES`], [`RISCV_F_FEATURES`]), the definition is read
    /// as for a 64-bit RISC-V target ([`Self::riscv_refusal`], with its
    /// processors), the one RISC-V width the backend builds. None of these
    /// names is an AArch64 or x86 feature in LLVM 22.1.2's tables (llc
    /// ignores them there, with a warning). A definition that states none
    /// is admitted: for a 64-bit RISC-V target its processor then selects
    /// `lp64d` (one implying `d`) or the soft-float default `lp64` (no
    /// 64-bit processor implies `e`, or `f` without `d`), and the default is
    /// left to the target the caller compiles for, which
    /// `import_text_for_target` reads.
    pub(crate) fn riscv_refusal_without_target(&self, floating: bool) -> Option<String> {
        let states_convention_feature = self.features.iter().any(|list| {
            list.split(',')
                .filter_map(|entry| entry.strip_prefix('+'))
                .any(|name| RISCV_E_FEATURES.contains(&name) || RISCV_F_FEATURES.contains(&name))
        });
        if !states_convention_feature {
            return None;
        }
        self.riscv_refusal(64, floating).map(|why| {
            format!(
                "no target is known (the module states no `target triple` and none was given), \
                 and the definition states a feature that selects a RISC-V calling convention: \
                 for a 64-bit RISC-V target, {why}"
            )
        })
    }
}

/// Why the processor `value` of the attribute `key` (`"target-cpu"` or
/// `"tune-cpu"`; no value reads as LLVM's empty one) is refused, or `None`:
/// a name whose features imply a mode feature
/// ([`MODE_IMPLYING_PROCESSORS`]), and every name `table` does not read
/// ([`ProcessorTable`]), each matched exactly as LLVM matches it. Both keys
/// follow the one rule. For `"tune-cpu"` an undefined name drops only
/// tuning (llc 22.1.2 kept the hard-float convention for four of them), so
/// refusing it there is a stated over-refusal.
fn processor_refusal(key: &str, value: Option<&str>, table: ProcessorTable) -> Option<String> {
    let name = value.unwrap_or("");
    if let Some((processor, feature)) = MODE_IMPLYING_PROCESSORS
        .iter()
        .find(|(processor, _)| *processor == name)
    {
        return Some(format!(
            "LLVM 22's `{processor}` processor implies the target feature `{feature}`, which \
             changes how llc builds code; this importer builds for its own target and refuses \
             `+{feature}` alike"
        ));
    }
    if table.reads(name) {
        return None;
    }
    let consequence = if key == "target-cpu" {
        "llc ignores a name it does not define (with a warning) and sets none of a \
         processor's features: on AArch64 it then builds the function without `fp-armv8` or \
         `neon`, with the soft-float calling convention (a `double` passed in `x0`), where \
         this importer's backend builds the hard-float one"
    } else {
        "llc ignores a tuning name it does not define (with a warning); `\"tune-cpu\"` is read \
         by the rule `\"target-cpu\"` is, for which such a name makes llc build an AArch64 \
         function soft-float"
    };
    Some(format!(
        "processor {name:?} is not one LLVM 22 defines for {}, matched exactly as llc \
         matches it; {consequence}",
        table.describe()
    ))
}

/// Why the `"target-features"` value `value` is refused, or `None` when it
/// is read. This importer builds for its own target, whatever the module's
/// features say. A `+feature` enabling an instruction-set extension only
/// permits llc to use instructions the CPU then has, so the importer's code
/// runs wherever llc's does (llc ignores a name it does not know, with a
/// warning), except that on RISC-V the extensions `e`, `d` and `f` also
/// select llc's calling convention: a RISC-V definition's features are read
/// together for that ([`SubtargetSelection::riscv_refusal`]), not here. A
/// `+feature` among [`MODE_FEATURE_PREFIXES`], or one that
/// implies such a feature ([`MODE_IMPLYING_FEATURES`]), changes what llc
/// builds, and a `-feature` forbids instructions the importer's backend may
/// still use (`-neon`, `-fp-armv8`): both are refused, except `-fmv` (no
/// code-generation effect; llc clears a feature with every feature that
/// implies it, and no LLVM 22.1.2 feature implies `fmv`).
///
/// The value is split as LLVM splits it, at every `,` (after its escapes are
/// decoded: `\2C` is a `,`), with nothing trimmed: LLVM's verifier rejects
/// an empty entry and one that does not start with `+` or `-` (` +neon`).
fn target_features_refusal(value: &str) -> Option<String> {
    if value.is_empty() {
        return None;
    }
    for feature in value.split(',') {
        if feature.is_empty() {
            return Some(
                "an empty target feature between commas (LLVM's verifier rejects it)".to_string(),
            );
        }
        if let Some(name) = feature.strip_prefix('+') {
            if MODE_FEATURE_PREFIXES
                .iter()
                .any(|prefix| name.starts_with(prefix))
            {
                return Some(format!(
                    "target feature `{feature}` changes how llc builds code (registers, ABI, \
                     alignment, address tagging or speculation mitigations); this importer \
                     builds for its own target"
                ));
            }
            if let Some((_, implied)) = MODE_IMPLYING_FEATURES
                .iter()
                .find(|(implying, _)| *implying == name)
            {
                return Some(format!(
                    "target feature `{feature}` implies `{implied}` in LLVM 22, which changes \
                     how llc builds code; this importer builds for its own target and refuses \
                     `+{implied}` alike"
                ));
            }
        } else if let Some(name) = feature.strip_prefix('-') {
            if name != "fmv" {
                return Some(format!(
                    "target feature `{feature}` forbids instructions this importer's backend \
                     may still use"
                ));
            }
        } else {
            return Some(format!(
                "target feature `{feature}` without a `+` or `-` (LLVM's verifier rejects a \
                 feature that does not start with one)"
            ));
        }
    }
    None
}

/// A value LLVM reads as an unsigned base-ten integer that fits 32 bits
/// (`StringRef::getAsInteger(10, unsigned)`).
fn is_unsigned_base_ten(value: Option<&str>) -> bool {
    value.is_some_and(|value| {
        !value.is_empty()
            && value.bytes().all(|b| b.is_ascii_digit())
            && value.parse::<u32>().is_ok()
    })
}

/// A `denormal-fp-math` value LLVM's `parseDenormalFPAttribute` reads: one
/// or two comma-separated modes, each `ieee`, `preserve-sign`,
/// `positive-zero`, `dynamic` or empty.
fn is_denormal_mode(value: &str) -> bool {
    let mode = |part: &str| {
        matches!(
            part,
            "" | "ieee" | "preserve-sign" | "positive-zero" | "dynamic"
        )
    };
    match value.split_once(',') {
        Some((output, input)) => mode(output) && mode(input),
        None => mode(value),
    }
}

/// A `stack-probe-size` LLVM reads as the decimal it spells: LLVM parses the
/// value with radix auto-detection (`getAsInteger(0, ...)`), so a leading
/// `0`, `0x` or `0b` is octal, hexadecimal or binary there. Only plain
/// decimals (no leading zero) are read here, as the size they spell.
fn plain_decimal(value: Option<&str>) -> Option<u64> {
    let value = value?;
    let first = *value.as_bytes().first()?;
    (first != b'0' && value.bytes().all(|b| b.is_ascii_digit()))
        .then(|| value.parse::<u64>().ok())
        .flatten()
}

/// Whether a stack-probe interval `size`, as LLVM reads the attribute or
/// the module flag, is one the importer's AArch64 frames honor: from the
/// 4096 bytes they are probed at to `2^63 - 1`. LLVM 22's
/// `AArch64FunctionInfo` reads the interval as a `uint64_t` (the
/// attribute's decimal; the flag's `getZExtValue`, which asserts that the
/// value needs at most 64 bits, `APInt.h`, and otherwise yields its low
/// 64 bits) and asserts `int64_t(ProbeSize) > 0`: at `2^63` and above the
/// size is negative there, and a release llc 22 built a 300000-byte
/// inline-probed frame at `2^64 - 4096` that crashed where the importer's
/// ran. The flag passes its value zero-extended, so a constant is read by
/// value at any width the flag reader reads (up to 128 bits): `i128 8192`
/// is 8192, and a value of `2^64` or more, whose low 64 bits a release llc
/// would read, is refused. The attribute reader and the module-flag reader
/// share this predicate.
pub(crate) fn stack_probe_interval_read(size: u128) -> bool {
    (4096..1u128 << 63).contains(&size)
}

/// Why the string attribute `"key"` (`="value"`) is refused, or `None` when
/// it is read. An allowlist: every key it does not name is refused. `key`
/// and `value` are decoded as LLVM decodes them.
///
/// The boolean attributes follow LLVM 22's reading of each (a survey of the
/// readers in `lib/CodeGen`, `lib/Target` and `lib/IR`): the floating-point
/// permissions, `disable-tail-calls` and `use-soft-float` are read by value
/// (`getValueAsBool`, true only for `"true"`), and `nooutline` by
/// presence, each only ever restricting llc; `no-builtins` is read by
/// presence too (`TargetLibraryInfo`), and it and every `no-builtin-<name>`
/// are refused, because this importer's backend reads a call of a library
/// function by its name; `branch-target-enforcement` is read by presence
/// (`AArch64FunctionInfo`), so any value asks for BTI landing pads, and it
/// is refused. A processor name is read against `processors`, the compile
/// target's table ([`ProcessorTable`]).
pub(crate) fn string_attribute_refusal(
    key: &str,
    value: Option<&str>,
    processors: ProcessorTable,
) -> Option<String> {
    match key {
        // Floating-point permissions and environment assumptions: they let
        // llc relax a result; the importer computes the unrelaxed one, which
        // they permit too.
        "no-trapping-math"
        | "no-infs-fp-math"
        | "no-nans-fp-math"
        | "no-signed-zeros-fp-math"
        | "unsafe-fp-math"
        | "approx-func-fp-math"
        | "less-precise-fpmad"
        | "reciprocal-estimates"
        | "correctly-rounded-divide-sqrt-fp-math" => None,
        "denormal-fp-math" | "denormal-fp-math-f32" if is_denormal_mode(value.unwrap_or("")) => {
            None
        }
        "denormal-fp-math" | "denormal-fp-math-f32" => Some(
            "a denormal mode LLVM's verifier rejects (it reads `ieee`, `preserve-sign`, \
             `positive-zero` or `dynamic`, one or two of them)"
                .to_string(),
        ),
        // A processor: read only when LLVM 22 defines the name for the
        // compile target's architecture ([`ProcessorTable`]; an undefined
        // name sets no processor feature at all) and its features imply no
        // mode feature refused as a `+feature` ([`MODE_IMPLYING_PROCESSORS`]).
        // Every name read implies instruction-set extensions, which only add
        // instructions (but for the RISC-V calling convention, read with a
        // RISC-V definition's features, [`SubtargetSelection`]), and tuning.
        "target-cpu" | "tune-cpu" => processor_refusal(key, value, processors),
        // Tuning, optimization limits, diagnostics and allocator facts: no
        // effect on what the function computes.
        "min-legal-vector-width"
        | "prefer-vector-width"
        | "no-jump-tables"
        | "disable-tail-calls"
        | "nooutline"
        | "use-sample-profile"
        | "alloc-family" => None,
        // `TargetLibraryInfo` reads a function's calls as no calls of the
        // C library functions (every one, or the one named), whatever the
        // value; the backend reads them by name (`trust-cg-irmid`'s
        // memory-call pass, `passes/mem_call.rs`, among other readers).
        "no-builtins" => Some(
            "llc 22 reads none of this function's calls as calls of C library functions, and \
             keeps them as calls; this importer's backend reads a call of a library function by \
             its name (a call of a declared `memcpy` or `memset` with a constant count may \
             become loads and stores, calling nothing)"
                .to_string(),
        ),
        _ if key.starts_with("no-builtin-") => Some(
            "llc 22 reads none of this function's calls of the named function as calls of the C \
             library function, and keeps them as calls; this importer's backend reads a call of \
             a library function by its name (a call of a declared `memcpy` or `memset` with a \
             constant count may become loads and stores, calling nothing)"
                .to_string(),
        ),
        "warn-stack-size" if is_unsigned_base_ten(value) => None,
        "warn-stack-size" => Some(
            "a `warn-stack-size` that is not an unsigned base-ten integer (LLVM's verifier \
             rejects it)"
                .to_string(),
        ),
        "alloc-variant-zeroed" if value.is_some_and(|value| !value.is_empty()) => None,
        "alloc-variant-zeroed" => {
            Some("an empty `alloc-variant-zeroed` (LLVM's verifier rejects it)".to_string())
        }
        // Frame records serve stack walkers (debuggers, profilers); what the
        // function computes does not depend on them.
        "frame-pointer"
            if matches!(
                value,
                Some("none" | "non-leaf" | "all" | "reserved" | "non-leaf-no-reserve")
            ) =>
        {
            None
        }
        "frame-pointer" => Some(
            "a `frame-pointer` value LLVM's verifier rejects (it reads `none`, `non-leaf`, \
             `non-leaf-no-reserve`, `reserved` or `all`)"
                .to_string(),
        ),
        "target-features" => target_features_refusal(value.unwrap_or("")),
        // trust-cg-lower's `ssp` policy protects arrays of 8 bytes and up,
        // LLVM's default threshold.
        "stack-protector-buffer-size" if value == Some("8") => None,
        "stack-protector-buffer-size" => Some(
            "a stack-protector threshold other than LLVM's default 8 bytes, which the \
             importer's `ssp` policy uses"
                .to_string(),
        ),
        // AArch64 frames are always probed at most 4096 bytes apart, as
        // LLVM's `inline-asm` method does; x86-64 and RISC-V frames are
        // unprobed (LIMITATIONS.md). `__chkstk_darwin` is the probe function
        // Apple's clang names on every Darwin function; upstream llc 22 on
        // AArch64 aborts on any method but `inline-asm` ("Unsupported stack
        // probing method"), Apple's LLVM calls the function for frames over
        // a page, which probes them as the inline method does.
        "probe-stack" if matches!(value, Some("inline-asm" | "__chkstk_darwin")) => None,
        "probe-stack" => Some(
            "a stack probe method other than `inline-asm` or Apple's `__chkstk_darwin` (llc on \
             AArch64 aborts on it; on x86-64 llc calls the named function, which this importer \
             does not)"
                .to_string(),
        ),
        "stack-probe-size"
            if plain_decimal(value)
                .is_some_and(|size| stack_probe_interval_read(u128::from(size))) =>
        {
            None
        }
        "stack-probe-size" => Some(
            "a stack-probe interval that is not a plain decimal from the 4096 bytes AArch64 \
             frames are probed at to 2^63 - 1 (LLVM reads a leading `0`, `0x` or `0b` as \
             octal, hexadecimal or binary, and a size at or above 2^63 as a negative \
             `int64_t`, which its AArch64 frame lowering asserts against)"
                .to_string(),
        ),
        "use-soft-float" if value == Some("false") => None,
        "sign-return-address" if value == Some("none") => None,
        // Read with `sign-return-address`, which is admitted only as `none`;
        // a function's or call's attributes that hold the key without it
        // are refused ([`ReturnAddressSigning`]).
        "sign-return-address-key" if matches!(value, Some("a_key" | "b_key")) => None,
        "sign-return-address-key" => Some(
            "a return-address signing key other than `a_key` or `b_key` (LLVM's verifier \
             rejects it)"
                .to_string(),
        ),
        "branch-target-enforcement" => Some(
            "llc 22 builds BTI landing pads whenever this attribute is present, whatever its \
             value (`AArch64FunctionInfo` reads its presence; only under an ARM or AArch64 \
             `target triple` does LLVM's parser first drop a `\"false\"` one); this importer's \
             backend builds none"
                .to_string(),
        ),
        "use-soft-float" | "sign-return-address" => Some(
            "llc builds the floating-point ABI or return-address signing code it asks for; this \
             importer's backend does not"
                .to_string(),
        ),
        _ => Some(
            "not a string attribute this importer reads (it reads only attributes known to \
             change nothing the importer builds)"
                .to_string(),
        ),
    }
}

/// The two return-address-signing string attributes one function's or
/// call's attributes name, inline and through its group, for the checks
/// LLVM 22's verifier makes over them (`verifyFunctionAttrs`, for every
/// function and every call, a call to an intrinsic included):
/// `"sign-return-address-key"` without `"sign-return-address"` is rejected
/// ("'sign-return-address-key' present without `sign-return-address`"),
/// where each attribute alone reads as valid, and so is a
/// `"sign-return-address"` other than `none`, `all` or `non-leaf` and a key
/// other than `a_key` or `b_key`. [`string_attribute_refusal`] refuses
/// every value but `none` and the two keys wherever the importer reads an
/// attribute; the values matter here only for a call the importer drops
/// (`parser::is_droppable_intrinsic`), whose attributes it reads for these
/// checks alone ([`ReturnAddressSigning::scan`]).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct ReturnAddressSigning {
    /// `"sign-return-address"` is among them.
    scope: bool,
    /// `"sign-return-address-key"` is among them.
    key: bool,
    /// One of the two has a value LLVM's verifier rejects.
    rejected_value: bool,
}

impl ReturnAddressSigning {
    /// Note the string attribute whose key is `tokens[at]` of `text`, with
    /// its value when `="value"` follows (both decoded as LLVM decodes
    /// them; no value reads as LLVM's empty one).
    pub(crate) fn note(&mut self, text: &str, tokens: &[Token], at: usize) {
        let value = match (tokens.get(at + 1), tokens.get(at + 2)) {
            (Some(equal), Some(value))
                if equal.kind == Kind::Punct(b'=') && value.kind == Kind::Str =>
            {
                string_text(value.text(text))
            }
            _ => Some(String::new()),
        };
        let value = value.as_deref();
        match string_text(tokens[at].text(text)).as_deref() {
            Some("sign-return-address") => {
                self.scope = true;
                self.rejected_value |= !matches!(value, Some("none" | "all" | "non-leaf"));
            }
            Some("sign-return-address-key") => {
                self.key = true;
                self.rejected_value |= !matches!(value, Some("a_key" | "b_key"));
            }
            _ => {}
        }
    }

    /// The two attributes among the function attributes `tokens` of `text`
    /// (a group's body, or a call's text from its callee on), each group
    /// `#N` adding `group(#N)`'s, read for these checks alone, so a refused
    /// attribute stops nothing: a string attribute key (`"key"`, `"key" =
    /// "value"`, whose value is skipped) is noted, and every bracketed
    /// group (a call's argument list, an operand bundle `[...]`,
    /// `memory(...)`) is skipped.
    pub(crate) fn scan(text: &str, tokens: &[Token], group: &dyn Fn(&str) -> Self) -> Self {
        let mut signing = Self::default();
        let mut index = 0;
        while let Some(token) = tokens.get(index) {
            match token.kind {
                Kind::Punct(b'(' | b'[' | b'{' | b'<') => {
                    index = skip_bracket_group(tokens, index);
                    continue;
                }
                Kind::Str => {
                    signing.note(text, tokens, index);
                    if tokens
                        .get(index + 1)
                        .is_some_and(|equal| equal.kind == Kind::Punct(b'='))
                    {
                        index += 2;
                    }
                }
                Kind::AttrGroup => signing = signing.union(group(token.text(text))),
                _ => {}
            }
            index += 1;
        }
        signing
    }

    /// The attributes of `self` and `other` together (a function's or
    /// call's inline attributes and its group's).
    pub(crate) fn union(self, other: Self) -> Self {
        Self {
            scope: self.scope || other.scope,
            key: self.key || other.key,
            rejected_value: self.rejected_value || other.rejected_value,
        }
    }

    /// Why one function's or call's attributes are refused, or `None`.
    pub(crate) fn refusal(self) -> Option<String> {
        if self.key && !self.scope {
            return Some(
                "attribute `\"sign-return-address-key\"` without `\"sign-return-address\"` \
                 among the same function's or call's attributes (LLVM's verifier rejects it: \
                 \"'sign-return-address-key' present without `sign-return-address`\")"
                    .to_string(),
            );
        }
        self.rejected_value.then(|| {
            "a `\"sign-return-address\"` other than `none`, `all` or `non-leaf`, or a \
             `\"sign-return-address-key\"` other than `a_key` or `b_key` (LLVM's verifier \
             rejects it)"
                .to_string()
        })
    }
}

/// The index after the bracket group opened at `open` in `tokens`.
pub(crate) fn skip_bracket_group(tokens: &[Token], open: usize) -> usize {
    let mut depth = 0i32;
    let mut at = open;
    while let Some(token) = tokens.get(at) {
        depth += match token.kind {
            Kind::Punct(b'(' | b'[' | b'{' | b'<') => 1,
            Kind::Punct(b')' | b']' | b'}' | b'>') => -1,
            _ => 0,
        };
        at += 1;
        if depth <= 0 {
            break;
        }
    }
    at
}

/// The outcome of [`read_function_attribute`].
pub(crate) enum AttributeRead {
    /// An attribute, read; the index after it.
    Read(usize),
    /// `tokens[index]` starts no function attribute.
    NotAnAttribute,
    /// An attribute the importer refuses: its spelling and the reason.
    Refused(String),
}

/// Read the function attribute starting at `tokens[index]` of `text`: a
/// keyword (`nounwind`, `memory(none)`, `alignstack=16` in a group), a
/// string attribute (`"key"`, `"key"="value"`) or an attribute group
/// reference (`#0`, refused when `group_refusal` names a refused attribute
/// of that group). A processor name is read against `processors`
/// ([`string_attribute_refusal`]).
pub(crate) fn read_function_attribute(
    text: &str,
    tokens: &[Token],
    index: usize,
    group_refusal: &dyn Fn(&str) -> Option<String>,
    processors: ProcessorTable,
) -> AttributeRead {
    let Some(token) = tokens.get(index) else {
        return AttributeRead::NotAnAttribute;
    };
    let spelled = token.text(text);
    match token.kind {
        Kind::AttrGroup => match group_refusal(spelled) {
            Some(why) => AttributeRead::Refused(format!("attribute group `{spelled}`: {why}")),
            None => AttributeRead::Read(index + 1),
        },
        Kind::Word if is_function_attribute_keyword(spelled) => {
            let mut next = index + 1;
            match tokens.get(next).map(|t| t.kind) {
                Some(Kind::Punct(b'(')) => next = skip_bracket_group(tokens, next),
                // The attribute-group form `alignstack=16`.
                Some(Kind::Punct(b'='))
                    if tokens
                        .get(next + 1)
                        .is_some_and(|value| value.kind == Kind::Number) =>
                {
                    next += 2;
                }
                _ => {}
            }
            match keyword_attribute_refusal(spelled) {
                Some(why) => AttributeRead::Refused(format!(
                    "attribute `{}` ({why})",
                    text[token.start..tokens[next - 1].end].trim()
                )),
                None => AttributeRead::Read(next),
            }
        }
        Kind::Str => {
            // The key and value as LLVM reads them: `\XX` and `\\` decoded
            // (`"+v8a\2C+call-saved-x9"` is two features).
            let (value, next) = match (tokens.get(index + 1), tokens.get(index + 2)) {
                (Some(equal), Some(value))
                    if equal.kind == Kind::Punct(b'=') && value.kind == Kind::Str =>
                {
                    (Some(value.text(text)), index + 3)
                }
                (Some(equal), _) if equal.kind == Kind::Punct(b'=') => {
                    return AttributeRead::Refused(format!(
                        "string attribute {spelled} without a quoted value"
                    ));
                }
                _ => (None, index + 1),
            };
            let spelling = text[token.start..tokens[next - 1].end].trim();
            let (Some(key), Some(value)) = (
                string_text(spelled),
                value.map_or(Some(None), |value| string_text(value).map(Some)),
            ) else {
                return AttributeRead::Refused(format!(
                    "attribute `{spelling}` (a key or value that is not UTF-8 after LLVM's \
                     escapes; no attribute this importer reads is)"
                ));
            };
            match string_attribute_refusal(&key, value.as_deref(), processors) {
                Some(why) => AttributeRead::Refused(format!("attribute `{spelling}` ({why})")),
                None => AttributeRead::Read(next),
            }
        }
        _ => AttributeRead::NotAnAttribute,
    }
}

/// Read an `attributes #N = { ... }` group body (`body`, without the
/// braces): its first attribute the importer refuses, as
/// `` `spelling` (reason) `` (`None` when it reads every one), and the
/// return-address-signing attributes it names, all of them, refused or not,
/// which a function or call using the group adds to its own
/// ([`ReturnAddressSigning`]). A processor name is read against
/// `processors` ([`string_attribute_refusal`]).
pub(crate) fn read_attribute_group(
    body: &str,
    processors: ProcessorTable,
) -> (Option<String>, ReturnAddressSigning) {
    let tokens = match crate::lexical::lex(body) {
        Ok(tokens) => tokens,
        Err(error) => {
            return (
                Some(format!("an attribute group LLVM's lexer rejects ({error})")),
                ReturnAddressSigning::default(),
            );
        }
    };
    let signing = ReturnAddressSigning::scan(body, &tokens, &|_| ReturnAddressSigning::default());
    let mut index = 0;
    while index < tokens.len() {
        match read_function_attribute(body, &tokens, index, &|_| None, processors) {
            AttributeRead::Read(next) => index = next,
            AttributeRead::Refused(why) => return (Some(why), signing),
            AttributeRead::NotAnAttribute => {
                return (
                    Some(format!(
                        "`{}` (not a function attribute this importer reads)",
                        tokens[index].text(body)
                    )),
                    signing,
                );
            }
        }
    }
    (None, signing)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use serde_json::{Map, Value};

    use super::*;

    /// The subtarget feature and processor tables of LLVM 22.1.2's AArch64,
    /// RISCV and X86 targets, extracted from `llvm-tblgen --dump-json` by
    /// `scripts/extract_llvm_subtarget_features.py`.
    const LLVM22_TABLES: &str = include_str!("../tests/fixtures/llvm22_subtarget_features.json");

    fn is_mode_feature(name: &str) -> bool {
        MODE_FEATURE_PREFIXES
            .iter()
            .any(|prefix| name.starts_with(prefix))
    }

    /// The features `names` set in llc: each one and, transitively, every
    /// feature its `Implies` list names (every name must be a feature).
    fn closure<'a>(
        features: &'a Map<String, Value>,
        names: impl IntoIterator<Item = &'a str>,
    ) -> BTreeSet<&'a str> {
        let mut set = BTreeSet::new();
        let mut pending: Vec<&str> = names.into_iter().collect();
        while let Some(name) = pending.pop() {
            if set.insert(name) {
                let implied = features[name].as_array().expect("an `Implies` list");
                pending.extend(implied.iter().map(|name| name.as_str().expect("a name")));
            }
        }
        set
    }

    fn strings(value: &Value) -> impl Iterator<Item = &str> {
        value
            .as_array()
            .expect("a list")
            .iter()
            .map(|name| name.as_str().expect("a name"))
    }

    /// [`MODE_IMPLYING_FEATURES`] and [`MODE_IMPLYING_PROCESSORS`] are
    /// exactly what LLVM 22.1.2's tables imply: every feature (not itself
    /// among [`MODE_FEATURE_PREFIXES`]) whose `Implies` closure holds a
    /// feature among them, and every processor or alias whose feature and
    /// tuning lists' closure does, each with the first such feature; both
    /// readers refuse each entry. No feature but `fmv` itself sets `fmv`, so
    /// `-fmv` (the one `-feature` read) clears nothing else. The fourth
    /// verifier round of L02-P15 found `+thunderx3t110` admitted.
    #[test]
    fn mode_implying_tables_are_the_closure_of_llvms_tables() {
        let tables: Value = serde_json::from_str(LLVM22_TABLES).expect("the extract");
        let mut sizes = Vec::new();
        let mut implying_features = BTreeSet::new();
        let mut implying_processors = BTreeSet::new();
        for (target, tables) in tables["targets"].as_object().expect("targets") {
            let features = tables["features"].as_object().expect("features");
            let processors = tables["processors"].as_object().expect("processors");
            let aliases = tables["aliases"].as_object().expect("aliases");
            for name in features.keys() {
                let set = closure(features, [name.as_str()]);
                assert!(
                    name == "fmv" || !set.contains("fmv"),
                    "{target}: +{name} sets fmv"
                );
                if is_mode_feature(name) {
                    continue;
                }
                if let Some(mode) = set.into_iter().find(|feature| is_mode_feature(feature)) {
                    implying_features.insert((name.clone(), mode.to_string()));
                }
            }
            let definitions = processors
                .iter()
                .chain(aliases.iter().map(|(alias, processor)| {
                    (alias, &processors[processor.as_str().expect("a processor")])
                }));
            for (name, defs) in definitions {
                for def in defs.as_array().expect("definitions") {
                    let set = closure(
                        features,
                        strings(&def["features"]).chain(strings(&def["tune"])),
                    );
                    if let Some(mode) = set.into_iter().find(|feature| is_mode_feature(feature)) {
                        implying_processors.insert((name.clone(), mode.to_string()));
                    }
                }
            }
            sizes.push((
                target.clone(),
                features.len(),
                processors.len() + aliases.len(),
            ));
        }
        let sizes: Vec<_> = sizes.iter().map(|(t, f, p)| (t.as_str(), *f, *p)).collect();
        assert_eq!(
            sizes,
            [("AArch64", 349, 99), ("RISCV", 348, 51), ("X86", 199, 131)]
        );
        let table = |entries: &[(&str, &str)]| -> BTreeSet<(String, String)> {
            entries
                .iter()
                .map(|(name, mode)| ((*name).to_string(), (*mode).to_string()))
                .collect()
        };
        assert_eq!(implying_features, table(&MODE_IMPLYING_FEATURES));
        assert_eq!(implying_processors, table(&MODE_IMPLYING_PROCESSORS));
        for (name, mode) in MODE_IMPLYING_FEATURES {
            for value in [format!("+{name}"), format!("+v8a,+{name}")] {
                let why = string_attribute_refusal(
                    "target-features",
                    Some(&value),
                    ProcessorTable::Aarch64,
                )
                .unwrap_or_else(|| panic!("{value} read"));
                assert!(why.contains(&format!("implies `{mode}`")), "{value}: {why}");
            }
        }
        for (name, mode) in MODE_IMPLYING_PROCESSORS {
            for key in ["target-cpu", "tune-cpu"] {
                for processors in ALL_PROCESSOR_TABLES {
                    let why = string_attribute_refusal(key, Some(name), processors)
                        .unwrap_or_else(|| panic!("{key}={name} read for {processors:?}"));
                    assert!(why.contains(&format!("feature `{mode}`")), "{key}: {why}");
                }
            }
        }
        assert_eq!(
            string_attribute_refusal("target-features", Some("-fmv"), ProcessorTable::Aarch64),
            None
        );
    }

    const ALL_PROCESSOR_TABLES: [ProcessorTable; 5] = [
        ProcessorTable::Aarch64,
        ProcessorTable::Riscv,
        ProcessorTable::X86,
        ProcessorTable::NoTarget,
        ProcessorTable::Other,
    ];

    /// [`AARCH64_PROCESSOR_NAMES`], [`RISCV_PROCESSOR_NAMES`] and
    /// [`X86_PROCESSOR_NAMES`] are exactly the processor and alias names of
    /// LLVM 22.1.2's tables (the committed extract); the `Implies` closure of
    /// every AArch64 name's feature list holds `fp-armv8` and `neon`, the
    /// hard-float AAPCS this importer's backend builds; and the names all
    /// three tables define are `generic` alone. Each key reads, for each
    /// [`ProcessorTable`], exactly the names it defines but those of
    /// [`MODE_IMPLYING_PROCESSORS`], and the empty name wherever a table is
    /// read. The second closure audit of L02-P15 (2026-10-23) found every
    /// name but `thunderx3t110` read, defined or not.
    #[test]
    fn processor_name_tables_are_llvms() {
        let tables: Value = serde_json::from_str(LLVM22_TABLES).expect("the extract");
        for (target, names) in [
            ("AArch64", &AARCH64_PROCESSOR_NAMES[..]),
            ("RISCV", &RISCV_PROCESSOR_NAMES[..]),
            ("X86", &X86_PROCESSOR_NAMES[..]),
        ] {
            let target = &tables["targets"][target];
            let derived: BTreeSet<&str> = ["processors", "aliases"]
                .iter()
                .flat_map(|section| target[section].as_object().expect(section).keys())
                .map(String::as_str)
                .collect();
            // Sorted and without repeats: `ProcessorTable::reads` searches
            // them by bisection.
            assert_eq!(derived.into_iter().collect::<Vec<_>>(), names);
        }
        let aarch64 = &tables["targets"]["AArch64"];
        let features = aarch64["features"].as_object().expect("features");
        for name in AARCH64_PROCESSOR_NAMES {
            let processor = aarch64["aliases"][name].as_str().unwrap_or(name);
            for def in aarch64["processors"][processor]
                .as_array()
                .expect("definitions")
            {
                let set = closure(features, strings(&def["features"]));
                assert!(
                    set.contains("fp-armv8") && set.contains("neon"),
                    "{name} lacks fp-armv8 or neon"
                );
            }
        }
        let common: Vec<&str> = AARCH64_PROCESSOR_NAMES
            .into_iter()
            .filter(|name| {
                RISCV_PROCESSOR_NAMES.contains(name) && X86_PROCESSOR_NAMES.contains(name)
            })
            .collect();
        assert_eq!(common, ["generic"]);

        let every_name: BTreeSet<&str> = AARCH64_PROCESSOR_NAMES
            .into_iter()
            .chain(RISCV_PROCESSOR_NAMES)
            .chain(X86_PROCESSOR_NAMES)
            .collect();
        for processors in ALL_PROCESSOR_TABLES {
            let defined: &[&str] = match processors {
                ProcessorTable::Aarch64 => &AARCH64_PROCESSOR_NAMES,
                ProcessorTable::Riscv => &RISCV_PROCESSOR_NAMES,
                ProcessorTable::X86 => &X86_PROCESSOR_NAMES,
                ProcessorTable::NoTarget => &["generic"],
                ProcessorTable::Other => &[],
            };
            for key in ["target-cpu", "tune-cpu"] {
                for name in &every_name {
                    let mode = MODE_IMPLYING_PROCESSORS
                        .iter()
                        .any(|(processor, _)| processor == name);
                    let why = string_attribute_refusal(key, Some(name), processors);
                    assert_eq!(
                        why.is_none(),
                        defined.contains(name) && !mode,
                        "{processors:?} {key}={name}: {why:?}"
                    );
                }
                for value in [None, Some("")] {
                    let why = string_attribute_refusal(key, value, processors);
                    assert_eq!(
                        why.is_none(),
                        processors != ProcessorTable::Other,
                        "{processors:?} {key}={value:?}: {why:?}"
                    );
                }
            }
        }
    }

    /// [`RISCV_D_FEATURES`], [`RISCV_E_FEATURES`] and [`RISCV64_PROCESSORS`]
    /// are exactly what LLVM 22.1.2's RISCV table implies: the features
    /// whose `Implies` closure holds `d` and `e` (the extensions
    /// `RISCVISAInfo::computeDefaultABI` reads, with `f`), and the processors
    /// whose feature list's closure holds `64bit`, with whether it holds
    /// `d`. No processor's closure holds `e`, and no tuning list's closure
    /// holds `e`, `d`, `f` or a width, so `"tune-cpu"` selects no calling
    /// convention. [`SubtargetSelection::riscv_refusal`] refuses every
    /// selection that gives `lp64e` and, for a definition that names a
    /// floating-point or vector type, every one that does not give `lp64d`.
    /// The fifth verifier round of L02-P15 found `+e` and `+d` read as
    /// instruction-set extensions.
    #[test]
    fn riscv_calling_convention_tables_are_the_closure_of_llvms_tables() {
        let tables: Value = serde_json::from_str(LLVM22_TABLES).expect("the extract");
        let riscv = &tables["targets"]["RISCV"];
        let features = riscv["features"].as_object().expect("features");
        let processors = riscv["processors"].as_object().expect("processors");
        assert!(
            riscv["aliases"].as_object().expect("aliases").is_empty(),
            "RISCV processor aliases"
        );
        for extension in ["e", "d", "f", "64bit"] {
            assert!(features.contains_key(extension), "{extension}");
        }
        let implying = |extension: &str| -> BTreeSet<String> {
            features
                .keys()
                .filter(|name| closure(features, [name.as_str()]).contains(extension))
                .cloned()
                .collect()
        };
        let names = |table: &[&str]| -> BTreeSet<String> {
            table.iter().map(|name| (*name).to_string()).collect()
        };
        assert_eq!(implying("d"), names(&RISCV_D_FEATURES));
        assert_eq!(implying("e"), names(&RISCV_E_FEATURES));
        assert_eq!(implying("f"), names(&RISCV_F_FEATURES));
        // None of them names an AArch64 or x86 feature: read with no
        // target known, they refuse nothing those targets' llc reads.
        for target in ["AArch64", "X86"] {
            let other = tables["targets"][target]["features"]
                .as_object()
                .expect("features");
            for name in RISCV_E_FEATURES.iter().chain(RISCV_F_FEATURES.iter()) {
                assert!(!other.contains_key(*name), "{target} {name}");
            }
        }
        let mut rv64 = BTreeSet::new();
        for (name, defs) in processors {
            let defs = defs.as_array().expect("definitions");
            assert_eq!(defs.len(), 1, "{name}");
            let set = closure(features, strings(&defs[0]["features"]));
            assert!(!set.contains("e"), "{name} implies e");
            // A 64-bit processor selects `lp64d` or the default `lp64`,
            // never `lp64f`, so a selection stating no `e`/`f` feature is
            // the default or `lp64d` (`riscv_refusal_without_target`).
            assert!(
                !(set.contains("64bit") && set.contains("f") && !set.contains("d")),
                "{name} implies f without d"
            );
            let tune = closure(features, strings(&defs[0]["tune"]));
            for extension in ["e", "d", "f", "64bit", "32bit"] {
                assert!(!tune.contains(extension), "{name} tunes {extension}");
            }
            if set.contains("64bit") {
                rv64.insert((name.clone(), set.contains("d")));
            }
        }
        let table: BTreeSet<(String, bool)> = RISCV64_PROCESSORS
            .iter()
            .map(|(name, d)| ((*name).to_string(), *d))
            .collect();
        assert_eq!(rv64, table);

        let selection = |cpu: Option<&str>, features: Option<&str>| SubtargetSelection {
            cpus: cpu.into_iter().map(str::to_string).collect(),
            features: features.into_iter().map(str::to_string).collect(),
        };
        for floating in [true, false] {
            for feature in RISCV_D_FEATURES {
                let value = format!("+{feature}");
                let why = selection(None, Some(&value)).riscv_refusal(64, floating);
                assert_eq!(why, None, "{value}");
                for e in RISCV_E_FEATURES {
                    let value = format!("+{e},+{feature}");
                    let why = selection(None, Some(&value)).riscv_refusal(64, floating);
                    assert!(why.is_some_and(|why| why.contains("lp64e")), "{value}");
                }
            }
            for (processor, _) in RISCV64_PROCESSORS {
                let with_d = selection(Some(processor), Some("+d"));
                assert_eq!(with_d.riscv_refusal(64, floating), None, "{processor} +d");
                let alone = selection(Some(processor), None);
                assert!(alone.riscv_refusal(32, floating).is_some(), "{processor}");
            }
        }
        // Without `d`, only a definition that names a floating-point or
        // vector type is refused: the conventions place integers alike.
        for (processor, d) in RISCV64_PROCESSORS {
            let alone = selection(Some(processor), None);
            assert_eq!(alone.riscv_refusal(64, true).is_none(), d, "{processor}");
            assert_eq!(alone.riscv_refusal(64, false), None, "{processor}");
        }
        for cpu in [
            None,
            Some(""),
            Some("generic"),
            Some("generic-rv32"),
            Some("sifive-e76"),
            Some("rocket"),
            Some("nosuchcpu"),
        ] {
            for features in [None, Some("+f,+m")] {
                let refusal = selection(cpu, features).riscv_refusal(64, true);
                assert!(refusal.is_some(), "{cpu:?} {features:?}");
                let refusal = selection(cpu, features).riscv_refusal(64, false);
                assert_eq!(refusal, None, "{cpu:?} {features:?}");
            }
            let refusal = selection(cpu, Some("+m,+d")).riscv_refusal(64, true);
            assert_eq!(refusal, None, "{cpu:?}");
        }
        // Two statements of a key: each must give `d` for a definition that
        // names a floating-point type.
        let two = SubtargetSelection {
            cpus: Vec::new(),
            features: vec!["+d".to_string(), "+m".to_string()],
        };
        assert!(two.riscv_refusal(64, true).is_some());
        assert_eq!(two.riscv_refusal(64, false), None);

        // With no target known, a definition stating a feature that selects
        // a RISC-V convention is read as for 64-bit RISC-V; one stating
        // none, whatever its processor, is not read (the sixth verifier
        // round of L02-P15 found a triple-less `+e` module compiled for
        // `riscv64` read as an extension).
        for floating in [true, false] {
            for e in RISCV_E_FEATURES {
                for list in [format!("+{e}"), format!("+m,+{e},+d")] {
                    let why = selection(None, Some(&list)).riscv_refusal_without_target(floating);
                    assert!(
                        why.is_some_and(|why| why.contains("lp64e") && why.contains("no target")),
                        "{list}"
                    );
                }
            }
            for feature in RISCV_D_FEATURES {
                let list = format!("+{feature}");
                let why = selection(None, Some(&list)).riscv_refusal_without_target(floating);
                assert_eq!(why, None, "{list}");
            }
            for feature in RISCV_F_FEATURES {
                let list = format!("+m,+{feature}");
                let why = selection(None, Some(&list)).riscv_refusal_without_target(floating);
                let d = RISCV_D_FEATURES.contains(&feature);
                assert_eq!(why.is_some(), floating && !d, "{list}");
                let with_d = selection(Some("sifive-u74"), Some(&list));
                assert_eq!(
                    with_d.riscv_refusal_without_target(floating),
                    None,
                    "{list}"
                );
            }
            for (processor, _) in RISCV64_PROCESSORS {
                for list in [None, Some("+m,+neon"), Some("-fmv")] {
                    let alone = selection(Some(processor), list);
                    assert_eq!(alone.riscv_refusal_without_target(floating), None);
                }
            }
        }
    }
}
