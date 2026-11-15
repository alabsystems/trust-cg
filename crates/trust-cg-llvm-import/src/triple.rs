// trust-cg-llvm-import / triple.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The compile target as LLVM 22.1.2's `Triple` reads a target triple: the
// facts the importer's rules depend on (the object format and the RISC-V
// width), derived in one place.

/// An object file format, as LLVM names them (`Triple::ObjectFormatType`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ObjectFormat {
    Coff,
    DxContainer,
    Elf,
    Goff,
    MachO,
    Spirv,
    Wasm,
    Xcoff,
}

impl ObjectFormat {
    /// The format's name in a diagnostic.
    pub(crate) fn name(self) -> &'static str {
        match self {
            Self::Coff => "COFF",
            Self::DxContainer => "DXContainer",
            Self::Elf => "ELF",
            Self::Goff => "GOFF",
            Self::MachO => "Mach-O",
            Self::Spirv => "SPIR-V",
            Self::Wasm => "Wasm",
            Self::Xcoff => "XCOFF",
        }
    }
}

/// The facts of a target triple the importer's rules read, as LLVM's
/// `Triple` constructor derives them from the string (`Triple::Triple`,
/// `parseArch`, `parseOS`, `parseFormat`, `getDefaultFormat` in
/// `llvm/lib/TargetParser/Triple.cpp`, LLVM 22.1.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TargetTriple {
    /// `Triple::getObjectFormat`: the format the triple's last component
    /// names by its ending (`-elf`, `-macho`, `-coff`, ...), or else the
    /// architecture's and OS's default. llc writes this format, and it
    /// decides LLVM's symbol prefixes (`_` and the private `L`/`l` on
    /// Mach-O, the private `.L` on ELF).
    pub(crate) object_format: ObjectFormat,
    /// The width of a RISC-V architecture (`riscv32`, `riscv32be`: 32;
    /// `riscv64`, `riscv64be`: 64), or `None` for any other.
    pub(crate) riscv_xlen: Option<u32>,
    /// Whether the architecture is spelled `aarch64` or `arm64`, two of the
    /// names `parseArch` reads as the little-endian 64-bit `Triple::aarch64`
    /// (the spelling `trust-cg-codegen`'s `TargetSpec::triple` writes is
    /// `aarch64`). Its other names (`arm64e`, `arm64ec`, `aarch64` with an
    /// ARM version) are not read as it: a rule admitting only AArch64 fails
    /// closed on them.
    pub(crate) aarch64: bool,
    /// Whether `parseArch` reads the architecture as `x86` (`i386` to
    /// `i986`) or `x86_64` (`amd64`, `x86_64`, `x86_64h`), the two LLVM's
    /// X86 target builds.
    pub(crate) x86: bool,
    /// Whether LLVM's `TargetLibraryInfo` has `memset_pattern16` (and `4`,
    /// `8`) for the triple's OS: macOS (`Triple::isMacOSX`, the OS names
    /// `darwin` and `macos`), iOS and tvOS (`isiOS`) and watchOS
    /// (`TargetLibraryInfo.cpp`, `initializeBase`). The version bounds it
    /// also reads (macOS 10.5, iOS 3.0) are not read here.
    pub(crate) memset_pattern_os: bool,
}

impl TargetTriple {
    /// Whether llc writes a Mach-O object for this target
    /// (`Triple::isOSBinFormatMachO`).
    pub(crate) fn is_mach_o(self) -> bool {
        self.object_format == ObjectFormat::MachO
    }

    /// Whether llc writes an ELF object for this target
    /// (`Triple::isOSBinFormatELF`).
    pub(crate) fn is_elf(self) -> bool {
        self.object_format == ObjectFormat::Elf
    }

    /// Whether the target is AArch64 ([`Self::aarch64`]) and llc writes an
    /// ELF object for it.
    pub(crate) fn is_aarch64_elf(self) -> bool {
        self.aarch64 && self.is_elf()
    }
}

/// The architectures as far as `getDefaultFormat` tells them apart.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Arch {
    /// `UnknownArch`, `aarch64`, `aarch64_32`, `arm`, `thumb`, `x86` and
    /// `x86_64`: COFF on Windows and UEFI, Mach-O on a Darwin OS, else ELF.
    CoffMachOElf,
    /// `mipsel`: COFF on Windows, else ELF.
    Mipsel,
    /// `ppc` and `ppc64`: XCOFF on AIX, Mach-O on a Darwin OS, else ELF.
    PowerPc,
    /// `systemz`: GOFF on z/OS, else ELF.
    SystemZ,
    Wasm,
    Spirv,
    Dxil,
    Riscv32,
    Riscv64,
    /// Every other architecture LLVM names: always ELF.
    Elf,
}

/// The operating systems as far as `getDefaultFormat` tells them apart.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Os {
    /// `Triple::isOSDarwin`: Darwin, macOS, iOS, tvOS, watchOS, DriverKit,
    /// visionOS (`xros`) and bridgeOS.
    Darwin,
    /// `Win32` (`win32`, `windows`).
    Windows,
    Uefi,
    Aix,
    /// z/OS (`zos`).
    Zos,
    Other,
}

/// Read `triple` as LLVM's `Triple` constructor reads it (no
/// normalization: LLVM's parser keeps a module's `target triple` as
/// written, while llc normalizes an `-mtriple`; the triples this crate's
/// driver passes are in normal form).
pub(crate) fn read(triple: &str) -> TargetTriple {
    // `StringRef::split(Components, '-', /*MaxSplit*/ 3)`: at most four
    // components, the last holding every later `-`.
    let components: Vec<&[u8]> = triple.as_bytes().splitn(4, |&byte| byte == b'-').collect();
    let arch = parse_arch(components[0]);
    let os = components.get(2).map_or(Os::Other, |os| parse_os(os));
    let object_format = components
        .get(3)
        .and_then(|environment| parse_format(environment))
        .unwrap_or_else(|| default_format(arch, os));
    let riscv_xlen = match arch {
        Arch::Riscv32 => Some(32),
        Arch::Riscv64 => Some(64),
        _ => None,
    };
    TargetTriple {
        object_format,
        riscv_xlen,
        aarch64: matches!(components[0], b"aarch64" | b"arm64"),
        x86: matches!(
            components[0],
            b"i386"
                | b"i486"
                | b"i586"
                | b"i686"
                | b"i786"
                | b"i886"
                | b"i986"
                | b"amd64"
                | b"x86_64"
                | b"x86_64h"
        ),
        memset_pattern_os: components.get(2).is_some_and(|os| has_memset_pattern(os)),
    }
}

/// `parseOS` reads the OS `darwin`, `macos`, `ios`, `tvos` or `watchos`,
/// for which `TargetLibraryInfo` has `memset_pattern16` (no OS name LLVM
/// lists before them is a prefix of one of them).
fn has_memset_pattern(os: &[u8]) -> bool {
    [&b"darwin"[..], b"ios", b"macos", b"tvos", b"watchos"]
        .iter()
        .any(|name| os.starts_with(name))
}

/// `parseFormat`: the format the component's ending names, in LLVM's order
/// (`xcoff` before `coff`).
fn parse_format(environment: &[u8]) -> Option<ObjectFormat> {
    [
        (&b"xcoff"[..], ObjectFormat::Xcoff),
        (b"coff", ObjectFormat::Coff),
        (b"elf", ObjectFormat::Elf),
        (b"goff", ObjectFormat::Goff),
        (b"macho", ObjectFormat::MachO),
        (b"wasm", ObjectFormat::Wasm),
        (b"spirv", ObjectFormat::Spirv),
    ]
    .into_iter()
    .find(|(ending, _)| environment.ends_with(ending))
    .map(|(_, format)| format)
}

/// `getDefaultFormat`.
fn default_format(arch: Arch, os: Os) -> ObjectFormat {
    match arch {
        Arch::CoffMachOElf => match os {
            Os::Windows | Os::Uefi => ObjectFormat::Coff,
            Os::Darwin => ObjectFormat::MachO,
            _ => ObjectFormat::Elf,
        },
        Arch::Mipsel if os == Os::Windows => ObjectFormat::Coff,
        Arch::PowerPc if os == Os::Aix => ObjectFormat::Xcoff,
        Arch::PowerPc if os == Os::Darwin => ObjectFormat::MachO,
        Arch::SystemZ if os == Os::Zos => ObjectFormat::Goff,
        Arch::Wasm => ObjectFormat::Wasm,
        Arch::Spirv => ObjectFormat::Spirv,
        Arch::Dxil => ObjectFormat::DxContainer,
        _ => ObjectFormat::Elf,
    }
}

/// `parseOS`: LLVM matches each OS name as a prefix of the component, in
/// its order; only the names `getDefaultFormat` reads are told apart (none
/// of the names before them in LLVM's list is a prefix of one of them).
fn parse_os(os: &[u8]) -> Os {
    const DARWIN: [&[u8]; 9] = [
        b"darwin",
        b"ios",
        b"macos",
        b"tvos",
        b"watchos",
        b"bridgeos",
        b"driverkit",
        b"xros",
        b"visionos",
    ];
    if DARWIN.iter().any(|name| os.starts_with(name)) {
        Os::Darwin
    } else if os.starts_with(b"win32") || os.starts_with(b"windows") {
        Os::Windows
    } else if os.starts_with(b"uefi") {
        Os::Uefi
    } else if os.starts_with(b"aix") {
        Os::Aix
    } else if os.starts_with(b"zos") {
        Os::Zos
    } else {
        Os::Other
    }
}

/// `parseArch`, as far as `getDefaultFormat` and the RISC-V width tell the
/// architectures apart.
fn parse_arch(name: &[u8]) -> Arch {
    let exact = match name {
        b"i386" | b"i486" | b"i586" | b"i686" | b"i786" | b"i886" | b"i986" | b"amd64"
        | b"x86_64" | b"x86_64h" | b"xscale" | b"aarch64" | b"aarch64_32" | b"aarch64_lfi"
        | b"arm64" | b"arm64_32" | b"arm64e" | b"arm64ec" | b"arm" | b"thumb" => {
            Some(Arch::CoffMachOElf)
        }
        b"powerpc" | b"powerpcspe" | b"ppc" | b"ppc32" | b"powerpc64" | b"ppu" | b"ppc64" => {
            Some(Arch::PowerPc)
        }
        b"mipsel" | b"mipsallegrexel" | b"mipsisa32r6el" | b"mipsr6el" => Some(Arch::Mipsel),
        b"riscv32" | b"riscv32be" => Some(Arch::Riscv32),
        b"riscv64" | b"riscv64be" => Some(Arch::Riscv64),
        b"s390x" | b"systemz" => Some(Arch::SystemZ),
        b"wasm32" | b"wasm64" => Some(Arch::Wasm),
        b"spirv" | b"spirv1.5" | b"spirv1.6" | b"spirv32" | b"spirv32v1.0" | b"spirv32v1.1"
        | b"spirv32v1.2" | b"spirv32v1.3" | b"spirv32v1.4" | b"spirv32v1.5" | b"spirv32v1.6"
        | b"spirv64" | b"spirv64v1.0" | b"spirv64v1.1" | b"spirv64v1.2" | b"spirv64v1.3"
        | b"spirv64v1.4" | b"spirv64v1.5" | b"spirv64v1.6" => Some(Arch::Spirv),
        b"dxil" | b"dxilv1.0" | b"dxilv1.1" | b"dxilv1.2" | b"dxilv1.3" | b"dxilv1.4"
        | b"dxilv1.5" | b"dxilv1.6" | b"dxilv1.7" | b"dxilv1.8" | b"dxilv1.9" => Some(Arch::Dxil),
        b"powerpcle" | b"ppcle" | b"ppc32le" | b"powerpc64le" | b"ppc64le" | b"xscaleeb"
        | b"aarch64_be" | b"arc" | b"armeb" | b"thumbeb" | b"avr" | b"m68k" | b"msp430"
        | b"mips" | b"mipseb" | b"mipsallegrex" | b"mipsisa32r6" | b"mipsr6" | b"mips64"
        | b"mips64eb" | b"mipsn32" | b"mipsisa64r6" | b"mips64r6" | b"mipsn32r6" | b"mips64el"
        | b"mipsn32el" | b"mipsisa64r6el" | b"mips64r6el" | b"mipsn32r6el" | b"r600"
        | b"amdgcn" | b"hexagon" | b"sparc" | b"sparcel" | b"sparcv9" | b"sparc64" | b"tce"
        | b"tcele" | b"xcore" | b"nvptx" | b"nvptx64" | b"amdil" | b"amdil64" | b"hsail"
        | b"hsail64" | b"spir" | b"spir64" | b"lanai" | b"renderscript32" | b"renderscript64"
        | b"shave" | b"ve" | b"csky" | b"loongarch32" | b"loongarch64" | b"xtensa" => {
            Some(Arch::Elf)
        }
        _ if name.starts_with(b"kalimba") => Some(Arch::Elf),
        _ => None,
    };
    if let Some(arch) = exact {
        return arch;
    }
    // `UnknownArch` so far: LLVM's special parsing of ARM and BPF names.
    if name.starts_with(b"arm") || name.starts_with(b"thumb") || name.starts_with(b"aarch64") {
        return parse_arm_arch(name);
    }
    if name.starts_with(b"bpf") {
        return match name {
            b"bpf" | b"bpf_be" | b"bpfeb" | b"bpf_le" | b"bpfel" => Arch::Elf,
            _ => Arch::CoffMachOElf,
        };
    }
    // `UnknownArch`.
    Arch::CoffMachOElf
}

/// `parseARMArch`: a little-endian name, or one LLVM does not read, is
/// `arm`, `thumb`, `aarch64` or `UnknownArch` (one default each); a
/// big-endian one is `armeb`, `thumbeb` or `aarch64_be` (ELF) unless its
/// canonical name is invalid, or a Thumb name names version 2 or 3
/// (`UnknownArch`). Version 6-M is `thumb`/`thumbeb`, which changes no
/// default.
fn parse_arm_arch(name: &[u8]) -> Arch {
    // `ARM::parseArchEndian`.
    let big_endian = name.starts_with(b"armeb")
        || name.starts_with(b"thumbeb")
        || name.starts_with(b"aarch64_be")
        || ((name.starts_with(b"arm") || name.starts_with(b"thumb")) && name.ends_with(b"eb"));
    if !big_endian {
        return Arch::CoffMachOElf;
    }
    // `ARM::parseArchISA` (every big-endian name has one).
    let thumb =
        !name.starts_with(b"aarch64") && !name.starts_with(b"arm64") && name.starts_with(b"thumb");
    let canonical = arm_canonical_arch_name(name);
    if canonical.is_empty()
        || (thumb && (canonical.starts_with(b"v2") || canonical.starts_with(b"v3")))
    {
        return Arch::CoffMachOElf;
    }
    Arch::Elf
}

/// `ARM::getCanonicalArchName`, with `StringRef`'s clamping `substr`; the
/// empty result is LLVM's error.
fn arm_canonical_arch_name(arch: &[u8]) -> &[u8] {
    fn substr(bytes: &[u8], start: usize, length: usize) -> &[u8] {
        let start = start.min(bytes.len());
        &bytes[start..bytes.len().min(start.saturating_add(length))]
    }
    fn contains(bytes: &[u8], needle: &[u8]) -> bool {
        bytes.windows(needle.len()).any(|window| window == needle)
    }
    let mut offset: Option<usize> = None;
    let mut rest = arch;
    if rest.starts_with(b"arm64_32") {
        offset = Some(8);
    } else if rest.starts_with(b"arm64e") {
        offset = Some(6);
    } else if rest.starts_with(b"arm64") {
        offset = Some(5);
    } else if rest.starts_with(b"aarch64_32") {
        offset = Some(10);
    } else if rest.starts_with(b"arm") {
        offset = Some(3);
    } else if rest.starts_with(b"thumb") {
        offset = Some(5);
    } else if rest.starts_with(b"aarch64") {
        // AArch64 spells big-endian `_be`, never `eb`.
        if contains(rest, b"eb") {
            return &[];
        }
        offset = Some(if substr(rest, 7, 3) == b"_be" { 10 } else { 7 });
    }
    match offset {
        // `armebv7`: past the `eb`.
        Some(at) if substr(rest, at, 2) == b"eb" => offset = Some(at + 2),
        // `armv7eb`: the `eb` chopped off.
        _ => rest = rest.strip_suffix(b"eb").unwrap_or(rest),
    }
    if let Some(at) = offset {
        rest = substr(rest, at, usize::MAX);
    }
    if rest.is_empty() {
        return arch;
    }
    if offset.is_some() {
        // A version name: `v` and a digit, and no second `eb`.
        if rest.len() >= 2 && (rest[0] != b'v' || !rest[1].is_ascii_digit()) {
            return &[];
        }
        if contains(rest, b"eb") {
            return &[];
        }
    }
    rest
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Triples read as LLVM 22.1.2's `Triple` reads them: the object format
    /// a `-elf`/`-macho`/`-coff` ending names over the default, the
    /// defaults by architecture and OS (Mach-O only for the `aarch64`,
    /// `arm`, `x86` and unknown families and `ppc` on a Darwin OS), no
    /// normalization, and the RISC-V width. Each row is what the LLVM
    /// 22.1.2 TargetParser library printed for it (the sixth verifier round
    /// of L02-P15 found `arm64-apple-macosx14.0.0-elf` read as Mach-O, by
    /// its OS alone).
    #[test]
    fn triples_are_read_as_llvm_reads_them() {
        use ObjectFormat::*;
        for (triple, format, xlen) in [
            ("arm64-apple-macosx14.0.0", MachO, None),
            ("arm64-apple-macosx14.0.0-elf", Elf, None),
            ("arm64-apple-none-elf", Elf, None),
            ("aarch64-apple-darwin", MachO, None),
            ("x86_64-apple-darwin23", MachO, None),
            ("arm64-apple-ios17.0.0-simulator", MachO, None),
            ("arm64-apple-xros1.0", MachO, None),
            // Every other Darwin OS name `parseOS` reads (`isOSDarwin`) and
            // the `win32` spelling of Windows: llc 22.1.2 wrote a Mach-O
            // object for each Apple row and a COFF one for each `win32` row
            // (`llvm-readobj --file-headers`; the fourth verifier round of
            // L02-P13 found these names decided by no test).
            ("arm64-apple-tvos17.0", MachO, None),
            ("x86_64-apple-tvos17.0", MachO, None),
            ("arm64-apple-watchos10.0", MachO, None),
            ("arm64_32-apple-watchos10.0", MachO, None),
            ("aarch64_32-apple-watchos10.0", MachO, None),
            ("arm64-apple-bridgeos8.0", MachO, None),
            ("arm64-apple-driverkit23.0", MachO, None),
            ("arm64-apple-visionos1.0", MachO, None),
            ("x86_64-pc-win32", Coff, None),
            ("aarch64-pc-win32", Coff, None),
            ("x86_64-apple-macosx-gnu-coff", Coff, None),
            ("aarch64-unknown-linux-gnu", Elf, None),
            ("aarch64-unknown-linux-gnu-macho", MachO, None),
            ("x86_64-unknown-linux-gnu-myself", Elf, None),
            ("aarch64-linux-gnu", Elf, None),
            ("arm64-macosx", Elf, None),
            ("arm64-apple", Elf, None),
            ("x86_64-pc-windows-msvc", Coff, None),
            ("aarch64-unknown-uefi", Coff, None),
            ("x86_64-pc-windows-msvc-elf", Elf, None),
            ("x86_64-unknown-linux-xcoff", Xcoff, None),
            ("aarch64-unknown-linux-gnu-coff", Coff, None),
            ("aarch64-apple-darwin-goff", Goff, None),
            ("aarch64-apple-darwin-wasm", Wasm, None),
            ("aarch64-apple-darwin-spirv", Spirv, None),
            ("foo-apple-darwin", MachO, None),
            ("powerpc-apple-darwin", MachO, None),
            ("powerpc-ibm-aix", Xcoff, None),
            ("powerpc64le-apple-darwin", Elf, None),
            ("mips-apple-darwin", Elf, None),
            ("mipsel-pc-windows", Coff, None),
            ("s390x-ibm-zos", Goff, None),
            ("wasm32-unknown-unknown", Wasm, None),
            ("spirv64-unknown-unknown", Spirv, None),
            ("dxil-pc-shadermodel6.0", DxContainer, None),
            ("armebv7-apple-darwin", Elf, None),
            ("armv7eb-apple-darwin", Elf, None),
            ("armebxyz-apple-darwin", MachO, None),
            ("thumbebv3-apple-darwin", MachO, None),
            ("thumbebv6m-apple-darwin", Elf, None),
            ("aarch64_be-apple-darwin", Elf, None),
            ("aarch64_bev8-apple-darwin", Elf, None),
            ("aarch64eb-apple-darwin", MachO, None),
            ("arm64eb-apple-darwin", Elf, None),
            ("bpf-apple-darwin", Elf, None),
            ("bpfx-apple-darwin", MachO, None),
            ("kalimba3-apple-darwin", Elf, None),
            ("riscv64-apple-darwin", Elf, Some(64)),
            ("riscv64-unknown-linux-gnu", Elf, Some(64)),
            ("riscv64be-unknown-elf", Elf, Some(64)),
            ("riscv32-unknown-elf", Elf, Some(32)),
            ("riscv64", Elf, Some(64)),
            ("riscv64gc-unknown-linux-gnu", Elf, None),
            ("", Elf, None),
        ] {
            let read = read(triple);
            assert_eq!(
                (read.object_format, read.riscv_xlen),
                (format, xlen),
                "{triple}"
            );
        }
    }

    /// The AArch64 spellings the relocation-model rule reads
    /// ([`TargetTriple::is_aarch64_elf`]): `aarch64` and `arm64` with an ELF
    /// object, and no other architecture, AArch64 name or object format.
    #[test]
    fn aarch64_elf_is_read_for_its_two_spellings() {
        for (triple, aarch64, aarch64_elf) in [
            ("aarch64-unknown-linux-gnu", true, true),
            ("arm64-unknown-linux-gnu", true, true),
            ("aarch64", true, true),
            ("aarch64-unknown-none-elf", true, true),
            ("aarch64-apple-darwin", true, false),
            ("aarch64-unknown-linux-gnu-macho", true, false),
            ("aarch64-pc-windows-msvc", true, false),
            ("arm64e-apple-ios", false, false),
            ("aarch64_be-unknown-linux-gnu", false, false),
            ("aarch64_32-unknown-linux-gnu", false, false),
            ("x86_64-unknown-linux-gnu", false, false),
            ("riscv64-unknown-linux-gnu", false, false),
            ("", false, false),
        ] {
            let read = read(triple);
            assert_eq!(
                (read.aarch64, read.is_aarch64_elf()),
                (aarch64, aarch64_elf),
                "{triple}"
            );
        }
    }

    /// The x86 spellings the processor-name rule reads
    /// ([`TargetTriple::x86`], `attributes::ProcessorTable`): the names
    /// `parseArch` reads as `x86` or `x86_64`, and no other.
    #[test]
    fn x86_is_read_for_llvms_x86_names() {
        for (triple, x86) in [
            ("x86_64-unknown-linux-gnu", true),
            ("x86_64h-apple-darwin", true),
            ("amd64-unknown-freebsd", true),
            ("i386-pc-linux-gnu", true),
            ("i686-pc-windows-msvc", true),
            ("i986", true),
            ("x86-64-unknown-linux-gnu", false),
            ("i86-pc-linux-gnu", false),
            ("aarch64-unknown-linux-gnu", false),
            ("riscv64-unknown-linux-gnu", false),
            ("", false),
        ] {
            assert_eq!(read(triple).x86, x86, "{triple}");
        }
    }

    /// LLVM 22.1.2's `TargetLibraryInfo` has `memset_pattern16` for the OS
    /// macOS (`darwin`, `macos`), iOS, tvOS and watchOS, read by `parseOS`
    /// as a prefix of the third component, and for no other Darwin OS
    /// (bridgeOS, DriverKit, visionOS), whatever the object format.
    #[test]
    fn memset_pattern_is_read_for_the_os_llvm_gives_it() {
        for (triple, has) in [
            ("arm64-apple-macosx14.0.0", true),
            ("aarch64-apple-darwin", true),
            ("x86_64-apple-darwin23", true),
            ("arm64-apple-ios17.0.0-simulator", true),
            ("arm64-apple-tvos17.0", true),
            ("arm64-apple-watchos10.0", true),
            ("arm64-apple-macosx14.0.0-elf", true),
            ("arm64-apple-xros1.0", false),
            ("arm64-apple-visionos1.0", false),
            ("arm64-apple-driverkit23.0", false),
            ("arm64-apple-bridgeos8.0", false),
            ("aarch64-unknown-linux-gnu", false),
            ("aarch64-unknown-linux-gnu-macho", false),
            ("arm64-macosx", false),
            ("arm64-apple", false),
            ("x86_64-pc-windows-msvc", false),
            ("", false),
        ] {
            assert_eq!(read(triple).memset_pattern_os, has, "{triple}");
        }
    }
}
