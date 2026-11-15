#![allow(dead_code)]
// trust-cg-codegen/tests/common/x86_64_native_host.rs - host facts for x86-64 native controls
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Host facts for x86-64 native link-and-run controls.
//!
//! Two hosts execute these controls: x86-64 Linux GNU (ELF objects, triple
//! `x86_64-unknown-linux-gnu`) and x86-64 macOS (Mach-O objects, triple
//! `x86_64-apple-darwin`). Every other host keeps object-only coverage and must
//! gate native execution at COMPILE time, so no runtime SKIP can be counted as
//! a pass by a floor runner. This is the x86-64 sibling of
//! [`super::super::native_host`]'s AArch64 facts (`common/native_host.rs`).
//!
//! Gate a native row with [`NATIVE_CFG`]'s spelling:
//!
//! ```ignore
//! #[cfg(any(
//!     all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"),
//!     all(target_arch = "x86_64", target_os = "macos"),
//! ))]
//! ```
//!
//! On a native host the toolchain this module names is a REQUIREMENT, not a
//! probe: a host without `c++` fails the row rather than skipping it, exactly as
//! the AArch64 Linux EH controls treat `g++`.

/// x86-64 Linux GNU: ELF objects linked by the host `c++`.
pub const LINUX_GNU: bool = cfg!(all(
    target_arch = "x86_64",
    target_os = "linux",
    target_env = "gnu"
));
/// x86-64 macOS: Mach-O objects linked by the host `c++`/ld64 (or ld-prime).
pub const DARWIN: bool = cfg!(all(target_arch = "x86_64", target_os = "macos"));
/// Whether objects for [`TRIPLE`] can be linked and executed on this host.
pub const NATIVE: bool = LINUX_GNU || DARWIN;

/// The `#[cfg(...)]` predicate a native row must carry, spelled out for the
/// doc comment above (attributes cannot read a `const`).
pub const NATIVE_CFG: &str = "any(all(target_arch = \"x86_64\", target_os = \"linux\", \
                              target_env = \"gnu\"), all(target_arch = \"x86_64\", \
                              target_os = \"macos\"))";

/// Triple whose objects this host links. Non-native hosts keep the historical
/// Darwin object-only spelling, which every host can cross-emit.
pub const TRIPLE: &str = if LINUX_GNU {
    "x86_64-unknown-linux-gnu"
} else {
    "x86_64-apple-darwin"
};

/// Human-readable host label for evidence lines.
pub const HOST: &str = if LINUX_GNU {
    "x86_64-linux-gnu/ELF"
} else if DARWIN {
    "x86_64-darwin/Mach-O"
} else {
    "non-native"
};

/// The C++ driver that links the fixture: it pulls in the personality routine
/// and the `__cxa_*` runtime (libstdc++/libgcc_s on GNU/Linux,
/// libc++/libc++abi on macOS) that `cc` would leave undefined.
///
/// `g++` on GNU/Linux, as the AArch64 Linux EH controls use: the unqualified
/// `c++` there is an `/etc/alternatives` link a developer PATH can shadow with
/// a wrapper that is not the GNU driver at all. On macOS `c++` IS the Xcode
/// clang++ driver and `g++` is only an alias for it.
pub const CXX_COMPILER: &str = if DARWIN { "c++" } else { "g++" };

/// The GNU reader that independently reads an emitted ELF object back. Required,
/// not probed, on a Linux GNU host — as in the AArch64 Linux EH controls.
pub const READELF: &str = "readelf";

/// Extra `c++` arguments for this host. GNU ld needs an explicit
/// non-executable stack; macOS needs the x86-64 slice named explicitly so an
/// arm64-default toolchain still produces one (harmless on a native x86-64
/// host), and ld64 rejects `-z`.
pub fn cxx_link_args() -> &'static [&'static str] {
    if DARWIN {
        &["-arch", "x86_64"]
    } else {
        &["-Wl,-z,noexecstack"]
    }
}

/// The object-file symbol a C translation unit uses for `name`.
pub fn c_symbol(name: &str) -> String {
    if DARWIN {
        format!("_{name}")
    } else {
        name.to_owned()
    }
}

/// The unwind sections an EH-bearing object for [`TRIPLE`] must carry: the LSDA
/// section and the DWARF CFI section, in this host's container's spelling.
pub fn eh_section_names() -> (&'static [u8], &'static [u8]) {
    if DARWIN {
        (b"__gcc_except_tab", b"__eh_frame")
    } else {
        (b".gcc_except_table", b".eh_frame")
    }
}

const ELF_MAGIC: &[u8; 4] = b"\x7fELF";
const EM_X86_64: u16 = 62;
const MH_MAGIC_64: u32 = 0xfeed_facf;
const CPU_TYPE_X86_64: u32 = 0x0100_0007;
const MH_OBJECT: u32 = 1;

/// Assert the relocatable-object container of [`TRIPLE`]: ELF on Linux GNU,
/// Mach-O on macOS and on the object-only hosts that keep the Darwin triple.
pub fn assert_native_object(object: &[u8]) {
    if LINUX_GNU {
        assert_elf_x86_64_object(object);
    } else {
        assert_macho_x86_64_object(object);
    }
}

/// ELF64, little-endian, relocatable, EM_X86_64.
pub fn assert_elf_x86_64_object(object: &[u8]) {
    assert!(object.len() >= 64, "ELF header truncated");
    assert_eq!(&object[..4], ELF_MAGIC, "ELF magic");
    assert_eq!(&object[4..6], b"\x02\x01", "ELFCLASS64/ELFDATA2LSB");
    assert_eq!(u16_le(object, 16), 1, "ET_REL");
    assert_eq!(u16_le(object, 18), EM_X86_64, "EM_X86_64");
}

/// Mach-O 64-bit, little-endian, MH_OBJECT, CPU_TYPE_X86_64.
pub fn assert_macho_x86_64_object(object: &[u8]) {
    assert!(object.len() >= 32, "Mach-O header truncated");
    assert_eq!(u32_le(object, 0), MH_MAGIC_64, "MH_MAGIC_64");
    assert_eq!(u32_le(object, 4), CPU_TYPE_X86_64, "CPU_TYPE_X86_64");
    assert_eq!(u32_le(object, 12), MH_OBJECT, "MH_OBJECT");
}

/// Whether `object` contains `needle` as a contiguous byte run (section names
/// and symbol names both live in the object's string tables).
pub fn object_contains(object: &[u8], needle: &[u8]) -> bool {
    object.windows(needle.len()).any(|w| w == needle)
}

fn u16_le(bytes: &[u8], at: usize) -> u16 {
    u16::from_le_bytes(bytes[at..at + 2].try_into().unwrap())
}

fn u32_le(bytes: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
}
