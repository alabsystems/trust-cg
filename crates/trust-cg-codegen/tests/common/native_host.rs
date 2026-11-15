#![allow(dead_code)]
// Copyright 2026 Andrew Yates | Apache-2.0
//! Host facts for AArch64 native link-and-run controls.
//!
//! Two hosts execute these controls: AArch64 Linux GNU (ELF objects, triple
//! `aarch64-unknown-linux-gnu`) and AArch64 macOS (Mach-O objects, triple
//! `aarch64-apple-darwin`). Every other host keeps object-only coverage and
//! must gate native execution at compile time, so no runtime SKIP can be
//! counted as a pass by a floor runner.
//!
//! The Linux arm of every helper is the identity (fixtures stay byte-for-byte
//! what the Linux floor already qualified). The Darwin arm translates the
//! fixtures' GNU/ELF assembly dialect and fails closed on any construct it
//! does not understand instead of guessing.

use std::collections::BTreeSet;

/// AArch64 Linux GNU: ELF objects linked by the host `cc`.
pub const LINUX_GNU: bool = cfg!(all(
    target_arch = "aarch64",
    target_os = "linux",
    target_env = "gnu"
));
/// AArch64 macOS: Mach-O objects linked by the host `cc`/ld64.
pub const DARWIN: bool = cfg!(all(target_arch = "aarch64", target_os = "macos"));
/// Whether objects for [`TRIPLE`] can be linked and executed on this host.
pub const NATIVE: bool = LINUX_GNU || DARWIN;

/// Triple whose objects this host links. Non-native hosts keep the historical
/// Darwin object-only spelling.
pub const TRIPLE: &str = if LINUX_GNU {
    "aarch64-unknown-linux-gnu"
} else {
    "aarch64-apple-darwin"
};

/// Human-readable host label for evidence lines.
pub const HOST: &str = if LINUX_GNU {
    "aarch64-linux-gnu/ELF"
} else if DARWIN {
    "aarch64-darwin/Mach-O"
} else {
    "non-native"
};

/// Trust IR target description for [`TRIPLE`] under the native C ABI.
pub fn target_info() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: TRIPLE.into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}

/// C compiler driver for fixtures that name one explicitly: the Xcode clang
/// on macOS, the PATH `cc` (GCC on the Linux floor host) on Linux.
pub const C_COMPILER: &str = if DARWIN { "/usr/bin/clang" } else { "cc" };

/// Extra link arguments hardening the fixture executable. GNU ld needs an
/// explicit non-executable stack; ld64 never grants an executable stack and
/// rejects `-z`.
pub fn link_hardening_args() -> &'static [&'static str] {
    if DARWIN { &[] } else { &["-Wl,-z,noexecstack"] }
}

/// C libraries a fixture driver needs after its inputs. glibc keeps libm
/// separate, and GNU ld's `--as-needed` keeps it only when it follows the
/// objects that use it; macOS libSystem already provides it.
pub fn c_math_library_args() -> &'static [&'static str] {
    if DARWIN { &[] } else { &["-lm"] }
}

/// The object-file symbol a C translation unit uses for `name`.
pub fn c_symbol(name: &str) -> String {
    if DARWIN {
        format!("_{name}")
    } else {
        name.to_owned()
    }
}

/// Relocatable object holding one fully resolved, fixup-free function body
/// for [`TRIPLE`]: ELF `.text` with an STT_FUNC symbol on Linux GNU, otherwise
/// Mach-O `__text` with the C `_` symbol prefix (the historical container).
pub fn naked_function_object(name: &str, code: &[u8]) -> Vec<u8> {
    naked_function_object_for(TRIPLE, name, code)
}

/// [`naked_function_object`] for an explicit native `triple`, so both
/// containers are checked on every host. Any other triple panics.
pub fn naked_function_object_for(triple: &str, name: &str, code: &[u8]) -> Vec<u8> {
    match triple {
        "aarch64-unknown-linux-gnu" => {
            let mut writer =
                trust_cg_codegen::elf::ElfWriter::new(trust_cg_codegen::elf::ElfMachine::AArch64);
            let text = writer.add_text_section(code);
            // STT_FUNC = 2; ELF symbols carry no leading underscore.
            writer.add_symbol(name, text, 0, code.len() as u64, true, 2);
            writer.write_checked().unwrap()
        }
        "aarch64-apple-darwin" => {
            let mut writer = trust_cg_codegen::macho::MachOWriter::new();
            writer.add_text_section(code);
            writer.add_symbol(&format!("_{name}"), 1, 0, true).unwrap();
            writer.write().unwrap()
        }
        other => panic!("no naked-function container for {other:?}"),
    }
}

/// The host `cc` spelling that links a non-PIE executable.
pub fn no_pie_link_flag() -> &'static str {
    if DARWIN { "-Wl,-no_pie" } else { "-no-pie" }
}

/// Compile every function of `module` for [`TRIPLE`] through the public
/// pipeline with an explicitly admitted AArch64 ISA `profile`, into one object
/// that also carries the module's globals.
///
/// This is explicit-profile pipeline evidence for optional FEAT_* families
/// (LSE, FP16, DotProd) that the generic Linux AOT profile refuses by design;
/// it is not generic Linux AOT admission. Callers first require
/// `profile.is_supported_by_host()`: a host without the feature is a failure,
/// never a skip.
pub fn compile_with_isa_profile(
    module: &trust_ir::Module,
    opt_level: trust_cg_codegen::pipeline::OptLevel,
    profile: trust_cg_codegen::target::AArch64IsaProfile,
) -> Result<Vec<u8>, String> {
    let object = compile_with_isa_profile_for(TRIPLE, module, opt_level, profile)?;
    assert_native_object(&object);
    Ok(object)
}

/// [`compile_with_isa_profile`] for an explicit `triple`, so object-level
/// controls can check the Linux GNU lane's object on every host.
pub fn compile_with_isa_profile_for(
    triple: &str,
    module: &trust_ir::Module,
    opt_level: trust_cg_codegen::pipeline::OptLevel,
    profile: trust_cg_codegen::target::AArch64IsaProfile,
) -> Result<Vec<u8>, String> {
    use trust_cg_codegen::pipeline::{Pipeline, PipelineConfig};
    let lowered = permit_translate_module(module).map_err(|error| error.to_string())?;
    let globals = trust_cg_codegen::compiler::module_object_globals(module)
        .map_err(|error| error.to_string())?;
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level,
        target_triple: triple.into(),
        ..PipelineConfig::default()
    })
    .with_aarch64_isa_profile(profile);
    let prepared = lowered
        .iter()
        .map(|(function, _)| {
            pipeline
                .prepare_function(function)
                .map_err(|error| format!("{}: {error}", function.name))
        })
        .collect::<Result<Vec<_>, _>>()?;
    pipeline
        .compile_module_with_globals(&prepared, &globals)
        .map_err(|error| error.to_string())
}

const ELF_MAGIC: &[u8; 4] = b"\x7fELF";
const EM_AARCH64: u16 = 183;
const MH_MAGIC_64: u32 = 0xfeed_facf;
const CPU_TYPE_ARM64: u32 = 0x0100_000c;
const MH_OBJECT: u32 = 1;
const LC_SEGMENT_64: u32 = 0x19;

/// Assert the relocatable-object container of [`TRIPLE`]: ELF on Linux GNU,
/// Mach-O on macOS and on the object-only hosts that keep the Darwin triple.
pub fn assert_native_object(object: &[u8]) {
    if LINUX_GNU {
        assert_elf_aarch64_object(object);
    } else {
        assert_macho_arm64_object(object);
    }
}

/// ELF64, little-endian, relocatable, EM_AARCH64.
pub fn assert_elf_aarch64_object(object: &[u8]) {
    assert!(object.len() >= 64, "ELF header truncated");
    assert_eq!(&object[..4], ELF_MAGIC, "ELF magic");
    assert_eq!(&object[4..6], b"\x02\x01", "ELFCLASS64/ELFDATA2LSB");
    assert_eq!(u16_le(object, 16), 1, "ET_REL");
    assert_eq!(u16_le(object, 18), EM_AARCH64, "EM_AARCH64");
}

/// Mach-O 64-bit, little-endian, MH_OBJECT, CPU_TYPE_ARM64.
pub fn assert_macho_arm64_object(object: &[u8]) {
    assert!(object.len() >= 32, "Mach-O header truncated");
    assert_eq!(u32_le(object, 0), MH_MAGIC_64, "MH_MAGIC_64");
    assert_eq!(u32_le(object, 4), CPU_TYPE_ARM64, "CPU_TYPE_ARM64");
    assert_eq!(u32_le(object, 12), MH_OBJECT, "MH_OBJECT");
}

fn u16_le(bytes: &[u8], at: usize) -> u16 {
    u16::from_le_bytes(bytes[at..at + 2].try_into().unwrap())
}

fn u32_le(bytes: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
}

fn u64_le(bytes: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap())
}

/// Instruction words of the object's code section, read by this parser rather
/// than the compiler's emitter/decoder: ELF `.text` or Mach-O
/// `__TEXT,__text`, chosen by the container magic.
pub fn text_words(object: &[u8]) -> Vec<u32> {
    let text = if object.starts_with(ELF_MAGIC) {
        elf_text(object)
    } else {
        macho_text(object)
    };
    assert_eq!(text.len() % 4, 0, "code section is not word sized");
    text.as_chunks::<4>()
        .0
        .iter()
        .map(|word| u32::from_le_bytes(*word))
        .collect()
}

fn elf_text(object: &[u8]) -> &[u8] {
    assert_elf_aarch64_object(object);
    let at16 = |p| usize::from(u16_le(object, p));
    let at32 = |p| u32_le(object, p) as usize;
    let at64 = |p| usize::try_from(u64_le(object, p)).unwrap();
    let table = at64(40);
    let entry_size = at16(58);
    let strings = table + at16(62) * entry_size;
    let names = &object[at64(strings + 24)..][..at64(strings + 32)];
    let mut found = None;
    for index in 0..at16(60) {
        let entry = table + index * entry_size;
        let name = &names[at32(entry)..];
        let end = name.iter().position(|b| *b == 0).unwrap();
        if &name[..end] == b".text" {
            assert!(found.is_none(), "duplicate ELF .text");
            found = Some(&object[at64(entry + 24)..][..at64(entry + 32)]);
        }
    }
    found.expect("ELF .text missing")
}

fn macho_text(object: &[u8]) -> &[u8] {
    assert_macho_arm64_object(object);
    let commands = u32_le(object, 16) as usize;
    let mut cursor = 32;
    let mut found = None;
    for _ in 0..commands {
        let command = u32_le(object, cursor);
        let size = u32_le(object, cursor + 4) as usize;
        assert!(size >= 8, "malformed Mach-O load command");
        if command == LC_SEGMENT_64 {
            let sections = u32_le(object, cursor + 64) as usize;
            for index in 0..sections {
                let section = cursor + 72 + index * 80;
                let name = fixed_name(&object[section..section + 16]);
                let segment = fixed_name(&object[section + 16..section + 32]);
                if (segment, name) == ("__TEXT", "__text") {
                    assert!(found.is_none(), "duplicate Mach-O __TEXT,__text");
                    let size = usize::try_from(u64_le(object, section + 40)).unwrap();
                    let offset = u32_le(object, section + 48) as usize;
                    found = Some(&object[offset..offset + size]);
                }
            }
        }
        cursor += size;
    }
    found.expect("Mach-O __TEXT,__text missing")
}

fn fixed_name(bytes: &[u8]) -> &str {
    let end = bytes.iter().position(|b| *b == 0).unwrap_or(bytes.len());
    std::str::from_utf8(&bytes[..end]).unwrap()
}

/// Host assembly for a fixture written in the GNU/ELF AArch64 dialect.
///
/// Linux returns the source unchanged. Darwin maps it to Apple's dialect:
/// globals and every reference to them gain the C `_` prefix, `.type`,
/// `.size` and `.note.GNU-stack` directives are dropped (Mach-O has none),
/// and GNU `;` statement separators become newlines (Apple treats `;` as a
/// comment, which would silently delete instructions). Unknown sections,
/// ELF relocation operators and globals spelled like registers panic.
pub fn assembly(gnu_elf: &str) -> String {
    if DARWIN {
        darwin_assembly(gnu_elf)
    } else {
        gnu_elf.to_owned()
    }
}

fn is_identifier_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'.' | b'$')
}

fn looks_like_register(name: &str) -> bool {
    let bytes = name.as_bytes();
    matches!(
        name,
        "sp" | "wsp" | "xzr" | "wzr" | "lr" | "fp" | "nzcv" | "fpcr" | "fpsr"
    ) || (bytes.len() >= 2
        && matches!(
            bytes[0],
            b'x' | b'w' | b'b' | b'h' | b's' | b'd' | b'q' | b'v'
        )
        && bytes[1..].iter().all(u8::is_ascii_digit))
}

/// Split into `(code, comment)` statements: GNU `;` separators start a new
/// statement, and a `//` comment stays attached, untranslated, to the last one.
fn statements(gnu_elf: &str) -> Vec<(String, Option<String>)> {
    let mut out = Vec::new();
    for line in gnu_elf.lines() {
        let (code, comment) = match line.find("//") {
            Some(at) => (&line[..at], Some(line[at..].to_owned())),
            None => (line, None),
        };
        if code.contains(';') {
            assert!(
                !code.contains('"'),
                "Darwin assembly: `;` inside a quoted operand is ambiguous: {line:?}"
            );
        }
        let parts: Vec<_> = code.split(';').map(str::trim).collect();
        let last = parts.len() - 1;
        for (index, part) in parts.into_iter().enumerate() {
            let comment = if index == last { comment.clone() } else { None };
            out.push((part.to_owned(), comment));
        }
    }
    out
}

/// The Darwin arm of [`assembly`], callable on any host so the translation
/// itself is tested everywhere.
pub fn darwin_assembly(gnu_elf: &str) -> String {
    let statements = statements(gnu_elf);
    let mut globals = BTreeSet::new();
    for (statement, _) in &statements {
        for directive in [".global", ".globl"] {
            if let Some(rest) = statement.strip_prefix(directive)
                && rest.starts_with(char::is_whitespace)
            {
                for name in rest.split(',').map(str::trim) {
                    assert!(
                        !name.is_empty() && name.bytes().all(is_identifier_byte),
                        "Darwin assembly: malformed global {statement:?}"
                    );
                    assert!(
                        !looks_like_register(name),
                        "Darwin assembly: global {name:?} is spelled like a register"
                    );
                    globals.insert(name.to_owned());
                }
            }
        }
    }
    let mut out = String::with_capacity(gnu_elf.len() + globals.len() * 4);
    for (statement, comment) in statements {
        if statement.is_empty() {
            if let Some(comment) = comment {
                out.push_str(&comment);
            }
            out.push('\n');
            continue;
        }
        if statement.starts_with(".type ")
            || statement.starts_with(".size ")
            || statement.starts_with(".section .note.GNU-stack")
        {
            continue;
        }
        for forbidden in [
            ":lo12:",
            ":got",
            ":tprel",
            ":tlsdesc",
            "%function",
            "@function",
        ] {
            assert!(
                !statement.contains(forbidden),
                "Darwin assembly: ELF-only operator {forbidden:?} in {statement:?}"
            );
        }
        let statement = if let Some(section) = statement.strip_prefix(".section") {
            match section.trim().split(',').next().unwrap().trim() {
                ".rodata" => ".section __TEXT,__const".to_owned(),
                ".data" => ".data".to_owned(),
                ".bss" => ".bss".to_owned(),
                other => panic!("Darwin assembly: no mapping for ELF section {other:?}"),
            }
        } else if let Some(rest) = statement.strip_prefix(".global") {
            format!(".globl{rest}")
        } else {
            statement
        };
        out.push_str(&prefix_globals(&statement, &globals));
        if let Some(comment) = comment {
            out.push(' ');
            out.push_str(&comment);
        }
        out.push('\n');
    }
    out
}

fn prefix_globals(statement: &str, globals: &BTreeSet<String>) -> String {
    let bytes = statement.as_bytes();
    let mut out = String::with_capacity(statement.len() + 8);
    let mut index = 0;
    while index < bytes.len() {
        if is_identifier_byte(bytes[index]) {
            let start = index;
            while index < bytes.len() && is_identifier_byte(bytes[index]) {
                index += 1;
            }
            let token = &statement[start..index];
            // `#imm` and `0x...` operands never name a global.
            let immediate = start > 0 && bytes[start - 1] == b'#';
            if !immediate && globals.contains(token) {
                out.push('_');
            }
            out.push_str(token);
        } else {
            out.push(bytes[index] as char);
            index += 1;
        }
    }
    out
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

/// `translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &trust_ir::Module,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}
