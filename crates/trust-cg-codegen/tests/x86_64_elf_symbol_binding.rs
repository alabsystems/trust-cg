// trust-cg-codegen/tests/x86_64_elf_symbol_binding.rs
//
// x86-64 ELF binding of module-local (Internal/Private) functions, and
// hidden/protected visibility on a function definition.
//
// Object level (every host): `Compiler::compile` admits direct calls to and
// the address of an Internal or Private function for
// `x86_64-unknown-linux-gnu` (O0-O3), and in each object the helper is one
// `STB_LOCAL` `STT_FUNC` symbol in an executable section while every
// relocation that reaches it names that symbol — the `R_X86_64_PLT32` call
// and the `R_X86_64_64` data slot holding its address. A hidden or protected
// `External` definition carries `STV_HIDDEN`/`STV_PROTECTED` in `st_other`
// and stays `STB_GLOBAL`. Symbols and relocations are read back by the
// independent ELF64 reader below, never by the emitter's writer model.
// The x86-64 COFF object path keeps refusing module-local references
// by name (`AotDirectModuleFunctionBindingUnsupported`): it binds only an
// unreferenced module-local definition local and read no reference back.
//
// Native (x86-64 Linux GNU host only, O0-O3): two modules that each define
// their own Internal `helper` returning a different value, linked into one
// executable with a C driver, each reach their own helper; a gcc twin with
// `static` helpers agrees. Linked into a shared object, neither `helper`
// reaches `.dynsym`, while the near-twin with an External helper does — so
// the binding is load-bearing and not an artefact of the link. Execution
// evidence for this host's GNU ld and glibc loader, not a linker or loader
// proof.
//
// Ruling OD-X86-ELF-LOCAL-BINDING-20261027 (binding) and
// OD-X86-ELF-DEFINITION-VISIBILITY-20261027 (visibility) own the boundary
// this row measures.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#[cfg(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
mod common;
#[cfg(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::{Linkage, Visibility};

const LINUX: &str = "x86_64-unknown-linux-gnu";
const WINDOWS: &str = "x86_64-pc-windows-msvc";
const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

// =============================================================================
// Independent ELF64 relocatable-object reader
// =============================================================================

const ET_REL: u16 = 1;
const EM_X86_64: u16 = 62;
const SHT_SYMTAB: u32 = 2;
const SHT_RELA: u32 = 4;
const SHF_EXECINSTR: u64 = 0x4;
const STB_LOCAL: u8 = 0;
const STB_GLOBAL: u8 = 1;
const STT_FUNC: u8 = 2;
const STV_DEFAULT: u8 = 0;
const STV_HIDDEN: u8 = 2;
const STV_PROTECTED: u8 = 3;
const R_X86_64_64: u32 = 1;
const R_X86_64_PLT32: u32 = 4;

fn rd_u16(bytes: &[u8], at: usize) -> u16 {
    u16::from_le_bytes(bytes[at..at + 2].try_into().unwrap())
}

fn rd_u32(bytes: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
}

fn rd_u64(bytes: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap())
}

#[derive(Debug, Clone)]
struct ElfSection {
    name: String,
    sh_type: u32,
    sh_flags: u64,
    offset: usize,
    size: usize,
    link: u32,
    info: u32,
    entsize: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ElfSymbol {
    name: String,
    binding: u8,
    symbol_type: u8,
    visibility: u8,
    section_index: u16,
    value: u64,
    size: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ElfReloc {
    /// Name of the section the record patches.
    section: String,
    offset: u64,
    reloc_type: u32,
    /// The named symbol's index, and its name.
    symbol_index: u32,
    symbol: String,
    addend: i64,
}

#[derive(Debug)]
struct Elf {
    sections: Vec<ElfSection>,
    symbols: Vec<ElfSymbol>,
    relocs: Vec<ElfReloc>,
    /// `sh_info` of `.symtab`: one past the last local symbol.
    first_global_symbol: u32,
}

impl Elf {
    /// The symbols spelled `name`.
    fn named(&self, name: &str) -> Vec<&ElfSymbol> {
        self.symbols
            .iter()
            .filter(|symbol| symbol.name == name)
            .collect()
    }

    /// The one symbol spelled `name`, or a panic naming every symbol.
    fn one(&self, name: &str) -> &ElfSymbol {
        let found = self.named(name);
        assert_eq!(
            found.len(),
            1,
            "expected exactly one symbol `{name}`, found {found:?} in {:?}",
            self.symbols
        );
        found[0]
    }

    /// Whether section `index` is executable.
    fn executable(&self, index: u16) -> bool {
        usize::from(index)
            .checked_sub(0)
            .and_then(|index| self.sections.get(index))
            .is_some_and(|section| section.sh_flags & SHF_EXECINSTR != 0)
    }

    /// Every relocation naming `name`.
    fn reaching(&self, name: &str) -> Vec<&ElfReloc> {
        self.relocs
            .iter()
            .filter(|reloc| reloc.symbol == name)
            .collect()
    }
}

/// Parse an `ET_REL` x86-64 ELF64 object's sections, `.symtab` and every
/// `SHT_RELA` record. A separate implementation from the crate's own reader:
/// this row's evidence must not come from the code it measures.
fn parse_elf(bytes: &[u8]) -> Elf {
    assert_eq!(&bytes[..4], b"\x7fELF", "not an ELF object");
    assert_eq!(bytes[4], 2, "not ELF64");
    assert_eq!(rd_u16(bytes, 16), ET_REL, "not a relocatable object");
    assert_eq!(rd_u16(bytes, 18), EM_X86_64, "not x86-64");
    let shoff = rd_u64(bytes, 40) as usize;
    let shentsize = usize::from(rd_u16(bytes, 58));
    let shnum = usize::from(rd_u16(bytes, 60));
    let shstrndx = usize::from(rd_u16(bytes, 62));
    let header = |index: usize| shoff + index * shentsize;
    let shstr = rd_u64(bytes, header(shstrndx) + 24) as usize;
    let string_at = |table: usize, offset: usize| {
        let start = table + offset;
        let end = bytes[start..]
            .iter()
            .position(|&byte| byte == 0)
            .map_or(bytes.len(), |len| start + len);
        String::from_utf8_lossy(&bytes[start..end]).into_owned()
    };
    let sections: Vec<ElfSection> = (0..shnum)
        .map(|index| {
            let at = header(index);
            ElfSection {
                name: string_at(shstr, rd_u32(bytes, at) as usize),
                sh_type: rd_u32(bytes, at + 4),
                sh_flags: rd_u64(bytes, at + 8),
                offset: rd_u64(bytes, at + 24) as usize,
                size: rd_u64(bytes, at + 32) as usize,
                link: rd_u32(bytes, at + 40),
                info: rd_u32(bytes, at + 44),
                entsize: rd_u64(bytes, at + 56) as usize,
            }
        })
        .collect();
    let symtab = sections
        .iter()
        .find(|section| section.sh_type == SHT_SYMTAB)
        .expect(".symtab present");
    let strtab = sections[symtab.link as usize].offset;
    let entsize = if symtab.entsize == 0 {
        24
    } else {
        symtab.entsize
    };
    let symbols: Vec<ElfSymbol> = (0..symtab.size / entsize)
        .map(|index| {
            let at = symtab.offset + index * entsize;
            let info = bytes[at + 4];
            ElfSymbol {
                name: string_at(strtab, rd_u32(bytes, at) as usize),
                binding: info >> 4,
                symbol_type: info & 0xf,
                visibility: bytes[at + 5] & 0x3,
                section_index: rd_u16(bytes, at + 6),
                value: rd_u64(bytes, at + 8),
                size: rd_u64(bytes, at + 16),
            }
        })
        .collect();
    let mut relocs = Vec::new();
    for section in sections.iter().filter(|s| s.sh_type == SHT_RELA) {
        let patched = sections[section.info as usize].name.clone();
        let entsize = if section.entsize == 0 {
            24
        } else {
            section.entsize
        };
        for index in 0..section.size / entsize {
            let at = section.offset + index * entsize;
            let info = rd_u64(bytes, at + 8);
            let symbol_index = (info >> 32) as u32;
            relocs.push(ElfReloc {
                section: patched.clone(),
                offset: rd_u64(bytes, at),
                reloc_type: (info & 0xffff_ffff) as u32,
                symbol_index,
                symbol: symbols
                    .get(symbol_index as usize)
                    .map(|symbol| symbol.name.clone())
                    .unwrap_or_default(),
                addend: rd_u64(bytes, at + 16) as i64,
            });
        }
    }
    Elf {
        first_global_symbol: symtab.info,
        sections,
        symbols,
        relocs,
    }
}

// =============================================================================
// The module
// =============================================================================

/// A module whose bodied `helper` (linkage `helper_linkage`, visibility
/// `helper_visibility`) returns `x + offset` and counts its calls in the
/// Internal global `<tag>_count` — the store keeps it out of the module
/// inliner, so its direct call stays a call. Its External entry points:
///
/// * `<tag>_direct(x)`: a direct `Call`;
/// * `<tag>_via_global(x)`: a `CallIndirect` through the pointer loaded from
///   `<tag>_slot`, a global of linkage `slot_linkage` initialized with
///   `SymbolAddr(helper)` (the data slot that must hold the local
///   definition's address);
/// * `<tag>_calls()`: the call count.
///
/// `slot_linkage` is `External` wherever the object is linked into an
/// executable, which is what makes the slot's label a non-local symbol and so
/// exercises the post-emission check's data-slot rule. A `cc -shared` link
/// needs `Internal` instead: the x86-64 backend implements only the `static`
/// relocation model (`CompilerConfig::relocation_model`, AArch64 ELF alone
/// implements `pie`/`pic`), so a body's PC-relative reference to a
/// PREEMPTIBLE global is a `R_X86_64_PC32` that GNU ld refuses in a shared
/// object ("recompile with -fPIC"). That boundary is this backend's, not this
/// row's subject.
#[path = "common/module_local_binding_fixture.rs"]
mod module_local_binding_fixture;
use module_local_binding_fixture::local_binding_module;

/// This file's modules are hand-built and carry no codegen license, which
/// trust-cg refuses by default: every compile here permits an unlicensed body
/// explicitly, so none of them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

fn compiler(triple: &str, opt_level: OptLevel) -> Compiler {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..Default::default()
        },
        TargetSpec::parse(triple).expect("triple"),
    )
    .with_codegen_license(permit_unlicensed())
}

// =============================================================================
// Object level
// =============================================================================

/// The x86-64 ELF object binds a module-local helper `STB_LOCAL` and every
/// reference to it — the `PLT32` call and the `R_X86_64_64` data slot — names
/// that one local definition. Before ruling OD-X86-ELF-LOCAL-BINDING-20261027
/// the census refused this module outright, because the emitter would have
/// made the helper a default-visible global.
#[test]
fn x86_64_elf_binds_a_module_local_helper_and_every_reference_to_it() {
    for linkage in [Linkage::Internal, Linkage::Private] {
        for opt_level in OPT_LEVELS {
            let module =
                local_binding_module("a", linkage, Visibility::Default, Linkage::External, 7);
            let object = compiler(LINUX, opt_level)
                .compile(&module)
                .unwrap_or_else(|error| {
                    panic!("{linkage:?} at {opt_level:?} must compile for {LINUX}: {error:?}")
                })
                .object_code;
            let elf = parse_elf(&object);
            let label = format!("{linkage:?}/{opt_level:?}");

            // One defined local function symbol, in an executable section.
            let helper = elf.one("helper");
            assert_eq!(
                (helper.binding, helper.symbol_type, helper.visibility),
                (STB_LOCAL, STT_FUNC, STV_DEFAULT),
                "{label}: the helper must be a defined STB_LOCAL STT_FUNC symbol: {helper:?}"
            );
            assert!(
                helper.section_index != 0 && elf.executable(helper.section_index),
                "{label}: the helper must be defined in an executable section: {helper:?}"
            );
            // It is in the local partition, which `sh_info` bounds.
            let index = elf
                .symbols
                .iter()
                .position(|symbol| symbol.name == "helper")
                .expect("the helper is in .symtab") as u32;
            assert!(
                index < elf.first_global_symbol,
                "{label}: symbol #{index} `helper` must precede sh_info {}",
                elf.first_global_symbol
            );
            // An exported entry point stays global.
            let direct = elf.one("a_direct");
            assert_eq!(
                (direct.binding, direct.symbol_type, direct.visibility),
                (STB_GLOBAL, STT_FUNC, STV_DEFAULT),
                "{label}: an External definition stays a default-visible global: {direct:?}"
            );
            // Every relocation that reaches the helper names THAT symbol: the
            // direct call from .text and the data slot holding its address.
            let reaching = elf.reaching("helper");
            assert!(
                !reaching.is_empty(),
                "{label}: no relocation names the helper: {:?}",
                elf.relocs
            );
            for reloc in &reaching {
                assert_eq!(
                    elf.symbols[reloc.symbol_index as usize].binding, STB_LOCAL,
                    "{label}: {reloc:?} reaches the helper through a non-local symbol"
                );
            }
            // The direct call is an `R_X86_64_PLT32` in an executable
            // section; the slot is an `R_X86_64_64` in a data section holding
            // the definition's own address (addend 0).
            let call = reaching
                .iter()
                .find(|reloc| reloc.reloc_type == R_X86_64_PLT32)
                .unwrap_or_else(|| {
                    panic!("{label}: no R_X86_64_PLT32 names the helper: {reaching:?}")
                });
            assert_eq!(
                call.section, ".text",
                "{label}: the direct call must patch .text: {call:?}"
            );
            let slot = reaching
                .iter()
                .find(|reloc| reloc.reloc_type == R_X86_64_64)
                .unwrap_or_else(|| {
                    panic!("{label}: no R_X86_64_64 names the helper: {reaching:?}")
                });
            assert!(
                slot.section.starts_with(".data"),
                "{label}: the address slot must be in a data section: {slot:?}"
            );
            assert_eq!(
                slot.addend, 0,
                "{label}: the slot holds the definition's own address: {slot:?}"
            );
            // No non-local symbol aliases the helper's bytes.
            let (start, end) = (helper.value, helper.value + helper.size.max(1));
            for alias in &elf.symbols {
                if alias.binding == STB_LOCAL || alias.section_index != helper.section_index {
                    continue;
                }
                let (from, to) = (alias.value, alias.value + alias.size.max(1));
                assert!(
                    to <= start || end <= from,
                    "{label}: non-local symbol {alias:?} overlaps the local helper {helper:?}"
                );
            }
        }
    }
}

/// The x86-64 COFF path binds an unreferenced module-local definition
/// static, but still refuses references to one by name rather than risk
/// binding the reference elsewhere. ELF and Mach-O have their own qualified
/// module-local reference paths.
#[test]
fn x86_64_coff_still_refuses_module_local_references() {
    let triple = WINDOWS;
    let module = local_binding_module(
        "a",
        Linkage::Internal,
        Visibility::Default,
        Linkage::External,
        7,
    );
    let error = compiler(triple, OptLevel::O0)
        .compile(&module)
        .expect_err("the COFF path still refuses module-local references");
    let text = format!("{error:?}");
    assert!(
        text.contains("AotDirectModuleFunctionBindingUnsupported")
            || text.contains("AotStaticFunctionIdentityBindingUnsupported"),
        "{triple}: expected a module-local binding refusal, got {text}"
    );
}

/// A hidden or protected `External` definition carries its `STV_*` in
/// `st_other` and stays `STB_GLOBAL` on x86-64 ELF (ruling
/// OD-X86-ELF-DEFINITION-VISIBILITY-20261027); the Mach-O path spells hidden
/// as a private extern and refuses protected, and both were refused before
/// the ruling.
#[test]
fn x86_64_elf_carries_hidden_and_protected_function_definitions() {
    for (visibility, expected) in [
        (Visibility::Hidden, STV_HIDDEN),
        (Visibility::Protected, STV_PROTECTED),
    ] {
        for opt_level in OPT_LEVELS {
            let module =
                local_binding_module("a", Linkage::External, visibility, Linkage::External, 7);
            let object = compiler(LINUX, opt_level)
                .compile(&module)
                .unwrap_or_else(|error| {
                    panic!("{visibility} at {opt_level:?} must compile for {LINUX}: {error:?}")
                })
                .object_code;
            let elf = parse_elf(&object);
            let helper = elf.one("helper");
            assert_eq!(
                (helper.binding, helper.symbol_type, helper.visibility),
                (STB_GLOBAL, STT_FUNC, expected),
                "{visibility} at {opt_level:?}: the definition must keep STB_GLOBAL and carry \
                 its STV_*: {helper:?}"
            );
            assert_eq!(
                elf.one("a_direct").visibility,
                STV_DEFAULT,
                "{visibility} at {opt_level:?}: an unstated definition stays default-visible"
            );
        }
    }
}

/// The declaration facet admitted by the bridge route must survive emission:
/// undefined hidden/protected helpers retain visibility, direct-call relocation
/// and the data-slot address, independently read back from actual ELF bytes.
#[test]
fn x86_64_elf_carries_hidden_and_protected_function_declarations() {
    #[path = "common/pinned_target.rs"]
    mod pinned_target;
    for (visibility, expected) in [
        (Visibility::Hidden, STV_HIDDEN),
        (Visibility::Protected, STV_PROTECTED),
    ] {
        for opt_level in OPT_LEVELS {
            let mut module =
                local_binding_module("a", Linkage::External, visibility, Linkage::External, 7);
            module
                .functions
                .iter_mut()
                .find(|f| f.name == "helper")
                .unwrap()
                .blocks
                .clear();
            let module = pinned_target::pinned(&module, LINUX);
            let object = compiler(LINUX, opt_level)
                .compile(&module)
                .unwrap()
                .object_code;
            let elf = parse_elf(&object);
            let helper = elf.one("helper");
            assert_eq!(
                (
                    helper.binding,
                    helper.symbol_type,
                    helper.visibility,
                    helper.section_index
                ),
                (STB_GLOBAL, 0, expected, 0),
                "{visibility} {opt_level:?}: undefined function visibility must reach ELF"
            );
            for reloc_type in [R_X86_64_PLT32, R_X86_64_64] {
                assert!(
                    elf.relocs
                        .iter()
                        .any(|r| r.symbol == "helper" && r.reloc_type == reloc_type),
                    "{visibility} {opt_level:?}: missing helper relocation {reloc_type}"
                );
            }
        }
    }
}

// =============================================================================
// Native: x86-64 Linux GNU only
// =============================================================================
//
// Gated at COMPILE time, not with a runtime skip: a `SKIP:` line is read by
// `scripts/soundness_check.sh` as a failure, which is right for a row that is
// nothing but the native run.

/// The C driver: it defines its OWN global `helper`, so a module whose call
/// bound globally would reach `x + 1000` instead of its own body. Each
/// module's entry points must print its own offset.
#[cfg(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
const DRIVER_C: &str = r#"
#include <stdio.h>
unsigned long a_direct(unsigned long);
unsigned long b_direct(unsigned long);
unsigned long a_via_global(unsigned long);
unsigned long b_via_global(unsigned long);
unsigned long a_calls(void);
unsigned long b_calls(void);
/* A global `helper` every module-local call must NOT reach. */
unsigned long helper(unsigned long x) { return x + 1000; }
int main(void) {
    printf("direct %lu %lu\n", a_direct(1), b_direct(1));
    printf("slot %lu %lu\n", a_via_global(1), b_via_global(1));
    printf("calls %lu %lu\n", a_calls(), b_calls());
    return 0;
}
"#;

/// The gcc twin: the same shape with `static` helpers, which is what rustc's
/// LLVM backend and gcc both bind locally. Its output must equal the
/// trust-cg one, so the expected text is not a number this row invented.
#[cfg(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
const TWIN_C: &str = r#"
static unsigned long a_count = 0;
static unsigned long b_count = 0;
static unsigned long helper(unsigned long x) { a_count = a_count + 1; return x + 7; }
static unsigned long b_helper(unsigned long x) { b_count = b_count + 1; return x + 100; }
unsigned long (*a_slot)(unsigned long) = helper;
unsigned long (*b_slot)(unsigned long) = b_helper;
unsigned long a_direct(unsigned long x) { return helper(x); }
unsigned long b_direct(unsigned long x) { return b_helper(x); }
unsigned long a_via_global(unsigned long x) { return a_slot(x); }
unsigned long b_via_global(unsigned long x) { return b_slot(x); }
unsigned long a_calls(void) { return a_count; }
unsigned long b_calls(void) { return b_count; }
"#;

/// What both the trust-cg link and the gcc twin must print: each module's own
/// helper (offsets 7 and 100), never the driver's global one (1000), and two
/// call counts of 2 each (the direct call and the slot call).
#[cfg(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
const EXPECTED: &str = "direct 8 101\nslot 8 101\ncalls 2 2\n";

#[cfg(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
fn cc(args: &[&str]) -> (bool, String) {
    use common::rosetta::{codegen_link_timeout, command_output_with_timeout};
    let mut command = std::process::Command::new("cc");
    for argument in args {
        command.arg(argument);
    }
    let output = command_output_with_timeout(&mut command, codegen_link_timeout())
        .expect("the host cc must spawn");
    let stderr = String::from_utf8_lossy(&output.output.stderr).to_string();
    (!output.timed_out && output.output.status.success(), stderr)
}

/// Two modules that each define their own Internal `helper` link into one
/// executable with a C object defining a GLOBAL `helper`, and each reaches
/// its own body through the direct call and through the data slot. The gcc
/// twin with `static` helpers prints the same.
///
/// Execution evidence for this host's `cc`, GNU ld and glibc loader; not a
/// linker or loader proof.
#[cfg(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
#[test]
fn native_two_modules_each_reach_their_own_module_local_helper() {
    use common::rosetta::{codegen_run_timeout, run_executable_with_timeout};

    for opt_level in OPT_LEVELS {
        let scratch = fresh_dir::create("x86_64-elf-local-binding");
        let dir = scratch.path();
        let mut objects = Vec::new();
        for (tag, offset) in [("a", 7), ("b", 100)] {
            let module = local_binding_module(
                tag,
                Linkage::Internal,
                Visibility::Default,
                Linkage::External,
                offset,
            );
            let object = compiler(LINUX, opt_level)
                .compile(&module)
                .unwrap_or_else(|error| panic!("{tag} at {opt_level:?} must compile: {error:?}"))
                .object_code;
            let path = dir.join(format!("{tag}.o"));
            std::fs::write(&path, &object).expect("write the object");
            objects.push(path);
        }
        let driver = dir.join("driver.c");
        let binary = dir.join("prog");
        std::fs::write(&driver, DRIVER_C).expect("write driver.c");
        let mut args = vec![
            "-O2".to_string(),
            "-o".to_string(),
            binary.to_str().unwrap().to_string(),
            driver.to_str().unwrap().to_string(),
        ];
        args.extend(
            objects
                .iter()
                .map(|path| path.to_str().unwrap().to_string()),
        );
        let borrowed: Vec<&str> = args.iter().map(String::as_str).collect();
        let (linked, stderr) = cc(&borrowed);
        assert!(linked, "{opt_level:?}: the link must succeed:\n{stderr}");
        let run = run_executable_with_timeout(&binary, codegen_run_timeout())
            .expect("run the linked program");
        assert!(!run.timed_out, "{opt_level:?}: the program timed out");
        let stdout = String::from_utf8_lossy(&run.output.stdout).to_string();
        assert!(
            run.output.status.success(),
            "{opt_level:?}: the program failed {}:\n{stdout}",
            run.output.status
        );
        assert_eq!(
            stdout, EXPECTED,
            "{opt_level:?}: each module must reach its OWN helper, never the driver's global one"
        );

        // The gcc twin: the same shape with `static` helpers.
        let twin = dir.join("twin.c");
        let twin_binary = dir.join("twin");
        std::fs::write(&twin, TWIN_C).expect("write twin.c");
        let (twin_linked, twin_stderr) = cc(&[
            "-O2",
            "-o",
            twin_binary.to_str().unwrap(),
            driver.to_str().unwrap(),
            twin.to_str().unwrap(),
        ]);
        assert!(
            twin_linked,
            "{opt_level:?}: the gcc twin must link:\n{twin_stderr}"
        );
        let twin_run = run_executable_with_timeout(&twin_binary, codegen_run_timeout())
            .expect("run the gcc twin");
        assert!(!twin_run.timed_out, "{opt_level:?}: the twin timed out");
        assert_eq!(
            String::from_utf8_lossy(&twin_run.output.stdout).to_string(),
            EXPECTED,
            "{opt_level:?}: the gcc twin pins the expected text"
        );
    }
}

/// A module-local helper stays out of a shared object's dynamic symbol table,
/// while the near-twin with an `External` helper is exported — so the binding
/// is load-bearing and not an artefact of the link.
#[cfg(all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
#[test]
fn native_a_module_local_helper_is_not_exported_from_a_shared_object() {
    use common::rosetta::{codegen_link_timeout, command_output_with_timeout};

    let scratch = fresh_dir::create("x86_64-elf-local-dynsym");
    let dir = scratch.path();
    let dynamic_symbols = |library: &std::path::Path| {
        let mut command = std::process::Command::new("nm");
        command.arg("-D").arg("--defined-only").arg(library);
        let output = command_output_with_timeout(&mut command, codegen_link_timeout())
            .expect("nm must spawn");
        assert!(
            !output.timed_out && output.output.status.success(),
            "nm must read the library:\n{}",
            String::from_utf8_lossy(&output.output.stderr)
        );
        String::from_utf8_lossy(&output.output.stdout)
            .lines()
            .filter_map(|line| line.split_whitespace().last().map(str::to_string))
            .collect::<std::collections::BTreeSet<String>>()
    };
    // The slot is Internal here: see `local_binding_module` — only AArch64 ELF
    // implements the `pic` relocation model, so a reference to a preemptible
    // global cannot be linked into an x86-64 shared object at all.
    for (linkage, exported) in [(Linkage::Internal, false), (Linkage::External, true)] {
        let module = local_binding_module("a", linkage, Visibility::Default, Linkage::Internal, 7);
        let object = compiler(LINUX, OptLevel::O2)
            .compile(&module)
            .unwrap_or_else(|error| panic!("{linkage:?} must compile: {error:?}"))
            .object_code;
        let path = dir.join(format!("shared_{linkage:?}.o"));
        let library = dir.join(format!("libshared_{linkage:?}.so"));
        std::fs::write(&path, &object).expect("write the object");
        let (linked, stderr) = cc(&[
            "-shared",
            "-o",
            library.to_str().unwrap(),
            path.to_str().unwrap(),
        ]);
        assert!(
            linked,
            "{linkage:?}: the shared link must succeed:\n{stderr}"
        );
        let symbols = dynamic_symbols(&library);
        assert_eq!(
            symbols.contains("helper"),
            exported,
            "{linkage:?}: `helper` in .dynsym must be {exported}: {symbols:?}"
        );
        assert!(
            symbols.contains("a_direct"),
            "{linkage:?}: the exported entry point must be in .dynsym: {symbols:?}"
        );
    }
}
