// Copyright 2026 Andrew Yates | Apache-2.0
//! ELF and Linux-native twin of `e2e_aarch64_direct_enums.rs` for direct-tag
//! trust-ir enums and enum/record-typed globals on aarch64-unknown-linux-gnu
//! (ledger L05-P5).
//!
//! Host-neutral rows compile the shared corpus to ELF at O0-O3 and check,
//! with an independent ELF64 reader, that every corpus function is a defined
//! global `STT_FUNC` of non-zero size in an executable section, and that
//! every enum-, record- and relocation-bearing global is a defined global
//! `STT_OBJECT` of the producer's size whose section bytes carry the
//! direct-tag image at the lanes the code reads, `g_slot`'s pointer payload
//! relocated by `R_AARCH64_ABS64` against `ord_disc` — each with byte
//! mutations showing the check can fail; that the reference interpreter is
//! pinned to the closed forms for this triple's corpus; and that what stays
//! refused is refused by name. The Linux-only rows link the object with `cc`
//! against the shared C driver and execute it at O0-O3, requiring the
//! driver's verdict and every printed oracle value to equal the
//! interpreter's, and call the `*_make` selectors with the unspecified upper
//! bits of `x1` set — the AAPCS64 narrowing rule an Apple-ABI caller never
//! exercises. Execution and object-structure evidence, not proof of enum
//! semantics.

#[path = "common/direct_enums_corpus.rs"]
mod corpus;

#[path = "common/admission_expect.rs"]
mod admission_expect;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::collections::BTreeMap;

use corpus::{GLOBAL_IMAGES, LEVELS, ORACLE};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir_build::validate_module;

const TRIPLE: &str = "aarch64-unknown-linux-gnu";
const SHT_SYMTAB: u32 = 2;
const SHT_RELA: u32 = 4;
const SHF_WRITE: u64 = 1;
const SHF_ALLOC: u64 = 2;
const SHF_EXECINSTR: u64 = 4;
const STB_GLOBAL: u8 = 1;
const STT_OBJECT: u8 = 1;
const STT_FUNC: u8 = 2;
const R_AARCH64_ABS64: u32 = 257;

fn compile(module: &trust_ir::Module, opt_level: OptLevel) -> Result<Vec<u8>, String> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(TRIPLE).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .map(|output| output.object_code)
    .map_err(|error| format!("{error:?}"))
}

fn bytes<const N: usize>(object: &[u8], offset: usize) -> Result<[u8; N], String> {
    object
        .get(offset..offset + N)
        .and_then(|slice| slice.try_into().ok())
        .ok_or_else(|| format!("read of {N} bytes at {offset:#x} is out of bounds"))
}

fn u16_at(object: &[u8], offset: usize) -> Result<u16, String> {
    bytes(object, offset).map(u16::from_le_bytes)
}

fn u32_at(object: &[u8], offset: usize) -> Result<u32, String> {
    bytes(object, offset).map(u32::from_le_bytes)
}

fn u64_at(object: &[u8], offset: usize) -> Result<u64, String> {
    bytes(object, offset).map(u64::from_le_bytes)
}

fn c_string(object: &[u8], offset: usize) -> Result<String, String> {
    let tail = object
        .get(offset..)
        .ok_or_else(|| format!("string at {offset:#x} is out of bounds"))?;
    let end = tail
        .iter()
        .position(|byte| *byte == 0)
        .ok_or_else(|| format!("string at {offset:#x} is unterminated"))?;
    String::from_utf8(tail[..end].to_vec()).map_err(|error| error.to_string())
}

struct Section {
    kind: u32,
    flags: u64,
    offset: usize,
    size: usize,
    link: usize,
    info: usize,
}

/// A symbol-table entry, with the file offset of its 24-byte record.
struct Symbol {
    name: String,
    binding: u8,
    kind: u8,
    section_index: usize,
    value: u64,
    size: u64,
    record: usize,
}

/// A relocation against a data section, with the file offset of its record.
struct DataRelocation {
    section_index: usize,
    offset: u64,
    kind: u32,
    symbol: String,
    addend: i64,
    record: usize,
}

/// Independent System V ELF64 little-endian relocatable-object reader.
struct Elf<'a> {
    object: &'a [u8],
    sections: Vec<Section>,
    symbols: Vec<Symbol>,
    relocations: Vec<DataRelocation>,
}

impl<'a> Elf<'a> {
    fn parse(object: &'a [u8]) -> Result<Self, String> {
        if object.get(..6) != Some(b"\x7fELF\x02\x01".as_slice()) {
            return Err("not an ELF64 little-endian object".into());
        }
        if u16_at(object, 16)? != 1 || u16_at(object, 18)? != 183 {
            return Err("not an AArch64 relocatable object".into());
        }
        let (shoff, shentsize, shnum) = (
            u64_at(object, 0x28)? as usize,
            u16_at(object, 0x3a)? as usize,
            u16_at(object, 0x3c)? as usize,
        );
        if shentsize != 64 {
            return Err(format!("section header size {shentsize}"));
        }
        let sections = (0..shnum)
            .map(|index| {
                let header = shoff + index * shentsize;
                Ok(Section {
                    kind: u32_at(object, header + 4)?,
                    flags: u64_at(object, header + 8)?,
                    offset: u64_at(object, header + 24)? as usize,
                    size: u64_at(object, header + 32)? as usize,
                    link: u32_at(object, header + 40)? as usize,
                    info: u32_at(object, header + 44)? as usize,
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        let symtab = sections
            .iter()
            .find(|section| section.kind == SHT_SYMTAB)
            .ok_or("no symbol table")?;
        let strtab = sections.get(symtab.link).ok_or("strtab out of range")?;
        let symbols = (0..symtab.size / 24)
            .map(|entry| {
                let record = symtab.offset + entry * 24;
                let info = bytes::<1>(object, record + 4)?[0];
                Ok(Symbol {
                    name: c_string(object, strtab.offset + u32_at(object, record)? as usize)?,
                    binding: info >> 4,
                    kind: info & 0xf,
                    section_index: u16_at(object, record + 6)? as usize,
                    value: u64_at(object, record + 8)?,
                    size: u64_at(object, record + 16)?,
                    record,
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        let mut relocations = Vec::new();
        for (index, rela) in sections.iter().enumerate() {
            if rela.kind != SHT_RELA {
                continue;
            }
            let target = sections.get(rela.info).ok_or("rela target out of range")?;
            if target.flags & SHF_EXECINSTR != 0 {
                continue;
            }
            let rela_symtab = sections.get(rela.link).ok_or("rela symtab out of range")?;
            if rela_symtab.kind != SHT_SYMTAB {
                return Err(format!("rela section {index} does not link a symbol table"));
            }
            let rela_strtab = sections
                .get(rela_symtab.link)
                .ok_or("strtab out of range")?;
            for entry in 0..rela.size / 24 {
                let record = rela.offset + entry * 24;
                let info = u64_at(object, record + 8)?;
                let symbol = rela_symtab.offset + (info >> 32) as usize * 24;
                relocations.push(DataRelocation {
                    section_index: rela.info,
                    offset: u64_at(object, record)?,
                    kind: info as u32,
                    symbol: c_string(
                        object,
                        rela_strtab.offset + u32_at(object, symbol)? as usize,
                    )?,
                    addend: u64_at(object, record + 16)? as i64,
                    record,
                });
            }
        }
        Ok(Self {
            object,
            sections,
            symbols,
            relocations,
        })
    }

    fn section(&self, index: usize) -> Result<&Section, String> {
        self.sections
            .get(index)
            .ok_or_else(|| format!("section {index} out of range"))
    }

    /// The one defined global symbol `name` of kind `kind`.
    fn defined_global(&self, name: &str, kind: u8) -> Result<&Symbol, String> {
        let mut found = self.symbols.iter().filter(|symbol| symbol.name == name);
        let symbol = found
            .next()
            .ok_or_else(|| format!("{name} is not in the symbol table"))?;
        if found.next().is_some() {
            return Err(format!("{name} is defined more than once"));
        }
        if symbol.binding != STB_GLOBAL || symbol.kind != kind || symbol.section_index == 0 {
            return Err(format!(
                "{name} is not a defined global symbol of type {kind} (binding {}, type {}, section {})",
                symbol.binding, symbol.kind, symbol.section_index
            ));
        }
        Ok(symbol)
    }

    /// The file bytes of `symbol`'s definition.
    fn symbol_bytes(&self, symbol: &Symbol) -> Result<&'a [u8], String> {
        let section = self.section(symbol.section_index)?;
        let start = symbol.value as usize;
        let end = start + symbol.size as usize;
        if end > section.size {
            return Err(format!("{} extends past its section", symbol.name));
        }
        self.object
            .get(section.offset + start..section.offset + end)
            .ok_or_else(|| format!("{} is outside the file", symbol.name))
    }
}

/// Function symbols `name -> (size, symbol record offset)` that are defined,
/// global and in an executable section.
fn defined_functions(object: &[u8]) -> Result<BTreeMap<String, (u64, usize)>, String> {
    let elf = Elf::parse(object)?;
    let mut functions = BTreeMap::new();
    for symbol in &elf.symbols {
        if symbol.binding != STB_GLOBAL || symbol.kind != STT_FUNC || symbol.section_index == 0 {
            continue;
        }
        if elf.section(symbol.section_index)?.flags & SHF_EXECINSTR == 0 {
            return Err(format!(
                "function symbol {} is not in an executable section",
                symbol.name
            ));
        }
        functions.insert(symbol.name.clone(), (symbol.size, symbol.record));
    }
    Ok(functions)
}

fn corpus_functions_are_defined(object: &[u8]) -> Result<(), String> {
    let functions = defined_functions(object)?;
    for symbol in corpus::symbols() {
        match functions.get(symbol) {
            Some((size, _)) if *size > 0 => {}
            Some(_) => return Err(format!("{symbol} has size 0")),
            None => return Err(format!("{symbol} is not a defined global function")),
        }
    }
    Ok(())
}

/// Every corpus global is a defined global `STT_OBJECT` of the producer's
/// size in an allocated, non-executable section (writable when the global is
/// mutable, read-only when it is immutable and relocation-free), its bytes
/// carry the direct-tag image at every lane the code reads, and its only
/// relocation is the `R_AARCH64_ABS64` against `ord_disc` (addend 0) at
/// `g_slot`'s pointer payload.
fn globals_carry_the_direct_tag_image(object: &[u8]) -> Result<(), String> {
    let elf = Elf::parse(object)?;
    for image in GLOBAL_IMAGES {
        let symbol = elf.defined_global(image.name, STT_OBJECT)?;
        let section = elf.section(symbol.section_index)?;
        if section.flags & SHF_ALLOC == 0 || section.flags & SHF_EXECINSTR != 0 {
            return Err(format!(
                "{} is not in an allocated data section",
                image.name
            ));
        }
        // A mutable global needs a writable section (the driver stores to
        // `g_mixed`); an immutable one without relocations must be read-only;
        // an immutable one with a relocation is `.data.rel.ro`-style, writable
        // in the object so the loader can apply the relocation, so its
        // writability is not constrained here.
        let writable = section.flags & SHF_WRITE != 0;
        if image.mutable && !writable {
            return Err(format!(
                "{} is mutable but in a read-only section",
                image.name
            ));
        }
        if !image.mutable && image.symbol_slot.is_none() && writable {
            return Err(format!(
                "{} is immutable and relocation-free but in a writable section",
                image.name
            ));
        }
        if symbol.size != image.size {
            return Err(format!(
                "{} has size {}, not the producer's {}",
                image.name, symbol.size, image.size
            ));
        }
        let data = elf.symbol_bytes(symbol)?;
        for (offset, want) in image.lanes {
            let offset = *offset as usize;
            if data.get(offset..offset + want.len()) != Some(*want) {
                return Err(format!(
                    "{} lane at {offset}: {:02x?}, want {want:02x?}",
                    image.name,
                    data.get(offset..offset + want.len())
                ));
            }
        }
        let relocations: Vec<_> = elf
            .relocations
            .iter()
            .filter(|relocation| {
                relocation.section_index == symbol.section_index
                    && relocation.offset >= symbol.value
                    && relocation.offset < symbol.value + symbol.size
            })
            .collect();
        match (image.symbol_slot, relocations.as_slice()) {
            (None, []) => {}
            (Some(slot), [relocation])
                if relocation.offset == symbol.value + slot
                    && relocation.kind == R_AARCH64_ABS64
                    && relocation.symbol == "ord_disc"
                    && relocation.addend == 0 => {}
            (slot, found) => {
                return Err(format!(
                    "{} has {} relocation(s) {:?}, want an R_AARCH64_ABS64 against ord_disc at {slot:?}",
                    image.name,
                    found.len(),
                    found
                        .iter()
                        .map(|r| (r.offset - symbol.value, r.kind, r.symbol.as_str(), r.addend))
                        .collect::<Vec<_>>()
                ));
            }
        }
    }
    Ok(())
}

#[test]
fn elf_object_defines_every_direct_enum_function_o0_through_o3() {
    let module = corpus::corpus(TRIPLE);
    for opt_level in LEVELS {
        let object = compile(&module, opt_level).unwrap();
        assert_eq!(
            corpus_functions_are_defined(&object),
            Ok(()),
            "{opt_level:?}"
        );
    }
    // Mutation controls: a local binding and a zero size must each fail with
    // the named reason.
    let object = compile(&module, OptLevel::O0).unwrap();
    let (_, record) = defined_functions(&object).unwrap()["ord_classify"];
    let mut local = object.clone();
    local[record + 4] &= 0x0f; // STB_GLOBAL -> STB_LOCAL
    assert_eq!(
        corpus_functions_are_defined(&local),
        Err("ord_classify is not a defined global function".to_string())
    );
    let mut empty = object;
    empty[record + 16..record + 24].copy_from_slice(&0u64.to_le_bytes());
    assert_eq!(
        corpus_functions_are_defined(&empty),
        Err("ord_classify has size 0".to_string())
    );
}

#[test]
fn elf_object_renders_enum_and_record_globals_from_the_direct_tag_image_o0_through_o3() {
    let module = corpus::corpus(TRIPLE);
    for opt_level in LEVELS {
        let object = compile(&module, opt_level).unwrap();
        assert_eq!(
            globals_carry_the_direct_tag_image(&object),
            Ok(()),
            "{opt_level:?}"
        );
    }
    // Mutation controls: a wrong lane byte, a wrong relocation type and a
    // wrong symbol size must each fail with the named reason.
    let object = compile(&module, OptLevel::O0).unwrap();
    let elf = Elf::parse(&object).unwrap();
    let g_bytes = elf.defined_global("g_bytes", STT_OBJECT).unwrap();
    let tail = elf.section(g_bytes.section_index).unwrap().offset + g_bytes.value as usize + 4;
    let g_slot = elf.defined_global("g_slot", STT_OBJECT).unwrap();
    let relocation = elf
        .relocations
        .iter()
        .find(|relocation| {
            relocation.section_index == g_slot.section_index
                && relocation.offset == g_slot.value + 8
        })
        .unwrap()
        .record;
    let g_rec = elf.defined_global("g_rec", STT_OBJECT).unwrap().record;
    let mut lane = object.clone();
    lane[tail] ^= 0x01; // g_bytes' trailing u8 0xe7 -> 0xe6
    assert_eq!(
        globals_carry_the_direct_tag_image(&lane),
        Err("g_bytes lane at 0: Some([01, 00, c3, a9, e6]), want [01, 00, c3, a9, e7]".to_string())
    );
    let mut narrow = object.clone();
    narrow[relocation + 8..relocation + 12].copy_from_slice(&(R_AARCH64_ABS64 + 1).to_le_bytes());
    assert_eq!(
        globals_carry_the_direct_tag_image(&narrow),
        Err(
            "g_slot has 1 relocation(s) [(8, 258, \"ord_disc\", 0)], want an R_AARCH64_ABS64 against ord_disc at Some(8)"
                .to_string()
        )
    );
    let mut short = object;
    short[g_rec + 16..g_rec + 24].copy_from_slice(&8u64.to_le_bytes());
    assert_eq!(
        globals_carry_the_direct_tag_image(&short),
        Err("g_rec has size 8, not the producer's 16".to_string())
    );
}

/// The interpreter is pinned to the closed forms for this triple's corpus,
/// so it cannot agree with a wrong native value by being wrong the same way.
#[test]
fn interpreter_oracle_matches_the_closed_forms() {
    let module = corpus::corpus(TRIPLE);
    assert_eq!(
        validate_module(&module),
        [],
        "the corpus must be valid trust-ir"
    );
    for (name, want) in ORACLE {
        assert_eq!(corpus::interpret(&module, name), *want, "{name}");
    }
}

/// What stays refused is refused by name on the ELF path too, at O0 and O3.
#[test]
fn elf_backend_refuses_what_stays_refused_by_name() {
    for (fixture, needle, module) in corpus::refusal_fixtures(TRIPLE) {
        for opt_level in [OptLevel::O0, OptLevel::O3] {
            let error = compile(&module, opt_level).expect_err(needle);
            assert!(
                admission_expect::names_first_finding(&module, &error, &permit_unlicensed())
                    .unwrap_or_else(|| error.contains(needle)),
                "{fixture} {opt_level:?}: neither trust-ir's admission finding nor `{needle}` \
                 in {error}"
            );
        }
    }
}

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[path = "common/rosetta.rs"]
mod process;

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
mod native {
    use super::{TRIPLE, compile, corpus, fresh_dir, process};
    use std::collections::BTreeMap;
    use std::fs;
    use std::path::Path;
    use std::process::Command;
    use trust_cg_codegen::pipeline::OptLevel;
    use trust_ir_build::validate_module;

    /// A fresh directory holding `module.o` and `driver.c`.
    fn stage(tag: &str, object: &[u8], driver: &str) -> fresh_dir::ScratchDir {
        let dir = fresh_dir::create(&format!("trust-cg-direct-enums-linux-{tag}-"));
        fs::write(dir.join("module.o"), object).unwrap();
        fs::write(dir.join("driver.c"), driver).unwrap();
        dir
    }

    /// Link `driver.c` with `module.o` by the host `cc` and run the result,
    /// returning its stdout; any link or run failure panics with the files.
    fn link_and_run(dir: &Path, opt_level: OptLevel) -> String {
        let binary = dir.join("driver");
        let link = process::command_output_with_timeout(
            Command::new("cc")
                .arg("-O2")
                .arg(dir.join("driver.c"))
                .arg(dir.join("module.o"))
                .arg("-o")
                .arg(&binary),
            process::codegen_link_timeout(),
        )
        .unwrap();
        assert!(
            !link.timed_out && link.output.status.success(),
            "{opt_level:?} files={dir:?}: {}",
            String::from_utf8_lossy(&link.output.stderr)
        );
        let run =
            process::run_executable_with_timeout(&binary, process::codegen_run_timeout()).unwrap();
        let stdout = String::from_utf8_lossy(&run.output.stdout).into_owned();
        assert!(
            !run.timed_out && run.output.status.success(),
            "{opt_level:?} files={dir:?}: {stdout} {}",
            String::from_utf8_lossy(&run.output.stderr)
        );
        stdout
    }

    #[test]
    fn native_direct_enums_agree_with_the_c_oracle_and_the_interpreter_o0_through_o3() {
        let module = corpus::corpus(TRIPLE);
        assert_eq!(
            validate_module(&module),
            [],
            "the corpus must be valid trust-ir"
        );
        let expected: BTreeMap<&str, u64> = corpus::ORACLE
            .iter()
            .map(|(name, _)| (*name, corpus::interpret(&module, name)))
            .collect();
        for opt_level in corpus::LEVELS {
            let object = compile(&module, opt_level).unwrap();
            assert_eq!(&object[..4], b"\x7fELF", "ELF object expected");
            let dir = stage("oracle", &object, &corpus::driver());
            let stdout = link_and_run(&dir, opt_level);
            let mut native: BTreeMap<&str, u64> = BTreeMap::new();
            let mut verdict = None;
            for line in stdout.lines() {
                if let Some((name, value)) = line.split_once('=') {
                    native.insert(name, value.trim().parse().expect("driver prints u64"));
                } else {
                    verdict = Some(line.trim().to_string());
                }
            }
            assert_eq!(
                verdict.as_deref(),
                Some(format!("PASS {} direct-enum checks", corpus::EXPECTED_CHECKS).as_str()),
                "{opt_level:?} files={dir:?}: incomplete native execution: {stdout}"
            );
            for (name, want) in &expected {
                assert_eq!(
                    native.get(name),
                    Some(want),
                    "{opt_level:?}: native `{name}` disagrees with the interpreter"
                );
            }
            eprintln!(
                "{opt_level:?}: {} and {} oracle values agree with the interpreter",
                verdict.unwrap_or_default(),
                expected.len()
            );
            fs::remove_dir_all(&dir).unwrap();
        }
    }

    /// AAPCS64 selector driver: every `*_make(out, which)` is called twice per
    /// selector, once as C calls it and once through `blr` with `x1` holding
    /// `which` in bits 0-7 and garbage above, and the two images must agree.
    const SELECTOR_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern void ord_make(void *, uint8_t);
extern void mixed_make(void *, uint8_t);
extern void reprc_make(void *, uint8_t);
extern void small_make(void *, uint8_t);

static int checks = 0;
static int discriminating = 0;
static int failures = 0;
static int quiet = 0; /* set while the negative control runs */

/* AAPCS64 (Arm IHI 0055, "Parameter passing rules"): Stage C rule C.9
   copies an Integral argument of 8 bytes or fewer "to the least significant
   bits in x[NGRN]", the Stage C preamble says "any unused bits in the
   register have unspecified value", and the rules' observations add that
   "named integral values must be narrowed by the callee rather than the
   caller". Apple's arm64 ABI diverges by making the CALLER sign- or
   zero-extend to 32 bits, so a callee that is correct on Darwin may read all
   of w1. A C caller here would extend anyway (`mov w1, #n`), so call through
   `blr` with x1 set to `dirt | which` instead: `which` in bits 0-7, `dirt`
   above. */
static void make_with_unspecified_upper_bits(void (*make)(void *, uint8_t),
                                             void *out, uint8_t which, uint64_t dirt) {
    register void *out_x0 __asm__("x0") = out;
    register uint64_t which_x1 __asm__("x1") = (dirt & ~0xffull) | which;
    register void (*make_x9)(void *, uint8_t) __asm__("x9") = make;
    __asm__ volatile("blr %2"
                     : "+r"(out_x0), "+r"(which_x1), "+r"(make_x9)
                     :
                     : "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x10", "x11", "x12",
                       "x13", "x14", "x15", "x16", "x17", "x18", "x30",
                       "v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7",
                       "v8", "v9", "v10", "v11", "v12", "v13", "v14", "v15",
                       "v16", "v17", "v18", "v19", "v20", "v21", "v22", "v23",
                       "v24", "v25", "v26", "v27", "v28", "v29", "v30", "v31",
                       "memory", "cc");
}

/* Each `*_make` switches on `which` over cases 0..n-2 and takes its default
   arm for everything else, so only a selector below `default_arm` can tell a
   narrowing callee from one that reads the whole register: with dirt above
   bit 7 an un-narrowed selector never equals a case and lands on the default
   arm, while the clean call does not. A selector that already takes the
   default arm (the last declared one, or an out-of-range value) lands there
   either way; those checks are consistency checks only and are counted apart. */
static int check_selector(const char *name, void (*make)(void *, uint8_t), uint8_t which,
                          uint8_t default_arm) {
    static const uint64_t dirts[2] = { 0xffffffffffffffffull, 0x0123456789abcdefull };
    uint8_t clean[16], dirty[16];
    int local_failures = 0;
    memset(clean, 0xEE, 16);
    make(clean, which);
    for (int i = 0; i < 2; i++) {
        memset(dirty, 0xEE, 16);
        make_with_unspecified_upper_bits(make, dirty, which, dirts[i]);
        checks++;
        if (which < default_arm) discriminating++;
        if (memcmp(clean, dirty, 16) != 0) {
            local_failures++;
            failures++;
            if (quiet) continue;
            int byte = 0;
            while (clean[byte] == dirty[byte]) byte++;
            printf("FAIL %s(which=%u, x1=%016llx): image differs at byte %d (%02x vs %02x)\n",
                   name, (unsigned)which, (unsigned long long)((dirts[i] & ~0xffull) | which),
                   byte, clean[byte], dirty[byte]);
        }
    }
    return local_failures;
}

/* Negative control: a callee that ignores the narrowing rule and switches on
   all of x1, with the same shape as `ord_make` (cases 0 and 1, default arm
   2). Called through the same `blr` path it must fail every discriminating
   check and no consistency check, which shows the discriminating checks can
   fail at all. */
static void unnarrowed_make(void *out, uint64_t which) {
    uint8_t *bytes = out;
    switch (which) {
    case 0: bytes[0] = 0x10; break;
    case 1: bytes[0] = 0x11; break;
    default: bytes[0] = 0x12; break;
    }
}

static int unnarrowed_control(void) {
    void (*make)(void *, uint8_t) = (void (*)(void *, uint8_t))unnarrowed_make;
    int saved_checks = checks, saved_discriminating = discriminating, saved_failures = failures;
    int caught = 0, spurious = 0;
    quiet = 1;
    for (uint8_t which = 0; which < 3; which++) {
        int before = discriminating;
        int failed = check_selector("unnarrowed_make", make, which, 2);
        if (discriminating > before) caught += failed; else spurious += failed;
    }
    quiet = 0;
    checks = saved_checks; discriminating = saved_discriminating; failures = saved_failures;
    printf("CONTROL unnarrowed callee fails %d of 4 discriminating checks and %d of 2 default-arm checks\n",
           caught, spurious);
    return caught == 4 && spurious == 0;
}

int main(void) {
    if (!unnarrowed_control()) { printf("FAIL the unnarrowed-callee control\n"); return 1; }
    /* Every declared selector and one out-of-range selector per function;
       the last declared selector is each function's default arm. */
    for (uint8_t which = 0; which < 3; which++) check_selector("ord_make", ord_make, which, 2);
    check_selector("ord_make", ord_make, 200, 2);
    for (uint8_t which = 0; which < 3; which++) check_selector("mixed_make", mixed_make, which, 2);
    check_selector("mixed_make", mixed_make, 200, 2);
    for (uint8_t which = 0; which < 2; which++) check_selector("reprc_make", reprc_make, which, 1);
    check_selector("reprc_make", reprc_make, 200, 1);
    for (uint8_t which = 0; which < 2; which++) check_selector("small_make", small_make, which, 1);
    check_selector("small_make", small_make, 200, 1);
    if (failures) { printf("FAIL %d of %d aapcs64 selector checks\n", failures, checks); return 1; }
    printf("PASS %d discriminating and %d default-arm aapcs64 selector checks\n",
           discriminating, checks - discriminating);
    return 0;
}
"#;

    /// (4 + 4 + 3 + 3 selectors) x 2 upper-bit patterns = 28 checks, of
    /// which only the selectors below each function's default arm
    /// (2 + 2 + 1 + 1) x 2 = 12 can tell a narrowing callee from one that
    /// reads all of `x1`; the other 16 land on the default arm either way.
    /// The driver first proves the 12 can fail with a non-narrowing C callee.
    const SELECTOR_CONTROL: &str = "CONTROL unnarrowed callee fails 4 of 4 discriminating checks and 0 of 2 default-arm checks";
    const SELECTOR_PASS: &str = "PASS 12 discriminating and 16 default-arm aapcs64 selector checks";

    #[test]
    fn native_make_selectors_ignore_the_unspecified_upper_bits_of_x1_o0_through_o3() {
        let module = corpus::corpus(TRIPLE);
        for opt_level in corpus::LEVELS {
            let object = compile(&module, opt_level).unwrap();
            let dir = stage("selector", &object, SELECTOR_DRIVER);
            let stdout = link_and_run(&dir, opt_level);
            assert_eq!(
                stdout.trim(),
                format!("{SELECTOR_CONTROL}\n{SELECTOR_PASS}"),
                "{opt_level:?} files={dir:?}: incomplete native execution"
            );
            eprintln!("{opt_level:?}: {}", stdout.trim());
            fs::remove_dir_all(&dir).unwrap();
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
