// Copyright 2026 Andrew Yates | Apache-2.0
//! ELF and Linux-native twin of `e2e_aarch64_heap_dealloc.rs` for TrustIR
//! `Inst::HeapAlloc` released by a call to the owning runtime's deallocation
//! entry point on aarch64-unknown-linux-gnu (`Inst::Dealloc` is refused for
//! codegen in every body, G18-1).
//!
//! Host-neutral rows compile the shared corpus to ELF at O0-O3 and check,
//! with an independent ELF64 reader and the `trust-cg-lift` decoder, that
//! every allocator entry is reached by a `BL` carrying an
//! `R_AARCH64_CALL26` relocation against the undefined global symbol, in the
//! expected number; two byte mutations show the check can fail. The
//! Linux-only row links the object with `cc -Wl,--wrap=malloc,--wrap=free`
//! against the shared counting driver and executes it at O0-O3 (the Linux
//! floor runs it; this Mac has no Linux linker or runtime). Execution and
//! object-structure evidence, not proof of the external allocator.

#[path = "common/heap_dealloc_corpus.rs"]
mod corpus;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::collections::BTreeMap;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_cg_lift::disasm::aarch64::{Instruction, decode};

const TRIPLE: &str = "aarch64-unknown-linux-gnu";
const SHT_SYMTAB: u32 = 2;
const SHT_RELA: u32 = 4;
const SHF_EXECINSTR: u64 = 4;
const R_AARCH64_CALL26: u32 = 283;
const R_AARCH64_JUMP26: u32 = 282;

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

fn u64_at(object: &[u8], offset: usize) -> Result<usize, String> {
    bytes(object, offset).map(|raw| u64::from_le_bytes(raw) as usize)
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

/// A relocation applied to an executable section.
struct TextRelocation {
    symbol: String,
    kind: u32,
    undefined_global: bool,
    /// File offsets of the relocation record and the relocated instruction.
    record: usize,
    instruction: usize,
}

/// Independent System V ELF64 little-endian relocatable-object reader.
fn text_relocations(object: &[u8]) -> Result<Vec<TextRelocation>, String> {
    if object.get(..6) != Some(b"\x7fELF\x02\x01".as_slice()) {
        return Err("not an ELF64 little-endian object".into());
    }
    if u16_at(object, 16)? != 1 || u16_at(object, 18)? != 183 {
        return Err("not an AArch64 relocatable object".into());
    }
    let (shoff, shentsize, shnum) = (
        u64_at(object, 0x28)?,
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
                flags: u64_at(object, header + 8)? as u64,
                offset: u64_at(object, header + 24)?,
                size: u64_at(object, header + 32)?,
                link: u32_at(object, header + 40)? as usize,
                info: u32_at(object, header + 44)? as usize,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let mut relocations = Vec::new();
    for rela in sections.iter().filter(|section| section.kind == SHT_RELA) {
        let target = sections.get(rela.info).ok_or("rela target out of range")?;
        if target.flags & SHF_EXECINSTR == 0 {
            continue;
        }
        let symtab = sections.get(rela.link).ok_or("rela symtab out of range")?;
        if symtab.kind != SHT_SYMTAB {
            return Err("rela link is not a symbol table".into());
        }
        let strtab = sections.get(symtab.link).ok_or("strtab out of range")?;
        for entry in 0..rela.size / 24 {
            let record = rela.offset + entry * 24;
            let offset = u64_at(object, record)?;
            let info = u64_at(object, record + 8)? as u64;
            let symbol = symtab.offset + (info >> 32) as usize * 24;
            let name = c_string(object, strtab.offset + u32_at(object, symbol)? as usize)?;
            let binding = bytes::<1>(object, symbol + 4)?[0] >> 4;
            let section_index = u16_at(object, symbol + 6)?;
            if offset + 4 > target.size {
                return Err(format!("relocation offset {offset:#x} outside its section"));
            }
            relocations.push(TextRelocation {
                symbol: name,
                kind: info as u32,
                undefined_global: binding == 1 && section_index == 0,
                record,
                instruction: target.offset + offset,
            });
        }
    }
    Ok(relocations)
}

/// Count the `BL` call sites of each allocator entry, refusing any other
/// relocation or instruction shape against one.
fn allocator_call_sites(object: &[u8]) -> Result<BTreeMap<String, usize>, String> {
    let mut sites = BTreeMap::new();
    for relocation in text_relocations(object)? {
        if !corpus::CALL_SITES
            .iter()
            .any(|(name, _)| *name == relocation.symbol)
        {
            continue;
        }
        if relocation.kind != R_AARCH64_CALL26 || !relocation.undefined_global {
            return Err(format!(
                "{} is reached by relocation type {} (undefined global: {})",
                relocation.symbol, relocation.kind, relocation.undefined_global
            ));
        }
        let word = u32_at(object, relocation.instruction)?;
        match decode(word) {
            Ok(Instruction::UncondBranch(branch)) if branch.link => {}
            other => {
                return Err(format!(
                    "{} relocation applies to {word:#010x} ({other:?}), not BL",
                    relocation.symbol
                ));
            }
        }
        *sites.entry(relocation.symbol).or_insert(0) += 1;
    }
    Ok(sites)
}

fn expected_call_sites() -> BTreeMap<String, usize> {
    corpus::CALL_SITES
        .iter()
        .map(|(name, count)| (name.to_string(), *count))
        .collect()
}

#[test]
fn elf_object_calls_every_allocator_entry_through_bl_o0_through_o3() {
    let module = corpus::corpus(TRIPLE);
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let object = compile(&module, opt_level).unwrap();
        assert_eq!(
            allocator_call_sites(&object),
            Ok(expected_call_sites()),
            "{opt_level:?}"
        );
    }

    // Mutation controls: the checker must reject a release reached by a
    // non-linking relocation and a relocated instruction that is not BL.
    let object = compile(&module, OptLevel::O0).unwrap();
    let release = text_relocations(&object)
        .unwrap()
        .into_iter()
        .find(|relocation| relocation.symbol == "__rust_dealloc")
        .unwrap();
    let mut jump = object.clone();
    jump[release.record + 8..release.record + 12].copy_from_slice(&R_AARCH64_JUMP26.to_le_bytes());
    assert!(allocator_call_sites(&jump).is_err());
    let mut branch = object;
    branch[release.instruction + 3] &= 0x7f; // BL -> B
    assert!(allocator_call_sites(&branch).is_err());
}

#[test]
fn elf_backend_refuses_every_dealloc_whatever_its_provenance() {
    for opt_level in [OptLevel::O0, OptLevel::O3] {
        for (shape, module) in corpus::dealloc_modules(TRIPLE) {
            let refusal = compile(&module, opt_level)
                .expect_err("every Inst::Dealloc must be refused (G18-1)");
            assert!(
                refusal.contains("[TCG-DEALLOC]") && refusal.contains("UnlowerableForCodegen"),
                "{shape} at {opt_level:?}: {refusal}"
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
    use std::fs;
    use std::process::Command;
    use trust_cg_codegen::pipeline::OptLevel;

    #[test]
    fn native_heap_dealloc_balances_rust_and_libc_allocators_o0_through_o3() {
        let module = corpus::corpus(TRIPLE);
        for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let object = compile(&module, opt_level).unwrap();
            let dir = fresh_dir::create("trust-cg-heap-dealloc-linux-");
            fs::write(dir.join("module.o"), &object).unwrap();
            fs::write(dir.join("driver.c"), corpus::DRIVER).unwrap();
            let binary = dir.join("driver");
            let link = process::command_output_with_timeout(
                Command::new("cc")
                    .arg("-O2")
                    .arg("-fno-builtin")
                    .arg(dir.join("driver.c"))
                    .arg(dir.join("module.o"))
                    .arg("-Wl,--wrap=malloc,--wrap=free")
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
            let run = process::run_executable_with_timeout(&binary, process::codegen_run_timeout())
                .unwrap();
            let stdout = String::from_utf8_lossy(&run.output.stdout);
            assert!(
                !run.timed_out && run.output.status.success(),
                "{opt_level:?} files={dir:?}: {stdout} {}",
                String::from_utf8_lossy(&run.output.stderr)
            );
            assert_eq!(
                stdout.trim(),
                corpus::EXPECTED_PASS,
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
