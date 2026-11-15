// Copyright 2026 Andrew Yates | Apache-2.0
//! ELF and Linux-native twin of `e2e_aarch64_niche_enum.rs` for trust-ir
//! niche-encoded enums on aarch64-unknown-linux-gnu.
//!
//! Host-neutral rows compile the shared corpus to ELF at O0-O3 and check,
//! with an independent ELF64 reader, that every corpus function is a defined
//! global `STT_FUNC` of non-zero size in an executable section — what the
//! Linux link of the C driver resolves — with two byte mutations showing the
//! check can fail; and that the real compiler refuses a niche whose reserved
//! value is a valid payload. The Linux-only row links the object with `cc`
//! against the shared C driver and executes it at O0-O3 (the Linux floor runs
//! it; this Mac has no Linux linker or runtime). Execution and
//! object-structure evidence, not proof of the niche codec.

#[path = "common/niche_enum_corpus.rs"]
mod corpus;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::collections::BTreeMap;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};

const TRIPLE: &str = "aarch64-unknown-linux-gnu";
const SHT_SYMTAB: u32 = 2;
const SHF_EXECINSTR: u64 = 4;
const STB_GLOBAL: u8 = 1;
const STT_FUNC: u8 = 2;

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
}

/// Function symbols `name -> (size, symbol record offset)` that are defined,
/// global and in an executable section, read by an independent ELF64 reader.
fn defined_functions(object: &[u8]) -> Result<BTreeMap<String, (u64, usize)>, String> {
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
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let symtab = sections
        .iter()
        .find(|section| section.kind == SHT_SYMTAB)
        .ok_or("no symbol table")?;
    let strtab = sections.get(symtab.link).ok_or("strtab out of range")?;
    let mut functions = BTreeMap::new();
    for entry in 0..symtab.size / 24 {
        let record = symtab.offset + entry * 24;
        let info = bytes::<1>(object, record + 4)?[0];
        let section_index = u16_at(object, record + 6)? as usize;
        let size = u64_at(object, record + 16)?;
        if info >> 4 != STB_GLOBAL || info & 0xf != STT_FUNC || section_index == 0 {
            continue;
        }
        let section = sections
            .get(section_index)
            .ok_or("symbol section out of range")?;
        if section.flags & SHF_EXECINSTR == 0 {
            return Err(format!(
                "function symbol {entry} is not in an executable section"
            ));
        }
        let name = c_string(object, strtab.offset + u32_at(object, record)? as usize)?;
        functions.insert(name, (size, record));
    }
    Ok(functions)
}

fn corpus_functions_are_defined(object: &[u8]) -> Result<(), String> {
    let functions = defined_functions(object)?;
    for symbol in corpus::SYMBOLS {
        match functions.get(*symbol) {
            Some((size, _)) if *size > 0 => {}
            Some(_) => return Err(format!("{symbol} has size 0")),
            None => return Err(format!("{symbol} is not a defined global function")),
        }
    }
    Ok(())
}

#[test]
fn elf_object_defines_every_niche_function_o0_through_o3() {
    let module = corpus::corpus(TRIPLE);
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let object = compile(&module, opt_level).unwrap();
        assert_eq!(
            corpus_functions_are_defined(&object),
            Ok(()),
            "{opt_level:?}"
        );
    }
    // Mutation controls: a local binding and a zero size must both fail.
    let object = compile(&module, OptLevel::O0).unwrap();
    let (_, record) = defined_functions(&object).unwrap()["tri_disc"];
    let mut local = object.clone();
    local[record + 4] &= 0x0f; // STB_GLOBAL -> STB_LOCAL
    assert!(corpus_functions_are_defined(&local).is_err());
    let mut empty = object;
    empty[record + 16..record + 24].copy_from_slice(&0u64.to_le_bytes());
    assert!(corpus_functions_are_defined(&empty).is_err());
}

#[test]
fn backend_refuses_canonical_enum_retagging_at_every_optimization() {
    let module = corpus::discriminant_write_module(TRIPLE);
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.iter().any(|error| matches!(
        error,
        trust_ir_build::ValidationError::FieldAccessInvalid { op, reason, .. }
            if op.as_str() == "insert_field" && reason.contains("cannot rewrite an enum discriminant")
    )), "{errors:?}");
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        // Since WS7.3 ingestion admission refuses it first, by trust-ir's
        // own finding (the adapter's `EnumTagWriteUnsupported` stays behind
        // it on the raw adapter entries).
        let error = compile(&module, level).expect_err("retagging must not reach emission");
        assert!(
            error.starts_with("InvalidTrustIr(") && error.contains("FieldAccessInvalid"),
            "{level:?}: {error}"
        );
    }
}

#[test]
fn elf_backend_refuses_a_niche_whose_reserved_value_is_a_valid_payload() {
    let mut module = corpus::corpus(TRIPLE);
    let char_enum = module
        .enums
        .iter_mut()
        .find(|e| e.name == "OptionChar")
        .expect("the corpus has Option<char>");
    if let Some(layout) = char_enum.layout.as_mut()
        && let trust_ir::ty::EnumTagEncoding::Niche { niche_start, .. } = &mut layout.encoding
    {
        // 'A' is a Unicode scalar value: `Some('A')` would decode as `None`.
        *niche_start = 0x41;
    }
    for opt_level in [OptLevel::O0, OptLevel::O3] {
        let error = compile(&module, opt_level).expect_err("an overlapping niche must be refused");
        assert!(
            error.contains("[TCG-NICHE-ENUM]") && error.contains("overlap"),
            "{opt_level:?}: {error}"
        );
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
    fn native_niche_enums_agree_with_the_c_oracle_o0_through_o3() {
        let module = corpus::corpus(TRIPLE);
        for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let object = compile(&module, opt_level).unwrap();
            let dir = fresh_dir::create("trust-cg-niche-enum-linux-");
            fs::write(dir.join("module.o"), &object).unwrap();
            fs::write(dir.join("driver.c"), corpus::DRIVER).unwrap();
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
