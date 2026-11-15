// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use trust_cg_codegen::macho::fixup::{FixupList, FixupTarget};
use trust_cg_codegen::macho::reloc::AArch64RelocKind;
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig, encode_function_with_fixups};
use trust_cg_ir::MachFunction;
use trust_cg_lower::Function;
use trust_cg_verify::source_bound_frame::{
    ScalarCellRelocation, check_aarch64_scalar_cell_bytes, check_aarch64_scalar_cell_elf,
};

#[derive(serde::Deserialize)]
struct Capture {
    case: String,
    module: trust_ir::Module,
    lir: Function,
}

fn captures() -> Vec<Capture> {
    serde_json::from_str(include_str!("../src/source_bound_cell_sources.json")).unwrap()
}

fn prepared(c: &Capture) -> (Pipeline, MachFunction) {
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: match c.case.rsplit_once('-').unwrap().1 {
            "O0" => OptLevel::O0,
            "O1" => OptLevel::O1,
            "O2" => OptLevel::O2,
            "O3" => OptLevel::O3,
            _ => unreachable!(),
        },
        verify: false,
        ..PipelineConfig::for_target("aarch64-unknown-linux-gnu")
    });
    let (machine, _) = pipeline
        .prepare_function_with_metrics_and_trust_ir_module(
            &c.lir,
            None,
            &c.module,
            &c.module.functions[0],
        )
        .unwrap();
    (pipeline, machine)
}

fn encoded(c: &Capture) -> (Vec<u8>, FixupList) {
    let (_, machine) = prepared(c);
    encode_function_with_fixups(&machine).unwrap()
}

fn relocations(fixups: &FixupList) -> Vec<ScalarCellRelocation<'_>> {
    fixups
        .iter()
        .map(|fixup| {
            assert_eq!(fixup.kind, AArch64RelocKind::Branch26);
            assert_eq!(fixup.tls_model, None);
            let FixupTarget::NamedSymbol(symbol) = &fixup.target else {
                panic!("unexpected call target")
            };
            ScalarCellRelocation {
                offset: u64::from(fixup.offset),
                kind: 283,
                symbol,
                addend: fixup.addend,
            }
        })
        .collect()
}

#[test]
fn all_actual_scalar_call_bytes_and_symbolic_fixups_match_original_source() {
    let cases = captures();
    assert_eq!(cases.len(), 24);
    for c in cases {
        let (code, fixups) = encoded(&c);
        let relocations = relocations(&fixups);
        let checked = check_aarch64_scalar_cell_bytes(&c.module, &c.lir, &code, &relocations)
            .unwrap_or_else(|e| panic!("{}: {e}", c.case));
        assert!(std::ptr::eq(checked.code(), code.as_slice()));
        assert!(std::ptr::eq(checked.relocations(), relocations.as_slice()));
        assert!(std::ptr::eq(checked.source().module(), &c.module));
        assert_eq!(checked.source().call_count(), 1);
        println!(
            "CELL_BYTES {}",
            serde_json::json!({"case": c.case, "code":code,"offset":relocations[0].offset,"symbol":relocations[0].symbol})
        );
    }
}

#[test]
fn every_instruction_word_and_every_relocation_field_is_bound() {
    let mut words = 0;
    let mut records = 0;
    for c in captures() {
        let (code, fixups) = encoded(&c);
        let original = relocations(&fixups);
        check_aarch64_scalar_cell_bytes(&c.module, &c.lir, &code, &original).unwrap();
        for offset in (0..code.len()).step_by(4) {
            let mut bad = code.clone();
            bad[offset..offset + 4].copy_from_slice(&0xd420_0000_u32.to_le_bytes());
            assert!(
                check_aarch64_scalar_cell_bytes(&c.module, &c.lir, &bad, &original).is_err(),
                "{} replaced word {offset}",
                c.case
            );
            words += 1;
        }
        for change in 0..12 {
            let mut bad = original.clone();
            let mut bytes = code.clone();
            match change {
                0 => bad[0].kind = 282,
                1 => bad[0].symbol = "other_callback",
                2 => bad[0].addend = 4,
                3 => bad[0].addend = -4,
                4 => bad[0].offset += 4,
                5 => bad[0].offset += 1,
                6 => bad[0].offset = u64::MAX,
                7 => bad.clear(),
                8 => bad.push(bad[0].clone()),
                9 => {
                    let offset = bad[0].offset as usize;
                    bytes[offset..offset + 4].copy_from_slice(&0x1400_0000_u32.to_le_bytes());
                }
                10 => bytes[bad[0].offset as usize] = 1,
                _ => bytes.pop().map(|_| ()).unwrap(),
            }
            assert!(
                check_aarch64_scalar_cell_bytes(&c.module, &c.lir, &bytes, &bad).is_err(),
                "{} relocation change {change}",
                c.case
            );
            records += 1;
        }
    }
    println!("CELL_BYTES_MUTATIONS words={words} records={records}");
    assert_eq!(records, 288);
    assert!(words >= 24 * 12);
}

#[test]
fn complete_actual_elf_callers_bind_object_bytes_and_symbols() {
    for c in captures() {
        let (pipeline, machine) = prepared(&c);
        let object = pipeline.compile_module(&[machine]).unwrap();
        let checked = check_aarch64_scalar_cell_elf(&c.module, &c.lir, &object)
            .unwrap_or_else(|e| panic!("{}: {e}", c.case));
        let (code, fixups) = encoded(&c);
        assert_eq!(checked.code(), code);
        assert_eq!(checked.relocations(), relocations(&fixups));
        assert!(std::ptr::eq(checked.object(), object.as_slice()));
        assert!(std::ptr::eq(checked.source().module(), &c.module));
        println!(
            "CELL_ELF {}",
            serde_json::json!({"case":c.case,"object":object})
        );
    }
}

fn field(bytes: &[u8], offset: usize, width: usize) -> u64 {
    bytes[offset..offset + width]
        .iter()
        .enumerate()
        .fold(0, |v, (i, b)| v | (u64::from(*b) << (i * 8)))
}
fn put(bytes: &mut [u8], offset: usize, width: usize, value: u64) {
    bytes[offset..offset + width].copy_from_slice(&value.to_le_bytes()[..width]);
}

#[test]
fn elf_refuses_malformed_headers_names_calling_conventions_and_relocation_links() {
    let mut rejected = 0;
    let mut truncated = 0;
    for c in captures()
        .into_iter()
        .filter(|c| c.case == "aliased_f32_read-O0" || c.case == "local_cell_read-O3")
    {
        let (pipeline, machine) = prepared(&c);
        let object = pipeline.compile_module(&[machine]).unwrap();
        check_aarch64_scalar_cell_elf(&c.module, &c.lir, &object).unwrap();
        let headers = field(&object, 40, 8) as usize;
        let count = field(&object, 60, 2) as usize;
        let section = |kind| {
            (0..count)
                .find(|i| field(&object, headers + i * 64 + 4, 4) == kind)
                .unwrap()
        };
        let symhdr = headers + section(2) * 64;
        let symdata = field(&object, symhdr + 24, 8) as usize;
        let symcount = field(&object, symhdr + 32, 8) as usize / 24;
        let strhdr = headers + field(&object, symhdr + 40, 4) as usize * 64;
        let strdata = field(&object, strhdr + 24, 8) as usize;
        let symbol = |name: &str| {
            (0..symcount)
                .find(|i| {
                    let start = strdata + field(&object, symdata + i * 24, 4) as usize;
                    let end = object[start..].iter().position(|b| *b == 0).unwrap() + start;
                    &object[start..end] == name.as_bytes()
                })
                .unwrap()
        };
        let caller = symdata + symbol(&c.lir.name) * 24;
        let callee = symdata + symbol("c_change") * 24;
        let text_index = field(&object, caller + 6, 2) as usize;
        let texthdr = headers + text_index * 64;
        let textdata = field(&object, texthdr + 24, 8) as usize;
        let relhdr = (0..count)
            .map(|i| headers + i * 64)
            .find(|h| {
                field(&object, h + 4, 4) == 4 && field(&object, h + 44, 4) == text_index as u64
            })
            .unwrap();
        let reldata = field(&object, relhdr + 24, 8) as usize;
        let name = strdata + field(&object, callee, 4) as usize;
        let cases = [
            (4, 1, 1),
            (5, 1, 2),
            (16, 2, 2),
            (18, 2, 62),
            (20, 4, 2),
            (24, 8, 4),
            (32, 8, 64),
            (40, 8, u64::MAX),
            (48, 4, 1),
            (52, 2, 63),
            (56, 2, 1),
            (58, 2, 63),
            (60, 2, 65),
            (62, 2, 0),
            (texthdr + 24, 8, 8),
            (texthdr + 32, 8, u64::MAX),
            (texthdr + 8, 8, 7),
            (symhdr + 24, 8, u64::MAX),
            (symhdr + 32, 8, 25),
            (symhdr + 40, 4, text_index as u64),
            (caller + 4, 1, 0x10),
            (caller + 5, 1, 0x80),
            (caller + 6, 2, 0),
            (caller + 8, 8, 4),
            (caller + 16, 8, 4),
            (callee + 4, 1, 0x20),
            (callee + 5, 1, 0x80),
            (callee + 5, 1, 2),
            (callee + 6, 2, text_index as u64),
            (callee + 8, 8, 4),
            (callee + 16, 8, 8),
            (name, 1, 255),
            (name + "c_change".len(), 1, b'X' as u64),
            (relhdr + 4, 4, 9),
            (relhdr + 40, 4, text_index as u64),
            (relhdr + 44, 4, 0),
            (reldata, 8, u64::MAX),
            (reldata + 8, 4, 282),
            (reldata + 12, 4, u32::MAX as u64),
            (reldata + 16, 8, 4),
            (textdata, 4, 0xd4200000),
        ];
        for (offset, width, value) in cases {
            let mut bad = object.clone();
            put(&mut bad, offset, width, value);
            assert_ne!(bad, object, "test mutation must change bytes");
            assert!(
                check_aarch64_scalar_cell_elf(&c.module, &c.lir, &bad).is_err(),
                "{} accepted ELF change {offset}/{width}/{value}",
                c.case
            );
            rejected += 1;
        }
        for length in 0..object.len() {
            assert!(
                check_aarch64_scalar_cell_elf(&c.module, &c.lir, &object[..length]).is_err(),
                "{} accepted truncation {length}",
                c.case
            );
            truncated += 1;
        }
        // A deterministic parser stress campaign makes no claim that every
        // changed non-executable byte is semantically invalid. Every input
        // must return a verdict without indexing/overflow panics.
        for i in 0..1024 {
            let mut bad = object.clone();
            let at = (i * 73 + 19) % bad.len();
            bad[at] ^= 1 << (i % 8);
            let _ = check_aarch64_scalar_cell_elf(&c.module, &c.lir, &bad);
        }
    }
    assert_eq!(rejected, 82);
    println!(
        "CELL_ELF_MUTATIONS rejected={rejected} truncated={truncated} no_panic_mutations=2048"
    );
}

#[cfg(all(target_arch = "aarch64", target_os = "linux"))]
#[test]
fn gnu_assembled_callers_independently_check_decoder_words_and_relocations() {
    use sha2::{Digest, Sha256};
    use std::process::Command;
    let assembler = "/usr/bin/as";
    let version = Command::new(assembler).arg("--version").output().unwrap();
    assert!(version.status.success());
    println!(
        "CELL_GNU_AS {}",
        serde_json::json!({"path":assembler,"sha256":format!("{:x}",Sha256::digest(std::fs::read(assembler).unwrap())),"version":String::from_utf8(version.stdout).unwrap()})
    );
    let mut count = 0;
    for c in captures()
        .into_iter()
        .filter(|c| c.case.ends_with("O0") && !c.case.contains("_write-"))
    {
        let small = c.case.contains("f32");
        let fp = if small { "s" } else { "d" };
        let gpr = if small { "w" } else { "x" };
        let local = c.case.starts_with("local_cell");
        for inverted in [false, true] {
            if inverted && !local {
                continue;
            }
            let mut setup = String::new();
            if local {
                setup = format!(
                    "{} {gpr}0, #{}\n",
                    if inverted { "movn" } else { "movz" },
                    if inverted { 65535 } else { 0 }
                );
                if small {
                    setup.push_str("movk w0, #49580, lsl #16\n");
                } else {
                    if inverted {
                        setup.push_str("movk x0, #0, lsl #16\n");
                    }
                    setup.push_str("movk x0, #32768, lsl #32\nmovk x0, #49205, lsl #48\n");
                }
                setup.push_str(&format!("fmov {fp}1, {gpr}0\n"));
            }
            let name = &c.lir.name;
            let copy = if local { "" } else { "mov v0.16b, v1.16b\n" };
            let data = if local { 1 } else { 0 };
            let below = if small { 20 } else { 24 };
            let assembly = format!(
                ".text\n.balign 4\n.global {name}\n.type {name}, %function\n{name}:\nstp x20, x19, [sp, #-32]!\nstp x29, x30, [sp, #16]\nadd x29, sp, #16\nsub sp, sp, #16\n{setup}sub x19, x29, #{below}\nstr {fp}{data}, [x19]\nmov x0, x19\n{copy}bl c_change\nldr {fp}0, [x19]\nadd sp, sp, #16\nldp x29, x30, [sp, #16]\nldp x20, x19, [sp], #32\nret\n.size {name}, .-{name}\n"
            );
            let dir = tempfile::tempdir().unwrap();
            let source = dir.path().join("caller.s");
            let path = dir.path().join("caller.o");
            std::fs::write(&source, &assembly).unwrap();
            let result = Command::new(assembler)
                .arg("-o")
                .arg(&path)
                .arg(&source)
                .output()
                .unwrap();
            assert!(
                result.status.success(),
                "{}",
                String::from_utf8_lossy(&result.stderr)
            );
            let object = std::fs::read(path).unwrap();
            check_aarch64_scalar_cell_elf(&c.module, &c.lir, &object)
                .unwrap_or_else(|e| panic!("{} movn={inverted}: {e}", c.case));
            println!(
                "CELL_GNU_OBJECT {}",
                serde_json::json!({"case":c.case,"movn":inverted,"assembly":assembly,"object":object})
            );
            count += 1;
        }
    }
    assert_eq!(count, 6);
}
