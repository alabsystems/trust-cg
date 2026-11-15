// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
#![cfg(all(target_arch = "aarch64", target_os = "linux"))]

use std::path::{Path, PathBuf};
use std::process::Command;
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_lower::Function;
use trust_cg_verify::source_bound_frame::{
    check_aarch64_scalar_cell_elf, check_aarch64_scalar_cell_link,
};

#[derive(Clone, serde::Deserialize)]
struct Capture {
    case: String,
    module: trust_ir::Module,
    lir: Function,
}
struct Fixture {
    capture: Capture,
    object: Vec<u8>,
    image: Vec<u8>,
    directory: PathBuf,
}
fn captures() -> Vec<Capture> {
    serde_json::from_str(include_str!("../src/source_bound_cell_sources.json")).unwrap()
}
fn run(tool: &str, args: &[&str], directory: &Path) {
    let result = Command::new(tool)
        .args(args)
        .current_dir(directory)
        .output()
        .unwrap_or_else(|e| panic!("required linker fixture tool {tool}: {e}"));
    assert!(
        result.status.success(),
        "{tool} {args:?}: {}",
        String::from_utf8_lossy(&result.stderr)
    );
}
fn fixture_directory() -> PathBuf {
    // Recorded in the fixture's evidence lines; removed at process exit.
    process_scratch::process_scoped("trust-cg-cell-link-")
}
fn emit(capture: &Capture) -> Vec<u8> {
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: match capture.case.rsplit_once('-').unwrap().1 {
            "O0" => OptLevel::O0,
            "O1" => OptLevel::O1,
            "O2" => OptLevel::O2,
            "O3" => OptLevel::O3,
            _ => unreachable!(),
        },
        verify: false,
        ..PipelineConfig::for_target("aarch64-unknown-linux-gnu")
    });
    let machine = pipeline
        .prepare_function_with_metrics_and_trust_ir_module(
            &capture.lir,
            None,
            &capture.module,
            &capture.module.functions[0],
        )
        .unwrap()
        .0;
    pipeline.compile_module(&[machine]).unwrap()
}
fn fixture(capture: Capture, callback_first: bool) -> Fixture {
    let directory = fixture_directory();
    let object = emit(&capture);
    let checked = check_aarch64_scalar_cell_elf(&capture.module, &capture.lir, &object).unwrap();
    let register = if checked.source().cell_width() == 4 {
        "s0"
    } else {
        "d0"
    };
    let mut assembly = ".text\n.p2align 2\n".to_owned();
    let mut names = Vec::new();
    for reloc in checked.relocations() {
        if names.contains(&reloc.symbol) {
            continue;
        }
        assert!(
            reloc
                .symbol
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'_')
        );
        names.push(reloc.symbol);
        assembly += &format!(
            ".global {0}\n.type {0},%function\n{0}:\nstr {register},[x0]\nret\n.size {0},.-{0}\n",
            reloc.symbol
        );
    }
    assembly += ".global unused_cell_decoy\n.type unused_cell_decoy,%function\nunused_cell_decoy:\nret\n.size unused_cell_decoy,.-unused_cell_decoy\n.section .note.GNU-stack,\"\",%progbits\n";
    std::fs::write(directory.join("caller.o"), &object).unwrap();
    std::fs::write(directory.join("callback.s"), assembly).unwrap();
    run("as", &["-o", "callback.o", "callback.s"], &directory);
    let inputs = if callback_first {
        ["callback.o", "caller.o"]
    } else {
        ["caller.o", "callback.o"]
    };
    run(
        "ld.lld",
        &[
            "-m",
            "aarch64elf",
            "--no-relax",
            "--build-id=none",
            "-e",
            &capture.lir.name,
            "-o",
            "linked.elf",
            inputs[0],
            inputs[1],
        ],
        &directory,
    );
    let image = std::fs::read(directory.join("linked.elf")).unwrap();
    Fixture {
        capture,
        object,
        image,
        directory,
    }
}
fn field(bytes: &[u8], offset: usize, width: usize) -> u64 {
    bytes[offset..offset + width]
        .iter()
        .enumerate()
        .fold(0, |v, (i, b)| v | (u64::from(*b) << (8 * i)))
}
fn put(bytes: &mut [u8], offset: usize, width: usize, value: u64) {
    bytes[offset..offset + width].copy_from_slice(&value.to_le_bytes()[..width]);
}
fn section(image: &[u8], kind: u64) -> usize {
    let start = field(image, 40, 8) as usize;
    (0..field(image, 60, 2) as usize)
        .map(|i| start + 64 * i)
        .find(|&h| field(image, h + 4, 4) == kind)
        .unwrap()
}
fn symbol(image: &[u8], name: &str) -> usize {
    let table = section(image, 2);
    let sh = field(image, 40, 8) as usize + 64 * field(image, table + 40, 4) as usize;
    let names = field(image, sh + 24, 8) as usize;
    let start = field(image, table + 24, 8) as usize;
    (0..field(image, table + 32, 8) as usize / 24)
        .map(|i| start + i * 24)
        .find(|&s| {
            let p = names + field(image, s, 4) as usize;
            image[p..].split(|b| *b == 0).next() == Some(name.as_bytes())
        })
        .unwrap()
}
fn file_offset(image: &[u8], name: &str) -> usize {
    let s = symbol(image, name);
    let h = field(image, 40, 8) as usize + 64 * field(image, s + 6, 2) as usize;
    (field(image, h + 24, 8) + field(image, s + 8, 8) - field(image, h + 16, 8)) as usize
}
fn refuse(f: &Fixture, image: &[u8], label: &str) {
    let checked =
        check_aarch64_scalar_cell_elf(&f.capture.module, &f.capture.lir, &f.object).unwrap();
    assert!(
        check_aarch64_scalar_cell_link(&checked, image).is_err(),
        "{} accepted {label}",
        f.capture.case
    );
}
fn controls() -> Vec<Fixture> {
    captures()
        .into_iter()
        .filter(|c| {
            c.case.contains("aliased_f") && c.case.contains("_read-") && c.case.ends_with("-O0")
        })
        .enumerate()
        .map(|(i, c)| fixture(c, i % 2 == 0))
        .collect()
}

#[test]
fn real_linker_images_bind_every_original_caller_and_callback_body() {
    let mut positive = 0;
    let mut negative = 0;
    let cases = captures();
    assert_eq!(cases.len(), 24);
    for (i, c) in cases.into_iter().enumerate() {
        let f = fixture(c, i % 2 == 0);
        let object =
            check_aarch64_scalar_cell_elf(&f.capture.module, &f.capture.lir, &f.object).unwrap();
        let linked = check_aarch64_scalar_cell_link(&object, &f.image)
            .unwrap_or_else(|e| panic!("{}: {e}", f.capture.case));
        assert!(std::ptr::eq(linked.object(), &object));
        assert!(std::ptr::eq(linked.image(), f.image.as_slice()));
        assert_eq!(linked.code().len(), object.code().len());
        assert_eq!(linked.callbacks().len(), 1);
        let callback = &linked.callbacks()[0];
        assert_eq!(callback.name(), object.relocations()[0].symbol);
        assert_eq!(callback.code().len(), 8);
        assert_eq!(&callback.code()[4..], &0xd65f_03c0u32.to_le_bytes());
        if callback.address() < linked.address() {
            negative += 1;
        } else {
            positive += 1;
        }
        println!(
            "CELL_LINK {}",
            serde_json::json!({"case":f.capture.case,"directory":f.directory,"caller":linked.address(),"callback":callback.address(),"callback_name":callback.name(),"image_bytes":f.image.len()})
        );
    }
    assert_eq!((positive, negative), (12, 12));
}

#[test]
fn every_linked_caller_word_and_call_destination_is_checked() {
    let cases = controls();
    assert_eq!(cases.len(), 2);
    let mut words = 0;
    for f in cases {
        let object =
            check_aarch64_scalar_cell_elf(&f.capture.module, &f.capture.lir, &f.object).unwrap();
        check_aarch64_scalar_cell_link(&object, &f.image).unwrap();
        let start = file_offset(&f.image, &f.capture.lir.name);
        for offset in (0..object.code().len()).step_by(4) {
            let mut bad = f.image.clone();
            put(&mut bad, start + offset, 4, 0xd420_0000);
            refuse(&f, &bad, "replaced instruction");
            words += 1;
        }
        for reloc in object.relocations() {
            let location = start + reloc.offset as usize;
            let word = field(&f.image, location, 4);
            for wrong in [(word & 0x03ff_ffff) | 0x1400_0000, word ^ 1, 0x9400_0000] {
                let mut bad = f.image.clone();
                put(&mut bad, location, 4, wrong);
                refuse(&f, &bad, "wrong branch kind or destination");
            }
        }
    }
    assert!(words >= 24);
    println!("CELL_LINK_WORD_CONTROLS {words}");
}

#[test]
fn load_mapping_symbol_and_dynamic_link_mutations_are_rejected() {
    let cases = controls();
    assert_eq!(cases.len(), 2);
    let mut count = 0;
    for f in cases {
        let object =
            check_aarch64_scalar_cell_elf(&f.capture.module, &f.capture.lir, &f.object).unwrap();
        check_aarch64_scalar_cell_link(&object, &f.image).unwrap();
        let caller = symbol(&f.image, &f.capture.lir.name);
        let callback = symbol(&f.image, object.relocations()[0].symbol);
        let decoy = symbol(&f.image, "unused_cell_decoy");
        let ph = field(&f.image, 32, 8) as usize;
        let load = (0..field(&f.image, 56, 2) as usize)
            .map(|i| ph + 56 * i)
            .find(|&h| field(&f.image, h, 4) == 1 && field(&f.image, h + 4, 4) == 5)
            .unwrap();
        let text = field(&f.image, 40, 8) as usize + 64 * field(&f.image, caller + 6, 2) as usize;
        let mutations = vec![
            (16, 2, 3),
            (ph, 4, 2),
            (load + 4, 4, 7),
            (load + 8, 8, field(&f.image, load + 8, 8) + 4),
            (load + 16, 8, field(&f.image, load + 16, 8) + 4),
            (load + 32, 8, 0),
            (load + 40, 8, 1),
            (load + 48, 8, 4096),
            (text + 16, 8, field(&f.image, text + 16, 8) + 4),
            (text + 8, 8, 7),
            (caller + 8, 8, field(&f.image, caller + 8, 8) + 4),
            (caller + 16, 8, 4),
            (callback + 8, 8, field(&f.image, callback + 8, 8) + 4),
            (callback + 4, 1, 0x22),
            (callback + 4, 1, 0x1a),
            (callback + 5, 1, 0x80),
            (callback + 6, 2, 0),
            (decoy, 4, field(&f.image, callback, 4)),
            (40, 8, u64::MAX),
            (56, 2, 129),
            (60, 2, 4097),
        ];
        for (offset, width, value) in mutations {
            let mut bad = f.image.clone();
            put(&mut bad, offset, width, value);
            refuse(&f, &bad, &format!("metadata {offset}/{width}/{value}"));
            count += 1;
        }
        // A non-code section cannot hide an unhandled relocation/dynamic table.
        // LLD's nonempty .comment gives an unrelated section to mutate without
        // making the caller or symbol mapping fail for an incidental reason.
        let sh = field(&f.image, 40, 8) as usize;
        let comment = (0..field(&f.image, 60, 2) as usize)
            .map(|i| sh + 64 * i)
            .find(|&h| {
                field(&f.image, h + 4, 4) == 1
                    && field(&f.image, h + 8, 8) & 2 == 0
                    && field(&f.image, h + 32, 8) != 0
            })
            .unwrap();
        for kind in [4, 6, 9, 11, 19, 0x6000_0001] {
            let mut bad = f.image.clone();
            put(&mut bad, comment + 4, 4, kind);
            refuse(&f, &bad, &format!("residual table section kind {kind}"));
            count += 1;
        }
        let mut duplicate = f.image.clone();
        duplicate[ph..ph + 56].copy_from_slice(&f.image[load..load + 56]);
        refuse(&f, &duplicate, "overlapping LOAD");
        count += 1;
        for end in [0, 7, 63, f.image.len() / 2, f.image.len() - 1] {
            refuse(&f, &f.image[..end], "truncated image");
            count += 1;
        }
    }
    assert_eq!(count, 66);
    println!("CELL_LINK_METADATA_CONTROLS {count}");
}

#[test]
fn corrupt_images_remain_bounded_and_never_panic() {
    let f = controls().remove(0);
    let object =
        check_aarch64_scalar_cell_elf(&f.capture.module, &f.capture.lir, &f.object).unwrap();
    let mut state = 0x1234_5678_9abc_def0u64;
    for _ in 0..1024 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let mut bad = f.image.clone();
        let offset = state as usize % bad.len();
        bad[offset] ^= ((state >> 32) as u8) | 1;
        let _ = check_aarch64_scalar_cell_link(&object, &bad);
    }
}

// Synthetic extensions of the original source captures, not new frontend captures.
fn chained(mut c: Capture, count: usize, distinct: bool) -> Capture {
    use trust_cg_lower::instructions::{Opcode as L, Value};
    for occurrence in 1..count {
        let value = 42 + occurrence as u32;
        let mut load = c.module.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .find(|n| matches!(n.inst, trust_ir::Inst::Load { .. }))
            .unwrap()
            .clone();
        let mut call = c.module.functions[0].blocks[0]
            .body
            .iter()
            .find(|n| matches!(n.inst, trust_ir::Inst::Call { .. }))
            .unwrap()
            .clone();
        load.results = vec![trust_ir::ValueId::new(value)];
        let trust_ir::Inst::Call { callee, args } = &mut call.inst else {
            unreachable!()
        };
        args[1] = trust_ir::ValueId::new(value);
        if distinct {
            let mut declaration = c.module.functions[1].clone();
            declaration.id = trust_ir::FuncId::new((occurrence + 1) as u32);
            declaration.name = format!("cell_change_{occurrence}");
            *callee = declaration.id;
            c.module.functions.push(declaration);
        }
        let body = &mut c.module.functions[0].blocks[0].body;
        let at = body.len() - 1;
        body.splice(at..at, [load, call]);
        let mut load = c
            .lir
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .find(|i| matches!(i.opcode, L::Load { .. }))
            .unwrap()
            .clone();
        let mut call = c.lir.blocks[&c.lir.entry_block]
            .instructions
            .iter()
            .find(|i| matches!(i.opcode, L::Call { .. }))
            .unwrap()
            .clone();
        load.results = vec![Value(value)];
        call.args[1] = Value(value);
        if distinct {
            let L::Call { name, .. } = &mut call.opcode else {
                unreachable!()
            };
            *name = format!("cell_change_{occurrence}");
        }
        let body = &mut c
            .lir
            .blocks
            .get_mut(&c.lir.entry_block)
            .unwrap()
            .instructions;
        let at = body.len() - 1;
        body.splice(at..at, [load, call]);
    }

    assert!(trust_ir_build::validate_module(&c.module).is_empty());
    c
}

#[test]
fn ordered_repeated_and_distinct_callbacks_bind_every_linked_call() {
    let mut cases = 0;
    let mut controls = 0;
    for original in captures().into_iter().filter(|c| {
        c.case.starts_with("aliased_f")
            && c.case.contains("_read-")
            && (c.case.ends_with("O0") || c.case.ends_with("O3"))
    }) {
        for count in [2, 16] {
            for distinct in [false, true] {
                let f = fixture(chained(original.clone(), count, distinct), cases % 2 == 0);
                let object =
                    check_aarch64_scalar_cell_elf(&f.capture.module, &f.capture.lir, &f.object)
                        .unwrap();
                let linked = check_aarch64_scalar_cell_link(&object, &f.image).unwrap();
                assert_eq!(object.relocations().len(), count);
                assert_eq!(linked.callbacks().len(), if distinct { count } else { 1 });
                let start = file_offset(&f.image, &f.capture.lir.name);
                let decoy = field(&f.image, symbol(&f.image, "unused_cell_decoy") + 8, 8);
                for reloc in object.relocations() {
                    let wrong_target = if distinct {
                        linked
                            .callbacks()
                            .iter()
                            .find(|c| c.name() != reloc.symbol)
                            .unwrap()
                            .address()
                    } else {
                        decoy
                    };
                    let pc = linked.address() + reloc.offset;
                    let delta = i64::try_from(i128::from(wrong_target) - i128::from(pc)).unwrap();
                    assert_eq!(delta % 4, 0);
                    assert!((-(1 << 27)..(1 << 27)).contains(&delta));
                    let word = 0x9400_0000 | ((delta / 4) as u32 & 0x03ff_ffff);
                    let mut bad = f.image.clone();
                    put(&mut bad, start + reloc.offset as usize, 4, u64::from(word));
                    refuse(&f, &bad, "call to wrong valid callback or decoy");
                    controls += 1;
                }
                println!(
                    "CELL_LINK_CHAIN {}",
                    serde_json::json!({"case":f.capture.case,"calls":count,"distinct":distinct,"directory":f.directory})
                );
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 16);
    assert_eq!(controls, 144);
    println!("CELL_LINK_CHAIN_CONTROLS {controls}");
}

fn pie_fixture(capture: Capture) -> Fixture {
    let directory = fixture_directory();
    let object = emit(&capture);
    let driver = match capture.lir.name.as_str() {
        "aliased_f32_read" => include_str!("fixtures/scalar_cell_drivers/aliased_f32_read.c"),
        "aliased_f32_write" => include_str!("fixtures/scalar_cell_drivers/aliased_f32_write.c"),
        "aliased_f64_read" => include_str!("fixtures/scalar_cell_drivers/aliased_f64_read.c"),
        "aliased_f64_write" => include_str!("fixtures/scalar_cell_drivers/aliased_f64_write.c"),
        "local_cell_read" => include_str!("fixtures/scalar_cell_drivers/local_cell_read.c"),
        "local_cell_read_f32" => include_str!("fixtures/scalar_cell_drivers/local_cell_read_f32.c"),
        _ => unreachable!(),
    };
    std::fs::write(directory.join("caller.o"), &object).unwrap();
    std::fs::write(directory.join("driver.c"), driver).unwrap();
    run(
        "cc",
        &[
            "-O0",
            "-fPIE",
            "-pie",
            "-Wl,-z,now",
            "-Wl,-z,noexecstack",
            "-Wl,--build-id=none",
            "-o",
            "linked.elf",
            "driver.c",
            "caller.o",
        ],
        &directory,
    );
    let image = std::fs::read(directory.join("linked.elf")).unwrap();
    Fixture {
        capture,
        object,
        image,
        directory,
    }
}

#[test]
fn real_abi_callback_pies_bind_and_execute_all_original_callers() {
    let cases = captures();
    assert_eq!(cases.len(), 24);
    for c in cases {
        let f = pie_fixture(c);
        let object =
            check_aarch64_scalar_cell_elf(&f.capture.module, &f.capture.lir, &f.object).unwrap();
        let linked = check_aarch64_scalar_cell_link(&object, &f.image)
            .unwrap_or_else(|e| panic!("{}: {e}", f.capture.case));
        assert!(linked.is_position_independent());
        assert_eq!(linked.callbacks().len(), 1);
        assert_eq!(linked.callbacks()[0].name(), "c_change");
        assert!(linked.callbacks()[0].code().len() > 8);
        let result = Command::new(f.directory.join("linked.elf"))
            .output()
            .unwrap();
        let expected = format!(
            "PASS scalar_cell family={} calls=17 checks=238",
            f.capture.lir.name
        );
        std::fs::write(f.directory.join("native.stdout"), &result.stdout).unwrap();
        std::fs::write(f.directory.join("native.stderr"), &result.stderr).unwrap();
        assert!(
            result.status.success(),
            "{}: {:?} {}",
            f.capture.case,
            result.status,
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&result.stdout).trim(), expected);
        println!(
            "CELL_PIE {}",
            serde_json::json!({"case":f.capture.case,"directory":f.directory,"calls":17,"checks":238,"caller_address":linked.address(),"callback_address":linked.callbacks()[0].address(),"callback_bytes":linked.callbacks()[0].code().len()})
        );
    }
}

fn dynamic_tag(image: &[u8], tag: u64) -> usize {
    let h = section(image, 6);
    let start = field(image, h + 24, 8) as usize;
    (0..field(image, h + 32, 8) as usize / 16)
        .map(|i| start + i * 16)
        .find(|&p| field(image, p, 8) == tag)
        .unwrap()
}

#[test]
fn pie_loader_metadata_and_relocation_write_mutations_are_rejected() {
    let mut count = 0;
    for capture in captures().into_iter().filter(|c| {
        c.case.contains("aliased_f") && c.case.contains("_read-") && c.case.ends_with("O0")
    }) {
        let f = pie_fixture(capture);
        let object =
            check_aarch64_scalar_cell_elf(&f.capture.module, &f.capture.lir, &f.object).unwrap();
        let linked = check_aarch64_scalar_cell_link(&object, &f.image).unwrap();
        let rela = section(&f.image, 4);
        let table = field(&f.image, rela + 24, 8) as usize;
        let dynamic = section(&f.image, 6);
        let dyn_offset = field(&f.image, dynamic + 24, 8);
        let dyn_address = field(&f.image, dynamic + 16, 8);
        let jmprel = dynamic_tag(&f.image, 23);
        let got = field(&f.image, dynamic_tag(&f.image, 3) + 8, 8);
        let symbols = section(&f.image, 11);
        let sym_data = field(&f.image, symbols + 24, 8) as usize;
        let ph = field(&f.image, 32, 8) as usize;
        let header = |kind| {
            (0..field(&f.image, 56, 2) as usize)
                .map(|i| ph + i * 56)
                .find(|&h| field(&f.image, h, 4) == kind)
                .unwrap()
        };
        let dynamic_header = header(2);
        let interp = field(&f.image, header(3) + 8, 8) as usize;
        let mutations = [
            (table, 8, linked.address()),
            (table, 8, linked.callbacks()[0].address()),
            (table, 8, dyn_address + jmprel as u64 - dyn_offset + 8),
            (table, 8, got + 8),
            (table + 8, 8, 1024),
            (table + 8, 8, 1032),
            (table + 8, 8, (u64::from(u32::MAX) << 32) | 1025),
            (dynamic_tag(&f.image, 7) + 8, 8, linked.address()),
            (
                dynamic_tag(&f.image, 8) + 8,
                8,
                field(&f.image, rela + 32, 8) + 24,
            ),
            (jmprel + 8, 8, linked.address()),
            (dynamic_tag(&f.image, 20) + 8, 8, 17),
            (dynamic_tag(&f.image, 30) + 8, 8, 12),
            (dynamic_tag(&f.image, 0x6fff_fffb) + 8, 8, 1),
            (dynamic_tag(&f.image, 0) + 16, 8, 1),
            (dynamic_tag(&f.image, 12), 8, 8),
            (dynamic_tag(&f.image, 12), 8, 22),
            (dynamic_tag(&f.image, 12), 8, 0x7000_0000),
            (dynamic_header + 8, 8, dyn_offset + 16),
            (sym_data + 4, 1, 1),
            (interp, 1, u64::from(b'X')),
            (16, 2, 2),
            (table + 24, 8, field(&f.image, table, 8)),
            (sym_data + 24 + 4, 1, 0x1a),
            (table, 8, u64::MAX - 7),
            (dynamic_header + 32, 8, 16 * 4097),
            (
                dynamic_tag(&f.image, 0x6fff_fff9) + 8,
                8,
                field(&f.image, rela + 32, 8) / 24 + 1,
            ),
        ];
        for (offset, width, value) in mutations {
            let mut bad = f.image.clone();
            put(&mut bad, offset, width, value);
            refuse(&f, &bad, &format!("PIE metadata {offset}/{width}/{value}"));
            count += 1;
        }
    }
    assert_eq!(count, 52);
    println!("CELL_PIE_METADATA_CONTROLS {count}");
}

#[path = "support/process_scratch.rs"]
mod process_scratch;
