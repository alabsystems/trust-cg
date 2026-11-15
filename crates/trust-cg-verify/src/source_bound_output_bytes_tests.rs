// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::super::tests::fixture;
use super::*;
use crate::ay_bridge::{AYConfig, generate_smt2_query_raw};
use crate::source_bound_frame::{diagnostic_output_memory_obligation, source_bound_frame};

fn words(paired: bool) -> Vec<u32> {
    let mut words = vec![0xa9bf_7bfd, 0x9100_03fd];
    if paired {
        words.extend([0xa900_0801, 0xa901_1003, 0xf900_1005]);
    } else {
        words.extend([
            0xf900_0001,
            0xf900_0402,
            0xf900_0803,
            0xf900_0c04,
            0xf900_1005,
        ]);
    }
    words.extend([0xa8c1_7bfd, 0xd65f_03c0]);
    words
}

fn bytes(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|word| word.to_le_bytes()).collect()
}

#[test]
fn output_bytes_match_the_complete_original_query_without_admission() {
    for paired in [false, true] {
        let (source, machine) = fixture(paired);
        let code = bytes(&words(paired));
        let checked = check_aarch64_output_bytes(&source, &code).unwrap();
        assert!(std::ptr::eq(checked.source(), &source));
        assert!(std::ptr::eq(checked.code(), code.as_slice()));
        let allocated = diagnostic_output_memory_obligation(&source, &machine).unwrap();
        let query = generate_smt2_query_raw(checked.obligation(), &AYConfig::default());
        assert_eq!(
            query,
            generate_smt2_query_raw(&allocated, &AYConfig::default())
        );
        // The exact byte count of the complete query. 3d1eb3c74 narrowed its
        // logic header from `(set-logic ALL)` to `(set-logic QF_ABV)` (+3); the
        // body is unchanged, and the equality above still binds both
        // constructions to the same bytes.
        assert_eq!(query.len(), 96337);
        assert!(source_bound_frame(&source, &machine).is_err());
        println!(
            "OUTPUT_BYTES_QUERY={}",
            serde_json::to_string(&query).unwrap()
        );
    }
}

#[test]
fn output_bytes_refuse_every_single_bit_change_in_the_original_streams() {
    for paired in [false, true] {
        let (source, _) = fixture(paired);
        let original = words(paired);
        for index in 0..original.len() {
            for bit in 0..32 {
                let mut changed = original.clone();
                changed[index] ^= 1 << bit;
                assert!(
                    check_aarch64_output_bytes(&source, &bytes(&changed)).is_err(),
                    "paired={paired} word={index} bit={bit}"
                );
            }
        }
    }
}

#[test]
fn output_bytes_refuse_missing_extra_reordered_and_trailing_effects() {
    let (source, _) = fixture(false);
    let original = words(false);
    for index in 0..original.len() {
        let mut changed = original.clone();
        changed.remove(index);
        assert!(check_aarch64_output_bytes(&source, &bytes(&changed)).is_err());
    }
    for instruction in [original[2], 0xd65f_03c0, 0x9400_0000, 0xf940_0001] {
        let mut changed = original.clone();
        changed.insert(3, instruction);
        assert!(check_aarch64_output_bytes(&source, &bytes(&changed)).is_err());
    }
    let mut changed = original.clone();
    changed.swap(2, 3);
    assert!(matches!(
        check_aarch64_output_bytes(&source, &bytes(&changed)),
        Err(OutputByteError::StoreMismatch)
    ));
    for count in 0..4 {
        assert!(check_aarch64_output_bytes(&source, &bytes(&original[..count])).is_err());
    }
    let mut changed = bytes(&original);
    changed.push(0);
    assert!(check_aarch64_output_bytes(&source, &changed).is_err());
    let mut changed = original;
    changed.insert(2, 0xd503_201f);
    assert!(check_aarch64_output_bytes(&source, &bytes(&changed)).is_ok());
    let mut limit = words(false);
    limit.splice(2..2, std::iter::repeat_n(0xd503_201f, 250));
    assert!(check_aarch64_output_bytes(&source, &bytes(&limit)).is_ok());
    limit.insert(2, 0xd503_201f);
    assert!(check_aarch64_output_bytes(&source, &bytes(&limit)).is_err());
}

#[test]
fn output_bytes_track_copies_addresses_literals_and_undefined_values() {
    let (source, _) = fixture(false);
    let mut copied = words(false);
    copied[2] = 0xf900_0009; // STR X9,[X0].
    copied.insert(2, 0xaa01_03e9); // MOV X9,X1.
    assert!(check_aarch64_output_bytes(&source, &bytes(&copied)).is_ok());
    copied[2] = 0xaa02_03e9;
    assert!(check_aarch64_output_bytes(&source, &bytes(&copied)).is_err());

    let mut addressed = words(false);
    addressed[3] = 0xf900_0122; // STR X2,[X9].
    addressed.insert(3, 0x9100_2009); // ADD X9,X0,#8.
    assert!(check_aarch64_output_bytes(&source, &bytes(&addressed)).is_ok());
    addressed[3] = 0x9100_4009;
    assert!(check_aarch64_output_bytes(&source, &bytes(&addressed)).is_err());

    let mut addressed = words(false);
    addressed[3] = 0xf900_0122;
    addressed.splice(3..3, [0xd280_0108, 0x8b08_0009]); // MOV X8,#8; ADD X9,X0,X8.
    assert!(check_aarch64_output_bytes(&source, &bytes(&addressed)).is_ok());
    addressed[3] = 0xf280_0108; // MOVK cannot read undefined X8.
    assert!(matches!(
        check_aarch64_output_bytes(&source, &bytes(&addressed)),
        Err(OutputByteError::BodyDomain)
    ));

    let mut literal_source = source;
    let block = literal_source
        .blocks
        .get_mut(&literal_source.entry_block)
        .unwrap();
    block.instructions[2].args[0] = trust_cg_lower::instructions::Value(6); // First address constant is zero.
    let mut literal = words(false);
    literal[2] = 0xf900_0008;
    literal.insert(2, 0xd280_0008); // MOVZ X8,#0.
    assert!(check_aarch64_output_bytes(&literal_source, &bytes(&literal)).is_ok());
    literal[2] = 0x9280_0008; // MOVN X8,#0 produces all ones.
    assert!(matches!(
        check_aarch64_output_bytes(&literal_source, &bytes(&literal)),
        Err(OutputByteError::StoreMismatch)
    ));
}

#[test]
fn output_bytes_preserve_every_literal_halfword() {
    use trust_cg_lower::instructions::{Instruction, Opcode, Value};
    let (mut source, _) = fixture(false);
    let block = source.blocks.get_mut(&source.entry_block).unwrap();
    block.instructions[2].args[0] = Value(100);
    block.instructions.insert(
        0,
        Instruction {
            opcode: Opcode::Iconst {
                ty: trust_cg_lower::Type::I64,
                imm: 0xfedc_ba98_7654_3210_u64 as i64,
            },
            args: vec![],
            results: vec![Value(100)],
        },
    );
    let mut literal = words(false);
    literal[2] = 0xf900_0008;
    // MOVZ X8,#0x3210; MOVK X8,#0x7654,LSL #16; then 0xba98/#32 and 0xfedc/#48.
    literal.splice(2..2, [0xd286_4208, 0xf2ae_ca88, 0xf2d7_5308, 0xf2ff_db88]);
    assert!(check_aarch64_output_bytes(&source, &bytes(&literal)).is_ok());
    for index in 2..6 {
        let mut wrong = literal.clone();
        wrong[index] ^= 1 << 5;
        assert!(matches!(
            check_aarch64_output_bytes(&source, &bytes(&wrong)),
            Err(OutputByteError::StoreMismatch)
        ));
    }
}

#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
#[test]
fn output_bytes_match_native_gnu_assembler_encoding() {
    use std::process::Command;
    // Removed when the test ends, passed or failed.
    let directory_scratch = tempfile::Builder::new()
        .prefix("tcg-output-byte-isa-")
        .tempdir()
        .unwrap();
    let directory = directory_scratch.path().to_path_buf();
    for tool in ["as", "objcopy"] {
        let output = Command::new(tool).arg("--version").output().unwrap();
        assert!(output.status.success());
        let version = String::from_utf8(output.stdout).unwrap();
        assert!(version.starts_with("GNU "), "{version}");
        std::fs::write(directory.join(format!("{tool}-version.log")), version).unwrap();
    }
    let cases = [
        (
            "scalar",
            "str x1,[x0]\nstr x2,[x0,#8]\nstr x3,[x0,#16]\nstr x4,[x0,#24]\nstr x5,[x0,#32]",
            words(false)[2..7].to_vec(),
        ),
        (
            "paired",
            "stp x1,x2,[x0]\nstp x3,x4,[x0,#16]\nstr x5,[x0,#32]",
            words(true)[2..5].to_vec(),
        ),
        (
            "copy",
            "mov x9,x1\nstr x9,[x0]",
            vec![0xaa01_03e9, 0xf900_0009],
        ),
        (
            "immediate",
            "add x9,x0,#8\nstr x2,[x9]",
            vec![0x9100_2009, 0xf900_0122],
        ),
        (
            "register",
            "movz x8,#8\nadd x9,x0,x8",
            vec![0xd280_0108, 0x8b08_0009],
        ),
        (
            "literal",
            "movz x8,#0x3210\nmovk x8,#0x7654,lsl #16\nmovk x8,#0xba98,lsl #32\nmovk x8,#0xfedc,lsl #48",
            vec![0xd286_4208, 0xf2ae_ca88, 0xf2d7_5308, 0xf2ff_db88],
        ),
        ("not", "movn x8,#0", vec![0x9280_0008]),
        ("nop", "nop", vec![0xd503_201f]),
        (
            "multiply-add-variants",
            "madd x12,x6,x9,x0\nmadd w12,w6,w9,w0\nmsub x12,x6,x9,x0\nsmaddl x12,w6,w9,x0\numaddl x12,w6,w9,x0\nmul x12,x6,x9",
            vec![
                0x9b09_00cc,
                0x1b09_00cc,
                0x9b09_80cc,
                0x9b29_00cc,
                0x9ba9_00cc,
                0x9b09_7ccc,
            ],
        ),
        (
            "actual-writer",
            "movz x6,#0\nmovz x9,#8\nmovz x10,#1\nmadd x12,x6,x9,x0\nmovz x6,#8\nmovz x7,#2\nmadd x13,x10,x6,x0\nmovz x6,#8\nmovz x10,#3\nmadd x14,x7,x6,x0\nmovz x6,#8\nmovz x7,#4\nmadd x9,x10,x6,x0\nmovz x6,#8\nstr x1,[x12]\nmadd x1,x7,x6,x0\nstr x2,[x13]\nstr x3,[x14]\nstr x4,[x9]\nstr x5,[x1]",
            include_bytes!("../tests/fixtures/output_memory_writer-frameless-O1.aarch64.bin")[..80]
                .as_chunks::<4>()
                .0
                .iter()
                .map(|b| u32::from_le_bytes(*b))
                .collect(),
        ),
    ];
    for (name, body, body_words) in cases {
        let assembly = directory.join(format!("{name}.s"));
        let object = directory.join(format!("{name}.o"));
        let binary = directory.join(format!("{name}.bin"));
        std::fs::write(
            &assembly,
            format!(
                ".text\nstp x29,x30,[sp,#-16]!\nmov x29,sp\n{body}\nldp x29,x30,[sp],#16\nret\n"
            ),
        )
        .unwrap();
        let assembled = Command::new("as")
            .arg("-o")
            .arg(&object)
            .arg(&assembly)
            .output()
            .unwrap();
        assert!(
            assembled.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&assembled.stderr)
        );
        let extracted = Command::new("objcopy")
            .args(["-O", "binary", "--only-section=.text"])
            .arg(&object)
            .arg(&binary)
            .output()
            .unwrap();
        assert!(
            extracted.status.success(),
            "{name}: {}",
            String::from_utf8_lossy(&extracted.stderr)
        );
        let mut expected = vec![0xa9bf_7bfd, 0x9100_03fd];
        expected.extend(body_words);
        expected.extend([0xa8c1_7bfd, 0xd65f_03c0]);
        assert_eq!(std::fs::read(binary).unwrap(), bytes(&expected), "{name}");
    }
    println!("OUTPUT_BYTES_ASSEMBLER_DIR={}", directory.display());
}

#[test]
fn output_bytes_frameless_whole_memory_and_frame_classification() {
    let (source, _) = fixture(false);
    let framed = words(false);
    let mut unframed = framed[2..framed.len() - 2].to_vec();
    unframed.push(0xd65f_03c0);
    let code = bytes(&unframed);
    let checked = check_aarch64_output_bytes(&source, &code).unwrap();
    assert_eq!(checked.frame(), Aarch64OutputFrame::Frameless);
    let query = generate_smt2_query_raw(checked.obligation(), &AYConfig::default());
    assert!(
        !query.contains("entry_sp") && !query.contains("entry_fp") && !query.contains("entry_lr")
    );
    assert!(query.contains("observe"));
    // Neither output alignment nor nonwrapping access is discharged by decoding.
    assert_eq!(checked.obligation().preconditions.len(), 2);
    for removed in [0, 1, framed.len() - 2] {
        let mut partial = framed.clone();
        partial.remove(removed);
        assert!(check_aarch64_output_bytes(&source, &bytes(&partial)).is_err());
    }
    for register in [18, 19, 29, 30, 31] {
        let mut forbidden = unframed.clone();
        forbidden[0] = (forbidden[0] & !(31 << 5)) | (register << 5);
        assert!(check_aarch64_output_bytes(&source, &bytes(&forbidden)).is_err());
    }
    let mut maximum = unframed;
    maximum.splice(0..0, std::iter::repeat_n(0xd503_201f, 250));
    assert!(check_aarch64_output_bytes(&source, &bytes(&maximum)).is_ok());
    maximum.insert(0, 0xd503_201f);
    assert!(check_aarch64_output_bytes(&source, &bytes(&maximum)).is_err());
}

#[test]
fn output_bytes_actual_writer_tracks_madd_and_reused_argument_register() {
    let (source, _) = fixture(false);
    // Extracted from the genuine Trust backend's qualified O1 ELF .text.
    let code = include_bytes!("../tests/fixtures/output_memory_writer-frameless-O1.aarch64.bin");
    let checked = check_aarch64_output_bytes(&source, code).unwrap();
    assert_eq!(checked.frame(), Aarch64OutputFrame::Frameless);
    let original: Vec<_> = code
        .as_chunks::<4>()
        .0
        .iter()
        .map(|b| u32::from_le_bytes(*b))
        .collect();
    let madds: Vec<_> = original
        .iter()
        .enumerate()
        .filter(|(_, word)| **word & 0xffe0_8000 == 0x9b00_0000)
        .map(|(i, _)| i)
        .collect();
    assert_eq!(madds.len(), 5);
    // The last MADD overwrites X1 only after its original argument was stored.
    assert_eq!(original[*madds.last().unwrap()] & 31, 1);
    let mut wrong_order = original.clone();
    let last = *madds.last().unwrap();
    wrong_order.swap(last - 1, last);
    assert!(matches!(
        check_aarch64_output_bytes(&source, &bytes(&wrong_order)),
        Err(OutputByteError::StoreMismatch)
    ));
    for index in madds {
        for replacement in [
            original[index] ^ (1 << 31),                  // W-width.
            original[index] ^ (1 << 15),                  // MSUB.
            original[index] ^ (1 << 21),                  // Widening multiply-add.
            (original[index] & !(31 << 10)) | (31 << 10), // MUL alias.
            (original[index] & !31) | 29,                 // FP destination.
            (original[index] & !(31 << 5)) | (16 << 5),   // Undefined factor.
            (original[index] & !(31 << 10)) | (1 << 10),  // Wrong base.
        ] {
            let mut changed = original.clone();
            changed[index] = replacement;
            assert!(
                check_aarch64_output_bytes(&source, &bytes(&changed)).is_err(),
                "word={index} replacement={replacement:08x}"
            );
        }
    }
    println!(
        "FRAMELESS_OUTPUT_QUERY={}",
        serde_json::to_string(&generate_smt2_query_raw(
            checked.obligation(),
            &AYConfig::default()
        ))
        .unwrap()
    );
}
