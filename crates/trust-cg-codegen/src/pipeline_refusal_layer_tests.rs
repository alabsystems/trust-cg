// trust-cg-codegen/pipeline_refusal_layer_tests.rs - every retyped AArch64
// pipeline refusal is raised with its layer's variant
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Trust-core architecture AD-8 / E0.3. The rustc bridge classifies a
//! [`PipelineError`] by VARIANT alone (`classify_compile_error` has no default
//! arm), and its own tests pin each variant's layer code. That is only honest if
//! every refusal is raised with the variant of the layer that refuses, so each
//! raise site this change retyped (from `ISel` / `Encoding` /
//! `MalformedAarch64Function` / `TargetObjectUnsupported`) is driven here by a
//! real input and its variant asserted, together with the site's own message so
//! the test cannot pass on a different refusal.
//!
//! Variant -> code, as the bridge files them: `ObjectEmission` ->
//! `TCG-OBJECT-EMIT`; `Unwind` / `MalformedAarch64Eh` -> `TCG-EH-UNWIND`;
//! `ModuleIo` / `WorkerPool` -> `TCG-COMPILE-DRIVER`; `DwarfEmit` ->
//! `TCG-DEBUG-INFO`; `FrameLowering(LowerError::FrameLowering)` ->
//! `TCG-REGALLOC-063`; `AotProfile` -> `TCG-REGALLOC-063`.

use super::*;

fn module_io_message(err: PipelineError) -> String {
    match err {
        PipelineError::ModuleIo(message) => message,
        other => panic!("expected PipelineError::ModuleIo, got {other:?}"),
    }
}

fn object_emission_message(err: PipelineError) -> String {
    match err {
        PipelineError::ObjectEmission(message) => message,
        other => panic!("expected PipelineError::ObjectEmission, got {other:?}"),
    }
}

fn unwind_message(err: PipelineError) -> String {
    match err {
        PipelineError::Unwind(message) => message,
        other => panic!("expected PipelineError::Unwind, got {other:?}"),
    }
}

fn malformed_eh_detail(err: PipelineError) -> (String, String) {
    match err {
        PipelineError::MalformedAarch64Eh { function, detail } => (function, detail),
        other => panic!("expected PipelineError::MalformedAarch64Eh, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// trust-ir module I/O -> ModuleIo (TCG-COMPILE-DRIVER)
// ---------------------------------------------------------------------------

fn missing_path(dir: &tempfile::TempDir, file_name: &str) -> std::path::PathBuf {
    let path = dir.path().join(file_name);
    assert!(!path.exists());
    path
}

fn write_file(dir: &tempfile::TempDir, file_name: &str, bytes: &[u8]) -> std::path::PathBuf {
    let path = dir.path().join(file_name);
    std::fs::write(&path, bytes).expect("write fixture");
    path
}

#[test]
fn load_module_as_tmbc_read_failure_is_module_io() {
    let dir = tempfile::tempdir().expect("tempdir");
    let message = module_io_message(
        load_module_as(&missing_path(&dir, "absent.bin"), FormatMode::Tmbc).unwrap_err(),
    );
    assert!(message.contains("I/O error"), "{message}");
}

#[test]
fn load_module_as_tmbc_magic_mismatch_is_module_io() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = write_file(&dir, "not-tmbc.bin", b"{\"not\": \"tmbc\"}");
    let message = module_io_message(load_module_as(&path, FormatMode::Tmbc).unwrap_err());
    assert!(
        message.contains("is neither a TRUST_IR module nor a tMBC envelope"),
        "{message}"
    );
}

#[test]
fn load_module_as_json_read_failure_is_module_io() {
    let dir = tempfile::tempdir().expect("tempdir");
    let message = module_io_message(
        load_module_as(&missing_path(&dir, "absent.bin"), FormatMode::Json).unwrap_err(),
    );
    assert!(message.contains("I/O error"), "{message}");
}

#[test]
fn load_module_as_json_parse_failure_is_module_io() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = write_file(&dir, "broken.bin", b"{ not json");
    let message = module_io_message(load_module_as(&path, FormatMode::Json).unwrap_err());
    assert!(message.starts_with("JSON error: "), "{message}");
}

#[test]
fn load_module_as_text_read_failure_is_module_io() {
    let dir = tempfile::tempdir().expect("tempdir");
    let message = module_io_message(
        load_module_as(&missing_path(&dir, "absent.bin"), FormatMode::Text).unwrap_err(),
    );
    assert!(message.contains("I/O error"), "{message}");
}

#[test]
fn load_module_as_auto_json_read_failure_is_module_io() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = missing_path(&dir, "absent.json");
    assert!(matches!(detect_input_format(&path), InputFormat::Json));
    let message = module_io_message(load_module_as(&path, FormatMode::Auto).unwrap_err());
    assert!(message.contains("I/O error"), "{message}");
}

#[test]
fn load_module_as_auto_json_parse_failure_is_module_io() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = write_file(&dir, "broken.json", b"{ not json");
    let message = module_io_message(load_module_as(&path, FormatMode::Auto).unwrap_err());
    assert!(message.starts_with("JSON error: "), "{message}");
}

#[test]
fn load_module_as_auto_tmbc_read_failure_is_module_io() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = missing_path(&dir, "absent.tmbc");
    assert!(matches!(detect_input_format(&path), InputFormat::Tmbc));
    let message = module_io_message(load_module_as(&path, FormatMode::Auto).unwrap_err());
    assert!(message.contains("I/O error"), "{message}");
}

#[test]
fn load_module_as_auto_trust_ir_read_failure_is_module_io() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = missing_path(&dir, "absent.trust_ir");
    assert!(matches!(detect_input_format(&path), InputFormat::TrustIr));
    let message = module_io_message(load_module_as(&path, FormatMode::Auto).unwrap_err());
    assert!(message.contains("I/O error"), "{message}");
}

#[test]
fn load_module_from_bytes_utf8_failure_is_module_io() {
    let message = module_io_message(load_module_from_bytes(&[0xff, 0xfe, 0xfd]).unwrap_err());
    assert!(message.contains("invalid utf-8"), "{message}");
}

#[test]
fn load_module_from_bytes_json_failure_is_module_io() {
    let message = module_io_message(load_module_from_bytes(b"{ not json").unwrap_err());
    assert!(message.starts_with("JSON error: "), "{message}");
}

#[test]
fn parse_trust_ir_text_failure_is_module_io() {
    let message = module_io_message(parse_trust_ir_text("module \"m\"\nfn @f( -> {").unwrap_err());
    assert!(message.starts_with(".trust_ir parse error: "), "{message}");
}

#[test]
fn save_module_to_trust_ir_text_write_failure_is_module_io() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("no-such-dir").join("m.trust_ir");
    let message = module_io_message(
        save_module_to_trust_ir_text(&trust_ir::Module::new("m"), &path).unwrap_err(),
    );
    assert!(
        message.starts_with("failed to write .trust_ir text file"),
        "{message}"
    );
}

#[test]
fn save_module_to_tmbc_write_failure_is_module_io() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("no-such-dir").join("m.tmbc");
    let message =
        module_io_message(save_module_to_tmbc(&trust_ir::Module::new("m"), &path).unwrap_err());
    assert!(
        message.starts_with("failed to write tMBC file"),
        "{message}"
    );
}

#[test]
fn decode_tmbc_short_buffer_is_module_io() {
    let message = module_io_message(decode_tmbc(&[0u8; 3]).unwrap_err());
    assert!(
        message.starts_with("invalid tMBC data: expected at least 8 bytes"),
        "{message}"
    );
}

#[test]
fn decode_tmbc_bad_magic_is_module_io() {
    let message = module_io_message(decode_tmbc(b"XXXX\x01\x00\x00\x00").unwrap_err());
    assert!(message.starts_with("invalid tMBC magic"), "{message}");
}

#[test]
fn decode_tmbc_bad_version_is_module_io() {
    let mut bytes = TMBC_MAGIC.to_vec();
    bytes.extend_from_slice(&(TMBC_VERSION.wrapping_add(1)).to_le_bytes());
    let message = module_io_message(decode_tmbc(&bytes).unwrap_err());
    assert!(message.starts_with("unsupported tMBC version"), "{message}");
}

#[test]
fn decode_tmbc_bad_payload_is_module_io() {
    let mut bytes = TMBC_MAGIC.to_vec();
    bytes.extend_from_slice(&TMBC_VERSION.to_le_bytes());
    bytes.extend_from_slice(b"not a trust_ir payload");
    let message = module_io_message(decode_tmbc(&bytes).unwrap_err());
    assert!(
        message.starts_with("failed to deserialize tMBC payload"),
        "{message}"
    );
}

// ---------------------------------------------------------------------------
// Object writer -> ObjectEmission (TCG-OBJECT-EMIT)
// ---------------------------------------------------------------------------

#[test]
fn pad_text_on_a_partial_word_is_object_emission() {
    let mut combined = vec![0u8; 3];
    let message = object_emission_message(
        pad_aarch64_text_for_function_alignment(&mut combined, "f", 4).unwrap_err(),
    );
    assert!(
        message.contains("is not word-aligned before placing `f`"),
        "{message}"
    );
}

fn object_global(name: &str) -> ObjectGlobal {
    ObjectGlobal {
        name: name.to_string(),
        data: vec![0; 8],
        mutable: true,
        is_external: true,
        symbol_refs: Vec::new(),
        is_thread_local: false,
        is_import: false,
        is_weak: false,
        align: 8,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        comdat: false,
        section: None,
    }
}

fn globals_refusal(globals: &[ObjectGlobal]) -> String {
    object_emission_message(validate_aarch64_object_globals(globals).unwrap_err())
}

#[test]
fn object_global_refusals_are_object_emission() {
    // Empty symbol name.
    let message = globals_refusal(&[object_global("")]);
    assert!(message.contains("has an empty symbol name"), "{message}");

    // Duplicate symbol.
    let message = globals_refusal(&[object_global("G"), object_global("G")]);
    assert!(
        message.contains("contains duplicate global symbol `G`"),
        "{message}"
    );

    // Invalid alignment.
    let mut global = object_global("G");
    global.align = 3;
    let message = globals_refusal(&[global]);
    assert!(message.contains("has invalid alignment 3"), "{message}");

    // Import carrying bytes.
    let mut global = object_global("G");
    global.is_import = true;
    let message = globals_refusal(&[global]);
    assert!(
        message.contains("is an import but carries local bytes"),
        "{message}"
    );

    // Weak without an external definition.
    let mut global = object_global("G");
    global.is_weak = true;
    global.is_external = false;
    let message = globals_refusal(&[global]);
    assert!(message.contains("has invalid weak linkage"), "{message}");

    // Import with a visibility.
    let mut global = object_global("G");
    global.is_import = true;
    global.data.clear();
    global.visibility = trust_ir::Visibility::Hidden;
    let message = globals_refusal(&[global]);
    assert!(
        message.contains("is an import with visibility"),
        "{message}"
    );

    // Import marked retained: refused off ELF (Mach-O, the JIT data image),
    // where llc's Mach-O writer would give it an `N_NO_DEAD_STRIP` undefined
    // symbol; the ELF emitters admit it and write nothing for the flag.
    let mut global = object_global("G");
    global.is_import = true;
    global.data.clear();
    global.retained = true;
    crate::pipeline::validate_aarch64_object_globals_with(std::slice::from_ref(&global), true)
        .expect("the ELF emitters admit a retained import");
    let message = globals_refusal(&[global]);
    assert!(
        message.contains("is an import marked retained") && message.contains("N_NO_DEAD_STRIP"),
        "{message}"
    );

    // Pointer slot with an empty target.
    let mut global = object_global("G");
    global.symbol_refs.push(GlobalSymbolRef {
        offset: 0,
        symbol: String::new(),
        addend: 0,
    });
    let message = globals_refusal(&[global]);
    assert!(
        message.contains("has a pointer slot with an empty target symbol"),
        "{message}"
    );

    // Duplicate pointer slots.
    let mut global = object_global("G");
    for _ in 0..2 {
        global.symbol_refs.push(GlobalSymbolRef {
            offset: 0,
            symbol: "T".to_string(),
            addend: 0,
        });
    }
    let message = globals_refusal(&[global]);
    assert!(
        message.contains("has duplicate pointer relocations at byte offset 0"),
        "{message}"
    );

    // Pointer slot offset overflow.
    let mut global = object_global("G");
    global.symbol_refs.push(GlobalSymbolRef {
        offset: u64::MAX - 3,
        symbol: "T".to_string(),
        addend: 0,
    });
    let message = globals_refusal(&[global]);
    assert!(message.contains("pointer slot offset"), "{message}");
    assert!(message.contains("overflows"), "{message}");

    // Pointer slot past the initializer.
    let mut global = object_global("G");
    global.data = vec![0; 4];
    global.symbol_refs.push(GlobalSymbolRef {
        offset: 0,
        symbol: "T".to_string(),
        addend: 0,
    });
    let message = globals_refusal(&[global]);
    assert!(
        message.contains("exceeds its 4 initializer bytes"),
        "{message}"
    );
}

#[test]
fn function_symbol_binding_refusals_are_object_emission() {
    let bindings = [FunctionSymbolBinding::LOCAL];
    let message =
        object_emission_message(function_symbol_binding_at(&bindings, 0, 2, "f").unwrap_err());
    assert!(
        message.contains("symbol-binding vector has 1 entries for a 2-function module"),
        "{message}"
    );

    let message =
        object_emission_message(function_symbol_binding_at(&bindings, 1, 1, "g").unwrap_err());
    assert!(
        message.contains("no symbol binding recorded for function `g` at index 1"),
        "{message}"
    );
}

#[test]
fn macho_module_symbol_refusals_are_object_emission() {
    use crate::macho::MachOWriter;
    use crate::macho::fixup::{Fixup, FixupList};

    // An exact module call to a function this module does not define.
    let mut writer = MachOWriter::new();
    writer.add_text_section(&[0; 4]);
    let mut fixups = FixupList::new();
    fixups.push(Fixup::branch_exact_sym(0, "absent".to_string()));
    let message = object_emission_message(
        add_module_symbols_for_fixups(
            &mut writer,
            &[("f".to_string(), 0)],
            &[],
            &fixups,
            &[],
            &BTreeSet::new(),
        )
        .err()
        .expect("an exact call to an absent function must refuse"),
    );
    assert!(
        message.contains("exact module call targets missing AArch64 function `absent`"),
        "{message}"
    );

    // A function and a data global that share one ABI symbol name resolve to two
    // different nlist indices.
    let mut writer = MachOWriter::new();
    writer.add_text_section(&[0; 4]);
    let message = object_emission_message(
        add_module_symbols_for_fixups(
            &mut writer,
            &[("G".to_string(), 0)],
            &[object_global("G")],
            &FixupList::new(),
            &[],
            &BTreeSet::new(),
        )
        .err()
        .expect("an ambiguous ABI symbol key must refuse"),
    );
    assert!(
        message.contains("ambiguous Mach-O ABI symbol key `_G`"),
        "{message}"
    );
}

#[test]
fn single_function_exact_call_to_another_function_is_object_emission() {
    use crate::macho::MachOWriter;
    use crate::macho::fixup::{Fixup, FixupList};
    let mut writer = MachOWriter::new();
    writer.add_text_section(&[0; 4]);
    let symbol = writer
        .add_symbol("_f", 1, 0, true)
        .expect("function symbol");
    let mut fixups = FixupList::new();
    fixups.push(Fixup::branch_exact_sym(0, "g".to_string()));
    let message = object_emission_message(
        add_single_function_symbol_ids_for_fixups(
            &mut writer,
            "f",
            symbol,
            &fixups,
            &HashMap::new(),
        )
        .err()
        .expect("a single-function object cannot resolve an exact call to another function"),
    );
    assert!(
        message.contains("cannot resolve exact module call to `g` from `f`"),
        "{message}"
    );
}

#[test]
fn final_macho_symbol_index_of_an_unknown_id_is_object_emission() {
    let mut writer = crate::macho::MachOWriter::new();
    let message = object_emission_message(
        final_macho_symbol_index(&mut writer, 7, "a test relocation").unwrap_err(),
    );
    assert!(
        message.contains("Mach-O symbol id 7 missing before a test relocation"),
        "{message}"
    );
}

fn elf_global_row(name: &str, section: u16, offset: u64) -> ElfGlobalSymbolRow {
    ElfGlobalSymbolRow {
        name: name.to_string(),
        section,
        offset,
        size: 8,
        is_weak: false,
        is_tls: false,
        is_external: true,
        visibility: crate::elf::constants::STV_DEFAULT,
        comdat_group: None,
    }
}

#[test]
fn elf_global_relocation_refusals_are_object_emission() {
    let mut global = object_global("G");
    global.symbol_refs.push(GlobalSymbolRef {
        offset: 1,
        symbol: "T".to_string(),
        addend: 0,
    });
    let symbol_indices: HashMap<String, u32> = [("T".to_string(), 1u32)].into_iter().collect();

    // The global was never placed in a data section.
    let mut writer = crate::elf::ElfWriter::new(crate::elf::ElfMachine::AArch64);
    let message = object_emission_message(
        add_aarch64_elf_global_relocations(
            &mut writer,
            std::slice::from_ref(&global),
            &[],
            &symbol_indices,
        )
        .unwrap_err(),
    );
    assert!(
        message.contains("global `G` has symbol-address slots but was not placed"),
        "{message}"
    );

    // Its slot offset overflows the section offset.
    let mut writer = crate::elf::ElfWriter::new(crate::elf::ElfMachine::AArch64);
    writer.add_text_section(&[0; 4]);
    let message = object_emission_message(
        add_aarch64_elf_global_relocations(
            &mut writer,
            std::slice::from_ref(&global),
            &[elf_global_row("G", 1, u64::MAX)],
            &symbol_indices,
        )
        .unwrap_err(),
    );
    assert_eq!(message, "ELF data relocation offset overflow");
}

/// `BL #0`, the placeholder a Branch26 fixup patches.
const BL_PLACEHOLDER: [u8; 4] = 0x9400_0000u32.to_le_bytes();

#[test]
fn elf_exact_call_to_an_absent_function_is_object_emission() {
    use crate::macho::fixup::{Fixup, FixupList};
    let mut fixups = FixupList::new();
    fixups.push(Fixup::branch_exact_sym(0, "absent".to_string()));
    let message = object_emission_message(
        emit_aarch64_elf_with_supported_fixups(
            "aarch64-unknown-linux-gnu",
            &BL_PLACEHOLDER,
            &[("f".to_string(), 0)],
            &[],
            &fixups,
            &plan_elf_text(
                crate::elf::ElfMachine::AArch64,
                &BL_PLACEHOLDER,
                &[("f".to_string(), 0)],
                2,
                ElfTextOptions {
                    function_sections: false,
                    functions: &[],
                },
            )
            .expect("single-function text plan"),
            &ElfModuleSymbolPlan::legacy(),
            None,
        )
        .unwrap_err(),
    );
    assert!(
        message.contains("exact module call targets missing AArch64 ELF function `absent`"),
        "{message}"
    );
}

fn frameless_layout() -> crate::frame::FrameLayout {
    crate::frame::FrameLayout {
        callee_saved_pairs: Vec::new(),
        callee_saved_area_size: 0,
        spill_area_size: 0,
        local_area_size: 0,
        outgoing_arg_area_size: 0,
        total_frame_size: 0,
        uses_frame_pointer: false,
        is_leaf: true,
        uses_red_zone: false,
        fp_to_spill_offset: 0,
        has_dynamic_alloc: false,
    }
}

/// A layout compact unwind cannot describe (runtime-sized frame), so the
/// Mach-O planner gives the function a DWARF FDE.
fn dwarf_fallback_layout() -> crate::frame::FrameLayout {
    crate::frame::FrameLayout {
        has_dynamic_alloc: true,
        ..frameless_layout()
    }
}

fn eh_data(code_len: u32, lsda: Option<(&[u8], &str)>) -> ModuleFunctionEhData {
    ModuleFunctionEhData {
        code_len,
        lsda: lsda.map(|(bytes, personality)| FunctionLsda {
            image: lsda_image(bytes),
            personality: personality.to_string(),
        }),
    }
}

/// An LSDA image with no typeinfo relocation (catch-all/cleanup bytes).
fn lsda_image(bytes: &[u8]) -> crate::exception_handling::LsdaImage {
    crate::exception_handling::LsdaImage {
        bytes: bytes.to_vec(),
        typeinfo_relocations: Vec::new(),
    }
}

const ELF_TRIPLE: &str = "aarch64-unknown-linux-gnu";

#[test]
fn elf_unwind_module_refusals_are_unwind() {
    use crate::macho::fixup::FixupList;
    let functions = [("f".to_string(), 0u64), ("g".to_string(), 4u64)];
    let lsda: &[u8] = &[0xff, 0x9b, 0x00, 0x00];

    // An EH module missing a frame layout.
    let message = unwind_message(
        emit_aarch64_elf_module_with_unwind(
            ELF_TRIPLE,
            &[0; 8],
            &functions,
            &[],
            &FixupList::new(),
            &[
                eh_data(4, Some((lsda, "__gxx_personality_v0"))),
                eh_data(4, None),
            ],
            &[Some(frameless_layout()), None],
            2,
            &ElfModuleSymbolPlan::legacy(),
            ElfTextOptions {
                function_sections: false,
                functions: &[],
            },
            None,
        )
        .unwrap_err(),
    );
    assert!(
        message.contains("EVERY function needs an .eh_frame FDE"),
        "{message}"
    );
    assert!(
        message.contains("no frame layout was provided for `g`"),
        "{message}"
    );

    // Two personalities in one module.
    let message = unwind_message(
        emit_aarch64_elf_module_with_unwind(
            ELF_TRIPLE,
            &[0; 8],
            &functions,
            &[],
            &FixupList::new(),
            &[
                eh_data(4, Some((lsda, "__gxx_personality_v0"))),
                eh_data(4, Some((lsda, "rust_eh_personality"))),
            ],
            &[Some(frameless_layout()), Some(frameless_layout())],
            2,
            &ElfModuleSymbolPlan::legacy(),
            ElfTextOptions {
                function_sections: false,
                functions: &[],
            },
            None,
        )
        .unwrap_err(),
    );
    assert!(
        message.contains("ELF module unwind emission supports one personality routine"),
        "{message}"
    );

    // A non-EH function in an EH module whose filler LSDA would cover zero bytes.
    let message = unwind_message(
        emit_aarch64_elf_module_with_unwind(
            ELF_TRIPLE,
            &[0; 4],
            &[("f".to_string(), 0), ("g".to_string(), 4)],
            &[],
            &FixupList::new(),
            &[
                eh_data(4, Some((lsda, "__gxx_personality_v0"))),
                eh_data(0, None),
            ],
            &[Some(frameless_layout()), Some(frameless_layout())],
            2,
            &ElfModuleSymbolPlan::legacy(),
            ElfTextOptions {
                function_sections: false,
                functions: &[],
            },
            None,
        )
        .unwrap_err(),
    );
    assert!(
        message.contains("synthetic filler LSDA for ELF module function g is invalid"),
        "{message}"
    );

    // A text offset no signed 64-bit relocation addend can carry never reaches
    // the FDE addend conversion: the ELF writer refuses the function symbol
    // first, as a value outside its section.
    let error = emit_aarch64_elf_module_with_unwind(
        ELF_TRIPLE,
        &[0; 4],
        &[("f".to_string(), u64::MAX)],
        &[],
        &FixupList::new(),
        &[eh_data(4, None)],
        &[Some(frameless_layout())],
        2,
        &ElfModuleSymbolPlan::legacy(),
        ElfTextOptions {
            function_sections: false,
            functions: &[],
        },
        None,
    )
    .unwrap_err();
    assert!(
        matches!(
            &error,
            PipelineError::ElfSymbol(crate::elf::ElfSymbolError::RangeOutOfSection { symbol, .. })
                if symbol == "f"
        ),
        "{error:?}"
    );

    // An EH module whose only LSDA is empty lays out no `.gcc_except_table`.
    let message = unwind_message(
        emit_aarch64_elf_module_with_unwind(
            ELF_TRIPLE,
            &[0; 4],
            &[("f".to_string(), 0)],
            &[],
            &FixupList::new(),
            &[eh_data(4, Some((&[], "__gxx_personality_v0")))],
            &[Some(frameless_layout())],
            2,
            &ElfModuleSymbolPlan::legacy(),
            ElfTextOptions {
                function_sections: false,
                functions: &[],
            },
            None,
        )
        .unwrap_err(),
    );
    assert!(
        message.contains("EH module produced no .gcc_except_table anchor symbol"),
        "{message}"
    );
}

#[test]
fn elf_unwind_module_exact_call_to_an_absent_function_is_object_emission() {
    use crate::macho::fixup::{Fixup, FixupList};
    let mut fixups = FixupList::new();
    fixups.push(Fixup::branch_exact_sym(0, "absent".to_string()));
    let message = object_emission_message(
        emit_aarch64_elf_module_with_unwind(
            ELF_TRIPLE,
            &BL_PLACEHOLDER,
            &[("f".to_string(), 0)],
            &[],
            &fixups,
            &[eh_data(4, None)],
            &[Some(frameless_layout())],
            2,
            &ElfModuleSymbolPlan::legacy(),
            ElfTextOptions {
                function_sections: false,
                functions: &[],
            },
            None,
        )
        .unwrap_err(),
    );
    assert!(
        message.contains(
            "exact module call targets missing unwind-enabled AArch64 ELF function `absent`"
        ),
        "{message}"
    );
}

fn ret_function(name: &str) -> IrMachFunction {
    let mut func = IrMachFunction::new(
        name.to_string(),
        trust_cg_ir::Signature::new(vec![], vec![]),
    );
    let ret = func.push_inst(IrMachInst::new(IrOpcode::Ret, vec![]));
    func.append_inst(func.entry, ret);
    func
}

fn pipeline_for(triple: &str) -> Pipeline {
    Pipeline::new(PipelineConfig {
        target_triple: triple.to_string(),
        ..Default::default()
    })
}

#[test]
fn module_emission_binding_refusals_are_object_emission() {
    let functions = [ret_function("f")];
    let message = object_emission_message(
        pipeline_for("aarch64-apple-darwin")
            .compile_module_emission_with_target_evidence(
                &functions,
                &[],
                &[],
                &[FunctionSymbolBinding::LOCAL, FunctionSymbolBinding::LOCAL],
            )
            .expect_err("a binding vector that is not 1:1 must refuse"),
    );
    assert!(
        message.contains("module emission received 2 symbol binding(s) for 1 function(s)"),
        "{message}"
    );
    // (The ELF refusal of a non-global binding this test also pinned is gone:
    // every ELF emitter now resolves symbol indices through checked handles
    // after the table is complete, so ELF honours any binding.)
}

// ---------------------------------------------------------------------------
// Exception handling / unwind -> Unwind, MalformedAarch64Eh (TCG-EH-UNWIND)
// ---------------------------------------------------------------------------

fn function_with_personality(name: &str, personality: Option<&str>) -> IrMachFunction {
    let mut func = ret_function(name);
    func.eh_metadata.personality = personality.map(str::to_string);
    // A no-handler call-site record keeps `has_eh_info()` true without a
    // personality.
    func.eh_metadata
        .add_call_site(trust_cg_ir::EhCallSiteEntry {
            call_block: func.entry,
            start_offset: 0,
            length: 4,
            landing_pad_block: None,
        });
    func
}

#[test]
fn machine_function_validator_personality_refusal_is_malformed_eh() {
    let func = function_with_personality("no_personality", None);
    let (function, detail) = malformed_eh_detail(
        validate_aarch64_mach_function_impl(
            &func,
            AArch64CfgValidationStage::SymbolicAuthority,
            None,
        )
        .unwrap_err(),
    );
    assert_eq!(function, "no_personality");
    assert!(
        detail.starts_with("invalid exception-handling personality"),
        "{detail}"
    );
}

#[test]
fn resolve_eh_offsets_refusal_is_malformed_eh() {
    let mut func = function_with_personality("bad_layout", Some("__gxx_personality_v0"));
    let (function, detail) =
        malformed_eh_detail(resolve_eh_offsets(&mut func, &HashMap::new(), 4).unwrap_err());
    assert_eq!(function, "bad_layout");
    assert!(
        detail.starts_with("invalid AArch64 EH metadata/layout: "),
        "{detail}"
    );
}

fn landing_pad(block: u32, offset: u32) -> trust_cg_ir::LandingPadEntry {
    trust_cg_ir::LandingPadEntry {
        block: BlockId(block),
        offset,
        catch_type_indices: vec![],
        is_cleanup: true,
    }
}

#[test]
fn lsda_generation_refusals_are_malformed_eh() {
    // Missing personality.
    let func = function_with_personality("p", None);
    let (_, detail) = malformed_eh_detail(generate_lsda_for_function(&func).unwrap_err());
    assert!(
        detail.starts_with("invalid exception-handling personality"),
        "{detail}"
    );

    // Duplicate landing-pad block.
    let mut func = function_with_personality("dup", Some("__gxx_personality_v0"));
    func.eh_metadata.add_landing_pad(landing_pad(1, 8));
    func.eh_metadata.add_landing_pad(landing_pad(1, 12));
    let (_, detail) = malformed_eh_detail(generate_lsda_for_function(&func).unwrap_err());
    assert!(
        detail.contains("duplicate landing-pad block BlockId(1)"),
        "{detail}"
    );

    // Call site naming a landing pad the table does not describe.
    let mut func = ret_function("missing_pad");
    func.eh_metadata.personality = Some("__gxx_personality_v0".to_string());
    func.eh_metadata
        .add_call_site(trust_cg_ir::EhCallSiteEntry {
            call_block: func.entry,
            start_offset: 0,
            length: 4,
            landing_pad_block: Some(BlockId(9)),
        });
    let (_, detail) = malformed_eh_detail(generate_lsda_for_function(&func).unwrap_err());
    assert!(
        detail.contains("call-site 0 references missing landing-pad block BlockId(9)"),
        "{detail}"
    );

    // A table the checked LSDA builder rejects (zero-length call site).
    let mut func = ret_function("empty_call_site");
    func.eh_metadata.personality = Some("__gxx_personality_v0".to_string());
    func.eh_metadata
        .add_call_site(trust_cg_ir::EhCallSiteEntry {
            call_block: func.entry,
            start_offset: 0,
            length: 0,
            landing_pad_block: None,
        });
    let (_, detail) = malformed_eh_detail(generate_lsda_for_function(&func).unwrap_err());
    assert!(
        detail.starts_with("invalid resolved exception table: "),
        "{detail}"
    );
    assert!(!detail.contains("duplicate landing-pad"), "{detail}");
}

#[test]
fn single_function_macho_personality_refusal_is_malformed_eh() {
    let func = function_with_personality("lsda_without_personality", None);
    let (function, detail) = malformed_eh_detail(
        pipeline_for("aarch64-apple-darwin")
            .emit_macho(
                &func,
                &[0xc0, 0x03, 0x5f, 0xd6],
                None,
                Some(&lsda_image(&[0xff, 0x9b, 0, 0])),
                None,
                None,
            )
            .unwrap_err(),
    );
    assert_eq!(function, "lsda_without_personality");
    assert!(
        detail.starts_with("invalid exception-handling personality"),
        "{detail}"
    );
}

#[test]
fn macho_module_unwind_planner_refusals_are_unwind() {
    let pipeline = pipeline_for("aarch64-apple-darwin");
    let lsda: &[u8] = &[0xff, 0x9b, 0x00, 0x00];
    let functions = [("f".to_string(), 0u64), ("g".to_string(), 4u64)];

    // A function without a frame layout.
    let mut writer = crate::macho::MachOWriter::new();
    let message = unwind_message(
        pipeline
            .plan_module_unwind_sections(
                &mut writer,
                &functions,
                &[
                    eh_data(4, Some((lsda, "__gxx_personality_v0"))),
                    eh_data(4, None),
                ],
                &[Some(frameless_layout()), None],
            )
            .err()
            .expect("a missing layout must refuse"),
    );
    assert!(
        message.contains("EVERY function needs an unwind-table entry"),
        "{message}"
    );
    assert!(
        message.contains("no frame layout was provided for `g`"),
        "{message}"
    );

    // Two personalities are planned, not refused (L03-P11): each routine gets
    // its own undefined symbol and each function keeps its own personality.
    let mut writer = crate::macho::MachOWriter::new();
    let plan = pipeline
        .plan_module_unwind_sections(
            &mut writer,
            &functions,
            &[
                eh_data(4, Some((lsda, "__gxx_personality_v0"))),
                eh_data(4, Some((lsda, "rust_eh_personality"))),
            ],
            &[Some(frameless_layout()), Some(frameless_layout())],
        )
        .expect("a Mach-O module may mix two personalities");
    assert_eq!(
        plan.personality_symbols.keys().collect::<Vec<_>>(),
        ["__gxx_personality_v0", "rust_eh_personality"]
    );
    assert_eq!(
        plan.personalities,
        [
            Some("__gxx_personality_v0".to_string()),
            Some("rust_eh_personality".to_string())
        ]
    );

    // A DWARF-fallback non-EH function, under a zPLR CIE, whose filler LSDA
    // would cover zero bytes.
    let mut writer = crate::macho::MachOWriter::new();
    let message = unwind_message(
        pipeline
            .plan_module_unwind_sections(
                &mut writer,
                &functions,
                &[
                    eh_data(4, Some((lsda, "__gxx_personality_v0"))),
                    eh_data(0, None),
                ],
                &[Some(dwarf_fallback_layout()), Some(dwarf_fallback_layout())],
            )
            .err()
            .expect("an empty filler LSDA must refuse"),
    );
    assert!(
        message.contains("synthetic filler LSDA for module function g is invalid"),
        "{message}"
    );
}

#[test]
fn macho_module_unwind_emission_refusals_are_unwind() {
    use crate::macho::fixup::FixupList;
    let pipeline = pipeline_for("aarch64-apple-darwin");
    let functions = [ret_function("f")];

    // A compact-unwind EH function whose LSDA is empty gets no LSDA symbol.
    let message = unwind_message(
        pipeline
            .emit_module_macho_with_unwind(
                &[0xc0, 0x03, 0x5f, 0xd6],
                FixupList::new(),
                &[("f".to_string(), 0)],
                &[eh_data(4, Some((&[], "__gxx_personality_v0")))],
                &[Some(frameless_layout())],
                &[],
                &functions,
                &[],
                ModuleDebugVariables::LinesOnly,
            )
            .unwrap_err(),
    );
    assert!(
        message.contains("module unwind emission: EH function `f` has no LSDA symbol"),
        "{message}"
    );

    // The same with a DWARF FDE: its LSDA slot has no symbol to point at.
    let message = unwind_message(
        pipeline
            .emit_module_macho_with_unwind(
                &[0xc0, 0x03, 0x5f, 0xd6],
                FixupList::new(),
                &[("f".to_string(), 0)],
                &[eh_data(4, Some((&[], "__gxx_personality_v0")))],
                &[Some(dwarf_fallback_layout())],
                &[],
                &functions,
                &[],
                ModuleDebugVariables::LinesOnly,
            )
            .unwrap_err(),
    );
    assert!(
        message.contains("module unwind emission: FDE for `f` has an LSDA slot but no LSDA symbol"),
        "{message}"
    );
}

fn lir_function_with_personality_only(name: &str) -> trust_cg_lower::Function {
    use trust_cg_lower::function::{BasicBlock, Signature};
    use trust_cg_lower::instructions::{Block, Instruction, Opcode};
    let mut func = trust_cg_lower::Function::new(name, Signature::default());
    func.eh_info.personality = Some("rust_eh_personality".to_string());
    func.entry_block = Block(0);
    func.block_order = vec![Block(0)];
    func.blocks.insert(
        Block(0),
        BasicBlock {
            params: vec![],
            instructions: vec![Instruction {
                opcode: Opcode::Return,
                args: vec![],
                results: vec![],
            }],
            source_locs: vec![],
        },
    );
    func
}

#[test]
fn isel_eh_structure_refusal_is_unwind() {
    let func = lir_function_with_personality_only("personality_only");
    let message = unwind_message(
        pipeline_for("aarch64-apple-darwin")
            .run_isel(&func, None)
            .expect_err("metadata-only EH must fail the LIR structural guard"),
    );
    assert!(
        message.starts_with("invalid exception-handling structure in `personality_only`"),
        "{message}"
    );
}

#[test]
fn stack_canary_on_an_unqualified_target_is_frame_lowering() {
    // An unmodeled triple (x86-64 here) is now refused earlier, by ABI
    // selection (`TargetAbiUnresolved`); Android is a modeled AArch64 target
    // whose canary the frame lowering cannot emit.
    let mut func = ret_function("guarded");
    func.stack_protector = trust_cg_ir::function::StackProtectorMode::StackGuard;
    match pipeline_for("aarch64-linux-android").run_frame_lowering(&mut func) {
        Err(PipelineError::FrameLowering(crate::lower::LowerError::FrameLowering(reason))) => {
            assert!(
                reason.starts_with(
                    "stack canary lowering supports only AArch64 Apple Mach-O and AArch64 Linux ELF"
                ),
                "{reason}"
            );
            assert!(
                reason.ends_with("(target `aarch64-linux-android`, ELF)"),
                "{reason}"
            );
        }
        other => panic!("expected a frame-lowering refusal, got {other:?}"),
    }
}

#[test]
fn aot_counter_ceiling_is_aot_profile_not_an_object_field() {
    let sink = Arc::new(std::sync::Mutex::new(
        trust_cg_opt::pgo::CounterMap::default(),
    ));
    {
        let mut map = sink.lock().expect("fresh counter map");
        for index in 0..4096u32 {
            map.sites.push(trust_cg_opt::pgo::CounterSite {
                function: "earlier".to_string(),
                block_id: index,
                counter_index: index,
                symbol: trust_cg_opt::pgo::counter_symbol("earlier", index),
            });
        }
    }
    let mut func = ret_function("next");
    let err = inject_aot_block_counters(&mut func, &sink).unwrap_err();
    assert!(
        matches!(
            err,
            PipelineError::AotProfile(crate::AotProfileError::CounterIndexTooLarge {
                index: 4096,
                max: 4095,
                ..
            })
        ),
        "{err:?}"
    );
    assert_eq!(
        err.to_string(),
        "AOT profile counter index 4096 for `next` exceeds 4095 (LdrRI/StrRI scaled offset ceiling)"
    );
}
