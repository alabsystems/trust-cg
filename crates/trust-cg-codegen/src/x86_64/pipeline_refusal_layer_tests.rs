// trust-cg-codegen/x86_64/pipeline_refusal_layer_tests.rs - every retyped x86-64
// pipeline refusal is raised with its layer's variant
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Trust-core architecture AD-8 / E0.3, x86-64 half: each raise site this change
//! retyped (from `FrameLowering` / `ConstantPool` / `RegAlloc` / `ISel` /
//! `MalformedFunction`) is driven by a real input and its variant asserted,
//! together with the site's own message. As the rustc bridge files them:
//! `ObjectEmission` -> `TCG-OBJECT-EMIT`; `Unwind` / `MalformedEh` ->
//! `TCG-EH-UNWIND`; `BlockProfiling` -> `TCG-JIT-EXEC`; `WorkerPool` ->
//! `TCG-COMPILE-DRIVER`.

use super::*;
use trust_cg_ir::x86_64_regs::{RAX, XMM6};
use trust_cg_lower::function::{EhCallSite, EhFunctionInfo, EhLandingPad, Signature};
use trust_cg_lower::instructions::Block;

fn object_emission_message(err: X86PipelineError) -> String {
    match err {
        X86PipelineError::ObjectEmission(message) => message,
        other => panic!("expected X86PipelineError::ObjectEmission, got {other:?}"),
    }
}

fn unwind_message(err: X86PipelineError) -> String {
    match err {
        X86PipelineError::Unwind(message) => message,
        other => panic!("expected X86PipelineError::Unwind, got {other:?}"),
    }
}

fn block_profiling_message(err: X86PipelineError) -> String {
    match err {
        X86PipelineError::BlockProfiling(message) => message,
        other => panic!("expected X86PipelineError::BlockProfiling, got {other:?}"),
    }
}

fn frame_metadata() -> X86FrameMetadata {
    X86FrameMetadata {
        callee_saved: Vec::new(),
        callee_saved_xmms: Vec::new(),
        xmm_save_offsets: Vec::new(),
        frame_size: 16,
        has_dynamic_alloc: false,
    }
}

// ---------------------------------------------------------------------------
// Windows COFF unwind records -> Unwind
// ---------------------------------------------------------------------------

#[test]
fn coff_unwind_info_refusals_are_unwind() {
    let metadata = X86FrameMetadata {
        frame_size: 12,
        ..frame_metadata()
    };
    let message = unwind_message(x86_64_coff_unwind_info(&metadata).unwrap_err());
    assert_eq!(message, "Windows x64 frame size 12 is not 8-byte aligned");

    let metadata = X86FrameMetadata {
        callee_saved_xmms: vec![XMM6],
        ..frame_metadata()
    };
    let message = unwind_message(x86_64_coff_unwind_info(&metadata).unwrap_err());
    assert_eq!(
        message,
        "Windows x64 XMM save metadata length mismatch: 1 register(s), 0 offset(s)"
    );
}

fn coff_unwind_record(
    text_offset: u32,
    code_len: u32,
    unwind_info_offset: u32,
) -> X86CoffUnwindRecord {
    X86CoffUnwindRecord {
        text_offset,
        code_len,
        unwind_info_offset,
        unwind_info: vec![0; 4],
    }
}

#[test]
fn coff_unwind_section_refusals_are_unwind() {
    let message = unwind_message(
        build_x86_64_coff_unwind_sections(&[coff_unwind_record(u32::MAX, 2, 0)]).unwrap_err(),
    );
    assert_eq!(message, "COFF unwind function range overflow");

    let message = unwind_message(
        build_x86_64_coff_unwind_sections(&[coff_unwind_record(0, 2, 8)]).unwrap_err(),
    );
    assert_eq!(message, "COFF unwind .xdata offset mismatch");
}

// ---------------------------------------------------------------------------
// Exception-handling tables -> MalformedEh / Unwind
// ---------------------------------------------------------------------------

fn function_with_eh(eh: EhFunctionInfo) -> X86ISelFunction {
    let mut func = X86ISelFunction::new("eh_fn".to_string(), Signature::default());
    for pad in &eh.landing_pads {
        func.ensure_block(pad.block);
    }
    for site in &eh.call_sites {
        func.ensure_block(site.call_block);
        func.ensure_block(site.landing_pad_block);
        if !func.blocks[&site.call_block]
            .insts
            .iter()
            .any(|inst| inst.opcode == X86Opcode::Call)
        {
            func.push_inst(site.call_block, X86ISelInst::new(X86Opcode::Call, vec![]));
        }
        func.add_successor(site.call_block, site.landing_pad_block);
    }
    func.eh_info = eh;
    func
}

fn offsets(pairs: &[(u32, usize)]) -> HashMap<LirBlock, usize> {
    pairs.iter().map(|&(b, o)| (Block(b), o)).collect()
}

fn encoded_calls(pairs: &[(u32, usize, usize, usize)]) -> X86EncodedCallRanges {
    pairs
        .iter()
        .map(|&(block, inst, start, end)| ((Block(block), inst), (start, end)))
        .collect()
}

fn one_pad_eh(personality: &str, catch_type_indices: Vec<u32>) -> EhFunctionInfo {
    EhFunctionInfo {
        personality: Some(personality.to_string()),
        landing_pads: vec![EhLandingPad {
            block: Block(2),
            catch_type_indices,
            is_cleanup: false,
        }],
        call_sites: vec![EhCallSite {
            call_block: Block(0),
            landing_pad_block: Block(2),
        }],
    }
}

#[test]
fn eh_offset_resolution_refusal_is_malformed_eh() {
    let func = function_with_eh(one_pad_eh("__gxx_personality_v0", vec![0]));
    // The landing pad resolves to offset 0, the LSDA's no-handler sentinel.
    match resolve_x86_eh_offsets(
        &func,
        &offsets(&[(0, 0x10), (2, 0x00)]),
        &encoded_calls(&[(0, 0, 0x18, 0x1D)]),
        0x30,
    ) {
        Err(X86PipelineError::MalformedEh { function, detail }) => {
            assert_eq!(function, "eh_fn");
            assert!(
                detail.starts_with("invalid x86 EH metadata/layout: "),
                "{detail}"
            );
        }
        other => panic!("expected MalformedEh, got {other:?}"),
    }
}

#[test]
fn lsda_for_a_typed_catch_is_malformed_eh() {
    let func = function_with_eh(one_pad_eh("__gxx_personality_v0", vec![1]));
    match x86_lsda_for_function(
        &func,
        &offsets(&[(0, 0x00), (2, 0x80)]),
        &encoded_calls(&[(0, 0, 0x20, 0x25)]),
        0xA0,
    ) {
        Err(X86PipelineError::MalformedEh { function, detail }) => {
            assert_eq!(function, "eh_fn");
            assert!(
                detail.starts_with("invalid resolved exception table: "),
                "{detail}"
            );
        }
        other => panic!("expected MalformedEh, got {other:?}"),
    }
}

#[test]
fn eh_frame_cfi_for_an_unencodable_push_is_unwind() {
    let record = X86EhFrameRecord {
        callee_saved: vec![XMM6],
        frame_size: 16,
        code_len: 8,
        symbol_index: 1,
    };
    let message = unwind_message(
        build_x86_64_eh_frame_cfi(&[record]).expect_err("an XMM push has no DWARF push rule"),
    );
    assert!(
        message.starts_with("x86-64 PUSH prologue cannot save register encoding"),
        "{message}"
    );
}

#[test]
fn eh_frame_bake_out_of_range_is_unwind() {
    let mut eh_frame = [0u8; 6];
    assert_eq!(
        unwind_message(bake_le_i32(&mut eh_frame, 4, 1).unwrap_err()),
        "x86-64 eh_frame i32 bake offset out of range"
    );
    assert_eq!(
        unwind_message(bake_le_i64(&mut eh_frame, 0, 1).unwrap_err()),
        "x86-64 eh_frame i64 bake offset out of range"
    );
}

#[test]
fn eh_frame_addend_patch_out_of_range_is_unwind() {
    let mut cfi = DwarfCfiSection::new_x86_64();
    cfi.add_fde(x86_64_fde_from_prologue(&[], 16, 0, 8, 0).expect("plain frame FDE"));
    // A buffer shorter than the serialized CFI the offsets describe.
    let mut eh_frame = [0u8; 8];
    assert_eq!(
        unwind_message(patch_x86_64_macho_eh_frame_addends(&mut eh_frame, &cfi).unwrap_err()),
        "x86-64 eh_frame relocation offset out of range"
    );
}

fn eh_frame_input(
    function_symbol_id: crate::macho::writer::SymbolId,
    eh: Option<X86EhFdeInput>,
    has_dynamic_alloc: bool,
) -> X86EhFrameInput {
    X86EhFrameInput {
        callee_saved: Vec::new(),
        frame_size: 16,
        code_len: 8,
        has_dynamic_alloc,
        function_symbol_id,
        eh,
    }
}

fn macho_writer_with_function() -> (MachOWriter, crate::macho::writer::SymbolId) {
    let mut writer = MachOWriter::for_target(MachOTarget::X86_64);
    writer.add_text_section(&[0xc3; 8]);
    let symbol = writer
        .add_symbol("_f", 1, 0, true)
        .expect("function symbol");
    (writer, symbol)
}

#[test]
fn macho_eh_frame_refusals_are_unwind() {
    // Two personalities in one object.
    let (mut writer, f) = macho_writer_with_function();
    let personality = |name: &str| X86EhFdeInput {
        personality: name.to_string(),
        personality_symbol_id: f,
        lsda_symbol_id: f,
    };
    let message = unwind_message(
        add_x86_64_eh_frame_to_macho(
            &mut writer,
            &[
                eh_frame_input(f, Some(personality("__gxx_personality_v0")), false),
                eh_frame_input(f, Some(personality("rust_eh_personality")), false),
            ],
        )
        .unwrap_err(),
    );
    assert!(
        message.starts_with("x86-64 Mach-O eh_frame: distinct personalities in one object"),
        "{message}"
    );

    // A push the DWARF FDE builder cannot describe.
    let (mut writer, f) = macho_writer_with_function();
    let mut input = eh_frame_input(f, None, true);
    input.callee_saved = vec![XMM6];
    let message = unwind_message(add_x86_64_eh_frame_to_macho(&mut writer, &[input]).unwrap_err());
    assert!(
        message.starts_with("x86-64 PUSH prologue cannot save register encoding"),
        "{message}"
    );

    // An EH FDE whose personality symbol id is not in the writer.
    let (mut writer, f) = macho_writer_with_function();
    let lsda = writer
        .add_symbol("_GCC_except_table_f", 1, 0, false)
        .expect("lsda symbol");
    let message = unwind_message(
        add_x86_64_eh_frame_to_macho(
            &mut writer,
            &[eh_frame_input(
                f,
                Some(X86EhFdeInput {
                    personality: "rust_eh_personality".to_string(),
                    personality_symbol_id: 999,
                    lsda_symbol_id: lsda,
                }),
                false,
            )],
        )
        .unwrap_err(),
    );
    assert_eq!(
        message,
        "x86-64 Mach-O personality symbol missing before relocation emission"
    );

    // A backtrace-only FDE whose function symbol id is not in the writer.
    let (mut writer, _) = macho_writer_with_function();
    let message = unwind_message(
        add_x86_64_eh_frame_to_macho(&mut writer, &[eh_frame_input(999, None, true)]).unwrap_err(),
    );
    assert_eq!(
        message,
        "x86-64 Mach-O function symbol missing before unwind relocation emission"
    );
}

// ---------------------------------------------------------------------------
// x86-64 ELF module unwind planning -> Unwind (landed on main as FrameLowering)
// ---------------------------------------------------------------------------

fn elf_eh_func(name: &str, personality: &str) -> X86EncodedFunc {
    X86EncodedFunc {
        frame_metadata: Some(frame_metadata()),
        eh: Some(X86EhData {
            personality: personality.to_string(),
            lsda_bytes: vec![0xff, 0x9b, 0x00],
        }),
        ..encoded_func(name)
    }
}

fn elf_unwind_plan_error(encoded: &[X86EncodedFunc]) -> String {
    let config = X86PipelineConfig {
        output_format: X86OutputFormat::Elf,
        ..X86PipelineConfig::default()
    };
    unwind_message(
        plan_x86_64_elf_module_unwind(&config, encoded)
            .expect_err("the ELF unwind planner must refuse this module"),
    )
}

#[test]
fn elf_module_unwind_plan_refusals_are_unwind() {
    // Two personalities in one object: one zPLR CIE cannot name both.
    let message = elf_unwind_plan_error(&[
        elf_eh_func("eh_a", "__gxx_personality_v0"),
        elf_eh_func("eh_b", "rust_eh_personality"),
    ]);
    assert!(
        message.starts_with("x86-64 ELF .eh_frame: distinct personalities in one object"),
        "{message}"
    );

    // A function of an EH-bearing module compiled without frame lowering.
    let frameless = X86EncodedFunc {
        frame_metadata: None,
        ..elf_eh_func("eh_frameless", "rust_eh_personality")
    };
    let message = elf_unwind_plan_error(&[frameless]);
    assert!(
        message.contains("EVERY function needs an .eh_frame FDE")
            && message.contains("emit_frame=false"),
        "{message}"
    );

    // A zero-length body: compile_module refuses it earlier (layout
    // validation), so only the planner itself reaches this arm.
    let empty = X86EncodedFunc {
        code_len: 0,
        ..elf_eh_func("eh_empty", "rust_eh_personality")
    };
    let message = elf_unwind_plan_error(&[empty]);
    assert!(
        message.contains("encoded to zero bytes") && message.contains("zero-length FDE"),
        "{message}"
    );

    // A prologue push the DWARF FDE builder cannot describe.
    let mut xmm_push = elf_eh_func("eh_xmm_push", "rust_eh_personality");
    xmm_push
        .frame_metadata
        .as_mut()
        .expect("frame metadata")
        .callee_saved = vec![XMM6];
    let message = elf_unwind_plan_error(&[xmm_push]);
    assert!(
        message.starts_with("x86-64 PUSH prologue cannot save register encoding"),
        "{message}"
    );
}

#[test]
fn elf_module_unwind_plan_filler_lsda_refusal_is_malformed_eh() {
    // A frame-covered non-EH function of an EH-bearing ELF module gets a
    // synthetic all-filler LSDA under the module's one personality. When that
    // personality is not representable in an object, the filler exception
    // table is refused -- an EH-table refusal (`MalformedEh`, TCG-EH-UNWIND),
    // exactly as the Mach-O filler pass files it, never a machine-function
    // layout refusal (`MalformedFunction`, which the bridge files as
    // TCG-REGALLOC-063).
    let config = X86PipelineConfig {
        output_format: X86OutputFormat::Elf,
        ..X86PipelineConfig::default()
    };
    let non_eh = X86EncodedFunc {
        frame_metadata: Some(frame_metadata()),
        text_offset: 8,
        ..encoded_func("plain")
    };
    match plan_x86_64_elf_module_unwind(
        &config,
        &[
            elf_eh_func("eh_bad_personality", "bad\0personality"),
            non_eh,
        ],
    ) {
        Err(X86PipelineError::MalformedEh { function, detail }) => {
            assert_eq!(function, "plain");
            assert!(
                detail.starts_with("invalid synthetic filler exception table: ")
                    && detail.contains("personality"),
                "{detail}"
            );
        }
        other => panic!("expected X86PipelineError::MalformedEh, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// JIT block profiling -> BlockProfiling (TCG-JIT-EXEC)
// ---------------------------------------------------------------------------

#[test]
fn block_profiling_offset_refusals_are_block_profiling() {
    let message = block_profiling_message(
        x86_block_offset(&HashMap::new(), Block(3), "testing").unwrap_err(),
    );
    assert_eq!(
        message,
        "x86 block profiling: block Block(3) missing byte offset while testing"
    );

    let message = block_profiling_message(
        x86_block_shift_for_offset(&[Block(0)], &offsets(&[(0, 0)]), 4, 9).unwrap_err(),
    );
    assert_eq!(
        message,
        "x86 block profiling: byte offset 9 is outside function body length 4"
    );
}

#[test]
fn block_counter_splice_refusals_are_block_profiling() {
    let empty = X86ISelFunction::new("empty".to_string(), Signature::default());
    let message = block_profiling_message(
        splice_x86_block_counter_trampolines(&empty, &[], &HashMap::new())
            .expect_err("empty block order"),
    );
    assert_eq!(message, "x86 block profiling: empty block order");

    let mut func = X86ISelFunction::new("f".to_string(), Signature::default());
    func.ensure_block(Block(0));
    let message = block_profiling_message(
        splice_x86_block_counter_trampolines(&func, &[0xc3; 4], &offsets(&[(0, 8)]))
            .expect_err("a block past the body"),
    );
    assert_eq!(
        message,
        "x86 block profiling: block Block(0) byte range 8..4 outside body length 4"
    );
}

#[test]
fn block_profiling_branch_retarget_refusals_are_block_profiling() {
    let order = [Block(0)];
    let block_offsets = offsets(&[(0, 0)]);
    let starts = offsets(&[(0, 0)]);
    let fixup = |disp32_offset, target| X86BranchFixup {
        disp32_offset,
        target: Block(target),
    };

    // The branch target has no trampoline.
    let mut spliced = vec![0u8; 32];
    let message = block_profiling_message(
        retarget_x86_block_profiling_branches(
            &mut spliced,
            &order,
            &block_offsets,
            8,
            &starts,
            vec![fixup(2, 7)],
        )
        .unwrap_err(),
    );
    assert_eq!(
        message,
        "x86 block profiling: branch target Block(7) missing trampoline start"
    );

    // The shifted rel32 field falls outside the spliced body.
    let mut spliced = vec![0u8; 20];
    let message = block_profiling_message(
        retarget_x86_block_profiling_branches(
            &mut spliced,
            &order,
            &block_offsets,
            8,
            &starts,
            vec![fixup(2, 0)],
        )
        .unwrap_err(),
    );
    assert_eq!(
        message,
        "x86 block profiling: rel32 patch site 20 outside code length 20"
    );

    // The target is beyond a signed 32-bit displacement.
    let far = offsets(&[(0, 1usize << 40)]);
    let mut spliced = vec![0u8; 64];
    let message = block_profiling_message(
        retarget_x86_block_profiling_branches(
            &mut spliced,
            &order,
            &block_offsets,
            8,
            &far,
            vec![fixup(2, 0)],
        )
        .unwrap_err(),
    );
    assert_eq!(
        message,
        "x86 block profiling: rel32 target 1099511627776 from patch site 20 is out of range \
         (1099511627752)"
    );
}

#[test]
fn rel32_patch_refusal_text_names_only_the_patch() {
    // The helper is shared by two layers, so its text carries neither's
    // context; each caller prefixes its own (above and below).
    let mut code = vec![0u8; 4];
    let outside = patch_x86_rel32(&mut code, 2, 0).unwrap_err();
    assert_eq!(
        outside,
        X86Rel32PatchError::SiteOutsideCode {
            disp32_offset: 2,
            code_len: 4,
        }
    );
    assert_eq!(
        outside.to_string(),
        "rel32 patch site 2 outside code length 4"
    );
    let mut code = vec![0u8; 8];
    let far = patch_x86_rel32(&mut code, 0, 1usize << 40).unwrap_err();
    assert_eq!(
        far.to_string(),
        "rel32 target 1099511627776 from patch site 0 is out of range (1099511627772)"
    );
}

#[test]
fn generic_branch_resolution_rel32_refusal_keeps_constant_pool() {
    // The rel32 helper is shared with branch resolution, which is an encoding
    // step: its refusal stays machine-code (`ConstantPool`, TCG-REGALLOC-063),
    // and its text names branch resolution, not block profiling.
    let mut code = vec![0u8; 4];
    match patch_x86_branch_fixups_to_block_offsets(
        &mut code,
        &offsets(&[(1, 0)]),
        vec![X86BranchFixup {
            disp32_offset: 2,
            target: Block(1),
        }],
    ) {
        Err(error @ X86PipelineError::ConstantPool(_)) => {
            // b60c75f7 rendered "x86-64 constant pool failed: x86 block
            // profiling: rel32 patch site 2 outside code length 4".
            assert_eq!(
                error.to_string(),
                "x86-64 constant pool failed: x86 branch resolution: rel32 patch site 2 \
                 outside code length 4"
            );
        }
        other => panic!("expected ConstantPool, got {other:?}"),
    }
}

#[test]
fn windows_jit_block_counters_under_simplified_regalloc_are_block_profiling() {
    let message = block_profiling_message(
        reject_x86_jit_block_counter_regalloc_mode(true, X86RegAllocMode::Simplified).unwrap_err(),
    );
    assert!(
        message.starts_with("Windows x86_64 JIT block counters require full regalloc"),
        "{message}"
    );
    assert!(reject_x86_jit_block_counter_regalloc_mode(false, X86RegAllocMode::Simplified).is_ok());
    assert!(
        reject_x86_jit_block_counter_regalloc_mode(
            true,
            X86RegAllocMode::Full(AllocStrategy::Greedy)
        )
        .is_ok()
    );
}

// ---------------------------------------------------------------------------
// Object writer -> ObjectEmission; object-inventory EH check -> Unwind
// ---------------------------------------------------------------------------

fn encoded_func(name: &str) -> X86EncodedFunc {
    X86EncodedFunc {
        has_body_instructions: true,
        name: name.to_string(),
        code_len: 8,
        const_pool_len: 0,
        const_pool_rdata_offset: 0,
        const_pool_rel32_fixups: Vec::new(),
        call_fixups: Vec::new(),
        global_ref_fixups: Vec::new(),
        text_offset: 0,
        frame_metadata: None,
        eh: None,
    }
}

fn rel32_fixup(disp32_offset: usize, const_pool_offset: u32) -> X86ConstPoolRel32Fixup {
    X86ConstPoolRel32Fixup {
        disp32_offset,
        const_pool_offset,
    }
}

fn coff_pipeline() -> X86Pipeline {
    X86Pipeline::new(X86PipelineConfig {
        output_format: X86OutputFormat::Coff,
        ..Default::default()
    })
}

#[test]
#[cfg(feature = "verify")]
fn object_inventory_refusals_have_their_layer_variants() {
    // COFF constant-pool relocations without `.rdata`.
    let mut func = encoded_func("f");
    func.const_pool_rel32_fixups.push(rel32_fixup(2, 0));
    let message = object_emission_message(
        coff_pipeline()
            .x86_object_relocation_inventory_rows(&[func], &[], X86OutputFormat::Coff, &[])
            .unwrap_err(),
    );
    assert_eq!(
        message,
        "module x86-64 COFF has .text constant-pool relocations but no .rdata"
    );

    // A Mach-O EH function without frame metadata.
    let mut func = encoded_func("eh_without_frame");
    func.eh = Some(X86EhData {
        personality: "rust_eh_personality".to_string(),
        lsda_bytes: vec![0xff; 4],
    });
    let message = unwind_message(
        X86Pipeline::new(X86PipelineConfig::default())
            .x86_object_relocation_inventory_rows(&[func], &[], X86OutputFormat::MachO, &[])
            .unwrap_err(),
    );
    assert!(
        message.starts_with("x86-64 Mach-O: EH function `eh_without_frame` has no frame metadata"),
        "{message}"
    );
}

#[test]
fn module_coff_constant_pool_refusals_are_object_emission() {
    let pipeline = coff_pipeline();
    let refuse = |func: X86EncodedFunc, code: &[u8], rdata: &[u8]| {
        object_emission_message(
            pipeline
                .emit_module_coff(
                    &[func],
                    code,
                    rdata,
                    &[],
                    &X86FunctionSymbolFacts::default(),
                )
                .unwrap_err(),
        )
    };

    let mut func = encoded_func("f");
    func.const_pool_rel32_fixups.push(rel32_fixup(2, 0));
    assert_eq!(
        refuse(func, &[0; 8], &[]),
        "module x86-64 COFF has .text constant-pool relocations but no .rdata"
    );

    let mut func = encoded_func("f");
    func.text_offset = u64::MAX;
    func.const_pool_rel32_fixups.push(rel32_fixup(2, 0));
    assert_eq!(
        refuse(func, &[0; 8], &[0; 8]),
        "COFF constant-pool relocation offset overflow"
    );

    let mut func = encoded_func("f");
    func.text_offset = u64::MAX - 2;
    func.const_pool_rel32_fixups.push(rel32_fixup(0, 0));
    assert_eq!(
        refuse(func, &[0; 8], &[0; 8]),
        "COFF constant-pool relocation patch range overflow"
    );

    let mut func = encoded_func("f");
    func.const_pool_rel32_fixups.push(rel32_fixup(6, 0));
    assert_eq!(
        refuse(func, &[0; 8], &[0; 8]),
        "COFF constant-pool relocation range 6..10 exceeds .text size 8"
    );

    let mut func = encoded_func("f");
    func.const_pool_rdata_offset = u64::MAX;
    func.const_pool_rel32_fixups.push(rel32_fixup(2, 1));
    assert_eq!(
        refuse(func, &[0; 8], &[0; 8]),
        "COFF constant-pool .rdata addend overflow"
    );

    let mut func = encoded_func("f");
    func.const_pool_rdata_offset = 1 << 31;
    func.const_pool_rel32_fixups.push(rel32_fixup(2, 0));
    assert_eq!(
        refuse(func, &[0; 8], &[0; 8]),
        "COFF constant-pool .rdata addend 2147483648 does not fit in REL32 field"
    );
}

#[test]
fn single_function_coff_constant_pool_refusals_are_object_emission() {
    let pipeline = coff_pipeline();
    assert_eq!(
        object_emission_message(
            pipeline
                .emit_coff_with_rodata("f", &[0; 8], &[], &[2], None)
                .unwrap_err()
        ),
        "single-function x86-64 COFF has .text constant-pool relocations but no .rdata"
    );
    assert_eq!(
        object_emission_message(
            pipeline
                .emit_coff_with_rodata("f", &[0; 8], &[0; 8], &[1usize << 33], None)
                .unwrap_err()
        ),
        "COFF constant-pool relocation offset 8589934592 does not fit in u32"
    );
}

#[test]
fn module_macho_emission_refusals_have_their_layer_variants() {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        output_format: X86OutputFormat::MachO,
        ..Default::default()
    });
    let eh_data = || X86EhData {
        personality: "rust_eh_personality".to_string(),
        lsda_bytes: vec![0xff, 0xff, 0x01, 0x00],
    };

    // A frame-covered non-EH function in an EH module whose filler LSDA would
    // cover zero bytes.
    let mut eh_fn = encoded_func("eh_fn");
    eh_fn.frame_metadata = Some(frame_metadata());
    eh_fn.eh = Some(eh_data());
    let mut empty = encoded_func("empty");
    empty.code_len = 0;
    empty.text_offset = 8;
    empty.frame_metadata = Some(frame_metadata());
    match pipeline.emit_module_macho(
        &[eh_fn, empty],
        &[0xc3; 8],
        &[],
        &X86FunctionSymbolFacts::default(),
    ) {
        Err(X86PipelineError::MalformedEh { function, detail }) => {
            assert_eq!(function, "empty");
            assert!(
                detail.starts_with("invalid synthetic filler exception table: "),
                "{detail}"
            );
        }
        other => panic!("expected MalformedEh, got {other:?}"),
    }

    // A thread-local global the shared TLV section writer refuses.
    let tls = crate::pipeline::ObjectGlobal {
        name: "bad\0tls".to_string(),
        data: vec![0; 8],
        mutable: true,
        is_external: true,
        symbol_refs: Vec::new(),
        is_thread_local: true,
        is_import: false,
        is_weak: false,
        align: 8,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        comdat: false,
        section: None,
    };
    let message = object_emission_message(
        pipeline
            .emit_module_macho(
                &[encoded_func("f")],
                &[0xc3; 8],
                std::slice::from_ref(&tls),
                &X86FunctionSymbolFacts::default(),
            )
            .unwrap_err(),
    );
    assert!(
        message.starts_with("x86-64 Mach-O thread-local descriptor section emission failed: "),
        "{message}"
    );

    // An EH function without frame metadata.
    let mut eh_fn = encoded_func("eh_without_frame");
    eh_fn.eh = Some(eh_data());
    let message = unwind_message(
        pipeline
            .emit_module_macho(
                &[eh_fn],
                &[0xc3; 8],
                &[],
                &X86FunctionSymbolFacts::default(),
            )
            .unwrap_err(),
    );
    assert!(
        message.starts_with("x86-64 Mach-O: EH function `eh_without_frame` has no frame metadata"),
        "{message}"
    );
}

fn minimal_function(name: &str) -> X86ISelFunction {
    let mut func = X86ISelFunction::new(name.to_string(), Signature::default());
    func.ensure_block(Block(0));
    func
}

#[test]
fn module_exact_call_to_an_absent_function_is_object_emission() {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O0,
        ..Default::default()
    });
    let mut caller = minimal_function("caller");
    let mut call = X86ISelInst::new(
        X86Opcode::Call,
        vec![X86ISelOperand::Symbol("absent".into())],
    );
    call.flags |= trust_cg_ir::inst::InstFlags::EXACT_MODULE_CALL;
    caller.push_inst(Block(0), call);
    caller.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));
    let message = object_emission_message(pipeline.compile_module(&[caller]).unwrap_err());
    assert_eq!(
        message,
        "exact module call from `caller` targets missing, ambiguous, or empty compiled function `absent`"
    );
}

#[test]
fn module_exact_address_of_an_absent_function_is_object_emission() {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: trust_cg_opt::OptLevel::O0,
        ..Default::default()
    });
    let mut function = minimal_function("materialize");
    function.sig.returns = vec![Type::I64];
    let value = VReg::new(0, RegClass::Gpr64);
    function.next_vreg = 1;
    function.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::LeaRip,
            vec![
                X86ISelOperand::VReg(value),
                X86ISelOperand::ExactModuleSymbol("absent".into()),
            ],
        ),
    );
    function.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![X86ISelOperand::PReg(RAX), X86ISelOperand::VReg(value)],
        ),
    );
    function.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));
    let message = object_emission_message(pipeline.compile_module(&[function]).unwrap_err());
    assert_eq!(
        message,
        "exact function address from `materialize` targets missing, ambiguous, or empty compiled function `absent`"
    );
}

// ---------------------------------------------------------------------------
// LIR EH structure at the x86 ISel entry points -> Unwind
// ---------------------------------------------------------------------------

fn lir_function_with_personality_only(name: &str) -> trust_cg_lower::Function {
    use trust_cg_lower::function::BasicBlock;
    use trust_cg_lower::instructions::{Instruction, Opcode};
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
fn x86_trust_ir_entry_points_refuse_invalid_eh_structure_as_unwind() {
    let pipeline = X86Pipeline::new(X86PipelineConfig::default());
    let func = lir_function_with_personality_only("personality_only");
    let message = unwind_message(
        pipeline
            .compile_trust_ir_function_with_regalloc_pressure_evidence(&func)
            .expect_err("metadata-only EH must fail the structural guard"),
    );
    assert!(
        message.starts_with("invalid exception-handling structure in `personality_only`"),
        "{message}"
    );

    let message = unwind_message(
        pipeline
            .compile_trust_ir_function_emitting_call_fixups(&func)
            .expect_err("metadata-only EH must fail the structural guard"),
    );
    assert!(
        message.starts_with("invalid exception-handling structure in `personality_only`"),
        "{message}"
    );
}

// ---------------------------------------------------------------------------
// x86-64 ELF direct call to a data object -> ObjectEmission
// ---------------------------------------------------------------------------

#[test]
fn elf_direct_call_to_a_data_object_is_object_emission() {
    let caller = X86EncodedFunc {
        call_fixups: vec![X86CallFixup {
            offset: 1,
            callee: "counter_table".to_string(),
            exact_module: true,
        }],
        ..encoded_func("caller")
    };
    let object = crate::pipeline::ObjectGlobal {
        name: "counter_table".to_string(),
        data: vec![0u8; 8],
        mutable: true,
        is_external: false,
        symbol_refs: Vec::new(),
        is_thread_local: false,
        is_import: false,
        is_weak: false,
        align: 8,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        section: None,
        comdat: false,
    };
    let message = object_emission_message(
        reject_x86_elf_calls_to_object_globals(&[caller], &[object])
            .expect_err("a direct call to a data object must be refused"),
    );
    assert!(message.contains("`caller`"), "{message}");
    assert!(
        message.contains("known data object global `counter_table`"),
        "{message}"
    );
}
