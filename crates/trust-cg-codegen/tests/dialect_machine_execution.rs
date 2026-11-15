//! Machine-facade semantics through real allocation, frame lowering and encoding.
//! The portable controls execute emitted bytes under the architectural interpreter;
//! macOS ARM64 also executes bounded, independently bootstrapped native probes.

mod common;

use common::a64_interp::A64Interp;
use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_codegen::frame::{
    compute_frame_layout, eliminate_frame_indices, insert_prologue_epilogue,
    legalize_large_mem_offsets,
};
use trust_cg_codegen::pipeline::{apply_regalloc, ir_to_regalloc, lower_copies};
use trust_cg_dialect::dialects::conversions::register_all;
use trust_cg_dialect::dialects::machir::{MACHIR_ADD_RR, MACHIR_MOVZ_I64, MACHIR_RET};
use trust_cg_dialect::emit_mach_function;
use trust_cg_dialect::id::DialectOpId;
use trust_cg_dialect::module::{DialectFunction, DialectModule};
use trust_cg_dialect::op::Attribute;
use trust_cg_dialect::registry::DialectRegistry;
use trust_cg_ir::regs::RegClass;
use trust_cg_ir::{MachFunction, Type};
use trust_cg_regalloc::{AllocConfig, allocate};

fn module(params: usize, constant: Option<u64>) -> DialectModule {
    let mut registry = DialectRegistry::new();
    let (_, _, machir, _) = register_all(&mut registry);
    let mut function =
        DialectFunction::new("machine_facade", vec![Type::I64; params], vec![Type::I64]).unwrap();
    let entry = function.entry_block().unwrap();
    let mut value = if let Some(bits) = constant {
        let result = function.alloc_value().unwrap();
        function
            .append_op(
                entry,
                DialectOpId::new(machir, MACHIR_MOVZ_I64),
                vec![(result, Type::I64)],
                vec![],
                vec![("value".into(), Attribute::U64(bits))],
                None,
            )
            .unwrap();
        result
    } else {
        function.params[0].0
    };
    for parameter in function
        .params
        .clone()
        .into_iter()
        .skip(usize::from(constant.is_none()))
    {
        let result = function.alloc_value().unwrap();
        function
            .append_op(
                entry,
                DialectOpId::new(machir, MACHIR_ADD_RR),
                vec![(result, Type::I64)],
                vec![value, parameter.0],
                vec![],
                None,
            )
            .unwrap();
        value = result;
    }
    function
        .append_op(
            entry,
            DialectOpId::new(machir, MACHIR_RET),
            vec![],
            vec![value],
            vec![],
            None,
        )
        .unwrap();
    let mut module = DialectModule::new("machine_facade", registry);
    module.push_function(function);
    module
}

fn machine_code(module: &DialectModule) -> Vec<u8> {
    machine_code_from_function(emit_mach_function(module, 0).expect("emit machine facade"))
}

fn machine_code_from_function(function: MachFunction) -> Vec<u8> {
    machine_code_with_register_floor(function, 9)
}

fn machine_code_with_register_floor(mut function: MachFunction, register_floor: u16) -> Vec<u8> {
    trust_cg_codegen::env_lock::with_env_edits(|env| {
        env.remove("TCG_AY_REGALLOC");
        let mut ra = ir_to_regalloc(&function).expect("adapt machine IR to regalloc");
        let mut config = AllocConfig::default_aarch64();
        // Preserve the instruction stream so apply_regalloc is sufficient here.
        // Allocation's mandatory translation validator is still run.
        config.enable_coalescing = false;
        config.enable_critical_edge_splitting = false;
        config.enable_splitting = false;
        config.enable_remat = false;
        config.enable_spill_code = false;
        config.enable_spill_slot_reuse = false;
        // Most fixtures exclude argument/result registers so accidental X0
        // placement cannot conceal a missing return transfer. A separate test
        // admits them to exercise entry-prefix physical-register liveness.
        config
            .allocatable_regs
            .get_mut(&RegClass::Gpr64)
            .unwrap()
            .retain(|reg| reg.encoding() >= register_floor);
        let allocation = allocate(&mut ra, &config).expect("validated allocation");
        assert!(
            allocation.spills.is_empty(),
            "bounded fixture must not need spill replay"
        );
        apply_regalloc(&mut function, &allocation.allocation);
        lower_copies(&mut function).unwrap();
        let frame = compute_frame_layout(&function, 0, false);
        insert_prologue_epilogue(&mut function, &frame).unwrap();
        eliminate_frame_indices(&mut function, &frame).unwrap();
        legalize_large_mem_offsets(&mut function).unwrap();
        function
            .block_order
            .iter()
            .flat_map(|block| &function.blocks[block.0 as usize].insts)
            .flat_map(|id| {
                encode_instruction(&function.insts[id.0 as usize])
                    .expect("legal AArch64 instruction")
                    .to_le_bytes()
            })
            .collect()
    })
}

fn interpreted_result(code: &[u8], arguments: &[u64]) -> u64 {
    let mut interpreter = A64Interp::new(code.to_vec());
    for (index, &argument) in arguments.iter().enumerate() {
        if index < 8 {
            interpreter.set_x(index, argument);
        } else {
            let address = interpreter.sp + (index as u64 - 8) * 8;
            for (byte, value) in argument.to_le_bytes().into_iter().enumerate() {
                interpreter.mem.insert(address + byte as u64, value);
            }
        }
    }
    interpreter.run(0).expect("interpret emitted instructions")
}

#[test]
fn facade_execution_small_constant_reaches_abi_result_register() {
    let code = machine_code(&module(0, Some(42)));
    assert_eq!(interpreted_result(&code, &[]), 42);
}

#[test]
fn facade_execution_wide_constants_have_legal_encodings() {
    for bits in [
        0x1_0000,
        0x1_0000_0000,
        1_u64 << 63,
        u64::MAX,
        0x1234_dead_beef_cafe,
    ] {
        let code = machine_code(&module(0, Some(bits)));
        assert_eq!(interpreted_result(&code, &[]), bits, "{bits:#018x}");
    }
}

#[test]
fn facade_execution_signed_constant_attributes_preserve_all_bits() {
    for value in [-1_i64, i64::MIN, -65537, i64::MAX] {
        let mut module = module(0, Some(0));
        module.functions[0].ops[0].attrs = vec![("value".into(), Attribute::I64(value))];
        assert_eq!(
            interpreted_result(&machine_code(&module), &[]),
            value as u64
        );
    }
}

#[test]
fn facade_execution_register_arguments_reach_the_body() {
    let code = machine_code(&module(2, None));
    for (a, b) in [(7_u64, 13_u64), (u64::MAX, 1), (1 << 63, 1 << 63)] {
        assert_eq!(interpreted_result(&code, &[a, b]), a.wrapping_add(b));
    }
}

#[test]
fn facade_execution_entry_copies_preserve_unread_argument_registers() {
    let arguments: Vec<_> = (1_u64..=8).map(|n| n * 0x1234_5678_9abc).collect();
    let expected = arguments.iter().copied().fold(0_u64, u64::wrapping_add);
    for register_floor in [0, 1] {
        // Excluding X0 additionally prevents the first copy from being a no-op.
        let function = emit_mach_function(&module(8, None), 0).unwrap();
        let code = machine_code_with_register_floor(function, register_floor);
        assert_eq!(interpreted_result(&code, &arguments), expected);
    }
}

#[test]
fn facade_execution_stack_arguments_survive_frame_lowering() {
    for count in [8, 9, 10, 12] {
        let arguments: Vec<_> = (0..count)
            .map(|i| (i as u64 + 1).wrapping_mul(0x8102_0304_0506_0708))
            .collect();
        let expected = arguments.iter().copied().fold(0_u64, u64::wrapping_add);
        assert_eq!(
            interpreted_result(&machine_code(&module(count, None)), &arguments),
            expected,
            "{count} arguments"
        );
    }
}

fn progressive_code(fingerprint: bool) -> Vec<u8> {
    let mut module = module(2, None);
    let verif = module.registry.by_name("verif").unwrap();
    module.functions[0].ops[0].op = DialectOpId::new(
        verif,
        if fingerprint {
            trust_cg_dialect::dialects::verif::FINGERPRINT_BATCH
        } else {
            trust_cg_dialect::dialects::verif::BFS_STEP
        },
    );
    let mut functions = trust_cg_dialect::lower_module(&mut module).expect("progressive lowering");
    machine_code_from_function(functions.remove(0))
}

#[test]
fn facade_execution_progressive_patterns_match_their_poc_formulas() {
    for fingerprint in [false, true] {
        let code = progressive_code(fingerprint);
        for (a, b) in [
            (7_u64, 13_u64),
            (u64::MAX, 1),
            (1 << 63, 0x1234_5678_9abc_def0),
        ] {
            let expected = if fingerprint {
                a ^ b ^ trust_cg_dialect::dialects::conversions::FINGERPRINT_BATCH_MAGIC
            } else {
                a.wrapping_add(b) ^ trust_cg_dialect::dialects::conversions::BFS_STEP_MAGIC
            };
            assert_eq!(interpreted_result(&code, &[a, b]), expected);
        }
    }
}

fn without_first_argument_transfer(mut code: Vec<u8>) -> Vec<u8> {
    let transfer = code
        .as_chunks_mut::<4>()
        .0
        .iter_mut()
        .find(|bytes| {
            let word = u32::from_le_bytes(bytes[..4].try_into().unwrap());
            // ORR Xd, XZR, X0 (the MOV Xd, X0 alias), ignoring only Rd.
            word & !31 == 0xaa00_03e0
        })
        .expect("an explicit X0 entry transfer must be present");
    transfer.copy_from_slice(&0xd503_201f_u32.to_le_bytes()); // NOP
    code
}

#[test]
fn facade_execution_detects_a_removed_argument_transfer() {
    let code = machine_code(&module(2, None));
    assert_eq!(interpreted_result(&code, &[7, 13]), 20);
    assert_ne!(
        interpreted_result(&without_first_argument_transfer(code), &[7, 13]),
        20
    );
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn native_exit(code: &[u8], arguments: &[u64], expected: u64) -> i32 {
    use std::os::unix::fs::PermissionsExt;
    use trust_cg_codegen::macho::linker::{MachOParser, link};
    use trust_cg_codegen::macho::writer::MachOWriter;
    use trust_cg_ir::regs::{SpecialReg, X9};
    use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand};

    // Independent caller bootstrap: always encode all four literal halfwords,
    // unlike the facade's sparse MOVK selection. No assembler or system linker.
    fn literal(words: &mut Vec<u32>, register: u32, bits: u64) {
        words.push(0xd280_0000 | (((bits & 0xffff) as u32) << 5) | register);
        for halfword in 1..4 {
            words.push(
                0xf280_0000
                    | (halfword << 21)
                    | ((((bits >> (halfword * 16)) & 0xffff) as u32) << 5)
                    | register,
            );
        }
    }
    assert!(arguments.len() <= 16, "bounded native fixture");
    assert_eq!(code.len() % 4, 0);
    let mut words = Vec::new();
    let stack_bytes = ((arguments.len().saturating_sub(8) * 8 + 15) & !15) as i64;
    if stack_bytes != 0 {
        words.push(
            encode_instruction(&MachInst::new(
                AArch64Opcode::SubRI,
                vec![
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::Imm(stack_bytes),
                ],
            ))
            .unwrap(),
        );
    }
    for index in 0..8 {
        literal(
            &mut words,
            index as u32,
            arguments.get(index).copied().unwrap_or(0),
        );
    }
    for (index, argument) in arguments.iter().enumerate().skip(8) {
        literal(&mut words, 9, *argument);
        words.push(
            encode_instruction(&MachInst::new(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::PReg(X9),
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::Imm((index as i64 - 8) * 8),
                ],
            ))
            .unwrap(),
        );
    }
    // Known scratch values make the removed-copy negative control deterministic.
    // Leave platform register X18, FP and LR untouched.
    for register in (9..=15).chain(19..=28) {
        literal(&mut words, register, 0);
    }
    let call = words.len();
    words.push(0); // BL body; resolved once the caller stub's length is known.
    literal(&mut words, 9, expected);
    words.extend([
        0xca09_0000, // EOR X0, X0, X9: compare all 64 result bits.
        0xf100_001f, // CMP X0, #0.
        0x1a9f_07e0, // CSET W0, NE: exit 0 on match, 1 on mismatch.
        0xd280_0030, // MOVZ X16, #1: Darwin SYS_exit.
        0xd400_1001, // SVC #0x80.
    ]);
    let displacement = words.len() - call;
    assert!(displacement < 1 << 25);
    words[call] = 0x9400_0000 | displacement as u32;
    let mut text: Vec<_> = words.into_iter().flat_map(u32::to_le_bytes).collect();
    text.extend_from_slice(code);
    let mut writer = MachOWriter::new();
    writer.add_text_section(&text);
    writer.add_symbol("_main", 1, 0, true).unwrap();
    let object = writer.write().unwrap();
    let executable = link(&[MachOParser::parse(&object).unwrap()]).unwrap();
    let directory = tempfile::Builder::new()
        .prefix("trust-cg-dialect-native-")
        .tempdir()
        .unwrap();
    let path = directory.path().join("probe");
    std::fs::write(&path, executable).unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
    let result = common::rosetta::run_executable_with_timeout(
        &path,
        common::rosetta::exec_timeout(std::time::Duration::from_secs(5)),
    )
    .unwrap();
    assert!(!result.timed_out, "native probe timed out");
    // Loader/signal/tool failures are failures, never accepted skip evidence.
    let status = result
        .output
        .status
        .code()
        .expect("native probe exited normally");
    assert!(
        [0, 1].contains(&status),
        "native probe failed: {:?}",
        result.output
    );
    status
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn facade_execution_native_matches_constants_arguments_and_progressive_patterns() {
    for bits in [
        0,
        42,
        0x1_0000,
        1_u64 << 63,
        u64::MAX,
        0x1234_dead_beef_cafe,
    ] {
        assert_eq!(
            native_exit(&machine_code(&module(0, Some(bits))), &[], bits),
            0
        );
    }
    for count in [2, 8, 9, 12] {
        let arguments: Vec<_> = (0..count)
            .map(|i| (i as u64 + 1).wrapping_mul(0x8102_0304_0506_0708))
            .collect();
        let expected = arguments.iter().copied().fold(0_u64, u64::wrapping_add);
        assert_eq!(
            native_exit(&machine_code(&module(count, None)), &arguments, expected),
            0
        );
    }
    let (a, b) = (0x8123_4567_89ab_cdef_u64, 0x7654_3210_fedc_ba98_u64);
    for fingerprint in [false, true] {
        let expected = if fingerprint {
            a ^ b ^ trust_cg_dialect::dialects::conversions::FINGERPRINT_BATCH_MAGIC
        } else {
            a.wrapping_add(b) ^ trust_cg_dialect::dialects::conversions::BFS_STEP_MAGIC
        };
        assert_eq!(
            native_exit(&progressive_code(fingerprint), &[a, b], expected),
            0
        );
    }
    eprintln!("[dialect-native] 12 native argument/result cases matched");
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn facade_execution_native_checker_rejects_high_bit_mismatch_and_removed_copy() {
    let code = machine_code(&module(0, Some(42)));
    assert_eq!(native_exit(&code, &[], 42 ^ (1_u64 << 63)), 1);
    let code = without_first_argument_transfer(machine_code(&module(2, None)));
    assert_eq!(native_exit(&code, &[7, 13], 20), 1);
}
