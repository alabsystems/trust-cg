//! Public AOT-profile preparation through allocation, object emission and linking.
//! Native macOS ARM64 controls check actual memory updates and the result value.

mod common;

use std::sync::{Arc, Mutex};
use trust_cg_codegen::macho::linker::MachOParser;
use trust_cg_codegen::pipeline::{
    ObjectGlobal, OptLevel, PGO_COUNTER_ARRAY_SYMBOL, Pipeline, PipelineConfig,
};
use trust_cg_ir::regs::{RegClass, VReg, X0};
use trust_cg_ir::{
    AArch64Opcode as Op, MachFunction, MachInst, MachOperand as Operand, Signature, Type,
};
use trust_cg_opt::pgo::CounterMap;

fn profile_object(remove_store: bool, with_argument: bool) -> Vec<u8> {
    trust_cg_codegen::env_lock::with_env_edits(|env| {
        // Only optional allocation-quality policy is normalized. Function
        // verification and mandatory allocation/encoding checks stay enabled.
        env.remove("TCG_AY_REGALLOC");
        let mut function = MachFunction::new(
            "profile_target".into(),
            Signature::new(
                if with_argument {
                    vec![Type::I64]
                } else {
                    vec![]
                },
                vec![Type::I64],
            ),
        );
        let tail = function.create_block();
        if with_argument {
            function.next_vreg = 2;
            let argument = function.push_inst(MachInst::new(
                Op::MovR,
                vec![
                    Operand::VReg(VReg::new(0, RegClass::Gpr64)),
                    Operand::PReg(X0),
                ],
            ));
            function.append_inst(function.entry, argument);
        }
        let branch = function.push_inst(MachInst::new(Op::B, vec![Operand::Block(tail)]));
        function.append_inst(function.entry, branch);
        function.add_edge(function.entry, tail);
        let result = if with_argument {
            function.push_inst(MachInst::new(
                Op::AddRI,
                vec![
                    Operand::VReg(VReg::new(1, RegClass::Gpr64)),
                    Operand::VReg(VReg::new(0, RegClass::Gpr64)),
                    Operand::Imm(37),
                ],
            ))
        } else {
            function.push_inst(MachInst::new(
                Op::Movz,
                vec![Operand::PReg(X0), Operand::Imm(37)],
            ))
        };
        function.append_inst(tail, result);
        if with_argument {
            let result = function.push_inst(MachInst::new(
                Op::MovR,
                vec![
                    Operand::PReg(X0),
                    Operand::VReg(VReg::new(1, RegClass::Gpr64)),
                ],
            ));
            function.append_inst(tail, result);
        }
        let ret = function.push_inst(MachInst::new(Op::Ret, vec![]).with_implicit_uses(&[X0]));
        function.append_inst(tail, ret);
        let sink = Arc::new(Mutex::new(CounterMap::new()));
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level: OptLevel::O0,
            verify: true,
            target_triple: "aarch64-apple-darwin".into(),
            ..PipelineConfig::default()
        })
        .with_profile_generate_sink(Arc::clone(&sink));
        pipeline.prepare_ir_function(&mut function).unwrap();
        let sites = sink.lock().unwrap();
        assert_eq!(sites.len(), 2);
        assert_eq!(
            sites
                .sites
                .iter()
                .map(|site| site.counter_index)
                .collect::<Vec<_>>(),
            [0, 1]
        );
        let stores: Vec<_> = function
            .block_order
            .iter()
            .flat_map(|block| &function.blocks[block.0 as usize].insts)
            .copied()
            .filter(|id| function.insts[id.0 as usize].opcode == Op::StrRI)
            .collect();
        assert_eq!(
            stores.len(),
            2,
            "both profile stores survive allocation/frame lowering"
        );
        if remove_store {
            function.insts[stores[0].0 as usize] = MachInst::new(Op::Nop, vec![]);
        }
        let globals = [ObjectGlobal {
            name: PGO_COUNTER_ARRAY_SYMBOL.into(),
            data: [0_u64, u64::MAX - 1]
                .into_iter()
                .flat_map(u64::to_le_bytes)
                .collect(),
            mutable: true,
            is_external: true,
            symbol_refs: vec![],
            is_thread_local: false,
            is_import: false,
            is_weak: false,
            align: 8,
            visibility: trust_ir::Visibility::Default,
            retained: false,
            section: None,
            comdat: false,
        }];
        pipeline
            .compile_module_with_globals(&[function], &globals)
            .unwrap()
    })
}

#[test]
fn aot_profile_object_contains_initialized_counters_and_relocations() {
    let object = MachOParser::parse(&profile_object(false, false)).unwrap();
    assert!(
        object
            .symbols
            .iter()
            .any(|symbol| symbol.name == "_profile_target")
    );
    assert!(
        object
            .symbols
            .iter()
            .any(|symbol| symbol.name == format!("_{PGO_COUNTER_ARRAY_SYMBOL}"))
    );
    let text = object
        .sections
        .iter()
        .find(|section| section.name == "__text")
        .unwrap();
    assert_eq!(text.relocations.len(), 4, "two PAGE21/PAGEOFF12 pairs");
    let data = object
        .sections
        .iter()
        .find(|section| section.name == "__data")
        .unwrap();
    assert_eq!(
        data.data,
        [0_u64, u64::MAX - 1]
            .into_iter()
            .flat_map(u64::to_le_bytes)
            .collect::<Vec<_>>()
    );
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn native_status(remove_store: bool, wrong_high_bit: bool, with_argument: bool) -> i32 {
    use std::os::unix::fs::PermissionsExt;
    use trust_cg_codegen::macho::linker::link;
    use trust_cg_codegen::macho::reloc::Relocation;
    use trust_cg_codegen::macho::writer::MachOWriter;

    // Independent caller: invoke the compiled two-block function three times,
    // check its result (37, or 7+37 with an argument), then compare the complete
    // u64 counters against [3, 1].
    // The second slot starts at MAX-1 to exercise runtime wrapping addition.
    let mut words = Vec::new();
    let mut calls = Vec::new();
    for _ in 0..3 {
        words.push(0xd280_00e0); // MOVZ X0,#7 (callee may consume one argument).
        calls.push(u32::try_from(words.len() * 4).unwrap());
        words.push(0x9400_0000); // BL profile_target (relocated).
    }
    words.push(0xd280_000a | ((if with_argument { 44 } else { 37 }) << 5)); // MOVZ X10, expected result.
    words.push(0xca0a_0000); // EOR X0,X0,X10.
    let page = u32::try_from(words.len() * 4).unwrap();
    words.extend([0x9000_0009, 0x9100_0129]); // ADRP X9 / ADD X9, PAGEOFF.
    let expected = [3 ^ if wrong_high_bit { 1_u64 << 63 } else { 0 }, 1];
    for (index, bits) in expected.into_iter().enumerate() {
        words.push(0xf940_012b | ((index as u32) << 10)); // LDR X11, [X9, #index*8].
        words.push(0xd280_000c | (((bits & 0xffff) as u32) << 5)); // MOVZ X12.
        for halfword in 1..4 {
            words.push(
                0xf280_000c
                    | (halfword << 21)
                    | ((((bits >> (halfword * 16)) & 0xffff) as u32) << 5),
            );
        }
        words.extend([0xca0c_016b, 0xaa0b_0000]); // EOR X11,X11,X12; ORR X0,X0,X11.
    }
    words.extend([
        0xf100_001f, // CMP X0,#0.
        0x1a9f_07e0, // CSET W0,NE (0 match / 1 mismatch).
        0xd280_0030, // MOVZ X16,#1 (Darwin SYS_exit).
        0xd400_1001, // SVC #0x80.
    ]);
    let mut writer = MachOWriter::new();
    writer.add_text_section(
        &words
            .into_iter()
            .flat_map(u32::to_le_bytes)
            .collect::<Vec<_>>(),
    );
    writer.add_symbol("_main", 1, 0, true).unwrap();
    let function_symbol =
        u32::try_from(writer.add_symbol("_profile_target", 0, 0, true).unwrap()).unwrap();
    let counter_symbol = u32::try_from(
        writer
            .add_symbol(&format!("_{PGO_COUNTER_ARRAY_SYMBOL}"), 0, 0, true)
            .unwrap(),
    )
    .unwrap();
    for offset in calls {
        writer
            .add_relocation(0, Relocation::branch26(offset, function_symbol))
            .unwrap();
    }
    writer
        .add_relocation(0, Relocation::page21(page, counter_symbol))
        .unwrap();
    writer
        .add_relocation(0, Relocation::pageoff12(page + 4, counter_symbol))
        .unwrap();
    let caller = MachOParser::parse(&writer.write().unwrap()).unwrap();
    let body = MachOParser::parse(&profile_object(remove_store, with_argument)).unwrap();
    let executable = link(&[caller, body]).unwrap();
    let directory = tempfile::Builder::new()
        .prefix("trust-cg-aot-profile-")
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
    assert!(!result.timed_out, "AOT profile native probe timed out");
    let status = result
        .output
        .status
        .code()
        .expect("native probe must exit normally");
    assert!(
        [0, 1].contains(&status),
        "native probe failed: {:?}",
        result.output
    );
    status
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn aot_profile_native_updates_both_slots_and_preserves_result() {
    assert_eq!(native_status(false, false, false), 0);
    assert_eq!(native_status(false, false, true), 0);
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn aot_profile_native_rejects_removed_store_and_wrong_high_bit() {
    assert_eq!(native_status(true, false, false), 1);
    assert_eq!(native_status(false, true, false), 1);
}
