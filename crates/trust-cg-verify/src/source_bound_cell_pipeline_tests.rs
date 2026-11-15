// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};

#[derive(Clone, serde::Deserialize)]
struct Capture {
    case: String,
    module: trust_ir::Module,
    lir: Function,
}

fn captures() -> Vec<Capture> {
    serde_json::from_str(include_str!("source_bound_cell_sources.json")).unwrap()
}

fn prepare(capture: &Capture) -> MachFunction {
    let opt_level = match capture.case.rsplit_once('-').unwrap().1 {
        "O0" => OptLevel::O0,
        "O1" => OptLevel::O1,
        "O2" => OptLevel::O2,
        "O3" => OptLevel::O3,
        other => panic!("unexpected optimization level: {other}"),
    };
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level,
        verify: false,
        ..PipelineConfig::for_target("aarch64-unknown-linux-gnu")
    });
    pipeline
        .prepare_function_with_metrics_and_trust_ir_module(
            &capture.lir,
            None,
            &capture.module,
            &capture.module.functions[0],
        )
        .unwrap()
        .0
}

#[test]
fn all_captured_scalar_callers_bind_through_the_real_pipeline() {
    use sha2::{Digest, Sha256};
    let identities: Vec<serde_json::Value> =
        serde_json::from_str(include_str!("source_bound_cell_machine_identities.json")).unwrap();
    let cases = captures();
    assert_eq!(cases.len(), 24);
    assert_eq!(identities.len(), cases.len());
    for (c, identity) in cases.into_iter().zip(identities) {
        let machine = prepare(&c);
        // The exact signature, instruction arena, CFG, layout, virtual-register
        // bound and stack slots must reproduce the separately retained Trust
        // backend capture: the six O0 rows after physical self-copy cleanup
        // (their pre-cleanup identities are independently reproduced below); for the six O1 rows
        // after the O1 `CfgSimplify` entry/fallthrough merge that 275e8973a
        // added; and for the twelve O2/O3 rows after e44b0c0a9 retired each
        // erased dead virtual copy as an operand-free `Nop` (each such row
        // records its step in `derivation`; with the pre-e44b0c0a9 marker,
        // operands kept, every row reproduces its capture exactly).
        // Debug/provenance maps follow this stable prefix.
        let debug = format!("{machine:#?}");
        let prefix = debug.split_once("    eh_metadata:").unwrap().0;
        assert_eq!(identity["case"], c.case);
        assert_eq!(identity["machine_prefix_bytes"], prefix.len());
        assert_eq!(
            identity["machine_prefix_sha256"],
            format!("{:x}", Sha256::digest(prefix.as_bytes())),
            "{}",
            c.case
        );
        if let Some(prior_identity) = identity.get("before_o0_identity_copy_cleanup") {
            assert!(c.case.ends_with("-O0"));
            let prior = trust_cg_process_env::with_env_overrides(
                &[("TRUST_CG_DISABLE_PASSES", "post_ra")],
                || prepare(&c),
            );
            let prior_debug = format!("{prior:#?}");
            let prior_prefix = prior_debug.split_once("    eh_metadata:").unwrap().0;
            assert_eq!(
                prior_identity["machine_prefix_bytes"],
                prior_prefix.len(),
                "{} historical O0 bytes",
                c.case
            );
            assert_eq!(
                prior_identity["machine_prefix_sha256"],
                format!("{:x}", Sha256::digest(prior_prefix.as_bytes())),
                "{} historical O0 hash",
                c.case
            );
        }
        let checked = check_aarch64_scalar_cell_frame(&c.module, &c.lir, &machine)
            .unwrap_or_else(|e| panic!("{}: {e}", c.case));
        assert!(std::ptr::eq(checked.source().module(), &c.module));
        assert!(std::ptr::eq(checked.source().lir(), &c.lir));
        assert!(std::ptr::eq(checked.machine(), &machine));
        assert_eq!(
            checked.cell_width(),
            if c.case.contains("f32") { 4 } else { 8 }
        );
        assert_eq!(checked.call_count(), 1);
        assert_eq!(checked.frame_instructions().len(), 7);
        let query = crate::ay_bridge::generate_smt2_query_raw(
            &checked.diagnostic_memory_obligation(),
            &Default::default(),
        );
        println!(
            "CELL_MEMORY_QUERY_BEGIN {}\n{query}CELL_MEMORY_QUERY_END {}",
            c.case, c.case
        );
        assert!(super::super::source_bound_frame(&c.lir, &machine).is_err());
        println!("CELL_PIPELINE {} captured=true matched=true", c.case);
    }
}

fn refused(c: &Capture, machine: &MachFunction, label: &str) {
    assert!(
        check_aarch64_scalar_cell_frame(&c.module, &c.lir, machine).is_err(),
        "{} accepted {label}",
        c.case
    );
}

#[test]
fn actual_callers_reject_source_call_cell_frame_and_layout_mutations() {
    let mut rejected = 0;
    for mut c in captures() {
        let machine = prepare(&c);
        let frame = check_aarch64_scalar_cell_frame(&c.module, &c.lir, &machine).unwrap();
        for id in frame.frame_instructions() {
            let mut bad = machine.clone();
            bad.insts[id.0 as usize] = MachInst::new(M::Nop, vec![]);
            refused(&c, &bad, "missing frame instruction");
            rejected += 1;
        }
        let call = machine
            .insts
            .iter()
            .position(|i| i.opcode == M::Bl)
            .unwrap();
        let load = machine
            .insts
            .iter()
            .position(|i| i.opcode == M::LdrRI)
            .unwrap();
        let store = machine
            .insts
            .iter()
            .rposition(|i| i.opcode == M::StrRI)
            .unwrap();
        let ret = machine
            .insts
            .iter()
            .position(|i| i.opcode == M::Ret)
            .unwrap();
        for change in 0..9 {
            let mut bad = machine.clone();
            match change {
                0 => bad.insts[call].operands[0] = O::Symbol("other_callback".into()),
                1 => bad.insts[call].implicit_uses = &[],
                2 => bad.insts[call].implicit_defs = &[X19],
                3 => bad.insts[load] = MachInst::new(M::Nop, vec![]),
                4 => {
                    bad.insts[store].operands[0] =
                        O::PReg(PReg::new(if frame.cell_width() == 4 { 159 } else { 127 }))
                }
                5 => bad.insts[ret].operands[0] = O::PReg(X29),
                6 => bad.insts.push(MachInst::new(
                    M::StrRI,
                    machine.insts[store].operands.clone(),
                )),
                7 => bad.block_order.push(bad.entry),
                _ => {
                    let first = bad.blocks[0].insts[0];
                    bad.blocks[0].insts.insert(1, first);
                }
            }
            refused(&c, &bad, "call/cell/layout mutation");
            rejected += 1;
        }
        // The independent original declaration must agree even when LIR and
        // machine instructions have not changed.
        c.module.functions[1].calling_conv = trust_ir::CallingConv::Fast;
        assert!(matches!(
            check_aarch64_scalar_cell_frame(&c.module, &c.lir, &machine),
            Err(ScalarCellFrameError::Source(_))
        ));
        rejected += 1;
    }
    assert_eq!(rejected, 24 * 17);
    println!("CELL_PIPELINE_MUTATIONS rejected={rejected}");
}

/// Since e44b0c0a9 the copy lowering retires a dead pure virtual copy as an
/// operand-free `Nop` with only its default `IS_PSEUDO` flag (no arena state;
/// the other operand-free `Nop`s here are flagless tombstones of formal
/// arguments and source instructions), so no virtual register survives
/// preparation. A retired copy that defines a value, writes memory or a
/// register, or became a real move is refused, and so is a read of a value no
/// instruction defines.
#[test]
fn erased_virtual_copies_never_define_values_or_hide_instructions() {
    let mut rejected = 0;
    for c in captures().into_iter().filter(|c| c.case.ends_with("O3")) {
        let machine = prepare(&c);
        check_aarch64_scalar_cell_frame(&c.module, &c.lir, &machine).unwrap();
        assert!(
            machine
                .insts
                .iter()
                .all(|inst| !inst.operands.iter().any(|o| matches!(o, O::VReg(_)))),
            "{}: a virtual register survived preparation",
            c.case
        );
        let retired: Vec<_> = machine
            .insts
            .iter()
            .enumerate()
            .filter_map(|(i, inst)| {
                (inst.opcode == M::Nop
                    && inst.operands.is_empty()
                    && inst.flags == InstFlags::IS_PSEUDO)
                    .then_some(i)
            })
            .collect();
        assert!(!retired.is_empty(), "{}: no retired copy", c.case);
        let undefined = O::VReg(trust_cg_ir::VReg::new(machine.next_vreg, RegClass::Gpr64));
        for index in retired {
            for change in 0..5 {
                let mut bad = machine.clone();
                match change {
                    0 => bad.insts[index].operands = vec![undefined.clone(), O::PReg(X19)],
                    1 => bad.insts[index].operands = vec![O::PReg(X19)],
                    2 => bad.insts[index].flags |= InstFlags::WRITES_MEMORY,
                    3 => bad.insts[index].implicit_defs = &[X19],
                    _ => {
                        bad.insts[index].opcode = M::MOVXrr;
                        bad.insts[index].operands = vec![O::PReg(X19), O::PReg(X19)];
                    }
                }
                refused(&c, &bad, "malformed or effectful retired copy");
                rejected += 1;
            }
            let mut bad = machine.clone();
            let load = bad.insts.iter_mut().find(|i| i.opcode == M::LdrRI).unwrap();
            load.operands[1] = undefined.clone();
            refused(&c, &bad, "use of a value no instruction defines");
            rejected += 1;
        }
    }
    assert_eq!(rejected, 48);
    println!("CELL_ERASED_COPY_MUTATIONS rejected={rejected}");
}

#[test]
fn constant_setup_rejects_wrong_bits_widths_shifts_and_address_aliases() {
    let mut rejected = 0;
    for c in captures()
        .into_iter()
        .filter(|c| c.case.starts_with("local_cell"))
    {
        let machine = prepare(&c);
        check_aarch64_scalar_cell_frame(&c.module, &c.lir, &machine).unwrap();
        let first = machine
            .insts
            .iter()
            .position(|i| i.opcode == M::Movz)
            .unwrap();
        let move_fp = machine
            .insts
            .iter()
            .position(|i| i.opcode == M::FmovGprFpr)
            .unwrap();
        for change in 0..10 {
            let mut bad = machine.clone();
            match change {
                0 => bad.insts[first].operands[1] = O::Imm(1),
                1 => bad.insts[first].operands[1] = O::Imm(-1),
                2 => bad.insts[first].operands[1] = O::Imm(65536),
                3..=5 => bad.insts[first]
                    .operands
                    .push(O::Imm([-1, 1, 64][change - 3])),
                6 => bad.insts[first].opcode = M::Movk,
                7 => {
                    bad.insts[move_fp].operands[1] =
                        O::PReg(PReg::new(if c.case.contains("f32") { 0 } else { 32 }))
                }
                8 => bad.insts[move_fp].operands[0] = O::PReg(PReg::new(104)),
                _ => {
                    let call = bad.insts.iter().position(|i| i.opcode == M::Bl).unwrap();
                    let overwrite = MachInst::new(M::Movz, vec![O::PReg(PReg::new(51)), O::Imm(0)]);
                    let id = InstId(bad.insts.len() as u32);
                    bad.insts.push(overwrite);
                    let block = bad
                        .blocks
                        .iter_mut()
                        .find(|b| b.insts.contains(&InstId(call as u32)))
                        .unwrap();
                    let at = block
                        .insts
                        .iter()
                        .position(|i| *i == InstId(call as u32))
                        .unwrap();
                    block.insts.insert(at, id);
                }
            }
            refused(&c, &bad, "constant setup or W/X address alias");
            rejected += 1;
        }
    }
    assert_eq!(rejected, 80);
    println!("CELL_CONSTANT_MUTATIONS rejected={rejected}");
}

fn replace_literal(c: &mut Capture, value: f64) {
    for node in c.module.functions[0]
        .blocks
        .iter_mut()
        .flat_map(|b| &mut b.body)
    {
        if let trust_ir::Inst::Const { value: literal, .. } = &mut node.inst {
            *literal = trust_ir::Constant::Float(value);
        }
    }
    for instruction in c.lir.blocks.values_mut().flat_map(|b| &mut b.instructions) {
        if let trust_cg_lower::instructions::Opcode::Fconst { imm, .. } = &mut instruction.opcode {
            *imm = value;
        }
    }
    assert!(trust_ir_build::validate_module(&c.module).is_empty());
}

#[test]
fn scalar_constants_preserve_signed_zero_subnormals_and_finite_extremes() {
    let mut accepted = 0;
    for mut c in captures()
        .into_iter()
        .filter(|c| c.case.starts_with("local_cell") && c.case.ends_with("O0"))
    {
        let values = if c.case.contains("f32") {
            [
                0.0,
                -0.0,
                f32::from_bits(1) as f64,
                f32::MIN_POSITIVE as f64,
                f32::MAX as f64,
                -(f32::MAX as f64),
            ]
        } else {
            [
                0.0,
                -0.0,
                f64::from_bits(1),
                f64::MIN_POSITIVE,
                f64::MAX,
                -f64::MAX,
            ]
        };
        for value in values {
            replace_literal(&mut c, value);
            let machine = prepare(&c);
            check_aarch64_scalar_cell_frame(&c.module, &c.lir, &machine)
                .unwrap_or_else(|e| panic!("{} {value:?}: {e}", c.case));
            accepted += 1;
        }
    }
    assert_eq!(accepted, 12);
    println!("CELL_CONSTANT_BOUNDARIES accepted={accepted}");
}

#[test]
fn constant_register_transfers_model_movn_and_writes_to_w_aliases() {
    let mut accepted = 0;
    for c in captures()
        .into_iter()
        .filter(|c| c.case.starts_with("local_cell") && c.case.ends_with("O0"))
    {
        let mut machine = prepare(&c);
        let first = machine
            .insts
            .iter()
            .position(|i| i.opcode == M::Movz)
            .unwrap();
        machine.insts[first].opcode = M::Movn;
        machine.insts[first].operands[1] = O::Imm(65535);
        if !c.case.contains("f32") {
            let dst = machine.insts[first].operands[0].clone();
            let id = InstId(machine.insts.len() as u32);
            machine
                .insts
                .push(MachInst::new(M::Movk, vec![dst, O::Imm(0), O::Imm(16)]));
            let at = machine.blocks[0]
                .insts
                .iter()
                .position(|i| *i == InstId(first as u32))
                .unwrap();
            machine.blocks[0].insts.insert(at + 1, id);
        }
        check_aarch64_scalar_cell_frame(&c.module, &c.lir, &machine).unwrap();
        accepted += 1;
    }
    let mut c = captures()
        .into_iter()
        .find(|c| c.case == "local_cell_read-O0")
        .unwrap();
    let mut machine = prepare(&c);
    let setup: Vec<_> = machine
        .insts
        .iter()
        .enumerate()
        .filter_map(|(i, inst)| matches!(inst.opcode, M::Movz | M::Movk).then_some(i))
        .collect();
    assert_eq!(setup.len(), 3);
    replace_literal(&mut c, f64::from_bits(0xc1ac_0000));
    // Starting with nonzero upper X0 bits distinguishes a W0 write that
    // clears them from an incorrect implementation which preserves them.
    for (index, (op, reg, imm, shift)) in setup.into_iter().zip([
        (M::Movz, 0, 65535, 48),
        (M::Movk, 32, 0, 0),
        (M::Movk, 32, 49580, 16),
    ]) {
        machine.insts[index] = MachInst::new(
            op,
            vec![O::PReg(PReg::new(reg)), O::Imm(imm), O::Imm(shift)],
        );
    }
    check_aarch64_scalar_cell_frame(&c.module, &c.lir, &machine).unwrap();
    accepted += 1;
    assert_eq!(accepted, 3);
    println!("CELL_CONSTANT_ALIAS_VARIANTS accepted={accepted}");
}

#[test]
fn ordered_callback_results_flow_into_subsequent_calls() {
    use trust_cg_lower::instructions::{Opcode as L, Value};
    let mut accepted = 0;
    for original in captures().into_iter().filter(|c| {
        c.case.starts_with("aliased_f")
            && c.case.contains("_read-")
            && (c.case.ends_with("O0") || c.case.ends_with("O3"))
    }) {
        for count in [2, 16] {
            let mut c = original.clone();
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
                let trust_ir::Inst::Call { args, .. } = &mut call.inst else {
                    unreachable!()
                };
                args[1] = trust_ir::ValueId::new(value);
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
            let machine = prepare(&c);
            let checked = check_aarch64_scalar_cell_frame(&c.module, &c.lir, &machine).unwrap();
            assert_eq!(checked.call_count(), count);
            let query = crate::ay_bridge::generate_smt2_query_raw(
                &checked.diagnostic_memory_obligation(),
                &Default::default(),
            );
            assert!(query.len() < 400_000);
            println!(
                "CELL_MEMORY_QUERY_BEGIN {}-calls{count}\n{query}CELL_MEMORY_QUERY_END {}-calls{count}",
                c.case, c.case
            );
            let mut bad = machine.clone();
            let second = bad
                .insts
                .iter()
                .enumerate()
                .filter(|(_, i)| i.opcode == M::Bl)
                .nth(1)
                .unwrap()
                .0;
            bad.insts[second] = MachInst::new(M::Nop, vec![]);
            refused(&c, &bad, "missing second callback");
            accepted += 1;
        }
    }
    assert_eq!(accepted, 8);
    println!("CELL_ORDERED_CALLS accepted={accepted} removed_second_call_refused={accepted}");
}
