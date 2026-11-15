// trust-cg-verify/tests/aarch64_switch_binding.rs
//
// Per-compile binding of AArch64 switch dispatch to the final bytes, on the
// real pipeline output at O0-O3: dense, holed, negative-range, wide-minimum
// and jump-table-sized switches (ADR/LDRSW/ADD/BR through a table), sparse
// binary-search-tree and linear-scan switches (CMP/B.EQ/B.LT groups, fused
// CBZ at O2+), for i64 and i32 selectors. Every shape must bind, and a
// corruption battery over the emitted words and table bytes (entry off by
// one, swapped entries, bounds off by one, wrong bounds condition or target,
// BR register swapped, LDRSW operands or scale changed, ADR displaced,
// normalization constant changed, case constant changed, branch condition
// inverted, materialization chunk changed) must refute at every level. A
// second battery changes a word together with its intent (bound off by one,
// bound on another register, table target retargeted off the recorded CFG,
// min_val or normalization changed, default edge moved onto a table arm), so
// each case passes the word-versus-intent comparison and is refuted by the
// semantic check it targets. A selector spilled under register pressure and
// reloaded for the bounds compare and again for the table load binds; the
// second reload moved to another slot is refused.
//
// This is a finite regression contract on this host's pipeline output, not a
// proof of the passes; the binding itself is stated in
// `trust_cg_verify::aarch64_switch_binding`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::HashMap;
use trust_cg_codegen::pipeline::{
    OptLevel, Pipeline, PipelineConfig, encode_function_with_fixups_and_blocks,
};

use trust_cg_ir::regs::PReg;
use trust_cg_ir::{AArch64Opcode, InstId, MachFunction, MachOperand};
use trust_cg_verify::aarch64_switch_binding::{
    SwitchBindingError, SwitchBindingReport, check_aarch64_switch_dispatch,
};
use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction,
    ICmpOp, Inst, InstrNode, Module as TrustIrModule, SwitchCase, Ty, ValueId,
};

const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn ret_const_block(bb: u32, vid: u32, k: i64) -> TrustIrBlock {
    TrustIrBlock {
        id: BlockId::new(bb),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(k as i128),
            })
            .with_result(ValueId::new(vid)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(vid)],
            }),
        ],
    }
}

/// `fn name(x: sel_ty) -> i64 { switch x { k_i => v_i, _ => dflt } }`.
fn build_switch_fn(
    m: &mut TrustIrModule,
    id: u32,
    name: &str,
    sel_ty: Ty,
    arms: &[(i64, i64)],
    dflt: i64,
) {
    let ft = m
        .add_func_type(FuncTy {
            params: vec![sel_ty.clone()],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    let default_bb = arms.len() as u32 + 1;
    let cases: Vec<SwitchCase> = arms
        .iter()
        .enumerate()
        .map(|(i, (cv, _))| SwitchCase {
            value: Constant::Int(*cv as i128),
            target: BlockId::new(i as u32 + 1),
            args: vec![],
        })
        .collect();
    let mut blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), sel_ty)],
        body: vec![InstrNode::new(Inst::Switch {
            value: ValueId::new(0),
            default: BlockId::new(default_bb),
            default_args: vec![],
            cases,
            exhaustive_enum_unreachable: false,
        })],
    }];
    for (i, (_, rv)) in arms.iter().enumerate() {
        blocks.push(ret_const_block(i as u32 + 1, 100 + i as u32, *rv));
    }
    blocks.push(ret_const_block(default_bb, 100 + arms.len() as u32, dflt));
    f.blocks = blocks;
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
}

fn arms(values: &[i64]) -> Vec<(i64, i64)> {
    values
        .iter()
        .enumerate()
        .map(|(i, v)| (*v, 1000 + i as i64))
        .collect()
}

fn jump_table_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("switch_binding_tables");
    build_switch_fn(
        &mut m,
        0,
        "dense_zero",
        Ty::I64,
        &arms(&[0, 1, 2, 3, 4, 5]),
        -1,
    );
    build_switch_fn(
        &mut m,
        1,
        "dense_holes_i32",
        Ty::I32,
        &arms(&[2, 3, 5, 6, 7]),
        -1,
    );
    build_switch_fn(
        &mut m,
        2,
        "dense_negative",
        Ty::I64,
        &arms(&[-3, -2, -1, 0, 1]),
        -99,
    );
    build_switch_fn(
        &mut m,
        3,
        "dense_wide_min",
        Ty::I64,
        &arms(&[10000, 10001, 10002, 10003, 10004]),
        0,
    );
    build_switch_fn(
        &mut m,
        4,
        "dense_twelve_i32",
        Ty::I32,
        &arms(&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]),
        7,
    );
    build_switch_fn(
        &mut m,
        5,
        "dense_negative_i32",
        Ty::I32,
        &arms(&[-4, -3, -2, -1, 0, 1, 2]),
        -5,
    );
    m
}

fn compare_tree_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("switch_binding_trees");
    build_switch_fn(
        &mut m,
        0,
        "bst_seven",
        Ty::I64,
        &arms(&[-7, 0, 3, 77, 300, 5000, 30000]),
        0,
    );
    build_switch_fn(
        &mut m,
        1,
        "bst_nine_i32",
        Ty::I32,
        &arms(&[-100, -7, 0, 3, 77, 300, 5000, 30000, 1_000_000]),
        -1,
    );
    build_switch_fn(
        &mut m,
        2,
        "linear_three_i32",
        Ty::I32,
        &arms(&[1, 9, 70000]),
        7,
    );
    build_switch_fn(&mut m, 3, "linear_two", Ty::I64, &arms(&[-1, 4096]), 9);
    m
}

fn compile(module: &TrustIrModule, opt: OptLevel) -> Vec<(MachFunction, Vec<u8>)> {
    // The fixtures are hand-built and claim-less (`body_gate: None`), which
    // the default license REFUSES (WS7.5, DG-73): state `Permit`, so every
    // verdict below is the switch binding's, never the license's.
    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &trust_cg_lower::CodegenLicensePolicy::default()
            .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
    )
    .expect("lower");
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: opt,
        verify: false,
        ..PipelineConfig::for_target("aarch64-apple-darwin")
    });
    lowered
        .iter()
        .map(|(function, _)| {
            let machine = pipeline
                .prepare_function(function)
                .unwrap_or_else(|e| panic!("{} @ {opt:?}: {e}", function.name));
            let (code, _, _) = encode_function_with_fixups_and_blocks(&machine)
                .unwrap_or_else(|e| panic!("{} @ {opt:?}: {e}", machine.name));
            (machine, code)
        })
        .collect()
}

/// `(byte offset, instruction)` of every emitted word, in layout order.
fn emitted(machine: &MachFunction) -> Vec<(usize, &trust_cg_ir::MachInst)> {
    let mut out = Vec::new();
    let mut offset = 0usize;
    for &block in &machine.block_order {
        for &id in &machine.block(block).insts {
            let inst = machine.inst(id);
            if inst.is_pseudo() {
                continue;
            }
            out.push((offset, inst));
            offset += 4;
        }
    }
    out
}

fn body_len(machine: &MachFunction) -> usize {
    emitted(machine).len() * 4
}

fn word(code: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(code[at..at + 4].try_into().unwrap())
}

fn with_word(code: &[u8], at: usize, w: u32) -> Vec<u8> {
    let mut out = code.to_vec();
    out[at..at + 4].copy_from_slice(&w.to_le_bytes());
    out
}

fn bind(machine: &MachFunction, code: &[u8]) -> SwitchBindingReport {
    check_aarch64_switch_dispatch(machine, code).unwrap_or_else(|e| panic!("{}: {e}", machine.name))
}

#[test]
fn jump_table_dispatch_binds_at_every_opt_level() {
    let module = jump_table_module();
    let mut bound = 0;
    for opt in OPT_LEVELS {
        for (machine, code) in compile(&module, opt) {
            let report = bind(&machine, &code);
            assert_eq!(
                report.jump_tables, 1,
                "{} @ {opt:?}: {report:?}",
                machine.name
            );
            let expected_entries = match machine.name.as_str() {
                "dense_zero" | "dense_holes_i32" => 6,
                "dense_negative" | "dense_wide_min" => 5,
                "dense_twelve_i32" => 12,
                "dense_negative_i32" => 7,
                other => panic!("unexpected function {other}"),
            };
            assert_eq!(
                report.table_entries, expected_entries,
                "{} @ {opt:?}: {report:?}",
                machine.name
            );
            // The bounds compare is a compare group with one consumer (B.HI).
            assert!(
                report.compare_groups >= 1,
                "{} @ {opt:?}: {report:?}",
                machine.name
            );
            if matches!(
                machine.name.as_str(),
                "dense_negative" | "dense_wide_min" | "dense_negative_i32"
            ) {
                assert!(
                    report.materialized_constants >= 1,
                    "{} @ {opt:?}: normalization constant must be materialized: {report:?}",
                    machine.name
                );
            }
            bound += 1;
        }
    }
    assert_eq!(bound, 6 * OPT_LEVELS.len());
}

#[test]
fn compare_tree_dispatch_binds_at_every_opt_level() {
    let module = compare_tree_module();
    let mut bound = 0;
    for opt in OPT_LEVELS {
        for (machine, code) in compile(&module, opt) {
            let report = bind(&machine, &code);
            assert_eq!(report.jump_tables, 0, "{} @ {opt:?}", machine.name);
            // Every case constant is routed by one equality test: a CMP+B.EQ
            // group, or a fused CBZ for `case 0` once fusion runs.
            let cases = match machine.name.as_str() {
                "bst_seven" => 7,
                "bst_nine_i32" => 9,
                "linear_three_i32" => 3,
                "linear_two" => 2,
                other => panic!("unexpected function {other}"),
            };
            assert_eq!(
                report.compare_groups + report.fused_branches,
                cases,
                "{} @ {opt:?}: {report:?}",
                machine.name
            );
            assert!(
                report.compare_consumers >= report.compare_groups,
                "{} @ {opt:?}: {report:?}",
                machine.name
            );
            // Constants outside imm12 are materialized: 30000/5000/-7/... .
            assert!(
                report.materialized_constants >= 1,
                "{} @ {opt:?}: {report:?}",
                machine.name
            );
            bound += 1;
        }
    }
    assert_eq!(bound, 4 * OPT_LEVELS.len());
}

/// Every dispatch word of the jump-table block, by opcode.
struct TableSite {
    cmp: usize,
    cmp_is_imm: bool,
    hi: usize,
    adr: usize,
    ldrsw: usize,
    add: usize,
    br: usize,
    sub_imm: Option<usize>,
    /// The MOVZ feeding a `SUB Xi, Xs, Xk` normalization, if any.
    sub_movz: Option<usize>,
    table: usize,
}

fn table_site(machine: &MachFunction) -> TableSite {
    let es = emitted(machine);
    let adr_index = es
        .iter()
        .position(|(_, inst)| {
            inst.opcode == AArch64Opcode::Adr
                && inst
                    .operands
                    .get(1)
                    .is_some_and(MachOperand::is_jump_table_index)
        })
        .expect("jump-table ADR");
    let find_back = |opcodes: &[AArch64Opcode]| {
        (0..adr_index)
            .rev()
            .find(|&i| opcodes.contains(&es[i].1.opcode))
            .map(|i| es[i].0)
    };
    let find_forward = |opcode: AArch64Opcode| {
        (adr_index..es.len())
            .find(|&i| es[i].1.opcode == opcode)
            .map(|i| es[i].0)
            .expect("dispatch word")
    };
    let sub_imm = find_back(&[AArch64Opcode::SubRI]);
    let sub_rr = (0..adr_index)
        .rev()
        .find(|&i| es[i].1.opcode == AArch64Opcode::SubRR);
    let sub_movz = sub_rr.and_then(|s| {
        (0..s)
            .rev()
            .find(|&i| es[i].1.opcode == AArch64Opcode::Movz)
            .map(|i| es[i].0)
    });
    let cmp = find_back(&[AArch64Opcode::CmpRI, AArch64Opcode::CmpRR]).expect("bounds CMP");
    TableSite {
        cmp,
        cmp_is_imm: es
            .iter()
            .any(|(o, inst)| *o == cmp && inst.opcode == AArch64Opcode::CmpRI),
        hi: find_back(&[AArch64Opcode::BCond]).expect("bounds branch"),
        adr: es[adr_index].0,
        ldrsw: find_forward(AArch64Opcode::LdrswRO),
        add: find_forward(AArch64Opcode::AddRR),
        br: find_forward(AArch64Opcode::Br),
        sub_imm,
        sub_movz,
        table: body_len(machine),
    }
}

#[test]
fn jump_table_corruptions_refute() {
    let module = jump_table_module();
    let mut refuted = 0;
    for opt in OPT_LEVELS {
        for (machine, code) in compile(&module, opt) {
            bind(&machine, &code);
            let site = table_site(&machine);
            let entries = machine.jump_tables[0].targets.len();
            let mut cases: Vec<(&str, Vec<u8>)> = Vec::new();
            // Table bytes.
            let entry0 = i32::from_le_bytes(code[site.table..site.table + 4].try_into().unwrap());
            let mut c = code.clone();
            c[site.table..site.table + 4].copy_from_slice(&(entry0 + 4).to_le_bytes());
            cases.push(("entry off by one word", c));
            let mut c = code.clone();
            c[site.table..site.table + 4].copy_from_slice(&(entry0 - 4).to_le_bytes());
            cases.push(("entry off by minus one word", c));
            let a = code[site.table..site.table + 4].to_vec();
            let b = code[site.table + 4..site.table + 8].to_vec();
            if a != b {
                let mut c = code.clone();
                c[site.table..site.table + 4].copy_from_slice(&b);
                c[site.table + 4..site.table + 8].copy_from_slice(&a);
                cases.push(("entries swapped", c));
            }
            let last = site.table + 4 * (entries - 1);
            let entry_last = i32::from_le_bytes(code[last..last + 4].try_into().unwrap());
            let mut c = code.clone();
            c[last..last + 4].copy_from_slice(&(entry_last + 8).to_le_bytes());
            cases.push(("last entry off by two words", c));
            cases.push(("table truncated", code[..code.len() - 4].to_vec()));
            // Bounds check.
            let cmp = word(&code, site.cmp);
            if site.cmp_is_imm {
                cases.push((
                    "bounds off by one (+1)",
                    with_word(&code, site.cmp, cmp + (1 << 10)),
                ));
                cases.push((
                    "bounds off by one (-1)",
                    with_word(&code, site.cmp, cmp - (1 << 10)),
                ));
                cases.push((
                    "bounds compare on another register",
                    with_word(&code, site.cmp, cmp ^ (1 << 5)),
                ));
            }
            let hi = word(&code, site.hi);
            cases.push((
                "bounds condition HS instead of HI",
                with_word(&code, site.hi, (hi & !0xF) | 2),
            ));
            cases.push((
                "bounds condition LS instead of HI",
                with_word(&code, site.hi, (hi & !0xF) | 9),
            ));
            cases.push((
                "bounds target off by one word",
                with_word(&code, site.hi, hi + (1 << 5)),
            ));
            // Register chain.
            let br = word(&code, site.br);
            let br_reg = (br >> 5) & 0x1F;
            cases.push((
                "BR register swapped",
                with_word(
                    &code,
                    site.br,
                    (br & !(0x1F << 5)) | (((br_reg + 1) % 31) << 5),
                ),
            ));
            let ldrsw = word(&code, site.ldrsw);
            let (rn, rm) = ((ldrsw >> 5) & 0x1F, (ldrsw >> 16) & 0x1F);
            cases.push((
                "LDRSW base and index swapped",
                with_word(
                    &code,
                    site.ldrsw,
                    (ldrsw & !((0x1F << 5) | (0x1F << 16))) | (rm << 5) | (rn << 16),
                ),
            ));
            cases.push((
                "LDRSW without the LSL #2 scale",
                with_word(&code, site.ldrsw, ldrsw & !(1 << 12)),
            ));
            cases.push((
                "LDRSW with SXTX extend",
                with_word(&code, site.ldrsw, (ldrsw & !(0b111 << 13)) | (0b111 << 13)),
            ));
            let add = word(&code, site.add);
            let (add_rn, add_rm) = ((add >> 5) & 0x1F, (add >> 16) & 0x1F);
            cases.push((
                "ADD reads the base twice",
                with_word(&code, site.add, (add & !(0x1F << 16)) | (add_rn << 16)),
            ));
            cases.push((
                "ADD reads the entry twice",
                with_word(&code, site.add, (add & !(0x1F << 5)) | (add_rm << 5)),
            ));
            cases.push((
                "ADD replaced by SUB",
                with_word(&code, site.add, add | (1 << 30)),
            ));
            let adr = word(&code, site.adr);
            cases.push((
                "ADR displaced by one word",
                with_word(&code, site.adr, adr + (1 << 5)),
            ));
            cases.push((
                "ADR displaced by one byte",
                with_word(&code, site.adr, adr + (1 << 29)),
            ));
            // Normalization.
            if let Some(sub) = site.sub_imm {
                let w = word(&code, sub);
                cases.push((
                    "SUB #min_val off by one",
                    with_word(&code, sub, w + (1 << 10)),
                ));
            }
            if let Some(movz) = site.sub_movz {
                let w = word(&code, movz);
                cases.push((
                    "materialized min_val off by one",
                    with_word(&code, movz, w + (1 << 5)),
                ));
            }
            for (label, bytes) in cases {
                let result = check_aarch64_switch_dispatch(&machine, &bytes);
                assert!(
                    result.is_err(),
                    "{} @ {opt:?}: {label} must refute, got {result:?}",
                    machine.name
                );
                refuted += 1;
            }
        }
    }
    println!("SWITCH_BINDING_TABLE_CORRUPTIONS refuted={refuted}");
    assert!(refuted >= 4 * 6 * 17);
}

#[test]
fn compare_tree_corruptions_refute() {
    let module = compare_tree_module();
    let mut refuted = 0;
    for opt in OPT_LEVELS {
        for (machine, code) in compile(&module, opt) {
            bind(&machine, &code);
            let es = emitted(&machine);
            let mut cases: Vec<(&str, Vec<u8>)> = Vec::new();
            for (i, (offset, inst)) in es.iter().enumerate() {
                let w = word(&code, *offset);
                match inst.opcode {
                    AArch64Opcode::CmpRI => {
                        cases.push((
                            "case constant off by one",
                            with_word(&code, *offset, w + (1 << 10)),
                        ));
                        cases.push((
                            "compare on another register",
                            with_word(&code, *offset, w ^ (1 << 5)),
                        ));
                        if inst
                            .operands
                            .first()
                            .is_some_and(|o| matches!(o, MachOperand::PReg(p) if p.encoding() < 32))
                        {
                            cases.push((
                                "64-bit compare narrowed to 32 bits",
                                with_word(&code, *offset, w & !(1 << 31)),
                            ));
                        }
                    }
                    AArch64Opcode::CmpRR => {
                        cases.push((
                            "compare operands swapped",
                            with_word(
                                &code,
                                *offset,
                                (w & !((0x1F << 5) | (0x1F << 16)))
                                    | (((w >> 16) & 0x1F) << 5)
                                    | (((w >> 5) & 0x1F) << 16),
                            ),
                        ));
                        // The materializing MOVZ/MOVK before it.
                        if let Some((mo, _)) = es[..i].iter().rev().find(|(_, m)| {
                            matches!(m.opcode, AArch64Opcode::Movz | AArch64Opcode::Movk)
                        }) {
                            let mw = word(&code, *mo);
                            cases.push((
                                "materialized constant chunk off by one",
                                with_word(&code, *mo, mw ^ (1 << 5)),
                            ));
                        }
                    }
                    AArch64Opcode::BCond => {
                        cases.push((
                            "branch condition inverted",
                            with_word(&code, *offset, w ^ 1),
                        ));
                        cases.push((
                            "branch displaced by one word",
                            with_word(&code, *offset, w + (1 << 5)),
                        ));
                    }
                    AArch64Opcode::Cbz => {
                        cases.push((
                            "CBZ turned into CBNZ",
                            with_word(&code, *offset, w | (1 << 24)),
                        ));
                        cases.push(("CBZ on another register", with_word(&code, *offset, w ^ 1)));
                        cases.push((
                            "CBZ displaced by one word",
                            with_word(&code, *offset, w + (1 << 5)),
                        ));
                    }
                    _ => {}
                }
            }
            assert!(
                !cases.is_empty(),
                "{} @ {opt:?}: no dispatch words",
                machine.name
            );
            for (label, bytes) in cases {
                let result = check_aarch64_switch_dispatch(&machine, &bytes);
                assert!(
                    result.is_err(),
                    "{} @ {opt:?}: {label} must refute, got {result:?}",
                    machine.name
                );
                refuted += 1;
            }
        }
    }
    println!("SWITCH_BINDING_TREE_CORRUPTIONS refuted={refuted}");
    assert!(refuted >= 4 * 4 * 6);
}

#[test]
fn fused_case_zero_binds_as_cbz_once_fusion_runs() {
    let module = compare_tree_module();
    let mut fused = 0;
    for opt in [OptLevel::O2, OptLevel::O3] {
        for (machine, code) in compile(&module, opt) {
            let report = bind(&machine, &code);
            // The 64-bit `case 0` leaf fuses to CBZ; the 32-bit tree is bound
            // either way (its fusion is the pass's choice, not this contract).
            if machine.name == "bst_seven" {
                assert!(
                    report.fused_branches >= 1,
                    "{} @ {opt:?}: {report:?}",
                    machine.name
                );
            }
            fused += report.fused_branches;
        }
    }
    assert!(fused >= 2, "fused CBZ words bound: {fused}");
}

/// The instruction id laid out at byte `at`.
fn inst_at(machine: &MachFunction, at: usize) -> InstId {
    let mut offset = 0usize;
    for &block in &machine.block_order {
        for &id in &machine.block(block).insts {
            if machine.inst(id).is_pseudo() {
                continue;
            }
            if offset == at {
                return id;
            }
            offset += 4;
        }
    }
    panic!("no instruction at byte {at}")
}

/// Start byte and emitted range of every laid-out block.
fn block_starts(machine: &MachFunction) -> HashMap<trust_cg_ir::BlockId, usize> {
    let mut out = HashMap::new();
    let mut offset = 0usize;
    for &block in &machine.block_order {
        out.insert(block, offset);
        offset += 4 * machine
            .block(block)
            .insts
            .iter()
            .filter(|id| !machine.inst(**id).is_pseudo())
            .count();
    }
    out
}

fn dispatch_block(machine: &MachFunction, adr: usize) -> trust_cg_ir::BlockId {
    let starts = block_starts(machine);
    machine
        .block_order
        .iter()
        .copied()
        .filter(|b| starts[b] <= adr)
        .max_by_key(|b| starts[b])
        .expect("dispatch block")
}

/// Corruptions that change a word and its intent together pass the generic
/// word-versus-intent comparison, so on real output each is refuted only by
/// the semantic check it targets: the bound covering the table exactly, one
/// value compared and loaded, every table target a recorded successor, the
/// normalization equal to `min_val`, and the default edge on the only
/// successor outside the table.
#[test]
fn jump_table_intent_consistent_corruptions_reach_each_semantic_check() {
    let module = jump_table_module();
    let mut hits: HashMap<&str, usize> = HashMap::new();
    for opt in OPT_LEVELS {
        for (machine, code) in compile(&module, opt) {
            bind(&machine, &code);
            let site = table_site(&machine);
            let name = machine.name.clone();
            let mut expect =
                |kind: &'static str,
                 patched: &MachFunction,
                 bytes: &[u8],
                 ok: &dyn Fn(&SwitchBindingError) -> bool| {
                    let result = check_aarch64_switch_dispatch(patched, bytes);
                    assert!(
                        result.as_ref().is_err_and(ok),
                        "{name} @ {opt:?}: {kind} must be refuted by its own check, got {result:?}"
                    );
                    *hits.entry(kind).or_default() += 1;
                };
            let cmp_id = inst_at(&machine, site.cmp);
            let cmp = word(&code, site.cmp);
            if site.cmp_is_imm {
                let k = machine.inst(cmp_id).operands[1].as_imm().expect("imm");
                for (delta, shift) in [(1i64, 1u32 << 10), (-1, 0u32.wrapping_sub(1 << 10))] {
                    if k + delta < 0 {
                        continue;
                    }
                    let mut patched = machine.clone();
                    patched.insts[cmp_id.0 as usize].operands[1] = MachOperand::Imm(k + delta);
                    expect(
                        "bound",
                        &patched,
                        &with_word(&code, site.cmp, cmp.wrapping_add(shift)),
                        &|e| {
                            matches!(e, SwitchBindingError::Bounds { detail, .. }
                                if detail.contains("does not cover"))
                        },
                    );
                }
                // Compare a register the block never writes or reads.
                let used: Vec<u16> = emitted(&machine)
                    .iter()
                    .flat_map(|(_, inst)| inst.operands.iter())
                    .filter_map(|op| match op {
                        MachOperand::PReg(p) => Some(p.encoding() & 31),
                        _ => None,
                    })
                    .collect();
                let other = (9u16..=15)
                    .find(|r| !used.contains(r))
                    .expect("free register");
                let mut patched = machine.clone();
                patched.insts[cmp_id.0 as usize].operands[0] = MachOperand::PReg(PReg::new(other));
                expect(
                    "index identity",
                    &patched,
                    &with_word(
                        &code,
                        site.cmp,
                        (cmp & !(0x1F << 5)) | (u32::from(other) << 5),
                    ),
                    &|e| {
                        matches!(
                            e,
                            SwitchBindingError::Chain {
                                what: "index identity",
                                ..
                            }
                        )
                    },
                );
            }
            // Table entry 0 retargeted, in the table data and the bytes, to
            // the dispatch block itself: a laid-out block start, but not a
            // recorded successor.
            let dispatch = dispatch_block(&machine, site.adr);
            if !machine.block(dispatch).succs.contains(&dispatch) {
                let mut patched = machine.clone();
                patched.jump_tables[0].targets[0] = dispatch;
                let mut bytes = code.clone();
                let entry = block_starts(&machine)[&dispatch] as i32 - site.table as i32;
                bytes[site.table..site.table + 4].copy_from_slice(&entry.to_le_bytes());
                expect("successor", &patched, &bytes, &|e| {
                    matches!(
                        e,
                        SwitchBindingError::TableTargetNotSuccessor { entry: 0, .. }
                    )
                });
            }
            // min_val changed in the table data.
            let mut patched = machine.clone();
            patched.jump_tables[0].min_val += 1;
            expect("min_val", &patched, &code, &|e| {
                matches!(e, SwitchBindingError::Normalization { .. })
            });
            // Normalization constant changed in the SUB word and its intent.
            if let Some(sub) = site.sub_imm {
                let sub_id = inst_at(&machine, sub);
                let k = machine.inst(sub_id).operands[2].as_imm().expect("imm");
                let mut patched = machine.clone();
                patched.insts[sub_id.0 as usize].operands[2] = MachOperand::Imm(k + 1);
                expect(
                    "normalization",
                    &patched,
                    &with_word(&code, sub, word(&code, sub) + (1 << 10)),
                    &|e| {
                        matches!(e, SwitchBindingError::Normalization { detail, .. }
                            if detail.contains("subtracts"))
                    },
                );
            }
            // The default edge moved, in the B.HI word and its intent, onto a
            // table arm while exactly one successor lies outside the table.
            let jt = &machine.jump_tables[0];
            let outside: Vec<_> = machine
                .block(dispatch)
                .succs
                .iter()
                .filter(|b| !jt.targets.contains(b))
                .copied()
                .collect();
            if let [default] = outside.as_slice() {
                let arm = *jt.targets.iter().find(|t| *t != default).expect("arm");
                let hi_id = inst_at(&machine, site.hi);
                let disp = (block_starts(&machine)[&arm] as i64 - site.hi as i64) / 4;
                let mut patched = machine.clone();
                patched.insts[hi_id.0 as usize].operands[1] = match machine.inst(hi_id).operands[1]
                {
                    MachOperand::Block(_) => MachOperand::Block(arm),
                    _ => MachOperand::Imm(disp),
                };
                let hi = word(&code, site.hi);
                expect(
                    "default edge",
                    &patched,
                    &with_word(
                        &code,
                        site.hi,
                        (hi & !(0x7_FFFF << 5)) | (((disp as u32) & 0x7_FFFF) << 5),
                    ),
                    &|e| {
                        matches!(e, SwitchBindingError::Bounds { detail, .. }
                            if detail.contains("only successor outside the table"))
                    },
                );
            }
        }
    }
    println!("SWITCH_BINDING_SEMANTIC_CORRUPTIONS {hits:?}");
    for (kind, minimum) in [
        ("bound", 4 * 6),
        ("index identity", 4 * 6),
        ("successor", 4 * 6),
        ("min_val", 4 * 6),
        ("normalization", 4),
        ("default edge", 4 * 5),
    ] {
        assert!(
            hits.get(kind).copied().unwrap_or(0) >= minimum,
            "{kind}: {hits:?}"
        );
    }
}

/// Twenty-four values live across a dense eight-case switch: the register
/// allocator spills the selector, and at some level reloads it once for the
/// bounds compare and once for the table load. Both reloads read one flagged
/// spill slot with nothing in between that can write it, so the binding
/// admits the dispatch; moving the second reload to another slot (word and
/// intent together) is refused as an index-identity break.
fn pressure_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("switch_binding_pressure");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(0), "sw_pressure", ft, BlockId::new(0));
    let mut next = 10u32;
    let mut fresh = || {
        next += 1;
        ValueId::new(next)
    };
    let konst = |v: ValueId, k: i128| {
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(k),
        })
        .with_result(v)
    };
    let bin = |v: ValueId, op: BinOp, lhs: ValueId, rhs: ValueId| {
        InstrNode::new(Inst::BinOp {
            op,
            ty: Ty::I64,
            lhs,
            rhs,
        })
        .with_result(v)
    };
    let (x, a) = (ValueId::new(0), ValueId::new(1));
    let mut body = Vec::new();
    let mut live = Vec::new();
    for i in 0..24i128 {
        let (c1, c2, t, v) = (fresh(), fresh(), fresh(), fresh());
        body.push(konst(c1, i + 3));
        body.push(konst(c2, i * 7 + 1));
        body.push(bin(t, BinOp::Mul, a, c1));
        body.push(bin(v, BinOp::Add, t, c2));
        live.push(v);
    }
    body.push(InstrNode::new(Inst::Switch {
        value: x,
        default: BlockId::new(9),
        default_args: vec![],
        cases: (0..8)
            .map(|k| SwitchCase {
                value: Constant::Int(k),
                target: BlockId::new(k as u32 + 1),
                args: vec![],
            })
            .collect(),
        exhaustive_enum_unreachable: false,
    }));
    let mut blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(x, Ty::I64), (a, Ty::I64)],
        body,
    }];
    for k in 0..9u32 {
        let mut body = Vec::new();
        let mut acc = fresh();
        body.push(konst(acc, i128::from(k)));
        for (i, v) in live.iter().enumerate() {
            let (ck, t, sum) = (fresh(), fresh(), fresh());
            body.push(konst(ck, i as i128 + i128::from(k) + 1));
            body.push(bin(t, BinOp::Mul, *v, ck));
            body.push(bin(sum, BinOp::Add, acc, t));
            acc = sum;
        }
        body.push(InstrNode::new(Inst::Return { values: vec![acc] }));
        blocks.push(TrustIrBlock {
            id: BlockId::new(k + 1),
            params: vec![],
            body,
        });
    }
    f.blocks = blocks;
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

#[test]
fn reloaded_spilled_index_binds_and_a_retargeted_reload_is_refused() {
    let module = pressure_module();
    let mut reloaded_levels = 0;
    for opt in OPT_LEVELS {
        for (machine, code) in compile(&module, opt) {
            let report = bind(&machine, &code);
            assert_eq!(
                (report.jump_tables, report.table_entries),
                (1, 8),
                "{opt:?}"
            );
            let site = table_site(&machine);
            let es = emitted(&machine);
            let ldrsw = machine.inst(inst_at(&machine, site.ldrsw));
            let index = ldrsw.operands[2].clone();
            // The latest writer of the index before the load, if a flagged
            // spill reload.
            let Some((reload_at, reload)) = es
                .iter()
                .rev()
                .filter(|(o, _)| *o > site.cmp && *o < site.ldrsw)
                .find(|(_, inst)| inst.operands.first() == Some(&index))
                .filter(|(_, inst)| {
                    inst.opcode == AArch64Opcode::LdrRI && inst.flags.is_spill_slot_access()
                })
                .map(|(o, inst)| (*o, *inst))
            else {
                continue;
            };
            reloaded_levels += 1;
            let MachOperand::MemOp { base, offset } = reload.operands[1] else {
                panic!("{opt:?}: reload address {:?}", reload.operands);
            };
            // Move the second reload 8 bytes lower (LDUR imm9), consistently.
            let id = inst_at(&machine, reload_at);
            let mut patched = machine.clone();
            patched.insts[id.0 as usize].operands[1] = MachOperand::MemOp {
                base,
                offset: offset - 8,
            };
            let w = word(&code, reload_at);
            assert_eq!(w & 0xFFE0_0C00, 0xF840_0000, "{opt:?}: LDUR X form");
            let imm9 = ((offset - 8) as u32) & 0x1FF;
            let bytes = with_word(&code, reload_at, (w & !(0x1FF << 12)) | (imm9 << 12));
            let result = check_aarch64_switch_dispatch(&patched, &bytes);
            assert!(
                matches!(
                    result,
                    Err(SwitchBindingError::Chain {
                        what: "index identity",
                        ..
                    })
                ),
                "{opt:?}: {result:?}"
            );
        }
    }
    println!("SWITCH_BINDING_RELOADED_INDEX levels={reloaded_levels}");
    assert!(
        reloaded_levels >= 1,
        "no level reloads the spilled index; the fixture no longer exercises the reload path"
    );
}

/// `fn folded_cmp(x: i64) -> i64 { if x == 20 + 3 { 1 } else { 2 } }` with the
/// right-hand side computed by a `BinOp` over two constants. The O1+ constant
/// folder rewrites that `BinOp` into ONE `MovI` (its shift-free MOVZ intent),
/// so the compare reads a register whose producer's intent is `MovI` while its
/// word decodes as `MOVZ Xd, #23` — the shape eight Trust trust-ir-cg run-make
/// tests reached (2026-09-28) and the binding refused as "compare constant decodes as
/// `Movz x0, #23, lsl #0` but the intent is `MovI [..]`".
fn folded_compare_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("switch_binding_folded_compare");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(0), "folded_cmp", ft, BlockId::new(0));
    let v = ValueId::new;
    let konst = |id: u32, k: i128| {
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(k),
        })
        .with_result(v(id))
    };
    f.blocks = vec![
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(v(0), Ty::I64)],
            body: vec![
                konst(1, 20),
                konst(2, 3),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: v(1),
                    rhs: v(2),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(3),
                })
                .with_result(v(4)),
                InstrNode::new(Inst::CondBr {
                    cond: v(4),
                    then_target: BlockId::new(1),
                    then_args: vec![],
                    else_target: BlockId::new(2),
                    else_args: vec![],
                }),
            ],
        },
        ret_const_block(1, 10, 1),
        ret_const_block(2, 11, 2),
    ];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

/// Byte offsets of every emitted `MovI` whose destination is the register
/// operand of a later `CMP` in the same block, with nothing writing that
/// register in between (by the machine-IR def model).
fn movi_compare_constants(machine: &MachFunction) -> Vec<usize> {
    use trust_cg_ir::aarch64_regs::hw_encoding;
    let hw = |op: Option<&MachOperand>| match op {
        Some(MachOperand::PReg(p)) => Some(hw_encoding(*p)),
        _ => None,
    };
    let mut sites = Vec::new();
    let mut offset = 0usize;
    for &block in &machine.block_order {
        let mut last_writer: HashMap<u8, (usize, AArch64Opcode)> = HashMap::new();
        for &id in &machine.block(block).insts {
            let inst = machine.inst(id);
            if inst.is_pseudo() {
                continue;
            }
            if matches!(inst.opcode, AArch64Opcode::CmpRR | AArch64Opcode::CMPXrr)
                && let Some(rhs) = hw(inst.operands.get(1))
                && let Some(&(at, AArch64Opcode::MovI)) = last_writer.get(&rhs)
            {
                sites.push(at);
            }
            trust_cg_opt::effects::aarch64_for_each_def_position(
                inst.opcode,
                inst.operands.len(),
                |pos| {
                    if let Some(reg) = hw(inst.operands.get(pos)) {
                        last_writer.insert(reg, (offset, inst.opcode));
                    }
                },
            );
            for preg in inst.implicit_defs {
                last_writer.insert(hw_encoding(*preg), (offset, inst.opcode));
            }
            offset += 4;
        }
    }
    sites
}

/// A compare constant the constant folder materialized as `MovI` binds at every
/// level where the pipeline emits it, and a changed constant word (with the
/// intent kept) is still refused as a compare-constant mismatch.
#[test]
fn const_folded_movi_compare_constant_binds() {
    let module = folded_compare_module();
    let mut movi_sites = 0usize;
    for opt in OPT_LEVELS {
        for (machine, code) in compile(&module, opt) {
            let report = bind(&machine, &code);
            let sites = movi_compare_constants(&machine);
            if sites.is_empty() {
                continue;
            }
            assert!(
                report.materialized_constants >= sites.len(),
                "{opt:?}: {report:?} for MovI sites {sites:?}"
            );
            for at in sites {
                movi_sites += 1;
                let w = word(&code, at);
                assert_eq!(w & 0x7F80_0000, 0x5280_0000, "{opt:?}: MOVZ word {w:#010x}");
                let imm16 = (w >> 5) & 0xFFFF;
                let bumped = (w & !(0xFFFF << 5)) | (((imm16 + 1) & 0xFFFF) << 5);
                let result = check_aarch64_switch_dispatch(&machine, &with_word(&code, at, bumped));
                assert!(
                    matches!(
                        result,
                        Err(SwitchBindingError::IntentMismatch {
                            what: "compare constant",
                            ..
                        })
                    ),
                    "{opt:?}: a changed MovI constant word must be refused: {result:?}"
                );
            }
        }
    }
    println!("SWITCH_BINDING_MOVI_COMPARE_CONSTANTS sites={movi_sites}");
    assert!(
        movi_sites >= 1,
        "no level emits a MovI compare constant; the fixture no longer exercises that intent"
    );
}
