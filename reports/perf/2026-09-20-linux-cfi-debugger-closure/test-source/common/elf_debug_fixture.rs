// trust-cg-codegen/tests/common/elf_debug_fixture.rs - shared DWARF fixture
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The source-spanned TrustIR fixture shared by the AArch64 ELF DWARF object
//! checks (`aarch64_elf_dwarf`) and the Linux debugger correspondence test
//! (`e2e_aarch64_elf_debugger_linux`), with its source text and expected
//! native result.

#![allow(dead_code)]

use std::collections::{BTreeSet, HashMap};
use std::path::{Path, PathBuf};

use trust_cg_ir::function::{DebugBaseType, DebugLocalVariable, DebugVariableStorage};
use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction,
    Inst, InstrNode, Linkage, Module as TrustIrModule, SourceSpan, Ty, ValueId,
};

pub const FIXTURE: &str = "elf_debug_fixture";
pub const FIXTURE_FILE: &str = "elf_debug_fixture.rs";
pub const BARRIER: &str = "spill_barrier";

/// Source lines the fixture's instructions carry.
pub const ALLOCA_LINE: u32 = 10;
pub const STORE_LINE: u32 = 11;
pub const SPILL_PROBE_LINE: u32 = 12;
pub const PRESSURE_LINE: u32 = 13;
pub const BARRIER_LINE: u32 = 14;
pub const FIRST_BODY_LINE: u32 = 20;
pub const BODY_LINES: u32 = 12;
pub const RESULT_LINE: u32 = FIRST_BODY_LINE + BODY_LINES;
pub const REG_PROBE_LINE: u32 = RESULT_LINE + 1;
pub const RETURN_LINE: u32 = RESULT_LINE + 2;
pub const PRESSURE_VALUES: u32 = 24;
pub const TAIL_CONST: i64 = 65_536;

fn span(line: u32, col: u32) -> SourceSpan {
    SourceSpan { file: 0, line, col }
}

fn const_i64(value: ValueId, imm: i64, line: u32) -> InstrNode {
    InstrNode::new(Inst::Const {
        ty: Ty::I64,
        value: Constant::Int(imm.into()),
    })
    .with_result(value)
    .with_span(span(line, 9))
}

fn binop(op: BinOp, lhs: ValueId, rhs: ValueId, result: ValueId, line: u32, col: u32) -> InstrNode {
    InstrNode::new(Inst::BinOp {
        op,
        ty: Ty::I64,
        lhs,
        rhs,
    })
    .with_result(result)
    .with_span(span(line, col))
}

/// `elf_debug_fixture(x)`: a stack-resident accumulator updated on
/// `BODY_LINES` source lines, a spill probe and `PRESSURE_VALUES` values live
/// across a call to `spill_barrier` (forcing spills and callee-saved
/// registers), a register-held probe and a constant.
pub fn fixture() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new(FIXTURE);
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), FIXTURE, ft, BlockId::new(0));
    let mut barrier = TrustIrFunction::new(FuncId::new(1), BARRIER, ft, BlockId::new(0));
    barrier.linkage = Linkage::External;

    let x = ValueId::new(0);
    let acc = ValueId::new(1);
    let mut next = 2u32;
    let mut fresh = || {
        let value = ValueId::new(next);
        next += 1;
        value
    };
    let mut body = vec![
        InstrNode::new(Inst::Alloca {
            ty: Ty::I64,
            count: None,
            align: None,
        })
        .with_result(acc)
        .with_span(span(ALLOCA_LINE, 9)),
        InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: acc,
            value: x,
            align: None,
            volatile: false,
        })
        .with_span(span(STORE_LINE, 5)),
    ];
    let spill_load = fresh();
    let spill_const = fresh();
    let spill_probe = fresh();
    body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::I64,
            ptr: acc,
            align: None,
            volatile: false,
        })
        .with_result(spill_load)
        .with_span(span(SPILL_PROBE_LINE, 13)),
    );
    body.push(const_i64(spill_const, 4096, SPILL_PROBE_LINE));
    body.push(binop(
        BinOp::Add,
        spill_load,
        spill_const,
        spill_probe,
        SPILL_PROBE_LINE,
        17,
    ));
    let mut pressure = Vec::new();
    for idx in 0..PRESSURE_VALUES {
        let constant = fresh();
        let value = fresh();
        body.push(const_i64(constant, 10_000 + i64::from(idx), PRESSURE_LINE));
        body.push(binop(
            BinOp::Add,
            x,
            constant,
            value,
            PRESSURE_LINE,
            17 + idx,
        ));
        pressure.push(value);
    }
    let barrier_result = fresh();
    body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(1),
            args: vec![x],
        })
        .with_result(barrier_result)
        .with_span(span(BARRIER_LINE, 5)),
    );
    for idx in 0..BODY_LINES {
        let line = FIRST_BODY_LINE + idx;
        let load = fresh();
        let step = fresh();
        let sum = fresh();
        body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: acc,
                align: None,
                volatile: false,
            })
            .with_result(load)
            .with_span(span(line, 13)),
        );
        body.push(const_i64(step, i64::from(idx) + 1, line));
        body.push(binop(BinOp::Add, load, step, sum, line, 17));
        body.push(
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: acc,
                value: sum,
                align: None,
                volatile: false,
            })
            .with_span(span(line, 21)),
        );
    }
    let result = fresh();
    body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::I64,
            ptr: acc,
            align: None,
            volatile: false,
        })
        .with_result(result)
        .with_span(span(RESULT_LINE, 13)),
    );
    let tail = fresh();
    let reg_probe = fresh();
    body.push(const_i64(tail, TAIL_CONST, REG_PROBE_LINE));
    body.push(binop(
        BinOp::Add,
        result,
        tail,
        reg_probe,
        REG_PROBE_LINE,
        17,
    ));
    let mut mix = pressure[0];
    for value in pressure.iter().copied().skip(1) {
        let mixed = fresh();
        body.push(binop(BinOp::Xor, mix, value, mixed, RETURN_LINE, 9));
        mix = mixed;
    }
    let with_barrier = fresh();
    let with_mix = fresh();
    let final_value = fresh();
    body.push(binop(
        BinOp::Add,
        reg_probe,
        barrier_result,
        with_barrier,
        RETURN_LINE,
        5,
    ));
    body.push(binop(
        BinOp::Add,
        with_barrier,
        mix,
        with_mix,
        RETURN_LINE,
        5,
    ));
    body.push(binop(
        BinOp::Add,
        with_mix,
        spill_probe,
        final_value,
        RETURN_LINE,
        5,
    ));
    body.push(
        InstrNode::new(Inst::Return {
            values: vec![final_value],
        })
        .with_span(span(RETURN_LINE, 1)),
    );
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(x, Ty::I64)],
        body,
    }];
    module.add_function(func.clone());
    module.add_function(barrier);
    (func, module)
}

/// Source lines any line row may name.
pub fn fixture_lines() -> BTreeSet<u64> {
    let mut lines: BTreeSet<u64> = [
        ALLOCA_LINE,
        STORE_LINE,
        SPILL_PROBE_LINE,
        PRESSURE_LINE,
        BARRIER_LINE,
        RESULT_LINE,
        REG_PROBE_LINE,
        RETURN_LINE,
    ]
    .into_iter()
    .map(u64::from)
    .collect();
    lines.extend((FIRST_BODY_LINE..FIRST_BODY_LINE + BODY_LINES).map(u64::from));
    lines
}

pub fn lir_fixture() -> trust_cg_lower::Function {
    let (func, module) = fixture();
    let names: HashMap<FuncId, String> = module
        .functions
        .iter()
        .map(|f| (f.id, f.name.clone()))
        .collect();
    let (mut lir, _) =
        trust_cg_lower::adapter::translate_function_with_names(&func, &module, &names)
            .expect("adapter should translate the ELF DWARF fixture");
    lir.debug_meta.source_file = Some(FIXTURE_FILE.to_string());
    lir.debug_meta.param_names = vec!["x".to_string()];
    let mut named_spill = false;
    let mut named_reg = false;
    for local in &mut lir.debug_meta.local_variables {
        if local.name == "local_0" {
            local.name = "acc".to_string();
        } else if !named_spill
            && local.decl_line == SPILL_PROBE_LINE
            && local.name.starts_with("value_")
        {
            local.name = "spill_probe".to_string();
            named_spill = true;
        } else if !named_reg
            && local.decl_line == REG_PROBE_LINE
            && local.name.starts_with("value_")
        {
            local.name = "reg_probe".to_string();
            named_reg = true;
        }
    }
    assert!(named_spill && named_reg, "fixture must name both probes");
    lir.debug_meta
        .local_variables
        .retain(|local| matches!(local.name.as_str(), "acc" | "spill_probe" | "reg_probe"));
    lir.debug_meta.local_variables.push(DebugLocalVariable {
        name: "tail_const".to_string(),
        ty: DebugBaseType::I64,
        storage: DebugVariableStorage::ConstantInt(TAIL_CONST as u64),
        decl_line: REG_PROBE_LINE,
    });
    lir
}

/// A second, frameless function so the module places a subprogram at a
/// non-zero text offset.
pub fn lir_fixture_leaf() -> trust_cg_lower::Function {
    let mut module = TrustIrModule::new(LEAF);
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), LEAF, ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            binop(
                BinOp::Mul,
                ValueId::new(0),
                ValueId::new(1),
                ValueId::new(2),
                RESULT_LINE,
                5,
            ),
            binop(
                BinOp::Add,
                ValueId::new(2),
                ValueId::new(0),
                ValueId::new(3),
                REG_PROBE_LINE,
                5,
            ),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            })
            .with_span(span(RETURN_LINE, 1)),
        ],
    }];
    module.add_function(func.clone());
    let (mut lir, _) = trust_cg_lower::translate_function(&func, &module)
        .expect("adapter should translate the leaf fixture");
    lir.debug_meta.source_file = Some(FIXTURE_FILE.to_string());
    lir
}

/// Name of the second, leaf fixture function.
pub const LEAF: &str = "elf_debug_leaf";

/// The value `x` the harnesses pass to the fixture.
pub const HARNESS_ARG: i64 = 7;

/// `spill_barrier(v)` as the C harnesses define it.
pub fn barrier(v: i64) -> i64 {
    v.wrapping_add(1)
}

/// What `elf_debug_fixture(x)` returns (wrapping `i64` arithmetic).
pub fn expected_result(x: i64) -> i64 {
    let spill_probe = x.wrapping_add(4096);
    let mut mix = x.wrapping_add(10_000);
    for idx in 1..i64::from(PRESSURE_VALUES) {
        mix ^= x.wrapping_add(10_000 + idx);
    }
    let acc = (1..=i64::from(BODY_LINES)).fold(x, |acc, step| acc.wrapping_add(step));
    let reg_probe = acc.wrapping_add(TAIL_CONST);
    reg_probe
        .wrapping_add(barrier(x))
        .wrapping_add(mix)
        .wrapping_add(spill_probe)
}

/// `acc` just before body line `FIRST_BODY_LINE + k` executes.
pub fn acc_before_body_line(x: i64, k: u32) -> i64 {
    (1..=i64::from(k)).fold(x, |acc, step| acc.wrapping_add(step))
}

/// Write the Rust source the line table names, so a debugger can list it.
pub fn write_fixture_source(dir: &Path) -> PathBuf {
    let mut lines = vec![String::new(); RETURN_LINE as usize + 1];
    lines[0] = format!("pub extern \"C\" fn {FIXTURE}(x: i64) -> i64 {{");
    lines[(ALLOCA_LINE - 1) as usize] = "    let mut acc = x;".to_string();
    lines[(STORE_LINE - 1) as usize] = "    let acc_ptr = &mut acc as *mut i64;".to_string();
    lines[(SPILL_PROBE_LINE - 1) as usize] =
        "    let spill_probe = unsafe { acc_ptr.read() }.wrapping_add(4096);".to_string();
    lines[(PRESSURE_LINE - 1) as usize] =
        "    let pressure: [i64; 24] = core::array::from_fn(|i| x + 10_000 + i as i64);"
            .to_string();
    lines[(BARRIER_LINE - 1) as usize] =
        "    let barrier = unsafe { spill_barrier(x) };".to_string();
    for k in 0..BODY_LINES {
        lines[(FIRST_BODY_LINE + k - 1) as usize] = format!(
            "    unsafe {{ acc_ptr.write(acc_ptr.read().wrapping_add({})); }}",
            k + 1
        );
    }
    lines[(RESULT_LINE - 1) as usize] = "    let result = unsafe { acc_ptr.read() };".to_string();
    lines[(REG_PROBE_LINE - 1) as usize] =
        "    let reg_probe = result.wrapping_add(tail_const);".to_string();
    lines[(RETURN_LINE - 1) as usize] =
        "    reg_probe + barrier + pressure.iter().fold(0, |m, v| m ^ v) + spill_probe".to_string();
    lines[RETURN_LINE as usize] = "}".to_string();
    for (idx, line) in lines.iter_mut().enumerate() {
        if line.is_empty() {
            *line = format!("// source padding line {}", idx + 1);
        }
    }
    let path = dir.join(FIXTURE_FILE);
    std::fs::write(&path, lines.join("\n")).expect("write fixture source");
    path
}
