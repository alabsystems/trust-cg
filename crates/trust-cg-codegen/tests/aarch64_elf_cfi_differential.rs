// trust-cg-codegen/tests/aarch64_elf_cfi_differential.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! External CFI differential for AArch64 ELF `.eh_frame`.
//!
//! Production module objects for `aarch64-unknown-linux-gnu` at O0-O3 carry
//! one FDE per function. For each function three independent views of the
//! frame are compared at every prologue instruction boundary and over the
//! body:
//!
//! 1. the unwind rows `llvm-dwarfdump --eh-frame` decodes from the emitted
//!    CIE/FDE bytes (CFA rule and every saved register's CFA offset);
//! 2. a simulation of the prologue as disassembled by `llvm-objdump`
//!    (pre-index / offset `STP` saves, `ADD X29, SP, #imm`, `SUB SP`
//!    allocation, `STR XZR, [SP]` probes and the probe loop);
//! 3. the in-crate `FrameLayout` the pipeline reports for the function.
//!
//! Fixtures cover callee-saved GPR pairs with spills across a call, every
//! callee-saved FPR pair (D8-D15, DWARF 72-79), a single FPR pair, frames
//! large enough for unrolled and looped stack probes, and a runtime-sized
//! allocation. Mutation controls corrupt the emitted CFA offset and rename a
//! saved D register to X8 and require the differential to fail.
//!
//! The FDEs describe synchronous unwinding: no epilogue CFI is emitted, so
//! after an epilogue reloads X29 (until its `ret`) the rows no longer
//! describe the frame. The differential measures exactly those windows and
//! requires every mismatching address to lie in one; it does not claim
//! asynchronous (signal or profiler) unwind correctness there.

#[path = "common/llvm_tools.rs"]
mod llvm_tools;

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use llvm_tools::{
    Insn, cleanup, disassemble, elf_section_extent, func_symbols, run_llvm, scratch_dir,
    written_registers,
};
use trust_cg_codegen::frame::FrameLayout;
use trust_cg_codegen::pipeline::{DispatchVerifyMode, OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::function::StackSlotSizeSource;
use trust_cg_lower::function::{
    BasicBlock, Function as LirFunction, Signature as LirSignature, StackSlotInfo,
};
use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
use trust_cg_lower::types::Type as LirType;
use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, CastOp, Constant, FuncId, FuncTy,
    Function as TrustIrFunction, Inst, InstrNode, Linkage, Module as TrustIrModule, Ty, ValueId,
};

const TRIPLE: &str = "aarch64-unknown-linux-gnu";
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const MIB: u32 = 1 << 20;

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

fn translate(module: &TrustIrModule, name: &str) -> LirFunction {
    let func = module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no fixture function {name}"));
    let names = module
        .functions
        .iter()
        .map(|f| (f.id, f.name.clone()))
        .collect();
    trust_cg_lower::translate_function_with_names_and_license(
        func,
        module,
        &names,
        &permit_unlicensed(),
    )
    .unwrap_or_else(|e| panic!("translate {name}: {e:?}"))
    .0
}

fn fbin(op: BinOp, lhs: u32, rhs: u32, result: u32) -> InstrNode {
    InstrNode::new(Inst::BinOp {
        op,
        ty: Ty::F64,
        lhs: ValueId::new(lhs),
        rhs: ValueId::new(rhs),
    })
    .with_result(ValueId::new(result))
}

fn ibin(op: BinOp, lhs: ValueId, rhs: ValueId, result: ValueId) -> InstrNode {
    InstrNode::new(Inst::BinOp {
        op,
        ty: Ty::I64,
        lhs,
        rhs,
    })
    .with_result(result)
}

/// `live_fp(a, b) = a + fmod(a, b)`: `a` lives across the libcall in D8.
fn live_fp() -> LirFunction {
    let mut m = TrustIrModule::new("cfi_live_fp");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::F64, Ty::F64],
            returns: vec![Ty::F64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(0), "cfi_live_fp", ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::F64), (ValueId::new(1), Ty::F64)],
        body: vec![
            fbin(BinOp::FRem, 0, 1, 2),
            fbin(BinOp::FAdd, 0, 2, 3),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    translate(&m, "cfi_live_fp")
}

/// Eight integer and eight `f64` arguments all live across an `fmod`
/// libcall: every callee-saved GPR (X19-X28) and FPR (D8-D15) pair.
fn stress() -> LirFunction {
    let mut m = TrustIrModule::new("cfi_stress");
    let mut params: Vec<Ty> = (0..8).map(|_| Ty::I64).collect();
    params.extend((0..8).map(|_| Ty::F64));
    let ft = m
        .add_func_type(FuncTy {
            params: params.clone(),
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(0), "cfi_stress", ft, BlockId::new(0));
    let mut next = 100u32;
    let mut fresh = || {
        next += 1;
        ValueId::new(next)
    };
    let fr = fresh();
    let mut body = vec![fbin(BinOp::FRem, 8, 9, fr.0)];
    let mut terms: Vec<ValueId> = (0..8).map(ValueId::new).collect();
    for k in 8..16 {
        let cast = fresh();
        body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::FPToSI,
                src_ty: Ty::F64,
                dst_ty: Ty::I64,
                operand: ValueId::new(k),
            })
            .with_result(cast),
        );
        terms.push(cast);
    }
    let fri = fresh();
    body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::FPToSI,
            src_ty: Ty::F64,
            dst_ty: Ty::I64,
            operand: fr,
        })
        .with_result(fri),
    );
    terms.push(fri);
    let mut acc = terms[0];
    for term in &terms[1..] {
        let sum = fresh();
        body.push(ibin(BinOp::Add, acc, *term, sum));
        acc = sum;
    }
    body.push(InstrNode::new(Inst::Return { values: vec![acc] }));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: params
            .iter()
            .enumerate()
            .map(|(i, ty)| (ValueId::new(i as u32), ty.clone()))
            .collect(),
        body,
    }];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    translate(&m, "cfi_stress")
}

/// Twenty-four values live across a call to an external function: callee-
/// saved GPR pairs plus spill slots.
fn spills() -> LirFunction {
    let mut m = TrustIrModule::new("cfi_spills");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(0), "cfi_spills", ft, BlockId::new(0));
    let mut barrier = TrustIrFunction::new(FuncId::new(1), "cfi_barrier", ft, BlockId::new(0));
    barrier.linkage = Linkage::External;
    let x = ValueId::new(0);
    let mut next = 1u32;
    let mut fresh = || {
        next += 1;
        ValueId::new(next)
    };
    let mut body = Vec::new();
    let mut live = Vec::new();
    for idx in 0..24 {
        let constant = fresh();
        let value = fresh();
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int((1000 + idx).into()),
            })
            .with_result(constant),
        );
        body.push(ibin(BinOp::Add, x, constant, value));
        live.push(value);
    }
    let called = fresh();
    body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(1),
            args: vec![x],
        })
        .with_result(called),
    );
    let mut acc = called;
    for value in live {
        let mixed = fresh();
        body.push(ibin(BinOp::Xor, acc, value, mixed));
        acc = mixed;
    }
    body.push(InstrNode::new(Inst::Return { values: vec![acc] }));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(x, Ty::I64)],
        body,
    }];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m.try_add_function(barrier)
        .expect("Module::try_add_function: test fixture");
    translate(&m, "cfi_spills")
}

fn inst(opcode: Opcode, args: Vec<u32>, results: Vec<u32>) -> Instruction {
    Instruction {
        opcode,
        args: args.into_iter().map(Value).collect(),
        results: results.into_iter().map(Value).collect(),
    }
}

/// `f(x) = x + x` through volatile stores at both ends of a `bytes` slot
/// (static frame, probed), or of an `x`-byte runtime slot when `None`.
fn far_end(name: &str, bytes: Option<u32>) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        LirSignature {
            params: vec![LirType::I64],
            returns: vec![LirType::I64],
        },
    );
    func.stack_slots.push(match bytes {
        Some(bytes) => StackSlotInfo::new(bytes, 16),
        None => StackSlotInfo::new_dynamic_with_unit(StackSlotSizeSource::Value(0), 1, 16),
    });
    let store = || Opcode::VolatileStore {
        ty: LirType::I64,
        align: None,
    };
    let load = || Opcode::VolatileLoad {
        ty: LirType::I64,
        align: None,
    };
    let constant = |imm, value| {
        inst(
            Opcode::Iconst {
                ty: LirType::I64,
                imm,
            },
            vec![],
            vec![value],
        )
    };
    let mut instructions = vec![inst(Opcode::StackAddr { slot: 0 }, vec![], vec![1])];
    match bytes {
        Some(bytes) => instructions.push(constant(i64::from(bytes) - 8, 3)),
        None => instructions.extend([constant(-8, 2), inst(Opcode::Iadd, vec![2, 0], vec![3])]),
    }
    instructions.extend([
        inst(Opcode::Iadd, vec![1, 3], vec![4]),
        inst(store(), vec![0, 1], vec![]),
        inst(store(), vec![0, 4], vec![]),
        inst(load(), vec![1], vec![5]),
        inst(load(), vec![4], vec![6]),
        inst(Opcode::Iadd, vec![5, 6], vec![7]),
        inst(Opcode::Return, vec![7], vec![]),
    ]);
    func.blocks.insert(
        Block(0),
        BasicBlock {
            params: vec![(Value(0), LirType::I64)],
            instructions,
            source_locs: vec![],
        },
    );
    func
}

fn fixtures() -> Vec<LirFunction> {
    vec![
        spills(),
        stress(),
        live_fp(),
        far_end("cfi_probe_unrolled", Some(4112)),
        far_end("cfi_probe_looped", Some(MIB)),
        far_end("cfi_probe_large", Some(3 * MIB / 2)),
        far_end("cfi_runtime_alloca", None),
    ]
}

struct CompiledModule {
    object: Vec<u8>,
    layouts: BTreeMap<String, FrameLayout>,
}

fn compile_module(level: OptLevel) -> CompiledModule {
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: level,
        verify_dispatch: DispatchVerifyMode::Off,
        ..PipelineConfig::for_target(TRIPLE)
    });
    let mut functions = Vec::new();
    let mut frame_layouts = Vec::new();
    let mut layouts = BTreeMap::new();
    for lir in fixtures() {
        let (func, metrics) = pipeline
            .prepare_function_with_metrics(&lir, None)
            .unwrap_or_else(|e| panic!("{level:?}: prepare {}: {e}", lir.name));
        let layout = metrics
            .frame_layout
            .clone()
            .unwrap_or_else(|| panic!("{level:?}: {} has no frame layout", lir.name));
        layouts.insert(func.name.clone(), layout);
        frame_layouts.push(metrics.frame_layout);
        functions.push(func);
    }
    let object = pipeline
        .compile_module_emission(&functions, &[], &frame_layouts, &[])
        .unwrap_or_else(|e| panic!("{level:?}: module emission: {e}"))
        .object;
    CompiledModule { object, layouts }
}

// ---------------------------------------------------------------------------
// Frame states
// ---------------------------------------------------------------------------

/// The CFA rule: `SP + n` or `X29 + n`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Cfa {
    Sp(i64),
    Fp(i64),
}

/// CFA rule plus each saved register's `CFA + offset` slot, keyed by DWARF
/// register number.
#[derive(Debug, Clone, PartialEq, Eq)]
struct FrameState {
    cfa: Cfa,
    saved: BTreeMap<u64, i64>,
}

impl FrameState {
    fn entry() -> Self {
        Self {
            cfa: Cfa::Sp(0),
            saved: BTreeMap::new(),
        }
    }
}

/// DWARF register number of an `llvm-dwarfdump` register name (`W19`,
/// `WSP`, `X8`, or an FP/SIMD view such as `D8`/`B8`/`Q8`).
fn dwarf_number(name: &str) -> Option<u64> {
    if name == "WSP" || name == "SP" {
        return Some(31);
    }
    let (class, digits) = name.split_at(name.find(|c: char| c.is_ascii_digit())?);
    let n: u64 = digits.parse().ok()?;
    match class {
        "W" | "X" if n <= 30 => Some(n),
        "B" | "H" | "S" | "D" | "Q" | "V" if n <= 31 => Some(64 + n),
        _ => None,
    }
}

/// One FDE decoded by `llvm-dwarfdump --eh-frame`.
#[derive(Debug, Clone)]
struct Fde {
    pc_begin: u64,
    pc_end: u64,
    rows: Vec<(u64, FrameState)>,
}

fn parse_cfa(text: &str) -> Option<Cfa> {
    let text = text.trim();
    let (reg, offset) = match text.find(['+', '-']) {
        Some(at) => (
            &text[..at],
            text[at..].trim_start_matches('+').parse().ok()?,
        ),
        None => (text, 0),
    };
    match reg {
        "WSP" | "SP" => Some(Cfa::Sp(offset)),
        "W29" | "X29" | "FP" => Some(Cfa::Fp(offset)),
        _ => None,
    }
}

fn parse_row(line: &str) -> Option<(u64, FrameState)> {
    let line = line.trim();
    let (address, rest) = line.split_once(": CFA=")?;
    let address = u64::from_str_radix(address.strip_prefix("0x")?, 16).ok()?;
    let (cfa, regs) = match rest.split_once(": ") {
        Some((cfa, regs)) => (cfa, regs),
        None => (rest, ""),
    };
    let mut state = FrameState {
        cfa: parse_cfa(cfa)?,
        saved: BTreeMap::new(),
    };
    for item in regs.split(", ").filter(|item| !item.is_empty()) {
        let (name, slot) = item.split_once("=[CFA")?;
        let offset: i64 = slot.trim_end_matches(']').parse().ok()?;
        state.saved.insert(dwarf_number(name.trim())?, offset);
    }
    Some((address, state))
}

fn parse_eh_frame(dump: &str) -> Vec<Fde> {
    let mut fdes = Vec::new();
    for line in dump.lines() {
        if line.contains(" FDE ") {
            let range = line.split("pc=").nth(1).expect("FDE pc range");
            let (begin, end) = range.trim().split_once("...").expect("FDE pc range");
            fdes.push(Fde {
                pc_begin: u64::from_str_radix(begin, 16).expect("pc begin"),
                pc_end: u64::from_str_radix(end.trim(), 16).expect("pc end"),
                rows: Vec::new(),
            });
        } else if let Some(fde) = fdes.last_mut()
            && let Some(row) = parse_row(line)
        {
            fde.rows.push(row);
        }
    }
    fdes
}

/// The state an FDE's rows give at `pc` (the last row at or before it).
fn state_at(fde: &Fde, pc: u64) -> Option<&FrameState> {
    fde.rows
        .iter()
        .rev()
        .find(|(address, _)| *address <= pc)
        .map(|(_, state)| state)
}

// ---------------------------------------------------------------------------
// Machine-code prologue simulation
// ---------------------------------------------------------------------------

fn immediate(op: &str) -> Option<i64> {
    let op = op.trim().trim_start_matches('#');
    let (negative, digits) = match op.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, op),
    };
    let value = match digits.strip_prefix("0x") {
        Some(hex) => i64::from_str_radix(hex, 16).ok()?,
        None => digits.parse().ok()?,
    };
    Some(if negative { -value } else { value })
}

/// `[sp, #imm]` / `[sp, #imm]!` / `[sp]` -> `(imm, pre_index)`.
fn sp_address(op: &str) -> Option<(i64, bool)> {
    let pre_index = op.ends_with('!');
    let inner = op
        .trim_end_matches('!')
        .strip_prefix('[')?
        .strip_suffix(']')?;
    let mut parts = inner.split(',').map(str::trim);
    if parts.next()? != "sp" {
        return None;
    }
    let offset = match parts.next() {
        Some(imm) => immediate(imm)?,
        None => 0,
    };
    Some((offset, pre_index))
}

fn shifted_immediate(ops: &[String]) -> Option<i64> {
    let value = immediate(ops.get(2)?)?;
    match ops.get(3).map(String::as_str) {
        None => Some(value),
        Some("lsl #12") => Some(value << 12),
        Some(_) => None,
    }
}

fn reg_bytes(op: &str) -> Option<i64> {
    match op.chars().next()? {
        'x' | 'd' => Some(8),
        'q' => Some(16),
        _ => None,
    }
}

/// Simulate the prologue starting at `insns[0]`. Returns the state before
/// each prologue instruction (keyed by address), the address of the first
/// body instruction, and the state there.
fn simulate_prologue(insns: &[&Insn]) -> (Vec<(u64, FrameState)>, u64, FrameState) {
    let mut state = FrameState::entry();
    let mut sp_off: i64 = 0; // CFA - SP
    let mut before = Vec::new();
    for insn in insns {
        let ops = &insn.operands;
        let m = insn.mnemonic.as_str();
        let mut next = state.clone();
        let mut handled = true;
        match m {
            "stp" | "str" if ops.last().is_some_and(|op| sp_address(op).is_some()) => {
                let (offset, pre_index) = sp_address(ops.last().unwrap()).unwrap();
                let regs = &ops[..ops.len() - 1];
                if regs.iter().all(|r| r == "xzr") {
                    // A stack probe touches the page; it saves nothing.
                } else {
                    let base = if pre_index {
                        sp_off -= offset;
                        if let Cfa::Sp(_) = next.cfa {
                            next.cfa = Cfa::Sp(sp_off);
                        }
                        -sp_off
                    } else {
                        -sp_off + offset
                    };
                    let mut slot = base;
                    for reg in regs {
                        let number = llvm_tools::dwarf_reg(reg).expect("saved register");
                        next.saved.insert(number, slot);
                        slot += reg_bytes(reg).expect("register width");
                    }
                }
            }
            "add" | "mov"
                if ops.first().map(String::as_str) == Some("x29")
                    && ops.get(1).map(String::as_str) == Some("sp") =>
            {
                let imm = if m == "mov" {
                    0
                } else {
                    immediate(&ops[2]).unwrap()
                };
                next.cfa = Cfa::Fp(sp_off - imm);
            }
            "sub"
                if ops.first().map(String::as_str) == Some("sp")
                    && ops.get(1).map(String::as_str) == Some("sp") =>
            {
                let imm = shifted_immediate(ops).expect("sub sp immediate");
                sp_off += imm;
                if let Cfa::Sp(_) = next.cfa {
                    next.cfa = Cfa::Sp(sp_off);
                }
            }
            // Probe-loop counter set-up and iteration: X16 only, and the
            // loop runs after X29 already anchors the CFA.
            "mov" | "movz" | "movk" | "subs" | "b.ne"
                if ops.first().map(String::as_str) == Some("x16") || m == "b.ne" =>
            {
                assert!(
                    matches!(state.cfa, Cfa::Fp(_)),
                    "a probe loop must run after X29 anchors the CFA: {insn:?}"
                );
            }
            _ => handled = false,
        }
        if !handled {
            return (before, insn.address, state);
        }
        before.push((insn.address, state.clone()));
        state = next;
    }
    panic!("function ended inside its prologue");
}

/// The frame the in-crate `FrameLayout` describes once the prologue ran:
/// FP/LR at the top of the callee-saved area (`X29 = CFA - 16`), extra pairs
/// below it, each stored with its higher-numbered register lower.
fn model_state(layout: &FrameLayout) -> FrameState {
    assert!(
        layout.uses_frame_pointer,
        "Linux frames keep a frame record"
    );
    // X0-X30 encode as 0-30 and V0-V31 as 64-95: exactly their AArch64
    // DWARF numbers ("DWARF for the Arm 64-bit Architecture", table 2).
    let dwarf = |reg: trust_cg_ir::regs::PReg, fpr: bool| {
        let enc = u64::from(reg.encoding());
        assert_eq!(fpr, enc >= 64, "pair class vs register {reg:?}");
        enc
    };
    let mut saved = BTreeMap::new();
    for (i, pair) in layout.callee_saved_pairs.iter().enumerate() {
        let i = i as i64;
        if i == 0 {
            saved.insert(dwarf(pair.reg1, pair.is_fpr), -16);
            saved.insert(dwarf(pair.reg2, pair.is_fpr), -8);
        } else {
            saved.insert(dwarf(pair.reg2, pair.is_fpr), -16 * (i + 1));
            saved.insert(dwarf(pair.reg1, pair.is_fpr), -(16 * i + 8));
        }
    }
    FrameState {
        cfa: Cfa::Fp(16),
        saved,
    }
}

/// Epilogue windows: addresses after an instruction reloads X29 and up to
/// the block's `ret` / tail branch, where synchronous-only CFI no longer
/// describes the frame.
fn epilogue_windows(body: &[&Insn]) -> Vec<(u64, u64)> {
    let mut windows = Vec::new();
    let mut open: Option<u64> = None;
    for insn in body {
        if let Some(start) = open
            && matches!(insn.mnemonic.as_str(), "ret" | "b" | "br")
        {
            windows.push((start, insn.address + 4));
            open = None;
            continue;
        }
        if open.is_none() && written_registers(insn).contains(&29) && insn.mnemonic != "bl" {
            open = Some(insn.address + 4);
        }
    }
    windows
}

#[derive(Debug, Default)]
struct Summary {
    functions: usize,
    prologue_points: usize,
    body_points: usize,
    epilogue_points: usize,
    fpr_saves: usize,
    probe_loops: usize,
}

/// Compare the three views for every FDE of `object`; `Err` describes the
/// first disagreement.
fn differential(
    context: &str,
    path: &Path,
    layouts: &BTreeMap<String, FrameLayout>,
) -> Result<Summary, String> {
    let dump = run_llvm("llvm-dwarfdump", &["--eh-frame"], path);
    if dump.contains("[stderr]") {
        return Err(format!("{context}: llvm-dwarfdump warnings:\n{dump}"));
    }
    let fdes = parse_eh_frame(&dump);
    let symbols = func_symbols(path);
    let insns = disassemble(path);
    let mut summary = Summary::default();
    if fdes.len() != layouts.len() {
        return Err(format!(
            "{context}: {} FDEs for {} functions:\n{dump}",
            fdes.len(),
            layouts.len()
        ));
    }
    for (name, layout) in layouts {
        let symbol = symbols
            .iter()
            .find(|s| s.name == *name)
            .ok_or_else(|| format!("{context}: no symbol {name}"))?;
        let fde = fdes
            .iter()
            .find(|f| f.pc_begin == symbol.value)
            .ok_or_else(|| format!("{context}: no FDE starts at {name} ({:#x})", symbol.value))?;
        if fde.pc_end > symbol.value + symbol.size {
            return Err(format!("{context}: {name} FDE {fde:?} exceeds its symbol"));
        }
        let code: Vec<&Insn> = insns
            .iter()
            .filter(|i| i.address >= fde.pc_begin && i.address < fde.pc_end)
            .collect();
        let (prologue, body_start, final_state) = simulate_prologue(&code);
        for (address, expected) in &prologue {
            let decoded = state_at(fde, *address)
                .ok_or_else(|| format!("{context}: {name} has no row at {address:#x}"))?;
            if decoded != expected {
                return Err(format!(
                    "{context}: {name} at {address:#x}: CFI {decoded:?} but the prologue gives \
                     {expected:?}"
                ));
            }
            summary.prologue_points += 1;
        }
        let model = model_state(layout);
        if final_state != model {
            return Err(format!(
                "{context}: {name} prologue ends in {final_state:?} but FrameLayout gives {model:?}"
            ));
        }
        if let Some((address, _)) = fde.rows.iter().find(|(address, _)| *address > body_start) {
            return Err(format!(
                "{context}: {name} has a CFI row inside its body at {address:#x}"
            ));
        }
        let body: Vec<&Insn> = code
            .iter()
            .copied()
            .filter(|i| i.address >= body_start)
            .collect();
        let windows = epilogue_windows(&body);
        for insn in &body {
            let decoded = state_at(fde, insn.address)
                .ok_or_else(|| format!("{context}: {name} has no row at {:#x}", insn.address))?;
            let in_epilogue = windows
                .iter()
                .any(|(lo, hi)| (*lo..*hi).contains(&insn.address));
            if in_epilogue {
                // Only the frame-record reload's successors and the return
                // are here; everything they do is undo the frame.
                if !matches!(
                    insn.mnemonic.as_str(),
                    "ldp" | "ldr" | "add" | "ret" | "b" | "br"
                ) {
                    return Err(format!("{context}: {name} epilogue window holds {insn:?}"));
                }
                summary.epilogue_points += 1;
            } else {
                if *decoded != model {
                    return Err(format!(
                        "{context}: {name} at {:#x}: CFI {decoded:?} but the frame is {model:?}",
                        insn.address
                    ));
                }
                let opens_window = windows.iter().any(|(lo, _)| *lo == insn.address + 4);
                if written_registers(insn).contains(&29) && insn.mnemonic != "bl" && !opens_window {
                    return Err(format!(
                        "{context}: {name} body rewrites X29 outside an epilogue: {insn:?}"
                    ));
                }
                summary.body_points += 1;
            }
        }
        if windows.is_empty() {
            return Err(format!("{context}: {name} has no epilogue"));
        }
        summary.fpr_saves += model.saved.keys().filter(|reg| **reg >= 64).count();
        summary.probe_loops += usize::from(code.iter().any(|i| i.mnemonic == "b.ne"));
        summary.functions += 1;
    }
    Ok(summary)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[test]
fn eh_frame_rows_match_prologues_and_frame_layouts_at_every_level() {
    let dir = scratch_dir("aarch64_elf_cfi");
    for level in LEVELS {
        let context = format!("{level:?}");
        let module = compile_module(level);
        let path = dir.join(format!("cfi_{level:?}.o"));
        fs::write(&path, &module.object).expect("write object");
        let summary =
            differential(&context, &path, &module.layouts).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(summary.functions, fixtures().len(), "{context}");
        // The stress fixture saves all of D8-D15 and live_fp at least D8.
        assert!(summary.fpr_saves >= 9, "{context}: {summary:?}");
        assert!(
            summary.probe_loops >= 2,
            "{context}: looped probes {summary:?}"
        );
        assert!(
            summary.prologue_points > 0 && summary.body_points > 0,
            "{context}"
        );
        eprintln!("{context}: {summary:?}");
    }
    cleanup(&dir);
}

/// Byte offset of the first FDE's first `DW_CFA_def_cfa_offset` operand in
/// the object's `.eh_frame`, read from the independent dump.
fn find_in_eh_frame(object: &[u8], pattern: &[u8]) -> usize {
    let (offset, size) = elf_section_extent(object, ".eh_frame").expect(".eh_frame");
    let at = object[offset..offset + size]
        .windows(pattern.len())
        .position(|w| w == pattern)
        .unwrap_or_else(|| panic!("pattern {pattern:02x?} not in .eh_frame"));
    offset + at
}

#[test]
fn corrupted_cfa_offset_is_caught_by_the_differential() {
    let dir = scratch_dir("aarch64_elf_cfi_cfa_mutation");
    let module = compile_module(OptLevel::O2);
    let good = dir.join("good.o");
    fs::write(&good, &module.object).expect("write");
    differential("good", &good, &module.layouts).expect("unmutated object must agree");

    // The first FDE (cfi_spills) opens with advance_loc(1) then
    // DW_CFA_def_cfa_offset <callee-saved area>; move the CFA 16 bytes.
    let csa = module.layouts["cfi_spills"].callee_saved_area_size;
    let mut object = module.object.clone();
    let at = find_in_eh_frame(&object, &[0x41, 0x0e, csa as u8]);
    object[at + 2] = (csa + 16) as u8;
    let bad = dir.join("cfa.o");
    fs::write(&bad, &object).expect("write");
    let err = differential("cfa mutation", &bad, &module.layouts)
        .expect_err("a wrong CFA offset must disagree with the prologue");
    assert!(err.contains("cfi_spills"), "{err}");
    cleanup(&dir);
}

#[test]
fn fpr_save_renamed_to_x8_is_caught_by_the_differential() {
    let dir = scratch_dir("aarch64_elf_cfi_fpr_mutation");
    let module = compile_module(OptLevel::O1);
    // DW_CFA_offset_extended D8 (DWARF 72): the correct encoding for an FPR.
    let mut object = module.object.clone();
    let at = find_in_eh_frame(&object, &[0x05, 72]);
    // The pre-fix encoding named the save DW_CFA_offset|8 = X8; rename the
    // register operand to 8 in place (same length) to reproduce it.
    object[at + 1] = 8;
    let bad = dir.join("fpr.o");
    fs::write(&bad, &object).expect("write");
    let err = differential("fpr mutation", &bad, &module.layouts)
        .expect_err("an FPR save described as X8 must disagree");
    assert!(err.contains("72") || err.contains("8:"), "{err}");
    cleanup(&dir);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its lowerings state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
