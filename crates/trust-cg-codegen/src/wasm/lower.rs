// trust-cg-codegen/wasm/lower.rs - trust-ir -> WebAssembly lowering
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! trust-ir → WebAssembly lowering.
//!
//! Consumes **trust-ir** directly (the contract IR — no new IR, no intermediate
//! SSA) and builds a [`WasmModule`] via [`super::encode`].
//!
//! Supported subset (grows by slice):
//! - **Slice 0** — straight-line `Const` + `BinOp` add/sub/mul over i32/i64 + `Return`.
//! - **Slice 1** — `ICmp` comparisons and structured `if/else`.
//! - **Slice 1b** — **reducible loops** and general structured control flow, via
//!   the dominator-tree relooper of Ramsey, *"Beyond Relooper: Recursive
//!   Translation of Unstructured Control Flow to Structured Control Flow"*
//!   (ICFP 2022). The CFG is structured by recursing the dominator tree in
//!   reverse-postorder: a **loop header** (target of a back-edge) opens a wasm
//!   `loop`; a **merge node** (≥2 forward predecessors) opens a wasm `block`
//!   whose `end` is the join; each edge becomes either an inline continuation,
//!   a `br` to a loop label (back-edge / "continue"), or a `br` to a block
//!   label (forward merge / "break"/join). Branch depths are computed from an
//!   absolute open-label count so the enclosing `if` is counted correctly.
//!
//! Block-parameter SSA is lowered to wasm locals: an edge's args are written
//! into the target block's param locals before control transfers (phi
//! resolution). Writes are permutation-safe (all reads pushed, then sets in
//! reverse) so a back-edge that swaps induction variables is correct.
//!
//! Fail-closed: irreducible / multi-entry loops, `Switch` (Slice 1c), and any
//! out-of-subset instruction are rejected explicitly, never mis-lowered.

use std::collections::{HashMap, HashSet};
use std::fmt;

use trust_ir::{
    BinOp, BlockId, CallingConv, CastOp, Constant, FCmpOp, FuncId, FuncTyId, Function, ICmpOp,
    Inst, Module, Ty, UnOp, ValueId,
};

/// Per-callee call target: its wasm function index and (optional) return type.
type CallTargets = HashMap<FuncId, (u32, Option<ValType>)>;
/// trust-ir signature → wasm type-section index (for `call_indirect`).
type SigTypes = HashMap<FuncTyId, u32>;

use super::encode::{
    FuncBody, FuncType, ValType, WasmModule, emit_i32_const, emit_local_get, emit_memarg, op,
    write_sleb128, write_uleb128,
};

/// Errors from lowering trust-ir to wasm. Fail-closed: anything outside the
/// supported subset is reported explicitly, never silently mis-lowered.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WasmLowerError {
    /// A type with no wasm value-type mapping (in this slice).
    UnsupportedType(String),
    /// An instruction outside the supported subset.
    UnsupportedInst(String),
    /// Control flow outside the supported subset (irreducible, switch, …).
    UnsupportedControlFlow(String),
    /// An operand referencing a value that was never defined/bound.
    UndefinedValue(String),
    /// A branch references a block id not present in the function.
    UndefinedBlock(String),
    /// Edge args / block params length mismatch (malformed SSA).
    ArityMismatch(String),
    /// A function whose declared entry block is absent.
    MissingEntry(String),
}

impl fmt::Display for WasmLowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use WasmLowerError::*;
        match self {
            UnsupportedType(m) => write!(f, "unsupported type for wasm lowering: {m}"),
            UnsupportedInst(m) => write!(f, "unsupported instruction for wasm lowering: {m}"),
            UnsupportedControlFlow(m) => {
                write!(f, "unsupported control flow for wasm lowering: {m}")
            }
            UndefinedValue(m) => write!(f, "use of undefined value in wasm lowering: {m}"),
            UndefinedBlock(m) => write!(f, "branch to undefined block in wasm lowering: {m}"),
            ArityMismatch(m) => write!(f, "edge arg / block-param arity mismatch: {m}"),
            MissingEntry(m) => write!(f, "function has no entry block: {m}"),
        }
    }
}

impl std::error::Error for WasmLowerError {}

/// Map a trust-ir scalar type to a wasm value type. Pointer-like types are
/// wasm32 addresses (i32).
fn valtype_of(ty: &Ty) -> Result<ValType, WasmLowerError> {
    match ty {
        Ty::I32 | Ty::U32 | Ty::Bool => Ok(ValType::I32),
        Ty::I64 | Ty::U64 => Ok(ValType::I64),
        Ty::F32 => Ok(ValType::F32),
        Ty::F64 => Ok(ValType::F64),
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) | Ty::Rc(_) => {
            Ok(ValType::I32)
        }
        other => Err(WasmLowerError::UnsupportedType(format!("{other:?}"))),
    }
}

/// The load/store opcode pair and natural-alignment exponent for a value type.
fn mem_ops(vt: ValType) -> Result<(u8, u8, u32), WasmLowerError> {
    match vt {
        ValType::I32 => Ok((op::I32_LOAD, op::I32_STORE, 2)),
        ValType::I64 => Ok((op::I64_LOAD, op::I64_STORE, 3)),
        other => Err(WasmLowerError::UnsupportedInst(format!(
            "load/store of {other:?} (Slice 2a: i32/i64/pointer)"
        ))),
    }
}

/// Round `n` up to a multiple of `align` (a power of two).
fn align_up(n: u32, align: u32) -> u32 {
    (n + align - 1) & !(align - 1)
}

/// Wasm opcode for an integer `BinOp` at a value type (Slice 0 subset).
fn int_binop_opcode(bin: BinOp, vt: ValType) -> Result<u8, WasmLowerError> {
    let code = match (bin, vt) {
        (BinOp::Add, ValType::I32) => op::I32_ADD,
        (BinOp::Sub, ValType::I32) => op::I32_SUB,
        (BinOp::Mul, ValType::I32) => op::I32_MUL,
        (BinOp::SDiv, ValType::I32) => op::I32_DIV_S,
        (BinOp::UDiv, ValType::I32) => op::I32_DIV_U,
        (BinOp::SRem, ValType::I32) => op::I32_REM_S,
        (BinOp::URem, ValType::I32) => op::I32_REM_U,
        (BinOp::Add, ValType::I64) => op::I64_ADD,
        (BinOp::Sub, ValType::I64) => op::I64_SUB,
        (BinOp::Mul, ValType::I64) => op::I64_MUL,
        (BinOp::SDiv, ValType::I64) => op::I64_DIV_S,
        (BinOp::UDiv, ValType::I64) => op::I64_DIV_U,
        (BinOp::SRem, ValType::I64) => op::I64_REM_S,
        (BinOp::URem, ValType::I64) => op::I64_REM_U,
        (BinOp::And, ValType::I32) => op::I32_AND,
        (BinOp::Or, ValType::I32) => op::I32_OR,
        (BinOp::Xor, ValType::I32) => op::I32_XOR,
        (BinOp::Shl, ValType::I32) => op::I32_SHL,
        (BinOp::AShr, ValType::I32) => op::I32_SHR_S,
        (BinOp::LShr, ValType::I32) => op::I32_SHR_U,
        (BinOp::And, ValType::I64) => op::I64_AND,
        (BinOp::Or, ValType::I64) => op::I64_OR,
        (BinOp::Xor, ValType::I64) => op::I64_XOR,
        (BinOp::Shl, ValType::I64) => op::I64_SHL,
        (BinOp::AShr, ValType::I64) => op::I64_SHR_S,
        (BinOp::LShr, ValType::I64) => op::I64_SHR_U,
        // IEEE-754 float arithmetic (round-to-nearest-ties-to-even).
        (BinOp::FAdd, ValType::F32) => op::F32_ADD,
        (BinOp::FSub, ValType::F32) => op::F32_SUB,
        (BinOp::FMul, ValType::F32) => op::F32_MUL,
        (BinOp::FDiv, ValType::F32) => op::F32_DIV,
        (BinOp::FAdd, ValType::F64) => op::F64_ADD,
        (BinOp::FSub, ValType::F64) => op::F64_SUB,
        (BinOp::FMul, ValType::F64) => op::F64_MUL,
        (BinOp::FDiv, ValType::F64) => op::F64_DIV,
        _ => {
            return Err(WasmLowerError::UnsupportedInst(format!(
                "BinOp::{bin:?} on {vt:?} (supported: int add/sub/mul/div/rem/and/or/xor/shl/shr; \
                 float add/sub/mul/div)"
            )));
        }
    };
    Ok(code)
}

/// Wasm opcode for an integer comparison `ICmp` at an operand value type.
/// Result is always i32 (a wasm boolean).
fn icmp_opcode(cmp: ICmpOp, vt: ValType) -> Result<u8, WasmLowerError> {
    use ICmpOp::*;
    use ValType::{I32, I64};
    let code = match (cmp, vt) {
        (Eq, I32) => op::I32_EQ,
        (Ne, I32) => op::I32_NE,
        (Slt, I32) => op::I32_LT_S,
        (Sle, I32) => op::I32_LE_S,
        (Sgt, I32) => op::I32_GT_S,
        (Sge, I32) => op::I32_GE_S,
        (Ult, I32) => op::I32_LT_U,
        (Ule, I32) => op::I32_LE_U,
        (Ugt, I32) => op::I32_GT_U,
        (Uge, I32) => op::I32_GE_U,
        (Eq, I64) => op::I64_EQ,
        (Ne, I64) => op::I64_NE,
        (Slt, I64) => op::I64_LT_S,
        (Sle, I64) => op::I64_LE_S,
        (Sgt, I64) => op::I64_GT_S,
        (Sge, I64) => op::I64_GE_S,
        (Ult, I64) => op::I64_LT_U,
        (Ule, I64) => op::I64_LE_U,
        (Ugt, I64) => op::I64_GT_U,
        (Uge, I64) => op::I64_GE_U,
        _ => {
            return Err(WasmLowerError::UnsupportedInst(format!(
                "ICmp::{cmp:?} on {vt:?} (supported: integer comparisons on i32/i64)"
            )));
        }
    };
    Ok(code)
}

/// Look up the wasm local slot bound to an SSA value.
fn slot(
    locals: &HashMap<ValueId, (u32, ValType)>,
    v: ValueId,
) -> Result<(u32, ValType), WasmLowerError> {
    locals
        .get(&v)
        .copied()
        .ok_or_else(|| WasmLowerError::UndefinedValue(format!("{v:?}")))
}

/// The wasm value type produced by a result-bearing instruction.
fn result_valtype(
    inst: &Inst,
    call_targets: &CallTargets,
    module: &Module,
) -> Result<ValType, WasmLowerError> {
    match inst {
        Inst::BinOp { ty, .. } => valtype_of(ty),
        // Every supported UnOp (Neg/Not/CtPop, FNeg/FAbs/FSqrt/FCeil/FFloor/
        // FTrunc) returns a value of the operand type.
        Inst::UnOp { ty, .. } => valtype_of(ty),
        Inst::ICmp { .. } => Ok(ValType::I32),
        Inst::FCmp { .. } => Ok(ValType::I32), // wasm float compares yield i32 0/1
        Inst::Cast { dst_ty, .. } => valtype_of(dst_ty),
        // A function-pointer constant is a table index (i32).
        Inst::Const {
            value: Constant::FnDef(_),
            ..
        } => Ok(ValType::I32),
        Inst::Const { ty, .. } => valtype_of(ty),
        Inst::Alloca { .. } => Ok(ValType::I32), // a pointer (wasm32 address)
        Inst::GEP { .. } => Ok(ValType::I32),    // a pointer (wasm32 address)
        Inst::Load { ty, .. } => valtype_of(ty),
        Inst::Call { callee, .. } => match call_targets.get(callee) {
            Some((_, Some(ret))) => Ok(*ret),
            Some((_, None)) => Err(WasmLowerError::UnsupportedInst(format!(
                "Call to {callee:?} returns no value but its result is used"
            ))),
            None => Err(WasmLowerError::UnsupportedInst(format!(
                "Call to unknown {callee:?}"
            ))),
        },
        Inst::CallIndirect { sig, .. } => match module.func_type(*sig) {
            Some(ft) => match ft.returns.first() {
                Some(ret) => valtype_of(ret),
                None => Err(WasmLowerError::UnsupportedInst(
                    "indirect call result used but signature returns void".to_string(),
                )),
            },
            None => Err(WasmLowerError::UnsupportedInst(format!(
                "unknown signature {sig:?}"
            ))),
        },
        other => Err(WasmLowerError::UnsupportedInst(format!(
            "result-producing {other:?}"
        ))),
    }
}

/// Run-length encode local declarations into wasm `(count, type)` runs.
fn run_length_encode(types: &[ValType]) -> Vec<(u32, ValType)> {
    let mut runs: Vec<(u32, ValType)> = Vec::new();
    for &vt in types {
        match runs.last_mut() {
            Some((count, last)) if *last == vt => *count += 1,
            _ => runs.push((1, vt)),
        }
    }
    runs
}

fn first_result(node: &trust_ir::InstrNode, func_name: &str) -> Result<ValueId, WasmLowerError> {
    node.results.first().copied().ok_or_else(|| {
        WasmLowerError::UnsupportedInst(format!("value op without result in `{func_name}`"))
    })
}

/// WebAssembly EH is not wired. Scan the complete function, including
/// unreachable blocks and zero-result nodes, before CFG/local lowering so no
/// incidental reachability or arity behavior can hide an EH instruction.
fn reject_unwired_eh_instructions(func: &Function) -> Result<(), WasmLowerError> {
    for block in &func.blocks {
        for node in &block.body {
            if matches!(
                node.inst,
                Inst::Invoke { .. } | Inst::LandingPad { .. } | Inst::Resume { .. }
            ) {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "{:?} in `{}` block {:?}: WebAssembly EH/LSDA/personality lowering is not wired",
                    node.inst, func.name, block.id
                )));
            }
        }
    }
    Ok(())
}

/// The terminator instruction of a block (its last instruction).
fn terminator_of(func: &Function, idx: usize) -> Result<&Inst, WasmLowerError> {
    match func.blocks[idx].body.last() {
        Some(node) if node.inst.is_terminator() => Ok(&node.inst),
        _ => Err(WasmLowerError::UnsupportedControlFlow(format!(
            "block {idx} of `{}` does not end in a terminator",
            func.name
        ))),
    }
}

/// An open wasm structured-control label, for branch-depth resolution.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Frame {
    /// A `loop` opened for a header block; `br` to it re-iterates (continue).
    Loop(usize),
    /// A `block` opened for a merge block; `br` to it jumps to the join (break).
    Block(usize),
}

/// Per-function lowering state.
struct Lowering<'a> {
    func: &'a Function,
    /// The enclosing trust-ir module, for type-layout queries (sizes/offsets).
    module: &'a Module,
    /// FuncId → (wasm function index, return type) for direct calls.
    call_targets: &'a CallTargets,
    /// trust-ir signature → wasm type index, for `call_indirect`.
    sig_types: &'a SigTypes,
    block_index: HashMap<BlockId, usize>,
    /// Dominator-tree children, each sorted by rpo_index ascending.
    dom_children: Vec<Vec<usize>>,
    /// Block is the target of a back-edge (loop header).
    is_header: Vec<bool>,
    /// Block has ≥2 forward predecessors (merge / join).
    is_merge: Vec<bool>,
    /// Recorded back-edges (source, target).
    back_edges: HashSet<(usize, usize)>,
    locals: HashMap<ValueId, (u32, ValType)>,
    param_types: Vec<ValType>,
    declared_locals: Vec<ValType>,
    next_local: u32,
    code: Vec<u8>,
    result_types: Option<Vec<ValType>>,
    /// Open structured-control labels, innermost last (for `br` resolution).
    context: Vec<(Frame, u32)>,
    /// Count of currently-open wasm labels (loop/block/if) — the `br` depth base.
    open_labels: u32,
    /// Blocks already emitted (defensive once-only guard).
    emitted: HashSet<usize>,
    /// The module's shadow stack-pointer global, if memory is in use.
    sp_global: Option<u32>,
    /// Byte offset within the frame for each `Alloca` result.
    alloca_offsets: HashMap<ValueId, u32>,
    /// Integer-constant value for each `Const` result (for constant GEP indices).
    const_ints: HashMap<ValueId, i64>,
    /// Total frame size in bytes (0 ⇒ no frame / no prologue).
    frame_size: u32,
    /// Local holding the caller's stack pointer (restored on return).
    saved_sp_local: u32,
    /// Local holding this frame's base address (`alloca` = base + offset).
    frame_base_local: u32,
}

/// Linear-memory layout: one 64KiB page; the shadow stack grows down from the
/// top. Plenty for the scalar frames Slice 2a produces.
const STACK_PAGES: u32 = 1;
const STACK_TOP: i64 = 65536;

impl<'a> Lowering<'a> {
    fn build(
        func: &'a Function,
        module: &'a Module,
        sp_global: Option<u32>,
        call_targets: &'a CallTargets,
        sig_types: &'a SigTypes,
    ) -> Result<Self, WasmLowerError> {
        let n = func.blocks.len();
        let block_index: HashMap<BlockId, usize> = func
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| (b.id, i))
            .collect();
        let idx_of = |b: BlockId| -> Result<usize, WasmLowerError> {
            block_index
                .get(&b)
                .copied()
                .ok_or_else(|| WasmLowerError::UndefinedBlock(format!("{b:?}")))
        };

        // Successors from terminators (fail-closed on Switch / non-branch).
        let mut succs: Vec<Vec<usize>> = Vec::with_capacity(n);
        for i in 0..n {
            let s = match terminator_of(func, i)? {
                Inst::Return { .. } | Inst::Unreachable => vec![],
                Inst::Br { target, .. } => vec![idx_of(*target)?],
                Inst::CondBr {
                    then_target,
                    else_target,
                    ..
                } => {
                    vec![idx_of(*then_target)?, idx_of(*else_target)?]
                }
                Inst::Switch { default, cases, .. } => {
                    let mut s = vec![idx_of(*default)?];
                    for c in cases {
                        s.push(idx_of(c.target)?);
                    }
                    s
                }
                other => {
                    return Err(WasmLowerError::UnsupportedControlFlow(format!(
                        "non-branch terminator {other:?}"
                    )));
                }
            };
            succs.push(s);
        }

        let entry = idx_of(func.entry)?;
        let (rpo_index, back_edges) = Self::reverse_postorder(&succs, entry, n);

        // Forward predecessors (exclude back-edges): edge (p, b) where not a back-edge.
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (p, ss) in succs.iter().enumerate() {
            for &b in ss {
                if !back_edges.contains(&(p, b)) {
                    preds[b].push(p);
                }
            }
        }

        let idom = Self::compute_idom(&preds, &rpo_index, entry, n);

        // Reducibility: every back-edge (u,v) must have v dominate u.
        for &(u, v) in &back_edges {
            if !Self::dominates(&idom, v, u, entry) {
                return Err(WasmLowerError::UnsupportedControlFlow(format!(
                    "irreducible control flow (multi-entry loop) in `{}`",
                    func.name
                )));
            }
        }

        // Merge nodes: ≥2 forward predecessors. Loop headers: back-edge targets.
        let is_merge: Vec<bool> = (0..n).map(|b| preds[b].len() >= 2).collect();
        let mut is_header = vec![false; n];
        for &(_, v) in &back_edges {
            is_header[v] = true;
        }

        // Integer constants, for resolving constant GEP (field) indices.
        let mut const_ints: HashMap<ValueId, i64> = HashMap::new();
        for block in &func.blocks {
            for node in &block.body {
                if let Inst::Const {
                    value: Constant::Int(v),
                    ..
                } = &node.inst
                    && let Some(r) = node.results.first()
                {
                    const_ints.insert(*r, *v as i64);
                }
            }
        }

        // Dominator-tree children, sorted by rpo_index ascending.
        let mut dom_children: Vec<Vec<usize>> = vec![Vec::new(); n];
        for c in 0..n {
            if c != entry && rpo_index[c] != usize::MAX {
                dom_children[idom[c]].push(c);
            }
        }
        for kids in &mut dom_children {
            kids.sort_by_key(|&c| rpo_index[c]);
        }

        Ok(Self {
            func,
            module,
            call_targets,
            sig_types,
            block_index,
            dom_children,
            is_header,
            is_merge,
            back_edges,
            locals: HashMap::new(),
            param_types: Vec::new(),
            declared_locals: Vec::new(),
            next_local: 0,
            code: Vec::new(),
            result_types: None,
            context: Vec::new(),
            open_labels: 0,
            emitted: HashSet::new(),
            sp_global,
            alloca_offsets: HashMap::new(),
            const_ints,
            frame_size: 0,
            saved_sp_local: 0,
            frame_base_local: 0,
        })
    }

    /// Pre-pass: lay out one stack frame for all `Alloca`s in the function
    /// (LLVM-style, hoisted to entry so allocas in loops reuse the slot). Each
    /// alloca gets a naturally-aligned offset; the frame is rounded to 8 bytes.
    /// If any alloca exists, two helper locals (saved SP, frame base) are
    /// reserved and the module's stack-pointer global is required.
    fn compute_frame(&mut self) -> Result<(), WasmLowerError> {
        let mut offset: u32 = 0;
        for block in &self.func.blocks {
            for node in &block.body {
                if let Inst::Alloca { ty, count, .. } = &node.inst {
                    if count.is_some() {
                        return Err(WasmLowerError::UnsupportedInst(
                            "array Alloca with a dynamic count (Slice 2b)".to_string(),
                        ));
                    }
                    // wasm allows unaligned access, so 8-byte slot alignment is
                    // a cleanliness choice, not a correctness requirement.
                    let size = self.size_of(ty)?;
                    offset = align_up(offset, 8);
                    let result = first_result(node, &self.func.name)?;
                    self.alloca_offsets.insert(result, offset);
                    offset += size;
                }
            }
        }
        if offset == 0 {
            return Ok(());
        }
        if self.sp_global.is_none() {
            return Err(WasmLowerError::UnsupportedInst(
                "function allocates but no stack-pointer global was provisioned".to_string(),
            ));
        }
        self.frame_size = align_up(offset, 8);
        self.saved_sp_local = self.next_local;
        self.declared_locals.push(ValType::I32);
        self.frame_base_local = self.next_local + 1;
        self.declared_locals.push(ValType::I32);
        self.next_local += 2;
        Ok(())
    }

    /// Emit the frame prologue: save the caller SP, carve out this frame, and
    /// publish the new SP. No-op when the function has no frame.
    fn emit_prologue(&mut self) {
        if self.frame_size == 0 {
            return;
        }
        let sp = self.sp_global.expect("frame implies sp_global");
        self.code.push(op::GLOBAL_GET);
        write_uleb128(&mut self.code, u64::from(sp));
        self.emit_local_set(self.saved_sp_local);
        emit_local_get(&mut self.code, self.saved_sp_local);
        emit_i32_const(&mut self.code, self.frame_size as i32);
        self.code.push(op::I32_SUB);
        self.code.push(op::LOCAL_TEE);
        write_uleb128(&mut self.code, u64::from(self.frame_base_local));
        self.code.push(op::GLOBAL_SET);
        write_uleb128(&mut self.code, u64::from(sp));
    }

    /// Iterative DFS from `entry`: records back-edges (retreating edges whose
    /// target is on the current path) and returns a reverse-postorder index
    /// (`usize::MAX` for unreachable blocks).
    fn reverse_postorder(
        succs: &[Vec<usize>],
        entry: usize,
        n: usize,
    ) -> (Vec<usize>, HashSet<(usize, usize)>) {
        let mut visited = vec![false; n];
        let mut on_path = vec![false; n];
        let mut postorder: Vec<usize> = Vec::new();
        let mut back_edges: HashSet<(usize, usize)> = HashSet::new();

        enum Step {
            Enter(usize),
            Exit(usize),
        }
        let mut stack = vec![Step::Enter(entry)];
        while let Some(step) = stack.pop() {
            match step {
                Step::Enter(u) => {
                    if visited[u] {
                        continue;
                    }
                    visited[u] = true;
                    on_path[u] = true;
                    stack.push(Step::Exit(u));
                    for &v in succs[u].iter().rev() {
                        if on_path[v] {
                            back_edges.insert((u, v));
                        } else if !visited[v] {
                            stack.push(Step::Enter(v));
                        }
                    }
                }
                Step::Exit(u) => {
                    on_path[u] = false;
                    postorder.push(u);
                }
            }
        }

        let mut rpo_index = vec![usize::MAX; n];
        for (pos, &block) in postorder.iter().rev().enumerate() {
            rpo_index[block] = pos;
        }
        (rpo_index, back_edges)
    }

    /// Cooper-Harvey-Kennedy iterative dominance over reverse-postorder.
    fn compute_idom(
        preds: &[Vec<usize>],
        rpo_index: &[usize],
        entry: usize,
        n: usize,
    ) -> Vec<usize> {
        // Reachable blocks in RPO order (excluding entry).
        let mut order: Vec<usize> = (0..n)
            .filter(|&b| b != entry && rpo_index[b] != usize::MAX)
            .collect();
        order.sort_by_key(|&b| rpo_index[b]);

        let undefined = usize::MAX;
        let mut idom = vec![undefined; n];
        idom[entry] = entry;

        let intersect = |mut a: usize, mut b: usize, idom: &[usize]| -> usize {
            while a != b {
                while rpo_index[a] > rpo_index[b] {
                    a = idom[a];
                }
                while rpo_index[b] > rpo_index[a] {
                    b = idom[b];
                }
            }
            a
        };

        let mut changed = true;
        while changed {
            changed = false;
            for &b in &order {
                let mut new_idom = undefined;
                for &p in &preds[b] {
                    if idom[p] == undefined {
                        continue; // not yet processed
                    }
                    new_idom = if new_idom == undefined {
                        p
                    } else {
                        intersect(p, new_idom, &idom)
                    };
                }
                if new_idom != undefined && idom[b] != new_idom {
                    idom[b] = new_idom;
                    changed = true;
                }
            }
        }
        idom
    }

    /// Does `a` dominate `b`? Walk `b`'s idom chain to the entry.
    fn dominates(idom: &[usize], a: usize, b: usize, entry: usize) -> bool {
        let mut cur = b;
        loop {
            if cur == a {
                return true;
            }
            if cur == entry {
                return false;
            }
            let next = idom[cur];
            if next == cur || next == usize::MAX {
                return false;
            }
            cur = next;
        }
    }

    /// Size in bytes of a type, via the trust-ir layout engine (scalars,
    /// arrays, structs, tuples).
    fn size_of(&self, ty: &Ty) -> Result<u32, WasmLowerError> {
        let shape = self
            .module
            .ty_layout_shape(ty)
            .map_err(|e| WasmLowerError::UnsupportedType(format!("layout of {ty:?}: {e:?}")))?;
        let bytes = shape
            .size_bytes()
            .ok_or_else(|| WasmLowerError::UnsupportedType(format!("{ty:?} has no byte size")))?;
        u32::try_from(bytes)
            .map_err(|_| WasmLowerError::UnsupportedType(format!("{ty:?} too large")))
    }

    fn idx(&self, b: BlockId) -> Result<usize, WasmLowerError> {
        self.block_index
            .get(&b)
            .copied()
            .ok_or_else(|| WasmLowerError::UndefinedBlock(format!("{b:?}")))
    }

    /// Assign a wasm local to every SSA value: entry-block params first (the
    /// function params), then every other block param and instruction result.
    fn assign_locals(&mut self) -> Result<(), WasmLowerError> {
        let entry = self.idx(self.func.entry)?;
        for (vid, ty) in &self.func.blocks[entry].params {
            let vt = valtype_of(ty)?;
            self.locals.insert(*vid, (self.next_local, vt));
            self.param_types.push(vt);
            self.next_local += 1;
        }
        for (bi, block) in self.func.blocks.iter().enumerate() {
            if bi != entry {
                for (vid, ty) in &block.params {
                    let vt = valtype_of(ty)?;
                    self.bind_declared(*vid, vt);
                }
            }
            for node in &block.body {
                if node.results.is_empty() {
                    continue;
                }
                let vt = result_valtype(&node.inst, self.call_targets, self.module)?;
                for &res in &node.results {
                    self.bind_declared(res, vt);
                }
            }
        }
        Ok(())
    }

    fn bind_declared(&mut self, v: ValueId, vt: ValType) {
        self.locals.insert(v, (self.next_local, vt));
        self.declared_locals.push(vt);
        self.next_local += 1;
    }

    fn emit_local_set(&mut self, idx: u32) {
        self.code.push(op::LOCAL_SET);
        write_uleb128(&mut self.code, u64::from(idx));
    }

    /// Emit a unary op, leaving the result on the operand stack. `src` is the
    /// operand's local. Integer `Neg`/`Not` have no wasm opcode, so they expand
    /// (`0 - x` / `x ^ -1`); the float unaries and `popcnt` are single opcodes.
    fn emit_unop(&mut self, un: UnOp, vt: ValType, src: u32) -> Result<(), WasmLowerError> {
        use ValType::{F32, F64, I32, I64};
        match (un, vt) {
            // Integer negate: 0 - x.
            (UnOp::Neg, I32) => {
                emit_i32_const(&mut self.code, 0);
                emit_local_get(&mut self.code, src);
                self.code.push(op::I32_SUB);
            }
            (UnOp::Neg, I64) => {
                self.code.push(op::I64_CONST);
                write_sleb128(&mut self.code, 0);
                emit_local_get(&mut self.code, src);
                self.code.push(op::I64_SUB);
            }
            // Bitwise NOT: x ^ -1 (all ones).
            (UnOp::Not, I32) => {
                emit_local_get(&mut self.code, src);
                emit_i32_const(&mut self.code, -1);
                self.code.push(op::I32_XOR);
            }
            (UnOp::Not, I64) => {
                emit_local_get(&mut self.code, src);
                self.code.push(op::I64_CONST);
                write_sleb128(&mut self.code, -1);
                self.code.push(op::I64_XOR);
            }
            // Single-opcode unaries: operand then opcode.
            _ => {
                let opcode = match (un, vt) {
                    (UnOp::CtPop, I32) => op::I32_POPCNT,
                    (UnOp::CtPop, I64) => op::I64_POPCNT,
                    (UnOp::FNeg, F32) => op::F32_NEG,
                    (UnOp::FNeg, F64) => op::F64_NEG,
                    (UnOp::FAbs, F32) => op::F32_ABS,
                    (UnOp::FAbs, F64) => op::F64_ABS,
                    (UnOp::FSqrt, F32) => op::F32_SQRT,
                    (UnOp::FSqrt, F64) => op::F64_SQRT,
                    (UnOp::FCeil, F32) => op::F32_CEIL,
                    (UnOp::FCeil, F64) => op::F64_CEIL,
                    (UnOp::FFloor, F32) => op::F32_FLOOR,
                    (UnOp::FFloor, F64) => op::F64_FLOOR,
                    (UnOp::FTrunc, F32) => op::F32_TRUNC,
                    (UnOp::FTrunc, F64) => op::F64_TRUNC,
                    _ => {
                        return Err(WasmLowerError::UnsupportedInst(format!(
                            "UnOp::{un:?} on {vt:?}"
                        )));
                    }
                };
                emit_local_get(&mut self.code, src);
                self.code.push(opcode);
            }
        }
        Ok(())
    }

    /// Emit a cast conversion. The operand is already on the stack; this appends
    /// the conversion opcode(s) for the `src_vt → dst_vt` value-type pair. A
    /// width-preserving int↔int or ptr cast is the identity (no opcode). Float→
    /// int uses the SATURATING `trunc_sat` (matching Rust `as` / the trust-ir
    /// interpreter, which saturate rather than trap).
    fn emit_cast(
        &mut self,
        op: CastOp,
        src_vt: ValType,
        dst_vt: ValType,
    ) -> Result<(), WasmLowerError> {
        use ValType::{F32, F64, I32, I64};
        let sat = |s: &mut Self, idx: u32| {
            s.code.push(op::FC_PREFIX);
            write_uleb128(&mut s.code, u64::from(idx));
        };
        match op {
            // Integer width changes (only i32/i64 here; sub-word handled by Load).
            CastOp::Trunc => match (src_vt, dst_vt) {
                (I64, I32) => self.code.push(op::I32_WRAP_I64),
                (a, b) if a == b => {} // same width: identity
                _ => return Err(self.bad_cast(op, src_vt, dst_vt)),
            },
            CastOp::ZExt => match (src_vt, dst_vt) {
                (I32, I64) => self.code.push(op::I64_EXTEND_I32_U),
                (a, b) if a == b => {}
                _ => return Err(self.bad_cast(op, src_vt, dst_vt)),
            },
            CastOp::SExt => match (src_vt, dst_vt) {
                (I32, I64) => self.code.push(op::I64_EXTEND_I32_S),
                (a, b) if a == b => {}
                _ => return Err(self.bad_cast(op, src_vt, dst_vt)),
            },
            CastOp::FPTrunc => match (src_vt, dst_vt) {
                (F64, F32) => self.code.push(op::F32_DEMOTE_F64),
                (a, b) if a == b => {}
                _ => return Err(self.bad_cast(op, src_vt, dst_vt)),
            },
            CastOp::FPExt => match (src_vt, dst_vt) {
                (F32, F64) => self.code.push(op::F64_PROMOTE_F32),
                (a, b) if a == b => {}
                _ => return Err(self.bad_cast(op, src_vt, dst_vt)),
            },
            // trunc_sat is EXACTLY the Sat variants' semantics (NaN -> 0,
            // clamp — Rust `as`), and a sound refinement for the raw
            // FPToSI/FPToUI (out-of-range/NaN is UB per trust-ir; a defined
            // saturated result refines UB).
            CastOp::FPToSI | CastOp::FPToSISat => match (src_vt, dst_vt) {
                (F32, I32) => sat(self, op::I32_TRUNC_SAT_F32_S),
                (F64, I32) => sat(self, op::I32_TRUNC_SAT_F64_S),
                (F32, I64) => sat(self, op::I64_TRUNC_SAT_F32_S),
                (F64, I64) => sat(self, op::I64_TRUNC_SAT_F64_S),
                _ => return Err(self.bad_cast(op, src_vt, dst_vt)),
            },
            CastOp::FPToUI | CastOp::FPToUISat => match (src_vt, dst_vt) {
                (F32, I32) => sat(self, op::I32_TRUNC_SAT_F32_U),
                (F64, I32) => sat(self, op::I32_TRUNC_SAT_F64_U),
                (F32, I64) => sat(self, op::I64_TRUNC_SAT_F32_U),
                (F64, I64) => sat(self, op::I64_TRUNC_SAT_F64_U),
                _ => return Err(self.bad_cast(op, src_vt, dst_vt)),
            },
            CastOp::SIToFP => match (src_vt, dst_vt) {
                (I32, F32) => self.code.push(op::F32_CONVERT_I32_S),
                (I32, F64) => self.code.push(op::F64_CONVERT_I32_S),
                (I64, F32) => self.code.push(op::F32_CONVERT_I64_S),
                (I64, F64) => self.code.push(op::F64_CONVERT_I64_S),
                _ => return Err(self.bad_cast(op, src_vt, dst_vt)),
            },
            CastOp::UIToFP => match (src_vt, dst_vt) {
                (I32, F32) => self.code.push(op::F32_CONVERT_I32_U),
                (I32, F64) => self.code.push(op::F64_CONVERT_I32_U),
                (I64, F32) => self.code.push(op::F32_CONVERT_I64_U),
                (I64, F64) => self.code.push(op::F64_CONVERT_I64_U),
                _ => return Err(self.bad_cast(op, src_vt, dst_vt)),
            },
            CastOp::Bitcast => match (src_vt, dst_vt) {
                (I32, F32) => self.code.push(op::F32_REINTERPRET_I32),
                (F32, I32) => self.code.push(op::I32_REINTERPRET_F32),
                (I64, F64) => self.code.push(op::F64_REINTERPRET_I64),
                (F64, I64) => self.code.push(op::I64_REINTERPRET_F64),
                (a, b) if a == b => {} // same repr: identity
                _ => return Err(self.bad_cast(op, src_vt, dst_vt)),
            },
            // Pointers are wasm32 i32; ptr↔int of equal width is the identity,
            // and a width change is the corresponding int conversion.
            CastOp::PtrToInt | CastOp::IntToPtr | CastOp::PtrToPtr => match (src_vt, dst_vt) {
                (a, b) if a == b => {}
                (I32, I64) => self.code.push(op::I64_EXTEND_I32_U),
                (I64, I32) => self.code.push(op::I32_WRAP_I64),
                _ => return Err(self.bad_cast(op, src_vt, dst_vt)),
            },
            // FPToSISat/FPToUISat: excluded from the proven surface (ay's
            // encode_cast fails closed; Lean-excluded), so they fail closed
            // here too even though wasm's trunc_sat family matches their
            // saturating semantics — no lowering without the proof story.
            CastOp::Transmute | CastOp::ReifyFnPointer => {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "Cast::{op:?} (not supported)"
                )));
            }
        }
        Ok(())
    }

    fn bad_cast(&self, op: CastOp, s: ValType, d: ValType) -> WasmLowerError {
        WasmLowerError::UnsupportedInst(format!("Cast::{op:?} {s:?} -> {d:?}"))
    }

    /// Emit a float comparison, leaving an i32 (0/1) on the stack. wasm's
    /// `eq/lt/gt/le/ge` are ORDERED (false on NaN) and `ne` is UNORDERED (true
    /// on NaN), so the ordered/unordered trust-ir predicates are built from
    /// these plus `isnan(x) = f.ne(x,x)` and `i32.or`. ONe (ordered ne) =
    /// `lt | gt`. The formal proof discharges these against `encode_trust_ir_
    /// fcmp` over all bit patterns (NaN included).
    fn emit_fcmp(
        &mut self,
        cmp: FCmpOp,
        vt: ValType,
        a: u32,
        b: u32,
    ) -> Result<(), WasmLowerError> {
        let (eq, ne, lt, gt, le, ge) = match vt {
            ValType::F32 => (
                op::F32_EQ,
                op::F32_NE,
                op::F32_LT,
                op::F32_GT,
                op::F32_LE,
                op::F32_GE,
            ),
            ValType::F64 => (
                op::F64_EQ,
                op::F64_NE,
                op::F64_LT,
                op::F64_GT,
                op::F64_LE,
                op::F64_GE,
            ),
            other => {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "FCmp on {other:?}"
                )));
            }
        };
        // a <op> b → i32 bool.
        let bin = |s: &mut Self, opcode: u8| {
            emit_local_get(&mut s.code, a);
            emit_local_get(&mut s.code, b);
            s.code.push(opcode);
        };
        match cmp {
            FCmpOp::OEq => bin(self, eq),
            FCmpOp::OLt => bin(self, lt),
            FCmpOp::OLe => bin(self, le),
            FCmpOp::OGt => bin(self, gt),
            FCmpOp::OGe => bin(self, ge),
            // ordered-not-equal = (a<b) | (a>b).
            FCmpOp::ONe => {
                bin(self, lt);
                bin(self, gt);
                self.code.push(op::I32_OR);
            }
            // unordered-not-equal is exactly wasm f.ne.
            FCmpOp::UNe => bin(self, ne),
            // unordered X = (ordered X) | isnan(a) | isnan(b).
            FCmpOp::UEq | FCmpOp::ULt | FCmpOp::ULe | FCmpOp::UGt | FCmpOp::UGe => {
                let ordered = match cmp {
                    FCmpOp::UEq => eq,
                    FCmpOp::ULt => lt,
                    FCmpOp::ULe => le,
                    FCmpOp::UGt => gt,
                    FCmpOp::UGe => ge,
                    _ => unreachable!(),
                };
                bin(self, ordered);
                // | isnan(a): a != a  (unordered ne is true iff NaN)
                emit_local_get(&mut self.code, a);
                emit_local_get(&mut self.code, a);
                self.code.push(ne);
                self.code.push(op::I32_OR);
                // | isnan(b)
                emit_local_get(&mut self.code, b);
                emit_local_get(&mut self.code, b);
                self.code.push(ne);
                self.code.push(op::I32_OR);
            }
        }
        Ok(())
    }

    /// Emit a block's non-terminator instructions (everything but the last).
    fn emit_block_body(&mut self, cur: usize) -> Result<(), WasmLowerError> {
        let body_len = self.func.blocks[cur].body.len();
        for ni in 0..body_len.saturating_sub(1) {
            let node = &self.func.blocks[cur].body[ni];
            match &node.inst {
                Inst::Const {
                    value: Constant::FnDef(fid),
                    ..
                } => {
                    // A function pointer is its table index (== its wasm funcidx).
                    let (widx, _) = *self.call_targets.get(fid).ok_or_else(|| {
                        WasmLowerError::UnsupportedInst(format!(
                            "function pointer to unknown {fid:?}"
                        ))
                    })?;
                    let dst = slot(&self.locals, first_result(node, &self.func.name)?)?.0;
                    emit_i32_const(&mut self.code, widx as i32);
                    self.emit_local_set(dst);
                }
                Inst::Const { ty, value } => {
                    let vt = valtype_of(ty)?;
                    let dst = slot(&self.locals, first_result(node, &self.func.name)?)?.0;
                    self.emit_const(vt, value)?;
                    self.emit_local_set(dst);
                }
                Inst::BinOp {
                    op: bin,
                    ty,
                    lhs,
                    rhs,
                } => {
                    let vt = valtype_of(ty)?;
                    let opcode = int_binop_opcode(*bin, vt)?;
                    let l = slot(&self.locals, *lhs)?.0;
                    let r = slot(&self.locals, *rhs)?.0;
                    let dst = slot(&self.locals, first_result(node, &self.func.name)?)?.0;
                    emit_local_get(&mut self.code, l);
                    emit_local_get(&mut self.code, r);
                    self.code.push(opcode);
                    self.emit_local_set(dst);
                }
                Inst::UnOp {
                    op: un,
                    ty,
                    operand,
                } => {
                    let vt = valtype_of(ty)?;
                    let src = slot(&self.locals, *operand)?.0;
                    let dst = slot(&self.locals, first_result(node, &self.func.name)?)?.0;
                    self.emit_unop(*un, vt, src)?;
                    self.emit_local_set(dst);
                }
                Inst::ICmp {
                    op: cmp,
                    ty,
                    lhs,
                    rhs,
                } => {
                    let vt = valtype_of(ty)?;
                    let opcode = icmp_opcode(*cmp, vt)?;
                    let l = slot(&self.locals, *lhs)?.0;
                    let r = slot(&self.locals, *rhs)?.0;
                    let dst = slot(&self.locals, first_result(node, &self.func.name)?)?.0;
                    emit_local_get(&mut self.code, l);
                    emit_local_get(&mut self.code, r);
                    self.code.push(opcode);
                    self.emit_local_set(dst);
                }
                Inst::FCmp {
                    op: cmp,
                    ty,
                    lhs,
                    rhs,
                } => {
                    let vt = valtype_of(ty)?;
                    let l = slot(&self.locals, *lhs)?.0;
                    let r = slot(&self.locals, *rhs)?.0;
                    let dst = slot(&self.locals, first_result(node, &self.func.name)?)?.0;
                    self.emit_fcmp(*cmp, vt, l, r)?;
                    self.emit_local_set(dst);
                }
                Inst::Cast {
                    op: cop,
                    src_ty,
                    dst_ty,
                    operand,
                } => {
                    let src_vt = valtype_of(src_ty)?;
                    let dst_vt = valtype_of(dst_ty)?;
                    let src = slot(&self.locals, *operand)?.0;
                    let dst = slot(&self.locals, first_result(node, &self.func.name)?)?.0;
                    emit_local_get(&mut self.code, src);
                    self.emit_cast(*cop, src_vt, dst_vt)?;
                    self.emit_local_set(dst);
                }
                Inst::Alloca { ty, .. } => {
                    let _ = ty; // size already accounted in the frame pre-pass
                    let result = first_result(node, &self.func.name)?;
                    let off = *self.alloca_offsets.get(&result).ok_or_else(|| {
                        WasmLowerError::UnsupportedInst(format!(
                            "Alloca result {result:?} missing a frame slot"
                        ))
                    })?;
                    let dst = slot(&self.locals, result)?.0;
                    // pointer = frame_base + offset
                    emit_local_get(&mut self.code, self.frame_base_local);
                    emit_i32_const(&mut self.code, off as i32);
                    self.code.push(op::I32_ADD);
                    self.emit_local_set(dst);
                }
                Inst::GEP {
                    pointee_ty,
                    base,
                    indices,
                    ..
                } => {
                    let dst = slot(&self.locals, first_result(node, &self.func.name)?)?.0;
                    let base_l = slot(&self.locals, *base)?.0;
                    let elem_size = self.size_of(pointee_ty)?;

                    // Element index (first): addr = base + idx0 * sizeof(pointee).
                    let (idx_l, idx_vt) = slot(&self.locals, indices[0])?;
                    if idx_vt != ValType::I32 {
                        return Err(WasmLowerError::UnsupportedInst(format!(
                            "GEP index of {idx_vt:?} (wasm32 addresses use i32 indices)"
                        )));
                    }
                    emit_local_get(&mut self.code, base_l);
                    emit_local_get(&mut self.code, idx_l);
                    emit_i32_const(&mut self.code, elem_size as i32);
                    self.code.push(op::I32_MUL);
                    self.code.push(op::I32_ADD);

                    match indices.len() {
                        1 => {}
                        2 => {
                            // Struct field: + field_offset(struct, const field).
                            let Ty::Struct(sid) = pointee_ty else {
                                return Err(WasmLowerError::UnsupportedInst(format!(
                                    "2-index GEP into non-struct {pointee_ty:?} (Slice 2c: structs)"
                                )));
                            };
                            let field = *self.const_ints.get(&indices[1]).ok_or_else(|| {
                                WasmLowerError::UnsupportedInst(
                                    "struct GEP field index must be a constant".to_string(),
                                )
                            })?;
                            let field = u32::try_from(field).map_err(|_| {
                                WasmLowerError::UnsupportedInst(format!("bad field index {field}"))
                            })?;
                            let off_bits = self
                                .module
                                .struct_field_offset_bits(*sid, field)
                                .map_err(|e| {
                                    WasmLowerError::UnsupportedInst(format!(
                                        "struct field offset: {e:?}"
                                    ))
                                })?;
                            emit_i32_const(&mut self.code, (off_bits / 8) as i32);
                            self.code.push(op::I32_ADD);
                        }
                        n => {
                            return Err(WasmLowerError::UnsupportedInst(format!(
                                "GEP with {n} indices (supported: 1 element, 2 struct-field)"
                            )));
                        }
                    }
                    self.emit_local_set(dst);
                }
                Inst::Load { ty, ptr, .. } => {
                    let vt = valtype_of(ty)?;
                    let (load_op, _, align) = mem_ops(vt)?;
                    let p = slot(&self.locals, *ptr)?.0;
                    let dst = slot(&self.locals, first_result(node, &self.func.name)?)?.0;
                    emit_local_get(&mut self.code, p);
                    self.code.push(load_op);
                    emit_memarg(&mut self.code, align, 0);
                    self.emit_local_set(dst);
                }
                Inst::Store { ty, ptr, value, .. } => {
                    let vt = valtype_of(ty)?;
                    let (_, store_op, align) = mem_ops(vt)?;
                    let p = slot(&self.locals, *ptr)?.0;
                    let v = slot(&self.locals, *value)?.0;
                    emit_local_get(&mut self.code, p); // address
                    emit_local_get(&mut self.code, v); // value
                    self.code.push(store_op);
                    emit_memarg(&mut self.code, align, 0);
                }
                // The WASM backend lowers only `CallingConv::C`. A non-C edge
                // is rejected here (fail-closed) rather than silently lowered
                // through the `sig`-derived `call_indirect` type index with the
                // wrong ABI, mirroring the adapter's indirect-call guard.
                Inst::CallIndirect {
                    callee,
                    sig,
                    args,
                    calling_conv,
                } => {
                    if *calling_conv != CallingConv::C {
                        return Err(WasmLowerError::UnsupportedInst(format!(
                            "call_indirect uses unsupported calling convention {calling_conv:?}; the WASM backend lowers only CallingConv::C"
                        )));
                    }
                    let type_idx = *self.sig_types.get(sig).ok_or_else(|| {
                        WasmLowerError::UnsupportedInst(format!(
                            "call_indirect with unknown {sig:?}"
                        ))
                    })?;
                    let ret_is_value = self
                        .module
                        .func_type(*sig)
                        .is_some_and(|ft| !ft.returns.is_empty());
                    // Push args, then the callee table index, then call_indirect.
                    let arg_locals: Vec<u32> = args
                        .iter()
                        .map(|a| slot(&self.locals, *a).map(|s| s.0))
                        .collect::<Result<_, _>>()?;
                    for a in arg_locals {
                        emit_local_get(&mut self.code, a);
                    }
                    let callee_l = slot(&self.locals, *callee)?.0;
                    emit_local_get(&mut self.code, callee_l);
                    self.code.push(op::CALL_INDIRECT);
                    write_uleb128(&mut self.code, u64::from(type_idx));
                    write_uleb128(&mut self.code, 0); // table 0
                    match (node.results.first(), ret_is_value) {
                        (Some(r), true) => {
                            let dst = slot(&self.locals, *r)?.0;
                            self.emit_local_set(dst);
                        }
                        (None, true) => self.code.push(op::DROP),
                        (None, false) => {}
                        (Some(_), false) => {
                            return Err(WasmLowerError::UnsupportedInst(
                                "indirect call result used but signature returns void".to_string(),
                            ));
                        }
                    }
                }
                Inst::Call { callee, args } => {
                    let (widx, ret) = *self.call_targets.get(callee).ok_or_else(|| {
                        WasmLowerError::UnsupportedInst(format!("Call to unknown {callee:?}"))
                    })?;
                    // Push args in order, then `call`.
                    let arg_locals: Vec<u32> = args
                        .iter()
                        .map(|a| slot(&self.locals, *a).map(|s| s.0))
                        .collect::<Result<_, _>>()?;
                    for a in arg_locals {
                        emit_local_get(&mut self.code, a);
                    }
                    self.code.push(op::CALL);
                    write_uleb128(&mut self.code, u64::from(widx));
                    // Consume the result: bind it, drop it, or (void) nothing.
                    match (node.results.first(), ret) {
                        (Some(r), Some(_)) => {
                            let dst = slot(&self.locals, *r)?.0;
                            self.emit_local_set(dst);
                        }
                        (None, Some(_)) => self.code.push(op::DROP),
                        (None, None) => {}
                        (Some(_), None) => {
                            return Err(WasmLowerError::UnsupportedInst(format!(
                                "Call to {callee:?} returns no value but its result is used"
                            )));
                        }
                    }
                }
                other => {
                    return Err(WasmLowerError::UnsupportedInst(format!(
                        "{other:?} (supported: Const, BinOp add/sub/mul, ICmp, Alloca, GEP, \
                         Load, Store, Call)"
                    )));
                }
            }
        }
        Ok(())
    }

    /// Emit a constant onto the wasm operand stack.
    fn emit_const(&mut self, vt: ValType, value: &Constant) -> Result<(), WasmLowerError> {
        match (vt, value) {
            (ValType::I32, Constant::Int(n)) => emit_i32_const(&mut self.code, *n as i32),
            (ValType::I32, Constant::Bool(b)) => emit_i32_const(&mut self.code, i32::from(*b)),
            (ValType::I64, Constant::Int(n)) => {
                self.code.push(op::I64_CONST);
                write_sleb128(&mut self.code, *n as i64);
            }
            _ => {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "Const {value:?} as {vt:?} (supported: integer/bool constants)"
                )));
            }
        }
        Ok(())
    }

    /// Set a target block's param locals from an edge's args (phi resolution).
    /// Permutation-safe: push every source value onto the operand stack first,
    /// then `local.set` the destinations in reverse — so a swap like
    /// `br head [b, a]` is correct.
    fn set_params(&mut self, target: BlockId, args: &[ValueId]) -> Result<(), WasmLowerError> {
        let ti = self.idx(target)?;
        let params = &self.func.blocks[ti].params;
        if params.len() != args.len() {
            return Err(WasmLowerError::ArityMismatch(format!(
                "block {ti}: {} params vs {} args",
                params.len(),
                args.len()
            )));
        }
        let mut dest_locals: Vec<u32> = Vec::with_capacity(args.len());
        for ((pv, _), av) in params.iter().zip(args) {
            let a = slot(&self.locals, *av)?.0;
            let p = slot(&self.locals, *pv)?.0;
            emit_local_get(&mut self.code, a);
            dest_locals.push(p);
        }
        for &p in dest_locals.iter().rev() {
            self.emit_local_set(p);
        }
        Ok(())
    }

    fn emit_return(&mut self, values: &[ValueId]) -> Result<(), WasmLowerError> {
        // Epilogue: restore the caller's stack pointer before leaving.
        if self.frame_size != 0 {
            let sp = self.sp_global.expect("frame implies sp_global");
            emit_local_get(&mut self.code, self.saved_sp_local);
            self.code.push(op::GLOBAL_SET);
            write_uleb128(&mut self.code, u64::from(sp));
        }
        let mut tys = Vec::with_capacity(values.len());
        for v in values {
            let (idx, vt) = slot(&self.locals, *v)?;
            emit_local_get(&mut self.code, idx);
            tys.push(vt);
        }
        self.code.push(op::RETURN);
        if self.result_types.is_none() {
            self.result_types = Some(tys);
        }
        Ok(())
    }

    /// Resolve a `br` to `target` of the given frame kind, returning the depth
    /// immediate. `N = open_labels - frame_depth` (counts the enclosing `if`).
    fn resolve_branch(&self, want_loop: bool, target: usize) -> Result<u32, WasmLowerError> {
        for (frame, depth) in self.context.iter().rev() {
            let matches = match frame {
                Frame::Loop(t) => want_loop && *t == target,
                Frame::Block(t) => !want_loop && *t == target,
            };
            if matches {
                return Ok(self.open_labels - depth);
            }
        }
        Err(WasmLowerError::UnsupportedControlFlow(format!(
            "branch target block {target} not in scope — unstructured CFG in `{}`",
            self.func.name
        )))
    }

    /// The dominator-tree children of `x` that are merge nodes (RPO-sorted).
    fn merge_children(&self, x: usize) -> Vec<usize> {
        self.dom_children[x]
            .iter()
            .copied()
            .filter(|&c| self.is_merge[c])
            .collect()
    }

    /// Open a structured-control scope: emit the opcode, push the frame.
    fn open_scope(&mut self, frame: Frame) {
        let opcode = match frame {
            Frame::Loop(_) => op::LOOP,
            Frame::Block(_) => op::BLOCK,
        };
        self.code.push(opcode);
        self.code.push(op::BLOCKTYPE_VOID);
        self.open_labels += 1;
        self.context.push((frame, self.open_labels));
    }

    fn close_scope(&mut self) {
        self.code.push(op::END);
        self.context.pop();
        self.open_labels -= 1;
    }

    /// Recurse the dominator tree at `x`: a loop header opens a `loop`.
    fn do_tree(&mut self, x: usize) -> Result<(), WasmLowerError> {
        let merge_kids = self.merge_children(x);
        if self.is_header[x] {
            self.open_scope(Frame::Loop(x));
            self.node_within(x, &merge_kids)?;
            self.close_scope();
        } else {
            self.node_within(x, &merge_kids)?;
        }
        Ok(())
    }

    /// Open a `block` for each pending merge child (earliest-RPO outermost),
    /// then emit `x`'s body in the innermost context. After each block's `end`,
    /// recurse the merge child's subtree (its join point).
    fn node_within(&mut self, x: usize, merge_kids: &[usize]) -> Result<(), WasmLowerError> {
        if let Some((&y, rest)) = merge_kids.split_first() {
            self.open_scope(Frame::Block(y));
            self.node_within(x, rest)?;
            self.close_scope();
            self.do_tree(y)?;
        } else {
            if !self.emitted.insert(x) {
                return Err(WasmLowerError::UnsupportedControlFlow(format!(
                    "re-emission of block {x} in `{}` — unstructured/irreducible CFG",
                    self.func.name
                )));
            }
            self.emit_block_body(x)?;
            self.do_terminator(x)?;
        }
        Ok(())
    }

    fn do_terminator(&mut self, x: usize) -> Result<(), WasmLowerError> {
        let term = terminator_of(self.func, x)?.clone();
        match term {
            Inst::Return { values } => self.emit_return(&values)?,
            Inst::Unreachable => self.code.push(op::UNREACHABLE),
            Inst::Br { target, args } => {
                self.set_params(target, &args)?;
                let t = self.idx(target)?;
                self.do_branch(x, t)?;
            }
            Inst::CondBr {
                cond,
                then_target,
                then_args,
                else_target,
                else_args,
            } => {
                let then_i = self.idx(then_target)?;
                let else_i = self.idx(else_target)?;
                let cond_local = slot(&self.locals, cond)?.0;
                emit_local_get(&mut self.code, cond_local);
                self.open_if();
                self.set_params(then_target, &then_args)?;
                self.do_branch(x, then_i)?;
                self.code.push(op::ELSE);
                self.set_params(else_target, &else_args)?;
                self.do_branch(x, else_i)?;
                self.close_if();
            }
            // `exhaustive_enum_unreachable` only authorizes dropping the default
            // edge; this compare-cascade always emits it (a correct superset),
            // so the hint is not consulted here.
            Inst::Switch {
                value,
                default,
                default_args,
                cases,
                exhaustive_enum_unreachable: _,
            } => {
                // Lower to an if/else compare-cascade: each case is
                // `if value == k { <case edge> } else { <rest> }`, ending in the
                // default edge. Reuses do_branch, so case targets that are merge
                // nodes / back-edges / inlinable blocks are all handled. The
                // nested `if`s are counted in open_labels, so branch depths stay
                // correct.
                let (vlocal, vt) = slot(&self.locals, value)?;
                self.emit_switch_cascade(x, vlocal, vt, &cases, default, &default_args)?;
            }
            other => {
                return Err(WasmLowerError::UnsupportedControlFlow(format!(
                    "terminator {other:?}"
                )));
            }
        }
        Ok(())
    }

    /// Emit an `if`/`else` opener with a void blocktype, counting the label.
    fn open_if(&mut self) {
        self.code.push(op::IF);
        self.code.push(op::BLOCKTYPE_VOID);
        self.open_labels += 1;
    }

    fn close_if(&mut self) {
        self.code.push(op::END);
        self.open_labels -= 1;
    }

    /// Emit the recursive `Switch` compare-cascade.
    fn emit_switch_cascade(
        &mut self,
        x: usize,
        vlocal: u32,
        vt: ValType,
        cases: &[trust_ir::SwitchCase],
        default: BlockId,
        default_args: &[ValueId],
    ) -> Result<(), WasmLowerError> {
        match cases.split_first() {
            None => {
                self.set_params(default, default_args)?;
                let d = self.idx(default)?;
                self.do_branch(x, d)
            }
            Some((case, rest)) => {
                let eq = match vt {
                    ValType::I32 => op::I32_EQ,
                    ValType::I64 => op::I64_EQ,
                    other => {
                        return Err(WasmLowerError::UnsupportedInst(format!(
                            "Switch on {other:?} (supported: i32/i64)"
                        )));
                    }
                };
                emit_local_get(&mut self.code, vlocal);
                self.emit_const(vt, &case.value)?;
                self.code.push(eq);
                self.open_if();
                self.set_params(case.target, &case.args)?;
                let t = self.idx(case.target)?;
                self.do_branch(x, t)?;
                self.code.push(op::ELSE);
                self.emit_switch_cascade(x, vlocal, vt, rest, default, default_args)?;
                self.close_if();
                Ok(())
            }
        }
    }

    /// Translate the edge `x -> t`: back-edge → `br` to the loop label; forward
    /// merge → `br` to the block label; otherwise inline `t`'s subtree.
    fn do_branch(&mut self, x: usize, t: usize) -> Result<(), WasmLowerError> {
        if self.back_edges.contains(&(x, t)) {
            let n = self.resolve_branch(true, t)?;
            self.code.push(op::BR);
            write_uleb128(&mut self.code, u64::from(n));
        } else if self.is_merge[t] {
            let n = self.resolve_branch(false, t)?;
            self.code.push(op::BR);
            write_uleb128(&mut self.code, u64::from(n));
        } else {
            self.do_tree(t)?;
        }
        Ok(())
    }
}

/// Lower a single trust-ir function and append it to `module`. Returns the new
/// wasm function index. Supports straight-line code, `if/else`, and reducible
/// loops; fail-closed on irreducible CFGs, `Switch`, and out-of-subset ops.
pub fn lower_function(
    module: &mut WasmModule,
    func: &Function,
    ir_module: &Module,
    sp_global: Option<u32>,
    call_targets: &CallTargets,
    sig_types: &SigTypes,
) -> Result<u32, WasmLowerError> {
    reject_unwired_eh_instructions(func)?;
    let mut low = Lowering::build(func, ir_module, sp_global, call_targets, sig_types)?;
    low.assign_locals()?;
    low.compute_frame()?;
    low.emit_prologue();
    let entry = low.idx(func.entry)?;
    low.do_tree(entry)?;
    // All paths return; mark the statically-dead tail so the module validates.
    low.code.push(op::UNREACHABLE);

    let results = low.result_types.unwrap_or_default();
    let ty_idx = module.add_type(FuncType {
        params: low.param_types,
        results,
    });
    let body = FuncBody {
        locals: run_length_encode(&low.declared_locals),
        code: low.code,
    };
    Ok(module.add_function(ty_idx, body))
}

/// True if `func` contains any `Alloca` (and therefore needs a stack frame).
fn uses_stack_frame(func: &Function) -> bool {
    func.blocks
        .iter()
        .flat_map(|b| &b.body)
        .any(|n| matches!(n.inst, Inst::Alloca { .. }))
}

/// True if `func` takes a function address or makes an indirect call (needs a
/// function table).
fn uses_func_table(func: &Function) -> bool {
    func.blocks.iter().flat_map(|b| &b.body).any(|n| {
        matches!(n.inst, Inst::CallIndirect { .. })
            || matches!(
                &n.inst,
                Inst::Const {
                    value: Constant::FnDef(_),
                    ..
                }
            )
    })
}

/// Map a trust-ir signature to a wasm function type.
fn wasm_func_type(ft: &trust_ir::FuncTy) -> Result<FuncType, WasmLowerError> {
    let params = ft.params.iter().map(valtype_of).collect::<Result<_, _>>()?;
    let results = ft
        .returns
        .iter()
        .map(valtype_of)
        .collect::<Result<_, _>>()?;
    Ok(FuncType { params, results })
}

/// Lower every function in a trust-ir module to wasm and export each under its
/// own name. If any function uses the stack (allocas), the module gains one
/// linear memory and a shared shadow stack-pointer global.
pub fn compile_module(module: &Module) -> Result<Vec<u8>, WasmLowerError> {
    let mut wasm = WasmModule::new();
    let sp_global = if module.functions.iter().any(uses_stack_frame) {
        wasm.ensure_memory(STACK_PAGES);
        Some(wasm.add_global(ValType::I32, true, STACK_TOP))
    } else {
        None
    };

    // Direct-call targets: wasm function indices are assigned in definition
    // order (no imports), so function `i` in the module is wasm function `i`.
    let mut call_targets: CallTargets = HashMap::new();
    for (i, func) in module.functions.iter().enumerate() {
        let ret = match module.func_type(func.ty) {
            Some(ft) => ft.returns.first().map(valtype_of).transpose()?,
            None => None,
        };
        call_targets.insert(func.id, (i as u32, ret));
    }

    // Function table + indirect-call signature types, if the module needs them.
    if module.functions.iter().any(uses_func_table) {
        wasm.set_func_table(module.functions.len() as u32);
    }
    let mut sig_types: SigTypes = HashMap::new();
    for func in &module.functions {
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            if let Inst::CallIndirect { sig, .. } = &node.inst
                && !sig_types.contains_key(sig)
            {
                let ft = module.func_type(*sig).ok_or_else(|| {
                    WasmLowerError::UnsupportedInst(format!("unknown signature {sig:?}"))
                })?;
                let idx = wasm.add_type(wasm_func_type(ft)?);
                sig_types.insert(*sig, idx);
            }
        }
    }

    for func in &module.functions {
        let idx = lower_function(
            &mut wasm,
            func,
            module,
            sp_global,
            &call_targets,
            &sig_types,
        )?;
        wasm.export_func(&func.name, idx);
    }
    Ok(wasm.finish())
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{ICmpOp, Ty};
    use trust_ir_build::ModuleBuilder;

    fn assert_wasm_header(bytes: &[u8]) {
        assert!(bytes.len() > 8, "module too short: {}", bytes.len());
        assert_eq!(
            &bytes[..8],
            &[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]
        );
    }

    fn binop_module(name: &str, ty: Ty, op: BinOp) -> Module {
        let mut mb = ModuleBuilder::new("m");
        let ft = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
        let mut fb = mb.function(name, ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, ty.clone());
        let b = fb.add_block_param(entry, ty.clone());
        fb.switch_to_block(entry);
        let r = fb.binop(op, ty, a, b);
        fb.ret(vec![r]);
        fb.build();
        mb.build()
    }

    #[test]
    fn lowers_straight_line_arithmetic() {
        for (ty, op) in [(Ty::I32, BinOp::Add), (Ty::I64, BinOp::Mul)] {
            assert_wasm_header(&compile_module(&binop_module("f", ty, op)).unwrap());
        }
    }

    #[test]
    fn lowers_division() {
        for (ty, op) in [
            (Ty::I32, BinOp::SDiv),
            (Ty::I32, BinOp::UDiv),
            (Ty::I32, BinOp::SRem),
            (Ty::I32, BinOp::URem),
            (Ty::I64, BinOp::SDiv),
            (Ty::I64, BinOp::URem),
        ] {
            assert_wasm_header(&compile_module(&binop_module("f", ty, op)).unwrap());
        }
    }

    #[test]
    fn lowers_const() {
        let mut mb = ModuleBuilder::new("m");
        let ft = mb.add_func_type(vec![], vec![Ty::I32]);
        let mut fb = mb.function("seven", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let c = fb.iconst(Ty::I32, 7);
        fb.ret(vec![c]);
        fb.build();
        assert_wasm_header(&compile_module(&mb.build()).unwrap());
    }

    /// max(a, b) = if a >= b { a } else { b } — an if/else diamond (merge join).
    #[test]
    fn lowers_if_else_diamond() {
        let mut mb = ModuleBuilder::new("m");
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("max", ft);
        let entry = fb.create_block();
        let then_b = fb.create_block();
        let else_b = fb.create_block();
        let join = fb.create_block();
        let r = fb.add_block_param(join, Ty::I32);
        let a = fb.add_block_param(entry, Ty::I32);
        let b = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let cond = fb.icmp(ICmpOp::Sge, Ty::I32, a, b);
        fb.condbr(cond, then_b, vec![], else_b, vec![]);
        fb.switch_to_block(then_b);
        fb.br(join, vec![a]);
        fb.switch_to_block(else_b);
        fb.br(join, vec![b]);
        fb.switch_to_block(join);
        fb.ret(vec![r]);
        fb.build();
        assert_wasm_header(&compile_module(&mb.build()).unwrap());
    }

    /// sum_to(n,acc,i,step): while i<=n { acc+=i; i+=step } ; return acc.
    #[test]
    fn lowers_counting_loop() {
        let bytes = compile_module(&sum_to_module()).unwrap();
        assert_wasm_header(&bytes);
    }

    fn sum_to_module() -> Module {
        let mut mb = ModuleBuilder::new("m");
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32, Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("sum_to", ft);
        let entry = fb.create_block();
        let header = fb.create_block();
        let body = fb.create_block();
        let exit = fb.create_block();
        let acc = fb.add_block_param(header, Ty::I32);
        let i = fb.add_block_param(header, Ty::I32);
        let bacc = fb.add_block_param(body, Ty::I32);
        let bi = fb.add_block_param(body, Ty::I32);
        let racc = fb.add_block_param(exit, Ty::I32);
        let n = fb.add_block_param(entry, Ty::I32);
        let acc0 = fb.add_block_param(entry, Ty::I32);
        let i0 = fb.add_block_param(entry, Ty::I32);
        let step = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.br(header, vec![acc0, i0]);
        fb.switch_to_block(header);
        let c = fb.icmp(ICmpOp::Sle, Ty::I32, i, n);
        fb.condbr(c, body, vec![acc, i], exit, vec![acc]);
        fb.switch_to_block(body);
        let nacc = fb.add(Ty::I32, bacc, bi);
        let ni = fb.add(Ty::I32, bi, step);
        fb.br(header, vec![nacc, ni]); // back-edge
        fb.switch_to_block(exit);
        fb.ret(vec![racc]);
        fb.build();
        mb.build()
    }

    /// Irreducible: entry → {A,B}; A↔B mutually branch (two loop entries).
    #[test]
    fn rejects_irreducible_loop() {
        let mut mb = ModuleBuilder::new("m");
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("irr", ft);
        let entry = fb.create_block();
        let a = fb.create_block();
        let b = fb.create_block();
        let exit = fb.create_block();
        let p = fb.add_block_param(entry, Ty::I32);
        let q = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.condbr(p, a, vec![], b, vec![]);
        fb.switch_to_block(a);
        fb.br(b, vec![]); // A -> B
        fb.switch_to_block(b);
        fb.condbr(q, a, vec![], exit, vec![]); // B -> A (back) and B -> exit
        fb.switch_to_block(exit);
        fb.ret(vec![p]);
        fb.build();
        let err = compile_module(&mb.build()).unwrap_err();
        assert!(
            matches!(err, WasmLowerError::UnsupportedControlFlow(_)),
            "{err}"
        );
    }

    /// switch v { 0 => a, 1 => b, _ => c } — a Switch compare-cascade.
    #[test]
    fn lowers_switch() {
        use trust_ir::SwitchCase;
        let mut mb = ModuleBuilder::new("m");
        let ft = mb.add_func_type(vec![Ty::I32; 4], vec![Ty::I32]);
        let mut fb = mb.function("pick", ft);
        let entry = fb.create_block();
        let c0 = fb.create_block();
        let c1 = fb.create_block();
        let def = fb.create_block();
        let join = fb.create_block();
        let r = fb.add_block_param(join, Ty::I32);
        let v = fb.add_block_param(entry, Ty::I32);
        let a = fb.add_block_param(entry, Ty::I32);
        let b = fb.add_block_param(entry, Ty::I32);
        let c = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.switch(
            v,
            vec![
                SwitchCase {
                    value: Constant::Int(0),
                    target: c0,
                    args: vec![],
                },
                SwitchCase {
                    value: Constant::Int(1),
                    target: c1,
                    args: vec![],
                },
            ],
            def,
            vec![],
        );
        fb.switch_to_block(c0);
        fb.br(join, vec![a]);
        fb.switch_to_block(c1);
        fb.br(join, vec![b]);
        fb.switch_to_block(def);
        fb.br(join, vec![c]);
        fb.switch_to_block(join);
        fb.ret(vec![r]);
        fb.build();
        assert_wasm_header(&compile_module(&mb.build()).unwrap());
    }

    /// roundtrip(x) = { let c = alloca i32; *c = x; *c } — alloca/store/load.
    #[test]
    fn lowers_alloca_store_load() {
        let mut mb = ModuleBuilder::new("m");
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("roundtrip", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let cell = fb.alloca(Ty::I32);
        fb.store(Ty::I32, cell, x);
        let r = fb.load(Ty::I32, cell);
        fb.ret(vec![r]);
        fb.build();
        let bytes = compile_module(&mb.build()).unwrap();
        assert_wasm_header(&bytes);
        // Memory section (id 5) must be present.
        assert!(bytes.contains(&0x05), "expected a memory section");
    }

    /// add3(a,b,c) = addtwo(addtwo(a,b), c) — direct calls, chained.
    #[test]
    fn lowers_direct_call() {
        let mut mb = ModuleBuilder::new("m");
        let ft2 = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let addtwo_id = {
            let mut fb = mb.function("addtwo", ft2);
            let e = fb.create_block();
            let a = fb.add_block_param(e, Ty::I32);
            let b = fb.add_block_param(e, Ty::I32);
            fb.switch_to_block(e);
            let r = fb.add(Ty::I32, a, b);
            fb.ret(vec![r]);
            fb.build()
        };
        let ft3 = mb.add_func_type(vec![Ty::I32, Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("add3", ft3);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        let c = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let ab = fb.call(addtwo_id, vec![a, b]);
        let abc = fb.call(addtwo_id, vec![ab, c]);
        fb.ret(vec![abc]);
        fb.build();
        assert_wasm_header(&compile_module(&mb.build()).unwrap());
    }

    /// set_get(i, x) = { let buf: [i32;4]; buf[i] = x; buf[i] } — array GEP.
    #[test]
    fn lowers_array_gep() {
        let mut mb = ModuleBuilder::new("m");
        let elem = mb.add_type(Ty::I32);
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("set_get", ft);
        let e = fb.create_block();
        let i = fb.add_block_param(e, Ty::I32);
        let x = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let buf = fb.alloca(Ty::Array(elem, 4));
        let p = fb.gep(Ty::I32, buf, vec![i]);
        fb.store(Ty::I32, p, x);
        let p2 = fb.gep(Ty::I32, buf, vec![i]);
        let r = fb.load(Ty::I32, p2);
        fb.ret(vec![r]);
        fb.build();
        let bytes = compile_module(&mb.build()).unwrap();
        assert_wasm_header(&bytes);
    }

    /// pair_sum(x,y): Pair{a@0,b@4}; p.a=x; p.b=y; p.a+p.b — struct-field GEP.
    #[test]
    fn lowers_struct_field_gep() {
        use trust_ir::StructId;
        use trust_ir::ty::{FieldDef, StructDef};
        let mut mb = ModuleBuilder::new("m");
        let sid = mb.add_struct(StructDef {
            id: StructId::new(0),
            name: "Pair".to_string(),
            fields: vec![
                FieldDef {
                    name: "a".to_string(),
                    ty: Ty::I32,
                    offset: Some(0),
                },
                FieldDef {
                    name: "b".to_string(),
                    ty: Ty::I32,
                    offset: Some(4),
                },
            ],
            size: Some(8),
            align: Some(4),
            repr: Default::default(),
        });
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("pair_sum", ft);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::I32);
        let y = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let buf = fb.alloca(Ty::Struct(sid));
        let zero = fb.iconst(Ty::I32, 0);
        let f0 = fb.iconst(Ty::I32, 0);
        let f1 = fb.iconst(Ty::I32, 1);
        let pa = fb.gep(Ty::Struct(sid), buf, vec![zero, f0]);
        fb.store(Ty::I32, pa, x);
        let pb = fb.gep(Ty::Struct(sid), buf, vec![zero, f1]);
        fb.store(Ty::I32, pb, y);
        let qa = fb.gep(Ty::Struct(sid), buf, vec![zero, f0]);
        let va = fb.load(Ty::I32, qa);
        let qb = fb.gep(Ty::Struct(sid), buf, vec![zero, f1]);
        let vb = fb.load(Ty::I32, qb);
        let s = fb.add(Ty::I32, va, vb);
        fb.ret(vec![s]);
        fb.build();
        assert_wasm_header(&compile_module(&mb.build()).unwrap());
    }

    /// dispatch(x,y) = (*fn_ptr(imul))(x,y) — indirect call through the table.
    #[test]
    fn lowers_indirect_call() {
        let mut mb = ModuleBuilder::new("m");
        let ft2 = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let imul_id = {
            let mut fb = mb.function("imul", ft2);
            let e = fb.create_block();
            let a = fb.add_block_param(e, Ty::I32);
            let b = fb.add_block_param(e, Ty::I32);
            fb.switch_to_block(e);
            let r = fb.mul(Ty::I32, a, b);
            fb.ret(vec![r]);
            fb.build()
        };
        let mut fb = mb.function("dispatch", ft2);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::I32);
        let y = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let fp = fb.fn_addr(ft2, imul_id);
        let r = fb.call_indirect(fp, ft2, vec![x, y]);
        fb.ret(vec![r]);
        fb.build();
        assert_wasm_header(&compile_module(&mb.build()).unwrap());
    }

    #[test]
    fn rejects_unsupported_binop() {
        // Float remainder has no wasm opcode (it's a libcall), so it stays
        // unlowered — a still-unsupported op for the fail-closed check.
        let err = compile_module(&binop_module("d", Ty::F32, BinOp::FRem)).unwrap_err();
        assert!(matches!(err, WasmLowerError::UnsupportedInst(_)), "{err}");
    }

    #[test]
    fn rejects_exception_handling_instructions_fail_closed() {
        use trust_ir::{
            Block as TrustIrBlock, FuncId, FuncTy, Function as TrustIrFunction, InstrNode, ValueId,
        };

        let make_module = |name: &str, blocks: Vec<TrustIrBlock>| {
            let mut module = Module::new(name);
            let ty = module.add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                is_vararg: false,
            });
            let mut func = TrustIrFunction::new(FuncId::new(0), name, ty, BlockId::new(0));
            func.blocks = blocks;
            module.add_function(func);
            module
        };

        let invoke = make_module(
            "wasm_reject_invoke",
            vec![
                TrustIrBlock {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![InstrNode::new(Inst::Invoke {
                        callee: FuncId::new(0),
                        args: vec![],
                        normal_dest: BlockId::new(1),
                        normal_args: vec![],
                        unwind_dest: BlockId::new(2),
                    })],
                },
                TrustIrBlock {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![InstrNode::new(Inst::Return { values: vec![] })],
                },
                TrustIrBlock {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![InstrNode::new(Inst::Return { values: vec![] })],
                },
            ],
        );
        let err = compile_module(&invoke).expect_err("Wasm has no EH instruction lowering");
        assert!(matches!(err, WasmLowerError::UnsupportedInst(_)), "{err}");
        assert!(err.to_string().contains("Invoke"), "{err}");

        let resume = make_module(
            "wasm_reject_resume",
            vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![],
                body: vec![InstrNode::new(Inst::Resume {
                    exn: ValueId::new(0),
                })],
            }],
        );
        let err = compile_module(&resume).expect_err("Wasm has no resume lowering");
        assert!(matches!(err, WasmLowerError::UnsupportedInst(_)), "{err}");
        assert!(err.to_string().contains("Resume"), "{err}");

        let landing_pad = make_module(
            "wasm_reject_landing_pad",
            vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::LandingPad {
                        is_cleanup: true,
                        catch_type_indices: vec![],
                    })
                    .with_results(vec![ValueId::new(0), ValueId::new(1)]),
                    InstrNode::new(Inst::Return { values: vec![] }),
                ],
            }],
        );
        let err = compile_module(&landing_pad).expect_err("Wasm has no landing-pad lowering");
        assert!(matches!(err, WasmLowerError::UnsupportedInst(_)), "{err}");
        assert!(err.to_string().contains("LandingPad"), "{err}");

        let unreachable_zero_result_pad = make_module(
            "wasm_reject_unreachable_landing_pad",
            vec![
                TrustIrBlock {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![InstrNode::new(Inst::Return { values: vec![] })],
                },
                TrustIrBlock {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::LandingPad {
                            is_cleanup: true,
                            catch_type_indices: vec![],
                        }),
                        InstrNode::new(Inst::Return { values: vec![] }),
                    ],
                },
            ],
        );
        let err = compile_module(&unreachable_zero_result_pad)
            .expect_err("the whole-function EH scan must include unreachable zero-result nodes");
        assert!(matches!(err, WasmLowerError::UnsupportedInst(_)), "{err}");
        assert!(err.to_string().contains("LandingPad"), "{err}");
    }

    /// Cross-check the backend's actual opcode emission against the
    /// proof-validated source-of-truth decode in trust-cg-verify. Closes the gap
    /// the refinement proofs (which hand-mirror the table) cannot: if
    /// `int_binop_opcode` ever emits the wrong opcode for a `BinOp`, the byte
    /// decodes to the wrong `WasmAluOp` and THIS unit test fails — so a backend
    /// opcode bug is caught by a test, not only by execution.
    #[test]
    fn backend_opcodes_match_proven_semantics() {
        use trust_cg_verify::wasm_semantics::{WasmAluOp, decode_int_binop};
        let cases = [
            (BinOp::Add, WasmAluOp::Add),
            (BinOp::Sub, WasmAluOp::Sub),
            (BinOp::Mul, WasmAluOp::Mul),
            (BinOp::SDiv, WasmAluOp::DivS),
            (BinOp::UDiv, WasmAluOp::DivU),
            (BinOp::SRem, WasmAluOp::RemS),
            (BinOp::URem, WasmAluOp::RemU),
            (BinOp::And, WasmAluOp::And),
            (BinOp::Or, WasmAluOp::Or),
            (BinOp::Xor, WasmAluOp::Xor),
            (BinOp::Shl, WasmAluOp::Shl),
            (BinOp::AShr, WasmAluOp::ShrS),
            (BinOp::LShr, WasmAluOp::ShrU),
        ];
        for (binop, expected) in cases {
            for vt in [ValType::I32, ValType::I64] {
                let byte = int_binop_opcode(binop, vt)
                    .unwrap_or_else(|e| panic!("{binop:?}/{vt:?} should lower: {e}"));
                assert_eq!(
                    decode_int_binop(byte),
                    Some(expected),
                    "backend emits {byte:#x} for {binop:?}/{vt:?} — decodes to {:?}, not {expected:?}",
                    decode_int_binop(byte),
                );
            }
        }
    }

    #[test]
    fn run_length_encode_groups_consecutive() {
        use ValType::*;
        assert_eq!(run_length_encode(&[]), vec![]);
        assert_eq!(run_length_encode(&[I32, I32, I32]), vec![(3, I32)]);
        assert_eq!(
            run_length_encode(&[I32, I64, I64, I32]),
            vec![(1, I32), (2, I64), (1, I32)]
        );
    }
}
