// trust-cg-codegen/tests/e2e_aarch64_vector_spills.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Q-register (128-bit NEON) spills, pair-spill refusal and the LL/SC
//! whole-window spill strategy, natively at O0-O3 (ledger L10-P10).
//!
//! Four vector fixtures keep more 128-bit values live than the Fpr128
//! allocation pool holds (`aarch64_allocatable_regs`: V0-V7 and V18-V31;
//! V8-V15 are excluded because AAPCS64 preserves only their low halves, and
//! V16/V17 are the spill scratches). The across-call fixture keeps fewer
//! (12) live across a call, which clobbers every pool register. Either way
//! the allocator spills Q registers into 16-byte, 16-byte-aligned slots
//! (`STR/LDR Qn`, stamped `SPILL_SLOT_ACCESS`).
//! Each prepared stream is checked three ways:
//!
//! * the final machine stream carries flagged 16-byte spill accesses at
//!   16-byte-aligned frame offsets, and the frame dataflow net
//!   (`[TCG-A64-SPILL-SLOT]`) models it (no decline) and checks at least every
//!   Q reload against its spill store;
//! * the object's words are decoded independently of the compiler (Arm ARM
//!   field masks) for `STR/LDR Q` and `STUR/LDUR Q` frame traffic;
//! * the linked program runs natively and matches a C model (wrapping
//!   unsigned lane arithmetic).
//!
//! Fixtures: vector-only pressure; mixed scalar/vector pressure; Q values live
//! across a call (every Fpr128 register is caller-clobbered, so each one is
//! spilled and reloaded around the call and no Q view of V8-V15 appears);
//! vector pressure in a dynamic frame (runtime-sized alloca), whose FP-relative
//! Q spill offsets need scratch-register legalization; and LL/SC atomics under
//! vector and scalar pressure on the BASELINE profile, where the pseudos need
//! more registers for spilled operands than X16/X17 and the whole-window spill
//! strategy borrows (and, when live, saves and restores) allocatable registers
//! outside every exclusive window. A second BASELINE LL/SC fixture branches on
//! the compare-exchange outcome and consumes its 28 live scalars only in the
//! two successor blocks, so a borrowed register is live after a pseudo only
//! through a successor's live-in set; the test requires such a save, and
//! native execution catches its omission.
//!
//! Corruption controls, each rejected by name at encoding: a deleted Q spill
//! store, a Q reload shifted by half a slot, onto the frame record or below the
//! frame, a Q reload into the wrong register, a 128-bit value kept in V8
//! across the call (`call-clobbered-upper-half-read`), two spill stores fused
//! into a flagged pair (`[TCG-A64-PAIR-SPILL]`: the allocator never forms pair
//! spills), and a spill reload or a plain load moved inside an exclusive
//! window (`[TCG-LLSC-SPILL-WINDOW]`, `[TCG-LLSC-WINDOW]`). A Q reload moved by
//! one whole slot onto another Q spill cell is the net's documented gap (the
//! final stream carries no slot identity): it encodes, and native execution
//! against the C model catches it.
//!
//! This is native differential and structural testing evidence for the
//! Darwin (and, not yet run, the Linux GNU) AArch64 floor. It is not a proof of
//! register allocation, spill placement, the exclusive monitor or forward
//! progress.

#[path = "common/native_host.rs"]
mod native_host;
#[path = "common/rosetta.rs"]
mod process;

use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig, encode_function};
use trust_cg_codegen::target::AArch64IsaProfile;
use trust_cg_ir::aarch64_regs::{V8, V16, V17, X29};
use trust_cg_ir::llsc::{is_exclusive_load, is_exclusive_store};
use trust_cg_ir::regs::{RegClass, preg_class};
use trust_cg_ir::{AArch64Opcode, InstFlags, InstId, MachFunction, MachInst, MachOperand, PReg};
use trust_cg_verify::post_ra_spill_slots::{
    FrameNetOutcome, FrameNetStats, SpillSlotViolationKind, analyze_frame,
};
use trust_ir::{
    AtomicRMWOp, BinOp, Block, BlockId, CastOp, Constant, FuncId, FuncTy, Function, Inst,
    InstrNode, Module, Ordering, Ty, ValueId,
};

const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
/// Live <4 x i32> values in the vector-only fixture.
const VEC_PRESSURE: usize = 40;
/// Live <4 x i32> values across the call.
const VEC_CALL: usize = 12;
/// Live <4 x i32> and i64 values in the mixed fixture.
const MIXED_VECTORS: usize = 28;
const MIXED_SCALARS: usize = 28;
/// Live <4 x i32> values in the dynamic-frame fixture.
const DYN_VECTORS: usize = 56;
/// Live <4 x i32> and u64 values in the LL/SC fixture.
const LLSC_VECTORS: usize = 28;
const LLSC_SCALARS: usize = 24;
/// Live u64 values across the branching LL/SC fixture's compare-exchange,
/// consumed only in its two successor blocks (the Gpr64 pool holds 25).
const LLSC_BRANCH_SCALARS: usize = 28;
/// Native rounds per program.
const ROUNDS: u64 = 64;

/// The allocator's Fpr128 pool: its size, after checking that it excludes
/// V8-V15 (partially callee-saved) and the V16/V17 spill scratches.
fn fpr128_pool() -> usize {
    let pool = trust_cg_regalloc::aarch64_allocatable_regs()
        .remove(&RegClass::Fpr128)
        .expect("Fpr128 pool");
    for reg in &pool {
        let number = reg.encoding() - trust_cg_ir::aarch64_regs::V0.encoding();
        assert!(
            !(8..=17).contains(&number),
            "Fpr128 pool must exclude V8-V17: {reg:?}"
        );
    }
    pool.len()
}

fn v4i32() -> Ty {
    Ty::Vector(Box::new(Ty::I32), 4)
}

// ---------------------------------------------------------------------------
// Fixture builders
// ---------------------------------------------------------------------------

struct Body {
    next: u32,
    body: Vec<InstrNode>,
}

impl Body {
    fn new(params: u32) -> Self {
        Self {
            next: params,
            body: Vec::new(),
        }
    }

    fn fresh(&mut self) -> ValueId {
        let id = ValueId::new(self.next);
        self.next += 1;
        id
    }

    fn emit(&mut self, inst: Inst) -> ValueId {
        let id = self.fresh();
        self.body.push(InstrNode::new(inst).with_result(id));
        id
    }

    fn const_i64(&mut self, value: i64) -> ValueId {
        self.emit(Inst::Const {
            ty: Ty::I64,
            value: Constant::i64(value),
        })
    }

    fn address(&mut self, pointee: Ty, base: ValueId, index: i64) -> ValueId {
        let index = self.const_i64(index);
        self.emit(Inst::GEP {
            pointee_ty: pointee,
            base,
            indices: vec![index],
            inbounds: true,
        })
    }

    fn load(&mut self, ty: Ty, ptr: ValueId, volatile: bool) -> ValueId {
        self.emit(Inst::Load {
            ty,
            ptr,
            volatile,
            align: None,
        })
    }

    fn load_vectors(&mut self, base: ValueId, count: usize) -> Vec<ValueId> {
        (0..count)
            .map(|i| {
                let address = self.address(Ty::I32, base, 4 * i as i64);
                self.load(v4i32(), address, false)
            })
            .collect()
    }

    fn load_scalars(&mut self, ty: Ty, base: ValueId, count: usize) -> Vec<ValueId> {
        (0..count)
            .map(|i| {
                let address = self.address(ty.clone(), base, i as i64);
                self.load(ty.clone(), address, false)
            })
            .collect()
    }

    fn binop(&mut self, op: BinOp, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.emit(Inst::BinOp { op, ty, lhs, rhs })
    }

    /// `acc = v0 + ... + v(n-1); for i: acc = (acc * v_i) ^ v_((7i+3) mod n)`,
    /// so every value stays live until the second phase consumes it.
    fn combine(&mut self, ty: Ty, values: &[ValueId]) -> ValueId {
        let mut acc = values[0];
        for &value in &values[1..] {
            acc = self.binop(BinOp::Add, ty.clone(), acc, value);
        }
        let n = values.len();
        for i in 0..n {
            let product = self.binop(BinOp::Mul, ty.clone(), acc, values[i]);
            acc = self.binop(BinOp::Xor, ty.clone(), product, values[(7 * i + 3) % n]);
        }
        acc
    }

    fn store(&mut self, ty: Ty, ptr: ValueId, value: ValueId, volatile: bool) {
        self.body.push(InstrNode::new(Inst::Store {
            ty,
            ptr,
            value,
            volatile,
            align: None,
        }));
    }

    fn finish(mut self, values: Vec<ValueId>) -> Vec<InstrNode> {
        self.body.push(InstrNode::new(Inst::Return { values }));
        self.body
    }
}

fn add_function(
    module: &mut Module,
    name: &str,
    params: Vec<Ty>,
    returns: Vec<Ty>,
    body: Vec<InstrNode>,
) {
    let sig = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(
        FuncId::new(module.functions.len() as u32),
        name,
        sig,
        BlockId::new(0),
    );
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: params
            .into_iter()
            .enumerate()
            .map(|(id, ty)| (ValueId::new(id as u32), ty))
            .collect(),
        body,
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

/// Like [`add_function`], with the entry block's parameters and then one
/// parameterless block per further body.
fn add_function_blocks(
    module: &mut Module,
    name: &str,
    params: Vec<Ty>,
    returns: Vec<Ty>,
    bodies: Vec<Vec<InstrNode>>,
) {
    let sig = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(
        FuncId::new(module.functions.len() as u32),
        name,
        sig,
        BlockId::new(0),
    );
    let entry_params: Vec<(ValueId, Ty)> = params
        .into_iter()
        .enumerate()
        .map(|(id, ty)| (ValueId::new(id as u32), ty))
        .collect();
    function.blocks = bodies
        .into_iter()
        .enumerate()
        .map(|(index, body)| Block {
            id: BlockId::new(index as u32),
            params: if index == 0 {
                entry_params.clone()
            } else {
                Vec::new()
            },
            body,
        })
        .collect();
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

fn new_module(name: &str) -> Module {
    let mut module = Module::new(name);
    module.target_info = Some(native_host::target_info());
    module
}

/// `vec_pressure(const u32 *src, u32 *out)`: 40 live <4 x i32>.
fn vec_pressure_module() -> Module {
    let mut module = new_module("vec_pressure");
    let mut b = Body::new(2);
    let vectors = b.load_vectors(ValueId::new(0), VEC_PRESSURE);
    let acc = b.combine(v4i32(), &vectors);
    b.store(v4i32(), ValueId::new(1), acc, false);
    add_function(
        &mut module,
        "vec_pressure",
        vec![Ty::Ptr, Ty::Ptr],
        vec![],
        b.finish(vec![]),
    );
    module
}

/// `vec_call(const u32 *src, u32 *out, i64 x) -> i64`: 12 live <4 x i32>
/// across `vec_call_helper(out, x)`, which writes memory and returns
/// `3x + 1`.
fn vec_call_module() -> Module {
    let mut module = new_module("vec_call");
    let mut b = Body::new(3);
    let vectors = b.load_vectors(ValueId::new(0), VEC_CALL);
    let result = b.emit(Inst::Call {
        callee: FuncId::new(1),
        args: vec![ValueId::new(1), ValueId::new(2)],
    });
    let acc = b.combine(v4i32(), &vectors);
    b.store(v4i32(), ValueId::new(1), acc, false);
    add_function(
        &mut module,
        "vec_call",
        vec![Ty::Ptr, Ty::Ptr, Ty::I64],
        vec![Ty::I64],
        b.finish(vec![result]),
    );
    let mut h = Body::new(2);
    let three = h.const_i64(3);
    let one = h.const_i64(1);
    let scaled = h.binop(BinOp::Mul, Ty::I64, ValueId::new(1), three);
    let biased = h.binop(BinOp::Add, Ty::I64, scaled, one);
    h.store(Ty::I64, ValueId::new(0), biased, false);
    add_function(
        &mut module,
        "vec_call_helper",
        vec![Ty::Ptr, Ty::I64],
        vec![Ty::I64],
        h.finish(vec![biased]),
    );
    module
}

/// `mixed_pressure(const u32 *src_v, const u64 *src_s, u32 *out) -> i64`:
/// 28 live <4 x i32> and 28 live i64.
fn mixed_module() -> Module {
    let mut module = new_module("mixed_pressure");
    let mut b = Body::new(3);
    let vectors = b.load_vectors(ValueId::new(0), MIXED_VECTORS);
    let scalars = b.load_scalars(Ty::I64, ValueId::new(1), MIXED_SCALARS);
    let vacc = b.combine(v4i32(), &vectors);
    let sacc = b.combine(Ty::I64, &scalars);
    b.store(v4i32(), ValueId::new(2), vacc, false);
    add_function(
        &mut module,
        "mixed_pressure",
        vec![Ty::Ptr, Ty::Ptr, Ty::Ptr],
        vec![Ty::I64],
        b.finish(vec![sacc]),
    );
    module
}

/// `vec_dynamic(const u32 *src, u32 *out, i64 n)`: a runtime-sized
/// `alloca u32 x n` (so SP is unknown after it and every spill slot is
/// addressed from X29), 56 live <4 x i32>, and the first vector round-tripped
/// through the alloca with volatile accesses so the frame stays dynamic.
fn vec_dynamic_module() -> Module {
    let mut module = new_module("vec_dynamic");
    let mut b = Body::new(3);
    let mut vectors = b.load_vectors(ValueId::new(0), DYN_VECTORS);
    let buffer = b.emit(Inst::Alloca {
        ty: Ty::U32,
        count: Some(ValueId::new(2)),
        align: Some(16),
    });
    // The last four elements, at a runtime index: an unbounded footprint keeps
    // the allocation runtime-sized.
    let four = b.const_i64(4);
    let last = b.binop(BinOp::Sub, Ty::I64, ValueId::new(2), four);
    let tail = b.emit(Inst::GEP {
        pointee_ty: Ty::U32,
        base: buffer,
        indices: vec![last],
        inbounds: true,
    });
    b.store(v4i32(), tail, vectors[0], true);
    vectors[0] = b.load(v4i32(), tail, true);
    let acc = b.combine(v4i32(), &vectors);
    b.store(v4i32(), ValueId::new(1), acc, false);
    add_function(
        &mut module,
        "vec_dynamic",
        vec![Ty::Ptr, Ty::Ptr, Ty::I64],
        vec![],
        b.finish(vec![]),
    );
    module
}

/// `llsc_pressure(const u32 *src_v, const u64 *src_s, u64 *atom, u64 v,
/// u32 *out) -> u64` on the BASELINE profile: a SeqCst fetch-add and an
/// AcqRel/Acquire compare-exchange under 28 live <4 x i32> and 24 live u64.
fn llsc_module() -> Module {
    let mut module = new_module("llsc_vector_pressure");
    let mut b = Body::new(5);
    let vectors = b.load_vectors(ValueId::new(0), LLSC_VECTORS);
    let scalars = b.load_scalars(Ty::U64, ValueId::new(1), LLSC_SCALARS);
    let old = b.emit(Inst::AtomicRMW {
        op: AtomicRMWOp::Add,
        ty: Ty::U64,
        ptr: ValueId::new(2),
        value: ValueId::new(3),
        ordering: Ordering::SeqCst,
    });
    let swapped = b.fresh();
    let ok = b.fresh();
    b.body.push(
        InstrNode::new(Inst::CmpXchg {
            ty: Ty::U64,
            ptr: ValueId::new(2),
            expected: scalars[0],
            desired: scalars[1],
            success: Ordering::AcqRel,
            failure: Ordering::Acquire,
            weak: false,
        })
        .with_results(vec![swapped, ok]),
    );
    let vacc = b.combine(v4i32(), &vectors);
    b.store(v4i32(), ValueId::new(4), vacc, false);
    let mut sacc = b.combine(Ty::U64, &scalars);
    sacc = b.binop(BinOp::Xor, Ty::U64, sacc, old);
    sacc = b.binop(BinOp::Add, Ty::U64, sacc, swapped);
    let ok_wide = b.emit(Inst::Cast {
        op: CastOp::ZExt,
        src_ty: Ty::Bool,
        dst_ty: Ty::U64,
        operand: ok,
    });
    sacc = b.binop(BinOp::Add, Ty::U64, sacc, ok_wide);
    add_function(
        &mut module,
        "llsc_pressure",
        vec![
            Ty::Ptr,
            Ty::Ptr,
            Ty::PtrMut(Box::new(Ty::U64)),
            Ty::U64,
            Ty::Ptr,
        ],
        vec![Ty::U64],
        b.finish(vec![sacc]),
    );
    module
}

/// `llsc_branch(const u64 *src_s, u64 *atom, u64 v) -> u64` on the BASELINE
/// profile: a SeqCst fetch-add and an AcqRel/Acquire compare-exchange under
/// 28 live u64, then a branch on the compare-exchange outcome. Every loaded
/// value is consumed only in the two successor blocks, so a register holding
/// one is live after the pseudos only through the successors' live-in sets:
/// the cross-block half of the borrow liveness.
fn llsc_branch_module() -> Module {
    let mut module = new_module("llsc_branch");
    let mut b = Body::new(3);
    let scalars = b.load_scalars(Ty::U64, ValueId::new(0), LLSC_BRANCH_SCALARS);
    let old = b.emit(Inst::AtomicRMW {
        op: AtomicRMWOp::Add,
        ty: Ty::U64,
        ptr: ValueId::new(1),
        value: ValueId::new(2),
        ordering: Ordering::SeqCst,
    });
    let swapped = b.fresh();
    let ok = b.fresh();
    b.body.push(
        InstrNode::new(Inst::CmpXchg {
            ty: Ty::U64,
            ptr: ValueId::new(1),
            expected: scalars[0],
            desired: scalars[1],
            success: Ordering::AcqRel,
            failure: Ordering::Acquire,
            weak: false,
        })
        .with_results(vec![swapped, ok]),
    );
    b.body.push(InstrNode::new(Inst::CondBr {
        cond: ok,
        then_target: BlockId::new(1),
        then_args: Vec::new(),
        else_target: BlockId::new(2),
        else_args: Vec::new(),
    }));
    let entry = std::mem::take(&mut b.body);
    // Swapped: `combine ^ old + swapped`.
    let mut acc = b.combine(Ty::U64, &scalars);
    acc = b.binop(BinOp::Xor, Ty::U64, acc, old);
    acc = b.binop(BinOp::Add, Ty::U64, acc, swapped);
    b.body
        .push(InstrNode::new(Inst::Return { values: vec![acc] }));
    let then_block = std::mem::take(&mut b.body);
    // Not swapped: `combine + old ^ swapped`.
    let mut acc = b.combine(Ty::U64, &scalars);
    acc = b.binop(BinOp::Add, Ty::U64, acc, old);
    acc = b.binop(BinOp::Xor, Ty::U64, acc, swapped);
    let else_block = b.finish(vec![acc]);
    add_function_blocks(
        &mut module,
        "llsc_branch",
        vec![Ty::Ptr, Ty::PtrMut(Box::new(Ty::U64)), Ty::U64],
        vec![Ty::U64],
        vec![entry, then_block, else_block],
    );
    module
}

// ---------------------------------------------------------------------------
// Pipeline routes
// ---------------------------------------------------------------------------

fn pipeline(opt_level: OptLevel, baseline: bool) -> Pipeline {
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level,
        target_triple: native_host::TRIPLE.into(),
        ..PipelineConfig::default()
    });
    if baseline {
        pipeline.with_aarch64_isa_profile(AArch64IsaProfile::BASELINE)
    } else {
        pipeline
    }
}

fn lowered(module: &Module) -> Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)> {
    assert!(trust_ir_build::validate::validate_module(module).is_empty());
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect("fixture must translate")
}

/// One object per function, through the full pipeline.
fn compile(module: &Module, opt_level: OptLevel, baseline: bool) -> Vec<Vec<u8>> {
    let pipeline = pipeline(opt_level, baseline);
    lowered(module)
        .iter()
        .map(|(function, _)| {
            pipeline
                .compile_function(function)
                .unwrap_or_else(|error| panic!("{} at {opt_level:?}: {error}", function.name))
        })
        .collect()
}

/// The prepared (allocated, spill-materialized, frame-lowered, expanded,
/// resolved) machine stream of the module's first function.
fn prepared(module: &Module, opt_level: OptLevel, baseline: bool) -> MachFunction {
    let lir = lowered(module);
    let (func, metrics) = pipeline(opt_level, baseline)
        .prepare_function_with_metrics(&lir[0].0, Some(&lir[0].1))
        .unwrap_or_else(|error| panic!("{opt_level:?}: prepare failed: {error}"));
    assert!(
        metrics.spill_slot_count > 0,
        "{opt_level:?}: the fixture must spill"
    );
    func
}

// ---------------------------------------------------------------------------
// Machine-stream inspection
// ---------------------------------------------------------------------------

fn data_reg(inst: &MachInst) -> Option<PReg> {
    match inst.operands.first() {
        Some(MachOperand::PReg(reg)) => Some(*reg),
        _ => None,
    }
}

fn mem_operand(inst: &MachInst) -> Option<(PReg, i64)> {
    inst.operands.iter().find_map(|op| match op {
        MachOperand::MemOp { base, offset } => Some((*base, *offset)),
        _ => None,
    })
}

fn is_q(reg: PReg) -> bool {
    preg_class(reg) == RegClass::Fpr128
}

/// Every instruction of the stream in layout order.
fn layout(func: &MachFunction) -> Vec<InstId> {
    func.block_order
        .iter()
        .flat_map(|block| func.blocks[block.0 as usize].insts.clone())
        .collect()
}

/// `(q_stores, q_reloads, other_spill_accesses)` over the whole stream.
fn spill_access_counts(func: &MachFunction) -> (usize, usize, usize) {
    let mut counts = (0, 0, 0);
    for id in layout(func) {
        let inst = &func.insts[id.0 as usize];
        if !inst.flags.is_spill_slot_access() {
            continue;
        }
        let q = data_reg(inst).is_some_and(is_q);
        match (inst.opcode, q) {
            (AArch64Opcode::StrRI, true) => counts.0 += 1,
            (AArch64Opcode::LdrRI, true) => counts.1 += 1,
            _ => counts.2 += 1,
        }
    }
    counts
}

/// Every flagged Q spill access addresses a 16-byte-aligned frame offset:
/// directly from X29 or SP, or (a legalized far offset) through X16/X17
/// holding `frame base + offset`. Returns the number of legalized accesses.
fn assert_q_spill_slots_aligned(func: &MachFunction, what: &str) -> usize {
    let mut legalized = 0;
    for id in layout(func) {
        let inst = &func.insts[id.0 as usize];
        if !inst.flags.is_spill_slot_access() || !data_reg(inst).is_some_and(is_q) {
            continue;
        }
        let (base, offset) = mem_operand(inst).unwrap_or_else(|| {
            panic!("{what}: Q spill access without a resolved frame operand: {inst:?}")
        });
        match base.encoding() {
            29 | 31 => assert_eq!(
                offset % 16,
                0,
                "{what}: Q spill slot not 16-byte aligned: {inst:?}"
            ),
            16 | 17 => {
                assert_eq!(offset, 0, "{what}: legalized Q access: {inst:?}");
                legalized += 1;
            }
            _ => panic!("{what}: Q spill base must be X29, SP, X16 or X17: {inst:?}"),
        }
    }
    legalized
}

fn analyzed(func: &MachFunction, what: &str) -> FrameNetStats {
    match analyze_frame(func) {
        FrameNetOutcome::Analyzed { violations, stats } => {
            assert!(
                violations.is_empty(),
                "{what}: clean stream reported {violations:?}"
            );
            stats
        }
        FrameNetOutcome::Declined(reason) => panic!("{what}: net declined ({})", reason.tag()),
    }
}

/// No instruction names the 128-bit view of V8-V15: a Q value never lives in
/// a partially callee-saved register.
fn assert_no_q_view_of_v8_to_v15(func: &MachFunction, what: &str) {
    for id in layout(func) {
        let inst = &func.insts[id.0 as usize];
        for operand in &inst.operands {
            if let MachOperand::PReg(reg) = operand {
                assert!(
                    !(72..=79).contains(&reg.encoding()),
                    "{what}: Q view of V8-V15 in {inst:?}"
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Independent word decoding (Arm ARM field masks)
// ---------------------------------------------------------------------------

fn frame_based(word: u32) -> bool {
    matches!(word >> 5 & 31, 29 | 31)
}

/// `STR Qt, [Xn, #imm]` (unsigned offset) or `STUR Qt` against SP/X29
/// (load/store register SIMD&FP, size=00 opc=10).
fn is_q_spill_store(word: u32) -> bool {
    (word & 0xffc0_0000 == 0x3d80_0000 || word & 0xffe0_0c00 == 0x3c80_0000) && frame_based(word)
}

/// `LDR Qt, [Xn, #imm]` or `LDUR Qt` against SP/X29 (size=00 opc=11).
fn is_q_spill_load(word: u32) -> bool {
    (word & 0xffc0_0000 == 0x3dc0_0000 || word & 0xffe0_0c00 == 0x3cc0_0000) && frame_based(word)
}

/// `LDR/STR Qt, [X16|X17]`: a legalized far Q access (unsigned offset 0).
fn is_q_access_through_ip_scratch(word: u32) -> bool {
    matches!(word & 0xffff_fc00, 0x3d80_0000 | 0x3dc0_0000) && matches!(word >> 5 & 31, 16 | 17)
}

/// Single-register W/X `LDR/STR` (unsigned offset or unscaled) against SP/X29.
fn is_gpr_spill_word(word: u32) -> bool {
    (word & 0x3f00_0000 == 0x3900_0000 || word & 0x3f20_0c00 == 0x3800_0000)
        && word >> 30 >= 2
        && frame_based(word)
}

/// Every load/store-class word (op0 = x1x0).
fn is_load_store(word: u32) -> bool {
    word & 0x0a00_0000 == 0x0800_0000
}

/// Load/store exclusive, single register or pair: `(load, pair)`.
fn exclusive(word: u32) -> Option<(bool, bool)> {
    if word & 0x3fa0_7c00 == 0x0800_7c00 {
        return Some((word >> 22 & 1 == 1, false));
    }
    if word & 0xbfa0_0000 == 0x8820_0000 {
        return Some((word >> 22 & 1 == 1, true));
    }
    None
}

/// Any LSE single-instruction atomic (LD<op>/SWP or CAS/CASP).
fn is_lse(word: u32) -> bool {
    word & 0x3f20_0c00 == 0x3820_0000
        || word & 0x3fa0_7c00 == 0x08a0_7c00
        || word & 0xbfa0_7c00 == 0x0820_7c00
}

/// Number of exclusive windows; every word strictly between a load-exclusive
/// and its store-exclusive must be a non-memory instruction.
fn spill_free_exclusive_windows(words: &[u32], what: &str) -> usize {
    let mut windows = 0;
    let mut index = 0;
    while index < words.len() {
        let Some((true, _)) = exclusive(words[index]) else {
            index += 1;
            continue;
        };
        let mut cursor = index + 1;
        loop {
            let word = *words
                .get(cursor)
                .unwrap_or_else(|| panic!("{what}: load-exclusive at {index} without a store"));
            if let Some((load, _)) = exclusive(word) {
                assert!(
                    !load,
                    "{what}: two load-exclusives without a store at {cursor}"
                );
                break;
            }
            assert!(
                !is_load_store(word),
                "{what}: memory access {word:#010x} inside the exclusive window at {cursor}"
            );
            cursor += 1;
            assert!(cursor - index <= 8, "{what}: exclusive window too long");
        }
        windows += 1;
        index = cursor + 1;
    }
    windows
}

// ---------------------------------------------------------------------------
// Native execution
// ---------------------------------------------------------------------------

fn scratch(tag: &str) -> PathBuf {
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "trust-cg-vector-spills-{tag}-{}-{stamp}",
        std::process::id()
    ));
    fs::create_dir_all(&path).unwrap();
    path
}

/// Link `objects` with `driver`, run it natively and return `(exit success,
/// stdout)`.
fn link_and_run_status(tag: &str, objects: &[Vec<u8>], driver: &str) -> (bool, String) {
    let root = scratch(tag);
    let driver_path = root.join("driver.c");
    fs::write(&driver_path, driver).unwrap();
    let mut link = Command::new(native_host::C_COMPILER);
    link.args(["-O2", "-std=c11"]).arg(&driver_path);
    for (index, object) in objects.iter().enumerate() {
        let path = root.join(format!("f{index}.o"));
        fs::write(&path, object).unwrap();
        link.arg(path);
    }
    let executable = root.join("driver");
    link.args(native_host::link_hardening_args())
        .arg("-o")
        .arg(&executable);
    let linked =
        process::command_output_with_timeout(&mut link, process::codegen_link_timeout()).unwrap();
    assert!(
        !linked.timed_out && linked.output.status.success(),
        "{tag}: link failed in {}: {}",
        root.display(),
        String::from_utf8_lossy(&linked.output.stderr)
    );
    let run =
        process::run_executable_with_timeout(&executable, process::codegen_run_timeout()).unwrap();
    assert!(
        !run.timed_out,
        "{tag}: native run timed out in {}",
        root.display()
    );
    let stdout = String::from_utf8_lossy(&run.output.stdout).into_owned();
    fs::remove_dir_all(root).unwrap();
    (run.output.status.success(), stdout)
}

/// Link and run; the program must succeed. Returns stdout.
fn link_and_run(tag: &str, objects: &[Vec<u8>], driver: &str) -> String {
    let (success, stdout) = link_and_run_status(tag, objects, driver);
    assert!(success, "{tag}: native run failed: {stdout}");
    stdout
}

/// The C model of [`Body::combine`] over `uint32_t` lanes and over
/// `uint64_t`, plus the shared input generators.
const C_MODEL: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <string.h>
static void combine_v(const uint32_t *src, int n, uint32_t out[4]) {
  uint32_t acc[4];
  for (int l = 0; l < 4; l++) acc[l] = src[l];
  for (int i = 1; i < n; i++) for (int l = 0; l < 4; l++) acc[l] += src[4 * i + l];
  for (int i = 0; i < n; i++) {
    int j = (7 * i + 3) % n;
    for (int l = 0; l < 4; l++) acc[l] = (acc[l] * src[4 * i + l]) ^ src[4 * j + l];
  }
  memcpy(out, acc, sizeof acc);
}
static uint64_t combine_s(const uint64_t *src, int n) {
  uint64_t acc = src[0];
  for (int i = 1; i < n; i++) acc += src[i];
  for (int i = 0; i < n; i++) acc = (acc * src[i]) ^ src[(7 * i + 3) % n];
  return acc;
}
static void fill_v(uint32_t *src, int n, uint64_t round) {
  for (int i = 0; i < 4 * n; i++) src[i] = (uint32_t)(0x9e3779b9u * (uint32_t)(i + 1)) ^ (uint32_t)(round * 0x85ebca6bu);
}
static void fill_s(uint64_t *src, int n, uint64_t round) {
  for (int i = 0; i < n; i++) src[i] = 0x9e3779b97f4a7c15ULL * (uint64_t)(i + 1) ^ (round * 0xc2b2ae3d27d4eb4fULL);
}
"#;

/// Driver for a `void f(const uint32_t *src, uint32_t *out[, int64_t n])`
/// vector fixture over `vectors` <4 x i32> inputs.
fn vector_driver(symbol: &str, vectors: usize, dynamic: bool) -> String {
    let (decl_tail, call_tail) = if dynamic {
        (", int64_t n", ", 4 * (int64_t)round + 4")
    } else {
        ("", "")
    };
    format!(
        r#"{C_MODEL}
extern void {symbol}(const uint32_t *src, uint32_t *out{decl_tail});
int main(void) {{
  uint32_t src[4 * {vectors}], want[4], got[4];
  unsigned checks = 0;
  for (uint64_t round = 0; round < {ROUNDS}; round++) {{
    fill_v(src, {vectors}, round);
    combine_v(src, {vectors}, want);
    memset(got, 0, sizeof got);
    {symbol}(src, got{call_tail});
    if (memcmp(got, want, sizeof got)) {{
      printf("round %llu: got %08x %08x %08x %08x want %08x %08x %08x %08x\n", (unsigned long long)round,
        got[0], got[1], got[2], got[3], want[0], want[1], want[2], want[3]);
      return 1;
    }}
    checks++;
  }}
  printf("{symbol}_checks=%u\n", checks);
  return 0;
}}
"#
    )
}

fn vec_call_driver() -> String {
    format!(
        r#"{C_MODEL}
extern int64_t vec_call(const uint32_t *src, uint32_t *out, int64_t x);
int main(void) {{
  uint32_t src[4 * {VEC_CALL}], want[4], got[4];
  unsigned checks = 0;
  for (uint64_t round = 0; round < {ROUNDS}; round++) {{
    fill_v(src, {VEC_CALL}, round);
    combine_v(src, {VEC_CALL}, want);
    memset(got, 0, sizeof got);
    int64_t x = (int64_t)(round * 12345) - 777;
    int64_t r = vec_call(src, got, x);
    if (r != x * 3 + 1 || memcmp(got, want, sizeof got)) {{
      printf("round %llu: r %lld got %08x %08x %08x %08x want %08x %08x %08x %08x\n", (unsigned long long)round,
        (long long)r, got[0], got[1], got[2], got[3], want[0], want[1], want[2], want[3]);
      return 1;
    }}
    checks++;
  }}
  printf("vec_call_checks=%u\n", checks);
  return 0;
}}
"#
    )
}

fn mixed_driver() -> String {
    format!(
        r#"{C_MODEL}
extern int64_t mixed_pressure(const uint32_t *src_v, const uint64_t *src_s, uint32_t *out);
int main(void) {{
  uint32_t src_v[4 * {MIXED_VECTORS}], want[4], got[4];
  uint64_t src_s[{MIXED_SCALARS}];
  unsigned checks = 0;
  for (uint64_t round = 0; round < {ROUNDS}; round++) {{
    fill_v(src_v, {MIXED_VECTORS}, round);
    fill_s(src_s, {MIXED_SCALARS}, round);
    combine_v(src_v, {MIXED_VECTORS}, want);
    uint64_t want_s = combine_s(src_s, {MIXED_SCALARS});
    memset(got, 0, sizeof got);
    uint64_t got_s = (uint64_t)mixed_pressure(src_v, src_s, got);
    if (got_s != want_s || memcmp(got, want, sizeof got)) {{
      printf("round %llu: scalar %llx/%llx vector %08x %08x %08x %08x / %08x %08x %08x %08x\n",
        (unsigned long long)round, (unsigned long long)got_s, (unsigned long long)want_s,
        got[0], got[1], got[2], got[3], want[0], want[1], want[2], want[3]);
      return 1;
    }}
    checks++;
  }}
  printf("mixed_checks=%u\n", checks);
  return 0;
}}
"#
    )
}

fn llsc_driver() -> String {
    format!(
        r#"{C_MODEL}
extern uint64_t llsc_pressure(const uint32_t *src_v, const uint64_t *src_s, uint64_t *atom, uint64_t v, uint32_t *out);
static uint64_t model(const uint32_t *src_v, const uint64_t *src_s, uint64_t *atom, uint64_t v, uint32_t *out) {{
  uint64_t old = *atom; *atom += v;
  uint64_t swapped = *atom; int ok = *atom == src_s[0]; if (ok) *atom = src_s[1];
  combine_v(src_v, {LLSC_VECTORS}, out);
  uint64_t acc = combine_s(src_s, {LLSC_SCALARS});
  acc ^= old; acc += swapped; acc += (uint64_t)ok;
  return acc;
}}
int main(void) {{
  uint32_t src_v[4 * {LLSC_VECTORS}], want[4], got[4];
  uint64_t src_s[{LLSC_SCALARS}];
  unsigned checks = 0, swaps = 0;
  for (uint64_t round = 0; round < {ROUNDS}; round++) {{
    fill_v(src_v, {LLSC_VECTORS}, round);
    fill_s(src_s, {LLSC_SCALARS}, round);
    uint64_t v = 3 + round * 2;
    uint64_t atom_a = round & 1 ? src_s[0] - v : round * 7, atom_b = atom_a;
    memset(got, 0, sizeof got);
    uint64_t want_s = model(src_v, src_s, &atom_b, v, want);
    uint64_t got_s = llsc_pressure(src_v, src_s, &atom_a, v, got);
    if (got_s != want_s || atom_a != atom_b || memcmp(got, want, sizeof got)) {{
      printf("round %llu: scalar %llx/%llx atom %llx/%llx\n", (unsigned long long)round,
        (unsigned long long)got_s, (unsigned long long)want_s,
        (unsigned long long)atom_a, (unsigned long long)atom_b);
      return 1;
    }}
    swaps += atom_b == src_s[1];
    checks++;
  }}
  printf("llsc_checks=%u swaps=%u\n", checks, swaps);
  return 0;
}}
"#
    )
}

fn llsc_branch_driver() -> String {
    format!(
        r#"{C_MODEL}
extern uint64_t llsc_branch(const uint64_t *src_s, uint64_t *atom, uint64_t v);
static uint64_t model(const uint64_t *src_s, uint64_t *atom, uint64_t v) {{
  uint64_t old = *atom; *atom += v;
  uint64_t swapped = *atom; int ok = *atom == src_s[0]; if (ok) *atom = src_s[1];
  uint64_t acc = combine_s(src_s, {LLSC_BRANCH_SCALARS});
  if (ok) {{ acc ^= old; acc += swapped; }} else {{ acc += old; acc ^= swapped; }}
  return acc;
}}
int main(void) {{
  uint64_t src_s[{LLSC_BRANCH_SCALARS}];
  unsigned checks = 0, swaps = 0;
  for (uint64_t round = 0; round < {ROUNDS}; round++) {{
    fill_s(src_s, {LLSC_BRANCH_SCALARS}, round);
    uint64_t v = 5 + round * 3;
    uint64_t atom_a = round & 1 ? src_s[0] - v : round * 11, atom_b = atom_a;
    uint64_t want = model(src_s, &atom_b, v);
    uint64_t got = llsc_branch(src_s, &atom_a, v);
    if (got != want || atom_a != atom_b) {{
      printf("round %llu: result %llx/%llx atom %llx/%llx\n", (unsigned long long)round,
        (unsigned long long)got, (unsigned long long)want,
        (unsigned long long)atom_a, (unsigned long long)atom_b);
      return 1;
    }}
    swaps += atom_b == src_s[1];
    checks++;
  }}
  printf("llsc_branch_checks=%u swaps=%u\n", checks, swaps);
  return 0;
}}
"#
    )
}

// ---------------------------------------------------------------------------
// Native controls at O0-O3
// ---------------------------------------------------------------------------

/// Why a fixture must spill Q registers.
#[derive(Clone, Copy)]
enum QSpillCause {
    /// More live 128-bit values than the Fpr128 pool holds.
    Pressure(usize),
    /// 128-bit values live across a call. [`fpr128_pool`] checks that the
    /// pool excludes V8-V15, so every pool register is caller-clobbered and
    /// each value must be spilled even though the pool could hold them all.
    AcrossCall(usize),
}

/// Shared shape: the prepared stream spills Q registers into aligned slots
/// and the frame net models it; the object's words carry Q spill traffic;
/// the linked program matches the C model. Returns the per-level prepared
/// streams.
fn check_fixture(
    name: &str,
    module: &Module,
    baseline: bool,
    driver: &str,
    expected_stdout: &str,
    cause: QSpillCause,
) -> Vec<(OptLevel, MachFunction, Vec<u32>)> {
    match cause {
        QSpillCause::Pressure(live_q) => assert!(
            live_q > fpr128_pool(),
            "{name}: {live_q} live vectors must exceed the Fpr128 pool"
        ),
        QSpillCause::AcrossCall(live_q) => assert!(
            live_q > 0 && live_q <= fpr128_pool(),
            "{name}: {live_q} vectors live across the call must fit the Fpr128 pool, so \
             the call, not pressure, forces their spills"
        ),
    }
    let mut streams = Vec::new();
    for opt_level in OPT_LEVELS {
        let what = format!("{name} {opt_level:?}");
        let func = prepared(module, opt_level, baseline);
        let (q_stores, q_reloads, others) = spill_access_counts(&func);
        assert!(
            q_stores > 0 && q_reloads > 0,
            "{what}: expected Q spill stores and reloads, found {q_stores}/{q_reloads}"
        );
        assert_q_spill_slots_aligned(&func, &what);
        assert_no_q_view_of_v8_to_v15(&func, &what);
        let stats = analyzed(&func, &what);
        assert!(
            stats.spill_reloads_checked as usize >= q_reloads,
            "{what}: net checked {} reloads, stream has {q_reloads} Q reloads",
            stats.spill_reloads_checked
        );
        encode_function(&func).unwrap_or_else(|error| panic!("{what}: encode failed: {error}"));

        let objects = compile(module, opt_level, baseline);
        let words = native_host::text_words(&objects[0]);
        let stores = words.iter().filter(|&&w| is_q_spill_store(w)).count();
        let loads = words.iter().filter(|&&w| is_q_spill_load(w)).count();
        let legalized = words
            .iter()
            .filter(|&&w| is_q_access_through_ip_scratch(w))
            .count();
        assert!(
            (stores > 0 || legalized > 0) && (loads > 0 || legalized > 0),
            "{what}: decoded {stores} STR Q / {loads} LDR Q / {legalized} legalized frame accesses"
        );
        if native_host::NATIVE {
            let stdout = link_and_run(&format!("{name}-{opt_level:?}"), &objects, driver);
            assert!(
                stdout.trim().starts_with(expected_stdout),
                "{what}: {stdout}"
            );
        }
        println!(
            "{what}: {q_stores} Q spill stores, {q_reloads} Q reloads, {others} other spill \
             accesses; net checked {} reloads; decoded {stores}/{loads}/{legalized}",
            stats.spill_reloads_checked
        );
        streams.push((opt_level, func, words));
    }
    streams
}

#[test]
fn vector_pressure_spills_q_registers_and_matches_c_model() {
    check_fixture(
        "vec_pressure",
        &vec_pressure_module(),
        false,
        &vector_driver("vec_pressure", VEC_PRESSURE, false),
        &format!("vec_pressure_checks={ROUNDS}"),
        QSpillCause::Pressure(VEC_PRESSURE),
    );
}

#[test]
fn mixed_scalar_vector_pressure_spills_both_banks_and_matches_c_model() {
    let streams = check_fixture(
        "mixed_pressure",
        &mixed_module(),
        false,
        &mixed_driver(),
        &format!("mixed_checks={ROUNDS}"),
        QSpillCause::Pressure(MIXED_VECTORS),
    );
    for (opt_level, func, words) in streams {
        let (_, _, others) = spill_access_counts(&func);
        assert!(others > 0, "{opt_level:?}: expected GPR spill traffic too");
        assert!(
            words.iter().any(|&w| is_gpr_spill_word(w)),
            "{opt_level:?}: decoded no GPR spill word"
        );
    }
}

#[test]
fn vector_values_live_across_a_call_are_spilled_and_reloaded() {
    let streams = check_fixture(
        "vec_call",
        &vec_call_module(),
        false,
        &vec_call_driver(),
        &format!("vec_call_checks={ROUNDS}"),
        QSpillCause::AcrossCall(VEC_CALL),
    );
    for (opt_level, func, _) in streams {
        // Twelve values live across the call, and no Fpr128 register survives
        // it: every one is spilled before and reloaded after.
        let insts = entry_insts(&func);
        let call = call_position(&func);
        let reloads_after = insts[call + 1..]
            .iter()
            .filter(|id| {
                let inst = &func.insts[id.0 as usize];
                inst.opcode == AArch64Opcode::LdrRI
                    && inst.flags.is_spill_slot_access()
                    && data_reg(inst).is_some_and(is_q)
            })
            .count();
        assert!(
            reloads_after >= VEC_CALL,
            "{opt_level:?}: {reloads_after} Q reloads after the call"
        );
        let stores_before = insts[..call]
            .iter()
            .filter(|id| {
                let inst = &func.insts[id.0 as usize];
                inst.opcode == AArch64Opcode::StrRI
                    && inst.flags.is_spill_slot_access()
                    && data_reg(inst).is_some_and(is_q)
            })
            .count();
        assert!(
            stores_before >= VEC_CALL,
            "{opt_level:?}: {stores_before} Q spill stores before the call"
        );
    }
}

#[test]
fn q_spills_in_a_dynamic_frame_are_fp_relative_and_legalized() {
    let module = vec_dynamic_module();
    let streams = check_fixture(
        "vec_dynamic",
        &module,
        false,
        &vector_driver("vec_dynamic", DYN_VECTORS, true),
        &format!("vec_dynamic_checks={ROUNDS}"),
        QSpillCause::Pressure(DYN_VECTORS),
    );
    let mut legalized = 0;
    for (opt_level, func, words) in streams {
        let what = format!("vec_dynamic {opt_level:?}");
        // SP is unknown after the runtime allocation, so every Q spill slot
        // is addressed from X29, directly or through a legalized X16/X17.
        for id in layout(&func) {
            let inst = &func.insts[id.0 as usize];
            if inst.flags.is_spill_slot_access() && data_reg(inst).is_some_and(is_q) {
                let (base, _) = mem_operand(inst).unwrap();
                assert_ne!(base.encoding(), 31, "{what}: SP-relative Q spill {inst:?}");
            }
        }
        let level = assert_q_spill_slots_aligned(&func, &what);
        let decoded = words
            .iter()
            .filter(|&&w| is_q_access_through_ip_scratch(w))
            .count();
        assert!(
            decoded >= level,
            "{what}: {level} legalized Q spill accesses, {decoded} decoded"
        );
        println!("{what}: {level} Q spill accesses legalized through X16/X17");
        legalized += level;
    }
    assert!(
        legalized > 0,
        "no Q spill offset needed legalization through X16/X17"
    );
}

/// Layout positions of the flagged spill accesses immediately before
/// (`before`, nearest first) and immediately after (`after`) the LL/SC loop
/// whose load-exclusive is at `head`: the loop ends at its retry `CBNZ`, or
/// for a compare-exchange at its `CLREX`.
struct WindowTraffic {
    before: Vec<usize>,
    after: Vec<usize>,
}

fn window_traffic(func: &MachFunction, insts: &[InstId], head: usize) -> WindowTraffic {
    let flagged = |pos: usize| {
        func.insts[insts[pos].0 as usize]
            .flags
            .is_spill_slot_access()
    };
    let mut before = Vec::new();
    let mut cursor = head;
    while cursor > 0 && flagged(cursor - 1) {
        cursor -= 1;
        before.push(cursor);
    }
    // The loop ends at the retry CBNZ, or for a compare-exchange at CLREX.
    let mut end = head + 1;
    while end < insts.len() {
        let opcode = func.insts[insts[end].0 as usize].opcode;
        if opcode == AArch64Opcode::Clrex {
            break;
        }
        if opcode == AArch64Opcode::Cbnz
            && !insts[end + 1..]
                .iter()
                .take(2)
                .any(|id| func.insts[id.0 as usize].opcode == AArch64Opcode::Clrex)
        {
            break;
        }
        end += 1;
    }
    let mut after = Vec::new();
    let mut cursor = end + 1;
    while cursor < insts.len() && flagged(cursor) {
        after.push(cursor);
        cursor += 1;
    }
    WindowTraffic { before, after }
}

fn is_ip(reg: PReg) -> bool {
    matches!(reg.encoding(), 16 | 17 | 48 | 49)
}

#[test]
fn baseline_llsc_windows_stay_spill_free_under_vector_and_scalar_pressure() {
    let module = llsc_module();
    let streams = check_fixture(
        "llsc_pressure",
        &module,
        true,
        &llsc_driver(),
        &format!("llsc_checks={ROUNDS}"),
        QSpillCause::Pressure(LLSC_VECTORS),
    );
    let mut decoded = 0;
    let mut beyond_ip_scratch = 0;
    let mut saved_and_restored = 0;
    for (opt_level, func, words) in streams {
        let what = format!("llsc_pressure {opt_level:?}");
        assert!(!words.iter().any(|&w| is_lse(w)), "{what}: LSE word");
        assert!(
            words.iter().any(|&w| is_gpr_spill_word(w)),
            "{what}: decoded no GPR spill word"
        );
        let windows = spill_free_exclusive_windows(&words, &what);
        assert_eq!(windows, 2, "{what}: one RMW and one CAS window");
        decoded += windows;

        // The whole-window strategy in the prepared stream: spill traffic of
        // each pseudo sits right before its load-exclusive and right after
        // its loop, never inside.
        let insts = layout(&func);
        for head in 0..insts.len() {
            if !is_exclusive_load(func.insts[insts[head].0 as usize].opcode) {
                continue;
            }
            let traffic = window_traffic(&func, &insts, head);
            let access = |pos: usize| {
                let inst = &func.insts[insts[pos].0 as usize];
                (
                    inst.opcode == AArch64Opcode::LdrRI,
                    data_reg(inst).unwrap(),
                    mem_operand(inst),
                )
            };
            let reloads_into_ip = traffic
                .before
                .iter()
                .filter(|&&pos| {
                    let (load, reg, _) = access(pos);
                    load && is_ip(reg)
                })
                .count();
            let def_store_from_other = traffic.after.iter().any(|&pos| {
                let (load, reg, _) = access(pos);
                !load && !is_ip(reg)
            });
            // Both IP scratches carry uses and a spilled def still needs a
            // third register: the case that used to be refused.
            if reloads_into_ip == 2 && def_store_from_other {
                beyond_ip_scratch += 1;
            }
            for &pos in &traffic.before {
                let (load, reg, address) = access(pos);
                if load || is_ip(reg) {
                    continue;
                }
                let restored = traffic
                    .after
                    .iter()
                    .any(|&after| access(after) == (true, reg, address));
                if restored {
                    saved_and_restored += 1;
                }
            }
        }
        println!("{what}: {windows} spill-free windows");
    }
    assert_eq!(decoded, 8);
    println!(
        "llsc_pressure: {beyond_ip_scratch} windows needed a third spill register, \
         {saved_and_restored} live borrowed registers saved and restored"
    );
    assert!(
        beyond_ip_scratch >= 1,
        "no level needs a third register for a pseudo's spilled operands"
    );
    assert!(
        saved_and_restored >= 1,
        "some level borrows a live register around a pseudo"
    );
}

/// Whether `inst` names general register number `n` (its X or W view) as an
/// operand, a memory base or an implicit operand.
fn mentions_gpr(inst: &MachInst, n: u16) -> bool {
    let named = |reg: PReg| reg.encoding() == n || reg.encoding() == n + 32;
    inst.operands.iter().any(|operand| match operand {
        MachOperand::PReg(reg) => named(*reg),
        MachOperand::MemOp { base, .. } => named(*base),
        _ => false,
    }) || inst
        .implicit_uses
        .iter()
        .chain(inst.implicit_defs)
        .any(|&reg| named(reg))
}

/// The borrow liveness across blocks. Every value loaded before the pseudos
/// is consumed only in the two successors of the compare-exchange's block,
/// so a register holding one is live after a pseudo only through the
/// successors' live-in sets. A borrowed register that the rest of its block
/// never names, yet is saved and restored around a pseudo, is one the
/// liveness found live in a successor; borrowing it unsaved would clobber a
/// value the successor reads, which the C model would catch natively.
#[test]
fn baseline_llsc_saves_borrowed_registers_live_only_in_successor_blocks() {
    let module = llsc_branch_module();
    let driver = llsc_branch_driver();
    let mut successor_only_saves = 0;
    for opt_level in OPT_LEVELS {
        let what = format!("llsc_branch {opt_level:?}");
        let func = prepared(&module, opt_level, true);
        analyzed(&func, &what);
        encode_function(&func).unwrap_or_else(|error| panic!("{what}: encode failed: {error}"));
        let mut pseudos = 0;
        let mut saves = 0;
        for block in &func.block_order {
            let block = &func.blocks[block.0 as usize];
            let insts = &block.insts;
            for head in 0..insts.len() {
                if !is_exclusive_load(func.insts[insts[head].0 as usize].opcode) {
                    continue;
                }
                pseudos += 1;
                let traffic = window_traffic(&func, insts, head);
                let access = |pos: usize| {
                    let inst = &func.insts[insts[pos].0 as usize];
                    (
                        inst.opcode == AArch64Opcode::LdrRI,
                        data_reg(inst).unwrap(),
                        mem_operand(inst),
                    )
                };
                let tail = traffic.after.last().map_or(head + 1, |&pos| pos + 1);
                for &pos in &traffic.before {
                    let (load, reg, address) = access(pos);
                    if load || is_ip(reg) {
                        continue;
                    }
                    let restored = traffic
                        .after
                        .iter()
                        .any(|&after| access(after) == (true, reg, address));
                    if !restored {
                        continue;
                    }
                    saves += 1;
                    let n = reg.encoding() % 32;
                    let named_later = insts[tail..]
                        .iter()
                        .any(|id| mentions_gpr(&func.insts[id.0 as usize], n));
                    if !named_later {
                        assert!(
                            !block.succs.is_empty(),
                            "{what}: {reg:?} saved around a pseudo in a block without successors"
                        );
                        successor_only_saves += 1;
                    }
                }
            }
        }
        assert_eq!(pseudos, 2, "{what}: one RMW and one CAS window");

        let objects = compile(&module, opt_level, true);
        let words = native_host::text_words(&objects[0]);
        assert!(!words.iter().any(|&w| is_lse(w)), "{what}: LSE word");
        assert_eq!(
            spill_free_exclusive_windows(&words, &what),
            2,
            "{what}: one RMW and one CAS window"
        );
        if native_host::NATIVE {
            let stdout = link_and_run(&format!("llsc_branch-{opt_level:?}"), &objects, &driver);
            let expected = format!("llsc_branch_checks={ROUNDS} swaps=");
            assert!(stdout.trim().starts_with(&expected), "{what}: {stdout}");
            let swaps: u64 = stdout.trim()[expected.len()..].parse().unwrap();
            assert!(
                swaps > 0 && swaps < ROUNDS,
                "{what}: both successors must run ({swaps} swaps)"
            );
        }
        println!("{what}: {saves} borrowed registers saved and restored");
    }
    println!("llsc_branch: {successor_only_saves} saves of registers live only in successors");
    assert!(
        successor_only_saves >= 1,
        "no level saves a borrowed register that only a successor block reads"
    );
}

// ---------------------------------------------------------------------------
// Corruption controls on the 16-byte spill cells (call fixture)
// ---------------------------------------------------------------------------

fn entry_insts(func: &MachFunction) -> Vec<InstId> {
    assert_eq!(
        func.blocks.len(),
        1,
        "the straight-line fixture stays one block"
    );
    func.blocks[func.entry.0 as usize].insts.clone()
}

fn call_position(func: &MachFunction) -> usize {
    entry_insts(func)
        .iter()
        .position(|id| func.insts[id.0 as usize].opcode == AArch64Opcode::Bl)
        .expect("fixture calls its helper")
}

/// Position of the first flagged Q reload after the call whose destination
/// is a call-clobbered V16-V31 register (V0-V7 count as defined by every
/// call, so a wrong-register control needs the clobbered bank).
fn q_reload_after_call(func: &MachFunction) -> usize {
    let insts = entry_insts(func);
    let call = call_position(func);
    insts
        .iter()
        .enumerate()
        .skip(call + 1)
        .find(|(_, id)| {
            let inst = &func.insts[id.0 as usize];
            inst.opcode == AArch64Opcode::LdrRI
                && inst.flags.is_spill_slot_access()
                && data_reg(inst).is_some_and(|reg| is_q(reg) && reg.encoding() >= V16.encoding())
        })
        .map(|(pos, _)| pos)
        .expect("a spilled Q value is reloaded into V16-V31 after the call")
}

/// Position of the flagged Q spill store before the call that writes the
/// cell the reload at `reload` reads.
fn q_store_for(func: &MachFunction, reload: usize) -> usize {
    let insts = entry_insts(func);
    let cell = mem_operand(&func.insts[insts[reload].0 as usize]);
    (0..call_position(func))
        .rev()
        .find(|&pos| {
            let inst = &func.insts[insts[pos].0 as usize];
            inst.opcode == AArch64Opcode::StrRI
                && inst.flags.is_spill_slot_access()
                && mem_operand(inst) == cell
        })
        .expect("the reloaded Q cell is spill-stored before the call")
}

fn inst_at(func: &mut MachFunction, pos: usize) -> &mut MachInst {
    let id = func.blocks[func.entry.0 as usize].insts[pos];
    &mut func.insts[id.0 as usize]
}

fn violation_kinds(func: &MachFunction) -> Vec<SpillSlotViolationKind> {
    match analyze_frame(func) {
        FrameNetOutcome::Analyzed { violations, .. } => violations.iter().map(|v| v.kind).collect(),
        FrameNetOutcome::Declined(reason) => panic!("{}: declined {}", func.name, reason.tag()),
    }
}

fn assert_rejected(func: &MachFunction, kind: SpillSlotViolationKind, what: &str) {
    let kinds = violation_kinds(func);
    assert!(
        kinds.contains(&kind),
        "{what}: expected {kind:?}, got {kinds:?}"
    );
    let error = encode_function(func).expect_err(what).to_string();
    assert!(
        error.contains("[TCG-A64-SPILL-SLOT]") && error.contains(kind.tag()),
        "{what}: encoder must fail closed with the named violation, got: {error}"
    );
}

fn assert_refused(func: &MachFunction, tag: &str, what: &str) {
    let error = encode_function(func).expect_err(what).to_string();
    assert!(error.contains(tag), "{what}: expected {tag}, got: {error}");
}

fn for_each_call_stream(check: impl Fn(OptLevel, MachFunction)) {
    let module = vec_call_module();
    for opt_level in OPT_LEVELS {
        check(opt_level, prepared(&module, opt_level, false));
    }
}

#[test]
fn corrupt_deleted_q_spill_store_is_rejected() {
    for_each_call_stream(|opt_level, mut func| {
        let reload = q_reload_after_call(&func);
        let store = q_store_for(&func, reload);
        let entry = func.entry.0 as usize;
        func.blocks[entry].insts.remove(store);
        assert_rejected(
            &func,
            SpillSlotViolationKind::ReloadWithoutReachingStore,
            &format!("{opt_level:?} deleted Q spill store"),
        );
    });
}

/// A Q reload shifted by half its 16-byte cell reads the halves of two
/// neighbouring cells (or leaves the spill area): never one spill store's
/// bytes, whatever the neighbours hold.
#[test]
fn corrupt_q_reload_shifted_by_half_a_slot_is_rejected() {
    const RELOAD_KINDS: [SpillSlotViolationKind; 4] = [
        SpillSlotViolationKind::ReloadMisalignedWithSpillStore,
        SpillSlotViolationKind::ReloadFromNonSpillStore,
        SpillSlotViolationKind::ReloadWithoutReachingStore,
        SpillSlotViolationKind::ReloadOfCallClobberedSlot,
    ];
    for_each_call_stream(|opt_level, clean| {
        for delta in [-8i64, 8] {
            let mut func = clean.clone();
            let reload = q_reload_after_call(&func);
            let inst = inst_at(&mut func, reload);
            let (base, offset) = mem_operand(inst).expect("resolved reload");
            inst.operands[1] = MachOperand::MemOp {
                base,
                offset: offset + delta,
            };
            let what = format!("{opt_level:?} Q reload offset {offset}{delta:+}");
            let kinds = violation_kinds(&func);
            let kind = RELOAD_KINDS
                .into_iter()
                .find(|kind| kinds.contains(kind))
                .unwrap_or_else(|| panic!("{what}: no reload violation in {kinds:?}"));
            assert_rejected(&func, kind, &what);
        }
    });
}

#[test]
fn corrupt_q_reload_onto_frame_record_or_below_the_frame_is_rejected() {
    for_each_call_stream(|opt_level, clean| {
        let reload = q_reload_after_call(&clean);
        let mut record = clean.clone();
        inst_at(&mut record, reload).operands[1] = MachOperand::MemOp {
            base: X29,
            offset: 0,
        };
        assert_rejected(
            &record,
            SpillSlotViolationKind::ReloadFromNonSpillStore,
            &format!("{opt_level:?} Q reload on the saved frame record"),
        );
        let mut below = clean;
        inst_at(&mut below, reload).operands[1] = MachOperand::MemOp {
            base: trust_cg_ir::aarch64_regs::SP,
            offset: -16,
        };
        assert_rejected(
            &below,
            SpillSlotViolationKind::ReloadWithoutReachingStore,
            &format!("{opt_level:?} Q reload below the frame"),
        );
    });
}

#[test]
fn corrupt_q_reload_into_wrong_register_is_rejected() {
    for_each_call_stream(|opt_level, mut func| {
        let reload = q_reload_after_call(&func);
        let inst = inst_at(&mut func, reload);
        let original = data_reg(inst).expect("Q reload destination");
        let replacement = if original == V16 { V17 } else { V16 };
        inst.operands[0] = MachOperand::PReg(replacement);
        assert_rejected(
            &func,
            SpillSlotViolationKind::ClobberedRegisterRead,
            &format!("{opt_level:?} Q reload into {replacement:?} instead of {original:?}"),
        );
    });
}

/// The allocator excludes V8-V15 from the Fpr128 pool because only their
/// low halves survive a call. Keeping one spilled value in V8 across the call
/// instead (a Q copy into V8 in place of the spill store, a Q copy out of it
/// in place of the reload) is rejected as a clobbered upper-half read.
#[test]
fn corrupt_q_value_kept_in_v8_across_the_call_is_rejected() {
    for_each_call_stream(|opt_level, mut func| {
        let reload = q_reload_after_call(&func);
        let store = q_store_for(&func, reload);
        let source = data_reg(inst_at(&mut func, store)).unwrap();
        let destination = data_reg(inst_at(&mut func, reload)).unwrap();
        let copy = |dst: PReg, src: PReg| {
            MachInst::new(
                AArch64Opcode::NeonOrrV,
                vec![
                    MachOperand::PReg(dst),
                    MachOperand::PReg(src),
                    MachOperand::PReg(src),
                ],
            )
        };
        *inst_at(&mut func, store) = copy(V8, source);
        *inst_at(&mut func, reload) = copy(destination, V8);
        assert_rejected(
            &func,
            SpillSlotViolationKind::UpperHalfClobberedRead,
            &format!("{opt_level:?} Q value kept in V8 across the call"),
        );
    });
}

/// Spill materialization never pairs two spill stores into one `STP`: a
/// flagged pair in the final stream is refused by name.
#[test]
fn corrupt_fused_q_pair_spill_is_refused_by_name() {
    for_each_call_stream(|opt_level, mut func| {
        let reload = q_reload_after_call(&func);
        let store = q_store_for(&func, reload);
        let inst = inst_at(&mut func, store);
        let data = data_reg(inst).unwrap();
        let (base, offset) = mem_operand(inst).unwrap();
        let mut pair = MachInst::new(
            AArch64Opcode::StpRI,
            vec![
                MachOperand::PReg(data),
                MachOperand::PReg(if data == V17 { V16 } else { V17 }),
                MachOperand::PReg(base),
                MachOperand::Imm(offset),
            ],
        );
        pair.flags.insert(InstFlags::SPILL_SLOT_ACCESS);
        *inst = pair;
        assert_refused(
            &func,
            "[TCG-A64-PAIR-SPILL]",
            &format!("{opt_level:?} fused Q pair spill"),
        );
    });
}

// ---------------------------------------------------------------------------
// Corruption controls on the exclusive windows (LL/SC fixture)
// ---------------------------------------------------------------------------

#[test]
fn corrupt_spill_reload_or_load_moved_into_an_exclusive_window_is_refused() {
    let module = llsc_module();
    for opt_level in OPT_LEVELS {
        let clean = prepared(&module, opt_level, true);
        let insts = layout(&clean);
        let head = insts
            .iter()
            .position(|id| is_exclusive_load(clean.insts[id.0 as usize].opcode))
            .expect("an exclusive window");
        let before = window_traffic(&clean, &insts, head).before;
        let reload = *before
            .iter()
            .find(|&&pos| clean.insts[insts[pos].0 as usize].opcode == AArch64Opcode::LdrRI)
            .expect("a spill reload before the window");
        let block = clean
            .blocks
            .iter()
            .position(|block| block.insts.contains(&insts[head]))
            .unwrap();
        let local = |func: &MachFunction, id: InstId| {
            func.blocks[block]
                .insts
                .iter()
                .position(|&other| other == id)
                .unwrap()
        };
        // The reload moved just after the load-exclusive.
        let mut moved = clean.clone();
        let reload_id = insts[reload];
        let from = local(&moved, reload_id);
        moved.blocks[block].insts.remove(from);
        let into = local(&moved, insts[head]) + 1;
        moved.blocks[block].insts.insert(into, reload_id);
        assert_refused(
            &moved,
            "[TCG-LLSC-SPILL-WINDOW]",
            &format!("{opt_level:?} spill reload inside the window"),
        );
        // A plain (unflagged) load placed inside the window.
        let mut plain = clean.clone();
        let mut load = clean.insts[reload_id.0 as usize].clone();
        load.flags = AArch64Opcode::LdrRI.default_flags();
        let load_id = plain.push_inst(load);
        let into = local(&plain, insts[head]) + 1;
        plain.blocks[block].insts.insert(into, load_id);
        assert_refused(
            &plain,
            "[TCG-LLSC-WINDOW]",
            &format!("{opt_level:?} plain load inside the window"),
        );
        // The same reload after the store-exclusive is outside every window.
        let mut outside = clean.clone();
        let from = local(&outside, reload_id);
        outside.blocks[block].insts.remove(from);
        let store = outside.blocks[block]
            .insts
            .iter()
            .position(|id| is_exclusive_store(outside.insts[id.0 as usize].opcode))
            .unwrap();
        outside.blocks[block].insts.insert(store + 1, reload_id);
        assert!(
            !encode_function(&outside)
                .err()
                .is_some_and(|error| error.to_string().contains("TCG-LLSC-")),
            "{opt_level:?}: a reload after the store-exclusive is not a window violation"
        );
    }
}

// ---------------------------------------------------------------------------
// The net's documented gap, caught by native execution
// ---------------------------------------------------------------------------

/// A Q reload moved by one whole slot onto another Q cell that a Q spill
/// store wrote earlier on the (straight-line) path reads a well-formed spill
/// value: the frame net has no slot identity and accepts it (LIMITATIONS.md).
/// The leaf `vec_pressure` stream then encodes, and native execution against
/// the C model is what catches the wrong value.
#[test]
fn known_gap_whole_q_slot_shift_is_missed_by_the_net_but_caught_natively() {
    let module = vec_pressure_module();
    let mut exercised = 0;
    for opt_level in OPT_LEVELS {
        let clean = prepared(&module, opt_level, false);
        assert_eq!(clean.blocks.len(), 1, "leaf fixture stays one block");
        let insts = entry_insts(&clean);
        // (position, base, offset) of each flagged Q spill store/reload.
        let access = |pos: usize, want_load: bool| {
            let inst = &clean.insts[insts[pos].0 as usize];
            (inst.flags.is_spill_slot_access()
                && data_reg(inst).is_some_and(is_q)
                && (inst.opcode == AArch64Opcode::LdrRI) == want_load)
                .then(|| mem_operand(inst))
                .flatten()
        };
        let shifted = (0..insts.len()).find_map(|pos| {
            let (base, offset) = access(pos, true)?;
            [16i64, -16].into_iter().find_map(|delta| {
                let target = (base, offset + delta);
                (0..pos)
                    .any(|earlier| access(earlier, false) == Some(target))
                    .then_some((pos, target))
            })
        });
        let Some((pos, (base, offset))) = shifted else {
            continue;
        };
        let mut func = clean.clone();
        inst_at(&mut func, pos).operands[1] = MachOperand::MemOp { base, offset };
        let kinds = violation_kinds(&func);
        assert!(
            kinds.is_empty(),
            "{opt_level:?}: the net would now catch a whole-slot shift ({kinds:?}); \
             retire this gap and its LIMITATIONS.md sentence"
        );
        let code = encode_function(&func)
            .unwrap_or_else(|error| panic!("{opt_level:?}: shifted stream must encode: {error}"));
        exercised += 1;
        if native_host::NATIVE {
            let object = native_host::naked_function_object("vec_pressure", &code);
            let (success, stdout) = link_and_run_status(
                &format!("vec_pressure-shifted-{opt_level:?}"),
                &[object],
                &vector_driver("vec_pressure", VEC_PRESSURE, false),
            );
            assert!(
                !success && stdout.starts_with("round 0:"),
                "{opt_level:?}: the C model must catch the shifted reload: {stdout}"
            );
        }
    }
    assert!(
        exercised > 0,
        "no level has a Q reload with a written neighbour cell"
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its lowerings state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
