// trust-cg-opt/tests/mach_id_admission.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! L10-P5 corruption controls for the optimizer's identity admission.
//!
//! Every pass of the O1, O2 and O3 ladders, run by the real pass manager:
//!
//! * with a stale counter (or a dangling block, instruction, stack-slot or
//!   jump-table reference) injected before it, is refused by name at its
//!   entry and the function is left untouched. The refusal comes from the
//!   pass manager's entry admission, which is the same scan whatever the
//!   pass; repeating it per pass shows each ladder pass is behind it, not
//!   that each pass was exercised;
//! * when it allocates, with the counter made stale by the pass before it
//!   (far below the live IDs, or a near miss one below the highest), is
//!   refused at its first allocation, and the refusal names the very ID the
//!   allocator would have issued again. A pass that declines on the stale
//!   counter and issues nothing is refused at the pass-manager exit instead,
//!   which the controls accept only when no counter or arena grew.
//!
//! SROA, which numbers its shadow registers while it analyses the function,
//! is refused before it writes one (a stale counter used to be raised by its
//! own bump and the alias then went unrefused), and promotes a memcpy fill
//! under the pass manager and every optimizer level.
//!
//! These are testing controls over hand-built fixtures, not a proof that every
//! pass allocates only through the counters.

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachIdAdmissionError, MachIdDomain, MachInst,
    MachOperand, RegClass, Signature, StackSlot, StackSlotId, VReg,
};
use trust_cg_opt::{MachinePass, OptLevel, OptimizationPipeline, PassManager};

fn vreg32(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}

fn vreg64(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}

fn emit(func: &mut MachFunction, block: BlockId, opcode: AArch64Opcode, ops: Vec<MachOperand>) {
    let id = func.push_inst(MachInst::new(opcode, ops));
    func.append_inst(block, id);
}

/// `bb0 -> bb1; bb1: v2 = v0 + v1 (+ more); cmp; b.cond bb2/bb3; bb3 -> bb1;
/// bb2: ret`, the trip-count-100 shape the scalar unroller recognizes, built
/// by the allocators so every counter is synchronized. It has no induction,
/// so the vectorizer no longer rewrites it: since 95660b90e its plain path
/// publishes only through the iteration-coverage clause, which a loop that is
/// not counted cannot pass ([`induction_store_loop`] is the vectorizer's).
fn counted_loop(extra_ops: bool) -> MachFunction {
    let mut func = MachFunction::new("loop".into(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let bb1 = func.create_block();
    let bb2 = func.create_block();
    let bb3 = func.create_block();
    let regs: Vec<u32> = (0..6).map(|_| func.alloc_vreg()).collect();
    emit(
        &mut func,
        bb0,
        AArch64Opcode::MovI,
        vec![vreg32(regs[0]), MachOperand::Imm(1)],
    );
    emit(
        &mut func,
        bb0,
        AArch64Opcode::MovI,
        vec![vreg32(regs[1]), MachOperand::Imm(2)],
    );
    emit(
        &mut func,
        bb0,
        AArch64Opcode::MovI,
        vec![vreg32(regs[3]), MachOperand::Imm(0)],
    );
    emit(
        &mut func,
        bb0,
        AArch64Opcode::B,
        vec![MachOperand::Block(bb1)],
    );
    emit(
        &mut func,
        bb1,
        AArch64Opcode::AddRR,
        vec![vreg32(regs[2]), vreg32(regs[0]), vreg32(regs[1])],
    );
    if extra_ops {
        emit(
            &mut func,
            bb1,
            AArch64Opcode::SubRR,
            vec![vreg32(regs[4]), vreg32(regs[2]), vreg32(regs[1])],
        );
        emit(
            &mut func,
            bb1,
            AArch64Opcode::MulRR,
            vec![vreg32(regs[5]), vreg32(regs[4]), vreg32(regs[0])],
        );
    }
    emit(
        &mut func,
        bb1,
        AArch64Opcode::CmpRI,
        vec![vreg32(regs[3]), MachOperand::Imm(100)],
    );
    emit(
        &mut func,
        bb1,
        AArch64Opcode::BCond,
        vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
    );
    emit(
        &mut func,
        bb3,
        AArch64Opcode::B,
        vec![MachOperand::Block(bb1)],
    );
    emit(&mut func, bb2, AArch64Opcode::Ret, vec![]);
    func.add_edge(bb0, bb1);
    func.add_edge(bb1, bb2);
    func.add_edge(bb1, bb3);
    func.add_edge(bb3, bb1);
    func
}

/// Straight-line constants, a redundant pair, a stack slot and a call: the
/// shape the scalar folding, CSE and frame-touching passes act on.
fn straight_line() -> MachFunction {
    let mut func = MachFunction::new("line".into(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let slot = func.alloc_stack_slot(StackSlot::new(8, 8));
    let r: Vec<u32> = (0..8).map(|_| func.alloc_vreg()).collect();
    emit(
        &mut func,
        bb0,
        AArch64Opcode::MovI,
        vec![vreg64(r[0]), MachOperand::Imm(6)],
    );
    emit(
        &mut func,
        bb0,
        AArch64Opcode::MovI,
        vec![vreg64(r[1]), MachOperand::Imm(7)],
    );
    emit(
        &mut func,
        bb0,
        AArch64Opcode::AddRR,
        vec![vreg64(r[2]), vreg64(r[0]), vreg64(r[1])],
    );
    emit(
        &mut func,
        bb0,
        AArch64Opcode::AddRR,
        vec![vreg64(r[3]), vreg64(r[0]), vreg64(r[1])],
    );
    emit(
        &mut func,
        bb0,
        AArch64Opcode::MulRR,
        vec![vreg64(r[4]), vreg64(r[2]), vreg64(r[3])],
    );
    emit(
        &mut func,
        bb0,
        AArch64Opcode::AddRI,
        vec![vreg64(r[5]), vreg64(r[4]), MachOperand::Imm(0)],
    );
    emit(
        &mut func,
        bb0,
        AArch64Opcode::StrRI,
        vec![
            vreg64(r[5]),
            MachOperand::StackSlot(slot),
            MachOperand::Imm(0),
        ],
    );
    emit(
        &mut func,
        bb0,
        AArch64Opcode::LdrRI,
        vec![
            vreg64(r[6]),
            MachOperand::StackSlot(slot),
            MachOperand::Imm(0),
        ],
    );
    emit(
        &mut func,
        bb0,
        AArch64Opcode::LslRI,
        vec![vreg64(r[7]), vreg64(r[6]), MachOperand::Imm(3)],
    );
    emit(&mut func, bb0, AArch64Opcode::Ret, vec![]);
    func
}

/// A loop whose body recomputes an invariant product by a constant and
/// accumulates into a counter: the hoisting, strength-reduction and unrolling
/// passes create blocks and registers on it.
fn invariant_loop() -> MachFunction {
    let mut func = MachFunction::new("inv".into(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let body = func.create_block();
    let exit = func.create_block();
    let r: Vec<u32> = (0..9).map(|_| func.alloc_vreg()).collect();
    let (a, b, i, n, ten, prod, sum, next, acc) =
        (r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8]);
    emit(
        &mut func,
        bb0,
        AArch64Opcode::MovI,
        vec![vreg64(a), MachOperand::Imm(3)],
    );
    emit(
        &mut func,
        bb0,
        AArch64Opcode::MovI,
        vec![vreg64(b), MachOperand::Imm(5)],
    );
    emit(
        &mut func,
        bb0,
        AArch64Opcode::MovI,
        vec![vreg64(i), MachOperand::Imm(0)],
    );
    emit(
        &mut func,
        bb0,
        AArch64Opcode::MovI,
        vec![vreg64(acc), MachOperand::Imm(0)],
    );
    emit(
        &mut func,
        bb0,
        AArch64Opcode::MovI,
        vec![vreg64(n), MachOperand::Imm(64)],
    );
    emit(
        &mut func,
        bb0,
        AArch64Opcode::B,
        vec![MachOperand::Block(header)],
    );
    emit(
        &mut func,
        header,
        AArch64Opcode::CmpRR,
        vec![vreg64(i), vreg64(n)],
    );
    emit(
        &mut func,
        header,
        AArch64Opcode::BCond,
        vec![MachOperand::Block(exit), MachOperand::Block(body)],
    );
    emit(
        &mut func,
        body,
        AArch64Opcode::MovI,
        vec![vreg64(ten), MachOperand::Imm(10)],
    );
    emit(
        &mut func,
        body,
        AArch64Opcode::MulRR,
        vec![vreg64(prod), vreg64(a), vreg64(ten)],
    );
    emit(
        &mut func,
        body,
        AArch64Opcode::AddRR,
        vec![vreg64(sum), vreg64(prod), vreg64(b)],
    );
    emit(
        &mut func,
        body,
        AArch64Opcode::AddRR,
        vec![vreg64(acc), vreg64(acc), vreg64(sum)],
    );
    emit(
        &mut func,
        body,
        AArch64Opcode::AddRI,
        vec![vreg64(next), vreg64(i), MachOperand::Imm(1)],
    );
    emit(
        &mut func,
        body,
        AArch64Opcode::MovR,
        vec![vreg64(i), vreg64(next)],
    );
    emit(
        &mut func,
        body,
        AArch64Opcode::B,
        vec![MachOperand::Block(header)],
    );
    emit(
        &mut func,
        exit,
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(trust_cg_ir::regs::X0), vreg64(acc)],
    );
    emit(&mut func, exit, AArch64Opcode::Ret, vec![]);
    func.add_edge(bb0, header);
    func.add_edge(header, exit);
    func.add_edge(header, body);
    func.add_edge(body, header);
    func
}

/// `if a < b { x = a + 1 } else { x = b - 1 }; return x * 12`: the diamond
/// if-conversion folds and the constant multiply strength reduction expands.
fn diamond() -> MachFunction {
    let mut func = MachFunction::new("diamond".into(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let then_block = func.create_block();
    let else_block = func.create_block();
    let join = func.create_block();
    let r: Vec<u32> = (0..6).map(|_| func.alloc_vreg()).collect();
    let (a, b, x, twelve, y, z) = (r[0], r[1], r[2], r[3], r[4], r[5]);
    emit(
        &mut func,
        bb0,
        AArch64Opcode::MovR,
        vec![vreg64(a), MachOperand::PReg(trust_cg_ir::regs::X0)],
    );
    emit(
        &mut func,
        bb0,
        AArch64Opcode::MovR,
        vec![vreg64(b), MachOperand::PReg(trust_cg_ir::regs::X1)],
    );
    emit(
        &mut func,
        bb0,
        AArch64Opcode::CmpRR,
        vec![vreg64(a), vreg64(b)],
    );
    emit(
        &mut func,
        bb0,
        AArch64Opcode::BCond,
        vec![
            MachOperand::Block(then_block),
            MachOperand::Block(else_block),
        ],
    );
    emit(
        &mut func,
        then_block,
        AArch64Opcode::AddRI,
        vec![vreg64(x), vreg64(a), MachOperand::Imm(1)],
    );
    emit(
        &mut func,
        then_block,
        AArch64Opcode::B,
        vec![MachOperand::Block(join)],
    );
    emit(
        &mut func,
        else_block,
        AArch64Opcode::SubRI,
        vec![vreg64(x), vreg64(b), MachOperand::Imm(1)],
    );
    emit(
        &mut func,
        else_block,
        AArch64Opcode::B,
        vec![MachOperand::Block(join)],
    );
    emit(
        &mut func,
        join,
        AArch64Opcode::MovI,
        vec![vreg64(twelve), MachOperand::Imm(12)],
    );
    emit(
        &mut func,
        join,
        AArch64Opcode::MulRR,
        vec![vreg64(y), vreg64(x), vreg64(twelve)],
    );
    emit(
        &mut func,
        join,
        AArch64Opcode::AddRI,
        vec![vreg64(z), vreg64(y), MachOperand::Imm(0)],
    );
    emit(
        &mut func,
        join,
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(trust_cg_ir::regs::X0), vreg64(z)],
    );
    emit(&mut func, join, AArch64Opcode::Ret, vec![]);
    func.add_edge(bb0, then_block);
    func.add_edge(bb0, else_block);
    func.add_edge(then_block, join);
    func.add_edge(else_block, join);
    func
}

/// `for (i = 0; i < n; i++) a[i] = i + 1` over `i32`, as the importer spells
/// it at -O0 (trust-cg-opt's `make_imported_o0_i32_induction_store_loop`):
/// a counted induction loop the vectorizer rewrites through the
/// iteration-coverage clause. `n` (v1) and `a` (v6) are live in.
fn induction_store_loop() -> MachFunction {
    let mut func = MachFunction::new("store_loop".into(), Signature::new(vec![], vec![]));
    let preheader = func.entry;
    let header = func.create_block();
    let body = func.create_block();
    let exit = func.create_block();
    let latch = func.create_block();
    let r: Vec<u32> = (0..10).map(|_| func.alloc_vreg()).collect();
    let (index, bound, one, value) = (r[0], r[1], r[2], r[3]);
    let (wide_index, stride, base, address, next, flag) = (r[4], r[5], r[6], r[7], r[8], r[9]);
    emit(
        &mut func,
        preheader,
        AArch64Opcode::Movz,
        vec![vreg32(index), MachOperand::Imm(0)],
    );
    emit(
        &mut func,
        preheader,
        AArch64Opcode::Movz,
        vec![vreg64(stride), MachOperand::Imm(4)],
    );
    emit(
        &mut func,
        preheader,
        AArch64Opcode::B,
        vec![MachOperand::Block(header)],
    );
    emit(
        &mut func,
        header,
        AArch64Opcode::CmpRR,
        vec![vreg32(index), vreg32(bound)],
    );
    emit(
        &mut func,
        header,
        AArch64Opcode::CSet,
        vec![vreg64(flag), MachOperand::Imm(11)],
    );
    emit(
        &mut func,
        header,
        AArch64Opcode::CmpRI,
        vec![vreg64(flag), MachOperand::Imm(0)],
    );
    emit(
        &mut func,
        header,
        AArch64Opcode::BCond,
        vec![MachOperand::Imm(1), MachOperand::Block(body)],
    );
    emit(
        &mut func,
        header,
        AArch64Opcode::B,
        vec![MachOperand::Block(exit)],
    );
    emit(
        &mut func,
        body,
        AArch64Opcode::Movz,
        vec![vreg32(one), MachOperand::Imm(1)],
    );
    emit(
        &mut func,
        body,
        AArch64Opcode::AddRR,
        vec![vreg32(value), vreg32(index), vreg32(one)],
    );
    emit(
        &mut func,
        body,
        AArch64Opcode::Sxtw,
        vec![vreg64(wide_index), vreg32(index)],
    );
    emit(
        &mut func,
        body,
        AArch64Opcode::Madd,
        vec![
            vreg64(address),
            vreg64(wide_index),
            vreg64(stride),
            vreg64(base),
        ],
    );
    emit(
        &mut func,
        body,
        AArch64Opcode::StrRI,
        vec![vreg32(value), vreg64(address), MachOperand::Imm(0)],
    );
    emit(
        &mut func,
        body,
        AArch64Opcode::B,
        vec![MachOperand::Block(latch)],
    );
    emit(
        &mut func,
        latch,
        AArch64Opcode::AddRR,
        vec![vreg32(next), vreg32(index), vreg32(one)],
    );
    emit(
        &mut func,
        latch,
        AArch64Opcode::MovR,
        vec![vreg32(index), vreg32(next)],
    );
    emit(
        &mut func,
        latch,
        AArch64Opcode::B,
        vec![MachOperand::Block(header)],
    );
    emit(&mut func, exit, AArch64Opcode::Ret, vec![]);
    func.add_edge(preheader, header);
    func.add_edge(header, body);
    func.add_edge(header, exit);
    func.add_edge(body, latch);
    func.add_edge(latch, header);
    func
}

fn fixtures() -> Vec<MachFunction> {
    vec![
        counted_loop(false),
        counted_loop(true),
        induction_store_loop(),
        straight_line(),
        invariant_loop(),
        diamond(),
    ]
}

const LEVELS: [OptLevel; 3] = [OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// Every pass of `level`'s ladder, in pipeline order.
fn ladder(level: OptLevel) -> Vec<Box<dyn MachinePass>> {
    OptimizationPipeline::new(level)
        .build_pass_manager()
        .into_passes()
}

/// One corruption of a well-formed function, naming the domain it breaks.
struct Corruption {
    label: &'static str,
    domain: MachIdDomain,
    apply: fn(&mut MachFunction),
}

fn corruptions() -> [Corruption; 6] {
    [
        Corruption {
            label: "stale vreg counter",
            domain: MachIdDomain::VReg,
            apply: |f| f.next_vreg = 1,
        },
        Corruption {
            label: "branch to a block past the arena",
            domain: MachIdDomain::Block,
            apply: |f| {
                let dangling = BlockId(f.blocks.len() as u32);
                f.blocks[0].succs.push(dangling);
            },
        },
        Corruption {
            label: "block naming an instruction past the arena",
            domain: MachIdDomain::Inst,
            apply: |f| {
                let dangling = InstId(f.insts.len() as u32);
                f.blocks[0].insts.insert(0, dangling);
            },
        },
        Corruption {
            label: "sidecar keyed by an instruction past the arena",
            domain: MachIdDomain::Inst,
            apply: |f| {
                let dangling = InstId(f.insts.len() as u32);
                f.lowering_provenance
                    .insert(dangling, trust_cg_ir::LoweringProvenance::UNATTRIBUTED);
            },
        },
        Corruption {
            label: "stack slot past the arena",
            domain: MachIdDomain::StackSlot,
            apply: |f| f.stack_protector_slot = Some(StackSlotId(f.stack_slots.len() as u32)),
        },
        Corruption {
            label: "jump table past the list",
            domain: MachIdDomain::JumpTable,
            apply: |f| {
                let detached = MachInst::new(
                    AArch64Opcode::Adr,
                    vec![vreg64(0), MachOperand::JumpTableIndex(0)],
                );
                f.insts.push(detached);
            },
        },
    ]
}

#[test]
fn every_ladder_pass_refuses_a_corrupted_function_at_its_entry() {
    let mut checked = 0usize;
    for level in LEVELS {
        for pass in ladder(level) {
            let name = pass.name().to_string();
            let mut manager = PassManager::new().with_pass(pass);
            for corruption in corruptions() {
                for fixture in fixtures() {
                    let mut func = fixture;
                    (corruption.apply)(&mut func);
                    let before = format!("{func:?}");
                    let stats = manager.run_once_with_stats(&mut func);
                    let refusal = stats.id_admission.expect_err(&format!(
                        "{level:?} `{name}` must refuse a {}",
                        corruption.label
                    ));
                    assert_eq!(refusal.boundary, format!("entry of pass `{name}`"));
                    assert_eq!(refusal.error.domain(), corruption.domain, "{name}");
                    assert_eq!(refusal.error.code(), "TCG-MIR-STALE-ID-COUNTER");
                    assert!(refusal.to_string().contains("refused at entry of pass `"));
                    assert_eq!(stats.changes, 0, "{name} ran on a refused function");
                    assert_eq!(format!("{func:?}"), before, "{name} touched it");
                    checked += 1;
                }
            }
        }
    }
    assert!(checked > 1_000, "only {checked} controls ran");
}

/// A test pass that lowers the register counter below a live ID without
/// allocating: the stale state a pass that wrote IDs by hand would leave.
struct StaleCounter {
    to: u32,
}

/// The far stale counter: below nearly every live register.
const FAR: StaleCounter = StaleCounter { to: 1 };

impl MachinePass for StaleCounter {
    fn name(&self) -> &str {
        "stale-counter"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        func.next_vreg = self.to;
        true
    }
}

/// The highest register ID `func` names (operands, detached instructions
/// included, and noalias parameters).
fn highest_vreg(func: &MachFunction) -> Option<u32> {
    func.insts
        .iter()
        .flat_map(|inst| inst.operands.iter().filter_map(MachOperand::as_vreg))
        .map(|reg| reg.id)
        .chain(func.noalias_params.iter().copied())
        .max()
}

/// The near-miss stale counter: exactly the highest live register, so the
/// next allocation would issue that live ID again.
fn near_miss(func: &MachFunction) -> StaleCounter {
    StaleCounter {
        to: highest_vreg(func).expect("fixture names a register"),
    }
}

/// The counter and arena extents: any growth means an ID was issued.
fn extents(func: &MachFunction) -> (u32, usize, usize, usize) {
    (
        func.next_vreg,
        func.insts.len(),
        func.blocks.len(),
        func.stack_slots.len(),
    )
}

/// Whether `pass` allocates any ID on `func`: arena or counter growth.
fn allocates(pass: &mut dyn MachinePass, func: &MachFunction) -> bool {
    let mut copy = func.clone();
    let before = extents(&copy);
    pass.run(&mut copy);
    before != extents(&copy)
}

/// Run `stale` and then `pass` under one pass manager on `fixture` and check
/// the refusal: at the pass's first allocation, naming the stale counter and
/// a live ID at or above it; or, only when the pass issued nothing (it
/// declined on the stale counter), at the pass-manager exit. Returns whether
/// the refusal came at the allocation.
fn refused_after_stale(
    level: OptLevel,
    fixture: &MachFunction,
    stale: StaleCounter,
    pass: Box<dyn MachinePass>,
) -> bool {
    let name = pass.name().to_string();
    let counter = stale.to;
    let mut input = fixture.clone();
    input.next_vreg = counter;
    let mut manager = PassManager::new()
        .with_pass(Box::new(stale))
        .with_pass(pass);
    let mut func = fixture.clone();
    let stats = manager.run_once_with_stats(&mut func);
    let refusal = stats.id_admission.expect_err(&format!(
        "{level:?} `{name}` ran on stale counter {counter} unrefused"
    ));
    assert!(
        matches!(
            refusal.error,
            MachIdAdmissionError::StaleCounter {
                domain: MachIdDomain::VReg,
                counter: refused,
                live_id,
                ..
            } if refused == u64::from(counter) && live_id >= counter
        ),
        "{level:?} `{name}`: {refusal}"
    );
    if refusal.boundary == format!("the first allocation in pass `{name}` (iteration 1)") {
        return true;
    }
    assert_eq!(
        refusal.boundary,
        format!("pass-manager exit (after pass `{name}`)"),
        "{level:?} `{name}`"
    );
    assert_eq!(
        extents(&func),
        extents(&input),
        "{level:?} `{name}` issued an ID from stale counter {counter} without an admission"
    );
    false
}

#[test]
fn an_allocating_pass_refuses_a_counter_left_stale_before_it() {
    let mut at_allocation = std::collections::BTreeSet::new();
    let mut controls = 0usize;
    for level in LEVELS {
        for (index, mut probe) in ladder(level).into_iter().enumerate() {
            for fixture in fixtures() {
                if !allocates(probe.as_mut(), &fixture) {
                    continue;
                }
                // A fresh instance of the same pass (passes may keep state)
                // for each stale counter: far below, and a near miss.
                for stale in [FAR, near_miss(&fixture)] {
                    let pass = ladder(level).swap_remove(index);
                    let name = pass.name().to_string();
                    if refused_after_stale(level, &fixture, stale, pass) {
                        at_allocation.insert(name);
                    }
                    controls += 1;
                }
            }
        }
    }
    assert!(controls >= 16, "only {controls} controls ran");
    // On these hand-built fixtures the vectorizer and the scalar unroller
    // allocate; the selection-built property test in trust-cg-codegen
    // (`tests/mach_id_admission_property.rs`) reaches the other allocating
    // passes on instruction-selection output.
    for expected in ["vectorize", "scalar-unroll"] {
        assert!(
            at_allocation.contains(expected),
            "`{expected}` was not refused at an allocation here: {at_allocation:?}"
        );
    }
}

/// `v0 = a; v1 = b; v2 = &slot; [v2] = v0; [v2 + 8] = v1; v7 = 7;
/// v3 = [v2]; v4 = [v2 + 8]; v5 = v3 + v4; v6 = v5 + v7; ret v6`: a
/// fully promotable 16-byte slot. SROA numbers two shadow registers from the
/// counter (8).
fn sroa_slot() -> MachFunction {
    use trust_cg_ir::regs::{SP, X0, X1};
    let mut func = MachFunction::new("sroa_slot".into(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    let slot = func.alloc_stack_slot(StackSlot::new(16, 8));
    func.next_vreg = 8;
    let ops: Vec<(AArch64Opcode, Vec<MachOperand>)> = vec![
        (AArch64Opcode::Copy, vec![vreg64(0), MachOperand::PReg(X0)]),
        (AArch64Opcode::Copy, vec![vreg64(1), MachOperand::PReg(X1)]),
        (
            AArch64Opcode::AddPCRel,
            vec![
                vreg64(2),
                MachOperand::PReg(SP),
                MachOperand::StackSlot(slot),
            ],
        ),
        (
            AArch64Opcode::StrRI,
            vec![vreg64(0), vreg64(2), MachOperand::Imm(0)],
        ),
        (
            AArch64Opcode::StrRI,
            vec![vreg64(1), vreg64(2), MachOperand::Imm(8)],
        ),
        (AArch64Opcode::Movz, vec![vreg64(7), MachOperand::Imm(7)]),
        (
            AArch64Opcode::LdrRI,
            vec![vreg64(3), vreg64(2), MachOperand::Imm(0)],
        ),
        (
            AArch64Opcode::LdrRI,
            vec![vreg64(4), vreg64(2), MachOperand::Imm(8)],
        ),
        (AArch64Opcode::AddRR, vec![vreg64(5), vreg64(3), vreg64(4)]),
        (AArch64Opcode::AddRR, vec![vreg64(6), vreg64(5), vreg64(7)]),
        (AArch64Opcode::Copy, vec![MachOperand::PReg(X0), vreg64(6)]),
        (AArch64Opcode::Ret, vec![]),
    ];
    for (opcode, operands) in ops {
        emit(&mut func, entry, opcode, operands);
    }
    func
}

fn sroa() -> Box<dyn MachinePass> {
    Box::new(trust_cg_opt::ScalarReplacementOfAggregates)
}

/// The registers SROA's rewritten moves write (its shadow registers).
fn shadow_defs(func: &MachFunction) -> Vec<u32> {
    func.block(func.entry)
        .insts
        .iter()
        .map(|id| func.inst(*id))
        .filter(|inst| inst.opcode == AArch64Opcode::MovR)
        .filter_map(|inst| inst.operands[0].as_vreg().map(|reg| reg.id))
        .filter(|id| *id >= 8)
        .collect()
}

#[test]
fn sroa_refuses_a_counter_left_stale_before_it_instead_of_aliasing() {
    // Clean: SROA promotes the slot through fresh shadows v8 and v9.
    let mut clean = sroa_slot();
    let stats = PassManager::new()
        .with_pass(sroa())
        .run_once_with_stats(&mut clean);
    assert_eq!(stats.id_admission, Ok(()));
    assert_eq!(stats.changes, 1);
    assert_eq!(shadow_defs(&clean), [8, 9]);
    assert_eq!(clean.next_vreg, 10);

    // A pass leaves the counter at the live v7 (a near miss) or far below.
    // SROA used to number its shadows from it (`MovR v7, v0` overwrote the
    // constant 7) and raise the counter past them itself, so every later
    // admission accepted the alias. Its range allocation now refuses before
    // it writes anything.
    for counter in [7, 6, 1] {
        let mut func = sroa_slot();
        let before = format!("{:?}", func.insts);
        let stats = PassManager::new()
            .with_pass(Box::new(StaleCounter { to: counter }))
            .with_pass(sroa())
            .run_once_with_stats(&mut func);
        let refusal = stats.id_admission.expect_err("stale counter refused");
        assert_eq!(
            refusal.boundary, "the first allocation in pass `sroa` (iteration 1)",
            "{refusal}"
        );
        assert!(
            matches!(
                refusal.error,
                MachIdAdmissionError::StaleCounter {
                    domain: MachIdDomain::VReg,
                    counter: refused,
                    live_id,
                    ..
                } if refused == u64::from(counter) && live_id >= counter
            ),
            "{refusal}"
        );
        assert_eq!(format!("{:?}", func.insts), before, "SROA wrote nothing");
        assert_eq!(func.next_vreg, counter, "nor repaired the counter");
    }
}

/// `v1 = src (x1); v10 = &slot; memcpy(v10, v1, 16, 0); v11 = v10 + 4;
/// v20 = [v10]; v21 = [v11]; ret`, the counter at 40: a whole-slot memcpy
/// fill SROA expands into two lane loads from `src`.
fn memcpy_fill() -> MachFunction {
    use trust_cg_ir::regs::{SP, X0, X1, X2, X3};
    let mut func = MachFunction::new("memcpy_fill".into(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    let slot = func.alloc_stack_slot(StackSlot::new(16, 4));
    func.next_vreg = 40;
    let ops: Vec<(AArch64Opcode, Vec<MachOperand>)> = vec![
        (AArch64Opcode::Copy, vec![vreg64(1), MachOperand::PReg(X1)]),
        (
            AArch64Opcode::AddPCRel,
            vec![
                vreg64(10),
                MachOperand::PReg(SP),
                MachOperand::StackSlot(slot),
            ],
        ),
        (AArch64Opcode::Movz, vec![vreg64(2), MachOperand::Imm(16)]),
        (AArch64Opcode::Movz, vec![vreg64(3), MachOperand::Imm(0)]),
        (AArch64Opcode::Copy, vec![MachOperand::PReg(X0), vreg64(10)]),
        (AArch64Opcode::Copy, vec![MachOperand::PReg(X1), vreg64(1)]),
        (AArch64Opcode::Copy, vec![MachOperand::PReg(X2), vreg64(2)]),
        (AArch64Opcode::Copy, vec![MachOperand::PReg(X3), vreg64(3)]),
        (
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("memcpy".to_string())],
        ),
        (
            AArch64Opcode::AddRI,
            vec![vreg64(11), vreg64(10), MachOperand::Imm(4)],
        ),
        (
            AArch64Opcode::LdrRI,
            vec![vreg32(20), vreg64(10), MachOperand::Imm(0)],
        ),
        (
            AArch64Opcode::LdrRI,
            vec![vreg32(21), vreg64(11), MachOperand::Imm(0)],
        ),
        (AArch64Opcode::Ret, vec![]),
    ];
    for (opcode, operands) in ops {
        emit(&mut func, entry, opcode, operands);
    }
    // The `bl memcpy` is the one instruction selection makes for a LIR
    // `Memcpy` (`LIBRARY_ROUTINE_CALL`), the only one SROA's fill reads.
    let call = func
        .block(entry)
        .insts
        .iter()
        .copied()
        .find(|id| func.inst(*id).opcode == AArch64Opcode::Bl)
        .expect("the fixture's memcpy call");
    func.inst_mut(call)
        .flags
        .insert(trust_cg_ir::InstFlags::LIBRARY_ROUTINE_CALL);
    func
}

fn calls_memcpy(func: &MachFunction) -> bool {
    func.block_order.iter().any(|block| {
        func.block(*block)
            .insts
            .iter()
            .any(|id| func.inst(*id).opcode == AArch64Opcode::Bl)
    })
}

#[test]
fn sroa_promotes_a_memcpy_fill_under_the_pass_manager_and_every_level() {
    // The lane loads are pushed after the shadows were allocated, so the
    // well-formed function is admitted (the shadow numbering used to be
    // unallocated when the first push re-derived, and was refused).
    let mut func = memcpy_fill();
    assert_eq!(func.admit_id_counters(), Ok(()));
    let stats = PassManager::new()
        .with_pass(sroa())
        .run_once_with_stats(&mut func);
    assert_eq!(stats.id_admission, Ok(()));
    assert_eq!(stats.changes, 1);
    assert!(!calls_memcpy(&func), "the memcpy call is expanded");
    assert_eq!(func.next_vreg, 42, "two lane shadows");

    for level in LEVELS {
        let mut func = memcpy_fill();
        let stats = OptimizationPipeline::new(level).run(&mut func);
        assert_eq!(stats.id_admission, Ok(()), "{level:?}");
        assert!(
            !calls_memcpy(&func),
            "{level:?}: the memcpy call is expanded"
        );
        assert_eq!(func.admit_id_counters(), Ok(()), "{level:?}");
    }
}

#[test]
fn a_refusal_stops_the_pass_manager_before_any_later_pass() {
    for level in LEVELS {
        let mut manager = PassManager::new()
            .with_pass(Box::new(FAR))
            .with_pass(Box::new(trust_cg_opt::passes::DeadCodeElimination));
        let mut func = counted_loop(true);
        let stats = if level == OptLevel::O3 {
            manager.run_to_fixpoint(&mut func, 4)
        } else {
            manager.run_once_with_stats(&mut func)
        };
        let refusal = stats.id_admission.expect_err("stale counter refused");
        assert!(refusal.error.code() == "TCG-MIR-STALE-ID-COUNTER");
        // DCE allocates nothing, so the pass-manager exit admission names it.
        assert_eq!(
            refusal.boundary, "pass-manager exit (after pass `dce`)",
            "{level:?}"
        );
    }
}

#[test]
fn the_optimization_pipeline_refuses_at_entry_and_after_post_convergence() {
    for level in LEVELS {
        let mut stale = counted_loop(true);
        stale.next_vreg = 0;
        let stats = OptimizationPipeline::new(level).run(&mut stale);
        let refusal = stats.id_admission.expect_err("stale input refused");
        assert!(refusal.boundary.starts_with("entry of pass `"), "{refusal}");

        let mut clean = counted_loop(true);
        let stats = OptimizationPipeline::new(level).run(&mut clean);
        assert_eq!(stats.id_admission, Ok(()), "{level:?}");
        assert_eq!(clean.admit_id_counters(), Ok(()));
    }
}
