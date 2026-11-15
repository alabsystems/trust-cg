// trust-cg-verify/post_ra_value_flow/model.rs - one AArch64 instruction, symbolically
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Symbolic execution of one AArch64 machine instruction for the post-RA
//! value-flow comparison.
//!
//! Every instruction is executed by exactly one rule:
//!
//! 1. **Move**: register copies (`Copy`, `MOV`, `FMOV` register forms, the
//!    `ORR Vd, Vn, Vn` vector move) copy the source term; constant moves
//!    (`MOVZ`/`MOVN`/`MOVI` and a `MOVK` of a constant) produce constants;
//!    64-bit add/subtract of an immediate or of a constant register is the
//!    linear term `base + k`. These are the only interpreted operations,
//!    exactly the ones post-allocation rewrites change the spelling of
//!    (copy lowering, rematerialization, post-index folding, frame-offset
//!    materialization).
//! 2. **Pure**: an instruction with no memory access, call, branch, trap or
//!    other effect computes an uninterpreted function of its register
//!    inputs, NZCV when it reads it, and its non-register operands.
//! 3. **Effect**: every other instruction (loads and stores of program
//!    memory, calls, atomics, barriers, trap carriers, returns) is an
//!    effect. Effects are compared one-for-one, in order, between the two
//!    functions; matched effects give their results the same terms.
//! 4. **Storage**: a load or store of allocator-owned frame storage (spill
//!    slots, callee-save slots) is not an effect: it moves a value through
//!    a tracked memory cell keyed by its exact address.
//!
//! The operand def/use partition is the allocator's own
//! ([`crate::post_ra_reaching_def::operand_roles`], itself built on
//! `trust_cg_opt::effects`); the memory-effect and NZCV tables are
//! `trust_cg_opt::effects`'s. Those shared tables are this check's
//! description of each opcode (a common-mode dependence, documented).

use std::collections::BTreeMap;

use trust_cg_ir::fast_hash::FxHashMap as HashMap;

use trust_cg_ir::{
    AArch64Opcode, InstFlags, InstId, MachFunction, MachInst, MachOperand, PReg, RegClass,
    SpecialReg,
};
use trust_cg_opt::effects::{definitely_writes_flags, may_clobber_nzcv, opcode_effect, reads_nzcv};

use super::ViolationKind;
use super::term::{Aux, OpId, OpKey, OpTag, Term, TermArena, TermId};

// ---------------------------------------------------------------------------
// Locations
// ---------------------------------------------------------------------------

/// Physical locations: X0-X30, SP, V0-V31, NZCV, FPCR, FPSR.
pub(crate) const NUM_PHYS: usize = 67;
pub(crate) const LOC_SP: u16 = 31;
pub(crate) const LOC_V0: u16 = 32;
pub(crate) const LOC_NZCV: u16 = 64;
pub(crate) const LOC_FPCR: u16 = 65;
pub(crate) const LOC_FPSR: u16 = 66;
/// X18, the Darwin platform register.
pub(crate) const LOC_X18: u16 = 18;

/// Width of NZCV terms.
pub(crate) const NZCV_BITS: u16 = 4;

/// Full width of a physical location.
pub(crate) fn loc_bits(loc: u16) -> u16 {
    match loc {
        0..=31 => 64,
        32..=63 => 128,
        LOC_NZCV => NZCV_BITS,
        _ => 64,
    }
}

/// Diagnostic name of a physical location.
pub(crate) fn loc_name(loc: u16) -> String {
    match loc {
        0..=30 => format!("x{loc}"),
        31 => "sp".to_string(),
        32..=63 => format!("v{}", loc - 32),
        LOC_NZCV => "nzcv".to_string(),
        LOC_FPCR => "fpcr".to_string(),
        LOC_FPSR => "fpsr".to_string(),
        _ => format!("loc{loc}"),
    }
}

/// A storage place: a physical location or (specification only) a virtual
/// register.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub(crate) enum Place {
    Phys(u16),
    Virt(u32),
}

/// A register operand: its place, the width it is read or written through
/// and its bank.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct View {
    pub(crate) place: Place,
    pub(crate) bits: u16,
    pub(crate) fpr: bool,
}

/// A register operand's meaning.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Reg {
    View(View),
    /// XZR/WZR: reads zero of this width, writes are discarded.
    Zero(u16),
}

fn class_bits(class: RegClass) -> Option<(u16, bool)> {
    Some(match class {
        RegClass::Gpr64 => (64, false),
        RegClass::Gpr32 => (32, false),
        RegClass::Fpr128 => (128, true),
        RegClass::Fpr64 => (64, true),
        RegClass::Fpr32 => (32, true),
        RegClass::Fpr16 => (16, true),
        RegClass::Fpr8 => (8, true),
        RegClass::System => return None,
    })
}

/// The meaning of a physical register (see `trust_cg_ir::aarch64_regs` for
/// the encoding layout).
pub(crate) fn preg_reg(p: PReg) -> Option<Reg> {
    let e = p.encoding();
    let view = |loc: u16, bits: u16, fpr: bool| {
        Some(Reg::View(View {
            place: Place::Phys(loc),
            bits,
            fpr,
        }))
    };
    match e {
        0..=30 => view(e, 64, false),
        31 => view(LOC_SP, 64, false),
        32..=62 => view(e - 32, 32, false),
        63 => view(LOC_SP, 32, false),
        64..=95 => view(LOC_V0 + (e - 64), 128, true),
        96..=127 => view(LOC_V0 + (e - 96), 64, true),
        128..=159 => view(LOC_V0 + (e - 128), 32, true),
        160 => Some(Reg::Zero(64)),
        161 => Some(Reg::Zero(32)),
        162 => view(LOC_NZCV, NZCV_BITS, false),
        163 => view(LOC_FPCR, 64, false),
        164 => view(LOC_FPSR, 64, false),
        165..=196 => view(LOC_V0 + (e - 165), 16, true),
        197..=228 => view(LOC_V0 + (e - 197), 8, true),
        _ => None,
    }
}

/// The register meaning of an operand: `None` when the operand is not a
/// register, `Some(Err)` for a register this model does not know.
pub(crate) fn operand_reg(op: &MachOperand) -> Option<Result<Reg, String>> {
    match op {
        MachOperand::VReg(v) => Some(
            class_bits(v.class)
                .map(|(bits, fpr)| {
                    Reg::View(View {
                        place: Place::Virt(v.id),
                        bits,
                        fpr,
                    })
                })
                .ok_or_else(|| format!("system-class virtual register v{}", v.id)),
        ),
        MachOperand::PReg(p) => {
            Some(preg_reg(*p).ok_or_else(|| format!("unmodeled physical register {p:?}")))
        }
        MachOperand::Special(SpecialReg::SP) => Some(Ok(Reg::View(View {
            place: Place::Phys(LOC_SP),
            bits: 64,
            fpr: false,
        }))),
        MachOperand::Special(SpecialReg::XZR) => Some(Ok(Reg::Zero(64))),
        MachOperand::Special(SpecialReg::WZR) => Some(Ok(Reg::Zero(32))),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// State
// ---------------------------------------------------------------------------

/// One frame-storage cell: the value a store left at an exact address.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct Cell {
    pub(crate) value: TermId,
    pub(crate) bytes: u16,
}

/// Symbolic machine state of one function at one program point.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct State {
    pub(crate) phys: Vec<TermId>,
    /// The width of the view each physical location was last written
    /// through in this block (its full width at block entry): a call
    /// argument written through `W2` is a 32-bit argument.
    pub(crate) written: Vec<u16>,
    pub(crate) virt: HashMap<u32, TermId>,
    /// Cells keyed by `(base term, byte offset)`.
    pub(crate) cells: BTreeMap<(TermId, i64), Cell>,
    /// After frame lowering (implementation only): no write on any path
    /// from the entry has touched the stack below `CFA + touched_low`. A
    /// write at a known CFA offset lowers it to that offset; a write the
    /// model cannot place (through an unknown pointer, a call, any other
    /// opaque effect) lowers it to the red zone below the SP it runs at.
    /// A stack probe is exempt from frame-storage privacy only where it
    /// writes wholly below it: memory nothing has written yet.
    pub(crate) touched_low: i64,
}

impl State {
    pub(crate) fn new(phys: Vec<TermId>) -> Self {
        let written = (0..phys.len() as u16).map(loc_bits).collect();
        Self {
            phys,
            written,
            virt: HashMap::default(),
            cells: BTreeMap::new(),
            touched_low: 0,
        }
    }
}

/// Bytes below SP a function may use without moving SP (the Darwin AArch64
/// red zone; other AArch64 targets have none, so this is the larger bound).
/// An opaque write's possible targets reach this far below the SP it runs at.
pub(crate) const RED_ZONE_BYTES: i64 = 128;

/// Which function of the comparison a state belongs to.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Side {
    Spec = 0,
    Impl = 1,
}

/// How a function's frame-index operands become addresses.
#[derive(Clone, Debug)]
pub(crate) enum AddressModel {
    /// Before frame lowering: stack slots and incoming arguments are symbols.
    Symbolic,
    /// Stack slots at the given CFA-relative offsets; incoming argument `n`
    /// at `CFA + n`.
    Frame { slot_cfa: Vec<Option<i64>> },
}

/// Per-function execution context.
pub(crate) struct SideCtx<'a> {
    pub(crate) func: &'a MachFunction,
    pub(crate) side: Side,
    pub(crate) address: AddressModel,
    /// Stack slots with this id or above were created by register
    /// allocation: their accesses are storage, not effects.
    pub(crate) allocator_slot_start: u32,
    /// After frame lowering: `SPILL_SLOT_ACCESS`-flagged accesses and
    /// accesses inside `[CFA + lo, CFA + hi)` (the callee-save area) are
    /// storage.
    pub(crate) frame_storage: Option<(i64, i64)>,
    /// After frame lowering: the CFA-relative byte ranges `[start, end)` of
    /// the program's stack slots (by slot id). Frame storage is private only
    /// if no storage access touches one of them.
    pub(crate) program_slots: Vec<(i64, i64, u32)>,
    /// After frame lowering: the CFA-relative byte range `[start, end)` of
    /// the outgoing stack-argument area at the bottom of the frame (empty
    /// when no call passes arguments on the stack). The stack-argument
    /// stores are program effects and the callee reads (and may write) the
    /// area, so no frame-storage access may touch it.
    pub(crate) outgoing_area: (i64, i64),
    /// X18 is the platform register (Darwin): the implementation may not
    /// write it.
    pub(crate) reserved_x18: bool,
    /// After frame lowering: instructions with an id at or above this were
    /// inserted by frame lowering (the arena is append-only), and their
    /// frame accesses (callee-save saves and restores, stack probes) are
    /// storage.
    pub(crate) inserted_from: Option<u32>,
    /// Recorded trap expansions: an instruction id to `(record, position)`.
    pub(crate) trap_records: HashMap<InstId, (usize, usize)>,
}

// ---------------------------------------------------------------------------
// Execution results
// ---------------------------------------------------------------------------

/// How a call or other effect changes registers beyond its outputs.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Clobber {
    None,
    /// An AAPCS64/DarwinPCS call: X0-X7 and V0-V7 hold results, the other
    /// volatile registers and NZCV are unknown, V8-V15 keep their low halves.
    Call,
}

/// A register write an effect performs after its outputs, independent of
/// the effect's result (a writeback base update).
#[derive(Clone, Copy, Debug)]
pub(crate) struct Writeback {
    pub(crate) view: View,
    pub(crate) value: TermId,
}

/// An effect, ready to be compared with the other function's.
#[derive(Clone, Debug)]
pub(crate) struct Event {
    pub(crate) key: OpId,
    pub(crate) args: Vec<TermId>,
    /// Registers receiving the effect's results, in slot order.
    pub(crate) outputs: Vec<View>,
    /// Whether the effect defines NZCV (as a result).
    pub(crate) flags_out: bool,
    pub(crate) writebacks: Vec<Writeback>,
    pub(crate) clobber: Clobber,
    /// Program-memory store `(address, bytes)`, which invalidates
    /// overlapping storage cells.
    pub(crate) store: Option<(TermId, u16)>,
    /// The effect may write memory the model does not place: anything but
    /// a plain load or store (a call, an atomic, a barrier, a trap carrier,
    /// an exit).
    pub(crate) opaque_write: bool,
    /// Registers whose values become unknown after the effect (the scratch
    /// and flag writes of a recorded trap expansion).
    pub(crate) junk_after: Vec<View>,
    /// Per argument, the width the comparison reads it at (empty: every
    /// argument at its full width). A call argument the caller wrote
    /// through a narrower view is observed only at that width.
    pub(crate) arg_widths: Vec<u16>,
    /// The instruction (first of a recorded expansion).
    pub(crate) inst: InstId,
    /// Instructions consumed (more than one for a recorded expansion).
    pub(crate) span: usize,
}

/// Outcome of executing one instruction.
pub(crate) enum Exec {
    /// Applied to the state (a move, pure operation or storage access).
    Applied,
    /// An effect to compare before it is applied.
    Event(Box<Event>),
    /// A pair access: one effect per element, in address order (a pair is
    /// two single-register accesses, so a pass may split it).
    Pair(Box<Event>, Box<Event>),
}

/// Why an instruction was not executed.
#[derive(Clone, Debug)]
pub(crate) enum ExecStop {
    /// The instruction is outside the model, with the reason.
    Unmodeled(String),
    /// Executing it breaks a property the model checks (a frame-storage
    /// access outside the private storage area).
    Violation(ViolationKind, String),
}

type ExecResult = Result<Exec, ExecStop>;

fn unmodeled<T>(inst: &MachInst, why: impl std::fmt::Display) -> Result<T, ExecStop> {
    Err(ExecStop::Unmodeled(format!("{:?}: {why}", inst.opcode)))
}

// ---------------------------------------------------------------------------
// Instruction classes
// ---------------------------------------------------------------------------

/// The allocator's def/use partition of an instruction's operands
/// ([`crate::post_ra_reaching_def::operand_role_masks`]).
#[derive(Clone, Copy)]
pub(crate) struct Roles {
    defs: u64,
    uses: u64,
}

impl Roles {
    pub(crate) fn of(inst: &MachInst) -> Result<Self, ExecStop> {
        if inst.operands.len() >= 64 {
            return unmodeled(inst, "64 or more operands");
        }
        let (defs, uses) = crate::post_ra_reaching_def::operand_role_masks(inst);
        Ok(Self { defs, uses })
    }

    pub(crate) fn is_def(self, pos: usize) -> bool {
        pos < 64 && self.defs & (1 << pos) != 0
    }

    pub(crate) fn is_use(self, pos: usize) -> bool {
        pos < 64 && self.uses & (1 << pos) != 0
    }
}

/// Branch-family opcodes that end a block's straight-line body.
pub(crate) fn is_branch_opcode(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        op,
        B | BCond | Bcc | Cbz | Cbnz | Tbz | Tbnz | Br | Ret | TailCall
    )
}

/// Calls that follow the AAPCS64/DarwinPCS clobber convention.
fn is_standard_call(op: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(op, Bl | BL | Blr | BLR)
}

/// A plain load or store whose spelling post-allocation rewrites change.
#[derive(Clone, Copy, Debug)]
struct PlainMem {
    load: bool,
    /// Data operand positions (one, or two for a pair).
    data: [usize; 2],
    pair: bool,
    /// Bytes per data register (`0` = the data register's width).
    bytes: u16,
    /// 0 zero-extend, 1 sign-extend.
    sign: bool,
    volatile: bool,
    base: usize,
    /// Pre-index (`true`) or post-index (`false`) writeback.
    writeback: Option<bool>,
}

/// The byte offset after a stack-slot address operand at `base`: an
/// immediate or nothing (any other operand there is outside the model).
fn slot_offset(inst: &MachInst, base: usize) -> Result<i64, ExecStop> {
    match inst.operands.get(base + 1) {
        None => Ok(0),
        Some(MachOperand::Imm(off)) => Ok(*off),
        Some(other) => unmodeled(
            inst,
            format!("unmodeled stack-slot offset operand {other:?}"),
        ),
    }
}

fn plain_mem(op: AArch64Opcode) -> Option<PlainMem> {
    use AArch64Opcode::*;
    let single = |load: bool, bytes: u16, sign: bool, volatile: bool| PlainMem {
        load,
        data: [0, 0],
        pair: false,
        bytes,
        sign,
        volatile,
        base: 1,
        writeback: None,
    };
    Some(match op {
        LdrRI => single(true, 0, false, false),
        LdrbRI => single(true, 1, false, false),
        LdrhRI => single(true, 2, false, false),
        LdrsbRI => single(true, 1, true, false),
        LdrshRI => single(true, 2, true, false),
        StrRI => single(false, 0, false, false),
        StrbRI => single(false, 1, false, false),
        StrhRI => single(false, 2, false, false),
        STRWui => single(false, 4, false, false),
        STRXui => single(false, 8, false, false),
        STRSui => single(false, 4, false, false),
        STRDui => single(false, 8, false, false),
        VolatileLdrRI => single(true, 0, false, true),
        VolatileLdrbRI => single(true, 1, false, true),
        VolatileLdrhRI => single(true, 2, false, true),
        VolatileStrRI => single(false, 0, false, true),
        VolatileStrbRI => single(false, 1, false, true),
        VolatileStrhRI => single(false, 2, false, true),
        LdrPreIndex | LdrPostIndex => PlainMem {
            writeback: Some(op == LdrPreIndex),
            ..single(true, 0, false, false)
        },
        StrPreIndex | StrPostIndex => PlainMem {
            writeback: Some(op == StrPreIndex),
            ..single(false, 0, false, false)
        },
        LdpRI | StpRI | LdpPostIndex | StpPreIndex => PlainMem {
            load: matches!(op, LdpRI | LdpPostIndex),
            data: [0, 1],
            pair: true,
            bytes: 0,
            sign: false,
            volatile: false,
            base: 2,
            writeback: match op {
                StpPreIndex => Some(true),
                LdpPostIndex => Some(false),
                _ => None,
            },
        },
        _ => return None,
    })
}

// ---------------------------------------------------------------------------
// The executor
// ---------------------------------------------------------------------------

/// Executes instructions of one function against a [`State`].
pub(crate) struct Exec1<'c, 'a> {
    pub(crate) arena: &'c mut TermArena,
    pub(crate) ctx: &'c SideCtx<'a>,
    /// Block and position used to key deterministic unknowns.
    pub(crate) block: u32,
    pub(crate) site: u32,
}

impl Exec1<'_, '_> {
    // -- register access ---------------------------------------------------

    /// A deterministic unknown for this side, block and site.
    fn unknown(&mut self, slot: u64, bits: u16) -> TermId {
        self.arena
            .unknown(self.ctx.side as u8, self.block, self.site, slot, bits)
    }

    pub(crate) fn read(&mut self, state: &State, view: View) -> TermId {
        match view.place {
            Place::Phys(loc) => {
                let full = state.phys[loc as usize];
                self.arena.trunc(view.bits, full)
            }
            Place::Virt(id) => match state.virt.get(&id) {
                Some(&term) => self.arena.resize(view.bits, term),
                // A read with no reaching definition: nothing in particular.
                None => self.unknown(0x4000_0000_0000_0000 | u64::from(id), view.bits),
            },
        }
    }

    fn read_reg(&mut self, state: &State, reg: Reg) -> TermId {
        match reg {
            Reg::View(view) => self.read(state, view),
            Reg::Zero(bits) => self.arena.constant(bits, 0),
        }
    }

    /// Write `value` through `view`: an AArch64 register write zeroes the
    /// bits above the written view.
    pub(crate) fn write(&mut self, state: &mut State, view: View, value: TermId) {
        let value = self.arena.resize(view.bits, value);
        match view.place {
            Place::Phys(loc) => {
                let full = loc_bits(loc);
                state.phys[loc as usize] = self.arena.zext(full, value);
                state.written[loc as usize] = view.bits;
            }
            Place::Virt(id) => {
                state.virt.insert(id, value);
            }
        }
    }

    fn write_reg(&mut self, state: &mut State, reg: Reg, value: TermId) {
        if let Reg::View(view) = reg {
            self.write(state, view, value);
        }
    }

    // -- addresses ---------------------------------------------------------

    fn slot_address(&mut self, inst: &MachInst, slot: u32) -> Result<TermId, ExecStop> {
        match &self.ctx.address {
            AddressModel::Symbolic => Ok(self.arena.slot(slot)),
            AddressModel::Frame { slot_cfa } => {
                match slot_cfa.get(slot as usize).copied().flatten() {
                    Some(offset) => {
                        let cfa = self.arena.cfa();
                        Ok(self.arena.lin(cfa, offset))
                    }
                    None => unmodeled(inst, format!("stack slot {slot} has no fixed frame offset")),
                }
            }
        }
    }

    fn incoming_address(&mut self, offset: i64) -> TermId {
        match &self.ctx.address {
            AddressModel::Symbolic => self.arena.incoming_arg(offset),
            AddressModel::Frame { .. } => {
                let cfa = self.arena.cfa();
                self.arena.lin(cfa, offset)
            }
        }
    }

    /// The effective address formed by the operands starting at `base`
    /// (`[base]`, `[base, #imm]`, `[base, IncomingArg]`, `[MemOp]`,
    /// `[StackSlot]`, `[StackSlot, #imm]`), and whether the base names an
    /// allocator-created stack slot.
    fn address(
        &mut self,
        state: &State,
        inst: &MachInst,
        base: usize,
    ) -> Result<(TermId, bool), ExecStop> {
        let ops = &inst.operands;
        let Some(op) = ops.get(base) else {
            return unmodeled(inst, "missing address operand");
        };
        match op {
            MachOperand::MemOp { base: reg, offset } => {
                let Some(Ok(reg)) = operand_reg(&MachOperand::PReg(*reg)) else {
                    return unmodeled(inst, "memory operand base is not a modeled register");
                };
                let b = self.read_reg(state, reg);
                Ok((self.arena.lin(b, *offset), false))
            }
            MachOperand::StackSlot(slot) => {
                let a = self.slot_address(inst, slot.0)?;
                let off = slot_offset(inst, base)?;
                Ok((
                    self.arena.lin(a, off),
                    slot.0 >= self.ctx.allocator_slot_start,
                ))
            }
            MachOperand::FrameIndex(index) => {
                let Ok(slot) = u32::try_from(index.0) else {
                    return unmodeled(inst, "negative frame index");
                };
                let a = self.slot_address(inst, slot)?;
                let off = slot_offset(inst, base)?;
                Ok((
                    self.arena.lin(a, off),
                    slot >= self.ctx.allocator_slot_start,
                ))
            }
            _ => match operand_reg(op) {
                Some(Ok(reg)) => match ops.get(base + 1) {
                    // `[FP, IncomingArg(n)]`: the caller's argument area.
                    Some(MachOperand::IncomingArg(offset)) => {
                        Ok((self.incoming_address(*offset), false))
                    }
                    None => {
                        let b = self.read_reg(state, reg);
                        Ok((self.arena.lin(b, 0), false))
                    }
                    Some(MachOperand::Imm(off)) => {
                        let b = self.read_reg(state, reg);
                        Ok((self.arena.lin(b, *off), false))
                    }
                    // `[Xn, #:lo12:sym]` (the late ADRP/ADD lo12 fusion folds
                    // `ADD Xa, Xn, #:lo12:sym` into the access): the address
                    // that `ADD` computes, the same term on both sides.
                    Some(MachOperand::Symbol(name)) => {
                        let b = self.read_reg(state, reg);
                        Ok((self.page_offset_address(b, name, false), false))
                    }
                    Some(MachOperand::ExactModuleSymbol(name)) => {
                        let b = self.read_reg(state, reg);
                        Ok((self.page_offset_address(b, name, true), false))
                    }
                    Some(other) => {
                        unmodeled(inst, format!("unmodeled address offset operand {other:?}"))
                    }
                },
                Some(Err(why)) => unmodeled(inst, why),
                None => unmodeled(inst, format!("unmodeled address operand {op:?}")),
            },
        }
    }

    /// `base + lo12(name)`: the value `ADD Xd, Xn, #:lo12:name`
    /// (`AddPCRel [Xd, Xn, Symbol]`, both 64-bit) computes from `base`.
    fn page_offset_address(&mut self, base: TermId, name: &str, exact: bool) -> TermId {
        let key = self.arena.op_id(OpKey {
            tag: OpTag::Inst(AArch64Opcode::AddPCRel as u16),
            aux: vec![
                Aux::View(0, 64, false),
                Aux::View(1, 64, false),
                Aux::Sym(2, name.to_string(), exact),
            ],
        });
        self.arena.op_term(key, &[base], 0, 64)
    }

    /// The storage cell an access at `addr` names, if it is storage.
    /// `fresh_probe` marks a store of zero at the current SP (a stack
    /// probe) wholly below every byte any earlier write touched.
    fn storage_cell(
        &mut self,
        id: InstId,
        inst: &MachInst,
        addr: TermId,
        allocator_slot: bool,
        bytes: u16,
        fresh_probe: bool,
    ) -> Result<Option<(TermId, i64)>, ExecStop> {
        let (base, offset) = self.arena.split_lin(addr);
        let spill = inst.flags.contains(InstFlags::SPILL_SLOT_ACCESS);
        let inserted = self.ctx.inserted_from.is_some_and(|from| id.0 >= from);
        if allocator_slot {
            return match self.arena.get(base) {
                Term::Slot(_) | Term::Cfa => Ok(Some((base, offset))),
                _ => unmodeled(inst, "allocator storage access with an unmodeled base"),
            };
        }
        if let Some((lo, hi)) = self.ctx.frame_storage {
            let in_save_area = matches!(self.arena.get(base), Term::Cfa)
                && offset >= lo
                && offset + i64::from(bytes) <= hi;
            if spill || inserted || in_save_area {
                if !matches!(self.arena.get(base), Term::Cfa) {
                    return unmodeled(
                        inst,
                        format!(
                            "frame storage access whose address {} is not CFA-relative",
                            self.arena.render(addr)
                        ),
                    );
                }
                // Storage cells are private: the model does not track
                // program memory, so a storage access that reached the
                // caller's frame, a program stack slot or the outgoing
                // stack-argument area would move a value the comparison
                // never sees. A stack probe (frame lowering's inserted
                // `STR XZR, [SP]`) may land on a program slot or the
                // outgoing area only where nothing has written yet: memory
                // the allocation it follows has just made part of the frame.
                self.check_private(inst, offset, bytes, inserted && !spill && fresh_probe)?;
                return Ok(Some((base, offset)));
            }
        }
        Ok(None)
    }

    /// Refuse a frame-storage access of `bytes` at `CFA + offset` that is
    /// not below the CFA or (unless `may_touch_program` holds) that overlaps
    /// a program stack slot or the outgoing stack-argument area.
    fn check_private(
        &self,
        inst: &MachInst,
        offset: i64,
        bytes: u16,
        may_touch_program: bool,
    ) -> Result<(), ExecStop> {
        let end = offset.saturating_add(i64::from(bytes));
        if end > 0 {
            return Err(ExecStop::Violation(
                ViolationKind::FrameMismatch,
                format!(
                    "{:?} {:?}: frame storage access at CFA{offset:+} ({bytes} bytes) reaches the caller's frame",
                    inst.opcode, inst.operands
                ),
            ));
        }
        if may_touch_program {
            return Ok(());
        }
        let (out_start, out_stop) = self.ctx.outgoing_area;
        if offset < out_stop && out_start < end {
            return Err(ExecStop::Violation(
                ViolationKind::FrameMismatch,
                format!(
                    "{:?} {:?}: frame storage access at CFA{offset:+} ({bytes} bytes) overlaps the outgoing stack-argument area [CFA{out_start:+}, CFA{out_stop:+})",
                    inst.opcode, inst.operands
                ),
            ));
        }
        if let Some(&(start, stop, slot)) = self
            .ctx
            .program_slots
            .iter()
            .find(|&&(start, stop, _)| offset < stop && start < end)
        {
            return Err(ExecStop::Violation(
                ViolationKind::FrameMismatch,
                format!(
                    "{:?} {:?}: frame storage access at CFA{offset:+} ({bytes} bytes) overlaps program stack slot {slot} [CFA{start:+}, CFA{stop:+})",
                    inst.opcode, inst.operands
                ),
            ));
        }
        Ok(())
    }

    fn cell_store(state: &mut State, key: (TermId, i64), value: TermId, bytes: u16) {
        Self::invalidate(state, key.0, key.1, i64::from(bytes));
        state.cells.insert(key, Cell { value, bytes });
    }

    /// Remove every cell overlapping `[base + offset, base + offset + bytes)`.
    pub(crate) fn invalidate(state: &mut State, base: TermId, offset: i64, bytes: i64) {
        let end = offset.saturating_add(bytes);
        let doomed: Vec<(TermId, i64)> = state
            .cells
            .range((base, i64::MIN)..=(base, i64::MAX))
            .filter(|&(&(_, start), cell)| start < end && start + i64::from(cell.bytes) > offset)
            .map(|(&key, _)| key)
            .collect();
        for key in doomed {
            state.cells.remove(&key);
        }
    }

    fn cell_load(&mut self, state: &State, key: (TermId, i64), bytes: u16) -> TermId {
        match state.cells.get(&key) {
            Some(cell) if cell.bytes == bytes => cell.value,
            Some(cell) if cell.bytes > bytes => {
                let value = cell.value;
                self.arena.trunc(bytes * 8, value)
            }
            // Unwritten or partially written storage: nothing in particular.
            _ => self.unknown(
                0x2000_0000_0000_0000 ^ ((key.0.0 as u64) << 24) ^ (key.1 as u64),
                bytes * 8,
            ),
        }
    }

    // -- operation keys ----------------------------------------------------

    /// The register views, immediates and other non-register operands of an
    /// instruction, as operation-key data.
    fn operand_aux(&self, inst: &MachInst) -> Result<Vec<Aux>, ExecStop> {
        let mut aux = Vec::with_capacity(inst.operands.len());
        for (pos, op) in inst.operands.iter().enumerate() {
            let pos = pos as u8;
            match op {
                MachOperand::Imm(v) => aux.push(Aux::Imm(pos, *v)),
                MachOperand::FImm(v) => aux.push(Aux::FImm(pos, v.to_bits())),
                MachOperand::Symbol(s) => aux.push(Aux::Sym(pos, s.clone(), false)),
                MachOperand::ExactModuleSymbol(s) => aux.push(Aux::Sym(pos, s.clone(), true)),
                MachOperand::JumpTableIndex(i) => aux.push(Aux::JumpTable(pos, *i)),
                MachOperand::Block(_) => aux.push(Aux::Shape(pos, 1)),
                MachOperand::StackSlot(_) | MachOperand::FrameIndex(_) => {
                    aux.push(Aux::Shape(pos, 2))
                }
                MachOperand::IncomingArg(_) | MachOperand::MemOp { .. } => {
                    aux.push(Aux::Shape(pos, 3))
                }
                _ => match operand_reg(op) {
                    Some(Ok(Reg::View(v))) => aux.push(Aux::View(pos, v.bits, v.fpr)),
                    Some(Ok(Reg::Zero(bits))) => aux.push(Aux::Zero(pos, bits)),
                    Some(Err(why)) => return unmodeled(inst, why),
                    None => return unmodeled(inst, format!("unmodeled operand {op:?}")),
                },
            }
        }
        Ok(aux)
    }

    /// Input terms and output views of a generic instruction: every use
    /// operand (a memory operand contributes its effective address), then
    /// NZCV when the instruction reads it, then its implicit uses.
    fn generic_io(
        &mut self,
        state: &State,
        inst: &MachInst,
        roles: Roles,
    ) -> Result<(Vec<TermId>, Vec<View>), ExecStop> {
        let mut args = Vec::new();
        let mut outs = Vec::new();
        let mut skip_next = false;
        for (pos, op) in inst.operands.iter().enumerate() {
            if skip_next {
                skip_next = false;
                continue;
            }
            match op {
                MachOperand::MemOp { .. } => {
                    let (addr, slot) = self.address(state, inst, pos)?;
                    if slot {
                        return unmodeled(
                            inst,
                            "an allocator stack slot used as an effect operand",
                        );
                    }
                    args.push(addr);
                    if roles.is_def(pos) {
                        return unmodeled(
                            inst,
                            "a writeback memory operand outside the plain forms",
                        );
                    }
                }
                MachOperand::StackSlot(_)
                | MachOperand::FrameIndex(_)
                | MachOperand::IncomingArg(_) => {
                    let (addr, slot) = self.address(state, inst, pos)?;
                    if slot {
                        return unmodeled(
                            inst,
                            "an allocator stack slot used as an effect operand",
                        );
                    }
                    args.push(addr);
                }
                _ => match operand_reg(op) {
                    Some(Ok(reg)) => {
                        if roles.is_use(pos) {
                            // `[FP, IncomingArg(n)]` names one address.
                            if let Some(MachOperand::IncomingArg(offset)) =
                                inst.operands.get(pos + 1)
                            {
                                args.push(self.incoming_address(*offset));
                                skip_next = true;
                                continue;
                            }
                            args.push(self.read_reg(state, reg));
                        }
                        if roles.is_def(pos)
                            && let Reg::View(view) = reg
                        {
                            outs.push(view);
                        }
                    }
                    Some(Err(why)) => return unmodeled(inst, why),
                    None => {}
                },
            }
        }
        if reads_nzcv(inst) {
            let flags = state.phys[LOC_NZCV as usize];
            args.push(flags);
        }
        let mut implicit: Vec<PReg> = inst.implicit_uses.to_vec();
        implicit.sort_unstable();
        implicit.dedup();
        for p in implicit {
            if p == trust_cg_ir::regs::NZCV && reads_nzcv(inst) {
                continue;
            }
            match preg_reg(p) {
                Some(reg) => {
                    let t = self.read_reg(state, reg);
                    args.push(t);
                }
                None => return unmodeled(inst, format!("unmodeled implicit use {p:?}")),
            }
        }
        Ok((args, outs))
    }

    fn inst_key(&mut self, inst: &MachInst, extra: &[Aux]) -> Result<OpId, ExecStop> {
        let mut aux = self.operand_aux(inst)?;
        let mut implicit: Vec<u16> = inst.implicit_uses.iter().map(|p| p.encoding()).collect();
        implicit.sort_unstable();
        implicit.dedup();
        aux.extend(implicit.into_iter().map(Aux::Implicit));
        aux.extend_from_slice(extra);
        Ok(self.arena.op_id(OpKey {
            tag: OpTag::Inst(inst.opcode as u16),
            aux,
        }))
    }

    // -- the rules ---------------------------------------------------------

    /// Execute `inst` (instruction `id`) against `state`.
    pub(crate) fn exec(&mut self, state: &mut State, id: InstId) -> ExecResult {
        let inst = self.ctx.func.inst(id);
        // A recorded trap expansion is judged as its carrier, whatever its
        // first instruction is.
        if let Some(&(record, position)) = self.ctx.trap_records.get(&id) {
            return self
                .trap_expansion_event(state, id, record, position)
                .map(|e| Exec::Event(Box::new(e)));
        }
        use AArch64Opcode::*;
        match inst.opcode {
            Nop | AlignNop => return Ok(Exec::Applied),
            Phi => return unmodeled(inst, "a phi survives to the compared function"),
            _ => {}
        }
        if let Some(applied) = self.try_move(state, inst)? {
            return Ok(applied);
        }
        // Frame lowering's stack-protector guard reads (`ADRP`/`LDR` of the
        // guard's GOT entry, then of the guard): the guard is constant for
        // the life of the process, so each read is a value of its address.
        if self.ctx.inserted_from.is_some_and(|from| id.0 >= from)
            && self.is_stack_guard_read(state, inst)
        {
            self.exec_pure(state, inst)?;
            return Ok(Exec::Applied);
        }
        // The ELF TLSDESC sequence frame lowering expands a `TlsDescCall`
        // into (`ADRP x0`, `LDR x1, [x0, #:tlsdesc_lo12:]`, `ADD x0, x0,
        // #:tlsdesc_lo12:`, `BLR x1`): the descriptor's resolver slot is
        // written by the dynamic linker before any code runs, so the inserted
        // read is a value of its address, and the call is the specification's
        // `TlsDescCall` when x0 and x1 hold exactly the descriptor address and
        // its resolver.
        if inst.opcode == AArch64Opcode::LdrTlsdesc
            && self.ctx.inserted_from.is_some_and(|from| id.0 >= from)
        {
            self.exec_pure(state, inst)?;
            return Ok(Exec::Applied);
        }
        if inst.opcode == AArch64Opcode::BlrTlsdesc {
            return self
                .tlsdesc_call_event(state, id, inst)
                .map(|e| Exec::Event(Box::new(e)));
        }
        if let Some(mem) = plain_mem(inst.opcode) {
            return self.exec_plain_mem(state, id, inst, mem);
        }
        if let Some(result) = self.exec_register_offset(state, id, inst) {
            return result;
        }
        if is_branch_opcode(inst.opcode) {
            return unmodeled(inst, "a branch inside a block body");
        }
        let pure = opcode_effect(inst.opcode).is_pure()
            && !inst.flags.contains(InstFlags::IS_CALL)
            && !inst.flags.contains(InstFlags::IS_BRANCH)
            && !inst.flags.contains(InstFlags::IS_RETURN)
            && !inst.flags.contains(InstFlags::IS_TERMINATOR)
            && !inst.flags.contains(InstFlags::READS_MEMORY)
            && !inst.flags.contains(InstFlags::WRITES_MEMORY)
            && !matches!(
                inst.opcode,
                Brk | TrapOverflow
                    | TrapBoundsCheck
                    | TrapBoundsCheckExact
                    | TrapNull
                    | TrapNullIfZero
                    | TrapDivZero
                    | TrapDivZeroIfZero
                    | TrapShiftRange
                    | TrapShiftRangeIfOOB
                    | TrapOverflowExact
                    | Copy
                    | Phi
            );
        if pure {
            self.exec_pure(state, inst)?;
            return Ok(Exec::Applied);
        }
        self.generic_event(state, id, inst)
            .map(|e| Exec::Event(Box::new(e)))
    }

    /// Whether `inst` reads the stack-protector guard or its GOT entry.
    fn is_stack_guard_read(&mut self, state: &State, inst: &MachInst) -> bool {
        let names_guard = |op: &MachOperand| matches!(op, MachOperand::Symbol(s) if s.contains("stack_chk_guard"));
        match inst.opcode {
            AArch64Opcode::LdrGot => inst.operands.iter().any(names_guard),
            AArch64Opcode::LdrRI => {
                let Some(Some(Ok(Reg::View(base)))) = inst.operands.get(1).map(operand_reg) else {
                    return false;
                };
                let address = self.read(state, base);
                self.mentions_guard(address, 4)
            }
            _ => false,
        }
    }

    fn mentions_guard(&self, t: TermId, depth: u32) -> bool {
        if depth == 0 {
            return false;
        }
        match self.arena.get(t) {
            Term::Op { op, args, .. } => {
                self.arena.op(*op).aux.iter().any(
                    |aux| matches!(aux, Aux::Sym(_, name, _) if name.contains("stack_chk_guard")),
                ) || args.iter().any(|&a| self.mentions_guard(a, depth - 1))
            }
            Term::Lin { base, .. } => self.mentions_guard(*base, depth - 1),
            Term::Sum { atoms } => atoms
                .iter()
                .any(|&(atom, _)| self.mentions_guard(atom, depth - 1)),
            _ => false,
        }
    }

    /// Register copies, constant moves and 64-bit linear address arithmetic.
    fn try_move(&mut self, state: &mut State, inst: &MachInst) -> Result<Option<Exec>, ExecStop> {
        use AArch64Opcode::*;
        let ops = &inst.operands;
        let reg_at = |k: usize| -> Option<Reg> {
            match ops.get(k).and_then(operand_reg) {
                Some(Ok(reg)) => Some(reg),
                _ => None,
            }
        };
        match inst.opcode {
            Copy | MovR | MOVWrr | MOVXrr | FmovFprFpr | FmovGprFpr | FmovFprGpr
                if ops.len() == 2 =>
            {
                let (Some(dst), Some(src)) = (reg_at(0), reg_at(1)) else {
                    return Ok(None);
                };
                let value = self.read_copy_source(state, dst, src);
                self.write_reg(state, dst, value);
                Ok(Some(Exec::Applied))
            }
            // `ORR Vd, Vn, Vn` (optionally with the Q=1 selector): a move.
            NeonOrrV if (ops.len() == 3 || ops.len() == 4) && ops[1] == ops[2] => {
                let (Some(dst), Some(src)) = (reg_at(0), reg_at(1)) else {
                    return Ok(None);
                };
                let q = match ops.get(3) {
                    Some(MachOperand::Imm(1)) => true,
                    Some(_) => return Ok(None),
                    None => matches!(dst, Reg::View(View { bits: 128, .. })),
                };
                let (Reg::View(dst), Reg::View(src)) = (dst, src) else {
                    return Ok(None);
                };
                let width = if q { 128 } else { 64 };
                let src_full = View { bits: width, ..src };
                let value = match src.place {
                    Place::Phys(_) => self.read(state, src_full),
                    // A virtual source holds only its own class's bits.
                    Place::Virt(_) => {
                        let v = self.read(state, src);
                        self.arena.resize(width, v)
                    }
                };
                match dst.place {
                    Place::Phys(_) => self.write(state, View { bits: width, ..dst }, value),
                    Place::Virt(_) => self.write(state, dst, value),
                }
                Ok(Some(Exec::Applied))
            }
            MovI | Movz | Movn | MOVZWi | MOVZXi => {
                let Some(dst) = reg_at(0) else {
                    return Ok(None);
                };
                let (Some(MachOperand::Imm(imm)), shift) = (ops.get(1), ops.get(2)) else {
                    return Ok(None);
                };
                let shift = match shift {
                    None => 0,
                    Some(MachOperand::Imm(s)) if (0..64).contains(s) => *s as u32,
                    Some(_) => return Ok(None),
                };
                if ops.len() > 3 {
                    return Ok(None);
                }
                let bits = match dst {
                    Reg::View(v) => v.bits,
                    Reg::Zero(b) => b,
                };
                let raw = ((*imm as u64) & 0xffff) << shift;
                let value = if inst.opcode == Movn { !raw } else { raw };
                let c = self.arena.constant(bits, u128::from(value));
                self.write_reg(state, dst, c);
                Ok(Some(Exec::Applied))
            }
            Movk => {
                let Some(dst) = reg_at(0) else {
                    return Ok(None);
                };
                let Reg::View(view) = dst else {
                    return Ok(None);
                };
                let (Some(MachOperand::Imm(imm)), shift) = (ops.get(1), ops.get(2)) else {
                    return Ok(None);
                };
                let shift = match shift {
                    None => 0,
                    Some(MachOperand::Imm(s)) if (0..64).contains(s) && s % 16 == 0 => *s as u32,
                    Some(_) => return Ok(None),
                };
                let old = self.read(state, view);
                match self.arena.const_value(old) {
                    Some(prev) if ops.len() <= 3 => {
                        let field = 0xffffu128 << shift;
                        let value = (prev & !field) | ((((*imm as u64) & 0xffff) as u128) << shift);
                        let c = self.arena.constant(view.bits, value);
                        self.write(state, view, c);
                        Ok(Some(Exec::Applied))
                    }
                    _ => Ok(None),
                }
            }
            // Zero extensions: the low 8/16/32 bits, zero-extended.
            Uxtb | Uxth | Uxtw if ops.len() == 2 => {
                let (Some(Reg::View(dst)), Some(src)) = (reg_at(0), reg_at(1)) else {
                    return Ok(None);
                };
                if dst.fpr {
                    return Ok(None);
                }
                let from = match inst.opcode {
                    Uxtb => 8,
                    Uxth => 16,
                    _ => 32,
                };
                let v = self.read_reg(state, src);
                let low = self.arena.trunc(from, v);
                let value = self.arena.zext(dst.bits, low);
                self.write(state, dst, value);
                Ok(Some(Exec::Applied))
            }
            // A 32-bit add/subtract of an immediate: the low 32 bits of the
            // 64-bit sum of the zero-extended source (`#0` is a W copy).
            AddRI | SubRI
                if ops.len() == 3
                    && matches!(
                        reg_at(0),
                        Some(Reg::View(View {
                            bits: 32,
                            fpr: false,
                            ..
                        }))
                    )
                    && matches!(ops[2], MachOperand::Imm(_)) =>
            {
                let (Some(Reg::View(dst)), Some(src)) = (reg_at(0), reg_at(1)) else {
                    return Ok(None);
                };
                let MachOperand::Imm(k) = ops[2] else {
                    return Ok(None);
                };
                let v = self.read_reg(state, src);
                let low = self.arena.trunc(32, v);
                let wide = self.arena.zext(64, low);
                let k = if inst.opcode == SubRI {
                    k.wrapping_neg()
                } else {
                    k
                };
                let sum = self.arena.lin(wide, k);
                let value = self.arena.trunc(32, sum);
                self.write(state, dst, value);
                Ok(Some(Exec::Applied))
            }
            AddRI | SubRI | AddRIShift12 => {
                let Some(Reg::View(dst)) = reg_at(0) else {
                    return Ok(None);
                };
                if dst.bits != 64 || dst.fpr {
                    return Ok(None);
                }
                if ops.len() != 3 {
                    return Ok(None);
                }
                let (base, slot) = match (&ops[1], &ops[2]) {
                    // `ADD d, slot, #imm`: the slot address plus the imm.
                    (
                        MachOperand::StackSlot(_) | MachOperand::FrameIndex(_),
                        MachOperand::Imm(_),
                    ) if inst.opcode == AddRI => self.address(state, inst, 1)?,
                    // `ADD d, FP, IncomingArg(n)`: the caller's argument area.
                    (_, MachOperand::IncomingArg(offset)) if inst.opcode == AddRI => {
                        (self.incoming_address(*offset), false)
                    }
                    (_, MachOperand::Imm(k)) => {
                        let Some(src) = reg_at(1) else {
                            return Ok(None);
                        };
                        let b = self.read_reg(state, src);
                        if self.arena.bits(b) != 64 {
                            return Ok(None);
                        }
                        let k = match inst.opcode {
                            AddRI => *k,
                            SubRI => k.wrapping_neg(),
                            _ => k.wrapping_shl(12),
                        };
                        (self.arena.lin(b, k), false)
                    }
                    _ => return Ok(None),
                };
                if slot {
                    return unmodeled(inst, "the address of an allocator stack slot is taken");
                }
                self.write(state, dst, base);
                Ok(Some(Exec::Applied))
            }
            // `ADD Xd, _, StackSlot` (the StackAddr form): the slot address.
            AddPCRel
                if ops.len() == 3
                    && matches!(
                        ops[2],
                        MachOperand::StackSlot(_) | MachOperand::FrameIndex(_)
                    ) =>
            {
                let Some(Reg::View(dst)) = reg_at(0) else {
                    return Ok(None);
                };
                let (addr, slot) = self.address(state, inst, 2)?;
                if slot {
                    return unmodeled(inst, "the address of an allocator stack slot is taken");
                }
                self.write(state, dst, addr);
                Ok(Some(Exec::Applied))
            }
            AddRR | SubRR if ops.len() == 3 && inst.implicit_defs.is_empty() => {
                let (Some(Reg::View(dst)), Some(a), Some(b)) = (reg_at(0), reg_at(1), reg_at(2))
                else {
                    return Ok(None);
                };
                if dst.bits != 64 || dst.fpr {
                    return Ok(None);
                }
                let ta = self.read_reg(state, a);
                let tb = self.read_reg(state, b);
                if self.arena.bits(ta) != 64 || self.arena.bits(tb) != 64 {
                    return Ok(None);
                }
                // The 64-bit wrapping sum or difference (an affine form).
                let k = if inst.opcode == SubRR { u64::MAX } else { 1 };
                let Some(sum) = self.arena.add_scaled64(ta, tb, k) else {
                    return Ok(None);
                };
                self.write(state, dst, sum);
                Ok(Some(Exec::Applied))
            }
            // `LSL Xd, Xn, #s` and `ADD Xd, Xn, Xm, LSL #k` on 64-bit
            // registers: wrapping multiples by `2^s` (affine forms).
            LslRI | AddRRShift
                if ops.len() == if inst.opcode == LslRI { 3 } else { 4 }
                    && inst.implicit_defs.is_empty() =>
            {
                let Some(Reg::View(dst)) = reg_at(0) else {
                    return Ok(None);
                };
                if dst.bits != 64 || dst.fpr {
                    return Ok(None);
                }
                let Some(MachOperand::Imm(shift)) = ops.last() else {
                    return Ok(None);
                };
                if !(0..64).contains(shift) {
                    return Ok(None);
                }
                let factor = 1u64 << *shift;
                let value = if inst.opcode == LslRI {
                    let Some(src) = reg_at(1) else {
                        return Ok(None);
                    };
                    let t = self.read_reg(state, src);
                    if self.arena.bits(t) != 64 {
                        return Ok(None);
                    }
                    match self.arena.scale64(t, factor) {
                        Some(value) => value,
                        None => return Ok(None),
                    }
                } else {
                    let (Some(a), Some(b)) = (reg_at(1), reg_at(2)) else {
                        return Ok(None);
                    };
                    let ta = self.read_reg(state, a);
                    let tb = self.read_reg(state, b);
                    if self.arena.bits(ta) != 64 || self.arena.bits(tb) != 64 {
                        return Ok(None);
                    }
                    match self.arena.add_scaled64(ta, tb, factor) {
                        Some(value) => value,
                        None => return Ok(None),
                    }
                };
                self.write(state, dst, value);
                Ok(Some(Exec::Applied))
            }
            _ => Ok(None),
        }
    }

    /// The value a copy from `src` into `dst` writes.
    fn read_copy_source(&mut self, state: &State, dst: Reg, src: Reg) -> TermId {
        let dst_bits = match dst {
            Reg::View(v) => v.bits,
            Reg::Zero(b) => b,
        };
        match src {
            Reg::Zero(_) => self.arena.constant(dst_bits, 0),
            Reg::View(src_view) => {
                // A physical source wider-read than its view (e.g. a 64-bit
                // `MOV X` of a register named through W) copies the whole
                // register, exactly as the hardware does.
                if dst_bits > src_view.bits
                    && let Place::Phys(_) = src_view.place
                {
                    let wide = View {
                        bits: dst_bits.min(loc_bits(match src_view.place {
                            Place::Phys(l) => l,
                            Place::Virt(_) => 0,
                        })),
                        ..src_view
                    };
                    return self.read(state, wide);
                }
                let v = self.read(state, src_view);
                self.arena.resize(dst_bits, v)
            }
        }
    }

    fn exec_pure(&mut self, state: &mut State, inst: &MachInst) -> Result<(), ExecStop> {
        let roles = Roles::of(inst)?;
        let (args, outs) = self.generic_io(state, inst, roles)?;
        let mut extra = Vec::new();
        let mut implicit_defs: Vec<PReg> = inst.implicit_defs.to_vec();
        implicit_defs.sort_unstable();
        implicit_defs.dedup();
        extra.extend(
            implicit_defs
                .iter()
                .map(|p| Aux::Implicit(0x8000 | p.encoding())),
        );
        let key = self.inst_key(inst, &extra)?;
        // Known-zero high bits of a mask or a logical right shift.
        let significant = match (inst.opcode, inst.operands.get(2)) {
            (AArch64Opcode::AndRI, Some(MachOperand::Imm(mask))) => {
                Some(64 - (*mask as u64).leading_zeros() as u16)
            }
            (AArch64Opcode::LsrRI, Some(MachOperand::Imm(k))) if (0..64).contains(k) => {
                Some(64 - *k as u16)
            }
            _ => None,
        };
        for (slot, view) in outs.iter().enumerate() {
            let t = self.arena.op_term(key, &args, slot as u16, view.bits);
            if slot == 0
                && let Some(n) = significant
            {
                self.arena.note_significant(t, n.min(view.bits));
            }
            self.write(state, *view, t);
        }
        for (i, p) in implicit_defs.iter().enumerate() {
            if *p == trust_cg_ir::regs::NZCV {
                continue;
            }
            let Some(reg) = preg_reg(*p) else {
                return unmodeled(inst, format!("unmodeled implicit def {p:?}"));
            };
            if let Reg::View(view) = reg {
                let t = self.arena.op_term(key, &args, 0x100 + i as u16, view.bits);
                self.write(state, view, t);
            }
        }
        if definitely_writes_flags(inst.opcode)
            || inst.implicit_defs.contains(&trust_cg_ir::regs::NZCV)
        {
            let t = self.arena.op_term(key, &args, 0xFFFF, NZCV_BITS);
            state.phys[LOC_NZCV as usize] = t;
        }
        Ok(())
    }

    fn exec_plain_mem(
        &mut self,
        state: &mut State,
        id: InstId,
        inst: &MachInst,
        mem: PlainMem,
    ) -> ExecResult {
        let ops = &inst.operands;
        let count = if mem.pair { 2 } else { 1 };
        let mut regs = Vec::with_capacity(count);
        for &pos in &mem.data[..count] {
            match ops.get(pos).and_then(operand_reg) {
                Some(Ok(reg)) => regs.push(reg),
                _ => return unmodeled(inst, "data operand is not a register"),
            }
        }
        let width = |reg: Reg| match reg {
            Reg::View(v) => v.bits,
            Reg::Zero(b) => b,
        };
        let bytes = if mem.bytes != 0 {
            mem.bytes
        } else {
            width(regs[0]) / 8
        };
        if mem.pair && width(regs[1]) != width(regs[0]) {
            return unmodeled(inst, "pair of unequal register widths");
        }
        // The address is one `MemOp`, or a base and at most one offset.
        let last = match ops.get(mem.base) {
            Some(MachOperand::MemOp { .. }) => mem.base + 1,
            _ => mem.base + 2,
        };
        if ops.len() > last {
            return unmodeled(inst, "an operand past the address of a plain access");
        }
        // Address: pre-index adds the immediate, post-index uses the base.
        let (base_addr, allocator_slot) = if mem.writeback == Some(false) {
            let Some(Ok(reg)) = ops.get(mem.base).and_then(operand_reg) else {
                return unmodeled(inst, "post-index base is not a register");
            };
            (self.read_reg(state, reg), false)
        } else {
            self.address(state, inst, mem.base)?
        };
        let addr = base_addr;
        let writeback = match mem.writeback {
            None => None,
            Some(pre) => {
                let Some(Ok(Reg::View(base_view))) = ops.get(mem.base).and_then(operand_reg) else {
                    return unmodeled(inst, "writeback base is not a register");
                };
                let Some(MachOperand::Imm(k)) = ops.get(mem.base + 1) else {
                    return unmodeled(inst, "writeback without an immediate");
                };
                let value = if pre { addr } else { self.arena.lin(addr, *k) };
                Some(Writeback {
                    view: base_view,
                    value,
                })
            }
        };
        self.plain_access(
            state,
            id,
            inst,
            mem,
            &regs,
            bytes,
            addr,
            allocator_slot,
            writeback,
        )
    }

    /// `LDR`/`STR Rt, [Xn, Xm{, LSL #log2(size)}]` (`LdrRO`/`StrRO` with no
    /// extend operand, or the LSL extends `Imm(6)` unscaled and `Imm(7)`
    /// scaled by the access size): a plain access at the 64-bit wrapping sum
    /// `Xn + (Xm << s)`, the address any other spelling of the access
    /// computes. Other extends (`UXTW`, `SXTW`, `SXTX`) stay generic events.
    fn exec_register_offset(
        &mut self,
        state: &mut State,
        id: InstId,
        inst: &MachInst,
    ) -> Option<ExecResult> {
        let load = match inst.opcode {
            AArch64Opcode::LdrRO => true,
            AArch64Opcode::StrRO => false,
            _ => return None,
        };
        let ops = &inst.operands;
        let scaled = match (ops.len(), ops.get(3)) {
            (3, None) => false,
            (4, Some(MachOperand::Imm(6))) => false,
            (4, Some(MachOperand::Imm(7))) => true,
            _ => return None,
        };
        let Some(Ok(data)) = ops.first().and_then(operand_reg) else {
            return None;
        };
        let bits = match data {
            Reg::View(v) => v.bits,
            Reg::Zero(b) => b,
        };
        let bytes = bits / 8;
        if !matches!(bytes, 1 | 2 | 4 | 8 | 16) {
            return None;
        }
        let (Some(Ok(base)), Some(Ok(index))) = (
            ops.get(1).and_then(operand_reg),
            ops.get(2).and_then(operand_reg),
        ) else {
            return None;
        };
        if !matches!(
            index,
            Reg::View(View {
                bits: 64,
                fpr: false,
                ..
            })
        ) {
            return None;
        }
        let tb = self.read_reg(state, base);
        let ti = self.read_reg(state, index);
        if self.arena.bits(tb) != 64 || self.arena.bits(ti) != 64 {
            return None;
        }
        let shift = if scaled { bytes.trailing_zeros() } else { 0 };
        let addr = self.arena.add_scaled64(tb, ti, 1u64 << shift)?;
        let mem = PlainMem {
            load,
            data: [0, 0],
            pair: false,
            bytes: 0,
            sign: false,
            volatile: false,
            base: 1,
            writeback: None,
        };
        Some(self.plain_access(state, id, inst, mem, &[data], bytes, addr, false, None))
    }

    /// A plain access of `regs` (`bytes` each) at `addr`: a storage cell
    /// access, or one program memory effect per element.
    #[allow(clippy::too_many_arguments)]
    fn plain_access(
        &mut self,
        state: &mut State,
        id: InstId,
        inst: &MachInst,
        mem: PlainMem,
        regs: &[Reg],
        bytes: u16,
        addr: TermId,
        allocator_slot: bool,
        writeback: Option<Writeback>,
    ) -> ExecResult {
        let count = regs.len();
        let total = bytes * count as u16;
        let probe = !mem.load
            && regs.iter().all(|reg| matches!(reg, Reg::Zero(_)))
            && addr == state.phys[LOC_SP as usize];
        let fresh_probe = probe && {
            let (base, offset) = self.arena.split_lin(addr);
            matches!(self.arena.get(base), Term::Cfa)
                && offset.saturating_add(i64::from(total)) <= state.touched_low
        };
        if let Some(key) = self.storage_cell(id, inst, addr, allocator_slot, total, fresh_probe)? {
            if mem.sign {
                return unmodeled(inst, "sign-extending storage reload");
            }
            if !mem.load
                && self.ctx.frame_storage.is_some()
                && matches!(self.arena.get(key.0), Term::Cfa)
            {
                state.touched_low = state.touched_low.min(key.1);
            }
            for (i, reg) in regs.iter().enumerate() {
                let cell = (key.0, key.1 + i64::from(bytes) * i as i64);
                if mem.load {
                    let v = self.cell_load(state, cell, bytes);
                    self.write_reg(state, *reg, v);
                } else {
                    let v = self.read_reg(state, *reg);
                    let v = self.arena.resize(bytes * 8, v);
                    Self::cell_store(state, cell, v, bytes);
                }
            }
            if let Some(wb) = writeback {
                self.write(state, wb.view, wb.value);
            }
            return Ok(Exec::Applied);
        }
        if allocator_slot {
            return unmodeled(inst, "allocator storage access that is not storage");
        }
        // A program memory access: one effect per element.
        let mut events = Vec::with_capacity(count);
        for (i, reg) in regs.iter().enumerate() {
            let element = self.arena.lin(addr, i64::from(bytes) * i as i64);
            let mut args = vec![element];
            let mut outputs = Vec::new();
            if mem.load {
                // A load into XZR still reads memory; it defines nothing.
                if let Reg::View(view) = reg {
                    outputs.push(*view);
                }
            } else {
                let v = self.read_reg(state, *reg);
                let v = self.arena.resize(bytes * 8, v);
                args.push(v);
            }
            let mut aux = vec![
                Aux::Imm(0, i64::from(bytes)),
                Aux::Imm(2, i64::from(mem.sign)),
                Aux::Imm(3, i64::from(mem.volatile)),
            ];
            match reg {
                Reg::View(v) => aux.push(Aux::View(0, v.bits, v.fpr)),
                Reg::Zero(b) => aux.push(Aux::Zero(0, *b)),
            }
            let key = self.arena.op_id(OpKey {
                tag: if mem.load { OpTag::Load } else { OpTag::Store },
                aux,
            });
            let last = i + 1 == count;
            events.push(Box::new(Event {
                key,
                args,
                outputs,
                flags_out: false,
                writebacks: if last {
                    writeback.into_iter().collect()
                } else {
                    Vec::new()
                },
                clobber: Clobber::None,
                store: (!mem.load).then_some((element, bytes)),
                opaque_write: false,
                junk_after: Vec::new(),
                arg_widths: Vec::new(),
                inst: id,
                span: 1,
            }));
        }
        let mut events = events.into_iter();
        let first = events.next().expect("one element at least");
        Ok(match events.next() {
            Some(second) => Exec::Pair(first, second),
            None => Exec::Event(first),
        })
    }

    fn generic_event(
        &mut self,
        state: &State,
        id: InstId,
        inst: &MachInst,
    ) -> Result<Event, ExecStop> {
        let roles = Roles::of(inst)?;
        let (mut args, mut outputs) = self.generic_io(state, inst, roles)?;
        let standard_call = is_standard_call(inst.opcode);
        // A call argument is observed at the width it was written through.
        let mut arg_widths = Vec::new();
        if standard_call {
            let explicit = args.len() - {
                let mut implicit: Vec<PReg> = inst.implicit_uses.to_vec();
                implicit.sort_unstable();
                implicit.dedup();
                implicit.len()
            };
            for &arg in &args {
                arg_widths.push(self.arena.bits(arg));
            }
            let mut implicit: Vec<PReg> = inst.implicit_uses.to_vec();
            implicit.sort_unstable();
            implicit.dedup();
            for (k, p) in implicit.iter().enumerate() {
                if let Some(Reg::View(View {
                    place: Place::Phys(loc),
                    bits,
                    ..
                })) = preg_reg(*p)
                {
                    let w = state.written[loc as usize].min(bits);
                    if let Some(slot) = arg_widths.get_mut(explicit + k) {
                        *slot = w;
                    }
                }
            }
        }
        let mut extra = Vec::new();
        // Flags that change what the instruction does: an exact module call
        // binds its target, and a call that cannot unwind has no call-site
        // region of its own, so gaining or losing either is a different
        // effect.
        let behavior = inst.flags.bits()
            & (InstFlags::EXACT_MODULE_CALL.bits() | InstFlags::CANNOT_UNWIND_CALL.bits());
        if behavior != 0 {
            extra.push(Aux::Flags(behavior));
        }
        let mut clobber = Clobber::None;
        let mut flags_out = false;
        let tag;
        if standard_call {
            tag = OpTag::Call;
            clobber = Clobber::Call;
            // Results: every AAPCS64 result register.
            outputs.clear();
            for loc in (0u16..8).chain(LOC_V0..LOC_V0 + 8) {
                outputs.push(View {
                    place: Place::Phys(loc),
                    bits: loc_bits(loc),
                    fpr: loc >= LOC_V0,
                });
            }
        } else {
            tag = OpTag::Inst(inst.opcode as u16);
            let mut implicit_defs: Vec<PReg> = inst.implicit_defs.to_vec();
            implicit_defs.sort_unstable();
            implicit_defs.dedup();
            for p in implicit_defs {
                if p == trust_cg_ir::regs::NZCV {
                    continue;
                }
                extra.push(Aux::Implicit(0x8000 | p.encoding()));
                match preg_reg(p) {
                    Some(Reg::View(view)) => outputs.push(view),
                    Some(Reg::Zero(_)) => {}
                    None => return unmodeled(inst, format!("unmodeled implicit def {p:?}")),
                }
            }
            flags_out = may_clobber_nzcv(inst);
            if inst.opcode == AArch64Opcode::TailCall || inst.opcode == AArch64Opcode::Ret {
                return unmodeled(inst, "an exit inside a block body");
            }
        }
        let mut aux = self.operand_aux(inst)?;
        let mut implicit: Vec<u16> = inst.implicit_uses.iter().map(|p| p.encoding()).collect();
        implicit.sort_unstable();
        implicit.dedup();
        aux.extend(implicit.into_iter().map(Aux::Implicit));
        aux.extend(extra);
        // A store-like effect through a frame address invalidates cells.
        let store = if opcode_effect(inst.opcode).writes_memory() && !standard_call {
            args.first().map(|&a| (a, 16u16))
        } else {
            None
        };
        // Every call reads SP: the callee finds its stack-passed arguments
        // (and the variadic area) at the SP it is entered with, so the SP at
        // the call is an argument like any register one.
        if standard_call || inst.is_call() {
            aux.push(Aux::Implicit(0x4000 | LOC_SP));
            args.push(state.phys[LOC_SP as usize]);
            if standard_call {
                arg_widths.push(64);
            }
        }
        let key = self.arena.op_id(OpKey { tag, aux });
        args.shrink_to_fit();
        Ok(Event {
            key,
            args,
            outputs,
            flags_out,
            writebacks: Vec::new(),
            clobber,
            store,
            opaque_write: true,
            junk_after: Vec::new(),
            arg_widths,
            inst: id,
            span: 1,
        })
    }

    /// `BLR x1` of an expanded TLSDESC sequence for `sym`: the
    /// specification's `TlsDescCall [sym]` (same implicit definitions) when
    /// x0 holds `ADD(ADRP sym, #:tlsdesc_lo12:sym)` and x1 holds the resolver
    /// read `LDR [ADRP sym, #:tlsdesc_lo12:sym]`; otherwise the instruction as
    /// it is (an effect no specification instruction matches).
    fn tlsdesc_call_event(
        &mut self,
        state: &State,
        id: InstId,
        inst: &MachInst,
    ) -> Result<Event, ExecStop> {
        use trust_cg_ir::aarch64_regs::{X0, X1};
        let [MachOperand::PReg(target), MachOperand::Symbol(sym)] = inst.operands.as_slice() else {
            return self.generic_event(state, id, inst);
        };
        let mut uses: Vec<PReg> = inst.implicit_uses.to_vec();
        uses.sort_unstable();
        uses.dedup();
        if target.encoding() != X1.encoding() || uses != [X0, X1] {
            return self.generic_event(state, id, inst);
        }
        let symbol_aux = |pos: u8| Aux::Sym(pos, sym.clone(), false);
        let adrp_key = self.arena.op_id(OpKey {
            tag: OpTag::Inst(AArch64Opcode::Adrp as u16),
            aux: vec![Aux::View(0, 64, false), symbol_aux(1)],
        });
        let page = self.arena.op_term(adrp_key, &[], 0, 64);
        let descriptor_key = |opcode: AArch64Opcode| OpKey {
            tag: OpTag::Inst(opcode as u16),
            aux: vec![
                Aux::View(0, 64, false),
                Aux::View(1, 64, false),
                symbol_aux(2),
            ],
        };
        let add_key = self
            .arena
            .op_id(descriptor_key(AArch64Opcode::AddTlsdescLo12));
        let ldr_key = self.arena.op_id(descriptor_key(AArch64Opcode::LdrTlsdesc));
        let descriptor = self.arena.op_term(add_key, &[page], 0, 64);
        let resolver = self.arena.op_term(ldr_key, &[page], 0, 64);
        let (Some(r0), Some(r1)) = (preg_reg(X0), preg_reg(X1)) else {
            return self.generic_event(state, id, inst);
        };
        let x0 = self.read_reg(state, r0);
        let x1 = self.read_reg(state, r1);
        if x0 != descriptor || x1 != resolver {
            return self.generic_event(state, id, inst);
        }
        let mut call = MachInst::new(
            AArch64Opcode::TlsDescCall,
            vec![MachOperand::Symbol(sym.clone())],
        );
        call.flags = inst.flags;
        call.implicit_defs = inst.implicit_defs;
        self.generic_event(state, id, &call)
    }

    /// A recorded trap expansion, judged as its carrier at the carrier's
    /// operands; every register the expansion writes is unknown after it.
    fn trap_expansion_event(
        &mut self,
        state: &State,
        id: InstId,
        record: usize,
        position: usize,
    ) -> Result<Event, ExecStop> {
        let func = self.ctx.func;
        let rec = &func.trap_expansions[record];
        if position != 0 {
            return unmodeled(
                func.inst(id),
                "a trap expansion entered past its first instruction",
            );
        }
        let carrier = &rec.carrier;
        let roles = Roles::of(carrier)?;
        let (args, outputs) = self.generic_io(state, carrier, roles)?;
        if !outputs.is_empty() {
            return unmodeled(carrier, "a trap carrier with register results");
        }
        let mut aux = self.operand_aux(carrier)?;
        let mut implicit: Vec<u16> = carrier.implicit_uses.iter().map(|p| p.encoding()).collect();
        implicit.sort_unstable();
        implicit.dedup();
        aux.extend(implicit.into_iter().map(Aux::Implicit));
        let key = self.arena.op_id(OpKey {
            tag: OpTag::Inst(carrier.opcode as u16),
            aux,
        });
        let mut junk_after = Vec::new();
        for &inst_id in &rec.insts {
            let inst = func.inst(inst_id);
            let roles = Roles::of(inst)?;
            for (pos, op) in inst.operands.iter().enumerate() {
                if roles.is_def(pos)
                    && let Some(Ok(Reg::View(view))) = operand_reg(op)
                {
                    junk_after.push(View {
                        bits: match view.place {
                            Place::Phys(l) => loc_bits(l),
                            Place::Virt(_) => view.bits,
                        },
                        ..view
                    });
                }
            }
            for p in inst.implicit_defs {
                if let Some(Reg::View(view)) = preg_reg(*p) {
                    junk_after.push(view);
                }
            }
            if may_clobber_nzcv(inst) || definitely_writes_flags(inst.opcode) {
                junk_after.push(View {
                    place: Place::Phys(LOC_NZCV),
                    bits: NZCV_BITS,
                    fpr: false,
                });
            }
        }
        Ok(Event {
            key,
            args,
            outputs: Vec::new(),
            flags_out: true,
            writebacks: Vec::new(),
            clobber: Clobber::None,
            store: None,
            opaque_write: true,
            junk_after,
            arg_widths: Vec::new(),
            inst: id,
            span: rec.insts.len(),
        })
    }

    /// Apply a matched effect: its outputs become the shared effect results
    /// `effect(block, ordinal)`; then its writebacks and clobbers.
    pub(crate) fn apply_event(&mut self, state: &mut State, event: &Event, ordinal: u32) {
        let block = self.block;
        if let Some((addr, bytes)) = event.store {
            let (base, offset) = self.arena.split_lin(addr);
            if matches!(self.arena.get(base), Term::Cfa | Term::Slot(_)) {
                Self::invalidate(state, base, offset, i64::from(bytes));
            }
        }
        if self.ctx.frame_storage.is_some() {
            self.note_write(state, event);
        }
        if event.clobber == Clobber::Call {
            self.apply_call_clobbers(state);
        }
        for (slot, view) in event.outputs.iter().enumerate() {
            let t = self.arena.ev(block, ordinal, slot as u16, view.bits);
            self.write(state, *view, t);
        }
        if event.flags_out && event.clobber == Clobber::None {
            let t = self.arena.ev(block, ordinal, 0xFFFF, NZCV_BITS);
            state.phys[LOC_NZCV as usize] = t;
        }
        for wb in &event.writebacks {
            self.write(state, wb.view, wb.value);
        }
        for (i, view) in event.junk_after.iter().enumerate() {
            let t = self.unknown(0x1000_0000_0000_0000 | i as u64, view.bits);
            self.write(state, *view, t);
        }
    }

    /// Lower `state.touched_low` for a matched effect's memory write: a
    /// program store at a known CFA offset touches that offset; one through
    /// an address the model cannot place, and every opaque effect, may
    /// touch anything the program can address, which (the AAPCS64 stack
    /// discipline: no pointer into the stack below SP outlives its
    /// allocation) reaches at most the red zone below the SP it runs at.
    fn note_write(&mut self, state: &mut State, event: &Event) {
        let placed = match event.store {
            Some((addr, _)) if !event.opaque_write => {
                let (base, offset) = self.arena.split_lin(addr);
                matches!(self.arena.get(base), Term::Cfa).then_some(offset)
            }
            None if !event.opaque_write => return,
            _ => None,
        };
        match placed {
            Some(offset) => state.touched_low = state.touched_low.min(offset),
            None => self.note_opaque_write(state),
        }
    }

    /// Lower `state.touched_low` for a write the model cannot place: to the
    /// red zone below the current SP (anywhere, when SP is not a known CFA
    /// offset).
    fn note_opaque_write(&mut self, state: &mut State) {
        let (base, sp) = self.arena.split_lin(state.phys[LOC_SP as usize]);
        let low = if matches!(self.arena.get(base), Term::Cfa) {
            sp.saturating_sub(RED_ZONE_BYTES)
        } else {
            i64::MIN
        };
        state.touched_low = state.touched_low.min(low);
    }

    /// The state on a call's exceptional edge: the call's clobbers, every
    /// result register unknown except X0 and X1, which hold the unwinder's
    /// exception values (the same in both functions); callee-saved
    /// registers and SP as at the call.
    pub(crate) fn apply_unwind(&mut self, state: &mut State, ordinal: u32) {
        if self.ctx.frame_storage.is_some() {
            self.note_opaque_write(state);
        }
        self.apply_call_clobbers(state);
        for loc in (2u16..8).chain(LOC_V0..LOC_V0 + 8) {
            let t = self.unknown(0x0800_0000_0000_0000 | u64::from(loc), loc_bits(loc));
            state.phys[loc as usize] = t;
        }
        for loc in 0u16..2 {
            let t = self.arena.ev(self.block, ordinal, 0x300 + loc, 64);
            state.phys[loc as usize] = t;
            state.written[loc as usize] = 64;
        }
    }

    /// AAPCS64/DarwinPCS call clobbers: X8-X18 and X30, V16-V31, the upper
    /// halves of V8-V15, NZCV, and every storage cell below SP (the callee's
    /// frame starts at the SP it is entered with). X0-X7/V0-V7 are written as
    /// results.
    fn apply_call_clobbers(&mut self, state: &mut State) {
        let (base, sp) = self.arena.split_lin(state.phys[LOC_SP as usize]);
        if matches!(self.arena.get(base), Term::Cfa) {
            state
                .cells
                .retain(|&(cell_base, start), _| cell_base != base || start >= sp);
        }
        // One unknown per register: two clobbered registers hold unrelated
        // values, so a compare of one with another decides nothing (a shared
        // term would make `CMP X9, X10` "equal").
        for loc in (8u16..=18).chain(std::iter::once(30)) {
            let t = self.unknown(0x0400_0000_0000_0000 | u64::from(loc), 64);
            state.phys[loc as usize] = t;
        }
        for n in 16u16..32 {
            let loc = LOC_V0 + n;
            let t = self.unknown(0x0400_0000_0000_0000 | u64::from(loc), 128);
            state.phys[loc as usize] = t;
        }
        for n in 8u16..16 {
            let loc = LOC_V0 + n;
            let low = self.arena.trunc(64, state.phys[loc as usize]);
            let t = self.arena.widen_keyed(
                low,
                128,
                self.ctx.side as u8,
                self.block,
                self.site,
                u64::from(loc),
            );
            state.phys[loc as usize] = t;
        }
        let flags = self.unknown(u64::from(LOC_NZCV), NZCV_BITS);
        state.phys[LOC_NZCV as usize] = flags;
    }
}

/// Every register place an instruction may write (explicit defs, writeback
/// bases, implicit defs, NZCV), for liveness and reserved-register checks.
pub(crate) fn inst_writes(inst: &MachInst, mut f: impl FnMut(Place)) {
    let (defs, _) = crate::post_ra_reaching_def::operand_role_masks(inst);
    for (pos, op) in inst.operands.iter().enumerate() {
        if pos >= 64 || defs & (1 << pos) == 0 {
            continue;
        }
        match op {
            MachOperand::MemOp { base, .. } => {
                if let Some(Reg::View(v)) = preg_reg(*base) {
                    f(v.place);
                }
            }
            _ => {
                if let Some(Ok(Reg::View(v))) = operand_reg(op) {
                    f(v.place);
                }
            }
        }
    }
    for p in inst.implicit_defs {
        if let Some(Reg::View(v)) = preg_reg(*p) {
            f(v.place);
        }
    }
    if definitely_writes_flags(inst.opcode) || may_clobber_nzcv(inst) {
        f(Place::Phys(LOC_NZCV));
    }
}

/// Every register place an instruction may read, for liveness.
pub(crate) fn inst_reads(inst: &MachInst, mut f: impl FnMut(Place)) {
    let (_, uses) = crate::post_ra_reaching_def::operand_role_masks(inst);
    for (pos, op) in inst.operands.iter().enumerate() {
        let is_use = pos >= 64 || uses & (1 << pos) != 0;
        match op {
            MachOperand::MemOp { base, .. } => {
                if let Some(Reg::View(v)) = preg_reg(*base) {
                    f(v.place);
                }
            }
            _ => {
                if is_use && let Some(Ok(Reg::View(v))) = operand_reg(op) {
                    f(v.place);
                }
            }
        }
    }
    for p in inst.implicit_uses {
        if let Some(Reg::View(v)) = preg_reg(*p) {
            f(v.place);
        }
    }
    if reads_nzcv(inst) {
        f(Place::Phys(LOC_NZCV));
    }
}
