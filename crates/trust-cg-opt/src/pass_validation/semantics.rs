// trust-cg-opt - Per-pass translation validation: instruction semantics
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Symbolic execution of one pre-allocation AArch64 machine instruction.
//!
//! Every non-branch instruction is executed by exactly one of three rules:
//!
//! 1. **Interpreted**: the integer ALU, move, extend, bitfield, select,
//!    compare and base-plus-immediate load/store opcodes listed in
//!    [`Exec::interpret`]. Their operand layouts are the encoder's
//!    (`trust-cg-codegen` `aarch64/encode.rs`); an instruction whose operands
//!    do not have the expected shape, that carries implicit registers, or
//!    whose flags add a call or side effect to its opcode's defaults falls
//!    through to rule 2 or 3 instead of being guessed.
//! 2. **Uninterpreted value**: an instruction with no memory access and no
//!    observable effect computes a deterministic function of its register
//!    inputs, immediates and (when it reads them) the flags. Its results are
//!    [`Term::Opaque`] keyed by all of those, so two instructions agree only
//!    when they are the same operation on the same inputs. A plain load is a
//!    value of the current world as well; it is recorded so the region check
//!    can refuse a load the output executes where the input did not.
//! 3. **Effect**: anything that may write memory, call, trap or otherwise be
//!    observed becomes a new world token ([`Term::Effect`]) over the old world
//!    and every input; its results are projections of that token.
//!
//! [`instruction_access`] is the read/write footprint of rule 2/3 (a
//! superset of what rule 1 reads, and exactly what every rule writes); the
//! region check's liveness is computed from it.
//!
//! [`Term::Opaque`]: super::term::Term::Opaque
//! [`Term::Effect`]: super::term::Term::Effect

use trust_cg_ir::regs::{CALL_CLOBBER_GPRS, CALLER_SAVED_FPRS};
use trust_cg_ir::{AArch64Opcode, InstFlags, MachInst, MachOperand, PReg, RegClass, SpecialReg};

use crate::effects::{
    aarch64_for_each_def_position, aarch64_for_each_use_position, may_clobber_nzcv, opcode_effect,
    reads_nzcv, writes_flags,
};
use crate::fast_hash::FxHashMap as HashMap;

use super::term::{Atom, Aux, FlagKind, LoadExt, Loc, Prim, TermArena, TermId};

/// Output slot of the flags result of an uninterpreted operation or effect.
const FLAGS_SLOT: u16 = 0xFFFF;
/// Output slots `CLOBBER_BASE + key` are register clobbers of an effect.
const CLOBBER_BASE: u16 = 0x8000;
/// Output slots `IMPLICIT_BASE + i` are implicit definitions of a value.
const IMPLICIT_BASE: u16 = 0x4000;

/// Why an instruction could not be executed symbolically.
#[derive(Debug, Clone)]
pub(crate) struct Unsupported(pub(crate) String);

/// Bank and view width of a register operand.
#[derive(Clone, Copy, Debug)]
struct View {
    loc: Loc,
    bits: u8,
    fpr: bool,
}

fn class_bits(class: RegClass) -> Option<(u8, bool)> {
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

/// Physical register encoding to (location, view width, bank). `None` for
/// the zero registers (read as zero, writes discarded) and unmodeled
/// encodings.
fn preg_view(p: PReg) -> Option<View> {
    let e = p.encoding();
    let v = |loc, bits, fpr| Some(View { loc, bits, fpr });
    match e {
        0..=30 => v(Loc::Gpr(e as u8), 64, false),
        31 => v(Loc::Sp, 64, false),
        32..=62 => v(Loc::Gpr((e - 32) as u8), 32, false),
        63 => v(Loc::Sp, 32, false),
        64..=95 => v(Loc::Fpr((e - 64) as u8), 128, true),
        96..=127 => v(Loc::Fpr((e - 96) as u8), 64, true),
        128..=159 => v(Loc::Fpr((e - 128) as u8), 32, true),
        162 => v(Loc::Flags, 64, false),
        163 | 164 => v(Loc::Sys(e), 64, false),
        165..=196 => v(Loc::Fpr((e - 165) as u8), 16, true),
        197..=228 => v(Loc::Fpr((e - 197) as u8), 8, true),
        _ => None,
    }
}

/// The location a physical register names (`None` for a zero register).
pub(crate) fn preg_loc(p: PReg) -> Option<Loc> {
    preg_view(p).map(|v| v.loc)
}

fn is_zero_preg(p: PReg) -> bool {
    matches!(p.encoding(), 160 | 161)
}

/// Location/view of a register operand; `Ok(None)` is a zero register.
fn operand_view(op: &MachOperand) -> Result<Option<View>, Unsupported> {
    match op {
        MachOperand::VReg(v) => {
            let (bits, fpr) = class_bits(v.class)
                .ok_or_else(|| Unsupported(format!("system-class vreg {v:?}")))?;
            Ok(Some(View {
                loc: Loc::VReg(v.id),
                bits,
                fpr,
            }))
        }
        MachOperand::PReg(p) if is_zero_preg(*p) => Ok(None),
        MachOperand::PReg(p) => preg_view(*p)
            .map(Some)
            .ok_or_else(|| Unsupported(format!("physical register {p:?}"))),
        MachOperand::Special(SpecialReg::SP) => Ok(Some(View {
            loc: Loc::Sp,
            bits: 64,
            fpr: false,
        })),
        MachOperand::Special(SpecialReg::XZR | SpecialReg::WZR) => Ok(None),
        other => Err(Unsupported(format!("not a register operand: {other:?}"))),
    }
}

fn is_register(op: &MachOperand) -> bool {
    matches!(
        op,
        MachOperand::VReg(_) | MachOperand::PReg(_) | MachOperand::Special(_)
    )
}

/// Byte width of a load/store transfer register.
fn transfer_bytes(op: &MachOperand) -> Option<u8> {
    let bits = match op {
        MachOperand::VReg(v) => class_bits(v.class)?.0,
        MachOperand::PReg(p) if is_zero_preg(*p) => {
            if p.encoding() == 160 {
                64
            } else {
                32
            }
        }
        MachOperand::PReg(p) => preg_view(*p)?.bits,
        MachOperand::Special(SpecialReg::XZR) => 64,
        MachOperand::Special(SpecialReg::WZR) => 32,
        _ => return None,
    };
    Some(bits / 8)
}

/// Byte width of a scalar base-plus-immediate access's transfer.
fn access_bytes(opcode: AArch64Opcode, data: &MachOperand) -> Option<u8> {
    use AArch64Opcode::*;
    match opcode {
        LdrbRI | LdrsbRI | StrbRI => Some(1),
        LdrhRI | LdrshRI | StrhRI => Some(2),
        _ => transfer_bytes(data),
    }
}

/// The base operand, immediate byte offset and byte width of a plain
/// base-plus-immediate access (`LDR`/`STR`, their byte and half forms, and
/// `LDP`/`STP` of two equal-width registers), read as the symbolic
/// semantics reads it. `None` for any other instruction or operand shape.
pub(super) fn base_offset_access(inst: &MachInst) -> Option<(&MachOperand, i64, u64)> {
    use AArch64Opcode::*;
    match (inst.opcode, inst.operands.as_slice()) {
        (
            LdrRI | LdrbRI | LdrhRI | LdrsbRI | LdrshRI | StrRI | StrbRI | StrhRI,
            [data, base, MachOperand::Imm(offset)],
        ) => Some((base, *offset, u64::from(access_bytes(inst.opcode, data)?))),
        (LdpRI | StpRI, [first, second, base, MachOperand::Imm(offset)]) => {
            let bytes = transfer_bytes(first)?;
            (transfer_bytes(second)? == bytes && matches!(bytes, 4 | 8 | 16)).then_some((
                base,
                *offset,
                2 * u64::from(bytes),
            ))
        }
        _ => None,
    }
}

fn imm(op: Option<&MachOperand>) -> Option<i64> {
    op.and_then(MachOperand::as_imm)
}

/// The non-register identity of an operand (for uninterpreted keys).
fn aux_of(pos: usize, op: &MachOperand) -> Aux {
    match op {
        MachOperand::Imm(v) => Aux::Imm(*v),
        MachOperand::FImm(f) => Aux::FImm(f.to_bits()),
        MachOperand::Block(b) => Aux::Block(b.0),
        MachOperand::JumpTableIndex(i) => Aux::JumpTable(*i),
        MachOperand::MemOp { offset, .. } => Aux::MemOffset(*offset),
        _ => Aux::Reg(pos as u8),
    }
}

fn is_call(inst: &MachInst) -> bool {
    inst.flags
        .union(inst.opcode.default_flags())
        .contains(InstFlags::IS_CALL)
        || matches!(
            inst.opcode,
            AArch64Opcode::Bl | AArch64Opcode::Blr | AArch64Opcode::BL | AArch64Opcode::BLR
        )
}

fn def_and_use_masks(inst: &MachInst) -> (u64, u64) {
    let mut def_mask = 0u64;
    aarch64_for_each_def_position(inst.opcode, inst.operands.len(), |pos| {
        if pos < 64 {
            def_mask |= 1 << pos;
        }
    });
    let mut use_mask = 0u64;
    aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |pos| {
        if pos < 64 {
            use_mask |= 1 << pos;
        }
    });
    (def_mask, use_mask)
}

/// Visit the locations `inst` may read (`write == false`) and the locations
/// it writes (`write == true`), as rules 2 and 3 model it: reads are the
/// register operands outside pure-definition positions, `MemOp` bases,
/// implicit uses, NZCV for a flag reader and the stack pointer for a call;
/// writes are the register operands in definition positions, implicit
/// definitions, a call's caller-saved registers and NZCV for anything that
/// may clobber it. A location may be visited more than once.
pub(crate) fn for_each_access(inst: &MachInst, mut f: impl FnMut(Loc, bool)) {
    let (def_mask, use_mask) = def_and_use_masks(inst);
    for (pos, op) in inst.operands.iter().enumerate() {
        let bit = if pos < 64 { 1u64 << pos } else { 0 };
        let is_def = def_mask & bit != 0;
        let pure_def = is_def && use_mask & bit == 0;
        match op {
            MachOperand::MemOp { base, .. } => {
                if let Some(loc) = preg_loc(*base) {
                    f(loc, false);
                }
            }
            op if is_register(op) => {
                if let Ok(Some(view)) = operand_view(op) {
                    if is_def {
                        f(view.loc, true);
                    }
                    if !pure_def {
                        f(view.loc, false);
                    }
                }
            }
            _ => {}
        }
    }
    for &p in inst.implicit_uses {
        if let Some(loc) = preg_loc(p) {
            f(loc, false);
        }
    }
    for &p in inst.implicit_defs {
        if let Some(loc) = preg_loc(p) {
            f(loc, true);
        }
    }
    let call = is_call(inst);
    if call {
        f(Loc::Sp, false);
        for p in CALL_CLOBBER_GPRS.iter().chain(CALLER_SAVED_FPRS.iter()) {
            if let Some(loc) = preg_loc(*p) {
                f(loc, true);
            }
        }
    }
    if reads_nzcv(inst) {
        f(Loc::Flags, false);
    }
    if may_clobber_nzcv(inst) || call {
        f(Loc::Flags, true);
    }
}

/// [`for_each_access`] collected: `(reads, writes)`, each without
/// duplicates.
pub(crate) fn instruction_access(inst: &MachInst) -> (Vec<Loc>, Vec<Loc>) {
    let mut reads = Vec::new();
    let mut writes = Vec::new();
    for_each_access(inst, |loc, write| {
        let list = if write { &mut writes } else { &mut reads };
        if !list.contains(&loc) {
            list.push(loc);
        }
    });
    (reads, writes)
}

/// The value of one location along one symbolic path.
#[derive(Clone, Copy, Debug)]
struct Value {
    term: TermId,
}

/// Symbolic machine state along one path through a region.
#[derive(Clone)]
pub(crate) struct State {
    /// Block the path started from (names the input atoms).
    origin: u32,
    vals: HashMap<Loc, Value>,
    /// Memory plus the effect history.
    pub(crate) world: TermId,
    /// Plain loads executed on this path, in order.
    pub(crate) loads: Vec<TermId>,
}

impl State {
    pub(crate) fn new(arena: &mut TermArena, origin: u32) -> Self {
        let world = arena.atom(
            Atom::Input {
                block: origin,
                loc: Loc::World,
                fpr: false,
            },
            None,
        );
        Self {
            origin,
            vals: HashMap::default(),
            world,
            loads: Vec::new(),
        }
    }

    /// The input atom for `loc` read through bank `fpr` (its value on entry
    /// to the path's origin block).
    fn input(&self, arena: &mut TermArena, loc: Loc, fpr: bool) -> TermId {
        let clean = if fpr {
            None
        } else {
            match loc {
                Loc::VReg(_) | Loc::Gpr(_) | Loc::Sp | Loc::Sys(_) => Some(64),
                Loc::Fpr(_) | Loc::Flags | Loc::World => None,
            }
        };
        arena.atom(
            Atom::Input {
                block: self.origin,
                loc,
                fpr,
            },
            clean,
        )
    }

    fn read_view(&self, arena: &mut TermArena, view: View) -> TermId {
        let term = match self.vals.get(&view.loc) {
            Some(v) => v.term,
            None => self.input(arena, view.loc, view.fpr),
        };
        arena.zext(term, view.bits)
    }

    fn write_view(&mut self, arena: &mut TermArena, view: View, term: TermId) {
        let term = arena.zext(term, view.bits);
        self.vals.insert(view.loc, Value { term });
    }

    /// Value of `loc` as the path leaves it. An unassigned location is its
    /// input atom; `fpr` picks the bank an unassigned virtual register is
    /// named in (it must be the same for both functions compared).
    pub(crate) fn final_value(&self, arena: &mut TermArena, loc: Loc, fpr: bool) -> TermId {
        if loc == Loc::World {
            return self.world;
        }
        if let Some(v) = self.vals.get(&loc) {
            return v.term;
        }
        let fpr = match loc {
            Loc::Fpr(_) => true,
            Loc::VReg(_) => fpr,
            _ => false,
        };
        self.input(arena, loc, fpr)
    }

    fn flags(&self, arena: &mut TermArena) -> TermId {
        match self.vals.get(&Loc::Flags) {
            Some(v) => v.term,
            None => self.input(arena, Loc::Flags, false),
        }
    }

    fn set_flags(&mut self, term: TermId) {
        self.vals.insert(Loc::Flags, Value { term });
    }
}

/// Executes instructions against a [`State`].
pub(crate) struct Exec<'a> {
    arena: &'a mut TermArena,
    state: &'a mut State,
}

impl<'a> Exec<'a> {
    pub(crate) fn new(arena: &'a mut TermArena, state: &'a mut State) -> Self {
        Self { arena, state }
    }

    fn read(&mut self, op: &MachOperand) -> Result<TermId, Unsupported> {
        match operand_view(op)? {
            Some(view) => Ok(self.state.read_view(self.arena, view)),
            None => Ok(self.arena.konst(0)),
        }
    }

    fn write(&mut self, op: &MachOperand, term: TermId) -> Result<(), Unsupported> {
        if let Some(view) = operand_view(op)? {
            self.state.write_view(self.arena, view, term);
        }
        Ok(())
    }

    /// Value of an operand used as an address base.
    fn address_base(&mut self, op: &MachOperand) -> Result<TermId, Unsupported> {
        Ok(match op {
            MachOperand::StackSlot(s) => self.arena.atom(Atom::Slot(s.0), Some(64)),
            MachOperand::FrameIndex(f) => self.arena.atom(Atom::FrameIndex(f.0), Some(64)),
            MachOperand::IncomingArg(o) => self.arena.atom(Atom::IncomingArg(*o), Some(64)),
            MachOperand::MemOp { base, offset } => {
                let b = self.read(&MachOperand::PReg(*base))?;
                self.arena.add_const(64, b, *offset as u64)
            }
            other => {
                let b = self.read(other)?;
                self.arena.zext(b, 64)
            }
        })
    }

    /// Width of the integer operation defined by `op` (a GPR destination).
    fn gpr_width(op: Option<&MachOperand>) -> Option<u8> {
        match op? {
            MachOperand::VReg(v) => match v.class {
                RegClass::Gpr64 => Some(64),
                RegClass::Gpr32 => Some(32),
                _ => None,
            },
            MachOperand::PReg(p) => match p.encoding() {
                0..=30 | 160 => Some(64),
                32..=62 | 161 => Some(32),
                _ => None,
            },
            MachOperand::Special(SpecialReg::XZR) => Some(64),
            MachOperand::Special(SpecialReg::WZR) => Some(32),
            _ => None,
        }
    }

    /// Execute a non-branch instruction. Branches and returns are the region
    /// checker's ([`Self::branch_condition`], [`Self::return_effect`]).
    pub(crate) fn step(&mut self, inst: &MachInst) -> Result<(), Unsupported> {
        if matches!(inst.opcode, AArch64Opcode::Nop | AArch64Opcode::AlignNop) {
            return Ok(());
        }
        if inst.opcode == AArch64Opcode::Phi {
            return Err(Unsupported("phi".to_string()));
        }
        if self.interpret(inst)? {
            return Ok(());
        }
        self.generic(inst)
    }

    /// The condition under which a conditional branch is taken.
    pub(crate) fn branch_condition(&mut self, inst: &MachInst) -> Result<TermId, Unsupported> {
        let flags = self.state.flags(self.arena);
        let state = &mut *self.state;
        super::region::branch_condition_term(self.arena, inst, flags, &mut |arena, op| {
            match operand_view(op)? {
                Some(view) => Ok(state.read_view(arena, view)),
                None => Ok(arena.konst(0)),
            }
        })
    }

    /// The world after a return: an effect over every operand, implicit use
    /// and `preserved` location.
    pub(crate) fn return_effect(
        &mut self,
        inst: &MachInst,
        preserved: &[Loc],
    ) -> Result<TermId, Unsupported> {
        let mut aux = Vec::new();
        let mut args = Vec::new();
        for (pos, op) in inst.operands.iter().enumerate() {
            aux.push(aux_of(pos, op));
            if is_register(op) {
                let v = self.read(op)?;
                args.push(v);
            } else if let MachOperand::Symbol(name) | MachOperand::ExactModuleSymbol(name) = op {
                let exact = matches!(op, MachOperand::ExactModuleSymbol(_));
                let v = self.arena.atom(
                    Atom::Symbol {
                        name: name.clone(),
                        exact,
                    },
                    Some(64),
                );
                args.push(v);
            }
        }
        aux.push(Aux::Implicit(
            inst.implicit_uses.iter().map(|p| p.encoding()).collect(),
        ));
        for &p in inst.implicit_uses {
            let v = self.read(&MachOperand::PReg(p))?;
            args.push(v);
        }
        for &loc in preserved {
            let fpr = matches!(loc, Loc::Fpr(_));
            let v = self.state.final_value(self.arena, loc, fpr);
            args.push(v);
        }
        aux.push(Aux::Flags(flags_key(
            inst.flags.union(inst.opcode.default_flags()),
        )));
        let world = self
            .arena
            .effect(self.state.world, inst.opcode as u16, aux, args);
        self.state.world = world;
        Ok(world)
    }

    /// Rule 1. Returns `Ok(false)` when the opcode or its operand shape is
    /// not one this table models, so the generic rules apply.
    fn interpret(&mut self, inst: &MachInst) -> Result<bool, Unsupported> {
        use AArch64Opcode::*;
        // Implicit registers, flags that add a call or side effect to the
        // opcode's defaults, or a possible NZCV clobber this table does not
        // write, all leave the instruction to the generic rules.
        let added = InstFlags::from_bits(inst.flags.bits() & !inst.opcode.default_flags().bits());
        if !inst.implicit_defs.is_empty()
            || !inst.implicit_uses.is_empty()
            || !added
                .intersection(InstFlags::HAS_SIDE_EFFECTS.union(InstFlags::IS_CALL))
                .is_empty()
            || (may_clobber_nzcv(inst) && !writes_flags(inst.opcode))
        {
            return Ok(false);
        }
        let ops = &inst.operands;
        let n = ops.len();
        let reg = |i: usize| ops.get(i).filter(|o| is_register(o));
        macro_rules! need {
            ($cond:expr) => {
                if !$cond {
                    return Ok(false);
                }
            };
        }
        match inst.opcode {
            AddRR | SubRR | MulRR | AndRR | OrrRR | EorRR | OrnRR | BicRR | LslRR | LsrRR
            | AsrRR | SDiv | UDiv => {
                need!(n == 3 && reg(0).is_some() && reg(1).is_some() && reg(2).is_some());
                let Some(w) = Self::gpr_width(ops.first()) else {
                    return Ok(false);
                };
                let a = self.read(&ops[1])?;
                let b = self.read(&ops[2])?;
                let r = match inst.opcode {
                    AddRR => self.arena.add(w, a, b),
                    SubRR => self.arena.sub(w, a, b),
                    MulRR => self.arena.mul(w, a, b),
                    AndRR => self.arena.and(w, a, b),
                    OrrRR => self.arena.or(w, a, b),
                    EorRR => self.arena.xor(w, a, b),
                    OrnRR => {
                        let nb = self.arena.not(w, b);
                        self.arena.or(w, a, nb)
                    }
                    BicRR => {
                        let nb = self.arena.not(w, b);
                        self.arena.and(w, a, nb)
                    }
                    LslRR => self.arena.binop(Prim::Lslv, w, a, b),
                    LsrRR => self.arena.binop(Prim::Lsrv, w, a, b),
                    AsrRR => self.arena.binop(Prim::Asrv, w, a, b),
                    SDiv => self.arena.binop(Prim::Sdiv, w, a, b),
                    _ => self.arena.binop(Prim::Udiv, w, a, b),
                };
                self.write(&ops[0], r)?;
            }
            Umulh | Smulh => {
                need!(n == 3 && reg(1).is_some() && reg(2).is_some());
                need!(Self::gpr_width(ops.first()) == Some(64));
                let a = self.read(&ops[1])?;
                let b = self.read(&ops[2])?;
                let op = if inst.opcode == Umulh {
                    Prim::Umulh
                } else {
                    Prim::Smulh
                };
                let r = self.arena.binop(op, 64, a, b);
                self.write(&ops[0], r)?;
            }
            AddRI | SubRI | AddRIShift12 | AndRI | OrrRI | EorRI => {
                need!(n == 3 && reg(0).is_some() && reg(1).is_some());
                let Some(k) = imm(ops.get(2)) else {
                    return Ok(false);
                };
                let Some(w) = Self::gpr_width(ops.first()) else {
                    return Ok(false);
                };
                // `ADD/SUB` with SP as source or destination is the
                // extended form; the immediate semantics are the same.
                let a = self.read(&ops[1])?;
                let r = match inst.opcode {
                    AddRI => self.arena.add_const(w, a, k as u64),
                    SubRI => self.arena.add_const(w, a, (k as u64).wrapping_neg()),
                    AddRIShift12 => {
                        need!((0..=4095).contains(&k));
                        self.arena.add_const(w, a, (k as u64) << 12)
                    }
                    _ => {
                        let kt = self.arena.konst(k as u64);
                        match inst.opcode {
                            AndRI => self.arena.and(w, a, kt),
                            OrrRI => self.arena.or(w, a, kt),
                            _ => self.arena.xor(w, a, kt),
                        }
                    }
                };
                self.write(&ops[0], r)?;
            }
            Neg => {
                need!(n == 2 && reg(1).is_some());
                let Some(w) = Self::gpr_width(ops.first()) else {
                    return Ok(false);
                };
                let a = self.read(&ops[1])?;
                let r = self.arena.neg(w, a);
                self.write(&ops[0], r)?;
            }
            Madd | Msub => {
                need!(reg(1).is_some() && reg(2).is_some());
                let Some(w) = Self::gpr_width(ops.first()) else {
                    return Ok(false);
                };
                let c = match (inst.opcode, n) {
                    (_, 4) => {
                        need!(reg(3).is_some());
                        self.read(&ops[3])?
                    }
                    // `MSUB d, n, m` with the addend omitted encodes XZR
                    // (`MNEG`).
                    (Msub, 3) => self.arena.konst(0),
                    _ => return Ok(false),
                };
                let a = self.read(&ops[1])?;
                let b = self.read(&ops[2])?;
                let p = self.arena.mul(w, a, b);
                let r = if inst.opcode == Madd {
                    self.arena.add(w, c, p)
                } else {
                    self.arena.sub(w, c, p)
                };
                self.write(&ops[0], r)?;
            }
            Smull | Umull => {
                need!(n == 3 && reg(1).is_some() && reg(2).is_some());
                let a = self.read(&ops[1])?;
                let b = self.read(&ops[2])?;
                let (a, b) = if inst.opcode == Smull {
                    (self.arena.sext(64, a, 32), self.arena.sext(64, b, 32))
                } else {
                    (self.arena.zext(a, 32), self.arena.zext(b, 32))
                };
                let r = self.arena.mul(64, a, b);
                self.write(&ops[0], r)?;
            }
            EorRRShift | EorRRLsl | EorRRLsr | AddRRShift | SubRRShift | AddRRShiftLsr => {
                need!(n == 4 && reg(1).is_some() && reg(2).is_some());
                let Some(w) = Self::gpr_width(ops.first()) else {
                    return Ok(false);
                };
                let Some(k) = imm(ops.get(3)) else {
                    return Ok(false);
                };
                // The encoder refuses amounts outside [1, width).
                need!(k >= 1 && k < i64::from(w));
                let a = self.read(&ops[1])?;
                let b = self.read(&ops[2])?;
                let k = k as u32;
                let shifted = match inst.opcode {
                    EorRRShift => self.arena.shift_const(Prim::Ror, w, b, k),
                    EorRRLsr | AddRRShiftLsr => self.arena.shift_const(Prim::Lshr, w, b, k),
                    _ => self.arena.shl(w, b, k),
                };
                let r = match inst.opcode {
                    EorRRShift | EorRRLsl | EorRRLsr => self.arena.xor(w, a, shifted),
                    SubRRShift => self.arena.sub(w, a, shifted),
                    _ => self.arena.add(w, a, shifted),
                };
                self.write(&ops[0], r)?;
            }
            LslRI | LsrRI | AsrRI | RorRI => {
                need!(n == 3 && reg(1).is_some());
                let Some(w) = Self::gpr_width(ops.first()) else {
                    return Ok(false);
                };
                let Some(k) = imm(ops.get(2)) else {
                    return Ok(false);
                };
                need!(k >= 0 && k < i64::from(w));
                let a = self.read(&ops[1])?;
                let k = k as u32;
                let r = match inst.opcode {
                    LslRI => {
                        if k == 0 {
                            self.arena.zext(a, w)
                        } else {
                            self.arena.shl(w, a, k)
                        }
                    }
                    LsrRI => self.arena.shift_const(Prim::Lshr, w, a, k),
                    AsrRI => self.arena.shift_const(Prim::Ashr, w, a, k),
                    _ => self.arena.shift_const(Prim::Ror, w, a, k),
                };
                self.write(&ops[0], r)?;
            }
            MovR | Copy | MOVWrr | MOVXrr => {
                need!(n == 2 && reg(0).is_some() && reg(1).is_some());
                let a = self.read(&ops[1])?;
                self.write(&ops[0], a)?;
            }
            MovI => {
                need!(n == 2);
                let Some(w) = Self::gpr_width(ops.first()) else {
                    return Ok(false);
                };
                let Some(k) = imm(ops.get(1)) else {
                    return Ok(false);
                };
                // The encoder emits `MovI` as a single MOVZ of a 16-bit field.
                need!((0..=0xFFFF).contains(&k));
                let _ = w;
                let r = self.arena.konst(k as u64);
                self.write(&ops[0], r)?;
            }
            Movz | Movn | Movk | MOVZWi | MOVZXi => {
                need!(n == 2 || n == 3);
                let Some(w) = Self::gpr_width(ops.first()) else {
                    return Ok(false);
                };
                let Some(k) = imm(ops.get(1)) else {
                    return Ok(false);
                };
                need!((0..=0xFFFF).contains(&k));
                let shift = if n == 3 {
                    let Some(s) = imm(ops.get(2)) else {
                        return Ok(false);
                    };
                    s
                } else {
                    0
                };
                need!(shift >= 0 && shift % 16 == 0 && shift < i64::from(w));
                let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
                let placed = (k as u64) << shift;
                let r = match inst.opcode {
                    Movn => self.arena.konst(!placed & mask),
                    Movk => {
                        let old = self.read(&ops[0])?;
                        let keep = self.arena.konst(!(0xFFFFu64 << shift) & mask);
                        let kept = self.arena.and(w, old, keep);
                        let new = self.arena.konst(placed & mask);
                        self.arena.or(w, kept, new)
                    }
                    _ => self.arena.konst(placed & mask),
                };
                self.write(&ops[0], r)?;
            }
            Sxtw | Sxtb | Sxth | Uxtb | Uxth | Uxtw => {
                need!(n == 2 && reg(1).is_some());
                let Some(w) = Self::gpr_width(ops.first()) else {
                    return Ok(false);
                };
                let a = self.read(&ops[1])?;
                let r = match inst.opcode {
                    Sxtw => self.arena.sext(w, a, 32),
                    Sxtb => self.arena.sext(w, a, 8),
                    Sxth => self.arena.sext(w, a, 16),
                    Uxtb => self.arena.zext(a, 8),
                    Uxth => self.arena.zext(a, 16),
                    _ => self.arena.zext(a, 32),
                };
                self.write(&ops[0], r)?;
            }
            Ubfm | Sbfm => {
                need!(n == 4 && reg(1).is_some());
                let Some(w) = Self::gpr_width(ops.first()) else {
                    return Ok(false);
                };
                let (Some(immr), Some(imms)) = (imm(ops.get(2)), imm(ops.get(3))) else {
                    return Ok(false);
                };
                need!((0..i64::from(w)).contains(&immr) && (0..i64::from(w)).contains(&imms));
                let (immr, imms) = (immr as u32, imms as u32);
                let a = self.read(&ops[1])?;
                let r = if imms >= immr {
                    // Extract `imms - immr + 1` bits starting at `immr`.
                    let field = (imms - immr + 1) as u8;
                    let shifted = self.arena.shift_const(Prim::Lshr, w, a, immr);
                    if inst.opcode == Ubfm {
                        self.arena.zext(shifted, field)
                    } else {
                        self.arena.sext(w, shifted, field)
                    }
                } else {
                    // Insert the low `imms + 1` bits at `width - immr`.
                    let field = (imms + 1) as u8;
                    let low = if inst.opcode == Ubfm {
                        self.arena.zext(a, field)
                    } else {
                        self.arena.sext(w, a, field)
                    };
                    self.arena.shl(w, low, u32::from(w) - immr)
                };
                self.write(&ops[0], r)?;
            }
            Csel | Csinc | Csinv | Csneg => {
                need!(n == 4 && reg(1).is_some() && reg(2).is_some());
                let Some(w) = Self::gpr_width(ops.first()) else {
                    return Ok(false);
                };
                let Some(cc) = imm(ops.get(3)) else {
                    return Ok(false);
                };
                need!((0..=15).contains(&cc));
                let flags = self.state.flags(self.arena);
                let c = self.arena.cond(cc as u8, flags);
                let a = self.read(&ops[1])?;
                let a = self.arena.zext(a, w);
                let b = self.read(&ops[2])?;
                let other = match inst.opcode {
                    Csel => self.arena.zext(b, w),
                    Csinc => self.arena.add_const(w, b, 1),
                    Csinv => self.arena.not(w, b),
                    _ => self.arena.neg(w, b),
                };
                let r = self.arena.ite(c, a, other);
                self.write(&ops[0], r)?;
            }
            CSet => {
                need!(n == 2);
                need!(Self::gpr_width(ops.first()).is_some());
                let Some(cc) = imm(ops.get(1)) else {
                    return Ok(false);
                };
                // The encoder emits CSINC with the inverted code, which is
                // only an alias for the codes below AL.
                need!((0..=13).contains(&cc));
                let flags = self.state.flags(self.arena);
                let c = self.arena.cond(cc as u8, flags);
                let one = self.arena.konst(1);
                let zero = self.arena.konst(0);
                let r = self.arena.ite(c, one, zero);
                self.write(&ops[0], r)?;
            }
            CmpRR | CMPWrr | CMPXrr | CmpRI | CMPWri | CMPXri | Tst => {
                need!(n == 2 && reg(0).is_some());
                let Some(w) = Self::gpr_width(ops.first()) else {
                    return Ok(false);
                };
                // A shifted or extended register form is not this shape.
                let a = self.read(&ops[0])?;
                let b = match &ops[1] {
                    MachOperand::Imm(k) => self.arena.konst(*k as u64),
                    op if is_register(op) => {
                        need!(Self::gpr_width(Some(op)) == Some(w));
                        self.read(op)?
                    }
                    _ => return Ok(false),
                };
                let kind = if inst.opcode == Tst {
                    FlagKind::And
                } else {
                    FlagKind::Sub
                };
                let f = self.arena.flags(kind, w, a, b);
                self.state.set_flags(f);
            }
            AddsRR | AddsRI | SubsRR | SubsRI => {
                need!(n == 3 && reg(1).is_some());
                // SUBS with an SP operand uses the extended-register form.
                need!(!matches!(ops[1], MachOperand::Special(SpecialReg::SP)));
                let Some(w) = Self::gpr_width(ops.first()) else {
                    return Ok(false);
                };
                let a = self.read(&ops[1])?;
                let b = match &ops[2] {
                    MachOperand::Imm(k) => self.arena.konst(*k as u64),
                    op if is_register(op) => self.read(op)?,
                    _ => return Ok(false),
                };
                let (r, kind) = if matches!(inst.opcode, AddsRR | AddsRI) {
                    (self.arena.add(w, a, b), FlagKind::Add)
                } else {
                    (self.arena.sub(w, a, b), FlagKind::Sub)
                };
                let f = self.arena.flags(kind, w, a, b);
                self.write(&ops[0], r)?;
                self.state.set_flags(f);
            }
            AddPCRel => {
                // `AddPCRel d, SP, StackSlot(s)` materializes a slot address.
                need!(n == 3);
                let sp = matches!(ops[1], MachOperand::Special(SpecialReg::SP))
                    || matches!(ops[1], MachOperand::PReg(p) if p.encoding() == 31);
                need!(sp);
                let MachOperand::StackSlot(s) = ops[2] else {
                    return Ok(false);
                };
                let r = self.arena.atom(Atom::Slot(s.0), Some(64));
                self.write(&ops[0], r)?;
            }
            LdrRI | LdrbRI | LdrhRI | LdrsbRI | LdrshRI | StrRI | StrbRI | StrhRI => {
                need!(n == 2 || n == 3);
                need!(reg(0).is_some());
                if n == 2 {
                    need!(matches!(ops[1], MachOperand::MemOp { .. }));
                }
                let base = self.address_base(&ops[1])?;
                let offset = if n == 3 {
                    match imm(ops.get(2)) {
                        Some(k) => k,
                        None => return Ok(false),
                    }
                } else {
                    0
                };
                let addr = self.arena.add_const(64, base, offset as u64);
                return self.scalar_memory(inst.opcode, &ops[0], addr);
            }
            LdpRI | StpRI => {
                need!(n == 4 && reg(0).is_some() && reg(1).is_some());
                let Some(offset) = imm(ops.get(3)) else {
                    return Ok(false);
                };
                let (Some(b0), Some(b1)) = (transfer_bytes(&ops[0]), transfer_bytes(&ops[1]))
                else {
                    return Ok(false);
                };
                need!(b0 == b1 && matches!(b0, 4 | 8 | 16));
                let base = self.address_base(&ops[2])?;
                let a0 = self.arena.add_const(64, base, offset as u64);
                let a1 = self.arena.add_const(64, a0, u64::from(b0));
                if inst.opcode == LdpRI {
                    let w = b0 * 8;
                    let v0 = self.arena.load(self.state.world, a0, b0, LoadExt::Zero, w);
                    let v1 = self.arena.load(self.state.world, a1, b0, LoadExt::Zero, w);
                    self.record_load(v0);
                    self.record_load(v1);
                    self.write(&ops[0], v0)?;
                    self.write(&ops[1], v1)?;
                } else {
                    let v0 = self.read(&ops[0])?;
                    let v1 = self.read(&ops[1])?;
                    let w = self.arena.store(self.state.world, a0, v0, b0);
                    self.state.world = self.arena.store(w, a1, v1, b0);
                }
            }
            _ => return Ok(false),
        }
        Ok(true)
    }

    fn record_load(&mut self, value: TermId) {
        // A forwarded load folded to the stored value reads no memory.
        if matches!(self.arena.get(value), super::term::Term::Load { .. }) {
            self.state.loads.push(value);
        }
    }

    /// A plain base+offset scalar load or store. `Ok(false)` leaves an
    /// unmodeled transfer width to the generic rules.
    fn scalar_memory(
        &mut self,
        opcode: AArch64Opcode,
        data: &MachOperand,
        addr: TermId,
    ) -> Result<bool, Unsupported> {
        use AArch64Opcode::*;
        let Some(bytes) = access_bytes(opcode, data) else {
            return Ok(false);
        };
        let is_load = matches!(opcode, LdrRI | LdrbRI | LdrhRI | LdrsbRI | LdrshRI);
        if is_load {
            let Some(view) = operand_view(data)? else {
                return Ok(false);
            };
            let width = view.bits;
            let ext = match opcode {
                LdrsbRI | LdrshRI => {
                    if width == 64 {
                        LoadExt::Sign64
                    } else {
                        LoadExt::Sign32
                    }
                }
                _ => LoadExt::Zero,
            };
            let v = self.arena.load(self.state.world, addr, bytes, ext, width);
            self.record_load(v);
            self.write(data, v)?;
        } else {
            let v = self.read(data)?;
            self.state.world = self.arena.store(self.state.world, addr, v, bytes);
        }
        Ok(true)
    }

    /// Rules 2 and 3.
    fn generic(&mut self, inst: &MachInst) -> Result<(), Unsupported> {
        let opcode = inst.opcode as u16;
        let ops = &inst.operands;
        let (def_mask, use_mask) = def_and_use_masks(inst);

        let mut aux = Vec::with_capacity(ops.len() + 3);
        let mut args = Vec::with_capacity(ops.len() + 2);
        let mut outputs: Vec<(usize, View)> = Vec::new();
        for (pos, op) in ops.iter().enumerate() {
            let bit = if pos < 64 { 1u64 << pos } else { 0 };
            let is_def = def_mask & bit != 0;
            let pure_def = is_def && use_mask & bit == 0;
            if is_register(op) {
                if is_def && let Some(view) = operand_view(op)? {
                    outputs.push((pos, view));
                    aux.push(Aux::Class(view.bits));
                }
                if !pure_def {
                    aux.push(Aux::Reg(pos as u8));
                    let v = self.read(op)?;
                    args.push(v);
                }
            } else {
                match op {
                    MachOperand::MemOp { base, .. } => {
                        aux.push(aux_of(pos, op));
                        let v = self.read(&MachOperand::PReg(*base))?;
                        args.push(v);
                    }
                    MachOperand::StackSlot(_)
                    | MachOperand::FrameIndex(_)
                    | MachOperand::IncomingArg(_) => {
                        aux.push(Aux::Reg(pos as u8));
                        let v = self.address_base(op)?;
                        args.push(v);
                    }
                    MachOperand::Symbol(name) | MachOperand::ExactModuleSymbol(name) => {
                        aux.push(Aux::Reg(pos as u8));
                        let exact = matches!(op, MachOperand::ExactModuleSymbol(_));
                        let v = self.arena.atom(
                            Atom::Symbol {
                                name: name.clone(),
                                exact,
                            },
                            Some(64),
                        );
                        args.push(v);
                    }
                    _ => aux.push(aux_of(pos, op)),
                }
            }
        }
        if !inst.implicit_uses.is_empty() {
            aux.push(Aux::Implicit(
                inst.implicit_uses.iter().map(|p| p.encoding()).collect(),
            ));
            for &p in inst.implicit_uses {
                let v = self.read(&MachOperand::PReg(p))?;
                args.push(v);
            }
        }
        if !inst.implicit_defs.is_empty() {
            aux.push(Aux::Implicit(
                inst.implicit_defs.iter().map(|p| p.encoding()).collect(),
            ));
        }
        let flags = inst.flags.union(inst.opcode.default_flags());
        aux.push(Aux::Flags(flags_key(flags)));
        if reads_nzcv(inst) {
            let f = self.state.flags(self.arena);
            args.push(f);
        }
        let call = is_call(inst);
        let clobbers_flags = may_clobber_nzcv(inst) || call;

        let effect = opcode_effect(inst.opcode);
        // `HAS_SIDE_EFFECTS` on a memory-pure flag reader or writer only
        // marks the NZCV access, which is modeled; anything else with it is
        // an observable effect.
        let flag_marker_only = effect.is_pure()
            && (writes_flags(inst.opcode) || crate::effects::reads_flags(inst.opcode));
        let mut side_flags = InstFlags::READS_MEMORY
            .union(InstFlags::WRITES_MEMORY)
            .union(InstFlags::IS_CALL)
            .union(InstFlags::IS_BRANCH)
            .union(InstFlags::IS_TERMINATOR)
            .union(InstFlags::IS_PSEUDO);
        if !flag_marker_only {
            side_flags = side_flags.union(InstFlags::HAS_SIDE_EFFECTS);
        }
        // `Copy` is a pseudo with a plain move's meaning; its other
        // pseudo-ness carries no behavior.
        let pseudo_ok = inst.opcode == AArch64Opcode::Copy;
        let observable = !flags.intersection(side_flags).is_empty()
            && !(pseudo_ok && flags.intersection(side_flags).bits() == InstFlags::IS_PSEUDO.bits());
        let pure = effect.is_pure() && !observable;
        let plain_load = effect == crate::effects::MemoryEffect::Load
            && flags
                .intersection(
                    InstFlags::WRITES_MEMORY
                        .union(InstFlags::HAS_SIDE_EFFECTS)
                        .union(InstFlags::IS_CALL)
                        .union(InstFlags::IS_BRANCH)
                        .union(InstFlags::IS_TERMINATOR),
                )
                .is_empty()
            && !is_volatile(inst.opcode);

        if pure || plain_load {
            if plain_load {
                // A read of the current world; it creates no new world.
                args.push(self.state.world);
            }
            let mut first_value = None;
            for (pos, view) in outputs {
                let clean = (!view.fpr || view.bits < 128).then_some(view.bits);
                let t = self
                    .arena
                    .opaque(opcode, aux.clone(), args.clone(), pos as u16, clean);
                first_value.get_or_insert(t);
                self.state.write_view(self.arena, view, t);
            }
            for (i, &p) in inst.implicit_defs.iter().enumerate() {
                if let Some(view) = preg_view(p) {
                    let t = self.arena.opaque(
                        opcode,
                        aux.clone(),
                        args.clone(),
                        IMPLICIT_BASE + i as u16,
                        None,
                    );
                    self.state.write_view(self.arena, view, t);
                }
            }
            if clobbers_flags {
                let t = self
                    .arena
                    .opaque(opcode, aux.clone(), args.clone(), FLAGS_SLOT, None);
                self.state.set_flags(t);
            }
            if plain_load {
                // Opaque load results are tracked like interpreted loads so a
                // speculated one is still refused.
                let t = match first_value {
                    Some(t) => t,
                    None => self.arena.opaque(opcode, aux, args, 0x7FFF, None),
                };
                self.state.loads.push(t);
            }
            return Ok(());
        }

        // Rule 3: an observable effect.
        if call {
            // A call may read its outgoing arguments off the stack.
            let sp = self.state.read_view(
                self.arena,
                View {
                    loc: Loc::Sp,
                    bits: 64,
                    fpr: false,
                },
            );
            args.push(sp);
        }
        let world = self.arena.effect(self.state.world, opcode, aux, args);
        self.state.world = world;
        for (pos, view) in outputs {
            let clean = (!view.fpr || view.bits < 128).then_some(view.bits);
            let t = self.arena.effect_out(world, pos as u16, clean);
            self.state.write_view(self.arena, view, t);
        }
        let mut clobbered: Vec<PReg> = inst.implicit_defs.to_vec();
        if call {
            clobbered.extend(CALL_CLOBBER_GPRS);
            clobbered.extend(CALLER_SAVED_FPRS);
        }
        for p in clobbered {
            if let Some(view) = preg_view(p) {
                let key = match view.loc {
                    Loc::Gpr(n) => u16::from(n),
                    Loc::Fpr(n) => 64 + u16::from(n),
                    Loc::Sp => 200,
                    Loc::Sys(e) => 300 + e,
                    _ => 400,
                };
                let t = self.arena.effect_out(world, CLOBBER_BASE + key, None);
                // A clobber writes the whole register.
                let whole = View {
                    loc: view.loc,
                    bits: if view.fpr { 128 } else { 64 },
                    fpr: view.fpr,
                };
                self.state.write_view(self.arena, whole, t);
            }
        }
        if clobbers_flags {
            let t = self.arena.effect_out(world, FLAGS_SLOT, None);
            self.state.set_flags(t);
        }
        Ok(())
    }
}

fn is_volatile(opcode: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        opcode,
        VolatileLdrRI
            | VolatileLdrbRI
            | VolatileLdrhRI
            | VolatileStrRI
            | VolatileStrbRI
            | VolatileStrhRI
    )
}

/// Flag bits that change an instruction's behavior or classification.
fn flags_key(flags: InstFlags) -> u16 {
    let mut key = 0u16;
    for (i, f) in [
        InstFlags::READS_MEMORY,
        InstFlags::WRITES_MEMORY,
        InstFlags::HAS_SIDE_EFFECTS,
        InstFlags::IS_CALL,
        InstFlags::IS_BRANCH,
        InstFlags::IS_TERMINATOR,
        InstFlags::IS_PSEUDO,
        InstFlags::IS_RETURN,
        // Native EH-region classification consumes this semantic property.
        // Losing or forging it is not the same call, despite identical bytes.
        InstFlags::CANNOT_UNWIND_CALL,
    ]
    .into_iter()
    .enumerate()
    {
        if flags.contains(f) {
            key |= 1 << i;
        }
    }
    key
}
