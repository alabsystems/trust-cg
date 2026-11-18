// trust-cg-verify/aarch64_trap_guard.rs - per-instance AArch64 trap/guard obligations
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Per-instance trap-guard obligations for the AArch64 trap surface (L04-P12):
//! the binding, execution and accounting layer over the trap-expansion verdict.
//!
//! # Where this sits
//!
//! [`crate::aarch64_trap_expansion`] decides, exactly and in process, that the
//! words of each recorded expansion (`MachFunction::trap_expansions`) trap
//! exactly when the RECORDED carrier's condition holds, and the function
//! verifier writes that verdict on the expansion's `BRK` row (credited only by
//! a Clean-checked replay through the verification request). That verdict
//! trusts instruction selection's choice of carrier and says nothing about
//! where the expansion sits. This module adds what it does not establish, and
//! never credits anything itself:
//!
//! * the carrier is bound to the source guard its TV-1 stamp names (kind,
//!   bound, bit width, overflow tag, operand widths);
//! * the window executes (in the emitted layout, on a reached block, not dead
//!   code);
//! * NZCV and the IP scratch registers it writes are dead after it;
//! * an unconditional `BRK` outside a window has a role this module binds
//!   exactly, or it is refused;
//! * a trap the function lost fails or refuses the function ([`account`]).
//!
//! Its own model of each window (symbolic execution over [`crate::nzcv`], a
//! directed battery checked against Rust's native arithmetic, then sampling)
//! is a second, independently written statement of the window semantics: a
//! disagreement with it fails the row, so the two models cannot drift apart
//! silently.
//!
//! [`analyze`] gives each instruction at most one [`TrapGuardRow`], which the
//! function verifier merges into the row it would otherwise write
//! ([`combine`]): a failure or refusal of this module replaces a milder row;
//! a window or role that holds and binds leaves the trap-expansion verdict
//! (on the `BRK`) and the instruction's own row (on the skip branch and the
//! flag producer) standing; without a replayed LIR source nothing can be
//! bound, and a row that would then be promotable is refused instead.
//!
//! ## Guard windows
//!
//! `trust_cg_codegen::lower::expand_trap_*` rewrites each surviving exact
//! carrier, after register allocation, into a window
//!
//! ```text
//!   flag producer / scratch setup      CMP | ADDS ZR | SUBS ZR | MOVZ(+MOVK) X16/W16 + CMP |
//!                                      MUL X16 + SMULH X17 + ASR X16 + CMP | UMULH X16 + CMP
//!   skip branch, displacement +2       CBNZ r | B.LO | B.VC | B.HS | B.EQ
//!   BRK #1                             the trap, at the skip branch's fall-through
//! ```
//!
//! and records the carrier, as it stood before the rewrite, with the
//! instructions it emitted, in `MachFunction::trap_expansions`; the first
//! instruction reuses the carrier's `InstId`. For each record this module
//!
//! 1. requires the window to execute: its block is in the emitted layout
//!    (`block_order`) and reached from the entry, a landing pad or the
//!    overflow block of a stack-limit check the stack-limit net certifies,
//!    along the recorded successor edges (otherwise refused), and its first
//!    instruction is not dead code after a `RET`, `B`, `BR`, tail call or
//!    unskipped trap that no branch of the function targets (otherwise the
//!    trap is missing: FAILED);
//! 2. re-derives the window from the final instructions: contiguous in one
//!    block from the recorded id, ending in a skip branch of displacement
//!    exactly 2 immediately followed by the `BRK`, built only from the
//!    modeled vocabulary above (anything else is refused, never guessed), and
//!    reaching neither another recorded carrier's window nor a `RET`, `B`,
//!    `BR` or tail call before its own skip branch (either is a missing
//!    trap);
//! 3. symbolically executes it over the carrier's operand registers (the
//!    Arm `AddWithCarry` flags of [`crate::nzcv`], W reads as the low half, W
//!    writes zero-extended), giving `trap = NOT(skip taken)`;
//! 4. states the carrier's semantics independently (a relational comparison,
//!    or the exact wide result not being representable) and compares the two
//!    on a directed boundary battery, where both must also agree with Rust's
//!    native arithmetic, and then on the sampling lane;
//! 5. binds the carrier to the source guard its TV-1 stamp names: kind,
//!    bound, bit width and overflow tag exactly, operand widths against the
//!    source types the LIR records; and
//! 6. checks that NZCV and the IP scratch registers the window writes are
//!    dead after it, so the fall-through path observes nothing of it.
//!
//! Each carrier is judged on its own and its verdict goes on its own rows: the
//! skip branch and the `BRK` of a well-formed window (its flag producer and
//! scratch setup keep their own instruction rows), and every instruction
//! scanned for a malformed one, the recorded first instruction included. Rows
//! merge monotonically: a failure is never replaced by a refusal or a bound
//! role, and a refusal never by a bound role. A refutation — the trap fires
//! where the condition is false or stays silent where it is true, the trap is
//! missing (no skip branch and `BRK`, a skip of another displacement, a window
//! that runs into another carrier's window, or a window that never executes as
//! in 1), the carrier names a different source guard, or a malformed carrier
//! degraded to an unconditional trap — FAILS the rows. A window that holds,
//! executes and binds gets no row of its own here. What that establishes is
//! narrow: the window, which can execute, traps exactly when the RECORDED
//! carrier's condition holds over the carrier's operand REGISTERS, and the
//! carrier is the stamped source guard's kind, constants and widths. Nothing
//! here binds the registers to the source values (the post-allocation value
//! flow judges a recorded expansion as its carrier at the carrier's operands)
//! or places the window before the operation the guard protects (a window
//! moved to another reachable position still holds).
//!
//! ## Source accounting
//!
//! A trap the emitted function lost has no row to fail, so [`analyze`] also
//! judges the function as a whole ([`account`]): a recorded expansion whose
//! first instruction is in no block is a missing trap (FAILED), and, wherever
//! the replayed LIR is indexed, every source guard (`GuardNull`,
//! `GuardDivZero`, `GuardShiftRange`, `GuardBoundsCheck`,
//! `GuardBoundsCheckDyn`, `GuardOverflow`), `Assert` and `Trap` must be
//! accounted for by an executing trap row whose judgement read its stamp and
//! implements it:
//!
//! * a guard by a recorded window (or an un-expanded carrier) that executes,
//!   holds against its carrier (for the window), and whose carrier is that
//!   guard's kind and constants (an operand width that does not bind leaves
//!   the row refused but the trap present);
//! * an `Assert` by an executing `BRK` stamped with it (its row is refused:
//!   the cross-block window is not modeled);
//! * a `Trap` by an executing `BRK` stamped with it that closes its block.
//!
//! A stamp alone accounts for nothing: the stack-limit trap, the `BRK` after a
//! noreturn call, a degraded bare trap, a refuted, displaced or mismatched
//! window, a stamped instruction that is not a trap, and a trap outside the
//! executed code account for no source trap. Two omission checks cover
//! a `GuardDivZero` with a constant-nonzero divisor at its LIR width and
//! a plain `Trap` on a contradictory retest of the nonzero switch edge.
//! The latter requires an unchanged typed source value, the omitted block
//! absent from the final layout, and live machine guards at the remainder
//! entrances. Any other unaccounted source trap refuses the function. The
//! function verifier reports either finding as a function precondition
//! failure (`TrapGuardAccounting`), so the function cannot be promoted, and
//! keeps the instruction rows.
//!
//! ## Unconditional traps
//!
//! A `BRK` outside a window keeps a promotable `Skipped` status only in a role
//! this module establishes ([`TRAP_GUARD_BOUND_ROLE`]):
//!
//! * the U10 stack-limit trap `BRK #0x534c`, alone in the overflow block of a
//!   check the stack-limit net ([`crate::aarch64_stack_limit::check`])
//!   certifies on this stream, with no source stamp (the function's
//!   stack-limit fields are claims; without the net's certificate, or with a
//!   stamp, the role is refused);
//! * the unreachable `BRK` closing a block after a call to `_Unwind_Resume` or
//!   `__stack_chk_fail`, unless its stamp names a source trap, which that role
//!   does not implement (refused);
//! * the source `Trap` terminator of the LIR entry block, as the `BRK` closing
//!   the machine entry block with no control transfer before it, so both trap
//!   exactly when the function runs its entry block to the end.
//!
//! Every other trap row is refused by name ([`TRAP_GUARD_REFUSED`]) and blocks
//! promotion: a `BRK` with no bound role, a guard-shaped window with no
//! recorded carrier, the `BRK` of an `Assert` trap block, a bare trap pseudo,
//! and a source-`Trap` `BRK` anywhere else (the branches that reach it decide
//! when it runs, and their polarity against the source's control flow is not
//! checked here). A source-`Trap` `BRK` that never executes FAILS. An
//! un-expanded exact carrier (a stream before the late expansion) is bound to
//! its stamped source like a window's carrier and otherwise left to the
//! trap-expansion verdict on its stated expansion.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::{Mutex, OnceLock};

use trust_cg_ir::provenance::SourceInstId;
use trust_cg_ir::regs::SpecialReg;
use trust_cg_ir::{
    AArch64Opcode as Op, BlockId, InstId, LoweringProvenance, MachFunction, MachInst, MachOperand,
    OverflowOp, RegClass, STACK_LIMIT_TRAP_IMM, unpack_overflow_tag,
};
use trust_cg_lower::Type as LirType;
use trust_cg_lower::instructions::Opcode as LirOpcode;

use crate::function_verifier::InstructionVerificationResult;
use crate::lowering_proof::{
    MachineSideProvenance, ProofObligation, TransvalCheckKind, VerificationConfig,
    memoized_verify_by_evaluation,
};
use crate::nzcv::{NzcvFlags, encode_adds, encode_subs, eval_condition};
use crate::provenance_xcheck::{LirSourceIndex, LirSourceInst};
use crate::smt::{EvalEnv, SmtExpr as E};
use crate::verify::VerificationResult;

/// Prefix of every row this module writes. The emitted-opcode inventory reads
/// it to keep a refused window's `CBNZ` out of the covered-elsewhere class.
pub const TRAP_GUARD_TAG: &str = "[TCG-TRAP-GUARD]";

/// Reason prefix of a trap row this module cannot bind or model.
pub const TRAP_GUARD_REFUSED: &str = "[TCG-TRAP-GUARD] refused";

/// Reason prefix of an unconditional `BRK` bound to an exact role.
pub const TRAP_GUARD_BOUND_ROLE: &str = "[TCG-TRAP-GUARD] bound unconditional trap";

/// Proof-name prefix of a failed trap row.
pub const TRAP_GUARD_FAILED: &str = "[TCG-TRAP-GUARD] trap-guard window";

/// The longest window an expansion emits is the signed-multiply one (six
/// instructions); anything longer is not an expansion.
const MAX_WINDOW: usize = 8;

/// Directed points are enumerated up to this many per window shape.
const MAX_DIRECTED_POINTS: usize = 8192;

// ---------------------------------------------------------------------------
// Opcode classes
// ---------------------------------------------------------------------------

/// The five exact carriers `expand_trap_*` rewrites.
pub fn is_exact_carrier(op: Op) -> bool {
    matches!(
        op,
        Op::TrapNullIfZero
            | Op::TrapDivZeroIfZero
            | Op::TrapShiftRangeIfOOB
            | Op::TrapBoundsCheckExact
            | Op::TrapOverflowExact
    )
}

/// The five bare trap pseudos the encoder emits as an unconditional `BRK #1`.
pub fn is_bare_trap(op: Op) -> bool {
    matches!(
        op,
        Op::TrapOverflow
            | Op::TrapBoundsCheck
            | Op::TrapNull
            | Op::TrapDivZero
            | Op::TrapShiftRange
    )
}

/// A `BRK` that encodes a trap word: no operand (`BRK #1`) or one 16-bit
/// comment immediate.
fn is_trap_word(inst: &MachInst) -> bool {
    inst.opcode == Op::Brk
        && match inst.operands.as_slice() {
            [] => true,
            [MachOperand::Imm(comment)] => (0..=0xffff).contains(comment),
            _ => false,
        }
}

/// A conditional branch whose last operand is a resolved word displacement.
fn skip_branch_displacement(inst: &MachInst) -> Option<i64> {
    match (inst.opcode, inst.operands.as_slice()) {
        (Op::BCond, [MachOperand::Imm(_), MachOperand::Imm(d)])
        | (Op::Cbnz | Op::Cbz, [_, MachOperand::Imm(d)]) => Some(*d),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Register model
// ---------------------------------------------------------------------------

/// A general-purpose register location: a physical register NUMBER (W and X
/// views share it) or a virtual register.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum RegKey {
    Gpr(u8),
    Virtual(u32),
}

impl std::fmt::Display for RegKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RegKey::Gpr(n) => write!(f, "x{n}"),
            RegKey::Virtual(v) => write!(f, "v{v}"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum RegRef {
    Reg { key: RegKey, width: u32 },
    Zero { width: u32 },
}

impl RegRef {
    fn width(self) -> u32 {
        match self {
            RegRef::Reg { width, .. } | RegRef::Zero { width } => width,
        }
    }
}

/// The modeled view of an operand: X0-X30 / W0-W30, XZR/WZR, or a GPR-class
/// virtual register. SP/WSP and every other bank are not modeled.
fn reg_ref(op: &MachOperand) -> Option<RegRef> {
    match op {
        MachOperand::PReg(p) => match p.encoding() {
            e @ 0..=30 => Some(RegRef::Reg {
                key: RegKey::Gpr(e as u8),
                width: 64,
            }),
            e @ 32..=62 => Some(RegRef::Reg {
                key: RegKey::Gpr((e - 32) as u8),
                width: 32,
            }),
            160 => Some(RegRef::Zero { width: 64 }),
            161 => Some(RegRef::Zero { width: 32 }),
            _ => None,
        },
        MachOperand::Special(SpecialReg::XZR) => Some(RegRef::Zero { width: 64 }),
        MachOperand::Special(SpecialReg::WZR) => Some(RegRef::Zero { width: 32 }),
        MachOperand::VReg(v) => match v.class {
            RegClass::Gpr64 => Some(RegRef::Reg {
                key: RegKey::Virtual(v.id),
                width: 64,
            }),
            RegClass::Gpr32 => Some(RegRef::Reg {
                key: RegKey::Virtual(v.id),
                width: 32,
            }),
            _ => None,
        },
        _ => None,
    }
}

fn mask(value: u64, width: u32) -> u64 {
    if width >= 64 {
        value
    } else {
        value & ((1u64 << width) - 1)
    }
}

fn low(expr: E, width: u32) -> E {
    if width >= 64 {
        expr
    } else {
        expr.extract(width - 1, 0)
    }
}

fn bit(cond: E) -> E {
    E::ite(cond, E::bv_const(1, 1), E::bv_const(0, 1))
}

fn not_bit(cond: E) -> E {
    E::ite(cond, E::bv_const(0, 1), E::bv_const(1, 1))
}

// ---------------------------------------------------------------------------
// Carriers
// ---------------------------------------------------------------------------

/// What an exact carrier checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CarrierKind {
    /// `TrapNullIfZero ptr`: trap iff `ptr == 0`.
    Null,
    /// `TrapDivZeroIfZero d`: trap iff `d == 0`.
    DivZero,
    /// `TrapShiftRangeIfOOB amount, #bitwidth`: trap iff `amount >=u bitwidth`.
    ShiftRange { bitwidth: i64 },
    /// `TrapBoundsCheckExact base, index, #bound`: trap iff `index >=u bound`.
    BoundsConst { bound: i64 },
    /// `TrapBoundsCheckExact base, index, len`: trap iff `index >=u len`.
    BoundsDyn,
    /// `TrapOverflowExact lhs, rhs, #tag`: trap iff the op overflows.
    Overflow {
        op: OverflowOp,
        width: u32,
        tag: i64,
    },
}

impl CarrierKind {
    fn describe(self) -> String {
        match self {
            CarrierKind::Null => "null-pointer guard (trap iff ptr == 0)".into(),
            CarrierKind::DivZero => "divide-by-zero guard (trap iff divisor == 0)".into(),
            CarrierKind::ShiftRange { bitwidth } => {
                format!("shift-range guard (trap iff amount >=u {bitwidth})")
            }
            CarrierKind::BoundsConst { bound } => {
                format!("bounds guard (trap iff index >=u {bound})")
            }
            CarrierKind::BoundsDyn => "dynamic bounds guard (trap iff index >=u len)".into(),
            CarrierKind::Overflow { op, width, .. } => {
                format!("overflow guard (trap iff {op:?} overflows at i{width})")
            }
        }
    }

    /// The kind without its constant: the obligation name, so the sampling
    /// lane's memo serves every bound and bit width of one window shape.
    fn shape(self) -> String {
        match self {
            CarrierKind::Null => "null-pointer guard".into(),
            CarrierKind::DivZero => "divide-by-zero guard".into(),
            CarrierKind::ShiftRange { .. } => "shift-range guard".into(),
            CarrierKind::BoundsConst { .. } => "constant bounds guard".into(),
            CarrierKind::BoundsDyn => "dynamic bounds guard".into(),
            CarrierKind::Overflow { op, width, .. } => format!("{op:?} i{width} overflow guard"),
        }
    }

    /// The carrier constant a window's `CMP #imm` must reproduce, if any.
    fn constant(self) -> Option<i64> {
        match self {
            CarrierKind::ShiftRange { bitwidth } => Some(bitwidth),
            CarrierKind::BoundsConst { bound } => Some(bound),
            _ => None,
        }
    }
}

fn carrier_kind(carrier: &MachInst) -> Result<CarrierKind, String> {
    let ops = carrier.operands.as_slice();
    let reg = |op: &MachOperand| matches!(reg_ref(op), Some(RegRef::Reg { .. }));
    match (carrier.opcode, ops) {
        (Op::TrapNullIfZero, [p]) if reg(p) => Ok(CarrierKind::Null),
        (Op::TrapDivZeroIfZero, [d]) if reg(d) => Ok(CarrierKind::DivZero),
        (Op::TrapShiftRangeIfOOB, [a, MachOperand::Imm(bw)]) if reg(a) && *bw >= 0 => {
            Ok(CarrierKind::ShiftRange { bitwidth: *bw })
        }
        (Op::TrapBoundsCheckExact, [_, i, MachOperand::Imm(b)]) if reg(i) && *b >= 0 => {
            Ok(CarrierKind::BoundsConst { bound: *b })
        }
        (Op::TrapBoundsCheckExact, [_, i, l]) if reg(i) && reg(l) => Ok(CarrierKind::BoundsDyn),
        (Op::TrapOverflowExact, [l, r, MachOperand::Imm(tag)]) if reg(l) && reg(r) => {
            let (op, width) = unpack_overflow_tag(*tag)
                .ok_or_else(|| format!("overflow tag {tag} does not decode"))?;
            if op.is_mul() && width != 64 {
                return Err(format!("{op:?} at i{width} has no expansion (64-bit only)"));
            }
            Ok(CarrierKind::Overflow {
                op,
                width: u32::from(width),
                tag: *tag,
            })
        }
        _ => Err(format!(
            "recorded carrier `{:?} {:?}` is not a well-formed exact guard carrier",
            carrier.opcode, carrier.operands
        )),
    }
}

/// Role names: each carrier register operand names a variable `c{i}` (its
/// first position), shared by the carrier side and the window side. Any other
/// register a window reads is a distinct input, so a window that tests a
/// different register than the carrier names refutes.
#[derive(Debug, Clone)]
struct RoleNames {
    names: HashMap<RegKey, String>,
}

impl RoleNames {
    fn for_carrier(carrier: &MachInst) -> Self {
        let mut names = HashMap::new();
        for (i, op) in carrier.operands.iter().enumerate() {
            if let Some(RegRef::Reg { key, .. }) = reg_ref(op) {
                names.entry(key).or_insert_with(|| format!("c{i}"));
            }
        }
        Self { names }
    }

    fn name(&self, key: RegKey) -> String {
        self.names
            .get(&key)
            .cloned()
            .unwrap_or_else(|| format!("other_{key}"))
    }
}

// ---------------------------------------------------------------------------
// Symbolic execution
// ---------------------------------------------------------------------------

/// Name of the variable that stands for the carrier constant when the
/// window's `CMP #imm` reproduces it exactly (so one evaluation cell serves
/// every bound and bit width of a shape).
const K: &str = "k";

struct Exec<'a> {
    names: &'a RoleNames,
    regs: HashMap<RegKey, E>,
    inputs: Vec<(String, u32)>,
    flags: Option<NzcvFlags>,
    wrote_flags: bool,
    written: BTreeSet<RegKey>,
    k_const: Option<i64>,
    used_k: bool,
}

impl<'a> Exec<'a> {
    fn new(names: &'a RoleNames, k_const: Option<i64>) -> Self {
        Self {
            names,
            regs: HashMap::new(),
            inputs: Vec::new(),
            flags: None,
            wrote_flags: false,
            written: BTreeSet::new(),
            k_const,
            used_k: false,
        }
    }

    fn input(&mut self, name: String) -> E {
        if !self.inputs.iter().any(|(n, _)| *n == name) {
            self.inputs.push((name.clone(), 64));
        }
        E::var(name, 64)
    }

    fn k_at(&mut self, width: u32) -> E {
        self.used_k = true;
        let k = self.input(K.to_string());
        low(k, width)
    }

    fn read(&mut self, op: &MachOperand) -> Result<(E, u32), String> {
        match reg_ref(op) {
            Some(RegRef::Zero { width }) => Ok((E::bv_const(0, width), width)),
            Some(RegRef::Reg { key, width }) => {
                let full = match self.regs.get(&key) {
                    Some(value) => value.clone(),
                    None => {
                        let name = self.names.name(key);
                        self.input(name)
                    }
                };
                Ok((low(full, width), width))
            }
            None => Err(format!(
                "operand {op:?} is not a modeled general-purpose register"
            )),
        }
    }

    fn read_at(&mut self, op: &MachOperand, width: u32) -> Result<E, String> {
        let (value, w) = self.read(op)?;
        if w != width {
            return Err(format!(
                "operand {op:?} is {w}-bit where the instruction is {width}-bit"
            ));
        }
        Ok(value)
    }

    fn write(&mut self, op: &MachOperand, value: E, width: u32) -> Result<(), String> {
        match reg_ref(op) {
            Some(RegRef::Zero { width: w }) if w == width => Ok(()),
            Some(RegRef::Reg { key, width: w }) if w == width => {
                let full = if w == 32 { value.zero_ext(32) } else { value };
                self.regs.insert(key, full);
                self.written.insert(key);
                Ok(())
            }
            _ => Err(format!(
                "destination {op:?} is not a modeled {width}-bit register"
            )),
        }
    }

    fn dest_width(op: &MachOperand) -> Result<u32, String> {
        reg_ref(op)
            .map(RegRef::width)
            .ok_or_else(|| format!("destination {op:?} is not a modeled register"))
    }

    /// Execute one non-branch window instruction.
    fn step(&mut self, inst: &MachInst) -> Result<(), String> {
        let ops = inst.operands.as_slice();
        let shape = || {
            format!(
                "{:?} {:?} is not a modeled shape",
                inst.opcode, inst.operands
            )
        };
        match inst.opcode {
            Op::CmpRI => {
                let [rn, MachOperand::Imm(imm)] = ops else {
                    return Err(shape());
                };
                if !(0..=4095).contains(imm) {
                    return Err(format!("CMP immediate {imm} is not an unshifted imm12"));
                }
                let Some(RegRef::Reg { width, .. }) = reg_ref(rn) else {
                    return Err(shape());
                };
                let lhs = self.read_at(rn, width)?;
                let rhs = if self.k_const == Some(*imm) {
                    self.k_at(width)
                } else {
                    E::bv_const(*imm as u64, width)
                };
                self.flags = Some(encode_subs(lhs, rhs, width).1);
                self.wrote_flags = true;
            }
            Op::CmpRR => {
                let [rn, rm] = ops else {
                    return Err(shape());
                };
                let width = Self::dest_width(rn)?;
                let lhs = self.read_at(rn, width)?;
                let rhs = self.read_at(rm, width)?;
                self.flags = Some(encode_subs(lhs, rhs, width).1);
                self.wrote_flags = true;
            }
            Op::AddsRR | Op::SubsRR => {
                let [rd, rn, rm] = ops else {
                    return Err(shape());
                };
                let width = Self::dest_width(rd)?;
                let lhs = self.read_at(rn, width)?;
                let rhs = self.read_at(rm, width)?;
                let (result, flags) = if inst.opcode == Op::AddsRR {
                    encode_adds(lhs, rhs, width)
                } else {
                    encode_subs(lhs, rhs, width)
                };
                self.write(rd, result, width)?;
                self.flags = Some(flags);
                self.wrote_flags = true;
            }
            Op::Movz => {
                let (rd, imm) = match ops {
                    [rd, MachOperand::Imm(v)] | [rd, MachOperand::Imm(v), MachOperand::Imm(0)] => {
                        (rd, *v)
                    }
                    _ => return Err(shape()),
                };
                if !(0..=0xffff).contains(&imm) {
                    return Err(shape());
                }
                let width = Self::dest_width(rd)?;
                self.write(rd, E::bv_const(imm as u64, width), width)?;
            }
            Op::Movk => {
                let (rd, imm, shift) = match ops {
                    [rd, MachOperand::Imm(v)] => (rd, *v, 0),
                    [rd, MachOperand::Imm(v), MachOperand::Imm(s)] => (rd, *v, *s),
                    _ => return Err(shape()),
                };
                let width = Self::dest_width(rd)?;
                if !(0..=0xffff).contains(&imm)
                    || !matches!(shift, 0 | 16 | 32 | 48)
                    || shift >= i64::from(width)
                {
                    return Err(shape());
                }
                let old = self.read_at(rd, width)?;
                let keep = !(0xffffu64 << shift);
                let value = old
                    .bvand(E::bv_const(mask(keep, width), width))
                    .bvor(E::bv_const((imm as u64) << shift, width));
                self.write(rd, value, width)?;
            }
            Op::MulRR => {
                let [rd, rn, rm] = ops else {
                    return Err(shape());
                };
                let width = Self::dest_width(rd)?;
                let lhs = self.read_at(rn, width)?;
                let rhs = self.read_at(rm, width)?;
                self.write(rd, lhs.bvmul(rhs), width)?;
            }
            Op::Smulh | Op::Umulh => {
                let [rd, rn, rm] = ops else {
                    return Err(shape());
                };
                let lhs = self.read_at(rn, 64)?;
                let rhs = self.read_at(rm, 64)?;
                let product = if inst.opcode == Op::Smulh {
                    lhs.sign_ext(64).bvmul(rhs.sign_ext(64))
                } else {
                    lhs.zero_ext(64).bvmul(rhs.zero_ext(64))
                };
                self.write(rd, product.extract(127, 64), 64)?;
            }
            Op::AsrRI => {
                let [rd, rn, MachOperand::Imm(s)] = ops else {
                    return Err(shape());
                };
                let width = Self::dest_width(rd)?;
                if !(0..i64::from(width)).contains(s) {
                    return Err(shape());
                }
                let value = self.read_at(rn, width)?;
                self.write(rd, value.bvashr(E::bv_const(*s as u64, width)), width)?;
            }
            other => {
                return Err(format!(
                    "{other:?} is outside the modeled trap-window vocabulary"
                ));
            }
        }
        Ok(())
    }

    /// The skip branch's taken condition.
    fn taken(&mut self, inst: &MachInst) -> Result<E, String> {
        match (inst.opcode, inst.operands.as_slice()) {
            (Op::BCond, [MachOperand::Imm(cc), MachOperand::Imm(_)]) => {
                let cc = crate::aarch64_select_proofs::cc_from_isel_immediate(*cc)
                    .ok_or_else(|| format!("B.cond condition {cc} is not EQ..LE"))?;
                let flags = self.flags.as_ref().ok_or_else(|| {
                    "the skip branch reads NZCV the window did not set".to_string()
                })?;
                Ok(eval_condition(cc, flags))
            }
            (Op::Cbnz | Op::Cbz, [rt, MachOperand::Imm(_)]) => {
                let (value, width) = self.read(rt)?;
                let zero = value.eq_expr(E::bv_const(0, width));
                Ok(if inst.opcode == Op::Cbz {
                    zero
                } else {
                    zero.not_expr()
                })
            }
            _ => Err(format!(
                "{:?} {:?} is not a modeled skip branch",
                inst.opcode, inst.operands
            )),
        }
    }
}

/// The carrier's own semantics over the shared role variables: a trap bit.
fn carrier_trap(carrier: &MachInst, kind: CarrierKind, exec: &mut Exec<'_>) -> Result<E, String> {
    let ops = carrier.operands.as_slice();
    let bound_at = |exec: &mut Exec<'_>, constant: i64, width: u32| -> Result<E, String> {
        if width < 64 && (constant as u64) >> width != 0 {
            return Err(format!(
                "carrier constant {constant} does not fit its {width}-bit operand"
            ));
        }
        Ok(if exec.used_k {
            exec.k_at(width)
        } else {
            E::bv_const(constant as u64, width)
        })
    };
    Ok(match kind {
        CarrierKind::Null | CarrierKind::DivZero => {
            let (value, width) = exec.read(&ops[0])?;
            bit(value.eq_expr(E::bv_const(0, width)))
        }
        CarrierKind::ShiftRange { bitwidth } => {
            let (amount, width) = exec.read(&ops[0])?;
            let limit = bound_at(exec, bitwidth, width)?;
            not_bit(amount.bvult(limit))
        }
        CarrierKind::BoundsConst { bound } => {
            let (index, width) = exec.read(&ops[1])?;
            let limit = bound_at(exec, bound, width)?;
            not_bit(index.bvult(limit))
        }
        CarrierKind::BoundsDyn => {
            let (index, width) = exec.read(&ops[1])?;
            let len = exec.read_at(&ops[2], width)?;
            not_bit(index.bvult(len))
        }
        CarrierKind::Overflow { op, width, .. } => {
            // The carrier's width is its tag's: read the low `width` bits of
            // each operand register whatever view it names.
            let (a, a_width) = exec.read(&ops[0])?;
            let (b, b_width) = exec.read(&ops[1])?;
            let a = low_of(a, a_width, width);
            let b = low_of(b, b_width, width);
            match op {
                // The exact (w+1)-bit result is not representable at w bits.
                OverflowOp::SignedAdd | OverflowOp::SignedSub => {
                    let exact = if op == OverflowOp::SignedAdd {
                        a.sign_ext(1).bvadd(b.sign_ext(1))
                    } else {
                        a.sign_ext(1).bvsub(b.sign_ext(1))
                    };
                    let wrapped = exact.clone().extract(width - 1, 0).sign_ext(1);
                    not_bit(exact.eq_expr(wrapped))
                }
                OverflowOp::UnsignedAdd => {
                    let exact = a.zero_ext(1).bvadd(b.zero_ext(1));
                    let wrapped = exact.clone().extract(width - 1, 0).zero_ext(1);
                    not_bit(exact.eq_expr(wrapped))
                }
                // The exact difference is negative.
                OverflowOp::UnsignedSub => bit(a.bvult(b)),
                // The exact 128-bit product is not the extension of its low half.
                OverflowOp::SignedMul => {
                    let exact = a.sign_ext(64).bvmul(b.sign_ext(64));
                    let wrapped = exact.clone().extract(63, 0).sign_ext(64);
                    not_bit(exact.eq_expr(wrapped))
                }
                OverflowOp::UnsignedMul => {
                    let exact = a.zero_ext(64).bvmul(b.zero_ext(64));
                    let wrapped = exact.clone().extract(63, 0).zero_ext(64);
                    not_bit(exact.eq_expr(wrapped))
                }
            }
        }
    })
}

/// The low `width` bits of a value read at `read_width` bits (zero-extended
/// when the read was narrower).
fn low_of(value: E, read_width: u32, width: u32) -> E {
    if read_width == width {
        value
    } else if read_width > width {
        value.extract(width - 1, 0)
    } else {
        value.zero_ext(width - read_width)
    }
}

/// Rust's own arithmetic on the carrier's semantics, at one point.
fn native_trap(
    carrier: &MachInst,
    kind: CarrierKind,
    used_k: bool,
    value: &dyn Fn(&MachOperand) -> Option<(u64, u32)>,
    k: Option<u64>,
) -> Option<bool> {
    let ops = carrier.operands.as_slice();
    let constant = |c: i64, width: u32| -> u64 {
        if used_k {
            mask(k.unwrap_or(0), width)
        } else {
            mask(c as u64, width)
        }
    };
    Some(match kind {
        CarrierKind::Null | CarrierKind::DivZero => value(&ops[0])?.0 == 0,
        CarrierKind::ShiftRange { bitwidth } => {
            let (amount, width) = value(&ops[0])?;
            amount >= constant(bitwidth, width)
        }
        CarrierKind::BoundsConst { bound } => {
            let (index, width) = value(&ops[1])?;
            index >= constant(bound, width)
        }
        CarrierKind::BoundsDyn => {
            let (index, width) = value(&ops[1])?;
            let (len, len_width) = value(&ops[2])?;
            if len_width != width {
                return None;
            }
            index >= len
        }
        CarrierKind::Overflow { op, width, .. } => {
            let a = mask(value(&ops[0])?.0, width);
            let b = mask(value(&ops[1])?.0, width);
            match (op, width) {
                (OverflowOp::SignedAdd, 32) => {
                    (a as u32 as i32).checked_add(b as u32 as i32).is_none()
                }
                (OverflowOp::SignedAdd, _) => (a as i64).checked_add(b as i64).is_none(),
                (OverflowOp::SignedSub, 32) => {
                    (a as u32 as i32).checked_sub(b as u32 as i32).is_none()
                }
                (OverflowOp::SignedSub, _) => (a as i64).checked_sub(b as i64).is_none(),
                (OverflowOp::UnsignedAdd, 32) => (a as u32).checked_add(b as u32).is_none(),
                (OverflowOp::UnsignedAdd, _) => a.checked_add(b).is_none(),
                (OverflowOp::UnsignedSub, 32) => (a as u32).checked_sub(b as u32).is_none(),
                (OverflowOp::UnsignedSub, _) => a.checked_sub(b).is_none(),
                (OverflowOp::SignedMul, _) => (a as i64).checked_mul(b as i64).is_none(),
                (OverflowOp::UnsignedMul, _) => a.checked_mul(b).is_none(),
            }
        }
    })
}

// ---------------------------------------------------------------------------
// Window decoding
// ---------------------------------------------------------------------------

/// Why a recorded carrier's window could not be judged.
#[derive(Debug, Clone, PartialEq, Eq)]
enum WindowFault {
    /// The trap is missing or does not sit at the skip branch's
    /// fall-through: a refutation.
    Missing(String),
    /// The window uses a shape outside the modeled vocabulary: refused.
    Unmodeled(String),
}

/// A [`WindowFault`] and the instructions scanned up to it (the carrier id,
/// what followed it, and a `BRK` right after the stopping point), which all
/// carry the verdict: the unstamped skip branch and `BRK` keep it visible
/// even where the stamped first instruction's row is replaced by TV-2.
#[derive(Debug, Clone, PartialEq, Eq)]
struct WindowError {
    fault: WindowFault,
    members: Vec<InstId>,
}

#[derive(Debug, Clone)]
struct Window {
    /// Every instruction from the recorded carrier id to the `BRK`.
    insts: Vec<InstId>,
    skip: InstId,
    brk: InstId,
    /// Block position of the `BRK`.
    brk_pos: usize,
    trap: E,
    inputs: Vec<(String, u32)>,
    wrote_flags: bool,
    written: BTreeSet<RegKey>,
    used_k: bool,
}

fn decode_window(
    func: &MachFunction,
    block: usize,
    start: usize,
    names: &RoleNames,
    k_const: Option<i64>,
    stops: &HashSet<InstId>,
) -> Result<Window, WindowError> {
    let insts = &func.blocks[block].insts;
    let limit = insts.len().min(start + MAX_WINDOW);
    let mut exec = Exec::new(names, k_const);
    let mut members = Vec::new();
    let trap_word_at = |pos: usize| {
        insts
            .get(pos)
            .filter(|id| !stops.contains(id))
            .and_then(|id| func.insts.get(id.0 as usize))
            .is_some_and(is_trap_word)
    };
    // Every scanned instruction carries a fault's verdict. A fault at the skip
    // branch also puts it on the BRK right after; a fault in the setup puts it
    // on the rest of the window's structure as well (through the next skip
    // branch and its BRK, within the window bound, never into another
    // recorded window), so the BRK states the actual reason.
    let fail = |fault: WindowFault, mut members: Vec<InstId>, pos: usize| {
        let at = insts.get(pos).and_then(|id| func.insts.get(id.0 as usize));
        if at.is_some_and(|inst| skip_branch_displacement(inst).is_some()) {
            if trap_word_at(pos + 1) {
                members.push(insts[pos + 1]);
            }
        } else if !at.is_some_and(is_trap_word) {
            let mut rest = Vec::new();
            for q in pos + 1..limit {
                let id = insts[q];
                let Some(inst) = func.insts.get(id.0 as usize) else {
                    break;
                };
                if stops.contains(&id) || ends_without_fallthrough(inst) {
                    if is_trap_word(inst) && !stops.contains(&id) {
                        rest.push(id);
                        members.append(&mut rest);
                    }
                    break;
                }
                rest.push(id);
                if skip_branch_displacement(inst).is_some() {
                    if trap_word_at(q + 1) {
                        rest.push(insts[q + 1]);
                    }
                    members.append(&mut rest);
                    break;
                }
            }
        }
        members.dedup();
        WindowError { fault, members }
    };
    for pos in start..limit {
        let id = insts[pos];
        if pos > start && stops.contains(&id) {
            return Err(fail(
                WindowFault::Missing(format!(
                    "the window runs into the recorded window of another carrier (instruction \
                     {}) before its own skip branch and BRK: the trap is missing",
                    id.0
                )),
                members,
                pos - 1,
            ));
        }
        let Some(inst) = func.insts.get(id.0 as usize) else {
            return Err(fail(
                WindowFault::Unmodeled(format!("instruction reference {} is out of range", id.0)),
                members,
                pos,
            ));
        };
        // A return, branch or tail call before any skip branch ends the
        // window with no trap in it. Its verdict stays on the window's own
        // instructions, not on the control transfer.
        if pos > start && inst.opcode != Op::Brk && ends_without_fallthrough(inst) {
            return Err(WindowError {
                fault: WindowFault::Missing(format!(
                    "the window reaches {:?} before any skip branch and BRK: the trap is missing",
                    inst.opcode
                )),
                members,
            });
        }
        members.push(id);
        if let Some(displacement) = skip_branch_displacement(inst) {
            let taken = match exec.taken(inst) {
                Ok(taken) => taken,
                Err(why) => return Err(fail(WindowFault::Unmodeled(why), members, pos)),
            };
            if displacement != 2 {
                return Err(fail(
                    WindowFault::Missing(format!(
                        "the skip branch {:?} has displacement {displacement}, so it does not \
                         skip exactly the one trap word at its fall-through",
                        inst.opcode
                    )),
                    members,
                    pos,
                ));
            }
            let brk = insts
                .get(pos + 1)
                .copied()
                .filter(|id| func.insts.get(id.0 as usize).is_some_and(is_trap_word));
            let Some(brk) = brk else {
                return Err(fail(
                    WindowFault::Missing(format!(
                        "the skip branch {:?} at block position {pos} is not followed in its \
                         block by a BRK: the trap is missing",
                        inst.opcode
                    )),
                    members,
                    pos,
                ));
            };
            members.push(brk);
            if exec
                .written
                .iter()
                .any(|key| !matches!(key, RegKey::Gpr(16 | 17)))
            {
                let written = format!("{:?}", exec.written);
                return Err(fail(
                    WindowFault::Unmodeled(format!(
                        "the window writes {written}, outside the IP scratch registers X16/X17"
                    )),
                    members,
                    pos,
                ));
            }
            return Ok(Window {
                insts: members,
                skip: id,
                brk,
                brk_pos: pos + 1,
                trap: not_bit(taken),
                inputs: exec.inputs,
                wrote_flags: exec.wrote_flags,
                written: exec.written,
                used_k: exec.used_k,
            });
        }
        if inst.opcode == Op::Brk {
            return Err(fail(
                WindowFault::Missing(
                    "a BRK is reached with no conditional skip branch before it: the trap fires \
                     unconditionally"
                        .into(),
                ),
                members,
                pos,
            ));
        }
        if let Err(why) = exec.step(inst) {
            return Err(fail(WindowFault::Unmodeled(why), members, pos));
        }
    }
    let last = insts.len().min(start + MAX_WINDOW).saturating_sub(1);
    Err(fail(
        WindowFault::Missing(format!(
            "no skip branch followed by a BRK within {MAX_WINDOW} instructions of the carrier: \
             the trap is missing"
        )),
        members,
        last,
    ))
}

// ---------------------------------------------------------------------------
// Deciding a window against its carrier
// ---------------------------------------------------------------------------

/// The outcome of comparing a window with its carrier.
#[derive(Debug, Clone, PartialEq, Eq)]
enum WindowCheck {
    /// The trap fires exactly when the carrier's condition holds on every
    /// directed point and the sampled inputs.
    Holds { directed: usize, sampled: u64 },
    /// A definite disagreement (or a source model that disagrees with the
    /// native oracle).
    Refuted(String),
    /// The window is malformed in a way that removes or misplaces the trap.
    Missing(String),
    /// The window or carrier is outside the modeled shapes.
    Unmodeled(String),
    /// The evaluator could not decide it.
    Undecided(String),
}

fn directed_values(constants: &[u64]) -> Vec<u64> {
    let mut values: Vec<u64> = vec![
        0,
        1,
        2,
        0x7f,
        0x80,
        0xffff,
        0x7fff_ffff,
        0x8000_0000,
        0xffff_ffff,
        0x1_0000_0000,
        0x1_ffff_fffe,
        0x7fff_ffff_ffff_ffff,
        0x8000_0000_0000_0000,
        0xffff_ffff_0000_0001,
        u64::MAX - 1,
        u64::MAX,
    ];
    for &c in constants {
        for v in [c.wrapping_sub(1), c, c.wrapping_add(1)] {
            values.push(v);
        }
    }
    values.sort_unstable();
    values.dedup();
    values
}

/// Enumerate assignments over `vars` (each from its own list): the full
/// product when it fits [`MAX_DIRECTED_POINTS`], otherwise every pair of
/// variables in full against three backgrounds for the rest.
fn directed_points(vars: &[(String, Vec<u64>)]) -> Vec<Vec<u64>> {
    let product: usize = vars
        .iter()
        .map(|(_, values)| values.len())
        .try_fold(1usize, |acc, n| acc.checked_mul(n))
        .unwrap_or(usize::MAX);
    let mut points = Vec::new();
    if product <= MAX_DIRECTED_POINTS {
        let mut index = vec![0usize; vars.len()];
        loop {
            points.push(
                index
                    .iter()
                    .zip(vars)
                    .map(|(&i, (_, values))| values[i])
                    .collect(),
            );
            let mut carry = 0;
            loop {
                if carry == vars.len() {
                    return points;
                }
                index[carry] += 1;
                if index[carry] < vars[carry].1.len() {
                    break;
                }
                index[carry] = 0;
                carry += 1;
            }
        }
    }
    for background in [0u64, 1, u64::MAX] {
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                for &vi in &vars[i].1 {
                    for &vj in &vars[j].1 {
                        let mut point = vec![background; vars.len()];
                        point[i] = vi;
                        point[j] = vj;
                        points.push(point);
                    }
                }
            }
        }
    }
    points
}

/// The exact inputs of one window check: the obligation, the carrier (by its
/// `Debug` rendering: `MachInst` is not `Hash`), whether the carrier constant
/// was abstracted, that constant, and the evaluator configuration.
type CheckKey = (ProofObligation, String, bool, Vec<u64>, u64, u32);

fn check_memo() -> &'static Mutex<HashMap<CheckKey, WindowCheck>> {
    static MEMO: OnceLock<Mutex<HashMap<CheckKey, WindowCheck>>> = OnceLock::new();
    MEMO.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Compare a decoded window with its carrier: the directed battery (machine,
/// carrier model and native oracle must agree at every point), then the
/// sampling lane. Memoized by the exact obligation, carrier and constants.
fn check_window(
    carrier: &MachInst,
    kind: CarrierKind,
    names: &RoleNames,
    window: &Window,
    config: &VerificationConfig,
) -> WindowCheck {
    let mut exec = Exec::new(names, kind.constant());
    exec.used_k = window.used_k;
    // Seed the window's inputs first so the obligation's input order is the
    // window's; the carrier may add its own (a register the window never read).
    exec.inputs = window.inputs.clone();
    let source = match carrier_trap(carrier, kind, &mut exec) {
        Ok(source) => source,
        Err(why) => return WindowCheck::Unmodeled(why),
    };
    let inputs = exec.inputs.clone();
    let obligation = ProofObligation {
        name: format!(
            "AArch64 trap-guard window: {} (trap iff skip branch not taken)",
            kind.shape()
        ),
        trust_ir_expr: source,
        aarch64_expr: window.trap.clone(),
        inputs: inputs.clone(),
        preconditions: Vec::new(),
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "Brk".to_string(),
            arity: u8::try_from(inputs.len()).unwrap_or(u8::MAX),
        },
    };
    let constants: Vec<u64> = kind.constant().map(|c| c as u64).into_iter().collect();
    let signature = carrier
        .operands
        .iter()
        .map(|op| match reg_ref(op) {
            Some(RegRef::Reg { key, width }) => format!("{}:{width}", names.name(key)),
            Some(RegRef::Zero { width }) => format!("zr:{width}"),
            None => format!("{op:?}"),
        })
        .collect::<Vec<_>>()
        .join(",");
    let key = (
        obligation.clone(),
        format!("{:?} {kind:?} [{signature}]", carrier.opcode),
        window.used_k,
        constants.clone(),
        config.sample_count,
        config.exhaustive_threshold,
    );
    if let Some(hit) = check_memo()
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .get(&key)
    {
        return hit.clone();
    }
    let result = check_window_uncached(
        carrier,
        kind,
        names,
        &obligation,
        window.used_k,
        &constants,
        config,
    );
    check_memo()
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .insert(key, result.clone());
    result
}

fn check_window_uncached(
    carrier: &MachInst,
    kind: CarrierKind,
    names: &RoleNames,
    obligation: &ProofObligation,
    used_k: bool,
    constants: &[u64],
    config: &VerificationConfig,
) -> WindowCheck {
    let vars: Vec<(String, Vec<u64>)> = obligation
        .inputs
        .iter()
        .map(|(name, _)| (name.clone(), directed_values(constants)))
        .collect();
    let points = directed_points(&vars);
    for point in &points {
        let mut env = EvalEnv::default();
        for ((name, _), value) in vars.iter().zip(point) {
            env.insert(name.clone(), *value);
        }
        let lookup = |name: &str| -> Option<u64> {
            vars.iter()
                .zip(point)
                .find(|((n, _), _)| n == name)
                .map(|(_, v)| *v)
        };
        let value = |op: &MachOperand| -> Option<(u64, u32)> {
            match reg_ref(op)? {
                RegRef::Zero { width } => Some((0, width)),
                RegRef::Reg { key, width } => Some((mask(lookup(&names.name(key))?, width), width)),
            }
        };
        let Some(native) = native_trap(carrier, kind, used_k, &value, lookup(K)) else {
            return WindowCheck::Unmodeled(
                "the native oracle cannot state this carrier's semantics".into(),
            );
        };
        let render = || {
            vars.iter()
                .zip(point)
                .map(|((n, _), v)| format!("{n}={v:#x}"))
                .collect::<Vec<_>>()
                .join(", ")
        };
        let source = match obligation.trust_ir_expr.try_eval(&env) {
            Ok(result) => result.as_u64() != 0,
            Err(error) => return WindowCheck::Undecided(format!("carrier model: {error}")),
        };
        if source != native {
            return WindowCheck::Refuted(format!(
                "the carrier model disagrees with Rust's native arithmetic at {} (model {source}, \
                 native {native}): a modeling defect, refused",
                render()
            ));
        }
        let machine = match obligation.aarch64_expr.try_eval(&env) {
            Ok(result) => result.as_u64() != 0,
            Err(error) => return WindowCheck::Undecided(format!("window: {error}")),
        };
        if machine != native {
            return WindowCheck::Refuted(format!(
                "at {} the window {} but the carrier's condition is {native}",
                render(),
                if machine { "traps" } else { "does not trap" }
            ));
        }
    }
    match memoized_verify_by_evaluation(obligation, config) {
        VerificationResult::Valid => WindowCheck::Holds {
            directed: points.len(),
            sampled: config.sample_count,
        },
        VerificationResult::Invalid { counterexample } => WindowCheck::Refuted(format!(
            "the sampling lane refutes the window: {counterexample}"
        )),
        VerificationResult::Unknown { reason } => WindowCheck::Undecided(reason),
    }
}

// ---------------------------------------------------------------------------
// Source binding
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum SourceBinding {
    /// Kind, constants and operand widths bind the carrier to this source.
    Bound { source: SourceInstId, how: String },
    /// The stamp names a source this carrier does not implement.
    Mismatch(String),
    /// With the replayed LIR, no exact binding could be established. `source`
    /// is the stamped source when the carrier implements its kind and
    /// constants and only an operand width does not bind.
    Unbound {
        source: Option<SourceInstId>,
        why: String,
    },
    /// No replayed LIR source is available, so nothing can be bound.
    NoSource(String),
}

impl SourceBinding {
    /// The source guard whose kind and constants the carrier implements, if
    /// any: what a holding, executing window accounts for.
    fn implemented_source(&self) -> Option<SourceInstId> {
        match self {
            SourceBinding::Bound { source, .. } => Some(*source),
            SourceBinding::Unbound { source, .. } => *source,
            SourceBinding::Mismatch(_) | SourceBinding::NoSource(_) => None,
        }
    }
}

/// The replayed source instruction the TV-1 stamp on `id` names, with its
/// coordinates.
fn stamped_source<'a>(
    func: &MachFunction,
    id: InstId,
    lir: Option<&'a LirSourceIndex>,
) -> Result<(SourceInstId, &'a LirSourceInst), String> {
    let Some(index) = lir else {
        return Err("no replayed LIR source is available to bind it".into());
    };
    match func.inst_lowering_provenance(id) {
        LoweringProvenance::SourceInst { id: source, .. } => {
            index.get(source).map(|inst| (source, inst)).ok_or_else(|| {
                format!(
                    "its stamp ({}, {}) names no instruction of the replayed LIR",
                    source.block, source.index
                )
            })
        }
        LoweringProvenance::Synthetic { reason } => {
            Err(format!("it carries no source stamp ({reason:?})"))
        }
    }
}

/// Whether an operand of the given register width faithfully holds a value of
/// the recorded source type: a 64-bit register an `I64`, a 32-bit one an
/// `I32`. Narrower source types leave register bits the carrier reads that
/// the source condition does not, so they are not bound.
fn width_binding(
    what: &str,
    register_width: u32,
    ty: Option<&Option<LirType>>,
) -> Result<(), String> {
    match (register_width, ty) {
        (64, Some(Some(LirType::I64))) | (32, Some(Some(LirType::I32))) => Ok(()),
        (_, Some(Some(ty))) => Err(format!(
            "the {what} is a {ty:?} source value carried in a {register_width}-bit register; \
             only I32 in W and I64 in X bind exactly"
        )),
        _ => Err(format!(
            "the replayed LIR records no type for the {what}, so its width does not bind"
        )),
    }
}

fn bind_source(
    func: &MachFunction,
    id: InstId,
    carrier: &MachInst,
    kind: CarrierKind,
    lir: Option<&LirSourceIndex>,
) -> SourceBinding {
    let (source_id, source) = match stamped_source(func, id, lir) {
        Ok(stamped) => stamped,
        Err(why) if lir.is_none() => {
            return SourceBinding::NoSource(format!("the carrier is unbound: {why}"));
        }
        Err(why) => {
            return SourceBinding::Unbound {
                source: None,
                why: format!("the carrier is unbound: {why}"),
            };
        }
    };
    let ops = carrier.operands.as_slice();
    let width = |op: &MachOperand| reg_ref(op).map_or(0, RegRef::width);
    let types = &source.value_flow.arg_types;
    let mismatch = || {
        SourceBinding::Mismatch(format!(
            "the carrier `{:?} {:?}` does not implement its stamped source `{}`",
            carrier.opcode, carrier.operands, source.opcode_debug
        ))
    };
    let widths: Result<(), String> = match (kind, &source.opcode) {
        (CarrierKind::Null, LirOpcode::GuardNull { .. }) if source.args.len() == 1 => {
            if width(&ops[0]) == 64 {
                Ok(())
            } else {
                Err("the pointer is carried in a 32-bit register".into())
            }
        }
        (CarrierKind::DivZero, LirOpcode::GuardDivZero { .. }) if source.args.len() == 1 => {
            width_binding("divisor", width(&ops[0]), types.first())
        }
        (
            CarrierKind::ShiftRange { bitwidth },
            LirOpcode::GuardShiftRange { bitwidth: src, .. },
        ) if source.args.len() == 1 => {
            if i64::from(*src) != bitwidth {
                return mismatch();
            }
            width_binding("shift amount", width(&ops[0]), types.first())
        }
        (CarrierKind::BoundsConst { bound }, LirOpcode::GuardBoundsCheck { bound: src, .. })
            if source.args.len() == 2 =>
        {
            if i64::try_from(*src).ok() != Some(bound) {
                return mismatch();
            }
            width_binding("index", width(&ops[1]), types.get(1))
        }
        (CarrierKind::BoundsDyn, LirOpcode::GuardBoundsCheckDyn { .. })
            if source.args.len() == 3 =>
        {
            width_binding("index", width(&ops[1]), types.get(1))
                .and_then(|()| width_binding("length", width(&ops[2]), types.get(2)))
        }
        (CarrierKind::Overflow { width: w, tag, .. }, LirOpcode::GuardOverflow { op_tag, .. })
            if source.args.len() == 2 =>
        {
            if *op_tag != tag {
                return mismatch();
            }
            if width(&ops[0]) == w && width(&ops[1]) == w {
                Ok(())
            } else {
                Err(format!(
                    "the operands are carried in {}/{}-bit registers for an i{w} overflow tag",
                    width(&ops[0]),
                    width(&ops[1])
                ))
            }
        }
        _ => return mismatch(),
    };
    match widths {
        Ok(()) => SourceBinding::Bound {
            source: source_id,
            how: format!(
                "bound to its stamped source `{}` (kind, constant and operand widths)",
                source.opcode_debug
            ),
        },
        Err(why) => SourceBinding::Unbound {
            source: Some(source_id),
            why: format!(
                "the carrier implements its stamped source `{}` but {why}",
                source.opcode_debug
            ),
        },
    }
}

// ---------------------------------------------------------------------------
// Fall-through effects
// ---------------------------------------------------------------------------

fn ends_without_fallthrough(inst: &MachInst) -> bool {
    matches!(
        inst.opcode,
        Op::Ret | Op::B | Op::Br | Op::TailCall | Op::Brk
    ) || is_bare_trap(inst.opcode)
}

/// Successors to continue a forward scan into at a block end, or why the scan
/// cannot continue soundly.
fn successors(func: &MachFunction, block: usize) -> Result<Vec<usize>, String> {
    let b = &func.blocks[block];
    if b.succs.is_empty() {
        let last = b.insts.last().and_then(|id| func.insts.get(id.0 as usize));
        if last.is_some_and(ends_without_fallthrough) {
            return Ok(Vec::new());
        }
        return Err(format!(
            "block {block} ends without a terminator and records no successor"
        ));
    }
    Ok(b.succs.iter().map(|s| s.0 as usize).collect())
}

/// NZCV is dead from `pos` in `block`: every path reaches a flag writer or a
/// call (NZCV is not preserved across one) before any flag reader.
fn nzcv_dead_from(
    func: &MachFunction,
    block: usize,
    pos: usize,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    use trust_cg_ir::target_info::{AArch64Target, TargetInfo};
    for &id in func.blocks[block].insts.iter().skip(pos) {
        let inst = func
            .insts
            .get(id.0 as usize)
            .ok_or_else(|| "a malformed instruction reference".to_string())?;
        let op = inst.opcode;
        if matches!(op, Op::BCond | Op::Bcc) || <AArch64Target as TargetInfo>::reads_flags(op) {
            return Err(format!("{op:?} may read NZCV the window wrote"));
        }
        if <AArch64Target as TargetInfo>::writes_flags(op) || inst.is_call() {
            return Ok(());
        }
        if op.is_pseudo() && op != Op::Nop {
            return Err(format!("{op:?} has no modeled flag effect"));
        }
    }
    for succ in successors(func, block)? {
        if visited.insert(succ) {
            nzcv_dead_from(func, succ, 0, visited)?;
        }
    }
    Ok(())
}

/// The GPR numbers in `live` are dead from `pos` in `block`: every path writes
/// them, or makes a call (IP0/IP1 do not survive one), before reading them.
fn scratch_dead_from(
    func: &MachFunction,
    block: usize,
    pos: usize,
    live: u32,
    visited: &mut HashSet<(usize, u32)>,
) -> Result<(), String> {
    let mut live = live;
    for &id in func.blocks[block].insts.iter().skip(pos) {
        if live == 0 {
            return Ok(());
        }
        let inst = func
            .insts
            .get(id.0 as usize)
            .ok_or_else(|| "a malformed instruction reference".to_string())?;
        let (generated, reads) = crate::post_ra_reaching_def::inst_gen_reads(inst);
        for reg in reads {
            if let Some(RegRef::Reg {
                key: RegKey::Gpr(n),
                ..
            }) = reg_ref(&MachOperand::PReg(reg))
                && n < 32
                && live & (1 << n) != 0
            {
                return Err(format!(
                    "{:?} reads x{n}, which the window overwrote",
                    inst.opcode
                ));
            }
        }
        live &= !(generated as u32);
        if inst.is_call() {
            live &= !((1 << 16) | (1 << 17));
        }
    }
    if live == 0 {
        return Ok(());
    }
    for succ in successors(func, block)? {
        if visited.insert((succ, live)) {
            scratch_dead_from(func, succ, 0, live, visited)?;
        }
    }
    Ok(())
}

fn fallthrough_effects(func: &MachFunction, block: usize, window: &Window) -> Result<(), String> {
    let after = window.brk_pos + 1;
    if window.wrote_flags {
        nzcv_dead_from(func, block, after, &mut HashSet::new())
            .map_err(|why| format!("NZCV may be live after the window: {why}"))?;
    }
    let mut live = 0u32;
    for key in &window.written {
        if let RegKey::Gpr(n) = key {
            live |= 1 << n;
        }
    }
    if live != 0 {
        scratch_dead_from(func, block, after, live, &mut HashSet::new())
            .map_err(|why| format!("an IP scratch register may be live after the window: {why}"))?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Rows
// ---------------------------------------------------------------------------

fn failed(detail: String) -> InstructionVerificationResult {
    InstructionVerificationResult::Failed {
        proof_name: TRAP_GUARD_FAILED.to_string(),
        detail: format!("{TRAP_GUARD_TAG} {detail}"),
    }
}

fn refused(reason: String) -> InstructionVerificationResult {
    InstructionVerificationResult::Unverified {
        reason: format!("{TRAP_GUARD_REFUSED}: {reason}"),
    }
}

fn bound_role(reason: String) -> InstructionVerificationResult {
    InstructionVerificationResult::Skipped {
        reason: format!("{TRAP_GUARD_BOUND_ROLE}: {reason}"),
    }
}

/// What this module decides for one instruction row (module documentation,
/// "Where this sits"). An instruction it has no objection to gets none.
#[derive(Debug, Clone)]
pub(crate) enum TrapGuardRow {
    /// A failure, a refusal or a bound unconditional role: merged into the
    /// function verifier's own row by [`combine`].
    Row(InstructionVerificationResult),
    /// The window or carrier holds, but no replayed LIR source is available
    /// to bind it: the function verifier's own row stands unless it would be
    /// promotable, and then it is refused with this reason.
    NoSource(String),
}

/// How strongly a row blocks: a failure over a refusal over everything else.
fn row_severity(row: &InstructionVerificationResult) -> u8 {
    match row {
        InstructionVerificationResult::Failed { .. } => 2,
        InstructionVerificationResult::Unverified { .. } => 1,
        InstructionVerificationResult::Skipped { .. }
        | InstructionVerificationResult::Verified { .. } => 0,
    }
}

/// Merge this module's decision for a row into the row the function verifier
/// would otherwise write (`base`; `base_promotable` says whether the
/// emitted-opcode inventory would count it as promotable).
///
/// A [`TrapGuardRow::Row`] replaces a milder base row (a failure or refusal
/// of this module over a promotable row, a bound role over the trap-expansion
/// verdict's skipped unconditional trap). Where both block, the more severe
/// kind wins and both texts are kept, this module's first unless the base row
/// alone fails. A [`TrapGuardRow::NoSource`] refuses a promotable base row and
/// keeps any other.
pub(crate) fn combine(
    own: &TrapGuardRow,
    base: InstructionVerificationResult,
    base_promotable: bool,
) -> InstructionVerificationResult {
    use InstructionVerificationResult as R;
    match own {
        TrapGuardRow::NoSource(reason) => {
            if base_promotable {
                refused(reason.clone())
            } else {
                base
            }
        }
        TrapGuardRow::Row(own) => match (own, base) {
            (
                R::Failed { proof_name, detail },
                R::Failed {
                    proof_name: base_name,
                    detail: base_detail,
                },
            ) => R::Failed {
                proof_name: proof_name.clone(),
                detail: format!("{detail}; and {base_name}: {base_detail}"),
            },
            (
                R::Unverified { reason },
                R::Failed {
                    proof_name: base_name,
                    detail: base_detail,
                },
            ) => R::Failed {
                proof_name: base_name,
                detail: format!("{base_detail}; and {reason}"),
            },
            (
                R::Unverified { reason },
                R::Unverified {
                    reason: base_reason,
                },
            ) => R::Unverified {
                reason: format!("{reason}; and {base_reason}"),
            },
            (own, base) if row_severity(&base) > row_severity(own) => base,
            (own, _) => own.clone(),
        },
    }
}

/// Everything known about one recorded carrier's window.
#[derive(Debug, Clone)]
struct WindowJudgement {
    /// Rows that carry the verdict.
    members: Vec<InstId>,
    check: WindowCheck,
    binding: Option<SourceBinding>,
    effects: Option<Result<(), String>>,
    describe: String,
    length: usize,
}

impl WindowJudgement {
    /// The source guard this window accounts for: the one its stamp names,
    /// when the window executes, holds against its carrier, and the carrier
    /// implements that guard's kind and constants (an operand width that
    /// does not bind leaves the row refused but the trap present).
    fn accounts(&self) -> Option<SourceInstId> {
        match &self.check {
            WindowCheck::Holds { .. } => self
                .binding
                .as_ref()
                .and_then(SourceBinding::implemented_source),
            _ => None,
        }
    }

    /// This module's decision for the window's rows: `None` when the window
    /// holds, executes, binds to its stamped source and leaves NZCV and its
    /// scratch registers dead (the rows are then the function verifier's own).
    fn verdict(&self) -> Option<TrapGuardRow> {
        let row = |result| Some(TrapGuardRow::Row(result));
        match &self.check {
            WindowCheck::Missing(why) | WindowCheck::Refuted(why) => {
                return row(failed(format!("{}: {why}", self.describe)));
            }
            WindowCheck::Unmodeled(why) => {
                return row(refused(format!("{}: {why}", self.describe)));
            }
            WindowCheck::Undecided(why) => {
                return row(refused(format!("{}: undecided: {why}", self.describe)));
            }
            WindowCheck::Holds { .. } => {}
        }
        if let Some(SourceBinding::Mismatch(why)) = &self.binding {
            return row(failed(format!("{}: {why}", self.describe)));
        }
        let WindowCheck::Holds { directed, sampled } = &self.check else {
            unreachable!("every non-holding check returned above");
        };
        let holds = format!(
            "the {}-instruction window traps exactly when the carrier's condition holds on {directed} \
             directed points (each agreeing with Rust's native arithmetic) and {sampled} sampled \
             inputs",
            self.length
        );
        let mut problems = Vec::new();
        if let Some(Err(why)) = &self.effects {
            problems.push(why.clone());
        }
        match &self.binding {
            Some(SourceBinding::Bound { .. }) => {}
            Some(SourceBinding::Unbound { why, .. }) => problems.push(why.clone()),
            Some(SourceBinding::NoSource(why)) if problems.is_empty() => {
                return Some(TrapGuardRow::NoSource(format!(
                    "{}: {holds}, but {why}",
                    self.describe
                )));
            }
            Some(SourceBinding::NoSource(why)) => problems.push(why.clone()),
            Some(SourceBinding::Mismatch(_)) | None => {
                problems.push("the carrier is unbound".to_string());
            }
        }
        if problems.is_empty() {
            None
        } else {
            row(refused(format!(
                "{}: {holds}, but {}",
                self.describe,
                problems.join("; and ")
            )))
        }
    }
}

/// Every recorded expansion as (its first instruction, the carrier it
/// rewrote). The late expansion reuses the carrier's `InstId` for the first
/// instruction it emits, so that id locates the window and carries the
/// carrier's TV-1 stamp. A record with no instruction locates nothing.
fn recorded_carriers(func: &MachFunction) -> impl Iterator<Item = (InstId, &MachInst)> {
    func.trap_expansions
        .iter()
        .filter_map(|record| record.insts.first().map(|&id| (id, &record.carrier)))
}

/// Function-wide facts every window judgement reads.
struct WindowContext<'a> {
    func: &'a MachFunction,
    lir: Option<&'a LirSourceIndex>,
    retained_source: Option<&'a trust_cg_lower::Function>,
    config: &'a VerificationConfig,
    /// The first instruction of every recorded window: no window's scan may
    /// run into another's.
    starts: HashSet<InstId>,
    /// Blocks of the emitted layout (`block_order`, the encoded domain) with
    /// the layout word of their first instruction. A block outside it is an
    /// arena shell the encoder never emits.
    block_word: HashMap<usize, i64>,
    /// Laid-out blocks reachable along the recorded successor edges from the
    /// entry, every landing pad and the stack-limit overflow block.
    reachable: HashSet<usize>,
    /// Every layout word some branch of the final stream may transfer to: the
    /// resolved word displacement of every branch in the layout, wherever it
    /// sits and whether or not it is itself reached (an over-approximation, so
    /// a window is never called dead while some branch could reach it). A
    /// symbolic `Block` operand, a jump table, a landing pad and a call
    /// return reach only a block's first instruction or a fall-through.
    targets: HashSet<i64>,
    /// The overflow block of a stack-limit check the U10 net
    /// ([`crate::aarch64_stack_limit::check`]) certifies on this stream with
    /// a `Trap` overflow action, or why there is none.
    stack_limit_trap_block: Result<usize, String>,
}

impl<'a> WindowContext<'a> {
    fn new(
        func: &'a MachFunction,
        lir: Option<&'a LirSourceIndex>,
        retained_source: Option<&'a trust_cg_lower::Function>,
        config: &'a VerificationConfig,
    ) -> Self {
        let mut block_word = HashMap::new();
        let mut targets = HashSet::new();
        let mut word = 0i64;
        for block in &func.block_order {
            let block = block.0 as usize;
            if block >= func.blocks.len() || block_word.contains_key(&block) {
                continue;
            }
            block_word.insert(block, word);
            for id in &func.blocks[block].insts {
                let Some(inst) = func.insts.get(id.0 as usize) else {
                    continue;
                };
                // Branch resolution counts exactly the non-pseudo
                // instructions, one word each.
                if inst.is_pseudo() {
                    continue;
                }
                if let Some(d) = resolved_displacement(inst) {
                    targets.insert(word + d);
                }
                word += 1;
            }
        }
        let stack_limit_trap_block = certified_stack_limit_trap_block(func);
        let mut roots = vec![func.entry.0 as usize];
        roots.extend(
            func.eh_metadata
                .landing_pads
                .iter()
                .map(|pad| pad.block.0 as usize),
        );
        // The overflow block is entered by the check's `B.LO`, an edge the
        // recorded successors need not carry; it is a root only where the
        // stack-limit net certifies that check.
        roots.extend(stack_limit_trap_block.as_ref().ok().copied());
        let mut reachable = HashSet::new();
        while let Some(block) = roots.pop() {
            if !block_word.contains_key(&block) || !reachable.insert(block) {
                continue;
            }
            roots.extend(func.blocks[block].succs.iter().map(|s| s.0 as usize));
        }
        Self {
            func,
            lir,
            retained_source,
            config,
            starts: recorded_carriers(func).map(|(id, _)| id).collect(),
            block_word,
            reachable,
            targets,
            stack_limit_trap_block,
        }
    }

    /// Whether the instruction at `pos` of `block` is shown to execute.
    ///
    /// A block outside the emitted layout, or one the recorded successor
    /// edges do not reach, is refused: the edges are a claim this module does
    /// not re-derive. Inside a reached block a forward walk keeps the
    /// position live through every instruction that falls through; after a
    /// `RET`, `B`, `BR`, tail call or unskipped trap it is live again only at
    /// a word some branch of the function targets. A position that walk
    /// leaves dead can never execute: that is a missing trap.
    fn executes(&self, block: usize, pos: usize) -> Result<(), WindowCheck> {
        let Some(&first_word) = self.block_word.get(&block) else {
            return Err(WindowCheck::Unmodeled(format!(
                "block {block} holding the window is not in the emitted layout (`block_order`), \
                 so the window is never encoded"
            )));
        };
        if !self.reachable.contains(&block) {
            return Err(WindowCheck::Unmodeled(format!(
                "block {block} holding the window is not reached from the entry, a landing pad or \
                 the stack-limit overflow block along the recorded successor edges, so the window \
                 is not shown to execute"
            )));
        }
        let mut live = true;
        let mut word = first_word;
        let mut stopper = None;
        for (p, id) in self.func.blocks[block].insts.iter().enumerate() {
            let inst = self.func.insts.get(id.0 as usize).ok_or_else(|| {
                WindowCheck::Unmodeled("a malformed instruction reference".into())
            })?;
            let encoded = !inst.is_pseudo();
            if encoded && self.targets.contains(&word) {
                live = true;
            }
            if p == pos {
                return if live {
                    Ok(())
                } else {
                    Err(WindowCheck::Missing(format!(
                        "the window follows {stopper:?} in block {block}, which does not fall \
                         through, and no branch of the function targets it: the window never \
                         executes, so the trap is missing"
                    )))
                };
            }
            if live && ends_without_fallthrough(inst) {
                live = false;
                stopper = Some(inst.opcode);
            }
            if encoded {
                word += 1;
            }
        }
        Err(WindowCheck::Unmodeled(format!(
            "block position {pos} is outside block {block}"
        )))
    }
}

/// The resolved word displacement of a branch (its last operand, after branch
/// resolution replaced the block operand), relative to the branch's own word.
fn resolved_displacement(inst: &MachInst) -> Option<i64> {
    match (inst.opcode, inst.operands.last()) {
        (
            Op::B | Op::BCond | Op::Bcc | Op::Cbz | Op::Cbnz | Op::Tbz | Op::Tbnz | Op::TailCall,
            Some(MachOperand::Imm(d)),
        ) => Some(*d),
        _ => None,
    }
}

fn judge_window(
    ctx: &WindowContext<'_>,
    block: usize,
    start: usize,
    id0: InstId,
    carrier: &MachInst,
) -> WindowJudgement {
    let func = ctx.func;
    let unjudged = |check: WindowCheck, describe: String| WindowJudgement {
        members: vec![id0],
        check,
        binding: None,
        effects: None,
        describe,
        length: 0,
    };
    let kind = match carrier_kind(carrier) {
        Ok(kind) => kind,
        Err(why) => {
            return unjudged(
                WindowCheck::Unmodeled(why),
                format!("recorded carrier {:?}", carrier.opcode),
            );
        }
    };
    let describe = format!("{:?} {}", carrier.opcode, kind.describe());
    let names = RoleNames::for_carrier(carrier);
    let window = match decode_window(func, block, start, &names, kind.constant(), &ctx.starts) {
        Ok(window) => window,
        Err(WindowError { fault, members }) => {
            // A malformed window outside the executed code is refused for
            // that, not failed for its shape: it is never run.
            let check = match (ctx.executes(block, start), fault) {
                (Err(WindowCheck::Unmodeled(why)), _) => WindowCheck::Unmodeled(why),
                (_, WindowFault::Missing(why)) => WindowCheck::Missing(why),
                (_, WindowFault::Unmodeled(why)) => WindowCheck::Unmodeled(why),
            };
            return WindowJudgement {
                members,
                check,
                binding: None,
                effects: None,
                describe,
                length: 0,
            };
        }
    };
    // A window that never executes cannot stand for its source guard: dead
    // code after a non-falling-through instruction is a missing trap (FAILS),
    // and a block outside the layout or the recorded edges is refused.
    if let Err(check) = ctx.executes(block, start) {
        return WindowJudgement {
            members: window.insts.clone(),
            check,
            binding: None,
            effects: None,
            describe,
            length: window.insts.len(),
        };
    }
    let check = check_window(carrier, kind, &names, &window, ctx.config);
    let binding = bind_source(func, id0, carrier, kind, ctx.lir);
    let effects = fallthrough_effects(func, block, &window);
    WindowJudgement {
        members: vec![window.skip, window.brk],
        check,
        binding: Some(binding),
        effects: Some(effects),
        describe,
        length: window.insts.len(),
    }
}

/// Names a call to a runtime routine that never returns.
fn noreturn_call_symbol(inst: &MachInst) -> Option<&'static str> {
    if !matches!(inst.opcode, Op::Bl | Op::BL) {
        return None;
    }
    let [MachOperand::Symbol(name), ..] = inst.operands.as_slice() else {
        return None;
    };
    [
        trust_cg_lower::RuntimeSymbol::UnwindResume,
        trust_cg_lower::RuntimeSymbol::StackChkFail,
    ]
    .into_iter()
    .map(trust_cg_lower::RuntimeSymbol::name)
    .find(|symbol| *symbol == name.as_str())
}

/// Whether a source opcode is a guard an exact carrier implements.
fn is_source_guard(opcode: &LirOpcode) -> bool {
    matches!(
        opcode,
        LirOpcode::GuardNull { .. }
            | LirOpcode::GuardDivZero { .. }
            | LirOpcode::GuardShiftRange { .. }
            | LirOpcode::GuardBoundsCheck { .. }
            | LirOpcode::GuardBoundsCheckDyn { .. }
            | LirOpcode::GuardOverflow { .. }
    )
}

/// The overflow block of the stack-limit check the U10 net
/// ([`crate::aarch64_stack_limit::check`]) certifies on `func`'s final stream
/// with a `Trap` overflow action, or why there is none. The function's
/// `stack_limit` and `stack_limit_overflow_block` fields are claims; only the
/// net's certificate makes the overflow block the stack-limit trap's.
fn certified_stack_limit_trap_block(func: &MachFunction) -> Result<usize, String> {
    use crate::aarch64_stack_limit::{StackLimitOutcome, check};
    if func.stack_limit.is_none() || func.stack_limit_overflow_block.is_none() {
        return Err("the function declares no stack-limit check with an overflow block".into());
    }
    match check(func) {
        Ok(Some(certificate)) => match certificate.outcome {
            StackLimitOutcome::Checked(checked)
                if checked.overflow == trust_cg_ir::StackLimitOverflow::Trap =>
            {
                Ok(checked.overflow_block.0 as usize)
            }
            StackLimitOutcome::Checked(checked) => Err(format!(
                "the certified check's overflow action is {:?}, not the trap",
                checked.overflow
            )),
            StackLimitOutcome::Elided => Err(
                "the stack-limit net certifies the check's elision, so no overflow block runs"
                    .into(),
            ),
        },
        Ok(None) => Err("the function requests no stack limit".into()),
        Err(violation) => Err(format!(
            "the stack-limit net refuses the stream ({violation})"
        )),
    }
}

/// Whether an instruction transfers control (or may), so a trap after it in
/// its block is not reached exactly when the block is entered.
fn transfers_control(inst: &MachInst) -> bool {
    matches!(
        inst.opcode,
        Op::B
            | Op::BCond
            | Op::Bcc
            | Op::Cbz
            | Op::Cbnz
            | Op::Tbz
            | Op::Tbnz
            | Op::Br
            | Op::Ret
            | Op::TailCall
            | Op::Brk
    ) || is_bare_trap(inst.opcode)
        || is_exact_carrier(inst.opcode)
}

/// What this module decides for one trap opcode no recorded carrier covers:
/// its row, and the source trap it accounts for.
#[derive(Debug, Default)]
struct Unrecorded {
    row: Option<TrapGuardRow>,
    accounts: Option<SourceInstId>,
}

impl Unrecorded {
    fn row(result: InstructionVerificationResult) -> Self {
        Self {
            row: Some(TrapGuardRow::Row(result)),
            accounts: None,
        }
    }
}

/// An exact carrier still in the stream (before the late expansion): bound
/// to its stamped source like a window's carrier, its trap condition left to
/// the trap-expansion verdict on its stated expansion. A carrier this module
/// cannot model is refused; one that never executes is a missing trap.
fn classify_unexpanded_carrier(
    ctx: &WindowContext<'_>,
    block: usize,
    pos: usize,
    id: InstId,
    inst: &MachInst,
) -> Unrecorded {
    let describe = format!("un-expanded exact guard carrier {:?}", inst.opcode);
    let kind = match carrier_kind(inst) {
        Ok(kind) => kind,
        Err(why) => return Unrecorded::row(refused(format!("{describe}: {why}"))),
    };
    match ctx.executes(block, pos) {
        Ok(()) => {}
        Err(WindowCheck::Missing(why)) => {
            return Unrecorded::row(failed(format!("{describe}: {why}")));
        }
        Err(other) => return Unrecorded::row(refused(format!("{describe}: {other:?}"))),
    }
    let binding = bind_source(ctx.func, id, inst, kind, ctx.lir);
    let accounts = binding.implemented_source();
    let row = match binding {
        SourceBinding::Bound { .. } => None,
        SourceBinding::Mismatch(why) => {
            Some(TrapGuardRow::Row(failed(format!("{describe}: {why}"))))
        }
        SourceBinding::Unbound { why, .. } => {
            Some(TrapGuardRow::Row(refused(format!("{describe}: {why}"))))
        }
        SourceBinding::NoSource(why) => Some(TrapGuardRow::NoSource(format!("{describe}: {why}"))),
    };
    Unrecorded { row, accounts }
}

/// The row of a trap opcode no recorded carrier covers, and the source trap
/// it accounts for (module documentation, "Unconditional traps").
fn classify_unrecorded(
    ctx: &WindowContext<'_>,
    block: usize,
    pos: usize,
    id: InstId,
    inst: &MachInst,
) -> Unrecorded {
    let (func, lir) = (ctx.func, ctx.lir);
    let op = inst.opcode;
    if is_exact_carrier(op) {
        return classify_unexpanded_carrier(ctx, block, pos, id, inst);
    }
    let bare = is_bare_trap(op);
    if op != Op::Brk && !bare {
        return Unrecorded::default();
    }
    let row = Unrecorded::row;
    let insts = &func.blocks[block].insts;
    let previous = pos
        .checked_sub(1)
        .and_then(|p| insts.get(p))
        .and_then(|id| func.insts.get(id.0 as usize));
    if previous.and_then(skip_branch_displacement) == Some(2) {
        return row(refused(format!(
            "{op:?} sits at the fall-through of a +2 skip branch but no guard carrier is \
             recorded for that window, so its condition is bound to nothing"
        )));
    }
    if bare {
        // Lowering emits a bare trap pseudo only where `expand_trap_*`
        // degrades a malformed exact carrier, and it keeps the carrier's
        // stamp: a guard's degraded carrier traps whether or not the guard's
        // condition holds.
        if let Ok((_, source)) = stamped_source(func, id, lir)
            && is_source_guard(&source.opcode)
        {
            return row(failed(format!(
                "a guard carrier for `{}` degraded to {op:?}, an unconditional BRK #1: it traps \
                 whenever reached, also where the source condition is false",
                source.opcode_debug
            )));
        }
        return row(refused(format!(
            "bare trap pseudo {op:?} (an unconditional BRK #1) has no recorded carrier and no \
             bound source role"
        )));
    }
    if !is_trap_word(inst) {
        return row(refused(format!(
            "BRK with operands {:?} is not a trap word",
            inst.operands
        )));
    }
    let last_in_block = pos + 1 == insts.len();
    // The U10 stack-limit trap: `BRK #0x534c` in the declared overflow block,
    // bound only where the stack-limit net certifies the check that enters
    // it. Frame insertion emits it with no source stamp; a stamp names a
    // source the role does not implement. It accounts for no source trap.
    if let [MachOperand::Imm(imm)] = inst.operands.as_slice()
        && *imm == i64::from(STACK_LIMIT_TRAP_IMM)
        && func.stack_limit.is_some()
        && func.stack_limit_overflow_block == Some(BlockId(block as u32))
    {
        let what = format!("stack-limit overflow trap BRK #{STACK_LIMIT_TRAP_IMM:#x}");
        if let LoweringProvenance::SourceInst { id: source, .. } = func.inst_lowering_provenance(id)
        {
            return row(refused(format!(
                "{what} carries a source stamp ({}, {}); frame insertion emits the stack-limit \
                 trap with none, so its role is not bound",
                source.block, source.index
            )));
        }
        return match &ctx.stack_limit_trap_block {
            Ok(certified) if *certified == block && insts.len() == 1 => row(bound_role(format!(
                "the U10 {what}, alone in the overflow block of the stack-limit check the \
                 stack-limit net certifies on this stream"
            ))),
            Ok(certified) => row(refused(format!(
                "{what} is not alone in the certified overflow block (the net certifies block \
                 {certified}, this is block {block} with {} instruction(s))",
                insts.len()
            ))),
            Err(why) => row(refused(format!("{what}: its role is not certified: {why}"))),
        };
    }
    // The unreachable BRK closing a block after a call that never returns.
    // Its role names no source trap: a stamp that names one contradicts it.
    // It accounts for no source trap.
    if last_in_block && let Some(symbol) = previous.and_then(noreturn_call_symbol) {
        if let Ok((_, source)) = stamped_source(func, id, lir)
            && needs_emitted_trap(&source.opcode)
        {
            return row(refused(format!(
                "BRK after the call to `{symbol}` carries the stamp of the source trap `{}`, \
                 which the unreachable word after a noreturn call does not implement",
                source.opcode_debug
            )));
        }
        return row(bound_role(format!(
            "unreachable BRK closing its block after the call to `{symbol}`, which never returns"
        )));
    }
    match stamped_source(func, id, lir) {
        Ok((source_id, source)) if matches!(source.opcode, LirOpcode::Trap) => {
            classify_source_trap(ctx, block, pos, last_in_block, source_id)
        }
        Ok((source_id, source)) if matches!(source.opcode, LirOpcode::Assert) => {
            // The trap of an `Assert` exists where its stamped BRK executes;
            // the row stays refused.
            let accounts = ctx.executes(block, pos).is_ok().then_some(source_id);
            Unrecorded {
                accounts,
                ..row(refused(
                    "BRK of an `Assert` trap block: the CMP/B.EQ that guards it sits in a \
                     predecessor block, and that cross-block window is not modeled"
                        .into(),
                ))
            }
        }
        Ok((_, source)) => row(refused(format!(
            "BRK stamped with source `{}` has no modeled trap role",
            source.opcode_debug
        ))),
        Err(why) => row(refused(format!(
            "BRK has no bound role: not a recorded guard window, not after a noreturn call, not \
             the stack-limit trap, and {why}"
        ))),
    }
}

/// A `BRK` stamped with a source `Trap`. It must close its block and execute
/// (in the layout, on a reached block, not dead code: a dead one is a missing
/// trap and FAILS); then it accounts for the `Trap`. Its role is bound only
/// where its placement is exact: the source `Trap` closes the LIR entry
/// block, and the `BRK` closes the machine entry block with no control
/// transfer before it, so both trap exactly when the function runs its entry
/// block to the end. A counted-loop terminal can also expose checked local
/// premises for a later source-bound proof. Its row still needs
/// correspondence of header visits and of the normal call continuation.
fn classify_source_trap(
    ctx: &WindowContext<'_>,
    block: usize,
    pos: usize,
    last_in_block: bool,
    source: SourceInstId,
) -> Unrecorded {
    if !last_in_block {
        return Unrecorded::row(refused(
            "BRK stamped as the source `Trap` is not the last instruction of its block".into(),
        ));
    }
    match ctx.executes(block, pos) {
        Ok(()) => {}
        Err(WindowCheck::Missing(why)) => {
            return Unrecorded::row(failed(format!("the source `Trap`'s BRK: {why}")));
        }
        Err(other) => {
            return Unrecorded::row(refused(format!(
                "the source `Trap`'s BRK is not shown to execute: {other:?}"
            )));
        }
    }
    let func = ctx.func;
    let insts = &func.blocks[block].insts;
    let entry_block = block == func.entry.0 as usize;
    let straight = insts[..pos]
        .iter()
        .filter_map(|id| func.insts.get(id.0 as usize))
        .all(|inst| !transfers_control(inst));
    let source_entry = ctx
        .lir
        .is_some_and(|index| index.entry_block() == source.block);
    let result = if entry_block && straight && source_entry {
        bound_role(
            "BRK is the source `Trap` terminator of the entry block its TV-1 stamp names, and \
             closes the machine entry block with no control transfer before it: both trap \
             exactly when the function runs its entry block to the end (the word is pinned by \
             the A64 decode-check)"
                .to_string(),
        )
    } else if let Some(reason) = ctx
        .retained_source
        .filter(|_| ctx.config.replays_source_bound_obligations())
        .and_then(|lir| crate::aarch64_terminal_trap::describe(lir, func, insts[pos], source))
    {
        refused(reason)
    } else {
        refused(
            "BRK is the source `Trap` terminator its TV-1 stamp names and executes, but it is \
             reached through branches whose polarity against the source's control flow this \
             obligation does not check"
                .to_string(),
        )
    };
    Unrecorded {
        accounts: Some(source),
        ..Unrecorded::row(result)
    }
}

/// How strongly a decision of this module blocks: a failure over a refusal
/// over a missing source over a bound role. Windows never overlap (no scan
/// runs into another recorded window), so two carriers' verdicts meeting on
/// one row is defense in depth, not an expected case.
fn severity(row: &TrapGuardRow) -> u8 {
    match row {
        TrapGuardRow::Row(InstructionVerificationResult::Failed { .. }) => 3,
        TrapGuardRow::Row(InstructionVerificationResult::Unverified { .. }) => 2,
        TrapGuardRow::NoSource(_) => 1,
        TrapGuardRow::Row(
            InstructionVerificationResult::Skipped { .. }
            | InstructionVerificationResult::Verified { .. },
        ) => 0,
    }
}

/// Record `row` for `id` unless a row at least as severe is already there:
/// two judgements reaching one instruction never let a later, milder verdict
/// overwrite an earlier failure.
fn merge_row(rows: &mut HashMap<InstId, TrapGuardRow>, id: InstId, row: TrapGuardRow) {
    match rows.get(&id) {
        Some(existing) if severity(existing) >= severity(&row) => {}
        _ => {
            rows.insert(id, row);
        }
    }
}

/// This module's decisions for one function, keyed by instruction, and its
/// function-level accounting.
#[derive(Debug)]
pub(crate) struct TrapAnalysis {
    rows: HashMap<InstId, TrapGuardRow>,
    accounting: Result<(), TrapGuardAccountingFailure>,
}

impl TrapAnalysis {
    /// This module's decision for `id`; `None` where it has no objection.
    pub(crate) fn row_for(&self, id: InstId) -> Option<&TrapGuardRow> {
        self.rows.get(&id)
    }

    /// The function-level accounting ([`account`]).
    pub(crate) fn accounting(&self) -> Result<(), TrapGuardAccountingFailure> {
        self.accounting.clone()
    }
}

/// Decide every trap row of `func` and the function's trap accounting (see
/// the module documentation).
pub(crate) fn analyze(
    func: &MachFunction,
    lir: Option<&LirSourceIndex>,
    retained_source: Option<&trust_cg_lower::Function>,
    config: &VerificationConfig,
) -> TrapAnalysis {
    let mut rows = HashMap::new();
    // Source traps an executing trap row that implements them accounts for.
    let mut accounted: HashSet<SourceInstId> = HashSet::new();
    let mut position: HashMap<InstId, (usize, usize)> = HashMap::new();
    for (b, block) in func.blocks.iter().enumerate() {
        for (p, &id) in block.insts.iter().enumerate() {
            position.entry(id).or_insert((b, p));
        }
    }
    // Every instruction a recorded expansion emitted is judged with its
    // window (or by the trap-expansion verdict), never as an unrecorded trap.
    let mut judged: HashSet<InstId> = func
        .trap_expansions
        .iter()
        .flat_map(|record| record.insts.iter().copied())
        .collect();
    let ctx = WindowContext::new(func, lir, retained_source, config);
    for (id0, carrier) in recorded_carriers(func) {
        // A record whose window is in no block has no row to carry its
        // missing trap: [`account`] fails the function for it.
        let Some(&(block, start)) = position.get(&id0) else {
            continue;
        };
        let Some(first) = func.insts.get(id0.0 as usize) else {
            continue;
        };
        if is_bare_trap(first.opcode) {
            merge_row(
                &mut rows,
                id0,
                TrapGuardRow::Row(failed(format!(
                    "the exact carrier `{:?} {:?}` degraded to {:?}, an unconditional BRK #1: it \
                     traps whenever reached, also where the source condition is false",
                    carrier.opcode, carrier.operands, first.opcode
                ))),
            );
            continue;
        }
        // Each carrier is judged on its own; its verdict lands on its own
        // rows, merged monotonically.
        let judgement = judge_window(&ctx, block, start, id0, carrier);
        judged.extend(judgement.members.iter().copied());
        accounted.extend(judgement.accounts());
        if let Some(row) = judgement.verdict() {
            for id in &judgement.members {
                merge_row(&mut rows, *id, row.clone());
            }
        }
    }
    for (b, block) in func.blocks.iter().enumerate() {
        for (p, &id) in block.insts.iter().enumerate() {
            if judged.contains(&id) || rows.contains_key(&id) {
                continue;
            }
            let Some(inst) = func.insts.get(id.0 as usize) else {
                continue;
            };
            let unrecorded = classify_unrecorded(&ctx, b, p, id, inst);
            accounted.extend(unrecorded.accounts);
            if let Some(row) = unrecorded.row {
                rows.insert(id, row);
            }
        }
    }
    TrapAnalysis {
        rows,
        accounting: accounting(func, lir, retained_source, &position, &accounted),
    }
}

// ---------------------------------------------------------------------------
// Source accounting
// ---------------------------------------------------------------------------

/// A function-level trap verdict no instruction row can carry (see the
/// module documentation, "Source accounting").
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrapGuardAccountingFailure {
    /// Recorded carriers whose window's first instruction is in no block of
    /// the function: the expansion emitted a trap the final function no longer
    /// has. A missing trap: this FAILS the function.
    pub absent_windows: Vec<String>,
    /// Source guard, `Assert` and `Trap` instructions no executing trap row
    /// that implements them accounts for: removed by a pass whose evidence
    /// this verifier does not check, dropped, moved out of the executed code,
    /// or carried only by a row that does not implement them. This REFUSES
    /// the function.
    pub unaccounted_sources: Vec<String>,
}

impl TrapGuardAccountingFailure {
    /// Whether a recorded window is absent (a missing trap), not only an
    /// unaccounted source trap (a refusal).
    pub fn has_missing_window(&self) -> bool {
        !self.absent_windows.is_empty()
    }
}

impl std::fmt::Display for TrapGuardAccountingFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut parts = Vec::new();
        if !self.absent_windows.is_empty() {
            parts.push(format!(
                "{TRAP_GUARD_FAILED}: missing trap: {} recorded guard window(s) are in no block of \
                 the function: {}",
                self.absent_windows.len(),
                self.absent_windows.join(", ")
            ));
        }
        if !self.unaccounted_sources.is_empty() {
            parts.push(format!(
                "{TRAP_GUARD_REFUSED}: {} source trap instruction(s) are accounted for by no \
                 executing trap row that implements them (removed by a pass whose evidence this \
                 verifier does not check, dropped, moved out of the executed code, or carried \
                 only by a row that does not implement them): {}",
                self.unaccounted_sources.len(),
                self.unaccounted_sources.join(", ")
            ));
        }
        f.write_str(&parts.join("; "))
    }
}

/// Whether a source instruction must be accounted for by an emitted trap.
fn needs_emitted_trap(opcode: &LirOpcode) -> bool {
    matches!(
        opcode,
        LirOpcode::GuardNull { .. }
            | LirOpcode::GuardDivZero { .. }
            | LirOpcode::GuardShiftRange { .. }
            | LirOpcode::GuardBoundsCheck { .. }
            | LirOpcode::GuardBoundsCheckDyn { .. }
            | LirOpcode::GuardOverflow { .. }
            | LirOpcode::Assert
            | LirOpcode::Trap
    )
}

/// A `GuardDivZero` whose divisor the replayed LIR defines as an `Iconst`
/// that is nonzero at its width can never trap; instruction selection elides
/// it (`select_guard_div_zero`). The width rule is the selector's.
fn statically_untrapping_div_zero(index: &LirSourceIndex, source: &LirSourceInst) -> bool {
    use crate::provenance_xcheck::LirValueOrigin;
    if !matches!(source.opcode, LirOpcode::GuardDivZero { .. }) {
        return false;
    }
    let [LirValueOrigin::Def { id }] = source.value_flow.args.as_slice() else {
        return false;
    };
    let Some(LirOpcode::Iconst { ty, imm }) = index.get(*id).map(|def| &def.opcode) else {
        return false;
    };
    let width = match ty {
        LirType::I8 => 8,
        LirType::I16 => 16,
        LirType::I32 => 32,
        _ => 64,
    };
    mask(*imm as u64, width) != 0
}

/// The function-level trap accounting (module documentation, "Source
/// accounting") of `func`, as the function verifier decides it. It runs the
/// whole trap-guard analysis; the verifier reads the same result from the
/// analysis it already made.
pub fn account(
    func: &MachFunction,
    lir: Option<&LirSourceIndex>,
    config: &VerificationConfig,
) -> Result<(), TrapGuardAccountingFailure> {
    analyze(func, lir, None, config).accounting()
}

/// Every recorded expansion's first instruction is in a block of the
/// function, and, with the replayed LIR, every source guard, `Assert` and
/// `Trap` must have an executing carrier or an exact omission proof. The
/// latter covers constant-nonzero division guards and one retained-source
/// contradictory branch shape with independently checked machine guards.
/// A stamp alone accounts for nothing: neither the
/// stack-limit trap, nor the `BRK` after a noreturn call, nor any row that
/// does not implement the source trap it names.
fn accounting(
    func: &MachFunction,
    lir: Option<&LirSourceIndex>,
    retained_source: Option<&trust_cg_lower::Function>,
    position: &HashMap<InstId, (usize, usize)>,
    accounted: &HashSet<SourceInstId>,
) -> Result<(), TrapGuardAccountingFailure> {
    let absent_windows: Vec<String> = recorded_carriers(func)
        .filter(|(id, _)| !position.contains_key(id))
        .map(|(id, carrier)| {
            format!(
                "`{:?} {:?}` recorded at instruction {}",
                carrier.opcode, carrier.operands, id.0
            )
        })
        .collect();
    let mut unaccounted_sources = Vec::new();
    if let Some(index) = lir {
        for (id, source) in index.sorted() {
            if !needs_emitted_trap(&source.opcode)
                || accounted.contains(&id)
                || statically_untrapping_div_zero(index, source)
                || (matches!(source.opcode, LirOpcode::Trap)
                    && retained_source.is_some_and(|lir| {
                        crate::aarch64_omitted_trap::allows_omission(lir, func, id)
                    }))
            {
                continue;
            }
            unaccounted_sources.push(format!(
                "`{}` at LIR ({}, {})",
                source.opcode_debug, id.block, id.index
            ));
        }
    }
    if absent_windows.is_empty() && unaccounted_sources.is_empty() {
        Ok(())
    } else {
        Err(TrapGuardAccountingFailure {
            absent_windows,
            unaccounted_sources,
        })
    }
}

// ---------------------------------------------------------------------------
// Shape catalog, mutation controls and the window model's self-check
// ---------------------------------------------------------------------------
//
// The coverage gate credits the carrier rows by the trap-expansion family
// (`aarch64_trap_expansion::trap_expansion_credit`). The family below checks
// this module's own window model, which vetoes rows, against the live
// expansions: every catalog shape holds and every negative control is
// refuted.

/// One window shape `trust_cg_codegen::lower::expand_trap_*` emits, as this
/// module models it: the carrier and the instructions its expansion produces.
///
/// The catalog is a second statement of the expansions, so it can drift from
/// them; `tests/aarch64_trap_guard_obligations.rs` runs the real expansion on
/// every catalog carrier and requires the identical instruction sequence.
#[derive(Debug, Clone)]
pub struct TrapGuardShape {
    /// Stable shape name.
    pub name: &'static str,
    /// The carrier as it stands before expansion.
    pub carrier: MachInst,
    /// The window its expansion emits, in order, ending with the `BRK`.
    pub window: Vec<MachInst>,
}

fn x(n: u16) -> MachOperand {
    MachOperand::PReg(trust_cg_ir::PReg::new(n))
}

fn w(n: u16) -> MachOperand {
    MachOperand::PReg(trust_cg_ir::PReg::new(32 + n))
}

fn imm(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}

fn mi(op: Op, operands: Vec<MachOperand>) -> MachInst {
    MachInst::new(op, operands)
}

fn skip(cc: trust_cg_ir::CondCode) -> MachInst {
    mi(Op::BCond, vec![imm(i64::from(cc.encoding())), imm(2)])
}

/// Every window shape the five expansions emit, one representative register
/// assignment and constant each: for every carrier kind, every register width
/// its expansion accepts (null and divide-by-zero on W or X; shift range on W
/// or X; the bounds index on W or X with an imm12, a MOVZ or a MOVZ+MOVK
/// bound, or a length of the index's width; add and subtract overflow at 32
/// and 64 bits; multiply overflow at 64 bits only, a 32-bit multiply tag
/// degrading to a bare trap), and every idiom. A register-length bounds check
/// whose index and length differ in width has no shape: its `CMP` does not
/// encode, and the window model refuses it.
pub fn trap_guard_shape_catalog() -> Vec<TrapGuardShape> {
    use trust_cg_ir::CondCode as Cc;
    let brk = || mi(Op::Brk, vec![]);
    let shape = |name, carrier, window| TrapGuardShape {
        name,
        carrier,
        window,
    };
    let mut shapes = vec![
        shape(
            "null_x",
            mi(Op::TrapNullIfZero, vec![x(0)]),
            vec![mi(Op::Cbnz, vec![x(0), imm(2)]), brk()],
        ),
        shape(
            "null_w",
            mi(Op::TrapNullIfZero, vec![w(0)]),
            vec![mi(Op::Cbnz, vec![w(0), imm(2)]), brk()],
        ),
        shape(
            "div_zero_x",
            mi(Op::TrapDivZeroIfZero, vec![x(1)]),
            vec![mi(Op::Cbnz, vec![x(1), imm(2)]), brk()],
        ),
        shape(
            "div_zero_w",
            mi(Op::TrapDivZeroIfZero, vec![w(1)]),
            vec![mi(Op::Cbnz, vec![w(1), imm(2)]), brk()],
        ),
        shape(
            "shift_range_w32",
            mi(Op::TrapShiftRangeIfOOB, vec![w(2), imm(32)]),
            vec![mi(Op::CmpRI, vec![w(2), imm(32)]), skip(Cc::LO), brk()],
        ),
        shape(
            "shift_range_x64",
            mi(Op::TrapShiftRangeIfOOB, vec![x(2), imm(64)]),
            vec![mi(Op::CmpRI, vec![x(2), imm(64)]), skip(Cc::LO), brk()],
        ),
        shape(
            "bounds_imm12",
            mi(Op::TrapBoundsCheckExact, vec![x(3), x(4), imm(10)]),
            vec![mi(Op::CmpRI, vec![x(4), imm(10)]), skip(Cc::LO), brk()],
        ),
        shape(
            "bounds_movz",
            mi(Op::TrapBoundsCheckExact, vec![x(3), x(4), imm(0x1234)]),
            vec![
                mi(Op::Movz, vec![x(16), imm(0x1234)]),
                mi(Op::CmpRR, vec![x(4), x(16)]),
                skip(Cc::LO),
                brk(),
            ],
        ),
        shape(
            "bounds_movz_movk",
            mi(Op::TrapBoundsCheckExact, vec![x(3), x(4), imm(0x12_3456)]),
            vec![
                mi(Op::Movz, vec![x(16), imm(0x3456)]),
                mi(Op::Movk, vec![x(16), imm(0x12), imm(16)]),
                mi(Op::CmpRR, vec![x(4), x(16)]),
                skip(Cc::LO),
                brk(),
            ],
        ),
        shape(
            "bounds_dyn",
            mi(Op::TrapBoundsCheckExact, vec![x(3), x(4), x(5)]),
            vec![mi(Op::CmpRR, vec![x(4), x(5)]), skip(Cc::LO), brk()],
        ),
        shape(
            "bounds_imm12_w",
            mi(Op::TrapBoundsCheckExact, vec![x(3), w(4), imm(10)]),
            vec![mi(Op::CmpRI, vec![w(4), imm(10)]), skip(Cc::LO), brk()],
        ),
        shape(
            "bounds_movz_w",
            mi(Op::TrapBoundsCheckExact, vec![x(3), w(4), imm(0x1234)]),
            vec![
                mi(Op::Movz, vec![w(16), imm(0x1234)]),
                mi(Op::CmpRR, vec![w(4), w(16)]),
                skip(Cc::LO),
                brk(),
            ],
        ),
        shape(
            "bounds_movz_movk_w",
            mi(Op::TrapBoundsCheckExact, vec![x(3), w(4), imm(0x12_3456)]),
            vec![
                mi(Op::Movz, vec![w(16), imm(0x3456)]),
                mi(Op::Movk, vec![w(16), imm(0x12), imm(16)]),
                mi(Op::CmpRR, vec![w(4), w(16)]),
                skip(Cc::LO),
                brk(),
            ],
        ),
        shape(
            "bounds_dyn_w",
            mi(Op::TrapBoundsCheckExact, vec![x(3), w(4), w(5)]),
            vec![mi(Op::CmpRR, vec![w(4), w(5)]), skip(Cc::LO), brk()],
        ),
    ];
    for (name, op, width, cc) in [
        ("overflow_sadd_32", OverflowOp::SignedAdd, 32, Cc::VC),
        ("overflow_sadd_64", OverflowOp::SignedAdd, 64, Cc::VC),
        ("overflow_ssub_32", OverflowOp::SignedSub, 32, Cc::VC),
        ("overflow_ssub_64", OverflowOp::SignedSub, 64, Cc::VC),
        ("overflow_uadd_32", OverflowOp::UnsignedAdd, 32, Cc::LO),
        ("overflow_uadd_64", OverflowOp::UnsignedAdd, 64, Cc::LO),
        ("overflow_usub_32", OverflowOp::UnsignedSub, 32, Cc::HS),
        ("overflow_usub_64", OverflowOp::UnsignedSub, 64, Cc::HS),
    ] {
        let (l, r, zr) = if width == 32 {
            (w(6), w(7), MachOperand::Special(SpecialReg::WZR))
        } else {
            (x(6), x(7), MachOperand::Special(SpecialReg::XZR))
        };
        let setter = if matches!(op, OverflowOp::SignedSub | OverflowOp::UnsignedSub) {
            Op::SubsRR
        } else {
            Op::AddsRR
        };
        let tag = trust_cg_ir::pack_overflow_tag(op, width);
        shapes.push(shape(
            name,
            mi(Op::TrapOverflowExact, vec![l.clone(), r.clone(), imm(tag)]),
            vec![mi(setter, vec![zr, l, r]), skip(cc), brk()],
        ));
    }
    let smul = trust_cg_ir::pack_overflow_tag(OverflowOp::SignedMul, 64);
    let umul = trust_cg_ir::pack_overflow_tag(OverflowOp::UnsignedMul, 64);
    shapes.push(shape(
        "overflow_smul_64",
        mi(Op::TrapOverflowExact, vec![x(6), x(7), imm(smul)]),
        vec![
            mi(Op::MulRR, vec![x(16), x(6), x(7)]),
            mi(Op::Smulh, vec![x(17), x(6), x(7)]),
            mi(Op::AsrRI, vec![x(16), x(16), imm(63)]),
            mi(Op::CmpRR, vec![x(17), x(16)]),
            skip(Cc::EQ),
            brk(),
        ],
    ));
    shapes.push(shape(
        "overflow_umul_64",
        mi(Op::TrapOverflowExact, vec![x(6), x(7), imm(umul)]),
        vec![
            mi(Op::Umulh, vec![x(16), x(6), x(7)]),
            mi(Op::CmpRI, vec![x(16), imm(0)]),
            skip(Cc::EQ),
            brk(),
        ],
    ));
    shapes
}

/// One mutation of a catalog window the trap-guard obligation must refute.
#[derive(Debug, Clone)]
pub struct TrapGuardControl {
    /// The shape it mutates.
    pub shape: &'static str,
    /// What was changed.
    pub mutation: String,
    /// The mutated window.
    pub window: Vec<MachInst>,
}

/// The register a window's guard test reads first (the operand a "wrong
/// register" or "wrong width" control replaces).
fn tested_operand(inst: &MachInst) -> Option<usize> {
    match inst.opcode {
        Op::Cbnz | Op::Cbz | Op::CmpRI | Op::CmpRR => Some(0),
        Op::AddsRR | Op::SubsRR | Op::Umulh => Some(2),
        Op::Smulh => Some(2),
        _ => None,
    }
}

fn other_view(op: &MachOperand) -> Option<MachOperand> {
    match reg_ref(op)? {
        RegRef::Reg {
            key: RegKey::Gpr(n),
            width: 64,
        } => Some(w(u16::from(n))),
        RegRef::Reg {
            key: RegKey::Gpr(n),
            width: 32,
        } => Some(x(u16::from(n))),
        _ => None,
    }
}

/// The negative controls of one catalog shape: an inverted skip condition, a
/// condition reading another flag, a different tested register, the other
/// register width, an off-by-one constant, the other flag setter, and three
/// ways of losing the trap. Each must be refuted, not merely left unbound.
pub fn trap_guard_controls(shape: &TrapGuardShape) -> Vec<TrapGuardControl> {
    let mut controls = Vec::new();
    let mut push = |mutation: String, window: Vec<MachInst>| {
        controls.push(TrapGuardControl {
            shape: shape.name,
            mutation,
            window,
        });
    };
    let skip_at = shape
        .window
        .iter()
        .position(|inst| skip_branch_displacement(inst).is_some())
        .expect("every catalog window has a skip branch");
    let skip_inst = &shape.window[skip_at];

    // Inverted condition.
    let mut inverted = shape.window.clone();
    match skip_inst.opcode {
        Op::BCond => {
            if let MachOperand::Imm(cc) = &mut inverted[skip_at].operands[0] {
                *cc ^= 1;
            }
        }
        Op::Cbnz => inverted[skip_at].opcode = Op::Cbz,
        _ => {}
    }
    push("inverted skip condition".into(), inverted);

    // A condition that reads a different flag.
    if skip_inst.opcode == Op::BCond {
        let mut wrong_flag = shape.window.clone();
        if let MachOperand::Imm(cc) = &mut wrong_flag[skip_at].operands[0] {
            // EQ/LO/HS/VC read Z/C/C/V; MI and PL read N.
            *cc = if *cc == 2 || *cc == 7 { 5 } else { 4 };
        }
        push("skip condition reads another flag".into(), wrong_flag);
    }

    // A different tested register, and the other width of the tested one.
    let tested =
        (0..skip_at + 1).find_map(|i| tested_operand(&shape.window[i]).map(|operand| (i, operand)));
    if let Some((i, operand)) = tested {
        let original = shape.window[i].operands[operand].clone();
        let mut wrong_register = shape.window.clone();
        wrong_register[i].operands[operand] = match shape.window[i].opcode {
            // SMULH reading the left operand twice.
            Op::Smulh => shape.window[i].operands[1].clone(),
            _ => match reg_ref(&original) {
                Some(RegRef::Reg { width: 32, .. }) => w(9),
                _ => x(9),
            },
        };
        push(
            format!("{:?} tests a different register", shape.window[i].opcode),
            wrong_register,
        );
        if !matches!(shape.window[i].opcode, Op::Smulh | Op::Umulh) {
            let mut wrong_width = shape.window[i].clone();
            for op in wrong_width.operands.iter_mut() {
                if let Some(view) = other_view(op) {
                    *op = view;
                } else if let MachOperand::Special(SpecialReg::XZR) = op {
                    *op = MachOperand::Special(SpecialReg::WZR);
                } else if let MachOperand::Special(SpecialReg::WZR) = op {
                    *op = MachOperand::Special(SpecialReg::XZR);
                }
            }
            let mut window = shape.window.clone();
            window[i] = wrong_width;
            push(
                format!(
                    "{:?} tests the other register width",
                    shape.window[i].opcode
                ),
                window,
            );
        }
    }

    // An off-by-one constant.
    if let Some(i) = shape
        .window
        .iter()
        .position(|inst| matches!(inst.opcode, Op::CmpRI | Op::Movz | Op::Movk))
    {
        let mut off = shape.window.clone();
        if let MachOperand::Imm(v) = &mut off[i].operands[1] {
            *v += 1;
        }
        push(
            format!("{:?} constant off by one", shape.window[i].opcode),
            off,
        );
    }

    // The other flag setter.
    if let Some(i) = shape
        .window
        .iter()
        .position(|inst| matches!(inst.opcode, Op::AddsRR | Op::SubsRR))
    {
        let mut swapped = shape.window.clone();
        swapped[i].opcode = if swapped[i].opcode == Op::AddsRR {
            Op::SubsRR
        } else {
            Op::AddsRR
        };
        push("the other flag-setting instruction".into(), swapped);
    }

    // The trap lost three ways.
    let brk_at = shape.window.len() - 1;
    let mut dropped = shape.window.clone();
    dropped.remove(brk_at);
    push("BRK dropped".into(), dropped);
    let mut displaced = shape.window.clone();
    if let Some(MachOperand::Imm(d)) = displaced[skip_at].operands.last_mut() {
        *d = 3;
    }
    push("skip displacement 3".into(), displaced);
    let mut nop = shape.window.clone();
    nop[brk_at] = mi(Op::Nop, vec![]);
    push("BRK replaced by NOP".into(), nop);
    controls
}

/// A one-block function holding `window` then `RET`, with `carrier` recorded
/// as the expansion of the window's instructions, as `expand_trap_*` leaves
/// it.
fn catalog_function(carrier: &MachInst, window: &[MachInst]) -> MachFunction {
    let mut func = MachFunction::new(
        "trap_guard_catalog".to_string(),
        trust_cg_ir::Signature::new(vec![], vec![]),
    );
    for inst in window.iter().cloned().chain([mi(Op::Ret, vec![])]) {
        let id = func.push_inst(inst);
        func.blocks[0].insts.push(id);
    }
    let insts = func.blocks[0].insts[..window.len()].to_vec();
    func.trap_expansions.push(trust_cg_ir::TrapExpansionRecord {
        carrier: carrier.clone(),
        insts,
    });
    func
}

/// What a successful self-check of the window model establishes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrapGuardCredit {
    /// Window shapes whose obligation held.
    pub shapes: usize,
    /// Directed points those obligations agreed on (with the native oracle).
    pub directed_points: usize,
    /// Mutation controls refuted (each by refutation or a missing trap).
    pub controls_refuted: usize,
}

/// The window model's self-check over [`trap_guard_shape_catalog`] and its
/// [`trap_guard_controls`], at the default evaluator configuration. Cached.
/// Evaluation evidence about this module's model, never proof credit.
pub fn trap_guard_credit() -> Result<TrapGuardCredit, String> {
    static CREDIT: OnceLock<Result<TrapGuardCredit, String>> = OnceLock::new();
    CREDIT
        .get_or_init(|| {
            let shapes = trap_guard_shape_catalog();
            let controls: Vec<_> = shapes.iter().flat_map(trap_guard_controls).collect();
            trap_guard_credit_with(&shapes, &controls, &VerificationConfig::default())
        })
        .clone()
}

/// [`trap_guard_credit`] over injected shapes and controls, so a test can hand
/// it a wrong window or a surviving control and watch it refuse.
///
/// Refuses unless every shape's window holds against its carrier (directed
/// battery with the native oracle, then the sampling lane) with its
/// fall-through effects dead, and every control is refuted or loses its trap.
pub fn trap_guard_credit_with(
    shapes: &[TrapGuardShape],
    controls: &[TrapGuardControl],
    config: &VerificationConfig,
) -> Result<TrapGuardCredit, String> {
    let mut directed_points = 0;
    for shape in shapes {
        let func = catalog_function(&shape.carrier, &shape.window);
        let id0 = func.blocks[0].insts[0];
        let judgement = judge_window(
            &WindowContext::new(&func, None, None, config),
            0,
            0,
            id0,
            &shape.carrier,
        );
        match &judgement.check {
            WindowCheck::Holds { directed, .. } => directed_points += directed,
            other => {
                return Err(format!(
                    "shape `{}`: the window does not hold against its carrier: {other:?}",
                    shape.name
                ));
            }
        }
        if let Some(Err(why)) = &judgement.effects {
            return Err(format!("shape `{}`: {why}", shape.name));
        }
    }
    let mut controls_refuted = 0;
    for control in controls {
        let carrier = shapes
            .iter()
            .find(|shape| shape.name == control.shape)
            .map(|shape| &shape.carrier)
            .ok_or_else(|| format!("control for unknown shape `{}`", control.shape))?;
        let func = catalog_function(carrier, &control.window);
        let id0 = func.blocks[0].insts[0];
        let judgement = judge_window(
            &WindowContext::new(&func, None, None, config),
            0,
            0,
            id0,
            carrier,
        );
        match &judgement.check {
            WindowCheck::Refuted(_) | WindowCheck::Missing(_) => controls_refuted += 1,
            other => {
                return Err(format!(
                    "control `{}` of shape `{}` survives: {other:?}",
                    control.mutation, control.shape
                ));
            }
        }
    }
    Ok(TrapGuardCredit {
        shapes: shapes.len(),
        directed_points,
        controls_refuted,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_verifier::{FunctionVerifier, OpcodeInventoryStatus};

    fn verify(func: &MachFunction) -> crate::function_verifier::FunctionVerificationReport {
        FunctionVerifier::new().verify(func)
    }

    fn row(
        report: &crate::function_verifier::FunctionVerificationReport,
        index: usize,
    ) -> &InstructionVerificationResult {
        &report.instructions[index].result
    }

    fn function(insts: Vec<MachInst>) -> MachFunction {
        let mut func = MachFunction::new(
            "trap_guard_unit".to_string(),
            trust_cg_ir::Signature::new(vec![], vec![]),
        );
        for inst in insts {
            let id = func.push_inst(inst);
            func.blocks[0].insts.push(id);
        }
        func
    }

    fn shape(name: &str) -> TrapGuardShape {
        trap_guard_shape_catalog()
            .into_iter()
            .find(|shape| shape.name == name)
            .unwrap_or_else(|| panic!("no catalog shape {name}"))
    }

    /// Record `carrier` as the expansion that emitted `insts`.
    fn record(func: &mut MachFunction, carrier: &MachInst, insts: &[InstId]) {
        func.trap_expansions.push(trust_cg_ir::TrapExpansionRecord {
            carrier: carrier.clone(),
            insts: insts.to_vec(),
        });
    }

    /// Block 0 positions `range` of `func`, as instruction ids.
    fn ids(func: &MachFunction, range: std::ops::Range<usize>) -> Vec<InstId> {
        func.blocks[0].insts[range].to_vec()
    }

    fn is_expansion_not_credit(row: &InstructionVerificationResult) -> bool {
        matches!(row, InstructionVerificationResult::Unverified { reason }
            if reason.starts_with(crate::aarch64_trap_expansion::TRAP_EXPANSION_IS_NOT_CREDIT))
    }

    #[test]
    fn every_catalog_shape_holds_and_every_control_is_refuted() {
        let shapes = trap_guard_shape_catalog();
        let controls: Vec<_> = shapes.iter().flat_map(trap_guard_controls).collect();
        assert_eq!(shapes.len(), 24, "five carriers, every width and idiom");
        let credit = trap_guard_credit().expect("the trap-guard family must hold");
        assert_eq!(credit.shapes, shapes.len());
        assert_eq!(credit.controls_refuted, controls.len());
        assert!(credit.directed_points >= shapes.len() * 16, "{credit:?}");
        // Every control class is exercised at least once.
        for class in [
            "inverted skip condition",
            "skip condition reads another flag",
            "tests a different register",
            "tests the other register width",
            "constant off by one",
            "the other flag-setting instruction",
            "BRK dropped",
            "skip displacement 3",
            "BRK replaced by NOP",
        ] {
            assert!(
                controls.iter().any(|c| c.mutation.contains(class)),
                "no control of class `{class}`"
            );
        }
        eprintln!(
            "trap-guard family: {} shapes, {} directed points, {} controls refuted",
            credit.shapes, credit.directed_points, credit.controls_refuted
        );
    }

    #[test]
    fn a_surviving_control_or_a_wrong_window_refuses_the_credit() {
        let shapes = trap_guard_shape_catalog();
        // A "control" that is the faithful window survives: refused.
        let faithful = TrapGuardControl {
            shape: shapes[0].name,
            mutation: "faithful copy".into(),
            window: shapes[0].window.clone(),
        };
        let err = trap_guard_credit_with(&shapes, &[faithful], &VerificationConfig::default())
            .expect_err("a surviving control must refuse the credit");
        assert!(err.contains("survives"), "{err}");
        // A shape whose window is wrong (CBZ for CBNZ) does not hold: refused.
        let mut wrong = shapes[0].clone();
        wrong.window[0].opcode = Op::Cbz;
        let err = trap_guard_credit_with(&[wrong], &[], &VerificationConfig::default())
            .expect_err("a wrong catalog window must refuse the credit");
        assert!(err.contains("does not hold"), "{err}");
    }

    /// Without a replayed LIR source a faithful window holds but is unbound:
    /// the CBNZ, which would be covered elsewhere, is refused by name, and the
    /// BRK keeps the trap-expansion verdict, uncredited without a replay.
    #[test]
    fn a_faithful_window_without_source_is_never_promotable() {
        let null = shape("null_x");
        let mut func = function(
            null.window
                .iter()
                .cloned()
                .chain([MachInst::new(Op::Ret, vec![])])
                .collect(),
        );
        let window = ids(&func, 0..2);
        record(&mut func, &null.carrier, &window);
        let report = verify(&func);
        let InstructionVerificationResult::Unverified { reason } = row(&report, 0) else {
            panic!("row 0: {:?}", row(&report, 0));
        };
        assert!(reason.starts_with(TRAP_GUARD_REFUSED), "{reason}");
        assert!(reason.contains("traps exactly when"), "{reason}");
        assert!(reason.contains("no replayed LIR source"), "{reason}");
        assert!(
            is_expansion_not_credit(row(&report, 1)),
            "{:?}",
            row(&report, 1)
        );
        let inventory = report.emitted_opcode_inventory();
        assert_eq!(
            inventory.entries[0].status,
            OpcodeInventoryStatus::Unverified
        );
        assert_eq!(
            inventory.entries[1].status,
            OpcodeInventoryStatus::Unverified
        );
        assert!(!inventory.is_promotable());
    }

    /// Every control fails the window rows of a verified function (not merely
    /// leaves them unbound).
    #[test]
    fn every_control_fails_its_rows_in_the_function_verifier() {
        for shape in trap_guard_shape_catalog() {
            for control in trap_guard_controls(&shape) {
                let mut func = function(
                    control
                        .window
                        .iter()
                        .cloned()
                        .chain([MachInst::new(Op::Ret, vec![])])
                        .collect(),
                );
                let window = ids(&func, 0..control.window.len());
                record(&mut func, &shape.carrier, &window);
                let report = verify(&func);
                assert!(
                    report.instructions.iter().any(|r| matches!(
                        &r.result,
                        InstructionVerificationResult::Failed { proof_name, .. }
                            if proof_name == TRAP_GUARD_FAILED
                    )),
                    "{} / {}: {:#?}",
                    shape.name,
                    control.mutation,
                    report.instructions
                );
                assert!(!report.emitted_opcode_inventory().is_promotable());
            }
        }
    }

    /// A recorded expansion whose first instruction is now a bare trap pseudo
    /// traps unconditionally where its carrier traps conditionally: FAILED.
    #[test]
    fn a_degraded_carrier_fails_as_an_unconditional_trap() {
        let mut func = function(vec![
            MachInst::new(Op::TrapNull, vec![]),
            MachInst::new(Op::Ret, vec![]),
        ]);
        let first = ids(&func, 0..1);
        record(
            &mut func,
            &MachInst::new(Op::TrapNullIfZero, vec![x(0)]),
            &first,
        );
        let report = verify(&func);
        let InstructionVerificationResult::Failed { detail, .. } = row(&report, 0) else {
            panic!("{:?}", row(&report, 0));
        };
        assert!(detail.contains("unconditional BRK #1"), "{detail}");
    }

    #[test]
    fn unrecorded_traps_are_refused_by_role() {
        // A bare BRK with no source: refused.
        let report = verify(&function(vec![MachInst::new(Op::Brk, vec![])]));
        let InstructionVerificationResult::Unverified { reason } = row(&report, 0) else {
            panic!("{:?}", row(&report, 0));
        };
        assert!(reason.contains("no bound role"), "{reason}");
        // A guard-shaped window with no recorded carrier: refused as unbound.
        let null = shape("null_x");
        let report = verify(&function(null.window.clone()));
        let InstructionVerificationResult::Unverified { reason } = row(&report, 1) else {
            panic!("{:?}", row(&report, 1));
        };
        assert!(reason.contains("no guard carrier is recorded"), "{reason}");
        // Every bare trap pseudo and every un-expanded exact carrier: refused.
        for op in [
            Op::TrapOverflow,
            Op::TrapBoundsCheck,
            Op::TrapNull,
            Op::TrapDivZero,
            Op::TrapShiftRange,
            Op::TrapNullIfZero,
            Op::TrapDivZeroIfZero,
            Op::TrapShiftRangeIfOOB,
            Op::TrapBoundsCheckExact,
            Op::TrapOverflowExact,
        ] {
            let report = verify(&function(vec![MachInst::new(op, vec![])]));
            let InstructionVerificationResult::Unverified { reason } = row(&report, 0) else {
                panic!("{op:?}: {:?}", row(&report, 0));
            };
            assert!(reason.starts_with(TRAP_GUARD_REFUSED), "{op:?}: {reason}");
            assert!(!report.emitted_opcode_inventory().is_promotable(), "{op:?}");
        }
    }

    /// The unreachable `BRK` after `_Unwind_Resume` keeps its bound role;
    /// the role is refused elsewhere, and the stack-limit trap word is
    /// refused wherever the stack-limit net does not certify its check.
    #[test]
    fn unconditional_roles_are_bound_only_where_established() {
        // The unreachable BRK closing a block after `_Unwind_Resume`.
        let report = verify(&function(vec![
            MachInst::new(
                Op::Bl,
                vec![MachOperand::Symbol("_Unwind_Resume".to_string())],
            ),
            MachInst::new(Op::Brk, vec![]),
        ]));
        let InstructionVerificationResult::Skipped { reason } = row(&report, 1) else {
            panic!("{:?}", row(&report, 1));
        };
        assert!(reason.starts_with(TRAP_GUARD_BOUND_ROLE), "{reason}");
        // Not the last instruction of its block, or after another callee:
        // refused.
        for insts in [
            vec![
                MachInst::new(
                    Op::Bl,
                    vec![MachOperand::Symbol("_Unwind_Resume".to_string())],
                ),
                MachInst::new(Op::Brk, vec![]),
                MachInst::new(Op::Ret, vec![]),
            ],
            vec![
                MachInst::new(Op::Bl, vec![MachOperand::Symbol("abort_ish".to_string())]),
                MachInst::new(Op::Brk, vec![]),
            ],
        ] {
            let report = verify(&function(insts));
            assert!(
                matches!(
                    row(&report, 1),
                    InstructionVerificationResult::Unverified { .. }
                ),
                "{:?}",
                row(&report, 1)
            );
        }
        // The stack-limit trap word in a declared overflow block, with no
        // check the stack-limit net certifies (no prologue, no compare): the
        // declaration is a claim, so the role is refused. A frame the net
        // certifies is `the_stack_limit_trap_keeps_its_role_only_where_certified`.
        let mut func = function(vec![MachInst::new(
            Op::Brk,
            vec![MachOperand::Imm(i64::from(STACK_LIMIT_TRAP_IMM))],
        )]);
        func.stack_limit_overflow_block = Some(BlockId(0));
        func.stack_limit = Some(trust_cg_ir::MachStackLimit {
            request: trust_cg_ir::StackLimitRequest {
                param: 0,
                source: trust_cg_ir::StackLimitSource::Value,
                overflow: trust_cg_ir::StackLimitOverflow::Trap,
            },
            limit_reg: trust_cg_ir::PReg::new(0),
            arg_regs: vec![trust_cg_ir::PReg::new(0)],
        });
        let report = verify(&func);
        assert!(
            matches!(row(&report, 0), InstructionVerificationResult::Unverified { reason }
                if reason.starts_with(TRAP_GUARD_REFUSED)
                    && reason.contains("its role is not certified")),
            "{:?}",
            row(&report, 0)
        );
        // The same word outside the overflow block: refused.
        func.stack_limit_overflow_block = None;
        let report = verify(&func);
        assert!(matches!(
            row(&report, 0),
            InstructionVerificationResult::Unverified { .. }
        ));
    }

    /// The fall-through must observe nothing of the window: a flag reader or
    /// an X16 reader after it refuses the skip branch (the trap-expansion
    /// verdict fails the `BRK` for the flag reader itself), and the X16
    /// reader, which that verdict does not look for, refuses the `BRK` too.
    #[test]
    fn live_flags_or_scratch_after_the_window_are_refused() {
        let shift = shape("shift_range_x64");
        let mut insts = shift.window.clone();
        insts.push(MachInst::new(
            Op::CSet,
            vec![
                MachOperand::PReg(trust_cg_ir::PReg::new(0)),
                MachOperand::Imm(0),
            ],
        ));
        insts.push(MachInst::new(Op::Ret, vec![]));
        let mut func = function(insts);
        let window = ids(&func, 0..shift.window.len());
        record(&mut func, &shift.carrier, &window);
        let report = verify(&func);
        let InstructionVerificationResult::Unverified { reason } = row(&report, 1) else {
            panic!("{:?}", row(&report, 1));
        };
        assert!(reason.contains("NZCV may be live"), "{reason}");
        assert!(row(&report, 2).is_failed(), "{:?}", row(&report, 2));

        let movz = shape("bounds_movz");
        let mut insts = movz.window.clone();
        insts.push(MachInst::new(Op::AddRR, vec![x(0), x(16), x(1)]));
        insts.push(MachInst::new(Op::Ret, vec![]));
        let mut func = function(insts);
        let window = ids(&func, 0..movz.window.len());
        record(&mut func, &movz.carrier, &window);
        let report = verify(&func);
        let InstructionVerificationResult::Unverified { reason } = row(&report, 3) else {
            panic!("{:?}", row(&report, 3));
        };
        assert!(
            reason.contains("IP scratch register may be live"),
            "{reason}"
        );
    }

    fn render(row: &TrapGuardRow) -> String {
        format!("{row:?}")
    }

    /// Rows merge monotonically in every order: a failure is never replaced
    /// by a refusal, a missing source or a bound role, a refusal never by a
    /// missing source or a bound role, and a missing source never by a bound
    /// role.
    #[test]
    fn rows_merge_monotonically_in_every_order() {
        let by_severity = [
            TrapGuardRow::Row(failed("refuted".into())),
            TrapGuardRow::Row(refused("unmodeled".into())),
            TrapGuardRow::NoSource("holds, no source".into()),
            TrapGuardRow::Row(bound_role("bound".into())),
        ];
        let id = InstId(7);
        for (i, first) in by_severity.iter().enumerate() {
            for (j, second) in by_severity.iter().enumerate() {
                let mut rows = HashMap::new();
                merge_row(&mut rows, id, first.clone());
                merge_row(&mut rows, id, second.clone());
                let kept = if i <= j { first } else { second };
                assert_eq!(
                    render(&rows[&id]),
                    render(kept),
                    "{} then {}",
                    render(first),
                    render(second)
                );
            }
        }
    }

    fn trap_failed_detail(
        report: &crate::function_verifier::FunctionVerificationReport,
        index: usize,
    ) -> String {
        match row(report, index) {
            InstructionVerificationResult::Failed { proof_name, detail }
                if proof_name == TRAP_GUARD_FAILED =>
            {
                detail.clone()
            }
            other => panic!("row {index}: expected a trap-guard failure, got {other:?}"),
        }
    }

    fn refusal(
        report: &crate::function_verifier::FunctionVerificationReport,
        index: usize,
    ) -> String {
        match row(report, index) {
            InstructionVerificationResult::Unverified { reason }
                if reason.starts_with(TRAP_GUARD_REFUSED) =>
            {
                reason.clone()
            }
            other => panic!("row {index}: expected a trap-guard refusal, got {other:?}"),
        }
    }

    /// A recorded window after a `RET` that no branch targets never runs: its
    /// trap is missing and its rows FAIL. A branch anywhere in the function
    /// that targets it keeps it live (it is then judged, never called dead).
    #[test]
    fn a_window_that_never_executes_fails() {
        let null = shape("null_x");
        let mut insts = vec![MachInst::new(Op::Ret, vec![])];
        insts.extend(null.window.iter().cloned());
        let mut func = function(insts);
        let window = ids(&func, 1..3);
        record(&mut func, &null.carrier, &window);
        let report = verify(&func);
        for index in [1, 2] {
            let detail = trap_failed_detail(&report, index);
            assert!(detail.contains("never executes"), "{detail}");
        }
        assert!(!report.emitted_opcode_inventory().is_promotable());

        // `B +2` over the `RET` targets the window's first word: it is live,
        // so it is judged (holding; the CBNZ is refused for want of a source
        // here, the BRK keeps the uncredited trap-expansion verdict).
        let mut insts = vec![
            MachInst::new(Op::B, vec![MachOperand::Imm(2)]),
            MachInst::new(Op::Ret, vec![]),
        ];
        insts.extend(null.window.iter().cloned());
        insts.push(MachInst::new(Op::Ret, vec![]));
        let mut func = function(insts);
        let window = ids(&func, 2..4);
        record(&mut func, &null.carrier, &window);
        let report = verify(&func);
        let reason = refusal(&report, 2);
        assert!(reason.contains("traps exactly when"), "{reason}");
        assert!(reason.contains("no replayed LIR source"), "{reason}");
        assert!(
            is_expansion_not_credit(row(&report, 3)),
            "{:?}",
            row(&report, 3)
        );
        assert_eq!(report.failed_count(), 0, "{:#?}", report.instructions);
    }

    /// A window in an arena block outside the emitted layout, or in a laid-out
    /// block the recorded edges do not reach, is refused: never credited, and
    /// never failed for its shape (a malformed one there is refused too).
    #[test]
    fn a_window_outside_the_layout_or_the_recorded_edges_is_refused() {
        let null = shape("null_x");
        for (laid_out, drop_brk) in [(false, false), (true, false), (false, true), (true, true)] {
            let mut func = function(vec![MachInst::new(Op::Ret, vec![])]);
            let window: Vec<InstId> = null
                .window
                .iter()
                .map(|inst| func.push_inst(inst.clone()))
                .collect();
            // A dropped BRK stays recorded but leaves the block.
            let mut body = window.clone();
            if drop_brk {
                body.pop();
            }
            body.push(func.push_inst(MachInst::new(Op::Ret, vec![])));
            func.blocks.push(trust_cg_ir::MachBlock {
                insts: body,
                preds: Vec::new(),
                succs: Vec::new(),
                loop_depth: 0,
            });
            if laid_out {
                func.block_order.push(BlockId(1));
            }
            record(&mut func, &null.carrier, &window);
            let report = verify(&func);
            let reason = refusal(&report, 1);
            let expected = if laid_out {
                "is not reached from the entry"
            } else {
                "is not in the emitted layout"
            };
            assert!(reason.contains(expected), "{laid_out} {drop_brk}: {reason}");
            assert_eq!(
                report.failed_count(),
                0,
                "{laid_out} {drop_brk}: {:#?}",
                report.instructions
            );
            assert!(!report.emitted_opcode_inventory().is_promotable());
        }
    }

    /// A malformed setup refuses the whole window, so the `BRK` states the
    /// carrier's actual reason rather than "no guard carrier is recorded".
    #[test]
    fn a_malformed_setup_puts_its_reason_on_the_brk() {
        let movz = shape("bounds_movz_w");
        let mut window = movz.window.clone();
        // The scratch at X16 against a W index: CMP widths disagree.
        window[0].operands[0] = x(16);
        window[1].operands[1] = x(16);
        let len = window.len();
        window.push(MachInst::new(Op::Ret, vec![]));
        let mut func = function(window);
        let expansion = ids(&func, 0..len);
        record(&mut func, &movz.carrier, &expansion);
        let report = verify(&func);
        let reason = refusal(&report, 3);
        assert!(
            reason.contains("is 64-bit where the instruction is 32-bit"),
            "{reason}"
        );
        assert!(!reason.contains("no guard carrier is recorded"), "{reason}");
    }

    /// The function-level accounting: a recorded window in no block is a
    /// missing trap (FAILED); without the replayed LIR nothing else is
    /// required.
    #[test]
    fn a_recorded_window_in_no_block_fails_the_function() {
        let null = shape("null_x");
        let mut func = function(vec![MachInst::new(Op::Ret, vec![])]);
        let orphan = func.push_inst(null.window[0].clone());
        record(&mut func, &null.carrier, &[orphan]);
        let config = VerificationConfig::default();
        let failure =
            account(&func, None, &config).expect_err("an absent window is a missing trap");
        assert!(failure.has_missing_window());
        assert!(failure.unaccounted_sources.is_empty());
        let text = failure.to_string();
        assert!(text.starts_with(TRAP_GUARD_FAILED), "{text}");
        let report = verify(&func);
        assert!(
            matches!(
                &report.precondition_failure,
                Some(crate::function_verifier::FunctionVerificationPreconditionFailure::TrapGuardAccounting(f))
                    if f.has_missing_window()
            ),
            "{:?}",
            report.precondition_failure
        );
        assert!(report.has_failures());
        assert!(!report.emitted_opcode_inventory().is_promotable());
        // The same function with its window in the block passes the
        // accounting (the window itself is then judged by row).
        func.blocks[0].insts.insert(0, orphan);
        assert_eq!(account(&func, None, &config), Ok(()));
    }
}
