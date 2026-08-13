// trust-cg-opt - Memory effects model
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Memory-effects model for machine instructions.
//!
//! Required for safe CSE, LICM, and DCE. Each opcode is classified as
//! Pure, Load, Store, or Call, which determines whether the instruction
//! can be reordered, eliminated, or hoisted.
//!
//! Reference: designs/2026-04-12-aarch64-backend.md, "Memory-Effects Model"
//!
//! | Effect | Meaning |
//! |--------|---------|
//! | Pure   | No memory access, no side effects. Safe to reorder, CSE, DCE. |
//! | Load   | Reads memory. Can be CSE'd with identical loads if no intervening store. |
//! | Store  | Writes memory. Barrier for loads and other stores. |
//! | Call   | Clobbers everything (conservative default). |

use trust_cg_ir::AArch64Opcode;
use trust_cg_ir::OpcodeCategory;
use trust_cg_ir::X86Opcode;
use trust_cg_lower::{X86ISelInst, X86ISelOperand};

/// Memory effect classification for an instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MemoryEffect {
    /// No memory access, no observable side effects.
    /// Safe to reorder, eliminate if unused, or CSE.
    Pure,
    /// Reads memory. May depend on prior stores.
    /// Can be CSE'd if no intervening store to the same location.
    Load,
    /// Writes memory. Acts as a barrier for loads and other stores.
    Store,
    /// Full memory barrier. Clobbers all registers and memory
    /// (conservative assumption for function calls).
    Call,
}

impl MemoryEffect {
    /// Returns true if this instruction has no memory side effects.
    /// Pure instructions can be safely eliminated if their result is unused.
    #[inline]
    pub fn is_pure(self) -> bool {
        self == Self::Pure
    }

    /// Returns true if this instruction reads memory.
    #[inline]
    pub fn reads_memory(self) -> bool {
        matches!(self, Self::Load | Self::Call)
    }

    /// Returns true if this instruction writes memory.
    #[inline]
    pub fn writes_memory(self) -> bool {
        matches!(self, Self::Store | Self::Call)
    }

    /// Returns true if this instruction is a memory barrier
    /// (prevents reordering of loads and stores across it).
    #[inline]
    pub fn is_barrier(self) -> bool {
        matches!(self, Self::Call)
    }
}

/// Classify the memory effect of an AArch64 opcode.
///
/// This is the authoritative source for memory effect information.
/// The classification is conservative: if in doubt, we classify as
/// having more effects rather than fewer (correctness over optimization).
pub fn opcode_effect(opcode: AArch64Opcode) -> MemoryEffect {
    use AArch64Opcode::*;
    match opcode {
        // -- Loads: read memory --
        LdrRI | LdrPreIndex | LdrPostIndex | LdrbRI | LdrhRI | LdrsbRI | LdrshRI | LdrLiteral
        | LdpRI | LdpPostIndex | LdrRO | LdrbRO | LdrhRO | LdrswRO | LdrGot | LdrTlvp
        | LdrGottprel | NeonLd1Post | NeonLdpQPost => MemoryEffect::Load,

        // -- Stores: write memory --
        StrRI | StrPreIndex | StrPostIndex | StrbRI | StrhRI | StpRI | StpPreIndex | StrRO
        | STRWui | STRXui | STRSui | STRDui | NeonSt1Post | NeonStpQPost => MemoryEffect::Store,

        // -- Volatile memory: full barrier --
        // A volatile access (MMIO / signal visibility) must never be elided,
        // CSE'd, forwarded, hoisted, or reordered. Classifying it as `Call`
        // (the strongest, most conservative effect) makes every effect-gated
        // pass treat it as an opaque barrier — stricter than C's volatile (which
        // only orders volatile-vs-volatile) but always sound. The opcode-
        // hardcoded passes (gvn/mem_pair/recurrence_store_forward) match the
        // PLAIN load/store opcodes, so they conservatively ignore these too.
        VolatileLdrRI | VolatileLdrbRI | VolatileLdrhRI | VolatileStrRI | VolatileStrbRI
        | VolatileStrhRI => MemoryEffect::Call,

        // -- Calls: full barrier --
        Bl | Blr | BL | BLR | TailCall => MemoryEffect::Call,

        // -- Stack allocation: side effect (modifies SP) --
        StackAlloc => MemoryEffect::Store,

        // -- Everything else: pure computation --
        // Arithmetic
        AddRR | AddRI | AddRIShift12 | SubRR | SubRI | MulRR | Msub | Smull | Umull | SDiv
        | UDiv | Neg => MemoryEffect::Pure,

        // Logical
        AndRR | AndRI | OrrRR | OrrRI | EorRR | EorRI | BicRR => MemoryEffect::Pure,

        // Shifts
        LslRR | LsrRR | AsrRR | LslRI | LsrRI | AsrRI | RorRI | Rbit => MemoryEffect::Pure,

        // Compare/test: these set flags but don't access memory.
        // Note: CMP/TST have HAS_SIDE_EFFECTS in InstFlags because they
        // write condition flags. DCE handles this via InstFlags, not
        // MemoryEffect. For memory-effect purposes, these are pure.
        CmpRR | CmpRI | CMPWrr | CMPXrr | CMPWri | CMPXri | Tst | Fcmp => MemoryEffect::Pure,

        // Conditional select/set: pure computation, no memory access.
        // FcselRR (scalar FP conditional select) is pure w.r.t. memory too — it
        // reads NZCV (see `reads_flags`) but touches no memory.
        Csel | CSet | Csinc | Csinv | Csneg | FcselRR => MemoryEffect::Pure,

        // Move (including LLVM-style typed aliases)
        MovR | MovI | Movz | Movn | Movk | FmovImm | MOVWrr | MOVXrr | MOVZWi | MOVZXi => {
            MemoryEffect::Pure
        }

        // Extension
        Sxtw | Uxtw | Sxtb | Sxth | Uxtb | Uxth => MemoryEffect::Pure,

        // Bitfield operations
        Ubfm | Sbfm | Bfm => MemoryEffect::Pure,

        // Logical (OR-NOT)
        OrnRR => MemoryEffect::Pure,

        // Logical with ROR-shifted source (EOR Rd, Rn, Rm, ROR #k): pure ALU.
        EorRRShift | EorRRLsl | EorRRLsr => MemoryEffect::Pure,

        // Arithmetic with a shifted source (ADD/SUB Rd, Rn, Rm, LSL #k and
        // ADD Rd, Rn, Rm, LSR #k): pure ALU.
        AddRRShift | SubRRShift | AddRRShiftLsr => MemoryEffect::Pure,

        // Floating-point arithmetic
        FaddRR | FsubRR | FmulRR | FdivRR | FmaddRR | FminnmRR | FmaxnmRR | FnegRR | FabsRR
        | FsqrtRR | FrintmRR | FrintpRR | FrintzRR => MemoryEffect::Pure,

        // NEON SIMD: pure computation (no memory access except LD1/ST1 above)
        NeonAddV | NeonSubV | NeonMulV | NeonFaddV | NeonFsubV | NeonFmulV | NeonFdivV
        | NeonFcmgtV | NeonAndV | NeonOrrV | NeonEorV | NeonBicV | NeonNotV | NeonRbitV
        | NeonRev32V | NeonRev64V | NeonCmeqV | NeonCmgtV | NeonCmgeV | NeonCmhiV | NeonCmhsV
        | NeonUmaxv | NeonSmaxV | NeonSminV | NeonUmaxV | NeonUminV | NeonAddpScalar
        | NeonDupElem | NeonDupGen | NeonInsGen | NeonUmovGen | NeonMovi | NeonShlVImm
        | NeonUshrVImm | NeonSshrVImm | NeonCntV | NeonUaddlpV | NeonSaddlpV | NeonAbsV
        | NeonUdotV | NeonBitV | NeonExtV | NeonSmlalV | NeonSmlal2V | NeonUmlalV | NeonUmlal2V
        | NeonUaddwV | NeonUaddw2V | NeonSaddwV | NeonSaddw2V | NeonMlaV | NeonUadalpV
        | NeonFmlaV | NeonFmlsV | NeonFmlaLaneV | NeonUcvtfV | NeonScvtfV | NeonFcvtlV
        | NeonFcvtl2V | NeonDupScalarD => MemoryEffect::Pure,

        // FP conversion
        FcvtzsRR | FcvtzuRR | ScvtfRR | UcvtfRR => MemoryEffect::Pure,

        // Float precision conversion
        FcvtSD | FcvtDS | FcvtHS | FcvtHD | FcvtSH | FcvtDH => MemoryEffect::Pure,

        // Bitcast (FMOV between GPR/FPR)
        FmovGprFpr | FmovFprGpr | FmovFprFpr => MemoryEffect::Pure,

        // Address computation (no memory access)
        Adrp | Adr | AddPCRel => MemoryEffect::Pure,
        // ELF local-exec TLS TPREL adds: pure ALU address arithmetic
        // (TPIDR_EL0 was read by the preceding Mrs, not here).
        AddTprelHi12 | AddTprelLo12 => MemoryEffect::Pure,

        // Checked arithmetic: set flags but no memory access
        AddsRR | AddsRI | SubsRR | SubsRI => MemoryEffect::Pure,

        // i128 multi-register arithmetic: pure computation (ADC/SBC read flags, no memory)
        Adc | Sbc | Umulh | Smulh | Madd => MemoryEffect::Pure,

        // Trap pseudo-instructions: control flow, not memory ops
        Brk | TrapOverflow | TrapBoundsCheck | TrapBoundsCheckExact | TrapNull | TrapNullIfZero
        | TrapDivZero | TrapDivZeroIfZero | TrapShiftRange | TrapShiftRangeIfOOB
        | TrapOverflowExact => MemoryEffect::Pure,

        // Reference counting: read and write memory (refcount field)
        Retain | Release => MemoryEffect::Store,

        // Atomic loads (load-acquire): memory read with ordering
        Ldar | Ldarb | Ldarh | Ldaxr => MemoryEffect::Load,

        // Atomic stores (store-release): memory write with ordering
        Stlr | Stlrb | Stlrh | Stlxr => MemoryEffect::Store,

        // Atomic RMW (LSE): both read and write — classify as Store (conservative)
        Ldadd | Ldadda | Ldaddal | Ldaddl | Ldclr | Ldclra | Ldclral | Ldclrl | Ldeor | Ldeora
        | Ldeoral | Ldeorl | Ldset | Ldseta | Ldsetal | Ldsetl | Ldsmax | Ldsmaxa | Ldsmaxal
        | Ldsmaxl | Ldsmin | Ldsmina | Ldsminal | Ldsminl | Ldumax | Ldumaxa | Ldumaxal
        | Ldumaxl | Ldumin | Ldumina | Lduminal | Lduminl | Swp | Swpa | Swpal | Swpl | Cas
        | Casa | Casal | Casl => MemoryEffect::Store,

        // Barriers: full memory barrier (acts like a call for ordering purposes)
        Dmb | Dsb | Isb => MemoryEffect::Call,

        // System register read (MRS): model as a Call for alias-analysis
        // purposes. This keeps MRS from being hoisted out of loops, sunk
        // past memory ops, or CSE'd across writes to the same sysreg.
        // TPIDR_EL0 specifically is thread-stable, but this opcode is the
        // umbrella for all sysregs (including performance counters), so the
        // conservative choice is a barrier-style classification.
        Mrs => MemoryEffect::Call,

        // Branches: not memory ops. DCE handles branches via InstFlags.
        B | BCond | Bcc | Cbz | Cbnz | Tbz | Tbnz | Br | Ret => MemoryEffect::Pure,

        // Pseudo-instructions
        Phi => MemoryEffect::Pure,
        Copy => MemoryEffect::Pure,
        Nop => MemoryEffect::Pure,

        // Emission-time alignment padding: an architectural NOP, no memory
        // effect. (Created only after every effect-gated pass has run; its
        // HAS_SIDE_EFFECTS InstFlags additionally pins it in place.)
        AlignNop => MemoryEffect::Pure,
    }
}

/// Returns true if this opcode produces a value (`operand[0]` is a def).
///
/// Instructions that don't produce values: CMP, TST, STR, STP, branches,
/// returns, NOP, calls, traps, and reference counting ops.
///
/// Delegates to [`AArch64Opcode::produces_value`] — the single source of
/// truth. This wrapper preserves the existing function signature for callers.
/// See issue #96.
pub fn produces_value(opcode: AArch64Opcode) -> bool {
    opcode.produces_value()
}

/// Returns true if this instruction produces a value.
///
/// Convenience wrapper around [`produces_value`] that takes a `MachInst`
/// reference instead of a bare opcode.
pub fn inst_produces_value(inst: &trust_cg_ir::MachInst) -> bool {
    produces_value(inst.opcode)
}

/// Explicit register-operand role used by passes that need AArch64 def/use
/// positions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperandRole {
    /// Operand is written by the instruction.
    Def,
    /// Operand is read by the instruction.
    Use,
    /// Operand is both read and written by the instruction.
    DefUse,
}

impl OperandRole {
    #[inline]
    pub fn is_def(self) -> bool {
        matches!(self, Self::Def | Self::DefUse)
    }

    #[inline]
    pub fn is_use(self) -> bool {
        matches!(self, Self::Use | Self::DefUse)
    }
}

/// Returns true for AArch64 LSE read-modify-write atomics whose old-value
/// destination is operand 1. Operand 0 is the update value and operand 2 is
/// the address register.
pub fn is_lse_rmw(opcode: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        opcode,
        Ldadd
            | Ldadda
            | Ldaddal
            | Ldaddl
            | Ldclr
            | Ldclra
            | Ldclral
            | Ldclrl
            | Ldeor
            | Ldeora
            | Ldeoral
            | Ldeorl
            | Ldset
            | Ldseta
            | Ldsetal
            | Ldsetl
            | Ldsmax
            | Ldsmaxa
            | Ldsmaxal
            | Ldsmaxl
            | Ldsmin
            | Ldsmina
            | Ldsminal
            | Ldsminl
            | Ldumax
            | Ldumaxa
            | Ldumaxal
            | Ldumaxl
            | Ldumin
            | Ldumina
            | Lduminal
            | Lduminl
            | Swp
            | Swpa
            | Swpal
            | Swpl
    )
}

/// Returns true for AArch64 LSE compare-and-swap atomics. Operand 0 is both
/// the expected-value input and the old-value result.
pub fn is_lse_cas(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::Cas | AArch64Opcode::Casa | AArch64Opcode::Casal | AArch64Opcode::Casl
    )
}

/// Returns true when operand 0 is explicitly both a def and a use.
pub fn operand_zero_is_def_use(opcode: AArch64Opcode) -> bool {
    is_lse_cas(opcode) || has_tied_def_use(opcode)
}

/// Classify explicit AArch64 operand roles for def/use consumers.
///
/// Most value-producing opcodes define operand 0. The exceptions captured
/// here are architectural operand layouts rather than scheduling policy:
/// - Single-register pre/post-index loads/stores define-use their base.
/// - `LdpRI` defines operands 0 and 1.
/// - `LdpPostIndex` defines operands 0 and 1 and define-uses its base.
/// - `StpPreIndex` / `NeonStpQPost` define-use their base (both data regs are uses).
/// - LSE RMW atomics define operand 1 and use the remaining operands.
/// - LSE CAS atomics define and use operand 0.
/// - MOVK/BFM/NEON INS define and use operand 0 because they preserve prior bits/lanes.
/// - NEON UDOT defines and uses operand 0 because it ACCUMULATES into Vd.
pub fn aarch64_operand_roles(opcode: AArch64Opcode, operand_count: usize) -> Vec<OperandRole> {
    let mut roles = vec![OperandRole::Use; operand_count];
    fill_operand_roles(opcode, &mut roles);
    roles
}

/// Fast-path inline capacity for the allocation-free role visitors. AArch64
/// machine instructions classified here never exceed this operand count in
/// practice; longer operand lists fall back to the heap [`aarch64_operand_roles`]
/// path (see the visitors below), so this is a performance threshold, never a
/// correctness bound.
const ROLE_INLINE_CAP: usize = 8;

/// Classify explicit AArch64 operand roles into a caller-provided slice.
///
/// `roles` must have length equal to the instruction's operand count and be
/// pre-initialized to [`OperandRole::Use`]. This is the single source of truth
/// for the role table; both the allocating [`aarch64_operand_roles`] and the
/// allocation-free visitors below delegate here so the classification content is
/// identical regardless of how the caller stores the result.
fn fill_operand_roles(opcode: AArch64Opcode, roles: &mut [OperandRole]) {
    let operand_count = roles.len();
    if operand_count == 0 {
        return;
    }

    match opcode {
        AArch64Opcode::NeonLd1Post => {
            roles[0] = OperandRole::Def;
            if operand_count > 1 {
                roles[1] = OperandRole::DefUse;
            }
            return;
        }
        // LDP Qt1, Qt2, [Xn], #imm — like LdpPostIndex: defines BOTH data
        // registers (operands 0 and 1) and define-uses the post-indexed base
        // (operand 2). Treating operand 1 as a plain use would let regalloc /
        // coalescing miss the second Q-register def (the exact "op0 is def"
        // class of P0 this table exists to prevent).
        AArch64Opcode::NeonLdpQPost => {
            for role in roles.iter_mut().take(2) {
                *role = OperandRole::Def;
            }
            if operand_count > 2 {
                roles[2] = OperandRole::DefUse;
            }
            return;
        }
        AArch64Opcode::NeonSt1Post => {
            if operand_count > 1 {
                roles[1] = OperandRole::DefUse;
            }
            return;
        }
        // STP Qt1, Qt2, [Xn], #imm — like StpPreIndex: BOTH data registers
        // (operands 0 and 1) are stored USES and the post-indexed base (operand
        // 2) is a def-use writeback. (The mirror of NeonLdpQPost, whose data
        // registers are DEFS instead.)
        AArch64Opcode::NeonStpQPost => {
            if operand_count > 2 {
                roles[2] = OperandRole::DefUse;
            }
            return;
        }
        AArch64Opcode::LdrPreIndex | AArch64Opcode::LdrPostIndex => {
            roles[0] = OperandRole::Def;
            if operand_count > 1 {
                roles[1] = OperandRole::DefUse;
            }
            return;
        }
        AArch64Opcode::StrPreIndex | AArch64Opcode::StrPostIndex => {
            if operand_count > 1 {
                roles[1] = OperandRole::DefUse;
            }
            return;
        }
        AArch64Opcode::LdpPostIndex => {
            for role in roles.iter_mut().take(2) {
                *role = OperandRole::Def;
            }
            if operand_count > 2 {
                roles[2] = OperandRole::DefUse;
            }
            return;
        }
        AArch64Opcode::StpPreIndex => {
            if operand_count > 2 {
                roles[2] = OperandRole::DefUse;
            }
            return;
        }
        _ => {}
    }

    if is_lse_rmw(opcode) {
        if operand_count > 1 {
            roles[1] = OperandRole::Def;
        }
        return;
    }

    if is_lse_cas(opcode) {
        roles[0] = OperandRole::DefUse;
        return;
    }

    if opcode == AArch64Opcode::LdpRI {
        for role in roles.iter_mut().take(2) {
            *role = OperandRole::Def;
        }
        return;
    }

    if produces_value(opcode) {
        roles[0] = if has_tied_def_use(opcode) {
            OperandRole::DefUse
        } else {
            OperandRole::Def
        };
    }
}

/// Invoke `f` with every explicit-operand role, without heap allocation for the
/// common case. Delegates to [`fill_operand_roles`], so the roles are identical
/// to [`aarch64_operand_roles`]; only the storage differs (inline stack array up
/// to [`ROLE_INLINE_CAP`], heap fallback beyond). Positions are visited in
/// ascending order, matching the `Vec`/`into_iter` callers.
#[inline]
fn for_each_operand_role(
    opcode: AArch64Opcode,
    operand_count: usize,
    mut f: impl FnMut(usize, OperandRole),
) {
    if operand_count <= ROLE_INLINE_CAP {
        let mut roles = [OperandRole::Use; ROLE_INLINE_CAP];
        let roles = &mut roles[..operand_count];
        fill_operand_roles(opcode, roles);
        for (pos, &role) in roles.iter().enumerate() {
            f(pos, role);
        }
    } else {
        for (pos, role) in aarch64_operand_roles(opcode, operand_count)
            .into_iter()
            .enumerate()
        {
            f(pos, role);
        }
    }
}

/// Invoke `f` for each explicit def-operand position, allocation-free. Identical
/// enumeration to [`aarch64_def_operand_positions`] without materializing a `Vec`.
#[inline]
pub fn aarch64_for_each_def_position(
    opcode: AArch64Opcode,
    operand_count: usize,
    mut f: impl FnMut(usize),
) {
    for_each_operand_role(opcode, operand_count, |pos, role| {
        if role.is_def() {
            f(pos);
        }
    });
}

/// Invoke `f` for each explicit use-operand position, allocation-free. Identical
/// enumeration to [`aarch64_use_operand_positions`] without materializing a `Vec`.
#[inline]
pub fn aarch64_for_each_use_position(
    opcode: AArch64Opcode,
    operand_count: usize,
    mut f: impl FnMut(usize),
) {
    for_each_operand_role(opcode, operand_count, |pos, role| {
        if role.is_use() {
            f(pos);
        }
    });
}

/// Return explicit operand positions written by an AArch64 opcode.
pub fn aarch64_def_operand_positions(opcode: AArch64Opcode, operand_count: usize) -> Vec<usize> {
    aarch64_operand_roles(opcode, operand_count)
        .into_iter()
        .enumerate()
        .filter_map(|(pos, role)| role.is_def().then_some(pos))
        .collect()
}

/// Return explicit operand positions read by an AArch64 opcode.
pub fn aarch64_use_operand_positions(opcode: AArch64Opcode, operand_count: usize) -> Vec<usize> {
    aarch64_operand_roles(opcode, operand_count)
        .into_iter()
        .enumerate()
        .filter_map(|(pos, role)| role.is_use().then_some(pos))
        .collect()
}

/// Returns true if an instruction with the given opcode can be safely
/// eliminated if its result is unused and it has no other side effects.
///
/// This combines the memory-effect model with the knowledge that
/// compare/test instructions set condition flags (a side effect tracked
/// by InstFlags, not MemoryEffect).
pub fn is_removable(opcode: AArch64Opcode) -> bool {
    let effect = opcode_effect(opcode);
    if !effect.is_pure() {
        return false;
    }

    use AArch64Opcode::*;
    // Compare/test and checked arithmetic set NZCV flags — not removable
    // even though they don't access memory.
    !matches!(
        opcode,
        CmpRR
            | CmpRI
            | Tst
            | Fcmp
            | AddsRR
            | AddsRI
            | SubsRR
            | SubsRI
            | Brk
            | TrapOverflow
            | TrapBoundsCheck
            | TrapBoundsCheckExact
            | TrapNull
            | TrapNullIfZero
            | TrapDivZero
            | TrapDivZeroIfZero
            | TrapShiftRange
            | TrapShiftRangeIfOOB
            | TrapOverflowExact
    )
}

/// Returns true if the opcode writes implicit NZCV condition flags.
///
/// These instructions set the processor flags (N, Z, C, V) as a side effect.
/// Any subsequent flag-reading instruction (CSet, Csel, BCond, etc.) depends
/// on the most recent flag-writing instruction, but this dependency is NOT
/// captured in the explicit operand list.
///
/// **The instruction scheduler must order flag-writers before flag-readers.**
/// Without explicit edges, the scheduler may freely reorder a CSet before
/// the CMP that sets the flags it consumes.
pub fn writes_flags(opcode: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    matches!(
        opcode,
        CmpRR
            | CmpRI
            | CMPWrr
            | CMPXrr
            | CMPWri
            | CMPXri
            | Tst
            | Fcmp
            | AddsRR
            | AddsRI
            | SubsRR
            | SubsRI
    )
}

/// Returns true if the opcode has a tied def-use operand (`operand[0]` is
/// both the destination AND an implicit source — a read-modify-write).
///
/// MOVK (`MOVK Rd, #imm16, LSL #shift`) inserts a 16-bit immediate into
/// the destination register while preserving the other bits. This means
/// the "current value" of Rd is an implicit input to the instruction,
/// but it does not appear in the operand list (which only contains
/// `[def_reg, imm, shift]`).
///
/// BFM (`BFM Rd, Rn, #immr, #imms`, alias `BFI`/`BFXIL`) is a bitfield
/// *insert*: it writes a contiguous bitfield of `Rn` into `Rd` while
/// preserving the bits of `Rd` outside that field. Like MOVK, the prior
/// value of `Rd` is an implicit input that is not visible in the operand
/// list. Its siblings `UBFM` and `SBFM` do NOT have this property — they
/// zero or sign-extend the uncovered bits and therefore fully redefine
/// `Rd`, so only `BFM` belongs here.
///
/// NEON `INS Vd.S[lane], Wn` inserts one scalar lane and preserves every
/// other lane in `Vd`. The destination vector is therefore also an input.
///
/// NEON `UDOT Vd.4S, Vn.16B, Vm.16B` (FEAT_DotProd) is a dot-product
/// ACCUMULATE: each 32-bit lane of `Vd` is `Vd[i] + sum(zext(Vn.b[4i+j]) *
/// zext(Vm.b[4i+j]))` — the prior value of `Vd` is an explicit addend, so the
/// destination register is also an input. Treating `operand[0]` as a plain def
/// would let regalloc consider the accumulator dead before the UDOT (and DCE
/// drop its initializer, or the scheduler reorder its setter), silently
/// corrupting the running sum — the exact "op0 is def" P0 class this table
/// exists to prevent.
///
/// **Why this matters:**
/// - **GVN/CSE**: two BFMs (or two MOVKs) with the same explicit operands
///   are NOT the same expression unless their prior destination values
///   match. Treating them as identical silently drops the second write
///   onto a different register and corrupts the destination. See issues
///   #366 (MOVK) and #408 (BFM).
/// - **Instruction scheduler**: a tied-def-use instruction must be ordered
///   AFTER the instruction that established its prior destination value.
///   Without an explicit RAW edge on `operand[0]`, the scheduler may move
///   it before its preceding setter in the materialize chain, or move
///   readers between the setter and a trailing MOVK/BFM. See issue #382.
pub fn has_tied_def_use(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::Movk
            | AArch64Opcode::Bfm
            | AArch64Opcode::NeonInsGen
            | AArch64Opcode::NeonUdotV
            | AArch64Opcode::NeonBitV
            // FMLA/FMLS accumulate into Vd (Vd[i] += / -= Vn[i]*Vm[i]) — the
            // prior destination value is an explicit addend, so operand 0 is a
            // tied def-use (same class of "op0 is def" P0 as UDOT/BIT). The
            // by-element form (NeonFmlaLaneV) accumulates identically.
            | AArch64Opcode::NeonFmlaV
            | AArch64Opcode::NeonFmlsV
            | AArch64Opcode::NeonFmlaLaneV
            // SMLAL/SMLAL2/UMLAL/UMLAL2 accumulate the widening product into Vd
            // (Vd.d[j] += ext(Vn)*ext(Vm)) — the prior destination is an explicit
            // addend, so operand 0 is a tied def-use (same class as UDOT/FMLA).
            | AArch64Opcode::NeonSmlalV
            | AArch64Opcode::NeonSmlal2V
            | AArch64Opcode::NeonUmlalV
            | AArch64Opcode::NeonUmlal2V
            // MLA.4S accumulates the same-width product into Vd
            // (Vd[i] += Vn[i]*Vm[i] mod 2^32) and UADALP.2D accumulates the
            // zero-extended adjacent source-lane pairs into Vd
            // (Vd.d[j] += zext64(Vn.4s[2j]) + zext64(Vn.4s[2j+1])) — in both
            // the prior destination is an explicit addend, so operand 0 is a
            // tied def-use (same class as UDOT/FMLA/xMLAL).
            | AArch64Opcode::NeonMlaV
            | AArch64Opcode::NeonUadalpV // NOTE: NeonUaddwV/NeonUaddw2V (UADDW/UADDW2) and their SIGNED
                                         // siblings NeonSaddwV/NeonSaddw2V (SADDW/SADDW2) are deliberately
                                         // NOT here: the ISA form is the plain THREE-OPERAND
                                         // `Vd = Vn + widen(Vm)` — the i64 addend Vn is a SEPARATE source
                                         // operand (operand 1), not the prior value of Vd. Operand 0 is a
                                         // pure def (see `test_neon_uaddw_is_three_operand_not_tied` /
                                         // `test_neon_saddw_is_three_operand_not_tied`).
    )
}

/// Returns true if the opcode reads implicit NZCV condition flags.
///
/// These instructions consume flag state set by a prior CMP/TST/ADDS/SUBS
/// but do NOT capture that dependency in their explicit operands. The
/// condition code immediate (e.g., LE=13) is just a selector for which
/// flags to test, NOT the flag values themselves. Therefore, two flag-reading
/// instructions with the same explicit operands may produce different values
/// if different comparisons set the flags.
///
/// This set covers:
/// - CSEL-family conditional selects (`CSEL`, `CSET`, `CSINC`, `CSINV`,
///   `CSNEG`) which test NZCV against a condition code immediate.
/// - `ADC`/`SBC` multi-precision arithmetic, which adds/subtracts with
///   the carry flag `C` set by a prior `ADDS`/`SUBS`. The carry bit is
///   an implicit input; two ADCs with identical explicit operands but
///   reached after different flag writers produce different results.
///   See issue #409 for the i128 miscompile class.
///
/// **CSE and GVN must skip these instructions.** Treating them as pure
/// functions of their explicit operands is unsound because the implicit
/// flag input is not visible in the operand list.
///
/// **LICM must not hoist these instructions out of loops** — the carry
/// flag changes every iteration based on the loop body's `ADDS`/`SUBS`.
///
/// **The instruction scheduler must add edges from the most recent
/// flag-writing instruction to each flag-reading instruction.**
pub fn reads_flags(opcode: AArch64Opcode) -> bool {
    use AArch64Opcode::*;
    // FcselRR (scalar FP conditional select) reads NZCV exactly like the integer
    // CSEL family — the scheduler MUST keep it after its flag-setting CMP.
    matches!(
        opcode,
        CSet | Csel | Csinc | Csinv | Csneg | FcselRR | Adc | Sbc
    )
}

// ===========================================================================
// x86-64 memory-effects model
// ===========================================================================

/// Classify the memory effect of an x86-64 opcode.
///
/// Mirrors [`opcode_effect`] for the x86-64 target.
pub fn x86_opcode_effect(opcode: X86Opcode) -> MemoryEffect {
    use X86Opcode::*;
    match opcode {
        // -- Loads: read memory --
        MovRM8 | MovRM16 | MovRM32 | MovRM | MovsdRM | MovssRM | MovdquRM | MovdqaRM | MovRMSib
        | MovsxdRMSib | MovRM32Sib | MovRM8Sib | MovsdRMSib | MovssRMSib | AddRM | SubRM | CmpRM
        | ImulRM
        | ImulRMSib | TestRM | Ptest
        | MovRipRel | MovssRipRel | MovsdRipRel | MovRipRelTlv | Pop => MemoryEffect::Load,

        // -- Stores: write memory --
        MovMR8 | MovMR16 | MovMR32 | MovMR | MovsdMR | MovssMR | MovdquMR | MovdqaMR | MovMRSib
        | MovMR32Sib | MovMR8Sib | Push => MemoryEffect::Store,

        // -- Volatile memory: full barrier (see the AArch64 counterpart) --
        // A volatile access must never be elided/CSE'd/forwarded/hoisted/
        // reordered; Call is the strongest, always-sound classification.
        VolatileMovRM8 | VolatileMovRM16 | VolatileMovRM32 | VolatileMovRM | VolatileMovMR8
        | VolatileMovMR16 | VolatileMovMR32 | VolatileMovMR | VolatileMovssRM | VolatileMovssMR
        | VolatileMovsdRM | VolatileMovsdMR | VolatileMovdquRM | VolatileMovdquMR
        | VolatileMovdqaRM | VolatileMovdqaMR => MemoryEffect::Call,

        // -- Calls / barriers: full memory ordering barrier --
        Call | CallR | CallM | Mfence => MemoryEffect::Call,

        // -- Everything else: pure computation --
        // Arithmetic
        AddRR | AddRI | SubRR | SubRI | ImulRR | ImulRRI | Neg | Inc | Dec => MemoryEffect::Pure,

        // Division (has side effects but no memory access)
        Idiv | Div | Mul => MemoryEffect::Pure,

        // Sign-extend implicit (CDQ/CQO)
        Cdq | Cqo => MemoryEffect::Pure,

        // Add/subtract with carry (i128): read+write the carry flag, no memory.
        // The flag dependency is enforced via x86_reads_flags/x86_writes_flags,
        // mirroring how AArch64 models Adc/Sbc as memory-pure.
        AdcRR | SbbRR => MemoryEffect::Pure,

        // Logical
        AndRR | AndRI | OrRR | OrRI | XorRR | XorRI | Not | Pand | Pandn | Por | Pxor => {
            MemoryEffect::Pure
        }

        // Shifts
        ShlRR | ShlRI | ShrRR | ShrRI | SarRR | SarRI | RolRI => MemoryEffect::Pure,

        // Compare/test (set flags, no memory access)
        CmpRR | CmpRI | CmpRI8 | TestRR | TestRI | Ucomisd | Ucomiss | BtRI => MemoryEffect::Pure,

        // Moves (register-register and register-immediate)
        MovRR | MovRR32 | MovRI | Movzx | MovzxW | MovsxB | MovsxW | Movsx | MovsdRR | MovssRR
        | MovdqaRR => MemoryEffect::Pure,

        // LEA (address computation, no memory access)
        Lea | LeaSib | LeaRip => MemoryEffect::Pure,

        // Conditional move/set
        Cmovcc | Cmovcc32 | Setcc => MemoryEffect::Pure,

        // SSE register-register arithmetic
        Addsd | Subsd | Mulsd | Divsd | Sqrtsd | Roundsd | Andpd | Addss | Subss | Mulss | Divss
        | Sqrtss | Roundss | Minsd | Maxsd | Minss | Maxss | Cmpsd | Cmpss
        | Andps | Pcmpeqb | Pcmpeqw | Pcmpgtb | Pcmpgtw | Pcmpeqd | Pcmpgtd | Paddb | Paddw
        | Paddd | Psubb | Psubw | Psubd | Paddq | Psubq | Pmullw | Pmuludq | Punpcklbw
        | Punpckldq | Packuswb | Punpckhbw | Punpcklqdq | Pmulld | Pcmpeqq | Pcmpgtq | Pshufd
        | Pmovmskb | Pinsrd | Pextrd | Pinsrq | Pextrq | Pblendvb | Pslld | Psrld | Psrad
        | Psllq | Psrlq | Psadbw
        // SSE/SSE2 packed floating-point arithmetic (`<4 x f32>` / `<2 x f64>`).
        // Pure: no memory access, no flags written, deterministic per-lane
        // IEEE arithmetic under the default MXCSR rounding mode.
        | Addps | Subps | Mulps | Divps | Addpd | Subpd | Mulpd | Divpd => MemoryEffect::Pure,

        // SSE type conversions
        Cvtsi2sd | Cvtsd2si | Cvttsd2si | Cvtsi2ss | Cvtss2si | Cvttss2si | Cvtsd2ss | Cvtss2sd => {
            MemoryEffect::Pure
        }

        // GPR <-> XMM transfers
        MovdToXmm | MovdFromXmm | MovqToXmm | MovqFromXmm => MemoryEffect::Pure,

        // Bit manipulation
        Bsf | Bsr | Tzcnt | Lzcnt | Popcnt | Bswap => MemoryEffect::Pure,

        // Atomic: conservative (read + write memory)
        Xchg => MemoryEffect::Store,
        Cmpxchg | Cmpxchg8 | Cmpxchg16 => MemoryEffect::Store,
        AtomicRmwCasLoop | AtomicRmwCasLoop8 | AtomicRmwCasLoop16 => MemoryEffect::Store,

        // Branches / control flow (no memory ops; DCE uses InstFlags)
        Jmp | JmpR | Jcc | Ret | Ud2 => MemoryEffect::Pure,

        // Pseudo-instructions
        Phi => MemoryEffect::Pure,
        StackAlloc => MemoryEffect::Store,
        Nop | NopMulti | V4I32MaskExtract | V16I8MaskExtract | V8I16MaskExtract
        | V2I64MaskExtract | V128BoolSelect => MemoryEffect::Pure,
        // Proof-only bounds-check / null-check / div-zero-check / shift-range-check
        // carriers (Sentinel S5): touch no memory. Their HAS_SIDE_EFFECTS flag (not
        // their memory effect) keeps DCE/scheduling from dropping or reordering them
        // before the kernel-gated proof pass decides.
        TrapBoundsCheckExact | TrapNullIfZeroExact | TrapDivZeroExact | TrapShiftRangeExact => {
            MemoryEffect::Pure
        }
    }
}

/// Classify the memory effect of an x86-64 ISel instruction.
///
/// Opcode-only metadata is intentionally conservative for opcodes that carry
/// both register and memory forms. This helper refines that metadata when the
/// lowered operands prove the precise form.
pub fn x86_inst_effect(inst: &X86ISelInst) -> MemoryEffect {
    let effect = match inst.opcode {
        X86Opcode::Ptest if x86_ptest_is_register_register_form(&inst.operands) => {
            MemoryEffect::Pure
        }
        _ => x86_opcode_effect(inst.opcode),
    };

    effect_from_flags_and_opcode_effect(inst.flags, effect)
}

fn effect_from_flags_and_opcode_effect(
    flags: trust_cg_ir::InstFlags,
    opcode_effect: MemoryEffect,
) -> MemoryEffect {
    if flags.is_call() || opcode_effect.is_barrier() {
        return MemoryEffect::Call;
    }

    if flags.writes_memory() || opcode_effect.writes_memory() {
        return MemoryEffect::Store;
    }

    if flags.reads_memory() || opcode_effect.reads_memory() {
        return MemoryEffect::Load;
    }

    MemoryEffect::Pure
}

fn x86_ptest_is_register_register_form(operands: &[X86ISelOperand]) -> bool {
    matches!(
        operands,
        [lhs, rhs] if x86_isel_operand_is_register(lhs) && x86_isel_operand_is_register(rhs)
    )
}

fn x86_isel_operand_is_register(operand: &X86ISelOperand) -> bool {
    matches!(operand, X86ISelOperand::VReg(_) | X86ISelOperand::PReg(_))
}

/// Returns true if this x86-64 opcode produces a value (`operand[0]` is a def).
pub fn x86_produces_value(opcode: X86Opcode) -> bool {
    use X86Opcode::*;
    !matches!(
        opcode,
        // Compare/test: only set flags
        CmpRR | CmpRI | CmpRI8 | CmpRM | TestRR | TestRI | TestRM
        | Ucomisd | Ucomiss | BtRI | Ptest
        // Stores
        | MovMR8 | MovMR16 | MovMR32 | MovMR | MovsdMR | MovssMR | MovdquMR | MovdqaMR
        | MovMRSib | MovMR32Sib | MovMR8Sib
        // Branches and control flow
        | Jmp | Jcc | Call | CallR | CallM | Ret
        // Stack store
        | Push
        // Pseudo with no value
        | Nop | NopMulti | StackAlloc
        // Memory fence
        | Mfence
        // Atomic exchange (complex implicit operands)
        | Cmpxchg
        // Fixed-register implicit writes
        | Cdq | Cqo | Idiv | Div | Mul
        // Trap terminator
        | Ud2
        // Proof-only trap carriers: every operand is a READ of the guarded
        // value (the expansion emits TEST/CMP on them); nothing is defined.
        // P0 (2026-07-18, b14/b18 runtime ud2): treating operand[0] as a def
        // gave a single-operand `TrapDivZeroExact [divisor]` ZERO reads once
        // magic-sdiv replaced the Div — liveness/DCE then dropped the
        // divisor's MovRI while the carrier expanded into a real test of a
        // never-written spill slot.
        | TrapBoundsCheckExact | TrapNullIfZeroExact | TrapDivZeroExact
        | TrapShiftRangeExact
    )
}

/// Returns true if this x86-64 opcode can be safely eliminated if
/// its result is unused.
///
/// x86 is more conservative than AArch64: most arithmetic instructions
/// set RFLAGS as a side effect. However, if a pass can prove the flags
/// are not consumed, the instruction is removable. This function returns
/// the conservative answer (assuming flags may be live).
pub fn x86_is_removable(opcode: X86Opcode) -> bool {
    let effect = x86_opcode_effect(opcode);
    if !effect.is_pure() {
        return false;
    }

    use X86Opcode::*;
    // On x86, arithmetic/logical/shift instructions set RFLAGS.
    // Only register moves, LEA, SSE moves, extensions, conversions,
    // GPR<->XMM transfers, and pseudo-instructions are truly removable.
    matches!(
        opcode,
        MovRR
            | MovRR32
            | MovRI
            | Movzx
            | MovzxW
            | MovsxB
            | MovsxW
            | Movsx
            | MovsdRR
            | MovssRR
            | MovdqaRR
            | Pand
            | Pandn
            | Por
            | Pxor
            | Pcmpeqb
            | Pcmpeqw
            | Pcmpgtb
            | Pcmpgtw
            | Pcmpeqd
            | Pcmpgtd
            | Paddb
            | Paddw
            | Psubb
            | Psubw
            | Paddq
            | Psubq
            | Pcmpeqq
            | Pcmpgtq
            | Punpckldq
            | Punpcklqdq
            | Pshufd
            | Pmovmskb
            | Pinsrd
            | Pextrd
            | Pinsrq
            | Pextrq
            | Pblendvb
            | V128BoolSelect
            | Lea
            | LeaSib
            | LeaRip
            | Cvtsi2sd
            | Cvtsd2si
            | Cvttsd2si
            | Cvtsi2ss
            | Cvtss2si
            | Cvttss2si
            | Cvtsd2ss
            | Cvtss2sd
            | MovdToXmm
            | MovdFromXmm
            | MovqToXmm
            | MovqFromXmm
            | Bswap
            | Phi
            | Nop
    )
}

/// Returns true if this x86-64 opcode writes RFLAGS.
///
/// On x86, nearly ALL arithmetic, logical, and shift instructions
/// modify condition flags. This is a fundamental difference from AArch64
/// where only explicit flag-setting instructions (CMP, TST, ADDS, SUBS)
/// modify NZCV.
pub fn x86_writes_flags(opcode: X86Opcode) -> bool {
    use X86Opcode::*;
    matches!(
        opcode,
        // Arithmetic
        AddRR | AddRI | AddRM | SubRR | SubRI | SubRM
        | AdcRR | SbbRR
        | ImulRR | ImulRRI | ImulRM | ImulRMSib | Idiv | Div | Mul
        | Neg | Inc | Dec
        // Logical
        | AndRR | AndRI | OrRR | OrRI | XorRR | XorRI | Not
        // Shifts
        | ShlRR | ShlRI | ShrRR | ShrRI | SarRR | SarRI | RolRI
        // Compare/test
        | CmpRR | CmpRI | CmpRI8 | CmpRM | TestRR | TestRI | TestRM
        | Ptest
        // FP compare
        | Ucomisd | Ucomiss
        // Bit manipulation that sets flags
        | Bsf | Bsr | Tzcnt | Lzcnt | Popcnt | BtRI
        // Atomic (CMPXCHG sets ZF + CF/PF/AF/SF/OF via its implicit compare
        // at EVERY width — the narrow siblings were missing, which
        // misclassified them as writing nothing; adversarial-review NIT)
        | Cmpxchg
        | Cmpxchg8
        | Cmpxchg16
        | AtomicRmwCasLoop
        | AtomicRmwCasLoop8
        | AtomicRmwCasLoop16
        | V4I32MaskExtract
        | V16I8MaskExtract
        | V8I16MaskExtract
        | V2I64MaskExtract
    )
}

/// Returns true if this x86-64 opcode architecturally DEFINES every
/// condition flag a `CondCode` can consume (CF/OF/SF/ZF/PF) — the
/// MUST-write counterpart of the may-write [`x86_writes_flags`].
///
/// A pass that deletes or reorders flag-producing code may treat an
/// instruction as a barrier that re-establishes RFLAGS **only** under this
/// predicate. `x86_writes_flags` is NOT sufficient: `Inc`/`Dec` preserve
/// CF, `BtRI` writes only CF, `Bsf`/`Bsr`/`Tzcnt`/`Lzcnt` define a subset,
/// `Imul*` leaves SF/ZF/PF undefined, and every shift with a (masked)
/// count of zero leaves ALL flags unchanged — so none of those qualify.
/// Fail-closed allowlist; extend only with an ISA-manual citation.
pub fn x86_defines_all_cc_flags(opcode: X86Opcode) -> bool {
    use X86Opcode::*;
    matches!(
        opcode,
        // Full-flag arithmetic (Intel SDM: CF/OF/SF/ZF/AF/PF all defined).
        AddRR | AddRI | AddRM | SubRR | SubRI | SubRM | Neg
        | AdcRR | SbbRR
        // Full-flag logical (CF/OF cleared; SF/ZF/PF defined).
        | AndRR | AndRI | OrRR | OrRI | XorRR | XorRI
        // Compare/test (same flag behavior as SUB/AND).
        | CmpRR | CmpRI | CmpRI8 | CmpRM | TestRR | TestRI | TestRM
    )
}

/// Returns true if this x86-64 opcode reads RFLAGS.
///
/// CMOVcc, SETcc, and Jcc all read condition flags to decide behavior.
///
/// `ADC`/`SBB` also read the implicit carry flag set by a prior `ADD`/`SUB`
/// (the i128 multi-register arithmetic class). The carry input is not in the
/// explicit operand list, so the scheduler must add an edge from the most
/// recent flag-writer to each `ADC`/`SBB`, and CSE/GVN/LICM must treat them as
/// impure. Mirrors the AArch64 `Adc`/`Sbc` flag-reading classification.
pub fn x86_reads_flags(opcode: X86Opcode) -> bool {
    use X86Opcode::*;
    matches!(opcode, Cmovcc | Cmovcc32 | Setcc | Jcc | AdcRR | SbbRR)
}

// ===========================================================================
// Target-independent category-based queries
// ===========================================================================

/// Target-independent memory effect classification based on [`OpcodeCategory`].
///
/// This provides a conservative but correct classification for any target.
/// Target-specific functions ([`opcode_effect`], [`x86_opcode_effect`]) provide
/// more precise per-opcode classification but are limited to their target.
///
/// Used by passes that want to reason about opcodes via category alone,
/// enabling multi-target optimization without per-target match arms.
pub fn category_memory_effect(cat: OpcodeCategory) -> MemoryEffect {
    use OpcodeCategory::*;
    match cat {
        Load => MemoryEffect::Load,
        Store => MemoryEffect::Store,
        Call => MemoryEffect::Call,
        // All other categories are pure computation.
        AddRR | AddRI | SubRR | SubRI | MulRR | Neg | AndRR | AndRI | OrRR | OrRI | XorRR
        | XorRI | ShlRR | ShlRI | ShrRR | ShrRI | SarRR | SarRI | MovRR | MovRI | CmpRR | CmpRI
        | Nop | Ret | Branch | CondBranch | Phi | Other => MemoryEffect::Pure,
    }
}

/// Target-independent removability check based on [`OpcodeCategory`].
///
/// An instruction is removable if:
/// 1. Its category has no memory effects (pure).
/// 2. It does not write implicit flags (as indicated by the caller-supplied
///    `target_writes_flags` value).
/// 3. It is not control flow.
///
/// This is conservative: target-specific functions ([`is_removable`],
/// [`x86_is_removable`]) may be more precise for their respective targets.
pub fn category_is_removable(cat: OpcodeCategory, target_writes_flags: bool) -> bool {
    if !category_memory_effect(cat).is_pure() {
        return false;
    }
    // Compare instructions always set flags — not removable.
    if matches!(cat, OpcodeCategory::CmpRR | OpcodeCategory::CmpRI) {
        return false;
    }
    // If the target says this opcode writes flags, not removable.
    if target_writes_flags {
        return false;
    }
    // Control flow is not removable.
    if matches!(
        cat,
        OpcodeCategory::Branch
            | OpcodeCategory::CondBranch
            | OpcodeCategory::Ret
            | OpcodeCategory::Call
    ) {
        return false;
    }
    true
}

/// Target-independent flag-reading check based on [`OpcodeCategory`].
///
/// Returns `true` for categories that are *known* to read flags.
/// Returns `false` conservatively — actual flag reading depends on the
/// target-specific opcode (e.g., `CSet` on AArch64 reads flags but has
/// category [`OpcodeCategory::Other`]).
pub fn category_reads_flags(cat: OpcodeCategory) -> bool {
    matches!(cat, OpcodeCategory::CondBranch)
}

/// Target-independent flag-writing check based on [`OpcodeCategory`].
///
/// Returns `true` for categories that are *known* to write flags.
/// Compare instructions always write flags on all targets.
pub fn category_writes_flags(cat: OpcodeCategory) -> bool {
    matches!(cat, OpcodeCategory::CmpRR | OpcodeCategory::CmpRI)
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::AArch64Opcode;

    #[test]
    fn test_arithmetic_is_pure() {
        assert_eq!(opcode_effect(AArch64Opcode::AddRR), MemoryEffect::Pure);
        assert_eq!(opcode_effect(AArch64Opcode::SubRI), MemoryEffect::Pure);
        assert_eq!(opcode_effect(AArch64Opcode::MulRR), MemoryEffect::Pure);
        assert_eq!(opcode_effect(AArch64Opcode::SDiv), MemoryEffect::Pure);
        assert_eq!(opcode_effect(AArch64Opcode::Rbit), MemoryEffect::Pure);
    }

    #[test]
    fn test_loads_are_load() {
        assert_eq!(opcode_effect(AArch64Opcode::LdrRI), MemoryEffect::Load);
        assert_eq!(
            opcode_effect(AArch64Opcode::LdrPreIndex),
            MemoryEffect::Load
        );
        assert_eq!(
            opcode_effect(AArch64Opcode::LdrPostIndex),
            MemoryEffect::Load
        );
        assert_eq!(opcode_effect(AArch64Opcode::LdpRI), MemoryEffect::Load);
        assert_eq!(opcode_effect(AArch64Opcode::LdrLiteral), MemoryEffect::Load);
        // Byte/halfword extending loads
        assert_eq!(opcode_effect(AArch64Opcode::LdrbRI), MemoryEffect::Load);
        assert_eq!(opcode_effect(AArch64Opcode::LdrhRI), MemoryEffect::Load);
        assert_eq!(opcode_effect(AArch64Opcode::LdrsbRI), MemoryEffect::Load);
        assert_eq!(opcode_effect(AArch64Opcode::LdrshRI), MemoryEffect::Load);
    }

    #[test]
    fn test_stores_are_store() {
        assert_eq!(opcode_effect(AArch64Opcode::StrRI), MemoryEffect::Store);
        assert_eq!(
            opcode_effect(AArch64Opcode::StrPreIndex),
            MemoryEffect::Store
        );
        assert_eq!(
            opcode_effect(AArch64Opcode::StrPostIndex),
            MemoryEffect::Store
        );
        assert_eq!(opcode_effect(AArch64Opcode::StpRI), MemoryEffect::Store);
        // Byte/halfword truncating stores
        assert_eq!(opcode_effect(AArch64Opcode::StrbRI), MemoryEffect::Store);
        assert_eq!(opcode_effect(AArch64Opcode::StrhRI), MemoryEffect::Store);
    }

    #[test]
    fn test_calls_are_call() {
        assert_eq!(opcode_effect(AArch64Opcode::Bl), MemoryEffect::Call);
        assert_eq!(opcode_effect(AArch64Opcode::Blr), MemoryEffect::Call);
    }

    #[test]
    fn test_branches_are_pure() {
        assert_eq!(opcode_effect(AArch64Opcode::B), MemoryEffect::Pure);
        assert_eq!(opcode_effect(AArch64Opcode::BCond), MemoryEffect::Pure);
        assert_eq!(opcode_effect(AArch64Opcode::Ret), MemoryEffect::Pure);
    }

    #[test]
    fn test_removable() {
        assert!(is_removable(AArch64Opcode::AddRR));
        assert!(is_removable(AArch64Opcode::MovR));
        assert!(is_removable(AArch64Opcode::NeonUmovGen));
        assert!(!is_removable(AArch64Opcode::CmpRR));
        assert!(!is_removable(AArch64Opcode::LdrRI));
        assert!(!is_removable(AArch64Opcode::StrRI));
        assert!(!is_removable(AArch64Opcode::Bl));
        assert!(!is_removable(AArch64Opcode::TrapNullIfZero));
    }

    #[test]
    fn test_memory_effect_queries() {
        assert!(MemoryEffect::Pure.is_pure());
        assert!(!MemoryEffect::Load.is_pure());

        assert!(MemoryEffect::Load.reads_memory());
        assert!(MemoryEffect::Call.reads_memory());
        assert!(!MemoryEffect::Pure.reads_memory());

        assert!(MemoryEffect::Store.writes_memory());
        assert!(MemoryEffect::Call.writes_memory());
        assert!(!MemoryEffect::Load.writes_memory());

        assert!(MemoryEffect::Call.is_barrier());
        assert!(!MemoryEffect::Store.is_barrier());
    }

    #[test]
    fn test_writes_flags() {
        assert!(writes_flags(AArch64Opcode::CmpRR));
        assert!(writes_flags(AArch64Opcode::CmpRI));
        assert!(writes_flags(AArch64Opcode::Tst));
        assert!(writes_flags(AArch64Opcode::Fcmp));
        assert!(writes_flags(AArch64Opcode::AddsRR));
        assert!(writes_flags(AArch64Opcode::SubsRI));
        // Arithmetic and moves should not write flags
        assert!(!writes_flags(AArch64Opcode::AddRR));
        assert!(!writes_flags(AArch64Opcode::MovR));
        assert!(!writes_flags(AArch64Opcode::CSet));
    }

    #[test]
    fn test_reads_flags() {
        assert!(reads_flags(AArch64Opcode::CSet));
        assert!(reads_flags(AArch64Opcode::Csel));
        assert!(reads_flags(AArch64Opcode::Csinc));
        assert!(reads_flags(AArch64Opcode::Csinv));
        assert!(reads_flags(AArch64Opcode::Csneg));
        // CMP writes but does not read flags
        assert!(!reads_flags(AArch64Opcode::CmpRR));
        assert!(!reads_flags(AArch64Opcode::AddRR));
    }

    // Regression for #409: ADC/SBC consume the carry flag implicitly for
    // multi-precision (i128) arithmetic. They must be classified as
    // flag-readers so that CSE/GVN/LICM/scheduler treat them as depending
    // on the most recent flag writer rather than as a free-to-reorder
    // pure function of their explicit operands.
    #[test]
    fn test_reads_flags_adc_sbc() {
        assert!(
            reads_flags(AArch64Opcode::Adc),
            "ADC reads carry implicitly — must be a flag-reader"
        );
        assert!(
            reads_flags(AArch64Opcode::Sbc),
            "SBC reads carry/borrow implicitly — must be a flag-reader"
        );
        // Sanity: the pure-arithmetic siblings do NOT read flags.
        assert!(!reads_flags(AArch64Opcode::AddRR));
        assert!(!reads_flags(AArch64Opcode::SubRR));
        assert!(!reads_flags(AArch64Opcode::Umulh));
        assert!(!reads_flags(AArch64Opcode::Smulh));
        assert!(!reads_flags(AArch64Opcode::Madd));
    }

    // Regression for #408: BFM is a bitfield *insert* that preserves the
    // bits of Rd outside the inserted field. Its prior destination value
    // is an implicit input — same shape as MOVK. Classifying it as tied
    // def-use stops GVN/CSE from folding two BFMs with identical explicit
    // operands but different prior Rd values into a single op.
    #[test]
    fn test_has_tied_def_use_bfm() {
        assert!(
            has_tied_def_use(AArch64Opcode::Bfm),
            "BFM preserves uncovered bits of Rd — must be tied def-use"
        );
        // MOVK remains tied (existing guarantee).
        assert!(has_tied_def_use(AArch64Opcode::Movk));
        // UBFM / SBFM fully redefine Rd (uncovered bits become 0 / sign-ext)
        // so they are NOT tied def-use.
        assert!(!has_tied_def_use(AArch64Opcode::Ubfm));
        assert!(!has_tied_def_use(AArch64Opcode::Sbfm));
        // Sanity: other arithmetic / moves are not tied.
        assert!(!has_tied_def_use(AArch64Opcode::AddRR));
        assert!(!has_tied_def_use(AArch64Opcode::MovR));
        assert!(!has_tied_def_use(AArch64Opcode::Adc));
    }

    #[test]
    fn test_has_tied_def_use_neon_ins_gen() {
        assert!(
            has_tied_def_use(AArch64Opcode::NeonInsGen),
            "INS preserves the other lanes of Vd — must be tied def-use"
        );
        assert_eq!(
            aarch64_operand_roles(AArch64Opcode::NeonInsGen, 4)[0],
            OperandRole::DefUse,
            "operand 0 is both the destination vector and preserved-lane input"
        );
        assert_eq!(
            aarch64_def_operand_positions(AArch64Opcode::NeonInsGen, 4),
            vec![0],
            "INS defines the destination vector operand"
        );
        let use_positions = aarch64_use_operand_positions(AArch64Opcode::NeonInsGen, 4);
        assert!(
            use_positions.contains(&0),
            "INS must read the preserved destination vector"
        );
        assert!(
            use_positions.contains(&1),
            "INS must read the inserted scalar operand"
        );
    }

    #[test]
    fn test_has_tied_def_use_neon_udot() {
        // UDOT Vd.4S, Vn.16B, Vm.16B ACCUMULATES into Vd — the prior value of
        // Vd is an explicit addend, so operand 0 must be a tied def-use.
        // Modeling it as a plain def would let regalloc treat the accumulator
        // as dead before the UDOT (and DCE drop its initializer), corrupting
        // the running sum — the "op0 is def" P0 class.
        assert!(
            has_tied_def_use(AArch64Opcode::NeonUdotV),
            "UDOT accumulates into Vd — must be tied def-use"
        );
        assert_eq!(
            aarch64_operand_roles(AArch64Opcode::NeonUdotV, 4),
            vec![
                OperandRole::DefUse,
                OperandRole::Use,
                OperandRole::Use,
                OperandRole::Use,
            ],
            "operand 0 is both the accumulator input and the destination"
        );
        assert_eq!(
            aarch64_def_operand_positions(AArch64Opcode::NeonUdotV, 4),
            vec![0],
            "UDOT defines only the accumulator operand"
        );
        assert_eq!(
            aarch64_use_operand_positions(AArch64Opcode::NeonUdotV, 4),
            vec![0, 1, 2, 3],
            "UDOT must READ the accumulator (operand 0) as well as Vn/Vm"
        );
    }

    #[test]
    fn test_has_tied_def_use_neon_mla() {
        // MLA Vd.4S, Vn.4S, Vm.4S ACCUMULATES the same-width product into Vd
        // (`Vd[i] += Vn[i]*Vm[i]` mod 2^32) — the prior value of Vd is an
        // explicit addend, so operand 0 must be a tied def-use (same class as
        // UDOT/FMLA/xMLAL). Modeling it as a plain def would let regalloc
        // treat the accumulator as dead before the MLA (and DCE drop its
        // initializer), corrupting the running sum.
        assert!(
            has_tied_def_use(AArch64Opcode::NeonMlaV),
            "MLA accumulates into Vd — must be tied def-use"
        );
        assert_eq!(
            aarch64_operand_roles(AArch64Opcode::NeonMlaV, 4),
            vec![
                OperandRole::DefUse,
                OperandRole::Use,
                OperandRole::Use,
                OperandRole::Use,
            ],
            "operand 0 is both the accumulator input and the destination"
        );
        assert_eq!(
            aarch64_def_operand_positions(AArch64Opcode::NeonMlaV, 4),
            vec![0],
            "MLA defines only the accumulator operand"
        );
        assert_eq!(
            aarch64_use_operand_positions(AArch64Opcode::NeonMlaV, 4),
            vec![0, 1, 2, 3],
            "MLA must READ the accumulator (operand 0) as well as Vn/Vm"
        );
    }

    #[test]
    fn test_has_tied_def_use_neon_uadalp() {
        // UADALP Vd.2D, Vn.4S ACCUMULATES the zero-extended adjacent
        // source-lane pairs into Vd (`Vd.d[j] += zext64(Vn.4s[2j]) +
        // zext64(Vn.4s[2j+1])`) — the prior value of Vd is an explicit addend,
        // so operand 0 must be a tied def-use (same class as UDOT; CONTRAST
        // the non-accumulating UADDLP, whose operand 0 is a pure def).
        assert!(
            has_tied_def_use(AArch64Opcode::NeonUadalpV),
            "UADALP accumulates into Vd — must be tied def-use"
        );
        assert!(
            !has_tied_def_use(AArch64Opcode::NeonUaddlpV),
            "UADDLP (no accumulate) must stay a plain def — the accumulate \
             axis is exactly what distinguishes the two opcodes"
        );
        assert_eq!(
            aarch64_operand_roles(AArch64Opcode::NeonUadalpV, 3),
            vec![OperandRole::DefUse, OperandRole::Use, OperandRole::Use],
            "operand 0 is both the accumulator input and the destination"
        );
        assert_eq!(
            aarch64_def_operand_positions(AArch64Opcode::NeonUadalpV, 3),
            vec![0],
            "UADALP defines only the accumulator operand"
        );
        assert_eq!(
            aarch64_use_operand_positions(AArch64Opcode::NeonUadalpV, 3),
            vec![0, 1, 2],
            "UADALP must READ the accumulator (operand 0) as well as Vn"
        );
    }

    #[test]
    fn test_has_tied_def_use_neon_smlal() {
        // SMLAL/SMLAL2/UMLAL/UMLAL2 Vd.2D, Vn.4S, Vm.4S ACCUMULATE the widening
        // product into Vd — the prior value of Vd is an explicit addend, so
        // operand 0 must be a tied def-use (same class as UDOT/FMLA). Modeling it
        // as a plain def would let CSE/GVN/regalloc break the read-modify-write.
        for op in [
            AArch64Opcode::NeonSmlalV,
            AArch64Opcode::NeonSmlal2V,
            AArch64Opcode::NeonUmlalV,
            AArch64Opcode::NeonUmlal2V,
        ] {
            assert!(
                has_tied_def_use(op),
                "{op:?} accumulates into Vd — must be tied def-use"
            );
            assert_eq!(
                aarch64_operand_roles(op, 4),
                vec![
                    OperandRole::DefUse,
                    OperandRole::Use,
                    OperandRole::Use,
                    OperandRole::Use,
                ],
                "{op:?}: operand 0 is both the accumulator input and the destination"
            );
            assert_eq!(
                aarch64_def_operand_positions(op, 4),
                vec![0],
                "{op:?} defines only the accumulator operand"
            );
            assert_eq!(
                aarch64_use_operand_positions(op, 4),
                vec![0, 1, 2, 3],
                "{op:?} must READ the accumulator (operand 0) as well as Vn/Vm"
            );
        }
    }

    #[test]
    fn test_neon_uaddw_is_three_operand_not_tied() {
        // UADDW/UADDW2 Vd.2D, Vn.2D, Vm.4S is the ISA's plain THREE-OPERAND
        // widening add: `Vd.d[j] = Vn.d[j] + zext64(Vm.4S[half+j])`. The i64
        // addend is the SEPARATE source operand Vn (operand 1) — Vd's prior
        // value is NEVER read, so operand 0 must be a pure Def, NOT a tied
        // def-use. Modeling it as tied would over-constrain regalloc; modeling
        // Vn as anything but a Use would let the addend die early (the exact
        // "op0 is def" class the role table exists to prevent).
        for op in [AArch64Opcode::NeonUaddwV, AArch64Opcode::NeonUaddw2V] {
            assert!(
                !has_tied_def_use(op),
                "{op:?} is the plain three-operand form — operand 0 must NOT be tied"
            );
            assert_eq!(
                aarch64_operand_roles(op, 4),
                vec![
                    OperandRole::Def,
                    OperandRole::Use,
                    OperandRole::Use,
                    OperandRole::Use,
                ],
                "{op:?}: Vd pure def; Vn (addend), Vm (.4S source), arr imm are uses"
            );
            assert_eq!(
                aarch64_def_operand_positions(op, 4),
                vec![0],
                "{op:?} defines only Vd"
            );
            assert_eq!(
                aarch64_use_operand_positions(op, 4),
                vec![1, 2, 3],
                "{op:?} must NOT read operand 0 (the addend is operand 1, Vn)"
            );
        }
    }

    #[test]
    fn test_neon_saddw_is_three_operand_not_tied() {
        // SADDW/SADDW2 Vd.2D, Vn.2D, Vm.4S — the SIGNED sibling of UADDW/UADDW2
        // — is the SAME plain THREE-OPERAND widening add:
        // `Vd.d[j] = Vn.d[j] + sext64(Vm.4S[half+j])`. The i64 addend is the
        // SEPARATE source operand Vn (operand 1) — Vd's prior value is NEVER
        // read, so operand 0 must be a pure Def, NOT a tied def-use. Modeling
        // it as tied would over-constrain regalloc; modeling Vn as anything but
        // a Use would let the addend die early (the exact "op0 is def" class
        // the role table exists to prevent).
        for op in [AArch64Opcode::NeonSaddwV, AArch64Opcode::NeonSaddw2V] {
            assert!(
                !has_tied_def_use(op),
                "{op:?} is the plain three-operand form — operand 0 must NOT be tied"
            );
            assert_eq!(
                aarch64_operand_roles(op, 4),
                vec![
                    OperandRole::Def,
                    OperandRole::Use,
                    OperandRole::Use,
                    OperandRole::Use,
                ],
                "{op:?}: Vd pure def; Vn (addend), Vm (.4S source), arr imm are uses"
            );
            assert_eq!(
                aarch64_def_operand_positions(op, 4),
                vec![0],
                "{op:?} defines only Vd"
            );
            assert_eq!(
                aarch64_use_operand_positions(op, 4),
                vec![1, 2, 3],
                "{op:?} must NOT read operand 0 (the addend is operand 1, Vn)"
            );
        }
    }

    #[test]
    fn post_index_memory_operand_roles_model_writeback() {
        assert_eq!(
            aarch64_operand_roles(AArch64Opcode::NeonLd1Post, 3),
            vec![OperandRole::Def, OperandRole::DefUse, OperandRole::Use],
            "LD1 post-index defines the vector and updates the base"
        );
        assert_eq!(
            aarch64_operand_roles(AArch64Opcode::NeonSt1Post, 3),
            vec![OperandRole::Use, OperandRole::DefUse, OperandRole::Use],
            "ST1 post-index reads the vector and updates the base"
        );
        assert_eq!(
            aarch64_operand_roles(AArch64Opcode::LdpPostIndex, 4),
            vec![
                OperandRole::Def,
                OperandRole::Def,
                OperandRole::DefUse,
                OperandRole::Use,
            ],
            "LDP post-index defines both loaded registers and updates base"
        );
        assert_eq!(
            aarch64_operand_roles(AArch64Opcode::NeonLdpQPost, 4),
            vec![
                OperandRole::Def,
                OperandRole::Def,
                OperandRole::DefUse,
                OperandRole::Use,
            ],
            "LDP Q-pair post-index defines both Q registers and updates base"
        );
        assert_eq!(
            aarch64_def_operand_positions(AArch64Opcode::NeonLdpQPost, 4),
            vec![0, 1, 2],
            "LDP Q-pair writeback: both loaded Q registers AND the base are defs"
        );
        assert_eq!(
            aarch64_use_operand_positions(AArch64Opcode::NeonLdpQPost, 4),
            vec![2, 3],
            "LDP Q-pair reads the old base and the post-index immediate"
        );
        // STP Q-pair post-index is the STORE mirror: BOTH data registers are
        // stored USES and only the base is a def-use writeback (never the "op0
        // is def" GPR-pair P0 shape).
        assert_eq!(
            aarch64_operand_roles(AArch64Opcode::NeonStpQPost, 4),
            vec![
                OperandRole::Use,
                OperandRole::Use,
                OperandRole::DefUse,
                OperandRole::Use,
            ],
            "STP Q-pair post-index reads both stored Q registers and updates base"
        );
        assert_eq!(
            aarch64_def_operand_positions(AArch64Opcode::NeonStpQPost, 4),
            vec![2],
            "STP Q-pair writeback: ONLY the base is a def (data regs are uses)"
        );
        assert_eq!(
            aarch64_use_operand_positions(AArch64Opcode::NeonStpQPost, 4),
            vec![0, 1, 2, 3],
            "STP Q-pair reads both Q registers, the old base, and the immediate"
        );
        assert_eq!(
            aarch64_operand_roles(AArch64Opcode::StpPreIndex, 4),
            vec![
                OperandRole::Use,
                OperandRole::Use,
                OperandRole::DefUse,
                OperandRole::Use,
            ],
            "STP pre-index reads both stored registers and updates base"
        );
        assert_eq!(
            aarch64_operand_roles(AArch64Opcode::LdrPreIndex, 3),
            vec![OperandRole::Def, OperandRole::DefUse, OperandRole::Use],
            "LDR pre-index defines loaded register and updates base"
        );
        assert_eq!(
            aarch64_operand_roles(AArch64Opcode::LdrPostIndex, 3),
            vec![OperandRole::Def, OperandRole::DefUse, OperandRole::Use],
            "LDR post-index defines loaded register and updates base"
        );
        assert_eq!(
            aarch64_operand_roles(AArch64Opcode::StrPreIndex, 3),
            vec![OperandRole::Use, OperandRole::DefUse, OperandRole::Use],
            "STR pre-index reads stored register and updates base"
        );
        assert_eq!(
            aarch64_operand_roles(AArch64Opcode::StrPostIndex, 3),
            vec![OperandRole::Use, OperandRole::DefUse, OperandRole::Use],
            "STR post-index reads stored register and updates base"
        );

        assert_eq!(
            aarch64_def_operand_positions(AArch64Opcode::NeonSt1Post, 3),
            vec![1],
            "post-index store base writeback must be visible as a def"
        );
        assert_eq!(
            aarch64_use_operand_positions(AArch64Opcode::NeonSt1Post, 3),
            vec![0, 1, 2],
            "post-index store still reads vector, old base, and arrangement"
        );
        assert_eq!(
            aarch64_def_operand_positions(AArch64Opcode::LdrPostIndex, 3),
            vec![0, 1],
            "single writeback load defines the loaded register and base"
        );
        assert_eq!(
            aarch64_use_operand_positions(AArch64Opcode::StrPostIndex, 3),
            vec![0, 1, 2],
            "single writeback store reads stored value, old base, and offset"
        );
    }

    #[test]
    fn atomic_lse_def_use_operand_roles_are_conservative() {
        use AArch64Opcode::*;

        for opcode in [
            Ldadd, Ldadda, Ldaddal, Ldclr, Ldclra, Ldclral, Ldeor, Ldeora, Ldeoral, Ldset, Ldseta,
            Ldsetal, Ldsmaxa, Ldsmina, Ldumaxa, Ldumina, Swp, Swpa, Swpal,
        ] {
            assert_eq!(
                aarch64_def_operand_positions(opcode, 3),
                vec![1],
                "{opcode:?} must define old-value operand 1"
            );
            assert_eq!(
                aarch64_use_operand_positions(opcode, 3),
                vec![0, 2],
                "{opcode:?} must use update/address operands 0 and 2"
            );
            assert_eq!(opcode_effect(opcode), MemoryEffect::Store);
        }

        for opcode in [Cas, Casa, Casal] {
            assert_eq!(
                aarch64_def_operand_positions(opcode, 3),
                vec![0],
                "{opcode:?} must define expected/result operand 0"
            );
            assert_eq!(
                aarch64_use_operand_positions(opcode, 3),
                vec![0, 1, 2],
                "{opcode:?} must use expected, desired, and address operands"
            );
            assert_eq!(opcode_effect(opcode), MemoryEffect::Store);
        }
    }
}

// ===========================================================================
// x86-64 tests
// ===========================================================================

#[cfg(test)]
mod tests_x86 {
    use super::*;
    use trust_cg_ir::X86Opcode;
    use trust_cg_ir::x86_64_regs::{RAX, XMM0, XMM1};
    use trust_cg_lower::{X86ISelInst, X86ISelOperand};

    #[test]
    fn test_x86_arithmetic_is_pure() {
        assert_eq!(x86_opcode_effect(X86Opcode::AddRR), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::SubRI), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::ImulRR), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Mul), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Neg), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Inc), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Dec), MemoryEffect::Pure);
    }

    #[test]
    fn test_x86_loads_are_load() {
        assert_eq!(x86_opcode_effect(X86Opcode::MovRM8), MemoryEffect::Load);
        assert_eq!(x86_opcode_effect(X86Opcode::MovRM16), MemoryEffect::Load);
        assert_eq!(x86_opcode_effect(X86Opcode::MovRM32), MemoryEffect::Load);
        assert_eq!(x86_opcode_effect(X86Opcode::MovRM), MemoryEffect::Load);
        assert_eq!(x86_opcode_effect(X86Opcode::MovsdRM), MemoryEffect::Load);
        assert_eq!(x86_opcode_effect(X86Opcode::MovssRM), MemoryEffect::Load);
        assert_eq!(x86_opcode_effect(X86Opcode::MovdqaRM), MemoryEffect::Load);
        assert_eq!(x86_opcode_effect(X86Opcode::Ptest), MemoryEffect::Load);
        assert_eq!(x86_opcode_effect(X86Opcode::Pop), MemoryEffect::Load);
        assert_eq!(x86_opcode_effect(X86Opcode::MovRMSib), MemoryEffect::Load);
    }

    #[test]
    fn test_x86_ptest_inst_effect_distinguishes_reg_and_memory_forms() {
        let rr = X86ISelInst::new(
            X86Opcode::Ptest,
            vec![X86ISelOperand::PReg(XMM0), X86ISelOperand::PReg(XMM1)],
        );
        assert_eq!(x86_inst_effect(&rr), MemoryEffect::Pure);
        assert!(rr.flags.has_side_effects());
        assert!(!rr.flags.reads_memory());

        let rm = X86ISelInst::new(
            X86Opcode::Ptest,
            vec![
                X86ISelOperand::PReg(XMM0),
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::PReg(RAX)),
                    disp: 0,
                },
            ],
        );
        assert_eq!(x86_inst_effect(&rm), MemoryEffect::Load);
        assert!(rm.flags.has_side_effects());
        assert!(rm.flags.reads_memory());

        let malformed = X86ISelInst::new(X86Opcode::Ptest, vec![]);
        assert_eq!(x86_inst_effect(&malformed), MemoryEffect::Load);
        assert!(malformed.flags.reads_memory());
    }

    #[test]
    fn test_x86_stores_are_store() {
        assert_eq!(x86_opcode_effect(X86Opcode::MovMR8), MemoryEffect::Store);
        assert_eq!(x86_opcode_effect(X86Opcode::MovMR16), MemoryEffect::Store);
        assert_eq!(x86_opcode_effect(X86Opcode::MovMR32), MemoryEffect::Store);
        assert_eq!(x86_opcode_effect(X86Opcode::MovMR), MemoryEffect::Store);
        assert_eq!(x86_opcode_effect(X86Opcode::MovsdMR), MemoryEffect::Store);
        assert_eq!(x86_opcode_effect(X86Opcode::MovdqaMR), MemoryEffect::Store);
        assert_eq!(x86_opcode_effect(X86Opcode::Push), MemoryEffect::Store);
    }

    #[test]
    fn test_x86_calls_are_call() {
        assert_eq!(x86_opcode_effect(X86Opcode::Call), MemoryEffect::Call);
        assert_eq!(x86_opcode_effect(X86Opcode::CallR), MemoryEffect::Call);
        assert_eq!(x86_opcode_effect(X86Opcode::CallM), MemoryEffect::Call);
        assert_eq!(x86_opcode_effect(X86Opcode::Mfence), MemoryEffect::Call);
    }

    #[test]
    fn test_x86_moves_are_pure() {
        assert_eq!(x86_opcode_effect(X86Opcode::MovRR), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::MovRR32), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::MovRI), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Lea), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Ud2), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Cvttsd2si), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Cvttss2si), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Pand), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Pandn), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Por), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Pxor), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Pcmpeqb), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Pcmpeqw), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Pcmpgtb), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Pcmpgtw), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Pcmpeqd), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Pcmpgtd), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Paddb), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Paddw), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Paddd), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Psubb), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Psubw), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Psubd), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Paddq), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Psubq), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Punpckldq), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Punpcklqdq), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Pcmpeqq), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Pcmpgtq), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Pshufd), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Pmovmskb), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::MovdqaRR), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Pinsrd), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Pextrd), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Pinsrq), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Pextrq), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Pblendvb), MemoryEffect::Pure);
        assert_eq!(
            x86_opcode_effect(X86Opcode::V4I32MaskExtract),
            MemoryEffect::Pure
        );
        assert_eq!(
            x86_opcode_effect(X86Opcode::V16I8MaskExtract),
            MemoryEffect::Pure
        );
        assert_eq!(
            x86_opcode_effect(X86Opcode::V8I16MaskExtract),
            MemoryEffect::Pure
        );
        assert_eq!(
            x86_opcode_effect(X86Opcode::V2I64MaskExtract),
            MemoryEffect::Pure
        );
        assert_eq!(
            x86_opcode_effect(X86Opcode::V128BoolSelect),
            MemoryEffect::Pure
        );
    }

    #[test]
    fn test_x86_produces_value() {
        assert!(x86_produces_value(X86Opcode::AddRR));
        assert!(x86_produces_value(X86Opcode::MovRR));
        assert!(x86_produces_value(X86Opcode::MovRR32));
        assert!(x86_produces_value(X86Opcode::MovRI));
        assert!(x86_produces_value(X86Opcode::Lea));
        assert!(x86_produces_value(X86Opcode::Cmovcc));
        assert!(x86_produces_value(X86Opcode::Cmovcc32));
        assert!(x86_produces_value(X86Opcode::Setcc));
        assert!(x86_produces_value(X86Opcode::Pop));
        assert!(x86_produces_value(X86Opcode::MovdqaRM));
        assert!(x86_produces_value(X86Opcode::Cvttsd2si));
        assert!(x86_produces_value(X86Opcode::Cvttss2si));
        assert!(x86_produces_value(X86Opcode::Pblendvb));
        assert!(x86_produces_value(X86Opcode::V128BoolSelect));

        assert!(!x86_produces_value(X86Opcode::CmpRR));
        assert!(!x86_produces_value(X86Opcode::CmpRI));
        assert!(!x86_produces_value(X86Opcode::TestRR));
        assert!(!x86_produces_value(X86Opcode::Ptest));
        assert!(!x86_produces_value(X86Opcode::MovMR8));
        assert!(!x86_produces_value(X86Opcode::MovMR16));
        assert!(!x86_produces_value(X86Opcode::MovMR32));
        assert!(!x86_produces_value(X86Opcode::MovMR));
        assert!(!x86_produces_value(X86Opcode::MovdqaMR));
        assert!(!x86_produces_value(X86Opcode::Push));
        assert!(!x86_produces_value(X86Opcode::Jmp));
        assert!(!x86_produces_value(X86Opcode::Ret));
        assert!(!x86_produces_value(X86Opcode::Call));
        assert!(!x86_produces_value(X86Opcode::Nop));
        assert!(!x86_produces_value(X86Opcode::Mfence));
        assert!(!x86_produces_value(X86Opcode::Idiv));
        assert!(!x86_produces_value(X86Opcode::Div));
        assert!(!x86_produces_value(X86Opcode::Mul));
        assert!(!x86_produces_value(X86Opcode::Ud2));
    }

    #[test]
    fn test_x86_removable() {
        // Moves and LEA are removable (no flag side effects)
        assert!(x86_is_removable(X86Opcode::MovRR));
        assert!(x86_is_removable(X86Opcode::MovRR32));
        assert!(x86_is_removable(X86Opcode::MovRI));
        assert!(x86_is_removable(X86Opcode::Lea));
        assert!(x86_is_removable(X86Opcode::Movzx));
        assert!(x86_is_removable(X86Opcode::Cvttsd2si));
        assert!(x86_is_removable(X86Opcode::Cvttss2si));
        assert!(x86_is_removable(X86Opcode::MovdqaRR));
        assert!(x86_is_removable(X86Opcode::Pand));
        assert!(x86_is_removable(X86Opcode::Pandn));
        assert!(x86_is_removable(X86Opcode::Por));
        assert!(x86_is_removable(X86Opcode::Pxor));
        assert!(x86_is_removable(X86Opcode::Pcmpeqb));
        assert!(x86_is_removable(X86Opcode::Pcmpeqw));
        assert!(x86_is_removable(X86Opcode::Pcmpgtb));
        assert!(x86_is_removable(X86Opcode::Pcmpgtw));
        assert!(x86_is_removable(X86Opcode::Pcmpeqd));
        assert!(x86_is_removable(X86Opcode::Pcmpgtd));
        assert!(x86_is_removable(X86Opcode::Paddb));
        assert!(x86_is_removable(X86Opcode::Paddw));
        assert!(x86_is_removable(X86Opcode::Psubb));
        assert!(x86_is_removable(X86Opcode::Psubw));
        assert!(x86_is_removable(X86Opcode::Paddq));
        assert!(x86_is_removable(X86Opcode::Psubq));
        assert!(x86_is_removable(X86Opcode::Pcmpeqq));
        assert!(x86_is_removable(X86Opcode::Pcmpgtq));
        assert!(x86_is_removable(X86Opcode::Punpckldq));
        assert!(x86_is_removable(X86Opcode::Punpcklqdq));
        assert!(x86_is_removable(X86Opcode::Pshufd));
        assert!(x86_is_removable(X86Opcode::Pmovmskb));
        assert!(x86_is_removable(X86Opcode::Pinsrd));
        assert!(x86_is_removable(X86Opcode::Pextrd));
        assert!(x86_is_removable(X86Opcode::Pinsrq));
        assert!(x86_is_removable(X86Opcode::Pextrq));
        assert!(x86_is_removable(X86Opcode::Pblendvb));
        assert!(x86_is_removable(X86Opcode::V128BoolSelect));
        assert!(
            !x86_is_removable(X86Opcode::V4I32MaskExtract),
            "pseudo lowering normalizes with scalar flag-writing instructions"
        );
        assert!(
            !x86_is_removable(X86Opcode::V16I8MaskExtract),
            "pseudo lowering normalizes with scalar flag-writing instructions"
        );
        assert!(
            !x86_is_removable(X86Opcode::V8I16MaskExtract),
            "pseudo lowering normalizes with scalar flag-writing instructions"
        );
        assert!(
            !x86_is_removable(X86Opcode::V2I64MaskExtract),
            "pseudo lowering normalizes with scalar flag-writing instructions"
        );

        // Arithmetic is NOT removable (sets RFLAGS)
        assert!(!x86_is_removable(X86Opcode::AddRR));
        assert!(!x86_is_removable(X86Opcode::SubRR));
        assert!(!x86_is_removable(X86Opcode::ImulRR));
        assert!(!x86_is_removable(X86Opcode::Mul));

        // Memory ops are not removable
        assert!(!x86_is_removable(X86Opcode::MovRM8));
        assert!(!x86_is_removable(X86Opcode::MovMR8));
        assert!(!x86_is_removable(X86Opcode::MovRM));
        assert!(!x86_is_removable(X86Opcode::MovMR));
        assert!(!x86_is_removable(X86Opcode::Ptest));
        assert!(!x86_is_removable(X86Opcode::Call));
        assert!(!x86_is_removable(X86Opcode::Mfence));
        assert!(!x86_is_removable(X86Opcode::Ud2));
    }

    #[test]
    fn test_x86_writes_flags() {
        // x86 arithmetic sets flags (unlike AArch64)
        assert!(x86_writes_flags(X86Opcode::AddRR));
        assert!(x86_writes_flags(X86Opcode::SubRR));
        assert!(x86_writes_flags(X86Opcode::ImulRR));
        assert!(x86_writes_flags(X86Opcode::Mul));
        assert!(x86_writes_flags(X86Opcode::Neg));
        assert!(x86_writes_flags(X86Opcode::AndRR));
        assert!(x86_writes_flags(X86Opcode::ShlRI));
        assert!(x86_writes_flags(X86Opcode::CmpRR));
        assert!(x86_writes_flags(X86Opcode::TestRR));
        assert!(x86_writes_flags(X86Opcode::Ptest));

        // Moves and LEA do NOT set flags
        assert!(!x86_writes_flags(X86Opcode::MovRR));
        assert!(!x86_writes_flags(X86Opcode::MovRR32));
        assert!(!x86_writes_flags(X86Opcode::MovRI));
        assert!(!x86_writes_flags(X86Opcode::Lea));
        assert!(!x86_writes_flags(X86Opcode::Cmovcc));
        assert!(!x86_writes_flags(X86Opcode::Cmovcc32));
        assert!(!x86_writes_flags(X86Opcode::Mfence));
        assert!(!x86_writes_flags(X86Opcode::Ud2));
        assert!(!x86_writes_flags(X86Opcode::Cvttsd2si));
        assert!(!x86_writes_flags(X86Opcode::Cvttss2si));
        assert!(!x86_writes_flags(X86Opcode::Pand));
        assert!(!x86_writes_flags(X86Opcode::Pandn));
        assert!(!x86_writes_flags(X86Opcode::Pcmpeqb));
        assert!(!x86_writes_flags(X86Opcode::Pcmpeqw));
        assert!(!x86_writes_flags(X86Opcode::Pcmpgtb));
        assert!(!x86_writes_flags(X86Opcode::Pcmpgtw));
        assert!(!x86_writes_flags(X86Opcode::Pcmpeqd));
        assert!(!x86_writes_flags(X86Opcode::Pcmpgtd));
        assert!(!x86_writes_flags(X86Opcode::Paddb));
        assert!(!x86_writes_flags(X86Opcode::Paddw));
        assert!(!x86_writes_flags(X86Opcode::Psubb));
        assert!(!x86_writes_flags(X86Opcode::Psubw));
        assert!(!x86_writes_flags(X86Opcode::Paddq));
        assert!(!x86_writes_flags(X86Opcode::Psubq));
        assert!(!x86_writes_flags(X86Opcode::Pcmpeqq));
        assert!(!x86_writes_flags(X86Opcode::Pcmpgtq));
        assert!(!x86_writes_flags(X86Opcode::Punpckldq));
        assert!(!x86_writes_flags(X86Opcode::Punpcklqdq));
        assert!(!x86_writes_flags(X86Opcode::Pmovmskb));
        assert!(x86_writes_flags(X86Opcode::V4I32MaskExtract));
        assert!(x86_writes_flags(X86Opcode::V16I8MaskExtract));
        assert!(x86_writes_flags(X86Opcode::V8I16MaskExtract));
        assert!(x86_writes_flags(X86Opcode::V2I64MaskExtract));
    }

    #[test]
    fn test_x86_reads_flags() {
        assert!(x86_reads_flags(X86Opcode::Cmovcc));
        assert!(x86_reads_flags(X86Opcode::Cmovcc32));
        assert!(x86_reads_flags(X86Opcode::Setcc));
        assert!(x86_reads_flags(X86Opcode::Jcc));

        assert!(!x86_reads_flags(X86Opcode::AddRR));
        assert!(!x86_reads_flags(X86Opcode::CmpRR));
        assert!(!x86_reads_flags(X86Opcode::Ptest));
        assert!(!x86_reads_flags(X86Opcode::Mul));
        assert!(!x86_reads_flags(X86Opcode::MovRR));
        assert!(!x86_reads_flags(X86Opcode::MovRR32));
        assert!(!x86_reads_flags(X86Opcode::Ud2));
        assert!(!x86_reads_flags(X86Opcode::Cvttsd2si));
        assert!(!x86_reads_flags(X86Opcode::Cvttss2si));
    }

    #[test]
    fn test_x86_sse_is_pure() {
        assert_eq!(x86_opcode_effect(X86Opcode::Addsd), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Mulsd), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Addss), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::MovsdRR), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::MovssRR), MemoryEffect::Pure);
    }

    #[test]
    fn test_x86_conversion_is_pure() {
        assert_eq!(x86_opcode_effect(X86Opcode::Cvtsi2sd), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Cvtsd2si), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Cvttsd2si), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Cvttss2si), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Cvtsd2ss), MemoryEffect::Pure);
        assert_eq!(x86_opcode_effect(X86Opcode::Cvtss2sd), MemoryEffect::Pure);
    }
}

// ===========================================================================
// Category-based tests
// ===========================================================================

#[cfg(test)]
mod tests_category {
    use super::*;
    use trust_cg_ir::OpcodeCategory;

    #[test]
    fn test_category_memory_effect_load() {
        assert_eq!(
            category_memory_effect(OpcodeCategory::Load),
            MemoryEffect::Load
        );
    }

    #[test]
    fn test_category_memory_effect_store() {
        assert_eq!(
            category_memory_effect(OpcodeCategory::Store),
            MemoryEffect::Store
        );
    }

    #[test]
    fn test_category_memory_effect_call() {
        assert_eq!(
            category_memory_effect(OpcodeCategory::Call),
            MemoryEffect::Call
        );
    }

    #[test]
    fn test_category_memory_effect_pure_arithmetic() {
        assert_eq!(
            category_memory_effect(OpcodeCategory::AddRR),
            MemoryEffect::Pure
        );
        assert_eq!(
            category_memory_effect(OpcodeCategory::SubRI),
            MemoryEffect::Pure
        );
        assert_eq!(
            category_memory_effect(OpcodeCategory::MulRR),
            MemoryEffect::Pure
        );
        assert_eq!(
            category_memory_effect(OpcodeCategory::Neg),
            MemoryEffect::Pure
        );
    }

    #[test]
    fn test_category_memory_effect_pure_logical() {
        assert_eq!(
            category_memory_effect(OpcodeCategory::AndRR),
            MemoryEffect::Pure
        );
        assert_eq!(
            category_memory_effect(OpcodeCategory::OrRI),
            MemoryEffect::Pure
        );
        assert_eq!(
            category_memory_effect(OpcodeCategory::XorRR),
            MemoryEffect::Pure
        );
    }

    #[test]
    fn test_category_memory_effect_pure_moves() {
        assert_eq!(
            category_memory_effect(OpcodeCategory::MovRR),
            MemoryEffect::Pure
        );
        assert_eq!(
            category_memory_effect(OpcodeCategory::MovRI),
            MemoryEffect::Pure
        );
    }

    #[test]
    fn test_category_memory_effect_other_is_pure() {
        // Other is conservatively pure (target-specific, but no known memory effect)
        assert_eq!(
            category_memory_effect(OpcodeCategory::Other),
            MemoryEffect::Pure
        );
    }

    #[test]
    fn test_category_is_removable_pure_no_flags() {
        assert!(category_is_removable(OpcodeCategory::AddRR, false));
        assert!(category_is_removable(OpcodeCategory::MovRR, false));
        assert!(category_is_removable(OpcodeCategory::ShlRI, false));
    }

    #[test]
    fn test_category_is_removable_memory_ops() {
        assert!(!category_is_removable(OpcodeCategory::Load, false));
        assert!(!category_is_removable(OpcodeCategory::Store, false));
        assert!(!category_is_removable(OpcodeCategory::Call, false));
    }

    #[test]
    fn test_category_is_removable_compare_not_removable() {
        assert!(!category_is_removable(OpcodeCategory::CmpRR, false));
        assert!(!category_is_removable(OpcodeCategory::CmpRI, false));
    }

    #[test]
    fn test_category_is_removable_flag_writing_not_removable() {
        // Even if category is pure, if the target says it writes flags, not removable
        assert!(!category_is_removable(OpcodeCategory::AddRR, true));
    }

    #[test]
    fn test_category_is_removable_control_flow() {
        assert!(!category_is_removable(OpcodeCategory::Branch, false));
        assert!(!category_is_removable(OpcodeCategory::CondBranch, false));
        assert!(!category_is_removable(OpcodeCategory::Ret, false));
    }

    #[test]
    fn test_category_reads_flags() {
        assert!(category_reads_flags(OpcodeCategory::CondBranch));
        assert!(!category_reads_flags(OpcodeCategory::AddRR));
        assert!(!category_reads_flags(OpcodeCategory::CmpRR));
        assert!(!category_reads_flags(OpcodeCategory::Other));
    }

    #[test]
    fn test_category_writes_flags() {
        assert!(category_writes_flags(OpcodeCategory::CmpRR));
        assert!(category_writes_flags(OpcodeCategory::CmpRI));
        assert!(!category_writes_flags(OpcodeCategory::AddRR));
        assert!(!category_writes_flags(OpcodeCategory::MovRR));
        assert!(!category_writes_flags(OpcodeCategory::Other));
    }

    // Cross-check: verify category-based classification is consistent
    // with the per-opcode AArch64 classification for categorized opcodes.
    #[test]
    fn test_category_consistent_with_aarch64_for_loads() {
        use trust_cg_ir::AArch64Opcode;
        let op = AArch64Opcode::LdrRI;
        let cat = op.categorize();
        assert_eq!(category_memory_effect(cat), opcode_effect(op));
    }

    #[test]
    fn test_category_consistent_with_aarch64_for_stores() {
        use trust_cg_ir::AArch64Opcode;
        let op = AArch64Opcode::StrRI;
        let cat = op.categorize();
        assert_eq!(category_memory_effect(cat), opcode_effect(op));
    }

    #[test]
    fn test_category_consistent_with_aarch64_for_calls() {
        use trust_cg_ir::AArch64Opcode;
        let op = AArch64Opcode::Bl;
        let cat = op.categorize();
        assert_eq!(category_memory_effect(cat), opcode_effect(op));
    }

    #[test]
    fn test_category_consistent_with_aarch64_for_arithmetic() {
        use trust_cg_ir::AArch64Opcode;
        let op = AArch64Opcode::AddRR;
        let cat = op.categorize();
        assert_eq!(category_memory_effect(cat), opcode_effect(op));
    }
}
