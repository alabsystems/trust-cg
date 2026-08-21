// trust-cg-ir - Multi-target opcode categorization
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Target-independent opcode categories and target abstraction trait.
//!
//! Optimization passes that need to reason about instruction semantics
//! (constant folding, peephole, CSE key hashing) can use [`OpcodeCategory`]
//! instead of matching target-specific opcode enums. Each target provides
//! a `categorize()` method mapping its opcodes to categories.
//!
//! # Design
//!
//! The category enum covers the *semantic* operations that optimization
//! passes care about (add, sub, shift-left, move-register, etc.). Opcodes
//! that don't map to any generic optimization pattern get [`OpcodeCategory::Other`].
//!
//! The [`TargetInfo`] trait collects per-target queries that optimization
//! passes need: categorization, value production, flag access, commutativity,
//! and canonical opcode accessors for mov/shl replacements in peephole.

use crate::inst::AArch64Opcode;
use crate::x86_64_ops::{X86Opcode, X86Sse2PackedOpcode};

// ---------------------------------------------------------------------------
// OpcodeCategory
// ---------------------------------------------------------------------------

/// Target-independent opcode category for use by optimization passes.
///
/// Passes can match on categories to apply generic transformations
/// (e.g., "add with zero immediate is identity") without knowing the
/// target-specific opcode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpcodeCategory {
    // -- Arithmetic --
    /// Register-register addition.
    AddRR,
    /// Register-immediate addition.
    AddRI,
    /// Register-register subtraction.
    SubRR,
    /// Register-immediate subtraction.
    SubRI,
    /// Register-register multiplication.
    MulRR,
    /// Unary negate.
    Neg,

    // -- Logical --
    /// Bitwise AND register-register.
    AndRR,
    /// Bitwise AND register-immediate.
    AndRI,
    /// Bitwise OR register-register.
    OrRR,
    /// Bitwise OR register-immediate.
    OrRI,
    /// Bitwise XOR register-register.
    XorRR,
    /// Bitwise XOR register-immediate.
    XorRI,

    // -- Shifts --
    /// Shift left by register.
    ShlRR,
    /// Shift left by immediate.
    ShlRI,
    /// Logical shift right by register.
    ShrRR,
    /// Logical shift right by immediate.
    ShrRI,
    /// Arithmetic shift right by register.
    SarRR,
    /// Arithmetic shift right by immediate.
    SarRI,

    // -- Move --
    /// Register-to-register move (copy).
    MovRR,
    /// Immediate-to-register move.
    MovRI,

    // -- Compare --
    /// Register-register compare (sets flags, no value produced).
    CmpRR,
    /// Register-immediate compare.
    CmpRI,

    // -- Control flow --
    /// No-operation.
    Nop,
    /// Function return.
    Ret,
    /// Function call.
    Call,
    /// Unconditional branch.
    Branch,
    /// Conditional branch.
    CondBranch,

    // -- Memory --
    /// Load from memory.
    Load,
    /// Store to memory.
    Store,

    // -- SSA --
    /// Phi node (SSA merge point).
    Phi,

    // -- Catch-all --
    /// Target-specific opcode with no generic category.
    Other,
}

impl OpcodeCategory {
    /// Returns true if this category is a binary arithmetic operation
    /// that optimization passes commonly fold or simplify.
    #[inline]
    pub fn is_arithmetic(self) -> bool {
        matches!(
            self,
            Self::AddRR | Self::AddRI | Self::SubRR | Self::SubRI | Self::MulRR | Self::Neg
        )
    }

    /// Returns true if this category is a binary logical operation.
    #[inline]
    pub fn is_logical(self) -> bool {
        matches!(
            self,
            Self::AndRR | Self::AndRI | Self::OrRR | Self::OrRI | Self::XorRR | Self::XorRI
        )
    }

    /// Returns true if this category is a shift operation.
    #[inline]
    pub fn is_shift(self) -> bool {
        matches!(
            self,
            Self::ShlRR | Self::ShlRI | Self::ShrRR | Self::ShrRI | Self::SarRR | Self::SarRI
        )
    }

    /// Returns true if this category is a move (register or immediate).
    #[inline]
    pub fn is_move(self) -> bool {
        matches!(self, Self::MovRR | Self::MovRI)
    }

    /// Returns true if this is a register-immediate form (has an immediate
    /// operand that optimization passes can inspect).
    #[inline]
    pub fn is_reg_imm(self) -> bool {
        matches!(
            self,
            Self::AddRI
                | Self::SubRI
                | Self::AndRI
                | Self::OrRI
                | Self::XorRI
                | Self::ShlRI
                | Self::ShrRI
                | Self::SarRI
                | Self::CmpRI
                | Self::MovRI
        )
    }

    /// Returns true if this is a register-register form where both source
    /// operands being the same register enables special simplifications
    /// (e.g., sub x,x = 0, or x,x = x, xor x,x = 0).
    #[inline]
    pub fn is_reg_reg_binary(self) -> bool {
        matches!(
            self,
            Self::AddRR
                | Self::SubRR
                | Self::MulRR
                | Self::AndRR
                | Self::OrRR
                | Self::XorRR
                | Self::ShlRR
                | Self::ShrRR
                | Self::SarRR
        )
    }
}

// ---------------------------------------------------------------------------
// AArch64Opcode::categorize
// ---------------------------------------------------------------------------

impl AArch64Opcode {
    /// Classify this AArch64 opcode into a target-independent category.
    pub fn categorize(self) -> OpcodeCategory {
        use AArch64Opcode::*;
        match self {
            // Arithmetic
            AddRR | NeonAddV => OpcodeCategory::AddRR,
            AddRI | AddRIShift12 => OpcodeCategory::AddRI,
            SubRR | NeonSubV => OpcodeCategory::SubRR,
            SubRI => OpcodeCategory::SubRI,
            MulRR | NeonMulV => OpcodeCategory::MulRR,
            Neg => OpcodeCategory::Neg,

            // Logical (AArch64 uses Orr/Eor naming)
            AndRR => OpcodeCategory::AndRR,
            AndRI => OpcodeCategory::AndRI,
            OrrRR => OpcodeCategory::OrRR,
            OrrRI => OpcodeCategory::OrRI,
            EorRR | EorRRShift | EorRRLsl | EorRRLsr => OpcodeCategory::XorRR,
            EorRI => OpcodeCategory::XorRI,

            // Shifts (AArch64 uses Lsl/Lsr/Asr naming)
            LslRR => OpcodeCategory::ShlRR,
            LslRI => OpcodeCategory::ShlRI,
            LsrRR => OpcodeCategory::ShrRR,
            LsrRI => OpcodeCategory::ShrRI,
            AsrRR => OpcodeCategory::SarRR,
            AsrRI => OpcodeCategory::SarRI,

            // Moves
            MovR | Copy | MOVWrr | MOVXrr => OpcodeCategory::MovRR,
            MovI | Movz | Movn | MOVZWi | MOVZXi => OpcodeCategory::MovRI,

            // Compare
            CmpRR | CMPWrr | CMPXrr => OpcodeCategory::CmpRR,
            CmpRI | CMPWri | CMPXri => OpcodeCategory::CmpRI,

            // Control flow
            B | Br => OpcodeCategory::Branch,
            BCond | Bcc | Cbz | Cbnz | Tbz | Tbnz => OpcodeCategory::CondBranch,
            Bl | Blr | BL | BLR | TailCall => OpcodeCategory::Call,
            Ret => OpcodeCategory::Ret,

            // Memory loads
            LdrRI | LdrPreIndex | LdrPostIndex | LdrbRI | LdrhRI | LdrsbRI | LdrshRI
            | LdrLiteral | LdpRI | LdpPostIndex | LdrRO | LdrbRO | LdrhRO | LdrswRO | LdrGot
            | LdrTlvp | LdrGottprel | NeonLd1Post | NeonLdpQPost | Ldar | Ldarb | Ldarh | Ldaxr => {
                OpcodeCategory::Load
            }

            // Memory stores
            StrRI | StrPreIndex | StrPostIndex | StrbRI | StrhRI | StpRI | StpPreIndex | StrRO
            | StrbRO | StrhRO | STRWui | STRXui | STRSui | STRDui | NeonSt1Post | NeonStpQPost
            | Stlr | Stlrb | Stlrh | Stlxr => OpcodeCategory::Store,

            // Pseudo
            Phi => OpcodeCategory::Phi,
            Nop => OpcodeCategory::Nop,

            // Everything else: target-specific without a generic category
            _ => OpcodeCategory::Other,
        }
    }
}

// ---------------------------------------------------------------------------
// X86Opcode::categorize
// ---------------------------------------------------------------------------

impl X86Opcode {
    /// Classify this x86-64 opcode into a target-independent category.
    pub fn categorize(self) -> OpcodeCategory {
        use X86Opcode::*;
        match self {
            // Arithmetic
            AddRR => OpcodeCategory::AddRR,
            AddRI => OpcodeCategory::AddRI,
            SubRR => OpcodeCategory::SubRR,
            SubRI => OpcodeCategory::SubRI,
            Paddb | Paddw | Paddd | Paddq => OpcodeCategory::AddRR,
            Psubb | Psubw | Psubd | Psubq => OpcodeCategory::SubRR,
            ImulRR | Pmullw => OpcodeCategory::MulRR,
            Neg => OpcodeCategory::Neg,

            // Logical (x86 uses Or/Xor naming)
            AndRR => OpcodeCategory::AndRR,
            AndRI => OpcodeCategory::AndRI,
            OrRR => OpcodeCategory::OrRR,
            OrRI => OpcodeCategory::OrRI,
            XorRR => OpcodeCategory::XorRR,
            XorRI => OpcodeCategory::XorRI,
            Pand => OpcodeCategory::AndRR,
            Por => OpcodeCategory::OrRR,
            Pxor => OpcodeCategory::XorRR,

            // Shifts (x86 uses Shl/Shr/Sar naming)
            ShlRR => OpcodeCategory::ShlRR,
            ShlRI => OpcodeCategory::ShlRI,
            ShrRR => OpcodeCategory::ShrRR,
            ShrRI => OpcodeCategory::ShrRI,
            SarRR => OpcodeCategory::SarRR,
            SarRI => OpcodeCategory::SarRI,

            // Moves
            MovRR | MovRR32 | MovsdRR | MovssRR | MovdqaRR => OpcodeCategory::MovRR,
            MovRI => OpcodeCategory::MovRI,

            // Compare
            CmpRR => OpcodeCategory::CmpRR,
            CmpRI | CmpRI8 => OpcodeCategory::CmpRI,

            // Control flow
            Jmp => OpcodeCategory::Branch,
            // Indirect near jump (jump-table dispatch) — a branch/terminator
            // like `Jmp`; falling into `Other` would hide it from the CFG/scheduler.
            JmpR => OpcodeCategory::Branch,
            Jcc => OpcodeCategory::CondBranch,
            Call | CallR | CallM => OpcodeCategory::Call,
            Ret => OpcodeCategory::Ret,

            // Memory loads
            MovRM8 | MovRM16 | MovRM32 | MovRM | MovsdRM | MovssRM | MovRMSib | MovsxdRMSib
            | MovRM32Sib | AddRM | SubRM | CmpRM | ImulRM | ImulRMSib | TestRM | Ptest
            | MovRipRel | MovRipRelTlv | MovssRipRel | MovsdRipRel | Pop => OpcodeCategory::Load,

            // Memory stores
            MovMR8 | MovMR16 | MovMR32 | MovMR | MovsdMR | MovssMR | MovMRSib | MovMR32Sib
            | Push => OpcodeCategory::Store,

            // Pseudo
            Phi => OpcodeCategory::Phi,
            V4I32MaskExtract | V16I8MaskExtract | V8I16MaskExtract | V2I64MaskExtract => {
                OpcodeCategory::Other
            }
            Nop => OpcodeCategory::Nop,

            // Everything else: target-specific
            _ => OpcodeCategory::Other,
        }
    }
}

// ---------------------------------------------------------------------------
// X86Sse2PackedOpcode::categorize
// ---------------------------------------------------------------------------

impl X86Sse2PackedOpcode {
    /// Classify this standalone SSE2 packed opcode into a target-independent
    /// category where the semantics line up with scalar optimization concepts.
    pub fn categorize(self) -> OpcodeCategory {
        use X86Sse2PackedOpcode::*;
        match self {
            Pand => OpcodeCategory::AndRR,
            Por => OpcodeCategory::OrRR,
            Pxor => OpcodeCategory::XorRR,
            MovdqaRR => OpcodeCategory::MovRR,
            Paddb | Paddw | Paddd | Paddq => OpcodeCategory::AddRR,
            Psubb | Psubw | Psubd | Psubq => OpcodeCategory::SubRR,
            Pandn | Pcmpeqb | Pcmpeqw | Pcmpeqd | Pshufd | Pmovmskb | Pcmpgtb | Pcmpgtw
            | Pcmpgtd | Pcmpeqq | Pcmpgtq | Punpcklbw | Punpckldq | Packuswb | Punpckhbw
            | Punpcklqdq | Pmuludq | Pslld | Psrld | Psrad | Psllq | Psrlq => OpcodeCategory::Other,
            Pmullw => OpcodeCategory::MulRR,
        }
    }
}

// ---------------------------------------------------------------------------
// TargetInfo trait
// ---------------------------------------------------------------------------

/// Target abstraction for optimization passes.
///
/// Provides target-independent queries needed by passes like peephole,
/// constant folding, CSE, and DCE. Each target (AArch64, x86-64)
/// implements this trait.
///
/// Note: memory effects (`MemoryEffect`) are NOT included here because
/// that type is defined in `trust-cg-opt`, not `trust-cg-ir`. Memory effect
/// queries remain in `trust-cg-opt/src/effects.rs`.
pub trait TargetInfo {
    /// The target-specific opcode type.
    type Opcode: Copy + Eq + core::hash::Hash + core::fmt::Debug;

    /// Classify an opcode into a target-independent category.
    fn categorize(opcode: Self::Opcode) -> OpcodeCategory;

    /// Does this opcode produce a value (operand[0] is a def)?
    fn produces_value(opcode: Self::Opcode) -> bool;

    /// Does this opcode write implicit condition flags?
    fn writes_flags(opcode: Self::Opcode) -> bool;

    /// Does this opcode read implicit condition flags?
    fn reads_flags(opcode: Self::Opcode) -> bool;

    /// Is this opcode commutative (operand order doesn't affect result)?
    fn is_commutative(opcode: Self::Opcode) -> bool;

    /// Return the register-to-register move opcode for this target.
    fn mov_rr() -> Self::Opcode;

    /// Return the immediate-to-register move opcode for this target.
    fn mov_ri() -> Self::Opcode;

    /// Return the shift-left-by-immediate opcode for this target.
    fn shl_ri() -> Self::Opcode;

    /// Return the register-register subtraction opcode for this target.
    fn sub_rr() -> Self::Opcode;

    /// Return the register-register addition opcode for this target.
    fn add_rr() -> Self::Opcode;

    /// Return the negate opcode for this target.
    fn neg() -> Self::Opcode;

    /// Return the register-immediate subtraction opcode for this target.
    fn sub_ri() -> Self::Opcode;

    /// Return the register-immediate addition opcode for this target.
    fn add_ri() -> Self::Opcode;
}

// ---------------------------------------------------------------------------
// AArch64Target
// ---------------------------------------------------------------------------

/// AArch64 target implementation.
pub struct AArch64Target;

impl TargetInfo for AArch64Target {
    type Opcode = AArch64Opcode;

    #[inline]
    fn categorize(opcode: AArch64Opcode) -> OpcodeCategory {
        opcode.categorize()
    }

    #[inline]
    fn produces_value(opcode: AArch64Opcode) -> bool {
        opcode.produces_value()
    }

    fn writes_flags(opcode: AArch64Opcode) -> bool {
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

    fn reads_flags(opcode: AArch64Opcode) -> bool {
        use AArch64Opcode::*;
        // Must stay in sync with `trust_cg_opt::effects::reads_flags`.
        // - CSEL-family: test NZCV against a condition code immediate.
        // - FCSEL: the scalar FP conditional select reads NZCV exactly like
        //   the integer CSEL family (this entry had drifted out of sync with
        //   `effects::reads_flags`; every scheduling/liveness consumer relies
        //   on this target model being complete).
        // - ADC/SBC: consume the carry flag for i128 multi-precision
        //   arithmetic. Classifying them here keeps any TargetInfo-based
        //   consumer from reordering/CSE'ing ADC/SBC across a flag writer.
        //   See issue #409.
        matches!(
            opcode,
            CSet | Csel | Csinc | Csinv | Csneg | FcselRR | Adc | Sbc
        )
    }

    fn is_commutative(opcode: AArch64Opcode) -> bool {
        opcode.is_commutative()
    }

    #[inline]
    fn mov_rr() -> AArch64Opcode {
        AArch64Opcode::MovR
    }

    #[inline]
    fn mov_ri() -> AArch64Opcode {
        AArch64Opcode::MovI
    }

    #[inline]
    fn shl_ri() -> AArch64Opcode {
        AArch64Opcode::LslRI
    }

    #[inline]
    fn sub_rr() -> AArch64Opcode {
        AArch64Opcode::SubRR
    }

    #[inline]
    fn add_rr() -> AArch64Opcode {
        AArch64Opcode::AddRR
    }

    #[inline]
    fn neg() -> AArch64Opcode {
        AArch64Opcode::Neg
    }

    #[inline]
    fn sub_ri() -> AArch64Opcode {
        AArch64Opcode::SubRI
    }

    #[inline]
    fn add_ri() -> AArch64Opcode {
        AArch64Opcode::AddRI
    }
}

// ---------------------------------------------------------------------------
// X86_64Target
// ---------------------------------------------------------------------------

/// x86-64 target implementation.
pub struct X86_64Target;

impl TargetInfo for X86_64Target {
    type Opcode = X86Opcode;

    #[inline]
    fn categorize(opcode: X86Opcode) -> OpcodeCategory {
        opcode.categorize()
    }

    fn produces_value(opcode: X86Opcode) -> bool {
        use X86Opcode::*;
        // Instructions that do NOT produce a value:
        !matches!(
            opcode,
            // Compare/test: only set flags
            CmpRR | CmpRI | CmpRI8 | CmpRM | TestRR | TestRI | TestRM
            | Ucomisd | Ucomiss | BtRI | Ptest
            // Stores
            | MovMR8 | MovMR16 | MovMR32 | MovMR | MovsdMR | MovssMR | MovMRSib
            // Branches and control flow
            | Jmp | JmpR | Jcc | Call | CallR | CallM | Ret
            // Stack store
            | Push
            // Pseudo with no value
            | Nop | NopMulti | StackAlloc
            // Memory fence
            | Mfence
            // Atomic exchange (complex implicit operands)
            | Cmpxchg | Cmpxchg8 | Cmpxchg16
            // Sign-extend implicit writes
            | Cdq | Cqo
            // Fixed-register arithmetic with implicit results
            | Idiv | Div | Mul
            // Trap terminator
            | Ud2
        )
    }

    fn writes_flags(opcode: X86Opcode) -> bool {
        use X86Opcode::*;
        // On x86, almost ALL arithmetic/logical/shift instructions set RFLAGS.
        // Only moves, LEA, and pseudo-instructions do NOT set flags.
        matches!(
            opcode,
            // Arithmetic
            AddRR | AddRI | AddRM | SubRR | SubRI | SubRM
            | ImulRR | ImulRRI | ImulRM | ImulRMSib | Idiv | Div | Mul
            | Neg | Inc | Dec
            // Logical
            | AndRR | AndRI | OrRR | OrRI | XorRR | XorRI | Not
            // Shifts
            | ShlRR | ShlRI | ShrRR | ShrRI | SarRR | SarRI
            // Compare/test
            | CmpRR | CmpRI | CmpRI8 | CmpRM | TestRR | TestRI | TestRM
            | Ptest
            // FP compare
            | Ucomisd | Ucomiss
            // Bit manipulation that sets flags
            | Bsf | Bsr | Tzcnt | Lzcnt | Popcnt | BtRI
            // Atomic
            | Cmpxchg | Cmpxchg8 | Cmpxchg16
            | AtomicRmwCasLoop
            | V4I32MaskExtract
            | V16I8MaskExtract
            | V8I16MaskExtract
            | V2I64MaskExtract
        )
    }

    fn reads_flags(opcode: X86Opcode) -> bool {
        use X86Opcode::*;
        matches!(opcode, Cmovcc | Cmovcc32 | Setcc | Jcc)
    }

    fn is_commutative(opcode: X86Opcode) -> bool {
        use X86Opcode::*;
        matches!(
            opcode,
            AddRR
                | ImulRR
                | AndRR
                | OrRR
                | XorRR
                | Addsd
                | Mulsd
                | Andpd
                | Addss
                | Mulss
                | Andps
                | Addps
                | Mulps
                | Addpd
                | Mulpd
                | Pand
                | Por
                | Pxor
                | Pcmpeqb
                | Pcmpeqw
                | Pcmpeqd
                | Pcmpeqq
                | Paddb
                | Paddw
                | Paddd
                | Paddq
                | Pmullw
                | Xchg
        )
    }

    #[inline]
    fn mov_rr() -> X86Opcode {
        X86Opcode::MovRR
    }

    #[inline]
    fn mov_ri() -> X86Opcode {
        X86Opcode::MovRI
    }

    #[inline]
    fn shl_ri() -> X86Opcode {
        X86Opcode::ShlRI
    }

    #[inline]
    fn sub_rr() -> X86Opcode {
        X86Opcode::SubRR
    }

    #[inline]
    fn add_rr() -> X86Opcode {
        X86Opcode::AddRR
    }

    #[inline]
    fn neg() -> X86Opcode {
        X86Opcode::Neg
    }

    #[inline]
    fn sub_ri() -> X86Opcode {
        X86Opcode::SubRI
    }

    #[inline]
    fn add_ri() -> X86Opcode {
        X86Opcode::AddRI
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // -- OpcodeCategory helper tests --

    #[test]
    fn category_is_arithmetic() {
        assert!(OpcodeCategory::AddRR.is_arithmetic());
        assert!(OpcodeCategory::SubRI.is_arithmetic());
        assert!(OpcodeCategory::Neg.is_arithmetic());
        assert!(!OpcodeCategory::AndRR.is_arithmetic());
        assert!(!OpcodeCategory::ShlRI.is_arithmetic());
        assert!(!OpcodeCategory::Other.is_arithmetic());
    }

    #[test]
    fn category_is_logical() {
        assert!(OpcodeCategory::AndRR.is_logical());
        assert!(OpcodeCategory::OrRI.is_logical());
        assert!(OpcodeCategory::XorRR.is_logical());
        assert!(!OpcodeCategory::AddRR.is_logical());
    }

    #[test]
    fn category_is_shift() {
        assert!(OpcodeCategory::ShlRR.is_shift());
        assert!(OpcodeCategory::SarRI.is_shift());
        assert!(!OpcodeCategory::AddRR.is_shift());
    }

    #[test]
    fn category_is_move() {
        assert!(OpcodeCategory::MovRR.is_move());
        assert!(OpcodeCategory::MovRI.is_move());
        assert!(!OpcodeCategory::AddRR.is_move());
    }

    // -- AArch64 categorize tests --

    #[test]
    fn aarch64_arithmetic_categories() {
        assert_eq!(AArch64Opcode::AddRR.categorize(), OpcodeCategory::AddRR);
        assert_eq!(AArch64Opcode::AddRI.categorize(), OpcodeCategory::AddRI);
        assert_eq!(
            AArch64Opcode::AddRIShift12.categorize(),
            OpcodeCategory::AddRI
        );
        assert_eq!(AArch64Opcode::SubRR.categorize(), OpcodeCategory::SubRR);
        assert_eq!(AArch64Opcode::SubRI.categorize(), OpcodeCategory::SubRI);
        assert_eq!(AArch64Opcode::MulRR.categorize(), OpcodeCategory::MulRR);
        assert_eq!(AArch64Opcode::NeonAddV.categorize(), OpcodeCategory::AddRR);
        assert_eq!(AArch64Opcode::NeonSubV.categorize(), OpcodeCategory::SubRR);
        assert_eq!(AArch64Opcode::NeonMulV.categorize(), OpcodeCategory::MulRR);
        assert_eq!(AArch64Opcode::Neg.categorize(), OpcodeCategory::Neg);
    }

    #[test]
    fn aarch64_logical_categories() {
        assert_eq!(AArch64Opcode::AndRR.categorize(), OpcodeCategory::AndRR);
        assert_eq!(AArch64Opcode::AndRI.categorize(), OpcodeCategory::AndRI);
        assert_eq!(AArch64Opcode::OrrRR.categorize(), OpcodeCategory::OrRR);
        assert_eq!(AArch64Opcode::OrrRI.categorize(), OpcodeCategory::OrRI);
        assert_eq!(AArch64Opcode::EorRR.categorize(), OpcodeCategory::XorRR);
        assert_eq!(AArch64Opcode::EorRI.categorize(), OpcodeCategory::XorRI);
    }

    #[test]
    fn aarch64_shift_categories() {
        assert_eq!(AArch64Opcode::LslRR.categorize(), OpcodeCategory::ShlRR);
        assert_eq!(AArch64Opcode::LslRI.categorize(), OpcodeCategory::ShlRI);
        assert_eq!(AArch64Opcode::LsrRR.categorize(), OpcodeCategory::ShrRR);
        assert_eq!(AArch64Opcode::LsrRI.categorize(), OpcodeCategory::ShrRI);
        assert_eq!(AArch64Opcode::AsrRR.categorize(), OpcodeCategory::SarRR);
        assert_eq!(AArch64Opcode::AsrRI.categorize(), OpcodeCategory::SarRI);
    }

    #[test]
    fn aarch64_move_categories() {
        assert_eq!(AArch64Opcode::MovR.categorize(), OpcodeCategory::MovRR);
        assert_eq!(AArch64Opcode::Copy.categorize(), OpcodeCategory::MovRR);
        assert_eq!(AArch64Opcode::MOVWrr.categorize(), OpcodeCategory::MovRR);
        assert_eq!(AArch64Opcode::MovI.categorize(), OpcodeCategory::MovRI);
        assert_eq!(AArch64Opcode::Movz.categorize(), OpcodeCategory::MovRI);
        assert_eq!(AArch64Opcode::Movn.categorize(), OpcodeCategory::MovRI);
    }

    #[test]
    fn aarch64_compare_categories() {
        assert_eq!(AArch64Opcode::CmpRR.categorize(), OpcodeCategory::CmpRR);
        assert_eq!(AArch64Opcode::CMPWrr.categorize(), OpcodeCategory::CmpRR);
        assert_eq!(AArch64Opcode::CmpRI.categorize(), OpcodeCategory::CmpRI);
        assert_eq!(AArch64Opcode::CMPXri.categorize(), OpcodeCategory::CmpRI);
    }

    #[test]
    fn aarch64_control_flow_categories() {
        assert_eq!(AArch64Opcode::B.categorize(), OpcodeCategory::Branch);
        assert_eq!(
            AArch64Opcode::BCond.categorize(),
            OpcodeCategory::CondBranch
        );
        assert_eq!(AArch64Opcode::Cbz.categorize(), OpcodeCategory::CondBranch);
        assert_eq!(AArch64Opcode::Bl.categorize(), OpcodeCategory::Call);
        assert_eq!(AArch64Opcode::BL.categorize(), OpcodeCategory::Call);
        assert_eq!(AArch64Opcode::Ret.categorize(), OpcodeCategory::Ret);
    }

    #[test]
    fn aarch64_memory_categories() {
        assert_eq!(AArch64Opcode::LdrRI.categorize(), OpcodeCategory::Load);
        assert_eq!(
            AArch64Opcode::LdrPreIndex.categorize(),
            OpcodeCategory::Load
        );
        assert_eq!(
            AArch64Opcode::LdrPostIndex.categorize(),
            OpcodeCategory::Load
        );
        assert_eq!(AArch64Opcode::LdpRI.categorize(), OpcodeCategory::Load);
        assert_eq!(AArch64Opcode::StrRI.categorize(), OpcodeCategory::Store);
        assert_eq!(
            AArch64Opcode::StrPreIndex.categorize(),
            OpcodeCategory::Store
        );
        assert_eq!(
            AArch64Opcode::StrPostIndex.categorize(),
            OpcodeCategory::Store
        );
        assert_eq!(AArch64Opcode::StpRI.categorize(), OpcodeCategory::Store);
    }

    #[test]
    fn aarch64_pseudo_categories() {
        assert_eq!(AArch64Opcode::Phi.categorize(), OpcodeCategory::Phi);
        assert_eq!(AArch64Opcode::Nop.categorize(), OpcodeCategory::Nop);
    }

    #[test]
    fn aarch64_other_categories() {
        // Target-specific opcodes that don't have generic categories
        assert_eq!(AArch64Opcode::Csel.categorize(), OpcodeCategory::Other);
        assert_eq!(AArch64Opcode::CSet.categorize(), OpcodeCategory::Other);
        assert_eq!(AArch64Opcode::Rbit.categorize(), OpcodeCategory::Other);
        assert_eq!(AArch64Opcode::FaddRR.categorize(), OpcodeCategory::Other);
        assert_eq!(AArch64Opcode::Movk.categorize(), OpcodeCategory::Other);
        assert_eq!(AArch64Opcode::Adrp.categorize(), OpcodeCategory::Other);
    }

    // -- X86 categorize tests --

    #[test]
    fn x86_arithmetic_categories() {
        assert_eq!(X86Opcode::AddRR.categorize(), OpcodeCategory::AddRR);
        assert_eq!(X86Opcode::AddRI.categorize(), OpcodeCategory::AddRI);
        assert_eq!(X86Opcode::SubRR.categorize(), OpcodeCategory::SubRR);
        assert_eq!(X86Opcode::SubRI.categorize(), OpcodeCategory::SubRI);
        assert_eq!(X86Opcode::Paddb.categorize(), OpcodeCategory::AddRR);
        assert_eq!(X86Opcode::Paddw.categorize(), OpcodeCategory::AddRR);
        assert_eq!(X86Opcode::Paddd.categorize(), OpcodeCategory::AddRR);
        assert_eq!(X86Opcode::Psubb.categorize(), OpcodeCategory::SubRR);
        assert_eq!(X86Opcode::Psubw.categorize(), OpcodeCategory::SubRR);
        assert_eq!(X86Opcode::Psubd.categorize(), OpcodeCategory::SubRR);
        assert_eq!(X86Opcode::Paddq.categorize(), OpcodeCategory::AddRR);
        assert_eq!(X86Opcode::Psubq.categorize(), OpcodeCategory::SubRR);
        assert_eq!(X86Opcode::Pmullw.categorize(), OpcodeCategory::MulRR);
        assert_eq!(X86Opcode::ImulRR.categorize(), OpcodeCategory::MulRR);
        assert_eq!(X86Opcode::Mul.categorize(), OpcodeCategory::Other);
        assert_eq!(X86Opcode::Neg.categorize(), OpcodeCategory::Neg);
    }

    #[test]
    fn x86_logical_categories() {
        assert_eq!(X86Opcode::AndRR.categorize(), OpcodeCategory::AndRR);
        assert_eq!(X86Opcode::AndRI.categorize(), OpcodeCategory::AndRI);
        assert_eq!(X86Opcode::OrRR.categorize(), OpcodeCategory::OrRR);
        assert_eq!(X86Opcode::OrRI.categorize(), OpcodeCategory::OrRI);
        assert_eq!(X86Opcode::XorRR.categorize(), OpcodeCategory::XorRR);
        assert_eq!(X86Opcode::XorRI.categorize(), OpcodeCategory::XorRI);
        assert_eq!(X86Opcode::Pand.categorize(), OpcodeCategory::AndRR);
        assert_eq!(X86Opcode::Pandn.categorize(), OpcodeCategory::Other);
        assert_eq!(X86Opcode::Por.categorize(), OpcodeCategory::OrRR);
        assert_eq!(X86Opcode::Pxor.categorize(), OpcodeCategory::XorRR);
    }

    #[test]
    fn x86_shift_categories() {
        assert_eq!(X86Opcode::ShlRR.categorize(), OpcodeCategory::ShlRR);
        assert_eq!(X86Opcode::ShlRI.categorize(), OpcodeCategory::ShlRI);
        assert_eq!(X86Opcode::ShrRR.categorize(), OpcodeCategory::ShrRR);
        assert_eq!(X86Opcode::ShrRI.categorize(), OpcodeCategory::ShrRI);
        assert_eq!(X86Opcode::SarRR.categorize(), OpcodeCategory::SarRR);
        assert_eq!(X86Opcode::SarRI.categorize(), OpcodeCategory::SarRI);
    }

    #[test]
    fn x86_move_categories() {
        assert_eq!(X86Opcode::MovRR.categorize(), OpcodeCategory::MovRR);
        assert_eq!(X86Opcode::MovRR32.categorize(), OpcodeCategory::MovRR);
        assert_eq!(X86Opcode::MovsdRR.categorize(), OpcodeCategory::MovRR);
        assert_eq!(X86Opcode::MovssRR.categorize(), OpcodeCategory::MovRR);
        assert_eq!(X86Opcode::MovdqaRR.categorize(), OpcodeCategory::MovRR);
        assert_eq!(X86Opcode::MovRI.categorize(), OpcodeCategory::MovRI);
    }

    #[test]
    fn x86_compare_categories() {
        assert_eq!(X86Opcode::CmpRR.categorize(), OpcodeCategory::CmpRR);
        assert_eq!(X86Opcode::CmpRI.categorize(), OpcodeCategory::CmpRI);
        assert_eq!(X86Opcode::CmpRI8.categorize(), OpcodeCategory::CmpRI);
    }

    #[test]
    fn x86_control_flow_categories() {
        assert_eq!(X86Opcode::Jmp.categorize(), OpcodeCategory::Branch);
        assert_eq!(X86Opcode::Jcc.categorize(), OpcodeCategory::CondBranch);
        assert_eq!(X86Opcode::Call.categorize(), OpcodeCategory::Call);
        assert_eq!(X86Opcode::CallR.categorize(), OpcodeCategory::Call);
        assert_eq!(X86Opcode::Ret.categorize(), OpcodeCategory::Ret);
    }

    #[test]
    fn x86_memory_categories() {
        assert_eq!(X86Opcode::MovRM.categorize(), OpcodeCategory::Load);
        assert_eq!(X86Opcode::MovsdRM.categorize(), OpcodeCategory::Load);
        assert_eq!(X86Opcode::Pop.categorize(), OpcodeCategory::Load);
        assert_eq!(X86Opcode::MovMR.categorize(), OpcodeCategory::Store);
        assert_eq!(X86Opcode::MovsdMR.categorize(), OpcodeCategory::Store);
        assert_eq!(X86Opcode::Push.categorize(), OpcodeCategory::Store);
    }

    #[test]
    fn x86_pseudo_categories() {
        assert_eq!(X86Opcode::Phi.categorize(), OpcodeCategory::Phi);
        assert_eq!(X86Opcode::Nop.categorize(), OpcodeCategory::Nop);
    }

    #[test]
    fn x86_other_categories() {
        assert_eq!(X86Opcode::Cmovcc.categorize(), OpcodeCategory::Other);
        assert_eq!(X86Opcode::Cmovcc32.categorize(), OpcodeCategory::Other);
        assert_eq!(X86Opcode::Setcc.categorize(), OpcodeCategory::Other);
        assert_eq!(X86Opcode::Lea.categorize(), OpcodeCategory::Other);
        assert_eq!(X86Opcode::Bswap.categorize(), OpcodeCategory::Other);
        assert_eq!(X86Opcode::Xchg.categorize(), OpcodeCategory::Other);
        assert_eq!(X86Opcode::Pcmpeqb.categorize(), OpcodeCategory::Other);
        assert_eq!(X86Opcode::Pcmpeqw.categorize(), OpcodeCategory::Other);
        assert_eq!(X86Opcode::Pcmpgtb.categorize(), OpcodeCategory::Other);
        assert_eq!(X86Opcode::Pcmpgtw.categorize(), OpcodeCategory::Other);
        assert_eq!(X86Opcode::Pcmpeqd.categorize(), OpcodeCategory::Other);
        assert_eq!(X86Opcode::Pcmpgtd.categorize(), OpcodeCategory::Other);
        assert_eq!(X86Opcode::Pcmpeqq.categorize(), OpcodeCategory::Other);
        assert_eq!(X86Opcode::Pcmpgtq.categorize(), OpcodeCategory::Other);
        assert_eq!(X86Opcode::Pshufd.categorize(), OpcodeCategory::Other);
        assert_eq!(X86Opcode::Pmovmskb.categorize(), OpcodeCategory::Other);
        assert_eq!(
            X86Opcode::V4I32MaskExtract.categorize(),
            OpcodeCategory::Other
        );
        assert_eq!(
            X86Opcode::V16I8MaskExtract.categorize(),
            OpcodeCategory::Other
        );
        assert_eq!(
            X86Opcode::V8I16MaskExtract.categorize(),
            OpcodeCategory::Other
        );
        assert_eq!(
            X86Opcode::V2I64MaskExtract.categorize(),
            OpcodeCategory::Other
        );
    }

    #[test]
    fn x86_sse2_packed_categories() {
        assert_eq!(
            X86Sse2PackedOpcode::Pand.categorize(),
            OpcodeCategory::AndRR
        );
        assert_eq!(X86Sse2PackedOpcode::Por.categorize(), OpcodeCategory::OrRR);
        assert_eq!(
            X86Sse2PackedOpcode::Pxor.categorize(),
            OpcodeCategory::XorRR
        );
        assert_eq!(
            X86Sse2PackedOpcode::MovdqaRR.categorize(),
            OpcodeCategory::MovRR
        );
        assert_eq!(
            X86Sse2PackedOpcode::Paddb.categorize(),
            OpcodeCategory::AddRR
        );
        assert_eq!(
            X86Sse2PackedOpcode::Paddw.categorize(),
            OpcodeCategory::AddRR
        );
        assert_eq!(
            X86Sse2PackedOpcode::Paddd.categorize(),
            OpcodeCategory::AddRR
        );
        assert_eq!(
            X86Sse2PackedOpcode::Psubb.categorize(),
            OpcodeCategory::SubRR
        );
        assert_eq!(
            X86Sse2PackedOpcode::Psubw.categorize(),
            OpcodeCategory::SubRR
        );
        assert_eq!(
            X86Sse2PackedOpcode::Psubd.categorize(),
            OpcodeCategory::SubRR
        );
        assert_eq!(
            X86Sse2PackedOpcode::Paddq.categorize(),
            OpcodeCategory::AddRR
        );
        assert_eq!(
            X86Sse2PackedOpcode::Psubq.categorize(),
            OpcodeCategory::SubRR
        );
        assert_eq!(
            X86Sse2PackedOpcode::Pmullw.categorize(),
            OpcodeCategory::MulRR
        );
        assert_eq!(
            X86Sse2PackedOpcode::Pcmpeqb.categorize(),
            OpcodeCategory::Other
        );
        assert_eq!(
            X86Sse2PackedOpcode::Pcmpeqw.categorize(),
            OpcodeCategory::Other
        );
        assert_eq!(
            X86Sse2PackedOpcode::Pcmpgtb.categorize(),
            OpcodeCategory::Other
        );
        assert_eq!(
            X86Sse2PackedOpcode::Pcmpgtw.categorize(),
            OpcodeCategory::Other
        );
        assert_eq!(
            X86Sse2PackedOpcode::Pcmpeqd.categorize(),
            OpcodeCategory::Other
        );
        assert_eq!(
            X86Sse2PackedOpcode::Pcmpgtd.categorize(),
            OpcodeCategory::Other
        );
        assert_eq!(
            X86Sse2PackedOpcode::Pcmpeqq.categorize(),
            OpcodeCategory::Other
        );
        assert_eq!(
            X86Sse2PackedOpcode::Pcmpgtq.categorize(),
            OpcodeCategory::Other
        );
        assert_eq!(
            X86Sse2PackedOpcode::Punpckldq.categorize(),
            OpcodeCategory::Other
        );
        assert_eq!(
            X86Sse2PackedOpcode::Punpcklqdq.categorize(),
            OpcodeCategory::Other
        );
        assert_eq!(
            X86Sse2PackedOpcode::Pandn.categorize(),
            OpcodeCategory::Other
        );
        assert_eq!(
            X86Sse2PackedOpcode::Pshufd.categorize(),
            OpcodeCategory::Other
        );
        assert_eq!(
            X86Sse2PackedOpcode::Pmovmskb.categorize(),
            OpcodeCategory::Other
        );
    }

    #[test]
    fn x86_sse2_packed_opcode_queries() {
        assert!(X86Sse2PackedOpcode::Pand.is_commutative());
        assert!(!X86Sse2PackedOpcode::Pandn.is_commutative());
        assert!(X86Sse2PackedOpcode::Por.is_commutative());
        assert!(X86Sse2PackedOpcode::Pxor.is_commutative());
        assert!(X86Sse2PackedOpcode::Pcmpeqb.is_commutative());
        assert!(X86Sse2PackedOpcode::Pcmpeqw.is_commutative());
        assert!(X86Sse2PackedOpcode::Pcmpeqd.is_commutative());
        assert!(X86Sse2PackedOpcode::Paddb.is_commutative());
        assert!(X86Sse2PackedOpcode::Paddw.is_commutative());
        assert!(X86Sse2PackedOpcode::Paddd.is_commutative());
        assert!(X86Sse2PackedOpcode::Paddq.is_commutative());
        assert!(X86Sse2PackedOpcode::Pmullw.is_commutative());
        assert!(X86Sse2PackedOpcode::Pcmpeqq.is_commutative());
        assert!(!X86Sse2PackedOpcode::Psubb.is_commutative());
        assert!(!X86Sse2PackedOpcode::Psubw.is_commutative());
        assert!(!X86Sse2PackedOpcode::Psubd.is_commutative());
        assert!(!X86Sse2PackedOpcode::Psubq.is_commutative());
        assert!(!X86Sse2PackedOpcode::Pcmpgtb.is_commutative());
        assert!(!X86Sse2PackedOpcode::Pcmpgtw.is_commutative());
        assert!(!X86Sse2PackedOpcode::Pcmpgtd.is_commutative());
        assert!(!X86Sse2PackedOpcode::Pcmpgtq.is_commutative());
        assert!(!X86Sse2PackedOpcode::Punpckldq.is_commutative());
        assert!(!X86Sse2PackedOpcode::Punpcklqdq.is_commutative());
        assert!(!X86Sse2PackedOpcode::Pshufd.is_commutative());
        assert!(!X86Sse2PackedOpcode::Pmovmskb.is_commutative());
        assert!(!X86Sse2PackedOpcode::MovdqaRR.is_commutative());
        assert!(X86Sse2PackedOpcode::Pmovmskb.produces_value());
        assert_eq!(
            X86Sse2PackedOpcode::Pshufd.default_flags(),
            crate::inst::InstFlags::EMPTY
        );
    }

    // -- TargetInfo trait tests --

    #[test]
    fn aarch64_target_info() {
        assert_eq!(
            AArch64Target::categorize(AArch64Opcode::AddRR),
            OpcodeCategory::AddRR
        );
        assert!(AArch64Target::produces_value(AArch64Opcode::AddRR));
        assert!(!AArch64Target::produces_value(AArch64Opcode::CmpRR));
        assert!(AArch64Target::writes_flags(AArch64Opcode::CmpRR));
        assert!(!AArch64Target::writes_flags(AArch64Opcode::AddRR));
        assert!(AArch64Target::reads_flags(AArch64Opcode::CSet));
        assert!(!AArch64Target::reads_flags(AArch64Opcode::AddRR));
        assert!(AArch64Target::is_commutative(AArch64Opcode::AddRR));
        assert!(!AArch64Target::is_commutative(AArch64Opcode::SubRR));
        assert_eq!(AArch64Target::mov_rr(), AArch64Opcode::MovR);
        assert_eq!(AArch64Target::mov_ri(), AArch64Opcode::MovI);
        assert_eq!(AArch64Target::shl_ri(), AArch64Opcode::LslRI);
        assert_eq!(AArch64Target::sub_rr(), AArch64Opcode::SubRR);
        assert_eq!(AArch64Target::add_rr(), AArch64Opcode::AddRR);
        assert_eq!(AArch64Target::neg(), AArch64Opcode::Neg);
        assert_eq!(AArch64Target::sub_ri(), AArch64Opcode::SubRI);
        assert_eq!(AArch64Target::add_ri(), AArch64Opcode::AddRI);
    }

    #[test]
    fn x86_target_info_queries() {
        assert_eq!(
            X86_64Target::categorize(X86Opcode::AddRR),
            OpcodeCategory::AddRR
        );
        assert_eq!(
            X86_64Target::categorize(X86Opcode::Ptest),
            OpcodeCategory::Load
        );
        assert!(X86_64Target::produces_value(X86Opcode::AddRR));
        assert!(X86_64Target::produces_value(X86Opcode::Pcmpeqb));
        assert!(X86_64Target::produces_value(X86Opcode::Pcmpeqw));
        assert!(X86_64Target::produces_value(X86Opcode::Pcmpgtb));
        assert!(X86_64Target::produces_value(X86Opcode::Pcmpgtw));
        assert!(X86_64Target::produces_value(X86Opcode::Cvttsd2si));
        assert!(X86_64Target::produces_value(X86Opcode::Cvttss2si));
        assert!(!X86_64Target::produces_value(X86Opcode::CmpRR));
        assert!(!X86_64Target::produces_value(X86Opcode::Ptest));
        assert!(!X86_64Target::produces_value(X86Opcode::Mul));
        assert!(!X86_64Target::produces_value(X86Opcode::Ud2));
        assert!(!X86_64Target::produces_value(X86Opcode::Mfence));
        // x86: ADD sets flags, unlike AArch64 ADD
        assert!(X86_64Target::writes_flags(X86Opcode::AddRR));
        assert!(!X86_64Target::writes_flags(X86Opcode::Paddb));
        assert!(!X86_64Target::writes_flags(X86Opcode::Paddw));
        assert!(!X86_64Target::writes_flags(X86Opcode::Paddd));
        assert!(!X86_64Target::writes_flags(X86Opcode::Pcmpeqb));
        assert!(!X86_64Target::writes_flags(X86Opcode::Pcmpeqw));
        assert!(!X86_64Target::writes_flags(X86Opcode::Pcmpgtb));
        assert!(!X86_64Target::writes_flags(X86Opcode::Pcmpgtw));
        assert!(!X86_64Target::writes_flags(X86Opcode::Psubb));
        assert!(!X86_64Target::writes_flags(X86Opcode::Psubw));
        assert!(!X86_64Target::writes_flags(X86Opcode::Pmullw));
        assert!(!X86_64Target::writes_flags(X86Opcode::Paddq));
        assert!(!X86_64Target::writes_flags(X86Opcode::Pcmpeqq));
        assert!(!X86_64Target::writes_flags(X86Opcode::Pcmpgtq));
        assert!(X86_64Target::writes_flags(X86Opcode::CmpRR));
        assert!(X86_64Target::writes_flags(X86Opcode::Ptest));
        assert!(X86_64Target::writes_flags(X86Opcode::Mul));
        assert!(!X86_64Target::writes_flags(X86Opcode::Ud2));
        assert!(!X86_64Target::writes_flags(X86Opcode::MovRR));
        assert!(!X86_64Target::writes_flags(X86Opcode::Cvttsd2si));
        assert!(!X86_64Target::writes_flags(X86Opcode::Cvttss2si));
        assert!(X86_64Target::reads_flags(X86Opcode::Cmovcc));
        assert!(X86_64Target::reads_flags(X86Opcode::Cmovcc32));
        assert!(X86_64Target::reads_flags(X86Opcode::Setcc));
        assert!(X86_64Target::reads_flags(X86Opcode::Jcc));
        assert!(!X86_64Target::reads_flags(X86Opcode::AddRR));
        assert!(!X86_64Target::reads_flags(X86Opcode::Mul));
        assert!(!X86_64Target::reads_flags(X86Opcode::Ptest));
        assert!(!X86_64Target::reads_flags(X86Opcode::Ud2));
        assert!(!X86_64Target::reads_flags(X86Opcode::Cvttsd2si));
        assert!(!X86_64Target::reads_flags(X86Opcode::Cvttss2si));
        assert!(X86_64Target::is_commutative(X86Opcode::AddRR));
        assert!(!X86_64Target::is_commutative(X86Opcode::SubRR));
        assert!(X86_64Target::is_commutative(X86Opcode::Paddb));
        assert!(X86_64Target::is_commutative(X86Opcode::Paddw));
        assert!(X86_64Target::is_commutative(X86Opcode::Paddd));
        assert!(X86_64Target::is_commutative(X86Opcode::Paddq));
        assert!(X86_64Target::is_commutative(X86Opcode::Pmullw));
        assert!(X86_64Target::is_commutative(X86Opcode::Pcmpeqb));
        assert!(X86_64Target::is_commutative(X86Opcode::Pcmpeqw));
        assert!(X86_64Target::is_commutative(X86Opcode::Pcmpeqq));
        assert!(!X86_64Target::is_commutative(X86Opcode::Psubb));
        assert!(!X86_64Target::is_commutative(X86Opcode::Psubw));
        assert!(!X86_64Target::is_commutative(X86Opcode::Psubd));
        assert!(!X86_64Target::is_commutative(X86Opcode::Psubq));
        assert!(!X86_64Target::is_commutative(X86Opcode::Pcmpgtb));
        assert!(!X86_64Target::is_commutative(X86Opcode::Pcmpgtw));
        assert!(!X86_64Target::is_commutative(X86Opcode::Pcmpgtq));
        assert_eq!(X86_64Target::mov_rr(), X86Opcode::MovRR);
        assert_eq!(X86_64Target::mov_ri(), X86Opcode::MovRI);
        assert_eq!(X86_64Target::shl_ri(), X86Opcode::ShlRI);
        assert_eq!(X86_64Target::sub_rr(), X86Opcode::SubRR);
        assert_eq!(X86_64Target::add_rr(), X86Opcode::AddRR);
        assert_eq!(X86_64Target::neg(), X86Opcode::Neg);
        assert_eq!(X86_64Target::sub_ri(), X86Opcode::SubRI);
        assert_eq!(X86_64Target::add_ri(), X86Opcode::AddRI);
    }

    // -- Cross-target consistency tests --

    #[test]
    fn both_targets_agree_on_add_category() {
        assert_eq!(
            AArch64Target::categorize(AArch64Opcode::AddRR),
            X86_64Target::categorize(X86Opcode::AddRR),
        );
        assert_eq!(
            AArch64Target::categorize(AArch64Opcode::AddRI),
            X86_64Target::categorize(X86Opcode::AddRI),
        );
    }

    #[test]
    fn both_targets_agree_on_sub_category() {
        assert_eq!(
            AArch64Target::categorize(AArch64Opcode::SubRR),
            X86_64Target::categorize(X86Opcode::SubRR),
        );
    }

    #[test]
    fn both_targets_agree_on_move_category() {
        assert_eq!(
            AArch64Target::categorize(AArch64Opcode::MovR),
            X86_64Target::categorize(X86Opcode::MovRR),
        );
        assert_eq!(
            AArch64Target::categorize(AArch64Opcode::MovI),
            X86_64Target::categorize(X86Opcode::MovRI),
        );
    }

    #[test]
    fn both_targets_mov_rr_categorizes_as_mov_rr() {
        assert_eq!(
            AArch64Target::categorize(AArch64Target::mov_rr()),
            OpcodeCategory::MovRR,
        );
        assert_eq!(
            X86_64Target::categorize(X86_64Target::mov_rr()),
            OpcodeCategory::MovRR,
        );
    }

    #[test]
    fn both_targets_shl_ri_categorizes_as_shl_ri() {
        assert_eq!(
            AArch64Target::categorize(AArch64Target::shl_ri()),
            OpcodeCategory::ShlRI,
        );
        assert_eq!(
            X86_64Target::categorize(X86_64Target::shl_ri()),
            OpcodeCategory::ShlRI,
        );
    }

    #[test]
    fn both_targets_sub_rr_categorizes_as_sub_rr() {
        assert_eq!(
            AArch64Target::categorize(AArch64Target::sub_rr()),
            OpcodeCategory::SubRR,
        );
        assert_eq!(
            X86_64Target::categorize(X86_64Target::sub_rr()),
            OpcodeCategory::SubRR,
        );
    }

    #[test]
    fn both_targets_add_rr_categorizes_as_add_rr() {
        assert_eq!(
            AArch64Target::categorize(AArch64Target::add_rr()),
            OpcodeCategory::AddRR,
        );
        assert_eq!(
            X86_64Target::categorize(X86_64Target::add_rr()),
            OpcodeCategory::AddRR,
        );
    }

    #[test]
    fn both_targets_neg_categorizes_as_neg() {
        assert_eq!(
            AArch64Target::categorize(AArch64Target::neg()),
            OpcodeCategory::Neg,
        );
        assert_eq!(
            X86_64Target::categorize(X86_64Target::neg()),
            OpcodeCategory::Neg,
        );
    }

    #[test]
    fn both_targets_sub_ri_categorizes_as_sub_ri() {
        assert_eq!(
            AArch64Target::categorize(AArch64Target::sub_ri()),
            OpcodeCategory::SubRI,
        );
        assert_eq!(
            X86_64Target::categorize(X86_64Target::sub_ri()),
            OpcodeCategory::SubRI,
        );
    }

    #[test]
    fn both_targets_add_ri_categorizes_as_add_ri() {
        assert_eq!(
            AArch64Target::categorize(AArch64Target::add_ri()),
            OpcodeCategory::AddRI,
        );
        assert_eq!(
            X86_64Target::categorize(X86_64Target::add_ri()),
            OpcodeCategory::AddRI,
        );
    }
}
