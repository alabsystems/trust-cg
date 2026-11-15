// trust-cg-ir - Shared machine IR model
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Typed shapes for the opaque AArch64 LL/SC atomic pseudos.
//!
//! Baseline armv8.0 has no FEAT_LSE single-instruction atomics, so
//! `AtomicRmw` / `CmpXchg` on a profile without LSE select an opaque pseudo
//! (`LlscRmw{8,16,32,64}` / `LlscCmpSwap{8,16,32,64}`) that register
//! allocation treats as one instruction. 128-bit atomics have no LSE
//! single-instruction form in the admitted profiles and always use the pair
//! pseudos (`LlscLoad128`, `LlscStore128`, `LlscRmw128`, `LlscCmpSwap128`).
//! Only after allocation, spill materialization and frame lowering does
//! `trust_cg_codegen::llsc::expand_llsc_atomics` replace a pseudo with a
//! load-exclusive / ALU / store-exclusive / `CBNZ` retry loop, so no spill,
//! reload or other memory access can land inside the exclusive window.
//!
//! This module is the single source of truth for the pseudo operand layout
//! and the typed immediates it carries. Every decoder of an immediate is
//! checked: an out-of-range value is `None`, never a default.

use crate::inst::AArch64Opcode;

/// Memory access width of an LL/SC pseudo, in bits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LlscWidth {
    /// Byte access (`LDXRB` / `STXRB`).
    B8,
    /// Halfword access (`LDXRH` / `STXRH`).
    B16,
    /// Word access (`LDXR Wt` / `STXR Ws, Wt`).
    B32,
    /// Doubleword access (`LDXR Xt` / `STXR Ws, Xt`).
    B64,
    /// Quadword access through an X-register pair (`LDXP` / `STXP`).
    B128,
}

impl LlscWidth {
    /// The single-register widths, narrowest first.
    pub const SINGLE_REGISTER: [Self; 4] = [Self::B8, Self::B16, Self::B32, Self::B64];
    /// Every width, narrowest first.
    pub const ALL: [Self; 5] = [Self::B8, Self::B16, Self::B32, Self::B64, Self::B128];

    /// Access width in bits.
    pub const fn bits(self) -> u32 {
        match self {
            Self::B8 => 8,
            Self::B16 => 16,
            Self::B32 => 32,
            Self::B64 => 64,
            Self::B128 => 128,
        }
    }

    /// True for the byte and halfword forms, whose loaded value is
    /// zero-extended into a W register and whose operands may carry
    /// arbitrary bits above the access width.
    pub const fn is_sub_word(self) -> bool {
        matches!(self, Self::B8 | Self::B16)
    }

    /// True for the X-register-pair form.
    pub const fn is_pair(self) -> bool {
        matches!(self, Self::B128)
    }
}

/// The read-modify-write operation performed inside an `LlscRmw*` loop.
///
/// Carried as operand [`LLSC_RMW_OP_OPERAND`] (or [`LLSC_RMW128_OP_OPERAND`])
/// via [`Self::to_imm`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LlscRmwOp {
    /// `new = old + value` (wrapping at the access width).
    Add,
    /// `new = old - value` (wrapping at the access width).
    Sub,
    /// `new = old & value`.
    And,
    /// `new = old | value`.
    Or,
    /// `new = old ^ value`.
    Xor,
    /// `new = value`.
    Xchg,
    /// Signed maximum at the access width.
    Smax,
    /// Signed minimum at the access width.
    Smin,
    /// Unsigned maximum at the access width.
    Umax,
    /// Unsigned minimum at the access width.
    Umin,
}

impl LlscRmwOp {
    /// Every operation, in immediate order.
    pub const ALL: [Self; 10] = [
        Self::Add,
        Self::Sub,
        Self::And,
        Self::Or,
        Self::Xor,
        Self::Xchg,
        Self::Smax,
        Self::Smin,
        Self::Umax,
        Self::Umin,
    ];

    /// The immediate operand value for this operation.
    pub const fn to_imm(self) -> i64 {
        match self {
            Self::Add => 0,
            Self::Sub => 1,
            Self::And => 2,
            Self::Or => 3,
            Self::Xor => 4,
            Self::Xchg => 5,
            Self::Smax => 6,
            Self::Smin => 7,
            Self::Umax => 8,
            Self::Umin => 9,
        }
    }

    /// Checked decoder: `None` for any value [`Self::to_imm`] never produces.
    pub const fn from_imm(imm: i64) -> Option<Self> {
        Some(match imm {
            0 => Self::Add,
            1 => Self::Sub,
            2 => Self::And,
            3 => Self::Or,
            4 => Self::Xor,
            5 => Self::Xchg,
            6 => Self::Smax,
            7 => Self::Smin,
            8 => Self::Umax,
            9 => Self::Umin,
            _ => return None,
        })
    }

    /// True for the min/max family, whose expansion compares (and therefore
    /// clobbers NZCV) and must extend sub-word operands before comparing.
    pub const fn is_min_max(self) -> bool {
        matches!(self, Self::Smax | Self::Smin | Self::Umax | Self::Umin)
    }
}

/// Acquire/release selection of an LL/SC loop.
///
/// `acquire` selects the load-acquire exclusive (`LDAXR*`/`LDAXP`) and
/// `release` the store-release exclusive (`STLXR*`/`STLXP`). Both set is the
/// sequentially consistent mapping used by LLVM and GCC for armv8.0
/// (`LDAXR`/`STLXR` are RCsc).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LlscOrdering {
    /// Use a load-acquire exclusive.
    pub acquire: bool,
    /// Use a store-release exclusive.
    pub release: bool,
}

impl LlscOrdering {
    /// Relaxed: `LDXR` / `STXR`.
    pub const RELAXED: Self = Self {
        acquire: false,
        release: false,
    };
    /// Acquire: `LDAXR` / `STXR`.
    pub const ACQUIRE: Self = Self {
        acquire: true,
        release: false,
    };
    /// Release: `LDXR` / `STLXR`.
    pub const RELEASE: Self = Self {
        acquire: false,
        release: true,
    };
    /// Acquire-release and sequentially consistent: `LDAXR` / `STLXR`.
    pub const ACQ_REL: Self = Self {
        acquire: true,
        release: true,
    };

    /// The immediate operand value: bit 0 = acquire, bit 1 = release.
    pub const fn to_imm(self) -> i64 {
        (self.acquire as i64) | ((self.release as i64) << 1)
    }

    /// Checked decoder: `None` outside `0..=3`.
    pub const fn from_imm(imm: i64) -> Option<Self> {
        match imm {
            0..=3 => Some(Self {
                acquire: imm & 1 != 0,
                release: imm & 2 != 0,
            }),
            _ => None,
        }
    }
}

/// Which pseudo family an opcode belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LlscPseudo {
    /// `LlscRmw{8,16,32,64,128}`.
    Rmw(LlscWidth),
    /// `LlscCmpSwap{8,16,32,64,128}`.
    CmpSwap(LlscWidth),
    /// `LlscLoad128`: a 128-bit atomic load (write-back loop).
    Load128,
    /// `LlscStore128`: a 128-bit atomic store.
    Store128,
}

impl LlscPseudo {
    /// Every pseudo, in opcode order.
    pub const ALL: [Self; 12] = [
        Self::Rmw(LlscWidth::B8),
        Self::Rmw(LlscWidth::B16),
        Self::Rmw(LlscWidth::B32),
        Self::Rmw(LlscWidth::B64),
        Self::CmpSwap(LlscWidth::B8),
        Self::CmpSwap(LlscWidth::B16),
        Self::CmpSwap(LlscWidth::B32),
        Self::CmpSwap(LlscWidth::B64),
        Self::Load128,
        Self::Store128,
        Self::Rmw(LlscWidth::B128),
        Self::CmpSwap(LlscWidth::B128),
    ];

    /// Classify an opcode; `None` for every non-pseudo opcode.
    pub const fn of(opcode: AArch64Opcode) -> Option<Self> {
        Some(match opcode {
            AArch64Opcode::LlscRmw8 => Self::Rmw(LlscWidth::B8),
            AArch64Opcode::LlscRmw16 => Self::Rmw(LlscWidth::B16),
            AArch64Opcode::LlscRmw32 => Self::Rmw(LlscWidth::B32),
            AArch64Opcode::LlscRmw64 => Self::Rmw(LlscWidth::B64),
            AArch64Opcode::LlscRmw128 => Self::Rmw(LlscWidth::B128),
            AArch64Opcode::LlscCmpSwap8 => Self::CmpSwap(LlscWidth::B8),
            AArch64Opcode::LlscCmpSwap16 => Self::CmpSwap(LlscWidth::B16),
            AArch64Opcode::LlscCmpSwap32 => Self::CmpSwap(LlscWidth::B32),
            AArch64Opcode::LlscCmpSwap64 => Self::CmpSwap(LlscWidth::B64),
            AArch64Opcode::LlscCmpSwap128 => Self::CmpSwap(LlscWidth::B128),
            AArch64Opcode::LlscLoad128 => Self::Load128,
            AArch64Opcode::LlscStore128 => Self::Store128,
            _ => return None,
        })
    }

    /// The pseudo opcode for this family and width.
    pub const fn opcode(self) -> AArch64Opcode {
        match self {
            Self::Rmw(LlscWidth::B8) => AArch64Opcode::LlscRmw8,
            Self::Rmw(LlscWidth::B16) => AArch64Opcode::LlscRmw16,
            Self::Rmw(LlscWidth::B32) => AArch64Opcode::LlscRmw32,
            Self::Rmw(LlscWidth::B64) => AArch64Opcode::LlscRmw64,
            Self::Rmw(LlscWidth::B128) => AArch64Opcode::LlscRmw128,
            Self::CmpSwap(LlscWidth::B8) => AArch64Opcode::LlscCmpSwap8,
            Self::CmpSwap(LlscWidth::B16) => AArch64Opcode::LlscCmpSwap16,
            Self::CmpSwap(LlscWidth::B32) => AArch64Opcode::LlscCmpSwap32,
            Self::CmpSwap(LlscWidth::B64) => AArch64Opcode::LlscCmpSwap64,
            Self::CmpSwap(LlscWidth::B128) => AArch64Opcode::LlscCmpSwap128,
            Self::Load128 => AArch64Opcode::LlscLoad128,
            Self::Store128 => AArch64Opcode::LlscStore128,
        }
    }

    /// Access width.
    pub const fn width(self) -> LlscWidth {
        match self {
            Self::Rmw(width) | Self::CmpSwap(width) => width,
            Self::Load128 | Self::Store128 => LlscWidth::B128,
        }
    }

    /// Exact operand count of the pseudo.
    pub const fn operand_count(self) -> usize {
        match self {
            Self::Rmw(LlscWidth::B128) => LLSC_RMW128_OPERAND_COUNT,
            Self::Rmw(_) => LLSC_RMW_OPERAND_COUNT,
            Self::CmpSwap(LlscWidth::B128) => LLSC_CAS128_OPERAND_COUNT,
            Self::CmpSwap(_) => LLSC_CMP_SWAP_OPERAND_COUNT,
            Self::Load128 => LLSC_LOAD128_OPERAND_COUNT,
            Self::Store128 => LLSC_STORE128_OPERAND_COUNT,
        }
    }

    /// Number of leading operands that are register definitions. Every other
    /// register operand is a use. All definitions are written only after all
    /// uses have been read for the last time within the loop, so allocation
    /// must give each definition a register distinct from every use.
    pub const fn def_count(self) -> usize {
        match self {
            Self::Rmw(LlscWidth::B128) => 5,
            Self::Rmw(_) => 3,
            Self::CmpSwap(LlscWidth::B128) => 3,
            Self::CmpSwap(_) => 2,
            Self::Load128 | Self::Store128 => 3,
        }
    }
}

/// `LlscRmw*` operand: loaded old value (def; the pseudo's result).
pub const LLSC_RMW_OLD_OPERAND: usize = 0;
/// `LlscRmw*` operand: computed new value scratch (def).
pub const LLSC_RMW_NEW_OPERAND: usize = 1;
/// `LlscRmw*` operand: store-exclusive status scratch (W def).
pub const LLSC_RMW_STATUS_OPERAND: usize = 2;
/// `LlscRmw*` operand: the update value (use).
pub const LLSC_RMW_VALUE_OPERAND: usize = 3;
/// `LlscRmw*` operand: the 64-bit address (use).
pub const LLSC_RMW_ADDR_OPERAND: usize = 4;
/// `LlscRmw*` operand: `Imm(LlscRmwOp::to_imm)`.
pub const LLSC_RMW_OP_OPERAND: usize = 5;
/// `LlscRmw*` operand: `Imm(LlscOrdering::to_imm)`.
pub const LLSC_RMW_ORDERING_OPERAND: usize = 6;
/// Exact `LlscRmw{8,16,32,64}` operand count.
pub const LLSC_RMW_OPERAND_COUNT: usize = 7;

/// `LlscCmpSwap*` operand: loaded old value (def; the pseudo's result).
pub const LLSC_CAS_OLD_OPERAND: usize = 0;
/// `LlscCmpSwap*` operand: store-exclusive status scratch (W def). Sub-word
/// forms also use it to hold the zero-extended expected value before the
/// store-exclusive overwrites it.
pub const LLSC_CAS_STATUS_OPERAND: usize = 1;
/// `LlscCmpSwap*` operand: expected value (use).
pub const LLSC_CAS_EXPECTED_OPERAND: usize = 2;
/// `LlscCmpSwap*` operand: desired value (use).
pub const LLSC_CAS_DESIRED_OPERAND: usize = 3;
/// `LlscCmpSwap*` operand: the 64-bit address (use).
pub const LLSC_CAS_ADDR_OPERAND: usize = 4;
/// `LlscCmpSwap*` operand: `Imm(LlscOrdering::to_imm)`.
pub const LLSC_CAS_ORDERING_OPERAND: usize = 5;
/// Exact `LlscCmpSwap{8,16,32,64}` operand count.
pub const LLSC_CMP_SWAP_OPERAND_COUNT: usize = 6;

/// `LlscLoad128` operand: loaded low doubleword (def; result low half).
pub const LLSC_LOAD128_LO_OPERAND: usize = 0;
/// `LlscLoad128` operand: loaded high doubleword (def; result high half).
pub const LLSC_LOAD128_HI_OPERAND: usize = 1;
/// `LlscLoad128` operand: store-exclusive status scratch (W def).
pub const LLSC_LOAD128_STATUS_OPERAND: usize = 2;
/// `LlscLoad128` operand: the 64-bit address (use).
pub const LLSC_LOAD128_ADDR_OPERAND: usize = 3;
/// `LlscLoad128` operand: `Imm(LlscOrdering::to_imm)`.
pub const LLSC_LOAD128_ORDERING_OPERAND: usize = 4;
/// Exact `LlscLoad128` operand count.
pub const LLSC_LOAD128_OPERAND_COUNT: usize = 5;

/// `LlscStore128` operand: scratch for the discarded loaded low half (def).
pub const LLSC_STORE128_SCRATCH_LO_OPERAND: usize = 0;
/// `LlscStore128` operand: scratch for the discarded loaded high half (def).
pub const LLSC_STORE128_SCRATCH_HI_OPERAND: usize = 1;
/// `LlscStore128` operand: store-exclusive status scratch (W def).
pub const LLSC_STORE128_STATUS_OPERAND: usize = 2;
/// `LlscStore128` operand: stored low doubleword (use).
pub const LLSC_STORE128_VALUE_LO_OPERAND: usize = 3;
/// `LlscStore128` operand: stored high doubleword (use).
pub const LLSC_STORE128_VALUE_HI_OPERAND: usize = 4;
/// `LlscStore128` operand: the 64-bit address (use).
pub const LLSC_STORE128_ADDR_OPERAND: usize = 5;
/// `LlscStore128` operand: `Imm(LlscOrdering::to_imm)`.
pub const LLSC_STORE128_ORDERING_OPERAND: usize = 6;
/// Exact `LlscStore128` operand count.
pub const LLSC_STORE128_OPERAND_COUNT: usize = 7;

/// `LlscRmw128` operand: loaded old low doubleword (def; result low half).
pub const LLSC_RMW128_OLD_LO_OPERAND: usize = 0;
/// `LlscRmw128` operand: loaded old high doubleword (def; result high half).
pub const LLSC_RMW128_OLD_HI_OPERAND: usize = 1;
/// `LlscRmw128` operand: computed new low doubleword scratch (def).
pub const LLSC_RMW128_NEW_LO_OPERAND: usize = 2;
/// `LlscRmw128` operand: computed new high doubleword scratch (def).
pub const LLSC_RMW128_NEW_HI_OPERAND: usize = 3;
/// `LlscRmw128` operand: store-exclusive status scratch (W def).
pub const LLSC_RMW128_STATUS_OPERAND: usize = 4;
/// `LlscRmw128` operand: update value low doubleword (use).
pub const LLSC_RMW128_VALUE_LO_OPERAND: usize = 5;
/// `LlscRmw128` operand: update value high doubleword (use).
pub const LLSC_RMW128_VALUE_HI_OPERAND: usize = 6;
/// `LlscRmw128` operand: the 64-bit address (use).
pub const LLSC_RMW128_ADDR_OPERAND: usize = 7;
/// `LlscRmw128` operand: `Imm(LlscRmwOp::to_imm)`.
pub const LLSC_RMW128_OP_OPERAND: usize = 8;
/// `LlscRmw128` operand: `Imm(LlscOrdering::to_imm)`.
pub const LLSC_RMW128_ORDERING_OPERAND: usize = 9;
/// Exact `LlscRmw128` operand count.
pub const LLSC_RMW128_OPERAND_COUNT: usize = 10;

/// `LlscCmpSwap128` operand: loaded old low doubleword (def).
pub const LLSC_CAS128_OLD_LO_OPERAND: usize = 0;
/// `LlscCmpSwap128` operand: loaded old high doubleword (def).
pub const LLSC_CAS128_OLD_HI_OPERAND: usize = 1;
/// `LlscCmpSwap128` operand: store-exclusive status scratch (W def).
pub const LLSC_CAS128_STATUS_OPERAND: usize = 2;
/// `LlscCmpSwap128` operand: expected low doubleword (use).
pub const LLSC_CAS128_EXPECTED_LO_OPERAND: usize = 3;
/// `LlscCmpSwap128` operand: expected high doubleword (use).
pub const LLSC_CAS128_EXPECTED_HI_OPERAND: usize = 4;
/// `LlscCmpSwap128` operand: desired low doubleword (use).
pub const LLSC_CAS128_DESIRED_LO_OPERAND: usize = 5;
/// `LlscCmpSwap128` operand: desired high doubleword (use).
pub const LLSC_CAS128_DESIRED_HI_OPERAND: usize = 6;
/// `LlscCmpSwap128` operand: the 64-bit address (use).
pub const LLSC_CAS128_ADDR_OPERAND: usize = 7;
/// `LlscCmpSwap128` operand: `Imm(LlscOrdering::to_imm)`.
pub const LLSC_CAS128_ORDERING_OPERAND: usize = 8;
/// Exact `LlscCmpSwap128` operand count.
pub const LLSC_CAS128_OPERAND_COUNT: usize = 9;

/// The load-exclusive opcode for a width and acquire choice.
pub const fn exclusive_load_opcode(width: LlscWidth, acquire: bool) -> AArch64Opcode {
    match (width, acquire) {
        (LlscWidth::B8, false) => AArch64Opcode::Ldxrb,
        (LlscWidth::B8, true) => AArch64Opcode::Ldaxrb,
        (LlscWidth::B16, false) => AArch64Opcode::Ldxrh,
        (LlscWidth::B16, true) => AArch64Opcode::Ldaxrh,
        (LlscWidth::B32 | LlscWidth::B64, false) => AArch64Opcode::Ldxr,
        (LlscWidth::B32 | LlscWidth::B64, true) => AArch64Opcode::Ldaxr,
        (LlscWidth::B128, false) => AArch64Opcode::Ldxp,
        (LlscWidth::B128, true) => AArch64Opcode::Ldaxp,
    }
}

/// The store-exclusive opcode for a width and release choice.
pub const fn exclusive_store_opcode(width: LlscWidth, release: bool) -> AArch64Opcode {
    match (width, release) {
        (LlscWidth::B8, false) => AArch64Opcode::Stxrb,
        (LlscWidth::B8, true) => AArch64Opcode::Stlxrb,
        (LlscWidth::B16, false) => AArch64Opcode::Stxrh,
        (LlscWidth::B16, true) => AArch64Opcode::Stlxrh,
        (LlscWidth::B32 | LlscWidth::B64, false) => AArch64Opcode::Stxr,
        (LlscWidth::B32 | LlscWidth::B64, true) => AArch64Opcode::Stlxr,
        (LlscWidth::B128, false) => AArch64Opcode::Stxp,
        (LlscWidth::B128, true) => AArch64Opcode::Stlxp,
    }
}

/// True for every load-exclusive opcode (single register or pair).
pub const fn is_exclusive_load(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::Ldxr
            | AArch64Opcode::Ldxrb
            | AArch64Opcode::Ldxrh
            | AArch64Opcode::Ldaxr
            | AArch64Opcode::Ldaxrb
            | AArch64Opcode::Ldaxrh
            | AArch64Opcode::Ldxp
            | AArch64Opcode::Ldaxp
    )
}

/// True for every store-exclusive opcode (single register or pair).
/// Operand 0 is the W status definition; the data and address operands are
/// uses.
pub const fn is_exclusive_store(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::Stxr
            | AArch64Opcode::Stxrb
            | AArch64Opcode::Stxrh
            | AArch64Opcode::Stlxr
            | AArch64Opcode::Stlxrb
            | AArch64Opcode::Stlxrh
            | AArch64Opcode::Stxp
            | AArch64Opcode::Stlxp
    )
}

/// True for the X-register-pair exclusives. A pair load defines operands 0
/// and 1; a pair store's data operands are 1 and 2 and its base is 3.
pub const fn is_exclusive_pair(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::Ldxp | AArch64Opcode::Ldaxp | AArch64Opcode::Stxp | AArch64Opcode::Stlxp
    )
}

/// Access width of an exclusive load/store opcode whose width is fixed by
/// the opcode (byte/halfword and pair forms). Word forms return `None`:
/// their width follows the data register class.
pub const fn exclusive_fixed_width(opcode: AArch64Opcode) -> Option<LlscWidth> {
    match opcode {
        AArch64Opcode::Ldxrb
        | AArch64Opcode::Ldaxrb
        | AArch64Opcode::Stxrb
        | AArch64Opcode::Stlxrb => Some(LlscWidth::B8),
        AArch64Opcode::Ldxrh
        | AArch64Opcode::Ldaxrh
        | AArch64Opcode::Stxrh
        | AArch64Opcode::Stlxrh => Some(LlscWidth::B16),
        AArch64Opcode::Ldxp | AArch64Opcode::Ldaxp | AArch64Opcode::Stxp | AArch64Opcode::Stlxp => {
            Some(LlscWidth::B128)
        }
        _ => None,
    }
}

/// True for the acquire (`LDAX*`) or release (`STLX*`) exclusive forms.
pub const fn is_ordered_exclusive(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::Ldaxr
            | AArch64Opcode::Ldaxrb
            | AArch64Opcode::Ldaxrh
            | AArch64Opcode::Ldaxp
            | AArch64Opcode::Stlxr
            | AArch64Opcode::Stlxrb
            | AArch64Opcode::Stlxrh
            | AArch64Opcode::Stlxp
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rmw_op_immediates_roundtrip_and_reject_unknown_values() {
        for op in LlscRmwOp::ALL {
            assert_eq!(LlscRmwOp::from_imm(op.to_imm()), Some(op));
        }
        for bad in [-1, 10, 11, i64::MAX, i64::MIN] {
            assert_eq!(LlscRmwOp::from_imm(bad), None, "{bad}");
        }
    }

    #[test]
    fn ordering_immediates_roundtrip_and_reject_unknown_values() {
        for ordering in [
            LlscOrdering::RELAXED,
            LlscOrdering::ACQUIRE,
            LlscOrdering::RELEASE,
            LlscOrdering::ACQ_REL,
        ] {
            assert_eq!(LlscOrdering::from_imm(ordering.to_imm()), Some(ordering));
        }
        for bad in [-1, 4, 5, i64::MAX] {
            assert_eq!(LlscOrdering::from_imm(bad), None, "{bad}");
        }
    }

    #[test]
    fn pseudo_classification_is_a_bijection_over_every_family() {
        let mut seen = std::collections::BTreeSet::new();
        for pseudo in LlscPseudo::ALL {
            let opcode = pseudo.opcode();
            assert_eq!(LlscPseudo::of(opcode), Some(pseudo));
            assert!(seen.insert(opcode as u16));
            assert!(pseudo.def_count() < pseudo.operand_count());
        }
        assert_eq!(seen.len(), 12);
        assert_eq!(LlscPseudo::of(AArch64Opcode::Casal), None);
        assert_eq!(LlscPseudo::of(AArch64Opcode::Ldaxr), None);
        assert_eq!(LlscPseudo::of(AArch64Opcode::Ldxp), None);
        assert_eq!(LlscPseudo::Load128.width(), LlscWidth::B128);
    }

    #[test]
    fn exclusive_opcode_selection_is_width_and_ordering_exact() {
        for width in LlscWidth::ALL {
            for ordered in [false, true] {
                let load = exclusive_load_opcode(width, ordered);
                assert!(is_exclusive_load(load));
                assert!(!is_exclusive_store(load));
                assert_eq!(is_ordered_exclusive(load), ordered);
                assert_eq!(is_exclusive_pair(load), width.is_pair());
                assert_eq!(
                    exclusive_fixed_width(load),
                    (width.is_sub_word() || width.is_pair()).then_some(width)
                );
                let store = exclusive_store_opcode(width, ordered);
                assert!(is_exclusive_store(store));
                assert!(!is_exclusive_load(store));
                assert_eq!(is_ordered_exclusive(store), ordered);
                assert_eq!(is_exclusive_pair(store), width.is_pair());
                assert_eq!(
                    exclusive_fixed_width(store),
                    (width.is_sub_word() || width.is_pair()).then_some(width)
                );
            }
        }
        assert_eq!(
            exclusive_load_opcode(LlscWidth::B32, true),
            AArch64Opcode::Ldaxr
        );
        assert_eq!(
            exclusive_store_opcode(LlscWidth::B64, false),
            AArch64Opcode::Stxr
        );
        assert_eq!(
            exclusive_store_opcode(LlscWidth::B128, true),
            AArch64Opcode::Stlxp
        );
    }
}
