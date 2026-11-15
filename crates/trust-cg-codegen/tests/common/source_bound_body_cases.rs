// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! The family corpus of the AArch64 whole-body owner tests
//! (`aarch64_source_bound_body`, `aarch64_source_bound_body_qualification`):
//! sources, references, the AOT and JIT preparations, input grids, typed
//! native calls and the corruptions of real machine bodies.
#![allow(dead_code)]

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::{AArch64Opcode as M, InstId, MachFunction, MachOperand};
use trust_ir::inst::{BinOp, ICmpOp, UnOp};
use trust_ir::{Module, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

pub const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// The C/Rust signature of a case (all integers travel as their bits).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sig {
    /// `(bool, bool, bool) -> bool`
    B3B,
    /// `(bool, u64, u64) -> u64`
    Bxx,
    /// `(u64, u64) -> u64`
    Xx,
    /// `(u32, u32) -> u32`
    Ww,
    /// `(u64) -> u64`
    X,
    /// `(u64, u64, u64, u64) -> u64`
    Xxxx,
    /// `(u64, u64, u64, u64) -> bool`
    XxxxB,
}

impl Sig {
    pub fn params(self) -> Vec<Ty> {
        match self {
            Sig::B3B => vec![Ty::Bool; 3],
            Sig::Bxx => vec![Ty::Bool, Ty::U64, Ty::U64],
            Sig::Xx => vec![Ty::U64; 2],
            Sig::Ww => vec![Ty::U32; 2],
            Sig::X => vec![Ty::U64],
            Sig::Xxxx | Sig::XxxxB => vec![Ty::I64; 4],
        }
    }

    pub fn result(self) -> Ty {
        match self {
            Sig::B3B | Sig::XxxxB => Ty::Bool,
            Sig::Ww => Ty::U32,
            Sig::Xxxx => Ty::I64,
            _ => Ty::U64,
        }
    }

    pub fn c_types(self) -> (&'static str, Vec<&'static str>) {
        match self {
            Sig::B3B => ("_Bool", vec!["_Bool"; 3]),
            Sig::Bxx => ("uint64_t", vec!["_Bool", "uint64_t", "uint64_t"]),
            Sig::Xx => ("uint64_t", vec!["uint64_t"; 2]),
            Sig::Ww => ("uint32_t", vec!["uint32_t"; 2]),
            Sig::X => ("uint64_t", vec!["uint64_t"]),
            Sig::Xxxx => ("uint64_t", vec!["uint64_t"; 4]),
            Sig::XxxxB => ("_Bool", vec!["uint64_t"; 4]),
        }
    }

    /// Input values for each parameter position.
    pub fn domain(self, position: usize) -> &'static [u64] {
        const BOOLS: &[u64] = &[0, 1];
        const WIDE: &[u64] = &[
            0,
            1,
            2,
            3,
            5,
            7,
            31,
            32,
            33,
            63,
            64,
            0x7f,
            0x80,
            0xff,
            0x7fff_ffff,
            0x8000_0000,
            0xffff_ffff,
            0x1_0000_0000,
            0x7fff_ffff_ffff_ffff,
            0x8000_0000_0000_0000,
            u64::MAX,
            0xdead_beef_0123_4567,
        ];
        const NARROW: &[u64] = &[
            0,
            1,
            2,
            31,
            32,
            0x7f,
            0x80,
            0x7fff_ffff,
            0x8000_0000,
            0xffff_ffff,
            0x8000_0000_0000_0000,
            u64::MAX,
        ];
        match (self, position) {
            (Sig::B3B, _) | (Sig::Bxx, 0) => BOOLS,
            (Sig::Ww, _) => &WIDE[..17],
            (Sig::Xxxx | Sig::XxxxB, _) => NARROW,
            _ => WIDE,
        }
    }
}

/// One family member: its source builder, its reference (`None` where the
/// source is undefined) and the same reference in C.
pub struct Case {
    pub name: &'static str,
    pub sig: Sig,
    pub build: fn(&mut FunctionBuilder<'_>, &[ValueId]),
    pub reference: fn(&[u64]) -> Option<u64>,
    pub c_body: &'static str,
}

fn bool_logic(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    let both = f.binop(BinOp::BAnd, Ty::Bool, p[0], p[1]);
    // trust-ir negates a Boolean as `c ^ true` (`UnOp::Not` is integer-only).
    let truth = f.bool_const(true);
    let not_c = f.binop(BinOp::BXor, Ty::Bool, p[2], truth);
    let either = f.binop(BinOp::BOr, Ty::Bool, not_c, p[0]);
    let result = f.binop(BinOp::BXor, Ty::Bool, both, either);
    f.ret(vec![result]);
}

fn bool_select(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    let result = f.select(Ty::U64, p[0], p[1], p[2]);
    f.ret(vec![result]);
}

fn bitwise64(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    let not_y = f.unop(UnOp::Not, Ty::U64, p[1]);
    let cleared = f.binop(BinOp::And, Ty::U64, p[0], not_y);
    let mask = f.iconst(Ty::U64, 0xff);
    let flipped = f.binop(BinOp::Xor, Ty::U64, p[0], mask);
    let result = f.binop(BinOp::Or, Ty::U64, cleared, flipped);
    f.ret(vec![result]);
}

fn bitwise32(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    let not_x = f.unop(UnOp::Not, Ty::U32, p[0]);
    let either = f.binop(BinOp::Or, Ty::U32, not_x, p[1]);
    let mask = f.iconst(Ty::U32, 0xf0f0);
    let kept = f.binop(BinOp::And, Ty::U32, p[0], mask);
    let result = f.binop(BinOp::Xor, Ty::U32, either, kept);
    f.ret(vec![result]);
}

fn masked_shift(f: &mut FunctionBuilder<'_>, p: &[ValueId], op: BinOp, ty: Ty, bits: i128) {
    let mask = f.iconst(ty.clone(), bits - 1);
    let amount = f.binop(BinOp::And, ty.clone(), p[1], mask);
    let result = f.binop(op, ty, p[0], amount);
    f.ret(vec![result]);
}

fn shl_masked64(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    masked_shift(f, p, BinOp::Shl, Ty::U64, 64);
}

fn lshr_masked32(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    masked_shift(f, p, BinOp::LShr, Ty::U32, 32);
}

fn ashr_masked64(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    masked_shift(f, p, BinOp::AShr, Ty::U64, 64);
}

fn shift_imm64(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    let three = f.iconst(Ty::U64, 3);
    let seven = f.iconst(Ty::U64, 7);
    let nine = f.iconst(Ty::U64, 9);
    let left = f.binop(BinOp::Shl, Ty::U64, p[0], three);
    let right = f.binop(BinOp::LShr, Ty::U64, p[0], seven);
    let arith = f.binop(BinOp::AShr, Ty::U64, p[0], nine);
    let both = f.binop(BinOp::Xor, Ty::U64, left, right);
    let result = f.binop(BinOp::Xor, Ty::U64, both, arith);
    f.ret(vec![result]);
}

fn shl_bare64(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    let result = f.binop(BinOp::Shl, Ty::U64, p[0], p[1]);
    f.ret(vec![result]);
}

fn nested_select(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    let less = f.icmp(ICmpOp::Slt, Ty::I64, p[0], p[1]);
    let equal = f.icmp(ICmpOp::Eq, Ty::I64, p[2], p[3]);
    let inner = f.select(Ty::I64, equal, p[2], p[3]);
    let outer = f.select(Ty::I64, less, inner, p[0]);
    let one = f.iconst(Ty::I64, 1);
    let result = f.binop(BinOp::Add, Ty::I64, outer, one);
    f.ret(vec![result]);
}

fn cmp_logic(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    let less = f.icmp(ICmpOp::Slt, Ty::I64, p[0], p[1]);
    let below = f.icmp(ICmpOp::Ult, Ty::I64, p[2], p[3]);
    let result = f.binop(BinOp::BOr, Ty::Bool, less, below);
    f.ret(vec![result]);
}

fn diamond(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    let then_block = f.create_block();
    let else_block = f.create_block();
    let join = f.create_block();
    let joined = f.add_block_param(join, Ty::U64);
    f.condbr(p[0], then_block, vec![], else_block, vec![]);
    f.switch_to_block(then_block);
    let mixed = f.binop(BinOp::Xor, Ty::U64, p[1], p[2]);
    f.br(join, vec![mixed]);
    f.switch_to_block(else_block);
    let five = f.iconst(Ty::U64, 5);
    let shifted = f.binop(BinOp::LShr, Ty::U64, p[2], five);
    f.br(join, vec![shifted]);
    f.switch_to_block(join);
    let one = f.iconst(Ty::U64, 1);
    let result = f.binop(BinOp::Add, Ty::U64, joined, one);
    f.ret(vec![result]);
}

fn dag(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    let inner = f.create_block();
    let other = f.create_block();
    let masked = f.create_block();
    let join = f.create_block();
    let first = f.add_block_param(join, Ty::I64);
    let second = f.add_block_param(join, Ty::I64);
    let less = f.icmp(ICmpOp::Slt, Ty::I64, p[0], p[1]);
    f.condbr(less, inner, vec![], other, vec![]);
    f.switch_to_block(inner);
    let above = f.icmp(ICmpOp::Ugt, Ty::I64, p[2], p[3]);
    f.condbr(above, join, vec![p[2], p[3]], masked, vec![]);
    f.switch_to_block(masked);
    let both = f.binop(BinOp::And, Ty::I64, p[0], p[3]);
    f.br(join, vec![both, p[1]]);
    f.switch_to_block(other);
    f.br(join, vec![p[3], p[2]]);
    f.switch_to_block(join);
    let result = f.binop(BinOp::Sub, Ty::I64, first, second);
    f.ret(vec![result]);
}

fn chain3(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    let nonzero = f.create_block();
    let odd = f.create_block();
    let even = f.create_block();
    let join = f.create_block();
    let joined = f.add_block_param(join, Ty::U32);
    let zero = f.iconst(Ty::U32, 0);
    let is_zero = f.icmp(ICmpOp::Eq, Ty::U32, p[0], zero);
    f.condbr(is_zero, join, vec![p[1]], nonzero, vec![]);
    f.switch_to_block(nonzero);
    let one = f.iconst(Ty::U32, 1);
    let low = f.binop(BinOp::And, Ty::U32, p[0], one);
    let zero = f.iconst(Ty::U32, 0);
    let is_odd = f.icmp(ICmpOp::Ne, Ty::U32, low, zero);
    f.condbr(is_odd, odd, vec![], even, vec![]);
    f.switch_to_block(odd);
    let sum = f.binop(BinOp::Add, Ty::U32, p[0], p[1]);
    f.br(join, vec![sum]);
    f.switch_to_block(even);
    let difference = f.binop(BinOp::Sub, Ty::U32, p[0], p[1]);
    f.br(join, vec![difference]);
    f.switch_to_block(join);
    f.ret(vec![joined]);
}

/// `(-x) ^ (y - 5)`: NEG and SUB #imm.
fn neg_sub(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    let negated = f.unop(UnOp::Neg, Ty::U64, p[0]);
    let five = f.iconst(Ty::U64, 5);
    let less = f.binop(BinOp::Sub, Ty::U64, p[1], five);
    let result = f.binop(BinOp::Xor, Ty::U64, negated, less);
    f.ret(vec![result]);
}

/// `(x + (y << 3)) ^ (x - (y << 4)) ^ (x + (y >> 5))`: shifted-register
/// ADD/SUB where the selector fuses them.
fn shifted_add(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    let (three, four, five) = (
        f.iconst(Ty::U64, 3),
        f.iconst(Ty::U64, 4),
        f.iconst(Ty::U64, 5),
    );
    let up3 = f.binop(BinOp::Shl, Ty::U64, p[1], three);
    let up4 = f.binop(BinOp::Shl, Ty::U64, p[1], four);
    let down5 = f.binop(BinOp::LShr, Ty::U64, p[1], five);
    let a = f.binop(BinOp::Add, Ty::U64, p[0], up3);
    let b = f.binop(BinOp::Sub, Ty::U64, p[0], up4);
    let c = f.binop(BinOp::Add, Ty::U64, p[0], down5);
    let ab = f.binop(BinOp::Xor, Ty::U64, a, b);
    let result = f.binop(BinOp::Xor, Ty::U64, ab, c);
    f.ret(vec![result]);
}

/// `(x ^ (y >> 7)) ^ (y << 9)` and a rotate `x ^ ror(y, 13)`: shifted and
/// rotated EOR where the selector fuses them.
fn xor_shifts(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    let (seven, nine, thirteen, fifty_one) = (
        f.iconst(Ty::U64, 7),
        f.iconst(Ty::U64, 9),
        f.iconst(Ty::U64, 13),
        f.iconst(Ty::U64, 51),
    );
    let down7 = f.binop(BinOp::LShr, Ty::U64, p[1], seven);
    let up9 = f.binop(BinOp::Shl, Ty::U64, p[1], nine);
    let a = f.binop(BinOp::Xor, Ty::U64, p[0], down7);
    let b = f.binop(BinOp::Xor, Ty::U64, a, up9);
    let low = f.binop(BinOp::LShr, Ty::U64, p[0], thirteen);
    let high = f.binop(BinOp::Shl, Ty::U64, p[0], fifty_one);
    let rotated = f.binop(BinOp::Or, Ty::U64, low, high);
    let result = f.binop(BinOp::Xor, Ty::U64, b, rotated);
    f.ret(vec![result]);
}

/// `((x ^ 0x1234_5678_9abc_def0) + 0x5000 | 0xff) ^ 0xffff_ffff_ffff_1234`:
/// wide constants (MOVZ/MOVK/MOVN), ADD #imm, LSL #12 and ORR #imm.
fn wide_constants(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    let wide = f.iconst(Ty::U64, 0x1234_5678_9abc_def0);
    let page = f.iconst(Ty::U64, 0x5000);
    let low = f.iconst(Ty::U64, 0xff);
    let inverted = f.iconst(Ty::U64, 0xffff_ffff_ffff_1234);
    let a = f.binop(BinOp::Xor, Ty::U64, p[0], wide);
    let b = f.binop(BinOp::Add, Ty::U64, a, page);
    let c = f.binop(BinOp::Or, Ty::U64, b, low);
    let result = f.binop(BinOp::Xor, Ty::U64, c, inverted);
    f.ret(vec![result]);
}

/// `if a & 8 != 0 { b ^ c } else { b - c }` and the sign bit of `d`: bit-test
/// branches.
fn bit_branch(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    let set = f.create_block();
    let clear = f.create_block();
    let join = f.create_block();
    let joined = f.add_block_param(join, Ty::I64);
    let eight = f.iconst(Ty::I64, 8);
    let bit = f.binop(BinOp::And, Ty::I64, p[0], eight);
    let zero = f.iconst(Ty::I64, 0);
    let is_set = f.icmp(ICmpOp::Ne, Ty::I64, bit, zero);
    f.condbr(is_set, set, vec![], clear, vec![]);
    f.switch_to_block(set);
    let mixed = f.binop(BinOp::Xor, Ty::I64, p[1], p[2]);
    f.br(join, vec![mixed]);
    f.switch_to_block(clear);
    let difference = f.binop(BinOp::Sub, Ty::I64, p[1], p[2]);
    f.br(join, vec![difference]);
    f.switch_to_block(join);
    let zero = f.iconst(Ty::I64, 0);
    let negative = f.icmp(ICmpOp::Slt, Ty::I64, p[3], zero);
    let one = f.iconst(Ty::I64, 1);
    let flipped = f.binop(BinOp::Xor, Ty::I64, joined, one);
    let result = f.select(Ty::I64, negative, flipped, joined);
    f.ret(vec![result]);
}

/// `select(a < b, c, d + 1) ^ select(a < b, c, !d) ^ select(a < b, c, -d)`:
/// the conditional increment, invert and negate idioms.
fn select_forms(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    let less = f.icmp(ICmpOp::Slt, Ty::I64, p[0], p[1]);
    let one = f.iconst(Ty::I64, 1);
    let succ = f.binop(BinOp::Add, Ty::I64, p[3], one);
    let inverted = f.unop(UnOp::Not, Ty::I64, p[3]);
    let negated = f.unop(UnOp::Neg, Ty::I64, p[3]);
    let a = f.select(Ty::I64, less, p[2], succ);
    let b = f.select(Ty::I64, less, p[2], inverted);
    let c = f.select(Ty::I64, less, p[2], negated);
    let ab = f.binop(BinOp::Xor, Ty::I64, a, b);
    let result = f.binop(BinOp::Xor, Ty::I64, ab, c);
    f.ret(vec![result]);
}

/// `(a < 100) | (b == 4095) | (c >= d)`: compares against imm12 constants.
fn cmp_imm(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    let hundred = f.iconst(Ty::I64, 100);
    let top = f.iconst(Ty::I64, 4095);
    let below = f.icmp(ICmpOp::Ult, Ty::I64, p[0], hundred);
    let equal = f.icmp(ICmpOp::Eq, Ty::I64, p[1], top);
    let at_least = f.icmp(ICmpOp::Sge, Ty::I64, p[2], p[3]);
    let either = f.binop(BinOp::BOr, Ty::Bool, below, equal);
    let result = f.binop(BinOp::BOr, Ty::Bool, either, at_least);
    f.ret(vec![result]);
}

/// `((x << 56) >> 56) ^ ((x << 32) >>> 32) ^ (x & 0xffff)` (`>>` signed):
/// the extension idioms.
fn extensions(f: &mut FunctionBuilder<'_>, p: &[ValueId]) {
    let (fifty_six, thirty_two) = (f.iconst(Ty::U64, 56), f.iconst(Ty::U64, 32));
    let half = f.iconst(Ty::U64, 0xffff);
    let up = f.binop(BinOp::Shl, Ty::U64, p[0], fifty_six);
    let byte = f.binop(BinOp::AShr, Ty::U64, up, fifty_six);
    let up32 = f.binop(BinOp::Shl, Ty::U64, p[0], thirty_two);
    let word = f.binop(BinOp::LShr, Ty::U64, up32, thirty_two);
    let low = f.binop(BinOp::And, Ty::U64, p[0], half);
    let a = f.binop(BinOp::Xor, Ty::U64, byte, word);
    let result = f.binop(BinOp::Xor, Ty::U64, a, low);
    f.ret(vec![result]);
}

fn signed(v: u64) -> i64 {
    v as i64
}

pub const CASES: &[Case] = &[
    Case {
        name: "bool_logic",
        sig: Sig::B3B,
        build: bool_logic,
        reference: |a| Some(((a[0] & a[1]) ^ ((a[2] ^ 1) | a[0])) & 1),
        c_body: "return (a0 & a1) ^ (!a2 | a0);",
    },
    Case {
        name: "bool_select",
        sig: Sig::Bxx,
        build: bool_select,
        reference: |a| Some(if a[0] != 0 { a[1] } else { a[2] }),
        c_body: "return a0 ? a1 : a2;",
    },
    Case {
        name: "bitwise64",
        sig: Sig::Xx,
        build: bitwise64,
        reference: |a| Some((a[0] & !a[1]) | (a[0] ^ 0xff)),
        c_body: "return (a0 & ~a1) | (a0 ^ 0xff);",
    },
    Case {
        name: "bitwise32",
        sig: Sig::Ww,
        build: bitwise32,
        reference: |a| {
            let (x, y) = (a[0] as u32, a[1] as u32);
            Some(u64::from((!x | y) ^ (x & 0xf0f0)))
        },
        c_body: "return (~a0 | a1) ^ (a0 & 0xf0f0u);",
    },
    Case {
        name: "shl_masked64",
        sig: Sig::Xx,
        build: shl_masked64,
        reference: |a| Some(a[0] << (a[1] & 63)),
        c_body: "return a0 << (a1 & 63);",
    },
    Case {
        name: "lshr_masked32",
        sig: Sig::Ww,
        build: lshr_masked32,
        reference: |a| Some(u64::from((a[0] as u32) >> (a[1] as u32 & 31))),
        c_body: "return a0 >> (a1 & 31);",
    },
    Case {
        name: "ashr_masked64",
        sig: Sig::Xx,
        build: ashr_masked64,
        reference: |a| Some((signed(a[0]) >> (a[1] & 63)) as u64),
        c_body: "return (uint64_t)((int64_t)a0 >> (a1 & 63));",
    },
    Case {
        name: "shift_imm64",
        sig: Sig::X,
        build: shift_imm64,
        reference: |a| Some((a[0] << 3) ^ (a[0] >> 7) ^ ((signed(a[0]) >> 9) as u64)),
        c_body: "return (a0 << 3) ^ (a0 >> 7) ^ (uint64_t)((int64_t)a0 >> 9);",
    },
    Case {
        name: "shl_bare64",
        sig: Sig::Xx,
        build: shl_bare64,
        // trust-ir ShiftInRange: an amount at or above the width is undefined.
        reference: |a| (a[1] < 64).then(|| a[0] << a[1]),
        c_body: "return a0 << a1; /* driver calls only a1 < 64 */",
    },
    Case {
        name: "nested_select",
        sig: Sig::Xxxx,
        build: nested_select,
        reference: |a| {
            let inner = if a[2] == a[3] { a[2] } else { a[3] };
            Some(
                if signed(a[0]) < signed(a[1]) {
                    inner
                } else {
                    a[0]
                }
                .wrapping_add(1),
            )
        },
        c_body: "uint64_t inner = a2 == a3 ? a2 : a3; \
                 return ((int64_t)a0 < (int64_t)a1 ? inner : a0) + 1;",
    },
    Case {
        name: "cmp_logic",
        sig: Sig::XxxxB,
        build: cmp_logic,
        reference: |a| Some(u64::from(signed(a[0]) < signed(a[1]) || a[2] < a[3])),
        c_body: "return ((int64_t)a0 < (int64_t)a1) | (a2 < a3);",
    },
    Case {
        name: "diamond",
        sig: Sig::Bxx,
        build: diamond,
        reference: |a| Some(if a[0] != 0 { a[1] ^ a[2] } else { a[2] >> 5 }.wrapping_add(1)),
        c_body: "return (a0 ? a1 ^ a2 : a2 >> 5) + 1;",
    },
    Case {
        name: "dag",
        sig: Sig::Xxxx,
        build: dag,
        reference: |a| {
            let (p, q) = if signed(a[0]) < signed(a[1]) {
                if a[2] > a[3] {
                    (a[2], a[3])
                } else {
                    (a[0] & a[3], a[1])
                }
            } else {
                (a[3], a[2])
            };
            Some(p.wrapping_sub(q))
        },
        c_body: "uint64_t p, q; \
                 if ((int64_t)a0 < (int64_t)a1) { if (a2 > a3) { p = a2; q = a3; } \
                 else { p = a0 & a3; q = a1; } } else { p = a3; q = a2; } return p - q;",
    },
    Case {
        name: "chain3",
        sig: Sig::Ww,
        build: chain3,
        reference: |a| {
            let (x, y) = (a[0] as u32, a[1] as u32);
            Some(u64::from(if x == 0 {
                y
            } else if x & 1 != 0 {
                x.wrapping_add(y)
            } else {
                x.wrapping_sub(y)
            }))
        },
        c_body: "return a0 == 0 ? a1 : (a0 & 1) ? a0 + a1 : a0 - a1;",
    },
    Case {
        name: "neg_sub",
        sig: Sig::Xx,
        build: neg_sub,
        reference: |a| Some(a[0].wrapping_neg() ^ a[1].wrapping_sub(5)),
        c_body: "return (0 - a0) ^ (a1 - 5);",
    },
    Case {
        name: "shifted_add",
        sig: Sig::Xx,
        build: shifted_add,
        reference: |a| {
            Some(
                a[0].wrapping_add(a[1] << 3)
                    ^ a[0].wrapping_sub(a[1] << 4)
                    ^ a[0].wrapping_add(a[1] >> 5),
            )
        },
        c_body: "return (a0 + (a1 << 3)) ^ (a0 - (a1 << 4)) ^ (a0 + (a1 >> 5));",
    },
    Case {
        name: "xor_shifts",
        sig: Sig::Xx,
        build: xor_shifts,
        reference: |a| Some(a[0] ^ (a[1] >> 7) ^ (a[1] << 9) ^ a[0].rotate_right(13)),
        c_body: "return a0 ^ (a1 >> 7) ^ (a1 << 9) ^ ((a0 >> 13) | (a0 << 51));",
    },
    Case {
        name: "wide_constants",
        sig: Sig::X,
        build: wide_constants,
        reference: |a| {
            Some(
                ((a[0] ^ 0x1234_5678_9abc_def0).wrapping_add(0x5000) | 0xff)
                    ^ 0xffff_ffff_ffff_1234,
            )
        },
        c_body: "return (((a0 ^ UINT64_C(0x123456789abcdef0)) + 0x5000) | 0xff) \
                 ^ UINT64_C(0xffffffffffff1234);",
    },
    Case {
        name: "bit_branch",
        sig: Sig::Xxxx,
        build: bit_branch,
        reference: |a| {
            let joined = if a[0] & 8 != 0 {
                a[1] ^ a[2]
            } else {
                a[1].wrapping_sub(a[2])
            };
            Some(if signed(a[3]) < 0 { joined ^ 1 } else { joined })
        },
        c_body: "uint64_t j = (a0 & 8) ? a1 ^ a2 : a1 - a2; \
                 return (int64_t)a3 < 0 ? j ^ 1 : j;",
    },
    Case {
        name: "select_forms",
        sig: Sig::Xxxx,
        build: select_forms,
        reference: |a| {
            let less = signed(a[0]) < signed(a[1]);
            let pick = |other: u64| if less { a[2] } else { other };
            Some(pick(a[3].wrapping_add(1)) ^ pick(!a[3]) ^ pick(a[3].wrapping_neg()))
        },
        c_body: "int l = (int64_t)a0 < (int64_t)a1; \
                 return (l ? a2 : a3 + 1) ^ (l ? a2 : ~a3) ^ (l ? a2 : 0 - a3);",
    },
    Case {
        name: "cmp_imm",
        sig: Sig::XxxxB,
        build: cmp_imm,
        reference: |a| {
            Some(u64::from(
                a[0] < 100 || a[1] == 4095 || signed(a[2]) >= signed(a[3]),
            ))
        },
        c_body: "return (a0 < 100) | (a1 == 4095) | ((int64_t)a2 >= (int64_t)a3);",
    },
    Case {
        name: "extensions",
        sig: Sig::X,
        build: extensions,
        reference: |a| {
            Some((((a[0] << 56) as i64 >> 56) as u64) ^ ((a[0] << 32) >> 32) ^ (a[0] & 0xffff))
        },
        c_body: "return (uint64_t)((int64_t)(a0 << 56) >> 56) ^ ((a0 << 32) >> 32) \
                 ^ (a0 & 0xffff);",
    },
];

pub fn symbol(case: &Case) -> String {
    format!("sb_{}", case.name)
}

pub fn module(case: &Case) -> Module {
    let mut builder = ModuleBuilder::new("source_bound_a64_body");
    let signature = builder.add_func_type(case.sig.params(), vec![case.sig.result()]);
    let mut f = builder.function(symbol(case), signature);
    let entry = f.create_block();
    let params: Vec<ValueId> = case
        .sig
        .params()
        .into_iter()
        .map(|ty| f.add_block_param(entry, ty))
        .collect();
    f.switch_to_block(entry);
    (case.build)(&mut f, &params);
    f.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

pub fn lir(module: &Module) -> trust_cg_lower::Function {
    trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        module,
        &permit_unlicensed(),
    )
    .expect("the source passes the actual TrustIR adapter")
    .0
}

/// The unchanged private-function capture uses the ordinary module adapter,
/// with explicit diagnostic body permission, rather than the stricter public
/// single-function v45 admission. This grants no proof authority.
pub fn captured_narrow_leaf() -> trust_cg_lower::Function {
    let module = trust_ir::binary::deserialize_module(include_bytes!(
        "../fixtures/aarch64_nonleaf_frame/termination_report.trust_irbin"
    ))
    .unwrap();
    let admitted = trust_cg_lower::ingest::admit_module(&module, &permit_unlicensed(), &[])
        .expect("the original module passes diagnostic ingestion");
    let (mut functions, _) =
        trust_cg_lower::translate_admitted_module_for_arch_with_access_model_and_stats(
            &admitted,
            trust_cg_lower::GuardCarrierArch::AArch64,
            trust_cg_lower::ObjectAccessModel::macho_dyld(),
            trust_cg_lower::ObjectSymbolPolicy::AARCH64_MACHO_MODULE,
        )
        .expect("the actual Mach-O module path preserves the captured hidden definition");
    assert_eq!(functions.len(), 1);
    functions.remove(0).0
}

/// The two preparations of a source the routes publish: the AOT route's
/// (the host pipeline's default register allocator) and the JIT's (the
/// `jit_fast` profile's latency-tuned allocator). Both at proof grade.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Prep {
    Aot,
    Jit,
}

pub const PREPS: [Prep; 2] = [Prep::Aot, Prep::Jit];

/// The machine function as `prep` prepares it, for the host triple at proof
/// grade. `Prep::Aot` keeps the pipeline's default register allocator, as
/// the AOT route does; `Prep::Jit` enables the fast one, as
/// `CompilerConfig::jit_fast` (and so the verifying JIT) does, and
/// `jit_preparation_is_the_published_jit_code` checks that its bytes are the
/// bytes the JIT publishes.
pub fn prepare_as(prep: Prep, lir: &trust_cg_lower::Function, level: OptLevel) -> MachFunction {
    Pipeline::new(PipelineConfig {
        opt_level: level,
        verify: false,
        enable_jit_fast_regalloc: prep == Prep::Jit,
        ..PipelineConfig::for_host_aarch64()
    })
    .with_proof_grade_aarch64_publication()
    .prepare_function(lir)
    .unwrap_or_else(|error| panic!("{}: {error}", lir.name))
}

pub fn grid(sig: Sig) -> Vec<Vec<u64>> {
    let arity = sig.params().len();
    let mut rows = vec![Vec::new()];
    for position in 0..arity {
        let mut next = Vec::new();
        for row in &rows {
            for value in sig.domain(position) {
                let mut extended = row.clone();
                extended.push(*value);
                next.push(extended);
            }
        }
        rows = next;
    }
    rows
}

pub fn on_big_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

/// One corruption of a real machine body: a class name and the mutated
/// function.
pub fn mutants(machine: &MachFunction, covered: &[InstId]) -> Vec<(&'static str, MachFunction)> {
    let mut out = Vec::new();
    let mut push = |class: &'static str, id: InstId, edit: &dyn Fn(&mut trust_cg_ir::MachInst)| {
        let mut changed = machine.clone();
        edit(&mut changed.insts[id.0 as usize]);
        let (before, after) = (&machine.insts[id.0 as usize], &changed.insts[id.0 as usize]);
        if (before.opcode, &before.operands) != (after.opcode, &after.operands) {
            out.push((class, changed));
        }
    };
    let in_arm = |id: InstId| {
        machine
            .block_order
            .iter()
            .skip(1)
            .any(|block| machine.blocks[block.0 as usize].insts.contains(&id))
    };
    for &id in covered {
        let inst = &machine.insts[id.0 as usize];
        let cc_index = match inst.opcode {
            M::Csel | M::Csinc | M::Csinv | M::Csneg => Some(3),
            M::CSet | M::BCond => Some(if inst.opcode == M::CSet { 1 } else { 0 }),
            _ => None,
        };
        if let Some(index) = cc_index
            && let Some(MachOperand::Imm(cc)) = inst.operands.get(index)
            && *cc < 14
        {
            push(
                "inverted condition",
                id,
                &|inst: &mut trust_cg_ir::MachInst| {
                    if let MachOperand::Imm(ref mut cc) = inst.operands[index] {
                        *cc ^= 1;
                    }
                },
            );
            // A different condition of the other order (signed for unsigned).
            push(
                "wrong condition",
                id,
                &|inst: &mut trust_cg_ir::MachInst| {
                    let MachOperand::Imm(ref mut cc) = inst.operands[index] else {
                        return;
                    };
                    *cc = match *cc {
                        0 | 1 => *cc ^ 1,
                        2 => 10,
                        3 => 11,
                        8 => 12,
                        9 => 13,
                        10 => 2,
                        11 => 3,
                        12 => 8,
                        13 => 9,
                        other => other ^ 1,
                    };
                },
            );
        }
        match inst.opcode {
            M::Csel | M::Csinc | M::Csinv | M::Csneg => {
                push("swapped arms", id, &|inst| inst.operands.swap(1, 2));
            }
            M::Cbz | M::Cbnz => push("cbz/cbnz exchanged", id, &|inst| {
                inst.opcode = if inst.opcode == M::Cbz {
                    M::Cbnz
                } else {
                    M::Cbz
                };
            }),
            M::Tbz | M::Tbnz => push("tbz/tbnz exchanged", id, &|inst| {
                inst.opcode = if inst.opcode == M::Tbz {
                    M::Tbnz
                } else {
                    M::Tbz
                };
            }),
            M::LslRR | M::LsrRR | M::AsrRR => push("wrong shift kind", id, &|inst| {
                inst.opcode = match inst.opcode {
                    M::LslRR => M::LsrRR,
                    M::LsrRR => M::AsrRR,
                    _ => M::LsrRR,
                };
            }),
            M::LslRI | M::LsrRI | M::AsrRI => {
                push("wrong shift kind", id, &|inst| {
                    inst.opcode = match inst.opcode {
                        M::LslRI => M::LsrRI,
                        M::LsrRI => M::AsrRI,
                        _ => M::LsrRI,
                    };
                });
                push(
                    "wrong shift amount",
                    id,
                    &|inst: &mut trust_cg_ir::MachInst| {
                        if let MachOperand::Imm(ref mut amount) = inst.operands[2]
                            && *amount < 31
                        {
                            *amount += 1;
                        }
                    },
                );
            }
            M::EorRRLsl | M::EorRRLsr | M::AddRRShift | M::AddRRShiftLsr => {
                push(
                    "wrong shift kind",
                    id,
                    &|inst: &mut trust_cg_ir::MachInst| {
                        inst.opcode = match inst.opcode {
                            M::EorRRLsl => M::EorRRLsr,
                            M::EorRRLsr => M::EorRRLsl,
                            M::AddRRShift => M::AddRRShiftLsr,
                            _ => M::AddRRShift,
                        };
                    },
                );
                push(
                    "wrong shift amount",
                    id,
                    &|inst: &mut trust_cg_ir::MachInst| {
                        if let MachOperand::Imm(ref mut amount) = inst.operands[3]
                            && *amount < 31
                        {
                            *amount += 1;
                        }
                    },
                );
            }
            M::Ubfm | M::Sbfm => push("wrong shift kind", id, &|inst| {
                inst.opcode = if inst.opcode == M::Ubfm {
                    M::Sbfm
                } else {
                    M::Ubfm
                };
            }),
            M::AndRI | M::OrrRI | M::EorRI => {
                push("changed mask", id, &|inst: &mut trust_cg_ir::MachInst| {
                    if let MachOperand::Imm(ref mut mask) = inst.operands[2]
                        && !matches!(*mask, 1 | -2)
                    {
                        *mask ^= 1;
                    }
                })
            }
            // Each replacement differs from the row unless both operands are
            // always zero (OR and EOR agree on disjoint operands, so neither
            // replaces the other: a rotate's two halves are disjoint).
            M::AndRR | M::OrrRR | M::EorRR | M::BicRR | M::OrnRR => {
                push("different logic row", id, &|inst| {
                    inst.opcode = match inst.opcode {
                        M::AndRR => M::OrrRR,
                        M::OrrRR | M::EorRR => M::AndRR,
                        M::BicRR => M::OrnRR,
                        _ => M::BicRR,
                    };
                });
            }
            _ => {}
        }
        // A dropped block argument: an arm's value row writes a register
        // nothing else reads, so the join sees whatever its old value was.
        if in_arm(id)
            && !matches!(
                inst.opcode,
                M::B | M::BCond
                    | M::Cbz
                    | M::Cbnz
                    | M::Tbz
                    | M::Tbnz
                    | M::CmpRR
                    | M::CmpRI
                    | M::Tst
            )
            && let Some(MachOperand::PReg(register)) = inst.operands.first()
        {
            let spare = trust_cg_ir::regs::PReg::new(if register.encoding() >= 32 {
                32 + 15
            } else {
                15
            });
            push("dropped block argument", id, &|inst| {
                inst.operands[0] = MachOperand::PReg(spare);
            });
        }
    }
    out
}

/// Call `name` in `buffer` with `args` under the case's C ABI.
pub fn call(
    buffer: &trust_cg_codegen::jit::ExecutableBuffer,
    name: &str,
    sig: Sig,
    a: &[u64],
) -> u64 {
    // SAFETY: each arm uses the exact source signature's C ABI and the
    // buffer stays live for the call.
    unsafe {
        match sig {
            Sig::B3B => u64::from((buffer
                .get_fn_bound::<extern "C" fn(bool, bool, bool) -> bool>(name)
                .unwrap()
                .as_ref())(a[0] != 0, a[1] != 0, a[2] != 0)),
            Sig::Bxx => (buffer
                .get_fn_bound::<extern "C" fn(bool, u64, u64) -> u64>(name)
                .unwrap()
                .as_ref())(a[0] != 0, a[1], a[2]),
            Sig::Xx => (buffer
                .get_fn_bound::<extern "C" fn(u64, u64) -> u64>(name)
                .unwrap()
                .as_ref())(a[0], a[1]),
            Sig::Ww => u64::from((buffer
                .get_fn_bound::<extern "C" fn(u32, u32) -> u32>(name)
                .unwrap()
                .as_ref())(a[0] as u32, a[1] as u32)),
            Sig::X => (buffer
                .get_fn_bound::<extern "C" fn(u64) -> u64>(name)
                .unwrap()
                .as_ref())(a[0]),
            Sig::Xxxx => (buffer
                .get_fn_bound::<extern "C" fn(u64, u64, u64, u64) -> u64>(name)
                .unwrap()
                .as_ref())(a[0], a[1], a[2], a[3]),
            Sig::XxxxB => u64::from((buffer
                .get_fn_bound::<extern "C" fn(u64, u64, u64, u64) -> bool>(name)
                .unwrap()
                .as_ref())(a[0], a[1], a[2], a[3])),
        }
    }
}

/// This module's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
