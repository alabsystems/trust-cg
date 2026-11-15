// trust-cg-codegen/wasm/lower/wide.rs - 128-bit integer arithmetic
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `I128` / `U128` arithmetic.
//!
//! A 128-bit integer value is carried either as a pair of `i64` locals (low
//! and high half, [`Carrier::Pair`], chosen per value by `pair.rs` at O1 and
//! above) or in memory (16 bytes, little-endian: the low `i64` half at offset
//! 0, the high half at 8). Every operation reads its operands' halves
//! ([`Lowering::load_halves`]: a pair's own locals, or two loads), computes
//! the result halves in `i64` locals, and writes them to the result
//! ([`Lowering::store_halves`]: into a pair's locals, or two stores into its
//! home slot). No library is called, so a closed module and an object
//! compute 128-bit arithmetic identically. Everything but division is inline
//! wasm:
//!
//! * add/sub propagate the carry/borrow between halves;
//! * mul composes the 64x64->128 product of the low halves (four 32-bit limb
//!   products) with the two cross terms;
//! * the shifts use the amount modulo 128 and select between the in-half and
//!   cross-half forms without a branch; a pair shifted or rotated by an
//!   integer constant (O1 and above, where pairs exist) gets the constant
//!   half shifts of that amount instead;
//! * division and remainder call the module's ONE trust-ir division helper
//!   (`helpers::divmod128_module`, compiled by this lane and carried by the
//!   closed module or the object itself) with the operands' halves, the
//!   result's home address (a transient frame slot for a pair, loaded after
//!   the call) and a constant mode; the helper writes the result;
//! * the checked forms (`Overflow`) derive the flag from the halves exactly as
//!   the 64-bit forms do from the words;
//! * float -> 128-bit conversions split the (exact) magnitude into two
//!   64-bit truncations and saturate, and 128-bit -> float conversions round
//!   ONCE: a normalized 64-bit window with a sticky bit, converted and scaled
//!   by an exact power of two.

use trust_ir::{AtomicRMWOp, BinOp, Constant, ICmpOp, Inst, OverflowOp, Ty, UnOp, ValueId};

use super::super::encode::{
    ValType, emit_i32_const, emit_local_get, op, write_sleb128, write_uleb128,
};
use super::super::layout::Carrier;
use super::{Lowering, WasmLowerError, slot};

/// A 128-bit value's halves, as two `i64` locals.
#[derive(Clone, Copy)]
pub(super) struct Halves {
    lo: u32,
    hi: u32,
}

/// Where a 128-bit `Switch` value is read from.
#[derive(Debug, Clone, Copy)]
pub(super) enum WideSource {
    /// The address of its 16 bytes.
    Addr(u32),
    /// Its `(low, high)` pair locals.
    Pair(u32, u32),
}

pub(super) fn is_wide(ty: &Ty) -> bool {
    matches!(ty, Ty::I128 | Ty::U128)
}

impl Lowering<'_> {
    fn i64c(&mut self, v: i64) {
        self.code.push(op::I64_CONST);
        write_sleb128(&mut self.code, v);
    }

    fn get(&mut self, l: u32) {
        emit_local_get(&mut self.code, l);
    }

    fn set(&mut self, l: u32) {
        self.emit_local_set(l);
    }

    fn halves(&mut self) -> Halves {
        Halves {
            lo: self.temp(ValType::I64),
            hi: self.temp(ValType::I64),
        }
    }

    /// The `(low, high)` locals of pair-carried `v`.
    pub(super) fn pair_of(&self, v: ValueId) -> Result<(u32, u32), WasmLowerError> {
        self.pair_locals.get(&v).copied().ok_or_else(|| {
            WasmLowerError::UndefinedValue(format!(
                "{v:?} in `{}` has no 128-bit pair locals",
                self.func.name
            ))
        })
    }

    /// Where 128-bit `v`'s halves are read from: its pair locals, or the
    /// address of its bytes.
    pub(super) fn wide_source(&mut self, v: ValueId) -> Result<WideSource, WasmLowerError> {
        if self.is_pair(v) {
            let (lo, hi) = self.pair_of(v)?;
            return Ok(WideSource::Pair(lo, hi));
        }
        Ok(WideSource::Addr(self.addr_local(v)?))
    }

    /// Push `[i64]`: the low (or, `high`, the high) half read from `src`.
    pub(super) fn push_wide_half(
        &mut self,
        src: WideSource,
        high: bool,
    ) -> Result<(), WasmLowerError> {
        match src {
            WideSource::Addr(addr) => {
                self.get(addr);
                self.emit_load(&Ty::U64, if high { 8 } else { 0 })
            }
            WideSource::Pair(lo, hi) => {
                self.get(if high { hi } else { lo });
                Ok(())
            }
        }
    }

    /// Whether `v` is pair-carried.
    pub(super) fn is_pair(&self, v: ValueId) -> bool {
        self.carriers.get(&v) == Some(&Carrier::Pair)
    }

    /// `v`'s halves: a pair's own locals (read-only to the caller: every
    /// 128-bit computation writes fresh [`Self::halves`]), or its bytes
    /// loaded into two fresh locals.
    pub(super) fn load_halves(&mut self, v: ValueId) -> Result<Halves, WasmLowerError> {
        if self.is_pair(v) {
            let (lo, hi) = self.pair_of(v)?;
            return Ok(Halves { lo, hi });
        }
        let a = self.addr_local(v)?;
        let h = self.halves();
        self.get(a);
        self.emit_load(&Ty::U64, 0)?;
        self.set(h.lo);
        self.get(a);
        self.emit_load(&Ty::U64, 8)?;
        self.set(h.hi);
        Ok(h)
    }

    /// Write halves to `result`: its pair locals, or its bytes.
    pub(super) fn store_halves(
        &mut self,
        result: ValueId,
        h: Halves,
    ) -> Result<(), WasmLowerError> {
        if self.is_pair(result) {
            let (lo, hi) = self.pair_of(result)?;
            self.get(h.lo);
            self.set(lo);
            self.get(h.hi);
            self.set(hi);
            return Ok(());
        }
        let a = self.addr_local(result)?;
        self.get(a);
        self.get(h.lo);
        self.emit_store(&Ty::U64, 0)?;
        self.get(a);
        self.get(h.hi);
        self.emit_store(&Ty::U64, 8)
    }

    /// Store pair-carried `v`'s halves at `addr + offset` (its 16-byte
    /// little-endian image).
    pub(super) fn store_pair_at(
        &mut self,
        addr: u32,
        offset: u32,
        v: ValueId,
    ) -> Result<(), WasmLowerError> {
        let (lo, hi) = self.pair_of(v)?;
        let hi_offset = offset.checked_add(8).ok_or_else(|| {
            WasmLowerError::FrameLayoutOverflow(format!(
                "a 128-bit value at offset {offset} in `{}`",
                self.func.name
            ))
        })?;
        self.get(addr);
        self.get(lo);
        self.emit_store(&Ty::U64, offset)?;
        self.get(addr);
        self.get(hi);
        self.emit_store(&Ty::U64, hi_offset)
    }

    /// Load the 16-byte image at `addr + offset` into pair-carried `v`'s
    /// locals; `push_addr` pushes `addr`, once per half.
    pub(super) fn load_pair_from(
        &mut self,
        v: ValueId,
        offset: u32,
        push_addr: &dyn Fn(&mut Self),
    ) -> Result<(), WasmLowerError> {
        let (lo, hi) = self.pair_of(v)?;
        let hi_offset = offset.checked_add(8).ok_or_else(|| {
            WasmLowerError::FrameLayoutOverflow(format!(
                "a 128-bit value at offset {offset} in `{}`",
                self.func.name
            ))
        })?;
        push_addr(self);
        self.emit_load(&Ty::U64, offset)?;
        self.set(lo);
        push_addr(self);
        self.emit_load(&Ty::U64, hi_offset)?;
        self.set(hi);
        Ok(())
    }

    /// Define pair-carried `v` as the 128-bit constant `k`.
    pub(super) fn const_pair(&mut self, v: ValueId, k: u128) -> Result<(), WasmLowerError> {
        let (lo, hi) = self.pair_of(v)?;
        self.i64c(k as u64 as i64);
        self.set(lo);
        self.i64c((k >> 64) as u64 as i64);
        self.set(hi);
        Ok(())
    }

    /// Copy pair-carried `source` into pair-carried `result`.
    pub(super) fn copy_pair(
        &mut self,
        result: ValueId,
        source: ValueId,
    ) -> Result<(), WasmLowerError> {
        let h = self.load_halves(source)?;
        self.store_halves(result, h)
    }

    /// `[] -> [i64]`: the high 64 bits of the unsigned product of locals `a`
    /// and `b`, from four 32-bit limb products.
    fn mulhu64(&mut self, a: u32, b: u32) {
        let (a0, a1, b0, b1) = (
            self.temp(ValType::I64),
            self.temp(ValType::I64),
            self.temp(ValType::I64),
            self.temp(ValType::I64),
        );
        for (src, lo, hi) in [(a, a0, a1), (b, b0, b1)] {
            self.get(src);
            self.i64c(0xffff_ffff);
            self.code.push(op::I64_AND);
            self.set(lo);
            self.get(src);
            self.i64c(32);
            self.code.push(op::I64_SHR_U);
            self.set(hi);
        }
        let (p01, p10, mid) = (
            self.temp(ValType::I64),
            self.temp(ValType::I64),
            self.temp(ValType::I64),
        );
        self.get(a0);
        self.get(b1);
        self.code.push(op::I64_MUL);
        self.set(p01);
        self.get(a1);
        self.get(b0);
        self.code.push(op::I64_MUL);
        self.set(p10);
        // mid = (a0*b0 >> 32) + (p01 & M) + (p10 & M)   (< 3 * 2^32, no wrap)
        self.get(a0);
        self.get(b0);
        self.code.push(op::I64_MUL);
        self.i64c(32);
        self.code.push(op::I64_SHR_U);
        self.get(p01);
        self.i64c(0xffff_ffff);
        self.code.push(op::I64_AND);
        self.code.push(op::I64_ADD);
        self.get(p10);
        self.i64c(0xffff_ffff);
        self.code.push(op::I64_AND);
        self.code.push(op::I64_ADD);
        self.set(mid);
        // hi = a1*b1 + (p01 >> 32) + (p10 >> 32) + (mid >> 32)
        self.get(a1);
        self.get(b1);
        self.code.push(op::I64_MUL);
        self.get(p01);
        self.i64c(32);
        self.code.push(op::I64_SHR_U);
        self.code.push(op::I64_ADD);
        self.get(p10);
        self.i64c(32);
        self.code.push(op::I64_SHR_U);
        self.code.push(op::I64_ADD);
        self.get(mid);
        self.i64c(32);
        self.code.push(op::I64_SHR_U);
        self.code.push(op::I64_ADD);
    }

    /// The wrapping 128-bit product of `a` and `b`.
    fn mul128(&mut self, a: Halves, b: Halves) -> Halves {
        let r = self.halves();
        self.get(a.lo);
        self.get(b.lo);
        self.code.push(op::I64_MUL);
        self.set(r.lo);
        self.mulhu64(a.lo, b.lo);
        self.get(a.lo);
        self.get(b.hi);
        self.code.push(op::I64_MUL);
        self.code.push(op::I64_ADD);
        self.get(a.hi);
        self.get(b.lo);
        self.code.push(op::I64_MUL);
        self.code.push(op::I64_ADD);
        self.set(r.hi);
        r
    }

    fn add128(&mut self, a: Halves, b: Halves) -> Halves {
        let r = self.halves();
        self.get(a.lo);
        self.get(b.lo);
        self.code.push(op::I64_ADD);
        self.set(r.lo);
        self.get(a.hi);
        self.get(b.hi);
        self.code.push(op::I64_ADD);
        self.get(r.lo);
        self.get(a.lo);
        self.code.push(op::I64_LT_U); // carry out of the low half
        self.code.push(op::I64_EXTEND_I32_U);
        self.code.push(op::I64_ADD);
        self.set(r.hi);
        r
    }

    fn sub128(&mut self, a: Halves, b: Halves) -> Halves {
        let r = self.halves();
        self.get(a.lo);
        self.get(b.lo);
        self.code.push(op::I64_SUB);
        self.set(r.lo);
        self.get(a.hi);
        self.get(b.hi);
        self.code.push(op::I64_SUB);
        self.get(a.lo);
        self.get(b.lo);
        self.code.push(op::I64_LT_U); // borrow out of the low half
        self.code.push(op::I64_EXTEND_I32_U);
        self.code.push(op::I64_SUB);
        self.set(r.hi);
        r
    }

    fn bitwise128(&mut self, opcode: u8, a: Halves, b: Halves) -> Halves {
        let r = self.halves();
        for (x, y, d) in [(a.lo, b.lo, r.lo), (a.hi, b.hi, r.hi)] {
            self.get(x);
            self.get(y);
            self.code.push(opcode);
            self.set(d);
        }
        r
    }

    fn const128(&mut self, v: u128) -> Halves {
        let r = self.halves();
        self.i64c(v as u64 as i64);
        self.set(r.lo);
        self.i64c((v >> 64) as u64 as i64);
        self.set(r.hi);
        r
    }

    fn neg128(&mut self, a: Halves) -> Halves {
        let z = self.const128(0);
        self.sub128(z, a)
    }

    /// `x << s` for a shift amount local `s` (i64) already reduced to 0..128.
    fn shl128(&mut self, a: Halves, s: u32) -> Halves {
        let (k, big) = self.shift_parts(s);
        let (x, y) = (self.temp(ValType::I64), self.temp(ValType::I64));
        // x = lo << k ; y = (hi << k) | ((lo >> 1) >> (63 - k))
        self.get(a.lo);
        self.get(k);
        self.code.push(op::I64_SHL);
        self.set(x);
        self.get(a.hi);
        self.get(k);
        self.code.push(op::I64_SHL);
        self.get(a.lo);
        self.i64c(1);
        self.code.push(op::I64_SHR_U);
        self.i64c(63);
        self.get(k);
        self.code.push(op::I64_SUB);
        self.code.push(op::I64_SHR_U);
        self.code.push(op::I64_OR);
        self.set(y);
        let r = self.halves();
        // big: hi = x, lo = 0 ; else hi = y, lo = x
        self.get(x);
        self.get(y);
        self.get(big);
        self.code.push(op::SELECT);
        self.set(r.hi);
        self.i64c(0);
        self.get(x);
        self.get(big);
        self.code.push(op::SELECT);
        self.set(r.lo);
        r
    }

    /// `x >> s`, logical or arithmetic.
    fn shr128(&mut self, a: Halves, s: u32, arith: bool) -> Halves {
        let (k, big) = self.shift_parts(s);
        let (x, y, fill) = (
            self.temp(ValType::I64),
            self.temp(ValType::I64),
            self.temp(ValType::I64),
        );
        let hi_shift = if arith { op::I64_SHR_S } else { op::I64_SHR_U };
        // x = hi >> k ; y = (lo >>u k) | ((hi << 1) << (63 - k))
        self.get(a.hi);
        self.get(k);
        self.code.push(hi_shift);
        self.set(x);
        self.get(a.lo);
        self.get(k);
        self.code.push(op::I64_SHR_U);
        self.get(a.hi);
        self.i64c(1);
        self.code.push(op::I64_SHL);
        self.i64c(63);
        self.get(k);
        self.code.push(op::I64_SUB);
        self.code.push(op::I64_SHL);
        self.code.push(op::I64_OR);
        self.set(y);
        if arith {
            self.get(a.hi);
            self.i64c(63);
            self.code.push(op::I64_SHR_S);
        } else {
            self.i64c(0);
        }
        self.set(fill);
        let r = self.halves();
        // big: lo = x, hi = fill ; else lo = y, hi = x
        self.get(x);
        self.get(y);
        self.get(big);
        self.code.push(op::SELECT);
        self.set(r.lo);
        self.get(fill);
        self.get(x);
        self.get(big);
        self.code.push(op::SELECT);
        self.set(r.hi);
        r
    }

    /// The amount, reduced modulo 128 as [`Self::amount128`] reduces it, of a
    /// shift or rotate whose amount operand is an integer `Const` of the
    /// function (the low seven bits of its value, which every carrier of the
    /// operand holds alike); `None` for any other operand.
    fn const_shift_amount(&self, amount: ValueId) -> Option<u32> {
        self.func
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .find(|n| n.results.as_slice() == [amount])
            .and_then(|n| match &n.inst {
                Inst::Const { ty, value } if ty.is_integer() => match value {
                    Constant::Int(k) => Some((*k as u128 & 127) as u32),
                    Constant::U128(k) => Some((*k & 127) as u32),
                    _ => None,
                },
                _ => None,
            })
    }

    /// `x << s` for a constant `s` in 0..128.
    fn shl128_const(&mut self, a: Halves, s: u32) -> Halves {
        let r = self.halves();
        match s {
            0 => {
                self.get(a.lo);
                self.set(r.lo);
                self.get(a.hi);
                self.set(r.hi);
            }
            1..=63 => {
                // hi = (hi << s) | (lo >>u (64 - s)) ; lo = lo << s
                self.get(a.hi);
                self.i64c(i64::from(s));
                self.code.push(op::I64_SHL);
                self.get(a.lo);
                self.i64c(i64::from(64 - s));
                self.code.push(op::I64_SHR_U);
                self.code.push(op::I64_OR);
                self.set(r.hi);
                self.get(a.lo);
                self.i64c(i64::from(s));
                self.code.push(op::I64_SHL);
                self.set(r.lo);
            }
            _ => {
                // hi = lo << (s - 64) ; lo = 0
                self.get(a.lo);
                if s > 64 {
                    self.i64c(i64::from(s - 64));
                    self.code.push(op::I64_SHL);
                }
                self.set(r.hi);
                self.i64c(0);
                self.set(r.lo);
            }
        }
        r
    }

    /// `x >> s` for a constant `s` in 0..128, logical or arithmetic.
    fn shr128_const(&mut self, a: Halves, s: u32, arith: bool) -> Halves {
        let r = self.halves();
        let hi_shift = if arith { op::I64_SHR_S } else { op::I64_SHR_U };
        match s {
            0 => {
                self.get(a.lo);
                self.set(r.lo);
                self.get(a.hi);
                self.set(r.hi);
            }
            1..=63 => {
                // lo = (lo >>u s) | (hi << (64 - s)) ; hi = hi >> s
                self.get(a.lo);
                self.i64c(i64::from(s));
                self.code.push(op::I64_SHR_U);
                self.get(a.hi);
                self.i64c(i64::from(64 - s));
                self.code.push(op::I64_SHL);
                self.code.push(op::I64_OR);
                self.set(r.lo);
                self.get(a.hi);
                self.i64c(i64::from(s));
                self.code.push(hi_shift);
                self.set(r.hi);
            }
            _ => {
                // lo = hi >> (s - 64) ; hi = the sign fill (or 0)
                self.get(a.hi);
                if s > 64 {
                    self.i64c(i64::from(s - 64));
                    self.code.push(hi_shift);
                }
                self.set(r.lo);
                if arith {
                    self.get(a.hi);
                    self.i64c(63);
                    self.code.push(op::I64_SHR_S);
                } else {
                    self.i64c(0);
                }
                self.set(r.hi);
            }
        }
        r
    }

    /// Split a 0..128 shift amount into `(amount mod 64, amount >= 64)`.
    fn shift_parts(&mut self, s: u32) -> (u32, u32) {
        let (k, big) = (self.temp(ValType::I64), self.temp(ValType::I32));
        self.get(s);
        self.i64c(63);
        self.code.push(op::I64_AND);
        self.set(k);
        self.get(s);
        self.i64c(64);
        self.code.push(op::I64_AND);
        self.code.push(op::I64_EQZ);
        self.code.push(op::I32_EQZ);
        self.set(big);
        (k, big)
    }

    /// A shift/rotate amount operand reduced modulo 128 into an i64 local.
    fn amount128(&mut self, amount: ValueId) -> Result<u32, WasmLowerError> {
        let s = self.temp(ValType::I64);
        if self.is_pair(amount) {
            let (lo, _) = self.pair_of(amount)?;
            self.get(lo);
        } else if super::super::layout::carrier_of(self.module, &self.value_ty(amount)?)?.is_mem() {
            let a = self.addr_local(amount)?;
            self.get(a);
            self.emit_load(&Ty::U64, 0)?;
        } else {
            let (l, vt) = slot(&self.locals, amount)?;
            self.get(l);
            if vt == ValType::I32 {
                self.code.push(op::I64_EXTEND_I32_U);
            }
        }
        self.i64c(127);
        self.code.push(op::I64_AND);
        self.set(s);
        Ok(s)
    }

    /// `[] -> [i32]` for a 128-bit comparison.
    fn cmp128(&mut self, cmp: ICmpOp, a: Halves, b: Halves) {
        use ICmpOp::*;
        let (lhs, rhs, hi_lt, lo_lt, strict) = match cmp {
            Eq | Ne => {
                self.get(a.lo);
                self.get(b.lo);
                self.code.push(op::I64_EQ);
                self.get(a.hi);
                self.get(b.hi);
                self.code.push(op::I64_EQ);
                self.code.push(op::I32_AND);
                if cmp == Ne {
                    self.code.push(op::I32_EQZ);
                }
                return;
            }
            Ult => (a, b, op::I64_LT_U, op::I64_LT_U, true),
            Ule => (b, a, op::I64_LT_U, op::I64_LT_U, false),
            Ugt => (b, a, op::I64_LT_U, op::I64_LT_U, true),
            Uge => (a, b, op::I64_LT_U, op::I64_LT_U, false),
            Slt => (a, b, op::I64_LT_S, op::I64_LT_U, true),
            Sle => (b, a, op::I64_LT_S, op::I64_LT_U, false),
            Sgt => (b, a, op::I64_LT_S, op::I64_LT_U, true),
            Sge => (a, b, op::I64_LT_S, op::I64_LT_U, false),
        };
        // lt(lhs, rhs) = hi_lt(lhs.hi, rhs.hi) | (lhs.hi == rhs.hi & lo_lt(lhs.lo, rhs.lo))
        self.get(lhs.hi);
        self.get(rhs.hi);
        self.code.push(hi_lt);
        self.get(lhs.hi);
        self.get(rhs.hi);
        self.code.push(op::I64_EQ);
        self.get(lhs.lo);
        self.get(rhs.lo);
        self.code.push(lo_lt);
        self.code.push(op::I32_AND);
        self.code.push(op::I32_OR);
        if !strict {
            // `a <= b` is `!(b < a)`: the operands were swapped above.
            self.code.push(op::I32_EQZ);
        }
    }

    /// `|a|` as unsigned halves and the sign (i32 0/1) of a signed 128-bit value.
    fn abs128(&mut self, a: Halves) -> (Halves, u32) {
        let neg = self.temp(ValType::I32);
        self.get(a.hi);
        self.i64c(0);
        self.code.push(op::I64_LT_S);
        self.set(neg);
        let n = self.neg128(a);
        let r = self.halves();
        for (x, y, d) in [(n.lo, a.lo, r.lo), (n.hi, a.hi, r.hi)] {
            self.get(x);
            self.get(y);
            self.get(neg);
            self.code.push(op::SELECT);
            self.set(d);
        }
        (r, neg)
    }

    /// Conditionally negate halves by an i32 flag.
    fn cond_neg128(&mut self, a: Halves, flag: u32) -> Halves {
        let n = self.neg128(a);
        let r = self.halves();
        for (x, y, d) in [(n.lo, a.lo, r.lo), (n.hi, a.hi, r.hi)] {
            self.get(x);
            self.get(y);
            self.get(flag);
            self.code.push(op::SELECT);
            self.set(d);
        }
        r
    }

    fn f64c(&mut self, v: f64) {
        self.code.push(op::F64_CONST);
        self.code.extend_from_slice(&v.to_le_bytes());
    }

    fn sat_op(&mut self, sub: u32) {
        self.code.push(op::FC_PREFIX);
        write_uleb128(&mut self.code, u64::from(sub));
    }

    /// Float -> 128-bit integer, SATURATING: NaN is 0, a value beyond the
    /// range clamps to its bound, anything else truncates toward zero — the
    /// reference interpreter's `FPToSISat`/`FPToUISat` with the bounds of the
    /// OP's signedness. The raw `FPToSI`/`FPToUI` are undefined exactly where
    /// these saturate, so they lower identically (and the rustc bridge's `as`
    /// casts rely on the saturation).
    ///
    /// With `a` the (f64-promoted, exact) magnitude, `h = trunc_sat_u64(a *
    /// 2^-64)` and `l = trunc_sat_u64(a - h * 2^64)` are both exact: `h` is
    /// `floor(a / 2^64)` (an f64 at or above `2^53` is already integral), and
    /// `a - h * 2^64` is a multiple of `ulp(a)` below `min(a, 2^64)`, so the
    /// subtraction does not round. NaN and negatives fall out of `trunc_sat`
    /// as 0; the saturation bounds are selected explicitly.
    pub(super) fn lower_float_to_wide(
        &mut self,
        result: ValueId,
        signed: bool,
        src_ty: &Ty,
        operand: ValueId,
    ) -> Result<(), WasmLowerError> {
        let src = slot(&self.locals, operand)?.0;
        let x = self.temp(ValType::F64);
        self.get(src);
        if *src_ty == Ty::F32 {
            self.code.push(op::F64_PROMOTE_F32);
        }
        self.set(x);
        let a = self.temp(ValType::F64);
        self.get(x);
        if signed {
            self.code.push(op::F64_ABS);
        }
        self.set(a);
        let split = self.halves();
        self.get(a);
        self.f64c(f64::from_bits(959 << 52)); // 2^-64
        self.code.push(op::F64_MUL);
        self.sat_op(op::I64_TRUNC_SAT_F64_U);
        self.set(split.hi);
        self.get(a);
        self.get(split.hi);
        self.code.push(op::F64_CONVERT_I64_U);
        self.f64c(f64::from_bits(1087 << 52)); // 2^64
        self.code.push(op::F64_MUL);
        self.code.push(op::F64_SUB);
        self.sat_op(op::I64_TRUNC_SAT_F64_U);
        self.set(split.lo);
        // (bound lo, bound hi, saturate?) per signedness.
        let r = if signed {
            let neg = self.temp(ValType::I32);
            self.get(x);
            self.f64c(0.0);
            self.code.push(op::F64_LT);
            self.set(neg);
            let big = self.temp(ValType::I32);
            self.get(a);
            self.f64c(f64::from_bits(1150 << 52)); // 2^127
            self.code.push(op::F64_GE);
            self.set(big);
            let v = self.cond_neg128(split, neg);
            let r = self.halves();
            // big: lo = neg ? 0 : -1 ; hi = neg ? i64::MIN : i64::MAX
            self.i64c(0);
            self.i64c(-1);
            self.get(neg);
            self.code.push(op::SELECT);
            self.get(v.lo);
            self.get(big);
            self.code.push(op::SELECT);
            self.set(r.lo);
            self.i64c(i64::MIN);
            self.i64c(i64::MAX);
            self.get(neg);
            self.code.push(op::SELECT);
            self.get(v.hi);
            self.get(big);
            self.code.push(op::SELECT);
            self.set(r.hi);
            r
        } else {
            let big = self.temp(ValType::I32);
            self.get(x);
            self.f64c(f64::from_bits(1151 << 52)); // 2^128
            self.code.push(op::F64_GE);
            self.set(big);
            let r = self.halves();
            for (from, to) in [(split.lo, r.lo), (split.hi, r.hi)] {
                self.i64c(-1);
                self.get(from);
                self.get(big);
                self.code.push(op::SELECT);
                self.set(to);
            }
            r
        };
        self.store_halves(result, r)
    }

    /// 128-bit integer -> float, rounded ONCE to nearest-even, as the
    /// reference interpreter rounds the exact integer (`as_signed` /
    /// `as_unsigned` by the OP's signedness).
    ///
    /// A magnitude below `2^64` is one `convert_i64_u`. Otherwise, with `n =
    /// clz(hi)`, the value shifted left by `n` has its top 64 bits in `top`
    /// (MSB set) and the rest nonzero exactly when `lo << n` is: OR-ing that
    /// as a sticky bit into bit 0 — far below the rounding position (bit 10
    /// for f64, bit 39 for f32) — makes `convert_i64_u(top | sticky)` round
    /// exactly as the whole value rounds. Scaling by `2^(64 - n)` is then
    /// exact, or overflows to infinity exactly where the value does.
    pub(super) fn lower_wide_to_float(
        &mut self,
        result: ValueId,
        signed: bool,
        dst_ty: &Ty,
        operand: ValueId,
    ) -> Result<(), WasmLowerError> {
        let x = self.load_halves(operand)?;
        let (a, neg) = if signed {
            let (a, neg) = self.abs128(x);
            (a, Some(neg))
        } else {
            (x, None)
        };
        let f32_dst = *dst_ty == Ty::F32;
        let (vt, convert, mul, neg_op) = if f32_dst {
            (
                ValType::F32,
                op::F32_CONVERT_I64_U,
                op::F32_MUL,
                op::F32_NEG,
            )
        } else {
            (
                ValType::F64,
                op::F64_CONVERT_I64_U,
                op::F64_MUL,
                op::F64_NEG,
            )
        };
        let n = self.temp(ValType::I64);
        self.get(a.hi);
        self.code.push(op::I64_CLZ);
        self.set(n);
        // top | sticky
        self.get(a.hi);
        self.get(n);
        self.code.push(op::I64_SHL);
        self.get(a.lo);
        self.i64c(1);
        self.code.push(op::I64_SHR_U);
        self.i64c(63);
        self.get(n);
        self.code.push(op::I64_SUB);
        self.code.push(op::I64_SHR_U);
        self.code.push(op::I64_OR);
        self.get(a.lo);
        self.get(n);
        self.code.push(op::I64_SHL);
        self.i64c(0);
        self.code.push(op::I64_NE);
        self.code.push(op::I64_EXTEND_I32_U);
        self.code.push(op::I64_OR);
        self.code.push(convert);
        // * 2^(64 - n), built from its exponent field.
        self.i64c(64);
        self.get(n);
        self.code.push(op::I64_SUB);
        if f32_dst {
            self.code.push(op::I32_WRAP_I64);
            emit_i32_const(&mut self.code, 127);
            self.code.push(op::I32_ADD);
            emit_i32_const(&mut self.code, 23);
            self.code.push(op::I32_SHL);
            self.code.push(op::F32_REINTERPRET_I32);
        } else {
            self.i64c(1023);
            self.code.push(op::I64_ADD);
            self.i64c(52);
            self.code.push(op::I64_SHL);
            self.code.push(op::F64_REINTERPRET_I64);
        }
        self.code.push(mul);
        // hi == 0: the low half alone, converted once.
        self.get(a.lo);
        self.code.push(convert);
        self.get(a.hi);
        self.i64c(0);
        self.code.push(op::I64_NE);
        self.code.push(op::SELECT);
        if let Some(neg) = neg {
            let m = self.temp(vt);
            self.set(m);
            self.get(m);
            self.code.push(neg_op);
            self.get(m);
            self.get(neg);
            self.code.push(op::SELECT);
        }
        let d = slot(&self.locals, result)?.0;
        self.set(d);
        Ok(())
    }

    /// A 128-bit `BinOp`.
    pub(super) fn lower_wide_binop(
        &mut self,
        site: (usize, usize),
        result: ValueId,
        bin: BinOp,
        lhs: ValueId,
        rhs: ValueId,
    ) -> Result<(), WasmLowerError> {
        if matches!(bin, BinOp::UDiv | BinOp::URem | BinOp::SDiv | BinOp::SRem) {
            return self.call_divmod128(site, result, bin, lhs, rhs);
        }
        let a = self.load_halves(lhs)?;
        // A constant amount on a pair (O1 and above only: pairs exist there
        // alone, so O0 keeps the general sequence) is applied with constant
        // half shifts, as the general form computes it for that amount.
        if matches!(
            bin,
            BinOp::Shl | BinOp::LShr | BinOp::AShr | BinOp::RotL | BinOp::RotR
        ) && (self.is_pair(lhs) || self.is_pair(result))
            && let Some(s) = self.const_shift_amount(rhs)
        {
            let r = match bin {
                BinOp::Shl => self.shl128_const(a, s),
                BinOp::LShr => self.shr128_const(a, s, false),
                BinOp::AShr => self.shr128_const(a, s, true),
                _ => {
                    // rotl(x, s) = (x << s) | (x >> ((128 - s) & 127)).
                    let back = (128 - s) & 127;
                    let (fwd, back) = if bin == BinOp::RotL {
                        (s, back)
                    } else {
                        (back, s)
                    };
                    let l = self.shl128_const(a, fwd);
                    let rr = self.shr128_const(a, back, false);
                    self.bitwise128(op::I64_OR, l, rr)
                }
            };
            return self.store_halves(result, r);
        }
        let r = match bin {
            BinOp::Shl | BinOp::LShr | BinOp::AShr | BinOp::RotL | BinOp::RotR => {
                let s = self.amount128(rhs)?;
                match bin {
                    BinOp::Shl => self.shl128(a, s),
                    BinOp::LShr => self.shr128(a, s, false),
                    BinOp::AShr => self.shr128(a, s, true),
                    _ => {
                        // rotl(x, s) = (x << s) | (x >> ((128 - s) & 127)); a zero
                        // amount gives x | x.
                        let t = self.temp(ValType::I64);
                        self.i64c(128);
                        self.get(s);
                        self.code.push(op::I64_SUB);
                        self.i64c(127);
                        self.code.push(op::I64_AND);
                        self.set(t);
                        let (fwd, back) = if bin == BinOp::RotL { (s, t) } else { (t, s) };
                        let l = self.shl128(a, fwd);
                        let rr = self.shr128(a, back, false);
                        self.bitwise128(op::I64_OR, l, rr)
                    }
                }
            }
            _ => {
                let b = self.load_halves(rhs)?;
                match bin {
                    BinOp::Add => self.add128(a, b),
                    BinOp::Sub => self.sub128(a, b),
                    BinOp::Mul => self.mul128(a, b),
                    BinOp::And | BinOp::BAnd => self.bitwise128(op::I64_AND, a, b),
                    BinOp::Or | BinOp::BOr => self.bitwise128(op::I64_OR, a, b),
                    BinOp::Xor | BinOp::BXor => self.bitwise128(op::I64_XOR, a, b),
                    other => {
                        return Err(WasmLowerError::UnsupportedInst(format!(
                            "BinOp::{other:?} on a 128-bit integer"
                        )));
                    }
                }
            }
        };
        self.store_halves(result, r)
    }

    /// A 128-bit `UDiv` / `URem` / `SDiv` / `SRem`: one call to the module's
    /// division helper, `(lhs.lo, lhs.hi, rhs.lo, rhs.hi, &result, mode)`,
    /// which stores the result's halves into its home slot — or, for a
    /// pair-carried result, into the site's transient frame slot
    /// (`compute_frame`), from which the pair is loaded after the call. The
    /// operands are read before the call, so a result slot shared with an
    /// operand is harmless.
    fn call_divmod128(
        &mut self,
        site: (usize, usize),
        result: ValueId,
        bin: BinOp,
        lhs: ValueId,
        rhs: ValueId,
    ) -> Result<(), WasmLowerError> {
        let callee = self.helpers.divmod128.ok_or_else(|| {
            WasmLowerError::UnsupportedInst(format!(
                "BinOp::{bin:?} on a 128-bit integer in `{}`: no 128-bit division helper was \
                 provisioned",
                self.func.name
            ))
        })?;
        for v in [lhs, rhs] {
            if self.is_pair(v) {
                let (lo, hi) = self.pair_of(v)?;
                self.get(lo);
                self.get(hi);
                continue;
            }
            let a = self.addr_local(v)?;
            self.get(a);
            self.emit_load(&Ty::U64, 0)?;
            self.get(a);
            self.emit_load(&Ty::U64, 8)?;
        }
        let scratch = if self.is_pair(result) {
            let off = *self.divmod_scratch.get(&site).ok_or_else(|| {
                WasmLowerError::UnsupportedInst(format!(
                    "128-bit division in `{}` has no scratch slot for its pair-carried result",
                    self.func.name
                ))
            })?;
            let base = self.frame.map(|f| f.base_local).ok_or_else(|| {
                WasmLowerError::UnsupportedInst(format!(
                    "128-bit division scratch in `{}` has no frame",
                    self.func.name
                ))
            })?;
            self.get(base);
            emit_i32_const(&mut self.code, off as i32);
            self.code.push(op::I32_ADD);
            Some((base, off))
        } else {
            let out = self.addr_local(result)?;
            self.get(out);
            None
        };
        let signed = matches!(bin, BinOp::SDiv | BinOp::SRem);
        let remainder = matches!(bin, BinOp::URem | BinOp::SRem);
        emit_i32_const(
            &mut self.code,
            super::super::helpers::divmod128_mode(signed, remainder),
        );
        self.emit_call(callee);
        if let Some((base, off)) = scratch {
            self.load_pair_from(result, off, &|s: &mut Self| s.get(base))?;
        }
        Ok(())
    }

    /// A 128-bit `UnOp`.
    pub(super) fn lower_wide_unop(
        &mut self,
        result: ValueId,
        un: UnOp,
        operand: ValueId,
    ) -> Result<(), WasmLowerError> {
        let a = self.load_halves(operand)?;
        let r = match un {
            UnOp::Neg => self.neg128(a),
            UnOp::Not => {
                let ones = self.const128(u128::MAX);
                self.bitwise128(op::I64_XOR, a, ones)
            }
            UnOp::CtPop | UnOp::CtLz | UnOp::CtTz => {
                let r = self.halves();
                match un {
                    UnOp::CtPop => {
                        self.get(a.lo);
                        self.code.push(op::I64_POPCNT);
                        self.get(a.hi);
                        self.code.push(op::I64_POPCNT);
                        self.code.push(op::I64_ADD);
                    }
                    UnOp::CtLz => {
                        // hi != 0 ? clz(hi) : 64 + clz(lo)
                        self.get(a.hi);
                        self.code.push(op::I64_CLZ);
                        self.get(a.lo);
                        self.code.push(op::I64_CLZ);
                        self.i64c(64);
                        self.code.push(op::I64_ADD);
                        self.get(a.hi);
                        self.code.push(op::I64_EQZ);
                        self.code.push(op::I32_EQZ);
                        self.code.push(op::SELECT);
                    }
                    _ => {
                        // lo != 0 ? ctz(lo) : 64 + ctz(hi)
                        self.get(a.lo);
                        self.code.push(op::I64_CTZ);
                        self.get(a.hi);
                        self.code.push(op::I64_CTZ);
                        self.i64c(64);
                        self.code.push(op::I64_ADD);
                        self.get(a.lo);
                        self.code.push(op::I64_EQZ);
                        self.code.push(op::I32_EQZ);
                        self.code.push(op::SELECT);
                    }
                }
                self.set(r.lo);
                self.i64c(0);
                self.set(r.hi);
                r
            }
            UnOp::BSwap | UnOp::BitReverse => {
                // The halves trade places, each reversed at 64 bits.
                let r = self.halves();
                let ty = Ty::U64;
                for (src, dst) in [(a.hi, r.lo), (a.lo, r.hi)] {
                    self.emit_bit_unop(un, &ty, src)?;
                    self.set(dst);
                }
                r
            }
            other => {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "UnOp::{other:?} on a 128-bit integer"
                )));
            }
        };
        self.store_halves(result, r)
    }

    /// A 128-bit `ICmp` into its i32 boolean result.
    pub(super) fn lower_wide_icmp(
        &mut self,
        result: ValueId,
        cmp: ICmpOp,
        lhs: ValueId,
        rhs: ValueId,
    ) -> Result<(), WasmLowerError> {
        let a = self.load_halves(lhs)?;
        let b = self.load_halves(rhs)?;
        let d = slot(&self.locals, result)?.0;
        self.cmp128(cmp, a, b);
        self.set(d);
        Ok(())
    }

    /// A 128-bit `Overflow`: the wrapped result and the overflow flag.
    pub(super) fn lower_wide_overflow(
        &mut self,
        results: &[ValueId],
        oop: OverflowOp,
        signed: bool,
        lhs: ValueId,
        rhs: ValueId,
    ) -> Result<(), WasmLowerError> {
        let a = self.load_halves(lhs)?;
        let b = self.load_halves(rhs)?;
        let flag = self.temp(ValType::I32);
        let value = match oop {
            OverflowOp::AddOverflow | OverflowOp::SubOverflow => {
                let add = oop == OverflowOp::AddOverflow;
                let r = if add {
                    self.add128(a, b)
                } else {
                    self.sub128(a, b)
                };
                if signed {
                    // add: ((a ^ r) & (b ^ r)) < 0 ; sub: ((a ^ b) & (a ^ r)) < 0
                    let (x, y) = if add { (b.hi, r.hi) } else { (b.hi, a.hi) };
                    self.get(a.hi);
                    self.get(r.hi);
                    self.code.push(op::I64_XOR);
                    self.get(x);
                    self.get(y);
                    self.code.push(op::I64_XOR);
                    self.code.push(op::I64_AND);
                    self.i64c(0);
                    self.code.push(op::I64_LT_S);
                } else if add {
                    self.cmp128(ICmpOp::Ult, r, a);
                } else {
                    self.cmp128(ICmpOp::Ult, a, b);
                }
                self.set(flag);
                r
            }
            OverflowOp::MulOverflow => {
                let product = self.mul128(a, b);
                let (ua, ub, neg) = if signed {
                    let (ua, na) = self.abs128(a);
                    let (ub, nb) = self.abs128(b);
                    let neg = self.temp(ValType::I32);
                    self.get(na);
                    self.get(nb);
                    self.code.push(op::I32_XOR);
                    self.set(neg);
                    (ua, ub, Some(neg))
                } else {
                    (a, b, None)
                };
                // Unsigned overflow of ua * ub: both high halves nonzero, or a
                // cross term's high word nonzero, or the high-half sum carries.
                let up = self.mul128(ua, ub);
                self.get(ua.hi);
                self.code.push(op::I64_EQZ);
                self.get(ub.hi);
                self.code.push(op::I64_EQZ);
                self.code.push(op::I32_OR);
                self.code.push(op::I32_EQZ);
                self.mulhu64(ua.hi, ub.lo);
                self.i64c(0);
                self.code.push(op::I64_NE);
                self.code.push(op::I32_OR);
                self.mulhu64(ua.lo, ub.hi);
                self.i64c(0);
                self.code.push(op::I64_NE);
                self.code.push(op::I32_OR);
                // carry: up.hi <u mulhu(ua.lo, ub.lo)
                self.get(up.hi);
                self.mulhu64(ua.lo, ub.lo);
                self.code.push(op::I64_LT_U);
                self.code.push(op::I32_OR);
                if let Some(neg) = neg {
                    // In range iff |product| <= 2^127 - 1 (+1 when negative).
                    let big = self.temp(ValType::I32);
                    let limit = self.const128(1u128 << 127);
                    self.set(big);
                    // neg ? up > 2^127 : up >= 2^127
                    self.cmp128(ICmpOp::Ugt, up, limit);
                    self.cmp128(ICmpOp::Uge, up, limit);
                    self.get(neg);
                    self.code.push(op::SELECT);
                    self.get(big);
                    self.code.push(op::I32_OR);
                }
                self.set(flag);
                product
            }
        };
        if let Some(&r) = results.first() {
            self.store_halves(r, value)?;
        }
        if let Some(&o) = results.get(1) {
            let d = slot(&self.locals, o)?.0;
            self.get(flag);
            self.set(d);
        }
        Ok(())
    }

    /// The halves of the 128-bit integer at the address in local `addr`.
    fn load_halves_at(&mut self, addr: u32) -> Result<Halves, WasmLowerError> {
        let h = self.halves();
        self.get(addr);
        self.emit_load(&Ty::U64, 0)?;
        self.set(h.lo);
        self.get(addr);
        self.emit_load(&Ty::U64, 8)?;
        self.set(h.hi);
        Ok(h)
    }

    /// Store halves at the address in local `addr`.
    fn store_halves_at(&mut self, addr: u32, h: Halves) -> Result<(), WasmLowerError> {
        self.get(addr);
        self.get(h.lo);
        self.emit_store(&Ty::U64, 0)?;
        self.get(addr);
        self.get(h.hi);
        self.emit_store(&Ty::U64, 8)
    }

    /// `cond ? a : b`, half by half; `cond` is an `i32` local.
    pub(super) fn select128(&mut self, cond: u32, a: Halves, b: Halves) -> Halves {
        let r = self.halves();
        for (x, y, d) in [(a.lo, b.lo, r.lo), (a.hi, b.hi, r.hi)] {
            self.get(x);
            self.get(y);
            self.get(cond);
            self.code.push(op::SELECT);
            self.set(d);
        }
        r
    }

    /// `AtomicRMW` on a 128-bit integer: `old = *p; *p = old <op> v;
    /// result = old`. The lane is single-threaded (it declares no shared
    /// memory and no `threads` feature), so the interpreter's atomic
    /// read-modify-write is exactly these plain loads and stores, whatever
    /// the ordering.
    pub(super) fn lower_wide_atomic_rmw(
        &mut self,
        result: Option<ValueId>,
        rop: AtomicRMWOp,
        ptr: ValueId,
        value: ValueId,
    ) -> Result<(), WasmLowerError> {
        let p = slot(&self.locals, ptr)?.0;
        let old = self.load_halves_at(p)?;
        let v = self.load_halves(value)?;
        let new = match rop {
            AtomicRMWOp::Xchg => v,
            AtomicRMWOp::Add => self.add128(old, v),
            AtomicRMWOp::Sub => self.sub128(old, v),
            AtomicRMWOp::And => self.bitwise128(op::I64_AND, old, v),
            AtomicRMWOp::Or => self.bitwise128(op::I64_OR, old, v),
            AtomicRMWOp::Xor => self.bitwise128(op::I64_XOR, old, v),
            AtomicRMWOp::Max | AtomicRMWOp::Min | AtomicRMWOp::UMax | AtomicRMWOp::UMin => {
                let keep_old = match rop {
                    AtomicRMWOp::Max => ICmpOp::Sgt,
                    AtomicRMWOp::Min => ICmpOp::Slt,
                    AtomicRMWOp::UMax => ICmpOp::Ugt,
                    _ => ICmpOp::Ult,
                };
                self.cmp128(keep_old, old, v);
                let c = self.temp(ValType::I32);
                self.set(c);
                self.select128(c, old, v)
            }
        };
        self.store_halves_at(p, new)?;
        if let Some(r) = result {
            self.store_halves(r, old)?;
        }
        Ok(())
    }

    /// `CmpXchg` on a 128-bit integer: results `(old, old == expected)`,
    /// `desired` stored on success — single-threaded, as
    /// [`Self::lower_wide_atomic_rmw`].
    pub(super) fn lower_wide_cmpxchg(
        &mut self,
        results: &[ValueId],
        ptr: ValueId,
        expected: ValueId,
        desired: ValueId,
    ) -> Result<(), WasmLowerError> {
        let p = slot(&self.locals, ptr)?.0;
        let old = self.load_halves_at(p)?;
        let e = self.load_halves(expected)?;
        let n = self.load_halves(desired)?;
        self.cmp128(ICmpOp::Eq, old, e);
        let ok = self.temp(ValType::I32);
        self.set(ok);
        let new = self.select128(ok, n, old);
        self.store_halves_at(p, new)?;
        if let Some(&r) = results.first() {
            self.store_halves(r, old)?;
        }
        if let Some(&r) = results.get(1) {
            let d = slot(&self.locals, r)?.0;
            self.get(ok);
            self.set(d);
        }
        Ok(())
    }

    /// Push `[i32]`: whether the 128-bit switch value read from `src`
    /// equals `case`.
    pub(super) fn emit_wide_case_eq(
        &mut self,
        src: WideSource,
        case: u128,
    ) -> Result<(), WasmLowerError> {
        self.push_wide_half(src, false)?;
        self.i64c(case as u64 as i64);
        self.code.push(op::I64_EQ);
        self.push_wide_half(src, true)?;
        self.i64c((case >> 64) as u64 as i64);
        self.code.push(op::I64_EQ);
        self.code.push(op::I32_AND);
        Ok(())
    }
}
