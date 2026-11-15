// trust-cg-codegen/wasm/lower/ops.rs - the scalar operators beyond Slice 0-3
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Scalar operators that have no single wasm opcode, or whose trust-ir
//! semantics differ from the nearest one:
//!
//! * `Overflow` (checked `add`/`sub`/`mul`) at every integer width;
//! * the bit intrinsics `CtLz`/`CtTz`/`BSwap`/`BitReverse` and the rotates,
//!   including their narrow-width forms;
//! * `FMin`/`FMax` (Rust `min`/`max`: a NaN operand yields the other operand,
//!   where wasm's `f*.min` propagates NaN) and `FCopySign`;
//! * `FRem` (exact `fmod`, through a helper — wasm has no remainder op);
//! * `Select`, `Assume`, `NullPtr`, `Undef`;
//! * atomics, lowered to plain memory operations: a wasm32 module without the
//!   threads proposal has one thread of execution and a non-shared memory, so
//!   every ordering is trivially satisfied (rustc's `wasm32-unknown-unknown`
//!   makes the same choice);
//! * `MemCopy` / `MemSet` (bulk-memory `memory.copy` / `memory.fill`).
//!
//! Every expansion keeps invariant N (the narrow-carrier invariant, module
//! docs of `super`): narrow operands are read at the view the operation needs
//! and narrow results are re-canonicalized.

use trust_cg_verify::wasm_local_tv::MAX_EXPANDED_COPY;
use trust_ir::{AtomicRMWOp, BinOp, Constant, ICmpOp, OverflowOp, Ty, UnOp, ValueId};

use super::super::encode::{ValType, emit_i32_const, emit_local_get, op, write_sleb128};
use super::super::layout::Carrier;
use super::{IntRepr, IntView, Lowering, WasmLowerError, int_repr_of, narrow_of, slot};

/// `if` block type producing one `i32`.
const BLOCKTYPE_I32: u8 = 0x7f;

impl Lowering<'_> {
    /// Declare a fresh scratch local.
    pub(super) fn temp(&mut self, vt: ValType) -> u32 {
        let idx = self.next_local;
        self.declared_locals.push(vt);
        self.next_local += 1;
        idx
    }

    fn i64_const(&mut self, v: i64) {
        self.code.push(op::I64_CONST);
        write_sleb128(&mut self.code, v);
    }

    fn int_repr(&self, ty: &Ty) -> Result<IntRepr, WasmLowerError> {
        int_repr_of(ty)
            .ok_or_else(|| WasmLowerError::UnsupportedInst(format!("integer operation on {ty:?}")))
    }

    /// Bind (or drop) result `index` of a node from the value on the stack.
    fn set_result(&mut self, results: &[ValueId], index: usize) -> Result<(), WasmLowerError> {
        match results.get(index) {
            Some(r) => {
                let d = slot(&self.locals, *r)?.0;
                self.emit_local_set(d);
            }
            None => self.code.push(op::DROP),
        }
        Ok(())
    }

    /// `Overflow { op, ty, lhs, rhs }` → `(wrapped value, overflowed)`.
    pub(super) fn lower_overflow(
        &mut self,
        results: &[ValueId],
        oop: OverflowOp,
        ty: &Ty,
        lhs: ValueId,
        rhs: ValueId,
    ) -> Result<(), WasmLowerError> {
        if matches!(ty, Ty::I128 | Ty::U128) {
            return Err(WasmLowerError::UnsupportedInst(format!(
                "Overflow::{oop:?} on {ty:?} (128-bit checked arithmetic)"
            )));
        }
        let repr = self.int_repr(ty)?;
        let a = slot(&self.locals, lhs)?.0;
        let b = slot(&self.locals, rhs)?.0;
        let view = if repr.signed {
            IntView::Signed
        } else {
            IntView::Unsigned
        };
        match repr.carrier {
            ValType::I32 if repr.bits < 32 => {
                // The exact result of an 8/16-bit add/sub/mul fits in i32.
                let exact = self.temp(ValType::I32);
                self.emit_operand(a, Some(repr), Some(view))?;
                self.emit_operand(b, Some(repr), Some(view))?;
                self.code.push(match oop {
                    OverflowOp::AddOverflow => op::I32_ADD,
                    OverflowOp::SubOverflow => op::I32_SUB,
                    OverflowOp::MulOverflow => op::I32_MUL,
                });
                self.emit_local_set(exact);
                let value = self.temp(ValType::I32);
                emit_local_get(&mut self.code, exact);
                self.emit_canonicalize(repr)?;
                self.emit_local_set(value);
                emit_local_get(&mut self.code, value);
                emit_local_get(&mut self.code, exact);
                self.code.push(op::I32_NE);
                self.set_result(results, 1)?;
                emit_local_get(&mut self.code, value);
                self.set_result(results, 0)
            }
            ValType::I32 => {
                // 32-bit: compute exactly in i64, overflow iff the wrapped
                // value does not extend back to the exact one.
                let extend = if repr.signed {
                    op::I64_EXTEND_I32_S
                } else {
                    op::I64_EXTEND_I32_U
                };
                let exact = self.temp(ValType::I64);
                emit_local_get(&mut self.code, a);
                self.code.push(extend);
                emit_local_get(&mut self.code, b);
                self.code.push(extend);
                self.code.push(match oop {
                    OverflowOp::AddOverflow => op::I64_ADD,
                    OverflowOp::SubOverflow => op::I64_SUB,
                    OverflowOp::MulOverflow => op::I64_MUL,
                });
                self.emit_local_set(exact);
                let value = self.temp(ValType::I32);
                emit_local_get(&mut self.code, exact);
                self.code.push(op::I32_WRAP_I64);
                self.emit_local_set(value);
                emit_local_get(&mut self.code, value);
                self.code.push(extend);
                emit_local_get(&mut self.code, exact);
                self.code.push(op::I64_NE);
                self.set_result(results, 1)?;
                emit_local_get(&mut self.code, value);
                self.set_result(results, 0)
            }
            ValType::I64 => self.lower_overflow_64(results, oop, repr.signed, a, b),
            other => Err(WasmLowerError::UnsupportedInst(format!(
                "Overflow on a {other:?} carrier"
            ))),
        }
    }

    fn lower_overflow_64(
        &mut self,
        results: &[ValueId],
        oop: OverflowOp,
        signed: bool,
        a: u32,
        b: u32,
    ) -> Result<(), WasmLowerError> {
        let r = self.temp(ValType::I64);
        emit_local_get(&mut self.code, a);
        emit_local_get(&mut self.code, b);
        self.code.push(match oop {
            OverflowOp::AddOverflow => op::I64_ADD,
            OverflowOp::SubOverflow => op::I64_SUB,
            OverflowOp::MulOverflow => op::I64_MUL,
        });
        self.emit_local_set(r);
        match (oop, signed) {
            (OverflowOp::AddOverflow, false) => {
                emit_local_get(&mut self.code, r);
                emit_local_get(&mut self.code, a);
                self.code.push(op::I64_LT_U);
            }
            (OverflowOp::SubOverflow, false) => {
                emit_local_get(&mut self.code, a);
                emit_local_get(&mut self.code, b);
                self.code.push(op::I64_LT_U);
            }
            (OverflowOp::AddOverflow, true) => {
                // ((a ^ r) & (b ^ r)) < 0
                emit_local_get(&mut self.code, a);
                emit_local_get(&mut self.code, r);
                self.code.push(op::I64_XOR);
                emit_local_get(&mut self.code, b);
                emit_local_get(&mut self.code, r);
                self.code.push(op::I64_XOR);
                self.code.push(op::I64_AND);
                self.i64_const(0);
                self.code.push(op::I64_LT_S);
            }
            (OverflowOp::SubOverflow, true) => {
                // ((a ^ b) & (a ^ r)) < 0
                emit_local_get(&mut self.code, a);
                emit_local_get(&mut self.code, b);
                self.code.push(op::I64_XOR);
                emit_local_get(&mut self.code, a);
                emit_local_get(&mut self.code, r);
                self.code.push(op::I64_XOR);
                self.code.push(op::I64_AND);
                self.i64_const(0);
                self.code.push(op::I64_LT_S);
            }
            (OverflowOp::MulOverflow, false) => {
                // a != 0 && r / a != b — the division never runs when a == 0.
                emit_local_get(&mut self.code, a);
                self.code.push(op::I64_EQZ);
                self.code.push(op::IF);
                self.code.push(BLOCKTYPE_I32);
                emit_i32_const(&mut self.code, 0);
                self.code.push(op::ELSE);
                emit_local_get(&mut self.code, r);
                emit_local_get(&mut self.code, a);
                self.code.push(op::I64_DIV_U);
                emit_local_get(&mut self.code, b);
                self.code.push(op::I64_NE);
                self.code.push(op::END);
            }
            (OverflowOp::MulOverflow, true) => {
                // a == -1: overflow iff b == MIN (the one product that wraps).
                // a == 0: never. Otherwise r / a != b, where the division can
                // trap on neither a zero divisor nor MIN / -1.
                emit_local_get(&mut self.code, a);
                self.i64_const(-1);
                self.code.push(op::I64_EQ);
                self.code.push(op::IF);
                self.code.push(BLOCKTYPE_I32);
                emit_local_get(&mut self.code, b);
                self.i64_const(i64::MIN);
                self.code.push(op::I64_EQ);
                self.code.push(op::ELSE);
                emit_local_get(&mut self.code, a);
                self.code.push(op::I64_EQZ);
                self.code.push(op::IF);
                self.code.push(BLOCKTYPE_I32);
                emit_i32_const(&mut self.code, 0);
                self.code.push(op::ELSE);
                emit_local_get(&mut self.code, r);
                emit_local_get(&mut self.code, a);
                self.code.push(op::I64_DIV_S);
                emit_local_get(&mut self.code, b);
                self.code.push(op::I64_NE);
                self.code.push(op::END);
                self.code.push(op::END);
            }
        }
        self.set_result(results, 1)?;
        emit_local_get(&mut self.code, r);
        self.set_result(results, 0)
    }

    /// The bit intrinsics `CtLz`, `CtTz`, `BSwap`, `BitReverse`, leaving the
    /// result on the stack. `src` is the operand's local.
    pub(super) fn emit_bit_unop(
        &mut self,
        un: UnOp,
        ty: &Ty,
        src: u32,
    ) -> Result<(), WasmLowerError> {
        let repr = self.int_repr(ty)?;
        let bits = repr.bits;
        match repr.carrier {
            ValType::I32 => {
                self.emit_operand(src, Some(repr), Some(IntView::Unsigned))?;
                match un {
                    UnOp::CtLz => {
                        self.code.push(op::I32_CLZ);
                        if bits < 32 {
                            emit_i32_const(&mut self.code, (32 - bits) as i32);
                            self.code.push(op::I32_SUB);
                        }
                    }
                    UnOp::CtTz => {
                        if bits < 32 {
                            // Plant a bit just above the value so ctz(0) = bits.
                            emit_i32_const(&mut self.code, 1 << bits);
                            self.code.push(op::I32_OR);
                        }
                        self.code.push(op::I32_CTZ);
                    }
                    UnOp::BSwap => {
                        self.emit_bswap32()?;
                        if bits < 32 {
                            emit_i32_const(&mut self.code, (32 - bits) as i32);
                            self.code.push(op::I32_SHR_U);
                        }
                    }
                    UnOp::BitReverse => {
                        self.emit_bitreverse32()?;
                        if bits < 32 {
                            emit_i32_const(&mut self.code, (32 - bits) as i32);
                            self.code.push(op::I32_SHR_U);
                        }
                    }
                    other => {
                        return Err(WasmLowerError::UnsupportedInst(format!("UnOp::{other:?}")));
                    }
                }
            }
            ValType::I64 => {
                emit_local_get(&mut self.code, src);
                match un {
                    UnOp::CtLz => self.code.push(op::I64_CLZ),
                    UnOp::CtTz => self.code.push(op::I64_CTZ),
                    UnOp::BSwap | UnOp::BitReverse => {
                        // Swap the two 32-bit halves, each reversed.
                        let x = self.temp(ValType::I64);
                        self.emit_local_set(x);
                        emit_local_get(&mut self.code, x);
                        self.code.push(op::I32_WRAP_I64);
                        if un == UnOp::BSwap {
                            self.emit_bswap32()?;
                        } else {
                            self.emit_bitreverse32()?;
                        }
                        self.code.push(op::I64_EXTEND_I32_U);
                        self.i64_const(32);
                        self.code.push(op::I64_SHL);
                        emit_local_get(&mut self.code, x);
                        self.i64_const(32);
                        self.code.push(op::I64_SHR_U);
                        self.code.push(op::I32_WRAP_I64);
                        if un == UnOp::BSwap {
                            self.emit_bswap32()?;
                        } else {
                            self.emit_bitreverse32()?;
                        }
                        self.code.push(op::I64_EXTEND_I32_U);
                        self.code.push(op::I64_OR);
                    }
                    other => {
                        return Err(WasmLowerError::UnsupportedInst(format!("UnOp::{other:?}")));
                    }
                }
            }
            other => {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "UnOp::{un:?} on a {other:?} carrier"
                )));
            }
        }
        self.canonicalize_result(ty)
    }

    /// `[i32 x] -> [i32 bswap(x)]`: `rotr(x & 0x00ff00ff, 8) | rotl(x & 0xff00ff00, 8)`.
    fn emit_bswap32(&mut self) -> Result<(), WasmLowerError> {
        let x = self.temp(ValType::I32);
        self.emit_local_set(x);
        emit_local_get(&mut self.code, x);
        emit_i32_const(&mut self.code, 0x00ff_00ff);
        self.code.push(op::I32_AND);
        emit_i32_const(&mut self.code, 8);
        self.code.push(op::I32_ROTR);
        emit_local_get(&mut self.code, x);
        emit_i32_const(&mut self.code, 0xff00_ff00_u32 as i32);
        self.code.push(op::I32_AND);
        emit_i32_const(&mut self.code, 8);
        self.code.push(op::I32_ROTL);
        self.code.push(op::I32_OR);
        Ok(())
    }

    /// `[i32 x] -> [i32 reverse_bits(x)]`: swap adjacent bits, pairs and
    /// nibbles, then the bytes.
    fn emit_bitreverse32(&mut self) -> Result<(), WasmLowerError> {
        let x = self.temp(ValType::I32);
        for (shift, mask) in [(1, 0x5555_5555_u32), (2, 0x3333_3333), (4, 0x0f0f_0f0f)] {
            self.emit_local_set(x);
            // ((x >> s) & m) | ((x & m) << s)
            emit_local_get(&mut self.code, x);
            emit_i32_const(&mut self.code, shift);
            self.code.push(op::I32_SHR_U);
            emit_i32_const(&mut self.code, mask as i32);
            self.code.push(op::I32_AND);
            emit_local_get(&mut self.code, x);
            emit_i32_const(&mut self.code, mask as i32);
            self.code.push(op::I32_AND);
            emit_i32_const(&mut self.code, shift);
            self.code.push(op::I32_SHL);
            self.code.push(op::I32_OR);
        }
        self.emit_bswap32()
    }

    /// `RotL` / `RotR`: the amount is reduced modulo the value's width.
    pub(super) fn emit_rotate(
        &mut self,
        bin: BinOp,
        ty: &Ty,
        a: u32,
        b: u32,
    ) -> Result<(), WasmLowerError> {
        let repr = self.int_repr(ty)?;
        let left = bin == BinOp::RotL;
        if !repr.is_narrow() {
            emit_local_get(&mut self.code, a);
            emit_local_get(&mut self.code, b);
            self.code.push(match (repr.carrier, left) {
                (ValType::I32, true) => op::I32_ROTL,
                (ValType::I32, false) => op::I32_ROTR,
                (ValType::I64, true) => op::I64_ROTL,
                (ValType::I64, false) => op::I64_ROTR,
                (other, _) => {
                    return Err(WasmLowerError::UnsupportedInst(format!(
                        "BinOp::{bin:?} on a {other:?} carrier"
                    )));
                }
            });
            return Ok(());
        }
        // Narrow width w: k = b mod w; (x << k) | (x >> (w - k)) on the
        // zero-extended value (k = 0 shifts right by w < 32, giving 0).
        let w = repr.bits as i32;
        let k = self.temp(ValType::I32);
        self.emit_operand(b, Some(repr), Some(IntView::Unsigned))?;
        emit_i32_const(&mut self.code, w);
        self.code.push(op::I32_REM_U);
        self.emit_local_set(k);
        let x = self.temp(ValType::I32);
        self.emit_operand(a, Some(repr), Some(IntView::Unsigned))?;
        self.emit_local_set(x);
        let (first, second) = if left {
            (op::I32_SHL, op::I32_SHR_U)
        } else {
            (op::I32_SHR_U, op::I32_SHL)
        };
        emit_local_get(&mut self.code, x);
        emit_local_get(&mut self.code, k);
        self.code.push(first);
        emit_local_get(&mut self.code, x);
        emit_i32_const(&mut self.code, w);
        emit_local_get(&mut self.code, k);
        self.code.push(op::I32_SUB);
        self.code.push(second);
        self.code.push(op::I32_OR);
        self.emit_canonicalize(repr)
    }

    /// Float `FMin`/`FMax`/`FCopySign`/`FRem`, leaving the result on the stack.
    pub(super) fn emit_float_binop(
        &mut self,
        bin: BinOp,
        vt: ValType,
        a: u32,
        b: u32,
    ) -> Result<(), WasmLowerError> {
        let (ne, min, max, copysign) = match vt {
            ValType::F32 => (op::F32_NE, op::F32_MIN, op::F32_MAX, op::F32_COPYSIGN),
            ValType::F64 => (op::F64_NE, op::F64_MIN, op::F64_MAX, op::F64_COPYSIGN),
            other => {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "BinOp::{bin:?} on {other:?}"
                )));
            }
        };
        match bin {
            BinOp::FMin | BinOp::FMax => {
                // isnan(a) ? b : (isnan(b) ? a : f.min/max(a, b))
                emit_local_get(&mut self.code, b);
                emit_local_get(&mut self.code, a);
                emit_local_get(&mut self.code, a);
                emit_local_get(&mut self.code, b);
                self.code.push(if bin == BinOp::FMin { min } else { max });
                emit_local_get(&mut self.code, b);
                emit_local_get(&mut self.code, b);
                self.code.push(ne);
                self.code.push(op::SELECT);
                emit_local_get(&mut self.code, a);
                emit_local_get(&mut self.code, a);
                self.code.push(ne);
                self.code.push(op::SELECT);
            }
            BinOp::FCopySign => {
                emit_local_get(&mut self.code, a);
                emit_local_get(&mut self.code, b);
                self.code.push(copysign);
            }
            BinOp::FRem => {
                let helper = match vt {
                    ValType::F32 => self.helpers.fmodf,
                    _ => self.helpers.fmod,
                };
                let callee = helper.ok_or_else(|| {
                    WasmLowerError::UnsupportedInst(format!(
                        "FRem on {vt:?} in `{}`: no fmod helper was provisioned",
                        self.func.name
                    ))
                })?;
                emit_local_get(&mut self.code, a);
                emit_local_get(&mut self.code, b);
                self.emit_call(callee);
            }
            other => {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "BinOp::{other:?} on {vt:?}"
                )));
            }
        }
        Ok(())
    }

    /// `Select { ty, cond, then_val, else_val }`.
    pub(super) fn lower_select(
        &mut self,
        result: ValueId,
        cond: ValueId,
        then_val: ValueId,
        else_val: ValueId,
    ) -> Result<(), WasmLowerError> {
        let c = slot(&self.locals, cond)?.0;
        match self.carrier(result)? {
            Carrier::Void => Ok(()),
            Carrier::Pair => {
                // Half by half (`pair.rs` ties both operands to the result's
                // class, so both are pairs).
                let t = self.load_halves(then_val)?;
                let e = self.load_halves(else_val)?;
                let r = self.select128(c, t, e);
                self.store_halves(result, r)
            }
            Carrier::Scalar(_) | Carrier::Mem { .. } => {
                // A memory-carried select picks an ADDRESS (an alias).
                let t = slot(&self.locals, then_val)?.0;
                let e = slot(&self.locals, else_val)?.0;
                let d = slot(&self.locals, result)?.0;
                emit_local_get(&mut self.code, t);
                emit_local_get(&mut self.code, e);
                emit_local_get(&mut self.code, c);
                self.code.push(op::SELECT);
                self.emit_local_set(d);
                Ok(())
            }
        }
    }

    /// `Undef { ty }`: poison refines to any value; a scalar or a pair gets
    /// zero, a memory-carried value its (uninitialized) home slot.
    pub(super) fn lower_undef(&mut self, result: ValueId, ty: &Ty) -> Result<(), WasmLowerError> {
        match self.carrier(result)? {
            Carrier::Pair => self.const_pair(result, 0),
            Carrier::Scalar(vt) => {
                let d = slot(&self.locals, result)?.0;
                match vt {
                    ValType::F32 | ValType::F64 => self.emit_const(ty, &Constant::Float(0.0))?,
                    ValType::I64 => self.i64_const(0),
                    ValType::I32 => emit_i32_const(&mut self.code, 0),
                }
                self.emit_local_set(d);
                Ok(())
            }
            Carrier::Void | Carrier::Mem { .. } => Ok(()),
        }
    }

    /// `AtomicRMW`: `old = *p; *p = old <op> v; result = old`.
    pub(super) fn lower_atomic_rmw(
        &mut self,
        result: Option<ValueId>,
        rop: AtomicRMWOp,
        ty: &Ty,
        ptr: ValueId,
        value: ValueId,
    ) -> Result<(), WasmLowerError> {
        if super::wide::is_wide(ty) {
            return self.lower_wide_atomic_rmw(result, rop, ptr, value);
        }
        let repr = self.int_repr(ty)?;
        let p = slot(&self.locals, ptr)?.0;
        let v = slot(&self.locals, value)?.0;
        let old = self.temp(repr.carrier);
        emit_local_get(&mut self.code, p);
        self.emit_load(ty, 0)?;
        self.emit_local_set(old);
        emit_local_get(&mut self.code, p);
        let (i32_ops, i64_ops) = (
            (
                op::I32_ADD,
                op::I32_SUB,
                op::I32_AND,
                op::I32_OR,
                op::I32_XOR,
            ),
            (
                op::I64_ADD,
                op::I64_SUB,
                op::I64_AND,
                op::I64_OR,
                op::I64_XOR,
            ),
        );
        let (add, sub, and, or, xor) = if repr.carrier == ValType::I64 {
            i64_ops
        } else {
            i32_ops
        };
        match rop {
            AtomicRMWOp::Xchg => emit_local_get(&mut self.code, v),
            AtomicRMWOp::Add
            | AtomicRMWOp::Sub
            | AtomicRMWOp::And
            | AtomicRMWOp::Or
            | AtomicRMWOp::Xor => {
                emit_local_get(&mut self.code, old);
                emit_local_get(&mut self.code, v);
                self.code.push(match rop {
                    AtomicRMWOp::Add => add,
                    AtomicRMWOp::Sub => sub,
                    AtomicRMWOp::And => and,
                    AtomicRMWOp::Or => or,
                    _ => xor,
                });
                self.emit_canonicalize(repr)?;
            }
            AtomicRMWOp::Max | AtomicRMWOp::Min | AtomicRMWOp::UMax | AtomicRMWOp::UMin => {
                let cmp = super::carrier_predicate(
                    match rop {
                        AtomicRMWOp::Max => ICmpOp::Sgt,
                        AtomicRMWOp::Min => ICmpOp::Slt,
                        AtomicRMWOp::UMax => ICmpOp::Ugt,
                        _ => ICmpOp::Ult,
                    },
                    ty,
                );
                let opcode = super::icmp_opcode(cmp, repr.carrier)?;
                let view = super::icmp_operand_view(cmp);
                emit_local_get(&mut self.code, old);
                emit_local_get(&mut self.code, v);
                self.emit_operand(old, narrow_of(ty), view)?;
                self.emit_operand(v, narrow_of(ty), view)?;
                self.code.push(opcode);
                self.code.push(op::SELECT);
            }
        }
        self.emit_store(ty, 0)?;
        if let Some(r) = result {
            let d = slot(&self.locals, r)?.0;
            emit_local_get(&mut self.code, old);
            self.emit_local_set(d);
        }
        Ok(())
    }

    /// `CmpXchg` (strong, which also implements weak): results
    /// `(old, old == expected)`; `desired` is stored on success.
    pub(super) fn lower_cmpxchg(
        &mut self,
        results: &[ValueId],
        ty: &Ty,
        ptr: ValueId,
        expected: ValueId,
        desired: ValueId,
    ) -> Result<(), WasmLowerError> {
        if super::wide::is_wide(ty) {
            return self.lower_wide_cmpxchg(results, ptr, expected, desired);
        }
        let repr = self.int_repr(ty)?;
        let p = slot(&self.locals, ptr)?.0;
        let e = slot(&self.locals, expected)?.0;
        let n = slot(&self.locals, desired)?.0;
        let old = self.temp(repr.carrier);
        emit_local_get(&mut self.code, p);
        self.emit_load(ty, 0)?;
        self.emit_local_set(old);
        let ok = self.temp(ValType::I32);
        // Two canonical carriers are equal exactly when their values are.
        emit_local_get(&mut self.code, old);
        emit_local_get(&mut self.code, e);
        self.code.push(if repr.carrier == ValType::I64 {
            op::I64_EQ
        } else {
            op::I32_EQ
        });
        self.emit_local_set(ok);
        emit_local_get(&mut self.code, p);
        emit_local_get(&mut self.code, n);
        emit_local_get(&mut self.code, old);
        emit_local_get(&mut self.code, ok);
        self.code.push(op::SELECT);
        self.emit_store(ty, 0)?;
        emit_local_get(&mut self.code, ok);
        self.set_result(results, 1)?;
        emit_local_get(&mut self.code, old);
        self.set_result(results, 0)
    }

    /// Push a byte count operand as an i32 (a wider count wraps: a count past
    /// the wasm32 address space is out of bounds either way; see
    /// `emit_index_i32`).
    fn push_count(&mut self, bytes: ValueId) -> Result<(), WasmLowerError> {
        self.emit_index_i32(bytes, "bulk-memory byte count")
    }

    /// Bind the byte count of a bulk-memory op to a fresh local and open
    /// `if (n != 0)` around the op, returning that local.
    ///
    /// trust-ir defines a zero-byte `MemCopy` / `MemSet` as a no-op that does
    /// not touch either pointer, while wasm's `memory.copy` / `memory.fill`
    /// bounds-check `d + n` (and `s + n`) BEFORE looking at `n` and trap when
    /// that end lies past the memory even for `n == 0`. The guard keeps a
    /// zero-byte op on a dangling or out-of-memory pointer from trapping; a
    /// nonzero count reaches the op unchanged, so its own bounds check still
    /// traps on a range trust-ir makes UB. The caller emits the op and
    /// [`Self::close_bulk_guard`].
    fn open_bulk_guard(&mut self, bytes: ValueId) -> Result<u32, WasmLowerError> {
        self.push_count(bytes)?;
        let n = self.temp(ValType::I32);
        self.emit_local_set(n);
        emit_local_get(&mut self.code, n);
        self.code.push(op::IF);
        self.code.push(op::BLOCKTYPE_VOID);
        Ok(n)
    }

    /// Close the `if` opened by [`Self::open_bulk_guard`].
    fn close_bulk_guard(&mut self) {
        self.code.push(op::END);
    }

    /// The count of a `MemCopy` when, at O1 and above, it is defined by an
    /// integer constant in `1..=MAX_EXPANDED_COPY`: the copy is then emitted
    /// with that constant and without the zero-count guard, which a nonzero
    /// count always passes (the aggregate moves emit `memory.copy` the same
    /// way), so the emission pass can expand it into loads and stores
    /// (`wasm_local_tv`'s small-copy rule, the same 32-byte bound). `None`
    /// at O0, where every op keeps its guard and the O0 bytes are unchanged,
    /// and for any other count: a longer copy, which the emission pass never
    /// expands, keeps its guard, as every `MemSet` does (no emission rule
    /// expands `memory.fill`).
    fn small_copy_count(&self, bytes: ValueId) -> Option<i32> {
        if !self.unit_scale_elided {
            return None;
        }
        let mut found = None;
        for node in self.func.blocks.iter().flat_map(|b| &b.body) {
            if node.results.as_slice() == [bytes] {
                found = Some(&node.inst);
                break;
            }
        }
        match found? {
            trust_ir::Inst::Const {
                ty,
                value: Constant::Int(k),
            } if ty.is_integer() || matches!(ty, Ty::Usize | Ty::Isize) => u64::try_from(*k)
                .ok()
                .filter(|k| (1..=MAX_EXPANDED_COPY).contains(k))
                .and_then(|k| i32::try_from(k).ok()),
            _ => None,
        }
    }

    /// `MemCopy` → `memory.copy` under a nonzero-count guard (`memory.copy`
    /// is defined for overlap, so it implements both `memcpy` and `memmove`),
    /// or with its small constant count and no guard
    /// ([`Self::small_copy_count`]).
    pub(super) fn lower_memcopy(
        &mut self,
        dst: ValueId,
        src: ValueId,
        bytes: ValueId,
    ) -> Result<(), WasmLowerError> {
        let d = slot(&self.locals, dst)?.0;
        let s = slot(&self.locals, src)?.0;
        if let Some(k) = self.small_copy_count(bytes) {
            emit_local_get(&mut self.code, d);
            emit_local_get(&mut self.code, s);
            emit_i32_const(&mut self.code, k);
            self.emit_bulk(op::MEMORY_COPY);
            self.code.push(0x00);
            self.code.push(0x00);
            return Ok(());
        }
        let n = self.open_bulk_guard(bytes)?;
        emit_local_get(&mut self.code, d);
        emit_local_get(&mut self.code, s);
        emit_local_get(&mut self.code, n);
        self.emit_bulk(op::MEMORY_COPY);
        self.code.push(0x00);
        self.code.push(0x00);
        self.close_bulk_guard();
        Ok(())
    }

    /// `MemSet` → `memory.fill` under a nonzero-count guard.
    pub(super) fn lower_memset(
        &mut self,
        dst: ValueId,
        byte: ValueId,
        bytes: ValueId,
    ) -> Result<(), WasmLowerError> {
        let d = slot(&self.locals, dst)?.0;
        let v = slot(&self.locals, byte)?.0;
        let n = self.open_bulk_guard(bytes)?;
        emit_local_get(&mut self.code, d);
        emit_local_get(&mut self.code, v);
        emit_local_get(&mut self.code, n);
        self.emit_bulk(op::MEMORY_FILL);
        self.code.push(0x00);
        self.close_bulk_guard();
        Ok(())
    }
}
