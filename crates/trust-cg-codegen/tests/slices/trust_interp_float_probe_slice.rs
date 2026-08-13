// ROUND 31 / TRUST BATCH 18 — FLOAT-LOWERING PROBE SLICE.
// Emit results (stage1 trust_ir_mir --mir-emit-closure, per root):
//   DIRECT float ops (p_fadd/p_fsub/p_fmul/p_fdiv/p_frem/p_flt/p_fle/p_feq/p_fne/
//     p_i642f/p_u642f/p_f2i64/p_f2u64/p_i1282f/p_f2i128/...): EMIT-FAIL
//     `place leaf is not a memory scalar: float` OR
//     `Rvalue::Cast source not a scalar leaf: float`.
//   INTRINSIC-METHOD float ops (p_isnan/p_fmin/p_fmax/p_fsqrt/p_ffloor/...):
//     EMIT-OK but as a HOLLOW F4 stub — f64 passed opaquely by-ref as `ptr`, the
//     op a BODYLESS extern leaf -> JIT LINK fails (UnresolvedSymbol).
//   p_int_ctrl (pure int control): EMIT-OK (proves the frontend works; floats are
//     the gap). scalar_tir_ty maps only Bool/Int/Uint (mir_lower.rs:116-137).

#![allow(dead_code)]
#![allow(unused_variables)]

#[no_mangle]
pub extern "C" fn p_fadd(a: f64, b: f64) -> f64 { a + b }
#[no_mangle]
pub extern "C" fn p_fsub(a: f64, b: f64) -> f64 { a - b }
#[no_mangle]
pub extern "C" fn p_fmul(a: f64, b: f64) -> f64 { a * b }
#[no_mangle]
pub extern "C" fn p_fdiv(a: f64, b: f64) -> f64 { a / b }
#[no_mangle]
pub extern "C" fn p_frem(a: f64, b: f64) -> f64 { a % b }
#[no_mangle]
pub extern "C" fn p_fmin(a: f64, b: f64) -> f64 { a.min(b) }
#[no_mangle]
pub extern "C" fn p_fmax(a: f64, b: f64) -> f64 { a.max(b) }
#[no_mangle]
pub extern "C" fn p_fneg(v: f64) -> f64 { -v }
#[no_mangle]
pub extern "C" fn p_fabs(v: f64) -> f64 { v.abs() }
#[no_mangle]
pub extern "C" fn p_fsqrt(v: f64) -> f64 { v.sqrt() }
#[no_mangle]
pub extern "C" fn p_ffloor(v: f64) -> f64 { v.floor() }
#[no_mangle]
pub extern "C" fn p_fceil(v: f64) -> f64 { v.ceil() }
#[no_mangle]
pub extern "C" fn p_ftrunc(v: f64) -> f64 { v.trunc() }
#[no_mangle]
pub extern "C" fn p_isnan(v: f64) -> u32 { v.is_nan() as u32 }
#[no_mangle]
pub extern "C" fn p_flt(a: f64, b: f64) -> u32 { (a < b) as u32 }
#[no_mangle]
pub extern "C" fn p_fle(a: f64, b: f64) -> u32 { (a <= b) as u32 }
#[no_mangle]
pub extern "C" fn p_feq(a: f64, b: f64) -> u32 { (a == b) as u32 }
#[no_mangle]
pub extern "C" fn p_fne(a: f64, b: f64) -> u32 { (a != b) as u32 }
#[no_mangle]
pub extern "C" fn p_f2i64(v: f64) -> i64 { v as i64 }
#[no_mangle]
pub extern "C" fn p_f2u64(v: f64) -> u64 { v as u64 }
#[no_mangle]
pub extern "C" fn p_i642f(v: i64) -> f64 { v as f64 }
#[no_mangle]
pub extern "C" fn p_u642f(v: u64) -> f64 { v as f64 }
#[no_mangle]
pub extern "C" fn p_f2i128(v: f64) -> i128 { v as i128 }
#[no_mangle]
pub extern "C" fn p_f2u128_i128(v: f64) -> i128 { v as u128 as i128 }
#[no_mangle]
pub extern "C" fn p_i1282f(v: i128) -> f64 { v as f64 }
#[no_mangle]
pub extern "C" fn p_i128u128_2f(v: i128) -> f64 { v as u128 as f64 }

// pure-int control (no float anywhere) — proves the frontend works; floats are the gap.
#[no_mangle]
pub extern "C" fn p_int_ctrl(a: i64, b: i64) -> i64 { a.wrapping_add(b) }
