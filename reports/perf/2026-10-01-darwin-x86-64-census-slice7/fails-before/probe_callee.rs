#![no_std]
pub struct Three { pub a: u64, pub b: u64, pub c: u64 }
#[inline(never)] pub fn make3(x: u64) -> Three { Three { a: x, b: x.wrapping_add(1), c: x.wrapping_mul(3) } }
#[inline(never)] pub fn sum3(x: u64) -> u64 { let t = make3(x); t.a.wrapping_add(t.b).wrapping_add(t.c) }
#[inline(never)] pub fn first3(x: u64) -> u64 { make3(x).b }
#[inline(never)] pub fn triple(x: u64) -> (u64, u64, u64) { (x, x ^ 5, x.wrapping_sub(2)) }
#[inline(never)] pub fn mid(x: u64) -> u64 { triple(x).1 }
#[inline(never)] pub fn opt(x: u64) -> Option<u64> { if x > 3 { Some(x) } else { None } }
#[inline(never)] pub fn opt_or(x: u64) -> u64 { match opt(x) { Some(v) => v, None => 9 } }
#[inline(never)] pub fn bump(p: &mut u64) { *p = p.wrapping_add(1); }
#[inline(never)] pub fn out_param(x: u64) -> u64 { let mut v = x; bump(&mut v); v }
#[inline(never)] pub fn twice_param(x: u64) -> u64 { let mut v = x; bump(&mut v); bump(&mut v); v }
#[inline(never)] pub fn peek(p: &u64) -> u64 { p.wrapping_mul(7) }
#[inline(never)] pub fn read_ref(x: u64) -> u64 { let v = x; peek(&v) }
#[inline(never)] pub fn fwd3(x: u64) -> Three { make3(x) }
#[inline(never)] pub fn branch_sret(c: bool, x: u64) -> u64 { if c { make3(x).c } else { x } }
