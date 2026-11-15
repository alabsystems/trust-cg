// Trust-verified x86-64 corpus: every function strict-verifies (verification ON)
// AND emits reachable monomorphic code. Shapes: scalar ALU, struct, tuple, call,
// bounded loop, array, match, i32, bool, Option, bit-count, xorshift.
#[unsafe(no_mangle)] pub extern "C" fn t_add_wrapping(a: u32, b: u32) -> u32 { a.wrapping_add(b) }
#[unsafe(no_mangle)] pub extern "C" fn t_xor(a: u64, b: u64) -> u64 { a ^ b }
#[unsafe(no_mangle)] pub extern "C" fn t_shl_masked(a: u64, s: u32) -> u64 { a << (s & 63) }
#[unsafe(no_mangle)] pub extern "C" fn t_shr_masked(a: u64, s: u32) -> u64 { a >> (s & 63) }
#[unsafe(no_mangle)] pub extern "C" fn t_mul_wrapping(a: u64, b: u64) -> u64 { a.wrapping_mul(b) }
#[unsafe(no_mangle)] pub extern "C" fn t_xorshift(mut x: u64) -> u64 {
    x ^= x << 13; x ^= x >> 7; x ^= x << 17; x
}
#[unsafe(no_mangle)] pub extern "C" fn t_cond_select(a: u64, b: u64, f: u32) -> u64 {
    if f & 1 == 0 { a.wrapping_add(b) } else { a ^ b }
}

pub struct P { pub a: u64, pub b: u64 }
#[unsafe(no_mangle)] pub extern "C" fn s01(a: u64, b: u64) -> u64 { let p = P { a, b }; p.a ^ p.b }

#[unsafe(no_mangle)] pub extern "C" fn s02(a: u64, b: u64) -> u64 { let t = (a, b); t.0.wrapping_add(t.1) }

fn inner(x: u64) -> u64 { x ^ 0x5555 }
#[unsafe(no_mangle)] pub extern "C" fn s03(a: u64) -> u64 { inner(a).wrapping_mul(3) }

#[unsafe(no_mangle)] pub extern "C" fn s04(a: u64) -> u64 {
    let mut acc = a; let mut i = 0u32;
    while i < 8 { acc = acc.wrapping_mul(3).wrapping_add(i as u64); i += 1; }
    acc }

#[unsafe(no_mangle)] pub extern "C" fn s05(a: u64) -> u64 {
    let t: [u64; 4] = [a, a ^ 1, a ^ 2, a ^ 3];
    t[0] ^ t[1] ^ t[2] ^ t[3] }

#[unsafe(no_mangle)] pub extern "C" fn s06(a: u64, k: u32) -> u64 {
    match k & 3 { 0 => a.wrapping_add(1), 1 => a ^ 2, 2 => a.wrapping_mul(3), _ => a >> 1 } }

#[unsafe(no_mangle)] pub extern "C" fn s07(a: i32, b: i32) -> i32 { a.wrapping_sub(b) }

#[unsafe(no_mangle)] pub extern "C" fn s08(a: u64, b: u64) -> u32 { (a > b) as u32 }

#[unsafe(no_mangle)] pub extern "C" fn s09(a: u64, f: u32) -> u64 {
    let o = if f & 1 == 0 { Some(a) } else { None };
    match o { Some(v) => v ^ 7, None => 0 } }

#[unsafe(no_mangle)] pub extern "C" fn s10(a: u64) -> u64 {
    let mut x = a; x ^= x << 13; x ^= x >> 7; x ^= x << 17; x.count_ones() as u64 ^ x }


pub enum E { X(u64), Y(u32), Z }
#[unsafe(no_mangle)] pub extern "C" fn e01(v: u64, k: u32) -> u64 {
    let e = match k & 3 { 0 => E::X(v), 1 => E::Y(v as u32), _ => E::Z };
    match e { E::X(a) => a ^ 1, E::Y(b) => b as u64, E::Z => 7 } }

#[unsafe(no_mangle)] pub extern "C" fn f03(a: f64, b: f64) -> u32 { (a < b) as u32 }

fn pick<T: Copy>(a: T, b: T, f: bool) -> T { if f { a } else { b } }
#[unsafe(no_mangle)] pub extern "C" fn g02(a: u64, b: u64, f: u32) -> u64 { pick(a, b, f & 1 == 0) }

#[unsafe(no_mangle)] pub extern "C" fn i01(a: u64, b: u64) -> u64 {
    let w = (a as u128).wrapping_mul(b as u128); (w >> 64) as u64 ^ (w as u64) }

trait Op2 { fn go2(&self, x: u64) -> u64; }
struct C;
impl Op2 for C { fn go2(&self, x: u64) -> u64 { x >> 3 } }
#[unsafe(no_mangle)] pub extern "C" fn tr02(x: u64) -> u64 { C.go2(x) }

#[unsafe(no_mangle)] pub extern "C" fn u02(a: u32, b: u32) -> u32 { a.saturating_sub(b) }

