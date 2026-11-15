// wide-numerics fixture: by-value `Option<u128>` / `Option<i128>` / `(u128, bool)` /
// `(u64, u128)` ARGUMENTS (rustc `PassMode::Pair` with a 128-bit INTEGER lane: four INTEGER
// eightbytes) at several register states, including exhaustion (the 128-bit lane goes wholly
// to the stack and a later u64 back-fills R9), plus core's own `Option<u128>::unwrap_unchecked`
// / `unwrap_or` (at -O0 share-generics may bind core's LLVM-built copy: a real boundary).
// Single-crate: both sides are one backend (the cross-backend matrix is kept with the design record).
// CORPUS FIXTURE. Correct exit = LLVM oracle (181 at O0/O2).
#![no_std]
#![no_main]
use core::hint::black_box as bb;
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
#[inline(never)] fn mix(acc: u64, v: u128) -> u64 { acc.wrapping_mul(1_000_003) ^ (v as u64) ^ ((v >> 64) as u64).rotate_left(13) }
#[inline(never)] fn o0(x: Option<u128>, z: u64) -> u64 { match x { Some(v) => mix(z, v), None => z ^ 0x55 } }
#[inline(never)] fn o3(a: u64, b: u64, c: u64, x: Option<u128>, z: u64) -> u64 { let s = z ^ a ^ b << 1 ^ c << 2; match x { Some(v) => mix(s, v), None => s ^ 0x55 } }
#[inline(never)] fn o5(a: u64, b: u64, c: u64, d: u64, e: u64, x: Option<u128>, z: u64) -> u64 { let s = z ^ a ^ b << 1 ^ c << 2 ^ d << 3 ^ e << 4; match x { Some(v) => mix(s, v), None => s ^ 0x55 } }
#[inline(never)] fn p1(a: u64, x: (u128, bool), z: u64) -> u64 { let s = z ^ a; if x.1 { mix(s, x.0) } else { s ^ 0x77 } }
#[inline(never)] fn p2(a: u64, b: u64, c: u64, d: u64, e: u64, x: (u64, u128), z: u64) -> u64 { mix(z ^ a ^ b << 1 ^ c << 2 ^ d << 3 ^ e << 4 ^ x.0, x.1) }
#[inline(never)] fn p3(x: Option<i128>, y: Option<u128>, z: u64) -> u64 { let s = match x { Some(v) => mix(z, v as u128), None => z ^ 0x11 }; match y { Some(v) => mix(s, v), None => s ^ 0x22 } }
#[inline(never)] fn p4(a: u64, b: u64, c: u64, d: u64, x: Option<u128>, z: u64) -> u64 { let s = z ^ a ^ b << 1 ^ c << 2 ^ d << 3; match x { Some(v) => mix(s, v), None => s ^ 0x55 } }
#[inline(never)] fn p6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, x: Option<u128>, z: u64) -> u64 { let s = z ^ a ^ b << 1 ^ c << 2 ^ d << 3 ^ e << 4 ^ f << 5; match x { Some(v) => mix(s, v), None => s ^ 0x55 } }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let x: u128 = bb(0x0123_4567_89ab_cdef_fedc_ba98_7654_3210);
    let mut s: u64 = 0;
    s = s.wrapping_mul(31) ^ o0(bb(Some(x)), bb(7));
    s = s.wrapping_mul(31) ^ o0(bb(None), bb(7));
    s = s.wrapping_mul(31) ^ o3(bb(1), bb(2), bb(3), bb(Some(x)), bb(7));
    s = s.wrapping_mul(31) ^ o5(bb(1), bb(2), bb(3), bb(4), bb(5), bb(Some(x)), bb(7));
    s = s.wrapping_mul(31) ^ o5(bb(1), bb(2), bb(3), bb(4), bb(5), bb(None), bb(7));
    s = s.wrapping_mul(31) ^ p1(bb(1), bb((x, true)), bb(7));
    s = s.wrapping_mul(31) ^ p1(bb(1), bb((x, false)), bb(7));
    s = s.wrapping_mul(31) ^ p2(bb(1), bb(2), bb(3), bb(4), bb(5), bb((9, x)), bb(7));
    s = s.wrapping_mul(31) ^ p3(bb(Some(-5)), bb(Some(x)), bb(7));
    s = s.wrapping_mul(31) ^ p3(bb(None), bb(None), bb(7));
    s = s.wrapping_mul(31) ^ p4(bb(1), bb(2), bb(3), bb(4), bb(Some(x)), bb(7));
    s = s.wrapping_mul(31) ^ p6(bb(1), bb(2), bb(3), bb(4), bb(5), bb(6), bb(Some(x)), bb(7));
    s = s.wrapping_mul(31) ^ p6(bb(1), bb(2), bb(3), bb(4), bb(5), bb(6), bb(None), bb(7));
    s = s.wrapping_mul(31) ^ (unsafe { bb(Some(x)).unwrap_unchecked() } as u64);
    s = s.wrapping_mul(31) ^ (bb(Some(x)).unwrap_or(3) >> 64) as u64;
    s = s.wrapping_mul(31) ^ (bb(None::<u128>).unwrap_or(3)) as u64;
    (s % 251) as i32
}
