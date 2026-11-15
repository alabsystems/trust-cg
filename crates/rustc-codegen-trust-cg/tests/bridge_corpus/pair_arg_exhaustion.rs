// CORPUS FIXTURE — a Rust-ABI `PassMode::Pair` ARGUMENT with EXACTLY ONE integer
// register left (five `u64`s before it: RDI..R8 taken, R9 free). rustc passes a
// `Pair` as two INDEPENDENT scalars (lane 0 in R9, lane 1 on the stack); a
// two-eightbyte AGGREGATE goes wholly to the stack. Measured 2026-09-23: the
// bridge declared the 16-byte slot as one aggregate, so a bridge callee read the
// pair from the wrong places whenever an LLVM-compiled caller passed it (and vice
// versa) — the slice family, `(u64, u64)`, `Range<usize>`, `Option<u64>` and a
// two-`u64` struct in both directions, `&str` / two slices / sret SIGSEGV. On
// x86-64 every `Pair` now rides the two-value lane. This whole-program fixture
// runs every call site through ONE backend, so it pins the bridge's own
// consistency across the shapes the lane now owns (direct call, fn pointer, a
// `&dyn` method, a trailing scalar after the pair, a const literal, a slice
// re-passed into a closure) plus the closure bodies, which keep the whole slot
// by structure. EXPECTED EXIT CODE: 23 (LLVM oracle and the bridge at O0-O3).
#![no_std]
#![no_main]

use core::hint::black_box as bb;
use core::ops::Range;
use core::ptr::NonNull;

#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

static A: [u8; 3] = [10, 20, 30];
static B: [u8; 5] = [1, 2, 3, 4, 5];

#[inline(never)]
fn s5(a: u64, b: u64, c: u64, d: u64, e: u64, s: &[u8]) -> u64 {
    a + b + c + d + e + s.len() as u64 * 100 + s[0] as u64
}
#[inline(never)]
fn t5(a: u64, b: u64, c: u64, d: u64, e: u64, t: &str) -> u64 {
    a + b + c + d + e + t.len() as u64 * 100 + t.as_bytes()[0] as u64
}
#[inline(never)]
fn trailing(a: u64, b: u64, c: u64, d: u64, e: u64, s: &[u8], g: u64) -> u64 {
    a + b + c + d + e + s.len() as u64 * 10 + g * 3
}
#[inline(never)]
fn two(a: u64, b: u64, c: u64, s: &[u8], t: &[u8]) -> u64 {
    a + b + c + s.len() as u64 * 10 + t.len() as u64 * 50 + t[0] as u64
}
#[inline(never)]
fn p5(a: u64, b: u64, c: u64, d: u64, e: u64, p: (u64, u64)) -> u64 {
    a + b + c + d + e + p.0 * 10 + p.1 * 100
}
#[inline(never)]
fn r5(a: u64, b: u64, c: u64, d: u64, e: u64, r: Range<usize>) -> u64 {
    a + b + c + d + e + r.start as u64 * 10 + r.end as u64 * 100
}
#[inline(never)]
fn o5(a: u64, b: u64, c: u64, d: u64, e: u64, o: Option<u64>) -> u64 {
    a + b + c + d + e
        + match o {
            Some(v) => v * 10,
            None => 7,
        }
}
#[inline(never)]
fn mk(s: &[u8]) -> NonNull<[u8]> {
    NonNull::from(s)
}
#[inline(never)]
fn n5(a: u64, b: u64, c: u64, d: u64, e: u64, p: NonNull<[u8]>) -> u64 {
    a + b + c + d + e + p.len() as u64 * 100
}
#[inline(never)]
fn repass(a: u64, b: u64, c: u64, d: u64, e: u64, s: &[u8]) -> u64 {
    let f = |x: &[u8]| x.len() as u64 + x[1] as u64;
    f(s) + a + b + c + d + e
}
trait Tk {
    fn m(&self, a: u64, b: u64, c: u64, d: u64, s: &[u8]) -> u64;
}
struct H(u64);
impl Tk for H {
    fn m(&self, a: u64, b: u64, c: u64, d: u64, s: &[u8]) -> u64 {
        self.0 + a + b + c + d + s.len() as u64 * 40
    }
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a: &[u8] = bb(&A[..]);
    let b: &[u8] = bb(&B[..]);
    let mut acc = 0u64;
    acc += s5(bb(1), bb(2), bb(3), bb(4), bb(5), a); // 15 + 300 + 10 = 325
    acc += t5(bb(1), bb(2), bb(3), bb(4), bb(5), bb("abc")); // 15 + 300 + 97 = 412
    acc += trailing(bb(1), bb(2), bb(3), bb(4), bb(5), b, bb(9)); // 15 + 50 + 27 = 92
    acc += two(bb(1), bb(2), bb(3), a, b); // 6 + 30 + 250 + 1 = 287
    acc += p5(bb(1), bb(2), bb(3), bb(4), bb(5), bb((6, 7))); // 15 + 60 + 700 = 775
    acc += r5(bb(1), bb(2), bb(3), bb(4), bb(5), bb(3..9)); // 15 + 30 + 900 = 945
    acc += o5(bb(1), bb(2), bb(3), bb(4), bb(5), bb(Some(8))); // 15 + 80 = 95
    acc += o5(bb(1), bb(1), bb(1), bb(1), bb(1), bb(None)); // 5 + 7 = 12
    acc += n5(bb(1), bb(2), bb(3), bb(4), bb(5), mk(b)); // 15 + 500 = 515
    acc += repass(bb(1), bb(2), bb(3), bb(4), bb(5), a); // 3 + 20 + 15 = 38
    let f: fn(u64, u64, u64, u64, u64, &[u8]) -> u64 = bb(s5);
    acc += f(bb(1), bb(2), bb(3), bb(4), bb(5), b); // 15 + 500 + 1 = 516
    let h = H(bb(50));
    let t: &dyn Tk = &h;
    acc += t.m(bb(1), bb(2), bb(3), bb(4), a); // 50 + 10 + 120 = 180
    acc += s5(bb(0), bb(0), bb(0), bb(0), bb(0), b"hi"); // 200 + 104 = 304
    let clo = |a: u64, b: u64, c: u64, d: u64, s: &[u8]| a + b + c + d + s.len() as u64 * 7;
    acc += clo(bb(1), bb(2), bb(3), bb(4), b); // 10 + 35 = 45
    (acc % 251) as i32
}
