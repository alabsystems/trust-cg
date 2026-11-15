// CORPUS FIXTURE — THE SCALAR SUB-LANE of rustc's `PassMode::Indirect {
// on_stack: false }` argument: an OVER-ALIGNED single-scalar newtype
// (`#[repr(C, align(16))] struct A16 { a: u64 }`, `#[repr(align(128))] struct
// CP(u64)`, `#[repr(align(16))] struct A8(u8)`, a padded `f64` / `bool` /
// `u128`) is ONE scalar to the bridge's type mapper but a padded `Memory` value
// to rustc, which passes it as a POINTER to a copy. Measured 2026-09-28 across a
// real boundary before the sub-lane: the bridge used the pointer register as the
// value (LLVM rlib + bridge bin SIGSEGV, the other direction silently wrong).
// This whole-program fixture runs every call site through ONE backend, so it
// pins the bridge's own consistency across the call-site families the sub-lane
// owns: direct calls, register exhaustion (the pointer in R9 with a scalar after
// it, and on the stack), a callee that writes its parameter (the caller's value
// must be unchanged), recursion, a `dyn` and a generic trait method, a fn
// pointer, a closure body called through the closure lane, a const operand, an
// alignment above the stack's (the copy's address is rounded up) and a 100
// 000-iteration loop of calls (the copies are frame slots; the stack must not
// grow). The newtypes are never passed through `black_box` whole: a padded
// scalar RETURN — which `black_box::<A16>` is — is refused by name
// (`[TCG-RET-ABI]`), not lowered. Left out because they fail closed before and
// after the sub-lane (`Place projection`, the loop-carried-local refusal): a
// newtype of such a newtype read through `o.0.a`, a borrowed parameter read
// through `&A16`, and a parameter mutated in a loop-headed body. The
// cross-backend agreement is `m145` (its `w1_*` rows).
// EXPECTED EXIT CODE: 7 (LLVM oracle at O0, O2 and O3; checked by hand:
// 965 + 20000500000 mod 997, mod 251).
#![no_std]
#![no_main]

use core::hint::black_box as bb;

#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[derive(Clone, Copy)]
#[repr(C, align(16))]
struct A16 {
    a: u64,
}
#[derive(Clone, Copy)]
#[repr(align(128))]
struct CP(u64);
#[derive(Clone, Copy)]
#[repr(align(16))]
struct A8(u8);
#[derive(Clone, Copy)]
#[repr(align(16))]
struct PF(f64);
#[derive(Clone, Copy)]
#[repr(align(32))]
struct W(u128);
#[derive(Clone, Copy)]
#[repr(align(16))]
struct B(bool);

#[inline(never)]
fn al(k: u64, a: A16, j: u64) -> u64 {
    k + a.a * 3 + j * 7
}
#[inline(never)]
fn cp(k: u64, c: CP, a: A8, j: u64) -> u64 {
    k + c.0 * 3 + a.0 as u64 * 5 + j * 7
}
#[inline(never)]
fn pf(x: f64, p: PF, y: f64) -> u64 {
    (x * 3.0 + p.0 * 5.0 + y * 7.0) as u64
}
#[inline(never)]
fn wide(w: W, k: u64) -> u64 {
    (w.0 as u64) ^ ((w.0 >> 64) as u64) ^ k
}
#[inline(never)]
fn flag(b: B, k: u64) -> u64 {
    if b.0 { k * 2 } else { k + 1 }
}
// Six integer arguments first: the pointer to the copy goes on the stack.
#[inline(never)]
fn exh6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, x: A16, g: u64) -> u64 {
    a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + x.a * 7 + g * 11
}
// Five first: the pointer takes R9 and the trailing scalar the stack.
#[inline(never)]
fn exh5(a: u64, b: u64, c: u64, d: u64, e: u64, x: A16, g: u64) -> u64 {
    a + b * 2 + c * 3 + d * 4 + e * 5 + x.a * 7 + g * 11
}
#[inline(never)]
fn bump(mut a: A16) -> u64 {
    a.a += 5;
    a.a * 2
}
#[inline(never)]
fn rec(a: A16, n: u64) -> u64 {
    if n == 0 {
        a.a
    } else {
        rec(A16 { a: a.a * 3 + n }, n - 1)
    }
}
trait TakeA16 {
    fn take(&self, a: A16) -> u64;
}
struct K(u64);
impl TakeA16 for K {
    #[inline(never)]
    fn take(&self, a: A16) -> u64 {
        self.0 * 10 + a.a * 3
    }
}
#[inline(never)]
fn via_dyn(s: &dyn TakeA16, a: A16) -> u64 {
    s.take(a)
}
#[inline(never)]
fn via_gen<S: TakeA16>(s: &S, a: A16) -> u64 {
    s.take(a)
}
#[inline(never)]
fn apply<F: Fn(A16) -> u64>(f: F, a: A16) -> u64 {
    f(a)
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut r = al(bb(3), A16 { a: bb(5) }, bb(7));
    r += cp(bb(1), CP(bb(2)), A8(bb(3)), bb(4));
    r += pf(bb(1.0), PF(bb(2.0)), bb(3.0));
    r += wide(W(bb((9u128 << 64) | 5)), bb(3));
    r += flag(B(bb(true)), bb(4)) + flag(B(bb(false)), bb(4));
    r += exh6(bb(1), bb(1), bb(1), bb(1), bb(1), bb(1), A16 { a: bb(2) }, bb(3));
    r += exh5(bb(1), bb(1), bb(1), bb(1), bb(1), A16 { a: bb(2) }, bb(3));
    let a = A16 { a: bb(4) };
    // The callee writes its copy; the caller's `a` must be unchanged after it.
    let m = bump(a);
    r += m + a.a * 100;
    r += rec(A16 { a: bb(1) }, bb(3));
    let k = K(bb(4));
    r += via_dyn(&k, a) + via_gen(&k, a);
    let f: fn(u64, A16, u64) -> u64 = bb(al);
    r += f(bb(1), a, bb(1));
    let kk = bb(6u64);
    r += apply(move |x: A16| x.a * kk + 1, a);
    r += al(1, A16 { a: 2 }, 3);
    let mut acc = 0u64;
    let mut i = 0u64;
    let n = bb(100_000u64);
    while i < n {
        acc = acc.wrapping_add(al(i, A16 { a: i ^ 5 }, 1));
        i += 1;
    }
    r += acc % 997;
    (r % 251) as i32
}
