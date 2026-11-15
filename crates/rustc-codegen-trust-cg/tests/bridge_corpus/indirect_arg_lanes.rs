// CORPUS FIXTURE — rustc's `PassMode::Indirect { on_stack: false }` ARGUMENT:
// every sized `Memory` value larger than a pointer (`{u32, u32, u32}`,
// `[u32; 3]`, `[u8; 16]`, 24- and 40-byte structs, a float struct that is not a
// `ScalarPair`, a `Memory` enum, a capturing closure environment) is passed as
// ONE POINTER to a copy the caller makes. Measured 2026-09-27: the bridge passed
// the bytes instead (register lanes up to 16 bytes, a `byval` stack copy above),
// so an LLVM caller of a bridge callee SIGSEGV'd and the other direction read
// wrong values. The indirect argument lane now passes the pointer. This
// whole-program fixture runs every call site through ONE backend, so it pins
// the bridge's own consistency across the call-site families the lane owns:
// direct calls, register exhaustion (the pointer in R9 with a scalar after it,
// and on the stack), an sret return beside an indirect argument, a callee that
// mutates its by-value parameter (the caller's original must be unchanged, for
// a `Copy` operand and a moved one), recursion, a closure body and a
// by-value closure environment, generic and `dyn` trait methods, a fn pointer,
// and const / `*p` operands. The cross-backend agreement is `m145`.
// EXPECTED EXIT CODE: 107 (LLVM oracle and the bridge at O0-O3).
#![no_std]
#![no_main]

use core::hint::black_box as bb;

#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[derive(Clone, Copy)]
struct T12 {
    a: u32,
    b: u32,
    c: u32,
}
#[derive(Clone, Copy)]
struct S24 {
    a: u64,
    b: u64,
    c: u64,
}
#[derive(Clone, Copy)]
struct S40 {
    a: u64,
    b: u32,
    c: u64,
    d: u16,
    e: u64,
}
#[derive(Clone, Copy)]
struct F3 {
    x: f32,
    y: f64,
    z: f32,
}
#[derive(Clone, Copy)]
enum E {
    A(u64, u64, u64),
    B(u32),
    C,
}
// Not `Copy`: the operand is a MOVE, which rustc passes as the moved-from place.
struct N12 {
    a: u32,
    b: u32,
    c: u32,
}

#[inline(never)]
fn t12(t: T12) -> u64 {
    t.a as u64 * 3 + t.b as u64 * 5 + t.c as u64 * 7
}
#[inline(never)]
fn arr3(t: [u32; 3], k: u64) -> u64 {
    t[0] as u64 * 3 + t[1] as u64 * 5 + t[2] as u64 * 7 + k * 11
}
#[inline(never)]
fn b16(b: [u8; 16]) -> u64 {
    b[0] as u64 + b[7] as u64 * 3 + b[15] as u64 * 5
}
#[inline(never)]
fn s24(s: S24) -> u64 {
    s.a * 3 + s.b * 5 + s.c * 7
}
#[inline(never)]
fn s40(s: S40) -> u64 {
    s.a * 3 + s.b as u64 * 5 + s.c * 7 + s.d as u64 * 11 + s.e * 13
}
#[inline(never)]
fn f3(f: F3, scale: f64) -> u64 {
    ((f.x as f64 * 2.0 + f.y * 3.0 + f.z as f64 * 5.0) * scale) as u64
}
#[inline(never)]
fn en(e: E) -> u64 {
    match e {
        E::A(a, b, c) => a * 3 + b * 5 + c * 7,
        E::B(x) => x as u64 * 11 + 1,
        E::C => 2,
    }
}
// Six integer arguments first: the pointer to the copy goes on the stack.
#[inline(never)]
fn exh6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, t: T12) -> u64 {
    a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + t12(t)
}
// Five first: the pointer takes R9 and the trailing scalar the stack.
#[inline(never)]
fn exh5(a: u64, b: u64, c: u64, d: u64, e: u64, t: T12, g: u64) -> u64 {
    a + b * 2 + c * 3 + d * 4 + e * 5 + t12(t) + g * 9
}
// The hidden return buffer (RDI) comes before the indirect pointer (RDX).
#[inline(never)]
fn sret_ind(k: u64, t: T12) -> S24 {
    S24 {
        a: k + t.a as u64,
        b: t.b as u64 * 2,
        c: t.c as u64 * 3,
    }
}
#[inline(never)]
fn mutate(mut t: T12) -> u64 {
    t.a += 100;
    t.b *= 3;
    t.c = t.a + t.b;
    t.c as u64
}
#[inline(never)]
fn mutate_n(mut n: N12) -> u64 {
    n.a += 1;
    n.b += n.a;
    n.c += n.b;
    n.c as u64
}
#[inline(never)]
fn rec(t: S24, n: u64) -> u64 {
    if n == 0 {
        t.a + t.b * 2 + t.c * 3
    } else {
        rec(
            S24 {
                a: t.b,
                b: t.c,
                c: t.a + n,
            },
            n - 1,
        )
    }
}
#[inline(never)]
fn apply<F: Fn(T12) -> u64>(f: F, t: T12) -> u64 {
    f(t)
}
#[inline(never)]
fn apply_env<F: FnOnce() -> u64>(f: F) -> u64 {
    f()
}
trait Sum12 {
    fn sum12(&self, t: T12) -> u64;
}
struct K(u64);
impl Sum12 for K {
    #[inline(never)]
    fn sum12(&self, t: T12) -> u64 {
        self.0 * 10 + t.a as u64 + t.b as u64 * 2 + t.c as u64 * 3
    }
}
#[inline(never)]
fn via_dyn(s: &dyn Sum12, t: T12) -> u64 {
    s.sum12(t)
}
#[inline(never)]
fn via_gen<S: Sum12>(s: &S, t: T12) -> u64 {
    s.sum12(t)
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let t = bb(T12 { a: 1, b: 2, c: 3 });
    let mut r = t12(t);
    r += arr3(bb([4, 5, 6]), bb(2));
    let mut bytes = [0u8; 16];
    bytes[0] = bb(9);
    bytes[7] = bb(4);
    bytes[15] = bb(2);
    r += b16(bb(bytes));
    r += s24(bb(S24 { a: 1, b: 2, c: 3 }));
    r += s40(bb(S40 {
        a: 1,
        b: 2,
        c: 3,
        d: 4,
        e: 5,
    }));
    r += f3(
        bb(F3 {
            x: 1.5,
            y: 2.0,
            z: 0.5,
        }),
        bb(2.0),
    );
    r += en(bb(E::A(1, 2, 3))) + en(bb(E::B(4))) + en(bb(E::C));
    r += exh6(bb(1), bb(1), bb(1), bb(1), bb(1), bb(1), t);
    r += exh5(bb(1), bb(1), bb(1), bb(1), bb(1), t, bb(2));
    let s = sret_ind(bb(5), t);
    r += s.a + s.b * 10 + s.c * 100;
    // The callee writes its copy; the caller's `t` must be unchanged after it.
    let m = mutate(t);
    r += m + t.a as u64 * 1000 + t.b as u64 * 100 + t.c as u64;
    let n = N12 {
        a: bb(1),
        b: bb(2),
        c: bb(3),
    };
    r += mutate_n(n);
    r += rec(bb(S24 { a: 1, b: 2, c: 3 }), bb(4));
    let k = bb(7u64);
    r += apply(move |x: T12| x.a as u64 * k + x.c as u64, t);
    let big = S24 {
        a: bb(3),
        b: 4,
        c: 5,
    };
    r += apply_env(move || big.a * 2 + big.b * 3 + big.c * 4);
    let kk = K(bb(4));
    r += via_dyn(&kk, t) + via_gen(&kk, t);
    let fp: fn(T12) -> u64 = bb(t12);
    r += fp(t);
    r += t12(T12 { a: 2, b: 2, c: 2 });
    let rt: &T12 = bb(&t);
    r += t12(*rt);
    (r % 251) as i32
}
