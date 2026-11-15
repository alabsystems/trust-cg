// CORPUS FIXTURE — the stack HOME of an over-aligned single-scalar newtype.
// `#[repr(C, align(16))] struct A16 { a: u64 }`, `#[repr(align(128))] struct
// CP(u64)` and `#[repr(align(16))] struct A8(u8)` are ONE scalar to the bridge's
// type mapper but padded `Memory` values to rustc, and a `&A16` is promised
// rustc's alignment and extent. Every stack home the bridge gives such a value
// used to be an `Alloca` of the scalar (8 or 1 bytes, scalar-aligned), so a
// reference to it was misaligned: measured 2026-09-28 (review finding, x86-64),
// a probe flagging a misaligned `&A16` gave 8 (none) for LLVM x LLVM and 15 with
// both sides bridge-built, and an LLVM `-O2` callee loading the promised 16
// aligned bytes SIGSEGV'd on a bridge local. Each flag below is one home: the
// temporary behind `&a` passed to a call (a local, a by-value parameter, an
// alignment above the stack's, a one-byte leaf), a raw-borrowed local's cell, a
// closure-captured local's cell, a `&dyn` data pointer, and a `&mut` temporary
// the callee writes through (its value must come back). Before, with the
// indirect argument lane but not this: O0 aborted on the `&*p` alignment check
// (134), O2 / O3 exited 70 (flags 174: by-value parameter, `CP`, `A8`, the
// closure cell and the `&mut` temporary misaligned). Left out because it fails
// closed before and after (`assignment destination projection is not
// scalar-bindable`): a field write `r.a = v` through the `&mut A16`. The
// cross-backend agreement is `m145` (its `w1_*_home_*` rows).
// EXPECTED EXIT CODE: 147 (LLVM oracle at O0, O2 and O3; checked by hand: no
// flag set, 5 * 16 + 2 * 32 + 3 = 147).
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

#[inline(never)]
fn mis16(r: &A16) -> u64 {
    (r as *const A16 as usize % 16 != 0) as u64
}
#[inline(never)]
fn mis_cp(r: &CP) -> u64 {
    (r as *const CP as usize % 128 != 0) as u64
}
#[inline(never)]
fn mis8(r: &A8) -> u64 {
    (r as *const A8 as usize % 16 != 0) as u64
}
#[inline(never)]
fn by_val(x: A16) -> u64 {
    mis16(&x)
}
#[inline(never)]
fn set16(r: &mut A16, v: u64) -> u64 {
    let m = mis16(r);
    *r = A16 { a: v };
    m
}
trait Addr {
    fn mis(&self) -> u64;
}
impl Addr for A16 {
    #[inline(never)]
    fn mis(&self) -> u64 {
        mis16(self)
    }
}
#[inline(never)]
fn via_dyn(d: &dyn Addr) -> u64 {
    d.mis()
}
#[inline(never)]
fn apply<F: Fn() -> u64>(f: F) -> u64 {
    f()
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a = A16 { a: bb(5) };
    let c = CP(bb(2));
    let e = A8(bb(3));
    let mut flags = mis16(&a);
    flags |= by_val(a) << 1;
    flags |= mis_cp(&c) << 2;
    flags |= mis8(&e) << 3;
    let b = A16 { a: bb(6) };
    let p = &raw const b;
    flags |= unsafe { mis16(&*p) } << 4;
    let d = A16 { a: bb(7) };
    flags |= apply(|| mis16(&d)) << 5;
    flags |= via_dyn(&a) << 6;
    let mut m = A16 { a: bb(1) };
    flags |= set16(&mut m, bb(3)) << 7;
    let r = flags + a.a * 16 + c.0 * 32 + m.a + e.0 as u64 * 0;
    (r % 251) as i32
}
