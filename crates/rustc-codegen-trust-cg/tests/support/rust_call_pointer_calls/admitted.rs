// `extern "rust-call"` shapes whose argument tuple places exactly like its
// elements: one scalar, two 8-byte integers, a `u8` before a `u64` (rustc does
// not extend the `u8`, so the callee reads only the low byte of the lane the
// bridge copies out of the tuple), one `&str`, nothing; and a method pointer
// with a receiver before the tuple. Calls through their pointers stay
// admitted, in both directions, and must match LLVM.
#![feature(unboxed_closures)]
#![allow(improper_ctypes_definitions)]

#[inline]
pub fn mx(h: u64, v: u64) -> u64 {
    (h ^ v).wrapping_mul(0x100000001b3).rotate_left(5)
}

#[inline(never)]
pub extern "rust-call" fn one(a: (u64,)) -> u64 {
    mx(a.0, 7)
}

#[inline(never)]
pub extern "rust-call" fn two(a: (u64, u64)) -> u64 {
    mx(a.0, a.1)
}

#[inline(never)]
pub extern "rust-call" fn narrow(a: (u8, u64)) -> u64 {
    mx(a.0 as u64, a.1)
}

#[inline(never)]
pub extern "rust-call" fn text(a: (&str,)) -> u64 {
    mx(a.0.len() as u64, a.0.as_bytes()[a.0.len() - 1] as u64)
}

#[inline(never)]
pub extern "rust-call" fn unit(_: ()) -> u64 {
    mx(7, 9)
}

pub struct S(pub u64);

impl S {
    #[inline(never)]
    pub extern "rust-call" fn m(&self, a: (u64, u64)) -> u64 {
        mx(two(a), self.0)
    }
}

#[inline(never)]
pub fn get_one() -> extern "rust-call" fn((u64,)) -> u64 {
    one
}

#[inline(never)]
pub fn get_two() -> extern "rust-call" fn((u64, u64)) -> u64 {
    two
}

#[inline(never)]
pub fn get_narrow() -> extern "rust-call" fn((u8, u64)) -> u64 {
    narrow
}

#[inline(never)]
pub fn get_text() -> extern "rust-call" fn((&str,)) -> u64 {
    text
}

#[inline(never)]
pub fn get_unit() -> extern "rust-call" fn(()) -> u64 {
    unit
}

#[inline(never)]
pub fn get_m() -> extern "rust-call" fn(&S, (u64, u64)) -> u64 {
    S::m
}

#[inline(never)]
pub fn call_two(f: extern "rust-call" fn((u64, u64)) -> u64, k: u64) -> u64 {
    f((k, k ^ 5))
}
