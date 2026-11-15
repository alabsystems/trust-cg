// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
#![no_std]

// The pointer-check MIR passes require an actual PanicImpl lang item. Import
// the same standard runtime that the LLVM driver links; a core-only rlib would
// contain unchecked pointer loads and could not qualify these assertion rows.
extern crate std;

unsafe extern "C" {
    fn assert_panic_record_drop(id: u64);
}

struct Guard(u64);

impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe { assert_panic_record_drop(self.0) }
    }
}

// These are source operations, not calls to panic helpers. Public, non-inlined
// required roots ensure the mixed driver executes the rlib's compiled bodies.
#[unsafe(no_mangle)]
#[track_caller]
#[inline(never)]
pub fn assert_add(lhs: u64, rhs: u64) -> u64 {
    let _guard = Guard(1);
    lhs + rhs
}

#[unsafe(no_mangle)]
#[track_caller]
#[inline(never)]
pub fn assert_sub(lhs: u64, rhs: u64) -> u64 {
    let _guard = Guard(2);
    lhs - rhs
}

#[unsafe(no_mangle)]
#[track_caller]
#[inline(never)]
pub fn assert_mul(lhs: u64, rhs: u64) -> u64 {
    let _guard = Guard(3);
    lhs * rhs
}

#[unsafe(no_mangle)]
#[track_caller]
#[inline(never)]
pub fn assert_div_overflow(lhs: i64, rhs: i64) -> u64 {
    let _guard = Guard(4);
    (lhs / rhs) as u64
}

#[unsafe(no_mangle)]
#[track_caller]
#[inline(never)]
pub fn assert_rem_overflow(lhs: i64, rhs: i64) -> u64 {
    let _guard = Guard(5);
    (lhs % rhs) as u64
}

#[unsafe(no_mangle)]
#[track_caller]
#[inline(never)]
pub fn assert_shl(lhs: u64, rhs: u32) -> u64 {
    let _guard = Guard(6);
    lhs << rhs
}

#[unsafe(no_mangle)]
#[track_caller]
#[inline(never)]
pub fn assert_shr(lhs: u64, rhs: u32) -> u64 {
    let _guard = Guard(7);
    lhs >> rhs
}

#[unsafe(no_mangle)]
#[track_caller]
#[inline(never)]
pub fn assert_neg(value: i64) -> u64 {
    let _guard = Guard(8);
    (-value) as u64
}

#[unsafe(no_mangle)]
#[track_caller]
#[inline(never)]
pub fn assert_div_zero(lhs: u64, rhs: u64) -> u64 {
    let _guard = Guard(9);
    lhs / rhs
}

#[unsafe(no_mangle)]
#[track_caller]
#[inline(never)]
pub fn assert_rem_zero(lhs: u64, rhs: u64) -> u64 {
    let _guard = Guard(10);
    lhs % rhs
}

#[unsafe(no_mangle)]
#[track_caller]
#[inline(never)]
pub fn assert_bounds(index: usize) -> u64 {
    let _guard = Guard(11);
    [10u64, 20, 30, 40][index]
}

#[unsafe(no_mangle)]
#[track_caller]
#[inline(never)]
pub unsafe fn assert_misaligned(pointer: *const u64) -> u64 {
    let _guard = Guard(12);
    unsafe { *pointer }
}

#[unsafe(no_mangle)]
#[track_caller]
#[inline(never)]
pub unsafe fn assert_null(pointer: *const u64) -> u64 {
    let _guard = Guard(13);
    unsafe { *pointer }
}

#[unsafe(no_mangle)]
#[track_caller]
#[inline(never)]
pub unsafe fn assert_null_reference(pointer: *const u8) -> u64 {
    let _guard = Guard(14);
    let reference = unsafe { &*pointer };
    u64::from(*reference)
}

#[unsafe(no_mangle)]
#[track_caller]
#[inline(never)]
pub fn assert_bounds_chain(index: usize) -> u64 {
    assert_bounds(index)
}

#[track_caller]
#[inline(always)]
fn inline_bounds(index: usize) -> u64 {
    [10u64, 20, 30, 40][index]
}

#[unsafe(no_mangle)]
#[track_caller]
#[inline(never)]
pub fn assert_inline_bounds(index: usize) -> u64 {
    let _guard = Guard(15);
    inline_bounds(index)
}

pub const SOURCE_FILE: &str = file!();
pub const PLAIN_DIV_LINE: u32 = line!() + 5;
#[unsafe(no_mangle)]
#[inline(never)]
pub fn assert_plain_div(lhs: u64, rhs: u64) -> u64 {
    let _guard = Guard(16);
    lhs / rhs
}
