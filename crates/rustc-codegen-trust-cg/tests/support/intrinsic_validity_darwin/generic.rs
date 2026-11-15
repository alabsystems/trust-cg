#![no_std]
#![feature(core_intrinsics)]
#![allow(internal_features)]
// Every validity intrinsic behind a generic `#[inline(never)]` wrapper: rustc's
// InstSimplify cannot fold an assert whose type is a parameter, and the MIR
// inliner may not inline the wrapper, so each instantiation below reaches the
// backend at every optimization level, valid ones included.
use core::{intrinsics, mem::MaybeUninit, num::NonZeroU64};

pub enum Empty {}

#[inline(never)]
fn zero_ok<T>() {
    intrinsics::assert_zero_valid::<T>()
}
#[inline(never)]
fn inhabited_ok<T>() {
    intrinsics::assert_inhabited::<T>()
}
#[inline(never)]
fn uninit_ok<T>() {
    intrinsics::assert_mem_uninitialized_valid::<T>()
}

#[unsafe(no_mangle)]
pub fn generic_valid(seed: u64) -> u64 {
    zero_ok::<[u64; 4]>();
    zero_ok::<Option<&'static u8>>();
    zero_ok::<MaybeUninit<&'static u8>>();
    zero_ok::<(u8, char, bool, *const u32, Option<NonZeroU64>)>();
    inhabited_ok::<&'static u8>();
    inhabited_ok::<u64>();
    uninit_ok::<MaybeUninit<&'static u8>>();
    uninit_ok::<[MaybeUninit<u64>; 3]>();
    seed.rotate_left(29) ^ 0x0f0e_0d0c_0b0a_0908
}

/// `bool` left uninitialized: valid without `-Zstrict-init-checks`, invalid
/// with it.
#[unsafe(no_mangle)]
pub fn generic_uninit_bool() {
    uninit_ok::<bool>()
}

#[unsafe(no_mangle)]
pub fn generic_invalid(case: u32) {
    match case {
        0 => zero_ok::<&'static u8>(),
        1 => zero_ok::<NonZeroU64>(),
        2 => inhabited_ok::<Empty>(),
        3 => uninit_ok::<&'static u8>(),
        4 => zero_ok::<fn(u64) -> u64>(),
        _ => unreachable!(),
    }
}
