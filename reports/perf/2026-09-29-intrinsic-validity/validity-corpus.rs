#![no_std]
#![feature(core_intrinsics)]
#![allow(internal_features)]

use core::{intrinsics, mem::MaybeUninit, num::NonZeroU64};

pub enum Empty {}

#[unsafe(no_mangle)]
pub fn valid_checks(seed: u64) -> u64 {
    intrinsics::assert_zero_valid::<[u64; 4]>();
    intrinsics::assert_zero_valid::<[(u8, char, bool, *const u32, Option<NonZeroU64>); 3]>();
    intrinsics::assert_zero_valid::<Option<&'static u8>>();
    intrinsics::assert_zero_valid::<MaybeUninit<&'static u8>>();
    intrinsics::assert_inhabited::<&'static u8>();
    intrinsics::assert_mem_uninitialized_valid::<MaybeUninit<&'static u8>>();
    seed.rotate_left(17) ^ 0x1234567890abcdef
}

#[unsafe(no_mangle)]
pub fn zeroed_scalar() -> u64 { unsafe { core::mem::zeroed() } }
#[unsafe(no_mangle)]
pub fn zeroed_char() -> char { unsafe { core::mem::zeroed() } }
#[unsafe(no_mangle)]
pub fn zeroed_bool() -> bool { unsafe { core::mem::zeroed() } }
#[unsafe(no_mangle)]
pub fn zeroed_option() -> bool {
    let value: Option<NonZeroU64> = unsafe { core::mem::zeroed() };
    value.is_none()
}

#[unsafe(no_mangle)]
pub fn invalid_check(case: u32) {
    match case {
        0 => intrinsics::assert_zero_valid::<&'static u8>(),
        1 => intrinsics::assert_zero_valid::<NonZeroU64>(),
        2 => intrinsics::assert_zero_valid::<fn(u64) -> u64>(),
        3 => intrinsics::assert_inhabited::<Empty>(),
        4 => intrinsics::assert_zero_valid::<Empty>(),
        5 => intrinsics::assert_mem_uninitialized_valid::<&'static u8>(),
        _ => unreachable!(),
    }
}

#[unsafe(no_mangle)]
pub fn uninitialized_bool_policy() {
    intrinsics::assert_mem_uninitialized_valid::<bool>();
}
