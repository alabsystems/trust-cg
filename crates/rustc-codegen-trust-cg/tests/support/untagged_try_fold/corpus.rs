#![no_std]
#![feature(try_trait_v2)]
use core::convert::Infallible;
use core::ops::{ControlFlow, FromResidual};
pub enum Never {}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn impossible(value: ControlFlow<Never, Infallible>) -> ControlFlow<Never, u64> {
    FromResidual::from_residual(value)
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn empty_match(value: ControlFlow<Never, Infallible>) -> u64 {
    match value {
        ControlFlow::Break(n) => match n {},
        ControlFlow::Continue(n) => match n {},
    }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn never_direct(value: Never) -> u64 {
    match value {}
}
#[inline(never)]
fn only_continue(value: u64) -> ControlFlow<Never, u64> {
    ControlFlow::Continue(value)
}
#[unsafe(no_mangle)]
pub extern "C" fn live_path(value: u64) -> u64 {
    let result: ControlFlow<Never, u64> = (0..4_u64).try_fold(value, |sum, i| {
        let next = only_continue(sum.wrapping_mul(3).wrapping_add(i))?;
        ControlFlow::Continue(next)
    });
    match result {
        ControlFlow::Continue(v) => v,
        ControlFlow::Break(n) => match n {},
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn drain_path(
    value: u64,
    count: u32,
    cursor: *mut u64,
    calls: *mut u64,
) -> u64 {
    let mut iter = 0..u64::from(count);
    let factor = (value & 3) + 1;
    let mut seen = 0_u64;
    let result: ControlFlow<Never, u64> = iter.try_fold(value, |sum, item| {
        seen = seen.wrapping_add(1);
        ControlFlow::Continue(sum.wrapping_mul(factor).wrapping_add(item))
    });
    let first = match result {
        ControlFlow::Continue(v) => v,
        ControlFlow::Break(n) => match n {},
    };
    let again: ControlFlow<Never, u64> = iter.try_fold(first ^ 0x123, |sum, item| {
        seen = seen.wrapping_add(1);
        ControlFlow::Continue(sum.wrapping_add(item))
    });
    unsafe {
        *cursor = iter.start;
        *calls = seen;
    }
    match again {
        ControlFlow::Continue(v) => v,
        ControlFlow::Break(n) => match n {},
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn narrow_path(value: u64, count: u32, mode: u32) -> u64 {
    match mode {
        0 => {
            let result: ControlFlow<Never, u8> = (0..count as u8)
                .try_fold(value as u8, |sum, i| {
                    ControlFlow::Continue(sum.wrapping_mul(3).wrapping_add(i))
                });
            match result {
                ControlFlow::Continue(v) => u64::from(v),
                ControlFlow::Break(n) => match n {},
            }
        }
        1 => {
            let result: ControlFlow<Never, u32> = (0..count).try_fold(value as u32, |sum, i| {
                ControlFlow::Continue(sum.wrapping_mul(3).wrapping_add(i))
            });
            match result {
                ControlFlow::Continue(v) => u64::from(v),
                ControlFlow::Break(n) => match n {},
            }
        }
        _ => {
            let result: ControlFlow<Never, i64> = (0..i64::from(count))
                .try_fold(value as i64, |sum, i| {
                    ControlFlow::Continue(sum.wrapping_mul(3).wrapping_add(i))
                });
            match result {
                ControlFlow::Continue(v) => v as u64,
                ControlFlow::Break(n) => match n {},
            }
        }
    }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn tagged_path(value: u64, count: u32, cursor: *mut u64) -> u64 {
    let mut iter = 0..u64::from(count);
    let result: ControlFlow<u64, u64> = iter.try_fold(value, |sum, i| {
        if i == 2 {
            ControlFlow::Break(sum)
        } else {
            ControlFlow::Continue(sum.wrapping_mul(3).wrapping_add(i))
        }
    });
    unsafe {
        *cursor = iter.start;
    }
    match result {
        ControlFlow::Continue(v) => v ^ 0xaa,
        ControlFlow::Break(v) => v ^ 0x55,
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn tagged_narrow_path(
    value: u64,
    count: u32,
    mode: u32,
    cursor: *mut u64,
) -> u64 {
    if mode == 0 {
        let mut iter = 0..count as u8;
        let result: ControlFlow<u8, u8> = iter.try_fold(value as u8, |sum, i| {
            if i == 2 {
                ControlFlow::Break(sum)
            } else {
                ControlFlow::Continue(sum.wrapping_mul(3).wrapping_add(i))
            }
        });
        unsafe {
            *cursor = u64::from(iter.start);
        }
        match result {
            ControlFlow::Continue(v) => u64::from(v) ^ 0xaa,
            ControlFlow::Break(v) => u64::from(v) ^ 0x55,
        }
    } else {
        let mut iter = 0..count;
        let result: ControlFlow<u32, u32> = iter.try_fold(value as u32, |sum, i| {
            if i == 2 {
                ControlFlow::Break(sum)
            } else {
                ControlFlow::Continue(sum.wrapping_mul(3).wrapping_add(i))
            }
        });
        unsafe {
            *cursor = u64::from(iter.start);
        }
        match result {
            ControlFlow::Continue(v) => u64::from(v) ^ 0xaa,
            ControlFlow::Break(v) => u64::from(v) ^ 0x55,
        }
    }
}
