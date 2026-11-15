#![no_std]
#![feature(try_trait_v2)]
use core::cmp::Ordering;
use core::convert::Infallible;
use core::ops::{ControlFlow, FromResidual};
#[unsafe(no_mangle)]
#[inline(never)]
pub fn residual_u64(r: ControlFlow<u64, Infallible>) -> ControlFlow<u64, u32> {
    FromResidual::from_residual(r)
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn residual_order(r: ControlFlow<Ordering, Infallible>) -> ControlFlow<Ordering, Ordering> {
    FromResidual::from_residual(r)
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn residual_unit(r: ControlFlow<(), Infallible>) -> ControlFlow<(), u64> {
    FromResidual::from_residual(r)
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn residual_ref(r: ControlFlow<&u64, Infallible>) -> ControlFlow<&u64, ()> {
    FromResidual::from_residual(r)
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn question_mark(value: u64, stop: bool) -> ControlFlow<u64, u64> {
    let value = if stop {
        ControlFlow::Break(value ^ 0x101)
    } else {
        ControlFlow::Continue(value)
    }?;
    ControlFlow::Continue(value.wrapping_add(7))
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn residual_nested(
    r: ControlFlow<ControlFlow<Ordering, Ordering>, Infallible>,
) -> ControlFlow<ControlFlow<Ordering, Ordering>, u64> {
    FromResidual::from_residual(r)
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn residual_mut(r: ControlFlow<&mut u64, Infallible>) -> ControlFlow<&mut u64, ()> {
    FromResidual::from_residual(r)
}
#[unsafe(no_mangle)]
pub extern "C" fn exercise(value: u64, mode: u32) -> u64 {
    let order = match value % 3 {
        0 => Ordering::Less,
        1 => Ordering::Equal,
        _ => Ordering::Greater,
    };
    match mode {
        0 => match residual_u64(ControlFlow::Break(value)) {
            ControlFlow::Break(x) => x,
            _ => !value,
        },
        1 => match residual_order(ControlFlow::Break(order)) {
            ControlFlow::Break(x) => x as i8 as u64,
            _ => 9,
        },
        2 => match residual_unit(ControlFlow::Break(())) {
            ControlFlow::Break(()) => 5,
            _ => 9,
        },
        3 => match residual_ref(ControlFlow::Break(&value)) {
            ControlFlow::Break(x) => *x,
            _ => !value,
        },
        4 | 5 => match question_mark(value, mode == 4) {
            ControlFlow::Break(x) => x,
            ControlFlow::Continue(x) => x,
        },
        6 => {
            let inner = if value & 1 == 0 {
                ControlFlow::Break(order)
            } else {
                ControlFlow::Continue(order)
            };
            match residual_nested(ControlFlow::Break(inner)) {
                ControlFlow::Break(ControlFlow::Break(x)) => x as i8 as u64,
                ControlFlow::Break(ControlFlow::Continue(x)) => (x as i8 as u64) ^ 0x42,
                _ => 9,
            }
        }
        7 => {
            let mut value = value;
            match residual_mut(ControlFlow::Break(&mut value)) {
                ControlFlow::Break(x) => *x = x.wrapping_add(9),
                _ => return 9,
            }
            value
        }
        _ => 0,
    }
}
