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
#[inline(never)]
fn live_step(value: u64, add: u64) -> ControlFlow<Never, u64> {
    let next = only_continue(value)?;
    ControlFlow::Continue(next.wrapping_mul(3).wrapping_add(add))
}
#[unsafe(no_mangle)]
pub extern "C" fn live_path(mut value: u64) -> u64 {
    let mut i = 0;
    while i < 4 {
        value = match live_step(value, i) {
            ControlFlow::Continue(v) => v,
            ControlFlow::Break(n) => match n {},
        };
        i += 1;
    }
    value
}
#[inline(never)]
fn option_never(value: Option<Never>, n: u64) -> u64 {
    match value {
        None => n.wrapping_add(11),
        Some(never) => match never {},
    }
}
#[inline(never)]
fn uninit_never(_value: core::mem::MaybeUninit<Never>, n: u64) -> u64 {
    n.wrapping_add(13)
}
#[inline(never)]
fn empty_never_array(_value: [Never; 0], n: u64) -> u64 {
    n.wrapping_add(17)
}
#[unsafe(no_mangle)]
pub extern "C" fn inhabited_zsts(value: u64) -> u64 {
    let value = option_never(None, value);
    let value = uninit_never(core::mem::MaybeUninit::uninit(), value);
    empty_never_array([], value)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn impossible_tuple(value: (u64, Never)) -> u64 {
    match value.1 {}
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn impossible_array(value: [Never; 1]) -> u64 {
    match value[0] {}
}
#[repr(C)]
#[derive(Clone, Copy)]
pub union EmptyUnion {
    pub unit: (),
    pub empty: [u8; 0],
}
#[inline(never)]
fn live_union(value: EmptyUnion, n: u64) -> u64 {
    let _ = unsafe { value.unit };
    n.wrapping_add(19)
}
#[inline(never)]
fn live_option(value: Option<Never>, n: u64) -> u64 {
    if value.is_none() {
        n.wrapping_add(23)
    } else {
        n
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn more_inhabited(value: u64) -> u64 {
    live_array(
        [(); 3],
        live_option(None, live_union(EmptyUnion { unit: () }, value)),
    )
}

#[inline(never)]
fn live_array(value: [(); 3], n: u64) -> u64 {
    let _ = value[2];
    n.wrapping_add(29)
}
#[inline(never)]
fn live_tagged(value: &Option<u64>) -> u64 {
    match value {
        None => 7,
        Some(n) => n.wrapping_add(31),
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn tagged_neighbor(n: u64) -> u64 {
    let value = if n & 1 == 0 { None } else { Some(n) };
    live_tagged(&value)
}
