#![no_std]
mod types;
use types::{Outer, Pair};

macro_rules! operation {
    ($name:ident, $ty:ty, $op:tt) => {
        mod $name {
            use super::{Outer, Pair};
            unsafe extern "Rust" {
                #[link_name = concat!(stringify!($name), "_observe")]
                fn observe(value: &mut Outer<$ty>);
            }
            #[unsafe(export_name = concat!(stringify!($name), "_scalar"))]
            pub fn scalar(value: $ty) -> $ty { $op value }
            #[unsafe(export_name = concat!(stringify!($name), "_pair"))]
            pub fn pair(mut value: Pair<$ty>) -> Pair<$ty> {
                value.lo = $op value.lo;
                value.hi = $op value.hi;
                value
            }
            #[unsafe(export_name = concat!(stringify!($name), "_borrowed"))]
            pub fn borrowed(mut value: Outer<$ty>) -> Outer<$ty> {
                value.inner.lo = $op value.inner.lo;
                unsafe { observe(&mut value) };
                value.inner.hi = $op value.inner.hi;
                value
            }
            #[unsafe(export_name = concat!(stringify!($name), "_through"))]
            pub fn through(value: &mut Outer<$ty>) {
                value.inner.lo = $op value.inner.lo;
                value.inner.hi = $op value.inner.hi;
            }
        }
    };
}
operation!(not_u8, u8, !);
operation!(not_i8, i8, !);
operation!(not_u16, u16, !);
operation!(not_i16, i16, !);
operation!(not_u32, u32, !);
operation!(not_i32, i32, !);
operation!(not_u64, u64, !);
operation!(not_i64, i64, !);
operation!(not_u128, u128, !);
operation!(not_i128, i128, !);
operation!(neg_i8, i8, -);
operation!(neg_i16, i16, -);
operation!(neg_i32, i32, -);
operation!(neg_i64, i64, -);
operation!(neg_i128, i128, -);

unsafe extern "Rust" {
    fn take_small(value: Outer<u8>) -> u64;
    fn take_small_spilled(
        a: u64,
        b: u64,
        c: u64,
        d: u64,
        e: u64,
        f: u64,
        g: u64,
        h: u64,
        value: Outer<u8>,
    ) -> u64;
}
#[unsafe(no_mangle)]
pub fn small_calls(
    value: Outer<u8>,
    function: fn(Outer<u8>) -> u64,
    object: &dyn types::Observe,
) -> u64 {
    let direct = unsafe { take_small(value) };
    let indirect = function(value);
    let virtual_value = object.take(value);
    let spilled = unsafe { take_small_spilled(1, 2, 4, 8, 16, 32, 64, 128, value) };
    direct
        ^ indirect.rotate_left(7)
        ^ virtual_value.rotate_left(19)
        ^ spilled.rotate_left(31)
        ^ value.tail
        ^ value.lead as u64
        ^ (value.inner.hi as u64) << 8
        ^ (value.inner.lo as u64) << 16
}
#[unsafe(no_mangle)]
pub fn small_spilled(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    h: u64,
    mut value: Outer<u8>,
) -> u64 {
    value.inner.hi = !value.inner.hi;
    value.inner.lo = !value.inner.lo;
    a ^ b
        ^ c
        ^ d
        ^ e
        ^ f
        ^ g
        ^ h
        ^ value.tail
        ^ value.lead as u64
        ^ (value.inner.hi as u64) << 8
        ^ (value.inner.lo as u64) << 16
}
