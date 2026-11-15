// Closure bodies taking small by-value aggregates on wasm32.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// A capture-free closure called through `Option::map` / `map_or` is a
// `FnOnce` body whose zero-sized env rustc still lists as `FnAbi::args[0]`
// while this backend's declaration drops it, so each of its real parameters
// sits one position further along in rustc's `FnAbi`. A one-field struct and
// a fieldless enum are declared as one scalar; the wasm32 gate that compares
// that scalar with rustc's `FnAbi` once indexed the bridge's input list, so it
// compared the parameter with the closure env and refused every such closure
// (`[TCG-ARG-ABI] rustc's FnAbi argument 0 is Closure(..)`). Covered: a
// one-field struct, a fieldless enum, a two-field struct and a one-field
// newtype over `u64`, each through `map`, `map_or`, `and_then` and `filter`,
// a capturing closure (whose env is a real parameter) and a direct call of a
// closure value.
#![no_std]

// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=3 -Ccodegen-units=4

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[derive(Clone, Copy)]
struct Fx(i32);
#[derive(Clone, Copy)]
struct Wide(u64);
#[derive(Clone, Copy)]
struct Pair {
    a: i32,
    b: u16,
}
#[derive(Clone, Copy, PartialEq)]
enum Level {
    Low = 3,
    Mid = 70,
    High = 1000,
}

#[inline(never)]
fn mk_fx(v: i32) -> Option<Fx> {
    if v > 0 { Some(Fx(v)) } else { None }
}
#[inline(never)]
fn mk_wide(v: i64) -> Option<Wide> {
    if v & 1 == 0 {
        Some(Wide(v as u64))
    } else {
        None
    }
}
#[inline(never)]
fn mk_pair(v: i32) -> Option<Pair> {
    if v % 3 != 0 {
        Some(Pair {
            a: v,
            b: (v as u16) ^ 0x55,
        })
    } else {
        None
    }
}
#[inline(never)]
fn mk_level(v: i32) -> Option<Level> {
    match v.rem_euclid(4) {
        0 => Some(Level::Low),
        1 => Some(Level::Mid),
        2 => Some(Level::High),
        _ => None,
    }
}

#[inline(never)]
fn fx_map(o: Option<Fx>) -> i64 {
    o.map(|x| x.0 as i64 * 3).unwrap_or(-1)
}
#[inline(never)]
fn fx_map_or(o: Option<Fx>) -> i32 {
    o.map_or(-7, |x| x.0 ^ 0x1234)
}
#[inline(never)]
fn fx_and_then(o: Option<Fx>) -> i32 {
    o.and_then(|x| if x.0 % 5 == 0 { None } else { Some(x.0 + 1) })
        .unwrap_or(-3)
}
#[inline(never)]
fn fx_filter(o: Option<Fx>) -> i32 {
    o.filter(|x| x.0 & 2 != 0).map_or(-9, |x| x.0)
}
#[inline(never)]
fn wide_map(o: Option<Wide>) -> u64 {
    o.map(|w| w.0.rotate_left(7)).unwrap_or(5)
}
#[inline(never)]
fn wide_map_or(o: Option<Wide>) -> u64 {
    o.map_or(11, |w| w.0 ^ 0xffff_0000_ffff)
}
#[inline(never)]
fn pair_map(o: Option<Pair>) -> i64 {
    o.map(|p| p.a as i64 * 7 + p.b as i64).unwrap_or(-2)
}
#[inline(never)]
fn pair_map_or(o: Option<Pair>) -> i32 {
    o.map_or(-4, |p| p.a ^ i32::from(p.b))
}
#[inline(never)]
fn pair_and_then(o: Option<Pair>) -> i32 {
    o.and_then(|p| if p.b & 1 == 0 { Some(p.a) } else { None })
        .unwrap_or(-6)
}
#[inline(never)]
fn level_map(o: Option<Level>) -> i64 {
    o.map(|l| l as i64 * 2).unwrap_or(-1)
}
#[inline(never)]
fn level_map_or(o: Option<Level>) -> i32 {
    o.map_or(-7, |l| l as i32)
}
#[inline(never)]
fn level_and_then(o: Option<Level>) -> i32 {
    o.and_then(|l| {
        if l == Level::Mid {
            None
        } else {
            Some(l as i32 + 1)
        }
    })
    .unwrap_or(-5)
}
#[inline(never)]
fn level_filter(o: Option<Level>) -> i32 {
    o.filter(|l| *l != Level::High).map_or(-8, |l| l as i32)
}
/// A capturing closure: its env is a real parameter on both sides.
#[inline(never)]
fn fx_capture(o: Option<Fx>, k: i32) -> i32 {
    o.map(|x| x.0.wrapping_mul(k)).unwrap_or(k)
}
#[inline(never)]
fn level_capture(o: Option<Level>, k: i32) -> i32 {
    o.map_or(k, |l| (l as i32) ^ k)
}
/// A direct call of a closure value taking each shape.
#[inline(never)]
fn direct(v: i32) -> i64 {
    let f = |x: Fx| x.0 as i64 + 1;
    let g = |l: Level| l as i64 * 3;
    let h = |p: Pair| p.a as i64 - p.b as i64;
    let w = |x: Wide| x.0 as i64 ^ 0x77;
    let l = match v & 3 {
        0 => Level::Low,
        1 => Level::Mid,
        _ => Level::High,
    };
    f(Fx(v)) ^ g(l) ^ h(Pair { a: v, b: v as u16 }) ^ w(Wide(v as u64))
}

#[no_mangle]
pub extern "C" fn cl_fx(v: i32) -> i64 {
    let o = mk_fx(v);
    fx_map(o)
        ^ i64::from(fx_map_or(o)) << 8
        ^ i64::from(fx_and_then(o)) << 20
        ^ i64::from(fx_filter(o)) << 40
}
#[no_mangle]
pub extern "C" fn cl_wide(v: i64) -> u64 {
    let o = mk_wide(v);
    wide_map(o) ^ wide_map_or(o).rotate_left(32)
}
#[no_mangle]
pub extern "C" fn cl_pair(v: i32) -> i64 {
    let o = mk_pair(v);
    pair_map(o) ^ i64::from(pair_map_or(o)) << 16 ^ i64::from(pair_and_then(o)) << 40
}
#[no_mangle]
pub extern "C" fn cl_level(v: i32) -> i64 {
    let o = mk_level(v);
    level_map(o)
        ^ i64::from(level_map_or(o)) << 12
        ^ i64::from(level_and_then(o)) << 28
        ^ i64::from(level_filter(o)) << 44
}
#[no_mangle]
pub extern "C" fn cl_capture(v: i32, k: i32) -> i64 {
    i64::from(fx_capture(mk_fx(v), k)) ^ i64::from(level_capture(mk_level(v), k)) << 32
}
#[no_mangle]
pub extern "C" fn cl_direct(v: i32) -> i64 {
    direct(v)
}
