#![no_std]
#![allow(dead_code)]
#![feature(core_float_math, float_minimum_maximum)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
#[derive(Clone, Copy)]
struct P2 {
    x: f32,
    y: f32,
}
#[derive(Clone, Copy)]
struct Pf {
    x: f32,
    t: u8,
}
#[inline(never)]
fn a1(v: [f32; 1]) -> [f32; 1] {
    [v[0] * 2.0 + 1.0]
}
#[inline(never)]
fn a2(v: [f32; 2]) -> [f32; 2] {
    [v[1] - 0.5, v[0] * 3.0]
}
#[inline(never)]
fn t2(v: (f32, f32)) -> (f32, f32) {
    (v.1 * v.0, v.0 - v.1)
}
#[inline(never)]
fn p2(v: P2) -> P2 {
    P2 {
        x: v.y + 1.0,
        y: -v.x,
    }
}
#[inline(never)]
fn pf(v: Pf) -> Pf {
    Pf {
        x: v.x * v.t as f32,
        t: v.t.wrapping_add(v.x as u8),
    }
}
#[inline(never)]
fn d2(v: (f64, f64)) -> (f64, f64) {
    (v.0 / v.1, v.1 % v.0)
}
#[inline(never)]
fn fd(v: (f32, f64)) -> (f64, f32) {
    (v.1 * 2.0, v.0 + 1.0)
}
#[inline(never)]
fn a3(v: [f32; 3]) -> [f32; 3] {
    [v[2], v[0] + v[1], v[1] * 0.25]
}
#[no_mangle]
pub extern "C" fn e_fd(x: f32, y: f64) -> f64 {
    let r = fd((x, y));
    r.0 + r.1 as f64 * 7.0
}
