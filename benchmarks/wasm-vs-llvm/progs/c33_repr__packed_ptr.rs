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
#[repr(C, packed)]
#[derive(Clone, Copy)]
struct Pk {
    a: u8,
    x: f64,
    b: u16,
    y: f32,
}
#[repr(C)]
#[derive(Clone, Copy)]
struct Rc {
    a: u8,
    x: f64,
    y: f32,
    b: u16,
}
#[repr(C, align(16))]
#[derive(Clone, Copy)]
struct Al {
    y: f32,
    x: f64,
}
#[inline(never)]
fn mkpk(k: u32, x: f64) -> Pk {
    Pk {
        a: k as u8,
        x,
        b: (k >> 8) as u16,
        y: x as f32,
    }
}
#[inline(never)]
fn sumpk(p: Pk) -> f64 {
    let x = p.x;
    let y = p.y;
    let b = p.b;
    p.a as f64 + x * 2.0 + b as f64 * 3.0 + y as f64 * 4.0
}
#[inline(never)]
fn mkrc(k: u32, x: f64) -> Rc {
    Rc {
        a: k as u8,
        x,
        y: x as f32 * 0.5,
        b: k as u16,
    }
}
#[inline(never)]
fn sumrc(p: &Rc) -> f64 {
    p.a as f64 + p.x * 2.0 + p.b as f64 * 3.0 + p.y as f64 * 4.0
}
#[inline(never)]
fn sumal(p: Al) -> f64 {
    p.y as f64 * 3.0 - p.x
}
#[no_mangle]
pub extern "C" fn packed_ptr(k: u32, x: f64) -> u64 {
    let p = mkpk(k, x);
    let q = core::ptr::addr_of!(p.x);
    unsafe { q.read_unaligned().to_bits() }
}
