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
use core::ops::{Add, Mul, Neg, Sub};
#[derive(Clone, Copy, PartialEq)]
struct V3 {
    x: f32,
    y: f32,
    z: f32,
}
impl Add for V3 {
    type Output = V3;
    fn add(self, o: V3) -> V3 {
        V3 {
            x: self.x + o.x,
            y: self.y + o.y,
            z: self.z + o.z,
        }
    }
}
impl Sub for V3 {
    type Output = V3;
    fn sub(self, o: V3) -> V3 {
        V3 {
            x: self.x - o.x,
            y: self.y - o.y,
            z: self.z - o.z,
        }
    }
}
impl Mul<f32> for V3 {
    type Output = V3;
    fn mul(self, k: f32) -> V3 {
        V3 {
            x: self.x * k,
            y: self.y * k,
            z: self.z * k,
        }
    }
}
impl Neg for V3 {
    type Output = V3;
    fn neg(self) -> V3 {
        V3 {
            x: -self.x,
            y: -self.y,
            z: -self.z,
        }
    }
}
#[inline(never)]
fn dot(a: V3, b: V3) -> f32 {
    a.x * b.x + a.y * b.y + a.z * b.z
}
#[inline(never)]
fn cross(a: &V3, b: &V3) -> V3 {
    V3 {
        x: a.y * b.z - a.z * b.y,
        y: a.z * b.x - a.x * b.z,
        z: a.x * b.y - a.y * b.x,
    }
}
#[no_mangle]
pub extern "C" fn v_eq(a: f32, b: f32) -> u32 {
    let u = V3 { x: a, y: b, z: 1.0 };
    let v = V3 { x: a, y: b, z: 1.0 };
    (u == v) as u32 + 2 * ((u * 0.5 == v * 0.5) as u32)
}
#[derive(Clone, Copy)]
struct V2d {
    x: f64,
    y: f64,
}
#[inline(never)]
fn len2(v: &V2d) -> f64 {
    v.x * v.x + v.y * v.y
}
