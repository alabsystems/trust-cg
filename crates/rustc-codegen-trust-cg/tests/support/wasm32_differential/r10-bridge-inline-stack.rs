// The wasm32 mid-end's inliner and the stack, compiled with optimization.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// * `leaf` holds a 16 KiB buffer and is called only at the base of the
//   recursive `walk`. A spliced slot is part of the caller's frame for its
//   whole activation, so inlining `leaf` into `walk` would make every level
//   hold the buffer and `deep(n)` overflow the 1 MiB stack from `n` near 64,
//   where LLVM's module returns a value. The inliner splices no allocating
//   callee into a caller on a cycle of direct calls.
// * `fill` holds a 2 KiB buffer, past the bound on the slots spliced into
//   one caller, and is called from `twice` at two sites; with rustc's MIR
//   inliner off (the last configuration) both stay calls of this backend.
// * `slow_path` is `#[cold]` (the bridge's side table keeps it a call) and
//   `init` writes `pair`'s slot through an out-pointer and is spliced: their
//   values are LLVM's too.
#![no_std]

// wasm32-differential-flags: -Copt-level=1
// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=3 -Ccodegen-units=4
// wasm32-differential-flags: -Copt-level=2 -Zinline-mir=no

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

fn leaf(x: u32) -> u32 {
    let mut buf = [0u32; 4096];
    let p = buf.as_mut_ptr();
    unsafe {
        let mut h = x;
        h = h.wrapping_mul(0x85eb_ca6b) ^ (h >> 13);
        *p.add((h as usize) & 4095) = h;
        h = h.wrapping_mul(0xc2b2_ae35) ^ (h >> 16);
        *p.add((h as usize) & 4095) ^= x;
        h = h.wrapping_mul(0x27d4_eb2f) ^ (h >> 15);
        *p.add((h as usize) & 4095) = h ^ 3;
        let a = *p.add((x as usize) & 4095);
        let b = *p.add((x.wrapping_mul(2_654_435_761) as usize) & 4095);
        a ^ b.rotate_left(3) ^ h
    }
}

fn walk(n: u32, x: u32) -> u32 {
    if n == 0 {
        leaf(x)
    } else {
        let r = walk(n - 1, x ^ n);
        r.rotate_left(n & 7) ^ n.wrapping_mul(0x9e37)
    }
}

#[no_mangle]
pub extern "C" fn deep(n: i32, x: i32) -> i32 {
    walk((n as u32) & 255, x as u32) as i32
}

fn fill(x: u32, k: u32) -> u32 {
    let mut buf = [0u32; 512];
    let p = buf.as_mut_ptr();
    unsafe {
        *p.add((x as usize) & 511) = k;
        *p.add((k as usize) & 511) ^= x.rotate_left(7);
        *p.add((x as usize) & 511) ^ *p.add((k.wrapping_add(x) as usize) & 511)
    }
}

#[no_mangle]
pub extern "C" fn twice(x: i32, k: i32) -> i32 {
    let (x, k) = (x as u32, k as u32);
    (fill(x, k) ^ fill(k, x).rotate_left(11)) as i32
}

#[cold]
fn slow_path(x: u32) -> u32 {
    x.wrapping_mul(0x9e37_79b9).rotate_left(13) ^ 0xdead_beef
}

#[no_mangle]
pub extern "C" fn e_cold(x: i32) -> i32 {
    let x = x as u32;
    (if x > 1000 { slow_path(x) } else { x + 1 }) as i32
}

fn init(out: &mut [u32; 2], a: u32, b: u32) {
    out[0] = a.wrapping_add(b);
    out[1] = a ^ b.rotate_left(5);
}

#[no_mangle]
pub extern "C" fn pair(a: i32, b: i32) -> i32 {
    let mut s = [0u32; 2];
    init(&mut s, a as u32, b as u32);
    s[1].wrapping_sub(s[0]) as i32
}
