// Function instances rustc copies into several codegen units, on wasm32.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// With more than one codegen unit rustc places a `LocalCopy` instance — an
// `#[inline(always)]` function, `core`'s `wrapping_*` / `PartialOrd::lt` /
// slice-index impls, and at `-O` every small, `#[inline]` or generic function
// and closure — in EVERY codegen unit that reaches it, as a CGU-private
// (`Internal`) copy under one symbol. Each module below is its own codegen
// unit under `-Ccodegen-units=16/64`, and each reaches the same instances: a
// shared `#[inline(always)]` helper, `core` arithmetic and comparisons, range
// slicing, a generic function, a closure-taking generic, a trait object's
// methods, and function pointers stored in statics (whose data lives in an
// object of its own). Every copy must link as one definition per symbol and
// compute what LLVM's private copies compute. No export compares function
// addresses: two CGUs' copies of one instance may or may not share one. An
// explicit `#[linkage]` keeps its weak binding.
//
// The copies of one crate are all it may share. The dependency
// `extern/r3-bridge-multicgu-dep.rs` is built with overflow checks on and
// copies the same `core` instances under the same symbols as this crate; in
// the optimized configurations this crate is built without overflow checks,
// so each crate must run its own copies (the dependency's `i32::abs(i32::MIN)`
// traps, this crate's wraps).
#![no_std]
#![allow(dead_code)]
#![feature(linkage)]

// wasm32-differential-flags: -Ccodegen-units=16
// wasm32-differential-flags: -Ccodegen-units=16 -Copt-level=2
// wasm32-differential-flags: -Ccodegen-units=64 -Copt-level=3
// wasm32-differential-flags: -Ccodegen-units=4 -Copt-level=1
// wasm32-differential-extern: multicgu_dep r3-bridge-multicgu-dep.rs -Coverflow-checks=on

extern crate multicgu_dep;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

mod shared {
    /// `LocalCopy` at every optimization level.
    #[inline(always)]
    pub fn mix(x: u32, k: u32) -> u32 {
        x.wrapping_mul(0x9e37_79b9).rotate_left(k & 31) ^ k
    }

    /// Generic: one instance per type, placed in every CGU that uses it once
    /// optimized.
    #[inline]
    pub fn larger<T: PartialOrd + Copy>(a: T, b: T) -> T {
        if a < b { b } else { a }
    }

    /// Takes a closure: every caller's closure type is its own instance.
    #[inline]
    pub fn fold3<F: Fn(u32, u32) -> u32>(seed: u32, xs: &[u32; 3], f: F) -> u32 {
        let mut acc = seed;
        for &x in xs {
            acc = f(acc, x);
        }
        acc
    }

    pub trait Shape {
        fn area(&self) -> u32;
        fn scale(&self, k: u32) -> u32 {
            self.area().wrapping_mul(k)
        }
    }

    pub struct Rect {
        pub w: u32,
        pub h: u32,
    }

    pub struct Tri {
        pub b: u32,
        pub h: u32,
    }

    impl Shape for Rect {
        fn area(&self) -> u32 {
            self.w.wrapping_mul(self.h)
        }
    }

    impl Shape for Tri {
        fn area(&self) -> u32 {
            self.b.wrapping_mul(self.h) / 2
        }
    }

    pub static TABLE: [u32; 8] = [3, 1, 4, 1, 5, 9, 2, 6];
}

mod left {
    use super::shared::{self, Shape};

    #[inline(never)]
    pub fn run(x: u32, k: u32) -> u32 {
        let m = shared::mix(x, k);
        let window = &shared::TABLE[(k % 4) as usize..];
        let mut s = 0u32;
        for v in window {
            s = s.wrapping_add(*v);
        }
        m.wrapping_add(s) ^ shared::larger(x, k)
    }

    #[inline(never)]
    pub fn folded(x: u32, k: u32) -> u32 {
        shared::fold3(x, &[k, 7, 11], |a, b| a.wrapping_mul(3).wrapping_add(b))
    }

    #[inline(never)]
    pub fn dyn_area(which: u32, x: u32) -> u32 {
        let r = shared::Rect { w: x & 0xff, h: 3 };
        let t = shared::Tri { b: x & 0xff, h: 5 };
        let s: &dyn Shape = if which & 1 == 0 { &r } else { &t };
        s.scale(which % 5).wrapping_add(s.area())
    }

    #[inline(never)]
    pub fn wide(a: u64, b: u64) -> u64 {
        shared::larger(a, b).wrapping_mul(3) ^ a.wrapping_add(b)
    }
}

mod right {
    use super::shared::{self, Shape};

    #[inline(never)]
    pub fn run(x: u32, k: u32) -> u32 {
        let m = shared::mix(k, x);
        let window = &shared::TABLE[..(x % 8) as usize];
        let mut s = 0u32;
        for v in window {
            s = s.wrapping_mul(5).wrapping_add(*v);
        }
        m.wrapping_sub(s) ^ shared::larger(k, x)
    }

    #[inline(never)]
    pub fn folded(x: u32, k: u32) -> u32 {
        shared::fold3(k, &[x, 2, 13], |a, b| (a ^ b).wrapping_add(1))
    }

    #[inline(never)]
    pub fn dyn_area(which: u32, x: u32) -> u32 {
        let t = shared::Tri {
            b: (x >> 3) & 0xff,
            h: 9,
        };
        let r = shared::Rect {
            w: (x >> 5) & 0xff,
            h: 2,
        };
        let s: &dyn Shape = if which & 2 == 0 { &t } else { &r };
        s.area() ^ s.scale(which % 3)
    }

    #[inline(never)]
    pub fn wide(a: u64, b: u64) -> u64 {
        shared::larger(b, a).wrapping_add(a.wrapping_mul(b))
    }
}

mod ops {
    #[inline(always)]
    fn dbl(x: u32) -> u32 {
        x.wrapping_mul(2)
    }
    fn inc(x: u32) -> u32 {
        x.wrapping_add(1)
    }
    fn tri(x: u32) -> u32 {
        super::shared::mix(x, 3)
    }

    /// Each static is its own object; its data holds the addresses of
    /// functions whose copies live in the CGUs that call them.
    pub static OPS: [fn(u32) -> u32; 3] = [dbl, inc, tri];

    #[inline(never)]
    pub fn apply(i: u32, x: u32) -> u32 {
        (OPS[(i % 3) as usize])(x)
    }

    #[inline(never)]
    pub fn direct(x: u32) -> u32 {
        dbl(x) ^ inc(x) ^ tri(x)
    }
}

mod explicit {
    /// A weak definition nothing overrides: the linker keeps this one.
    #[linkage = "weak"]
    #[no_mangle]
    pub fn r3_multicgu_weak(x: u32) -> u32 {
        x.wrapping_mul(3) ^ 0x5a
    }

    #[linkage = "weak_odr"]
    #[inline(never)]
    pub fn once(x: u32) -> u32 {
        super::shared::mix(x, 5).wrapping_add(1)
    }
}

mod iter {
    #[inline(never)]
    pub fn take_max(n: u32, t: u32) -> u32 {
        (1..1 + n % 20)
            .take((t % 12) as usize)
            .map(|x| x * 7 % 11)
            .fold(777, |a, b| if b > a || a == 777 { b } else { a })
    }

    #[inline(never)]
    pub fn count(n: u32, t: u32) -> u32 {
        (0..n % 30).take((t % 9) as usize).count() as u32
    }
}

mod cross_crate {
    #[inline(never)]
    pub fn abs_via_ptr(x: i32) -> i32 {
        let f: fn(i32) -> i32 = i32::abs;
        core::hint::black_box(f)(x)
    }

    #[inline(never)]
    pub fn pow_via_ptr(x: u32, y: u32) -> u32 {
        let f: fn(u32, u32) -> u32 = u32::pow;
        core::hint::black_box(f)(x, y & 7)
    }

    #[inline(never)]
    pub fn mix(x: u32, y: u32) -> u32 {
        x.wrapping_add(y).rotate_left(y & 31)
    }
}

#[no_mangle]
pub extern "C" fn e_left(x: u32, k: u32) -> u32 {
    left::run(x, k)
}
#[no_mangle]
pub extern "C" fn e_right(x: u32, k: u32) -> u32 {
    right::run(x, k)
}
#[no_mangle]
pub extern "C" fn e_folded(x: u32, k: u32) -> u32 {
    left::folded(x, k) ^ right::folded(x, k)
}
#[no_mangle]
pub extern "C" fn e_dyn(which: u32, x: u32) -> u32 {
    left::dyn_area(which, x).wrapping_add(right::dyn_area(which, x))
}
#[no_mangle]
pub extern "C" fn e_wide(a: u64, b: u64) -> u64 {
    left::wide(a, b) ^ right::wide(a, b)
}
#[no_mangle]
pub extern "C" fn e_apply(i: u32, x: u32) -> u32 {
    ops::apply(i, x)
}
#[no_mangle]
pub extern "C" fn e_direct(x: u32) -> u32 {
    ops::direct(x) ^ shared::mix(x, 9)
}
#[no_mangle]
pub extern "C" fn e_explicit(x: u32) -> u32 {
    explicit::r3_multicgu_weak(x) ^ explicit::once(x) ^ ops::direct(x)
}
#[no_mangle]
pub extern "C" fn e_take_max(n: u32, t: u32) -> u32 {
    iter::take_max(n, t)
}
#[no_mangle]
pub extern "C" fn e_count(n: u32, t: u32) -> u32 {
    iter::count(n, t)
}
#[no_mangle]
pub extern "C" fn e_dep_abs(x: i32) -> i32 {
    multicgu_dep::abs_via_ptr(x)
}
#[no_mangle]
pub extern "C" fn e_dep_abs_direct(x: i32) -> i32 {
    multicgu_dep::abs_direct(x)
}
#[no_mangle]
pub extern "C" fn e_local_abs(x: i32) -> i32 {
    cross_crate::abs_via_ptr(x)
}
#[no_mangle]
pub extern "C" fn e_local_abs_direct(x: i32) -> i32 {
    x.abs()
}
#[no_mangle]
pub extern "C" fn e_dep_pow(x: u32, y: u32) -> u32 {
    multicgu_dep::pow_via_ptr(x, y)
}
#[no_mangle]
pub extern "C" fn e_local_pow(x: u32, y: u32) -> u32 {
    cross_crate::pow_via_ptr(x, y)
}
#[no_mangle]
pub extern "C" fn e_mixes(x: u32, y: u32) -> u32 {
    multicgu_dep::mix(x, y) ^ cross_crate::mix(y, x)
}
#[no_mangle]
pub extern "C" fn e_dep_larger(x: u32, y: u32) -> u32 {
    multicgu_dep::larger(x, y)
        ^ multicgu_dep::larger_u32(y, x)
        ^ multicgu_dep::larger(x as i64, -(y as i64)) as u32
}
