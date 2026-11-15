// By-value array iteration on wasm32: `for x in [a, b, c]`, `[..].into_iter()`
// chains, a partly consumed `array::IntoIter` (by `next`, `nth`, `next_back`
// or a short-circuiting `find`/`any`/`all`), and core's own `next_back`,
// `nth`, `size_hint` and `rfold` over the same state.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// `core::array::IntoIter<T, N>` keeps `alive: IndexRange { start, end }` as two
// `usize` indices, four bytes each on wasm32. The bridge's state model is
// rustc's own layout (`ArrayIntoIterLayout`), read through `layout_of` at the
// session's pointer width, so the constructor, `next`, the identity
// `into_iter` and the chain drives store and load those indices at four
// bytes. At `-O2`/`-O3` rustc's MIR inliner inlines `IntoIter::fold` down to
// `<IndexRange as Iterator>::try_fold` over core's `PolymorphicIter` closure,
// which the chain engine drives as a `Range<usize>` source; at `-O0` a cdylib
// lowers the iterator's `drop_glue` (a no-op for these elements) and core's
// bodies that read the state. Overflow traps count only when both sides trap.
#![no_std]

// wasm32-differential-flags: -Copt-level=1
// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=3
// wasm32-differential-flags: -Copt-level=2 -Coverflow-checks=on
// wasm32-differential-flags: -Copt-level=3 -Ccodegen-units=4

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[no_mangle]
pub extern "C" fn for_i32(a: i32, b: i32, c: i32) -> i32 {
    let mut s = 0i32;
    for x in [a, b, c] {
        s = s.wrapping_mul(31).wrapping_add(x);
    }
    s
}
#[no_mangle]
pub extern "C" fn for_u8(a: u32, b: u32) -> u32 {
    let mut s = 0u32;
    for x in [a as u8, b as u8, (a ^ b) as u8, 7u8, 200u8] {
        s = s.wrapping_mul(5).wrapping_add(x as u32);
    }
    s
}
#[no_mangle]
pub extern "C" fn for_u16_break(a: u32, b: u32) -> u32 {
    let mut s = 0u32;
    for x in [a as u16, b as u16, 3, 9, 11, 13] {
        if x == 9 {
            break;
        }
        s = s.wrapping_add(x as u32);
    }
    s
}
#[no_mangle]
pub extern "C" fn for_i64(a: i64, b: i64) -> i64 {
    let mut s = 1i64;
    for x in [a, b, a.wrapping_sub(b), 12] {
        s = s.wrapping_mul(x | 1);
    }
    s
}
#[no_mangle]
pub extern "C" fn for_f64(a: f64, b: f64) -> f64 {
    let mut s = 0.0f64;
    for x in [a, b, 0.5, -2.25] {
        s = s * 0.5 + x;
    }
    s
}
#[no_mangle]
pub extern "C" fn for_f32(a: f32, b: f32) -> f32 {
    let mut s = 0.0f32;
    for x in [a, b, 1.5] {
        s += x;
    }
    s
}
#[no_mangle]
pub extern "C" fn for_bool(a: u32) -> u32 {
    let mut n = 0u32;
    for x in [a & 1 != 0, a & 2 != 0, a & 4 != 0, true] {
        if x {
            n += 1;
        }
    }
    n
}
#[no_mangle]
pub extern "C" fn map_sum_u32(a: u32, b: u32) -> u32 {
    [a, b, 7, 9].into_iter().map(|x| x & 0xff).sum()
}
#[no_mangle]
pub extern "C" fn map_fold_i64(a: i64, b: i64) -> i64 {
    [a, b, a ^ b]
        .into_iter()
        .map(|x| x.wrapping_mul(3))
        .fold(0i64, |s, x| s.wrapping_add(x))
}
#[no_mangle]
pub extern "C" fn sum_u64(a: u64, b: u64) -> u64 {
    [a, b, 1u64 << 40]
        .into_iter()
        .fold(0u64, |s, x| s.wrapping_add(x))
}
#[no_mangle]
pub extern "C" fn filter_count(a: i32, b: i32) -> u32 {
    [a, b, -a, -b, 0, 5].into_iter().filter(|x| *x > 0).count() as u32
}
#[no_mangle]
pub extern "C" fn partial_then_for(a: i32, b: i32) -> i32 {
    let mut it = [a, b, 3, 4, 5].into_iter();
    let first = it.next().unwrap_or(0);
    let second = it.next().unwrap_or(0);
    let mut s = first.wrapping_mul(100).wrapping_add(second);
    for x in it {
        s = s.wrapping_mul(7).wrapping_add(x);
    }
    s
}
#[no_mangle]
pub extern "C" fn manual_next(a: i32) -> i32 {
    let mut it = [a, a + 1].into_iter();
    let x = it.next().unwrap_or(-1);
    let y = it.next().unwrap_or(-1);
    let z = it.next().unwrap_or(-1);
    x.wrapping_mul(10000)
        .wrapping_add(y.wrapping_mul(100))
        .wrapping_add(z)
}
#[no_mangle]
pub extern "C" fn any_all(a: i32, b: i32) -> u32 {
    let p = [a, b, 3].into_iter().any(|x| x == 7) as u32;
    let q = [a, b, 3].into_iter().all(|x| x > 0) as u32;
    p * 2 + q
}
#[no_mangle]
pub extern "C" fn enumerate_sum(a: u32, b: u32) -> u32 {
    let mut s = 0u32;
    for (i, x) in [a, b, 5].into_iter().enumerate() {
        s = s.wrapping_add((i as u32 + 1).wrapping_mul(x));
    }
    s
}
#[no_mangle]
pub extern "C" fn nested(a: i32, b: i32) -> i32 {
    let mut s = 0i32;
    for x in [a, b] {
        for y in [x, x + 1, 2] {
            s = s.wrapping_add(x.wrapping_mul(y));
        }
    }
    s
}

#[no_mangle]
pub extern "C" fn rev_for(a: i32, b: i32) -> i32 {
    let mut s = 0i32;
    for x in [a, b, 3].into_iter().rev() {
        s = s.wrapping_mul(10).wrapping_add(x);
    }
    s
}
#[no_mangle]
pub extern "C" fn sh(a: i32) -> u32 {
    let mut it = [a, 2, 3].into_iter();
    it.next();
    it.size_hint().0 as u32
}
#[no_mangle]
pub extern "C" fn find_val(a: i32, b: i32) -> i32 {
    [a, b, 3, 4].into_iter().find(|x| *x > 2).unwrap_or(-5)
}
#[no_mangle]
pub extern "C" fn for_mut_acc(a: i64, b: i64) -> i64 {
    let mut lo = i64::MAX;
    let mut hi = i64::MIN;
    for x in [a, b, a.wrapping_add(b), 0] {
        if x < lo {
            lo = x;
        }
        if x > hi {
            hi = x;
        }
    }
    hi.wrapping_sub(lo)
}
#[no_mangle]
pub extern "C" fn last_elem(a: u32, b: u32) -> u32 {
    [a, b, 3].into_iter().last().unwrap_or(0)
}
#[no_mangle]
pub extern "C" fn chars_arr(a: u32) -> u32 {
    let mut s = 0u32;
    for c in ['a', 'z', char::from_u32(a & 0x7f).unwrap_or('q')] {
        s = s.wrapping_mul(131).wrapping_add(c as u32);
    }
    s
}
#[no_mangle]
pub extern "C" fn i8_arr(a: i32, b: i32) -> i32 {
    let mut s = 0i32;
    for x in [a as i8, b as i8, -128i8, 127i8, 0] {
        s = s.wrapping_mul(3).wrapping_add(x as i32);
    }
    s
}
#[no_mangle]
pub extern "C" fn both_ends(a: i32, b: i32) -> i32 {
    let mut it = [a, b, 3, 4].into_iter();
    let x = it.next_back().unwrap_or(-1);
    let y = it.next().unwrap_or(-1);
    let z = it.next_back().unwrap_or(-1);
    let w = it.next().unwrap_or(-1);
    let v = it.next().unwrap_or(-1);
    let u = it.next_back().unwrap_or(-1);
    x.wrapping_mul(7)
        .wrapping_add(y.wrapping_mul(11))
        .wrapping_add(z.wrapping_mul(13))
        .wrapping_add(w.wrapping_mul(17))
        .wrapping_add(v.wrapping_mul(19))
        .wrapping_add(u)
}
#[no_mangle]
pub extern "C" fn rev_fold(a: u32, b: u32) -> u32 {
    [a, b, 3, 4]
        .into_iter()
        .rev()
        .fold(0u32, |s, x| s.wrapping_mul(31).wrapping_add(x))
}
#[no_mangle]
pub extern "C" fn back_then_for(a: i32, b: i32) -> i32 {
    let mut it = [a, b, 3, 4, 5].into_iter();
    let last = it.next_back().unwrap_or(0);
    let mut s = last;
    for x in it {
        s = s.wrapping_mul(3).wrapping_add(x);
    }
    s
}

#[inline(never)]
fn sum_by_value(arr: [u32; 4]) -> u32 {
    arr.into_iter().map(|x| x.rotate_left(3)).sum()
}
#[no_mangle]
pub extern "C" fn helper_sum(a: u32, b: u32) -> u32 {
    sum_by_value([a, b, a & b, a | b])
}

#[inline(never)]
fn make_iter(a: i32, b: i32) -> core::array::IntoIter<i32, 3> {
    [a, b, a.wrapping_sub(b)].into_iter()
}
#[no_mangle]
pub extern "C" fn returned_iter(a: i32, b: i32) -> i32 {
    let mut s = 0i32;
    for x in make_iter(a, b) {
        s = s.wrapping_mul(17).wrapping_add(x);
    }
    s
}
#[no_mangle]
pub extern "C" fn usize_arr(a: u32, b: u32) -> u32 {
    let mut s = 0usize;
    for x in [a as usize, b as usize, usize::MAX, 1] {
        s = s.wrapping_add(x);
    }
    s as u32
}
#[no_mangle]
pub extern "C" fn isize_sum(a: i32, b: i32) -> i32 {
    [a as isize, b as isize, -3isize].into_iter().sum::<isize>() as i32
}
#[no_mangle]
pub extern "C" fn u128_arr(a: u64, b: u64) -> u64 {
    let mut s = 0u128;
    for x in [a as u128, (b as u128) << 64, u128::MAX] {
        s = s.wrapping_add(x);
    }
    (s >> 32) as u64 ^ s as u64
}
#[no_mangle]
pub extern "C" fn long_arr(a: u32) -> u32 {
    let mut s = 0u32;
    for x in [a, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] {
        s = s.wrapping_mul(3) ^ x;
    }
    s
}
#[no_mangle]
pub extern "C" fn single(a: u64) -> u64 {
    let mut s = 0u64;
    for x in [a] {
        s = s.wrapping_add(x.wrapping_mul(3));
    }
    s
}
#[no_mangle]
pub extern "C" fn count_all(a: i32, b: i32) -> u32 {
    [a, b, 3, 4, 5].into_iter().count() as u32
        + [a, b].into_iter().filter(|x| *x == 1).count() as u32
}
#[no_mangle]
pub extern "C" fn take_skip(a: u32, b: u32) -> u32 {
    let p: u32 = [a, b, 3, 4, 5].into_iter().skip(1).take(3).sum();
    p
}
#[no_mangle]
pub extern "C" fn nth_dyn(a: u32, k: u32) -> u32 {
    let mut it = [a, 10, 20, 30, 40].into_iter();
    let x = it.nth((k % 7) as usize).unwrap_or(99);
    let y = it.next().unwrap_or(77);
    let n = it.size_hint().0 as u32;
    x.wrapping_mul(1000)
        .wrapping_add(y.wrapping_mul(10))
        .wrapping_add(n)
}

// A short-circuiting consumer leaves the rest of the iterator in place.
#[no_mangle]
pub extern "C" fn find_then_rest(a: i32, b: i32) -> i32 {
    let mut it = [a, b, 3, 4, 5, 6].into_iter();
    let f = it.find(|x| *x > 3).unwrap_or(-1);
    let mut s = f.wrapping_mul(1000);
    for x in it {
        s = s.wrapping_mul(3).wrapping_add(x);
    }
    s
}
#[no_mangle]
pub extern "C" fn any_then_next(a: i32, b: i32) -> i32 {
    let mut it = [a, b, 7, 8].into_iter();
    let hit = it.any(|x| x == 7) as i32;
    let n = it.next().unwrap_or(-1);
    let m = it.next().unwrap_or(-2);
    hit * 10000 + n.wrapping_mul(100).wrapping_add(m)
}
#[no_mangle]
pub extern "C" fn all_then_count(a: i32, b: i32) -> u32 {
    let mut it = [a, b, -1, 8, 9].into_iter();
    let ok = it.all(|x| x >= 0) as u32;
    ok * 100 + it.count() as u32
}
