#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
#[derive(Clone, Copy)]
struct P {
    a: u8,
    b: u64,
    c: u16,
}
#[derive(Clone, Copy)]
struct W {
    n: usize,
    p: *const u8,
    t: u32,
}
static PS: [P; 4] = [
    P {
        a: 1,
        b: u64::MAX,
        c: 7,
    },
    P {
        a: 2,
        b: 5,
        c: 65535,
    },
    P {
        a: 255,
        b: 1 << 40,
        c: 0,
    },
    P { a: 9, b: 3, c: 300 },
];
static BYTES: [u8; 6] = [10, 20, 30, 40, 50, 60];

#[inline(never)]
fn sum_ps(xs: &[P]) -> u64 {
    let mut s = 0u64;
    for p in xs {
        s = s
            .wrapping_mul(31)
            .wrapping_add(p.a as u64 ^ p.b ^ (p.c as u64) << 48);
    }
    s
}
#[no_mangle]
pub extern "C" fn e_ps(lo: u32, hi: u32) -> u64 {
    let lo = (lo % 5) as usize;
    let hi = (hi % 5) as usize;
    if lo > hi {
        return 1;
    }
    sum_ps(&PS[lo..hi])
}
#[no_mangle]
pub extern "C" fn e_ps_local(k: u32) -> u64 {
    let mut arr = PS;
    arr[(k % 4) as usize].b ^= k as u64;
    arr[(k as usize / 4) % 4].c = k as u16;
    sum_ps(&arr) ^ sum_ps(&arr[1..])
}
#[inline(never)]
fn sum_ws(xs: &[W]) -> u32 {
    let mut s = 0u32;
    for w in xs {
        s = s
            .wrapping_mul(7)
            .wrapping_add(w.n as u32 ^ w.t ^ unsafe { *w.p } as u32);
    }
    s
}
#[no_mangle]
pub extern "C" fn e_ws(k: u32) -> u32 {
    let ws = [
        W {
            n: k as usize,
            p: &BYTES[0],
            t: 1,
        },
        W {
            n: usize::MAX,
            p: &BYTES[(k % 6) as usize],
            t: k,
        },
        W {
            n: 3,
            p: &BYTES[5],
            t: 0xffff,
        },
    ];
    sum_ws(&ws) ^ sum_ws(&ws[(k % 4) as usize..]) << 16
}
#[inline(never)]
fn tup_sum(xs: &[(u16, u64, u8)]) -> u64 {
    let mut s = 0u64;
    for t in xs.iter() {
        s = s.rotate_left(7) ^ t.0 as u64 ^ t.1 ^ (t.2 as u64) << 56;
    }
    s
}
#[no_mangle]
pub extern "C" fn e_tuples(k: u32) -> u64 {
    let arr = [
        (1u16, 2u64, 3u8),
        (k as u16, k as u64 * 3, k as u8),
        (65535, u64::MAX, 255),
    ];
    tup_sum(&arr[(k % 4) as usize..])
}
#[inline(never)]
fn pairs_idx(xs: &[(u32, u64)], i: usize) -> u64 {
    match xs.get(i) {
        Some(t) => t.1 ^ t.0 as u64,
        None => 12,
    }
}
#[no_mangle]
pub extern "C" fn e_pairs_get(k: u32) -> u64 {
    let arr = [
        (1u32, 2u64),
        (3, 4),
        (k, k as u64 * 5),
        (0xffff_ffff, 1 << 63),
    ];
    pairs_idx(&arr, (k % 6) as usize)
}
#[inline(never)]
fn opt_sum(xs: &[Option<u32>]) -> u32 {
    let mut s = 0u32;
    for o in xs {
        s = s.wrapping_mul(3).wrapping_add(match o {
            Some(v) => *v,
            None => 1000,
        });
    }
    s
}
#[no_mangle]
pub extern "C" fn e_opts(k: u32) -> u32 {
    let arr = [Some(k), None, Some(7), Some(u32::MAX), None];
    opt_sum(&arr[(k % 6) as usize..])
}
#[inline(never)]
fn arr2d(xs: &[[u16; 3]]) -> u32 {
    let mut s = 0u32;
    for row in xs {
        for v in row {
            s = s.wrapping_mul(5).wrapping_add(*v as u32);
        }
    }
    s
}
#[no_mangle]
pub extern "C" fn e_arr2d(k: u32) -> u32 {
    let a = [[1u16, 2, 3], [k as u16, 65535, 0], [9, 8, 7], [4, 5, 6]];
    arr2d(&a[(k % 5) as usize..])
}
#[inline(never)]
fn char_sum(xs: &[char]) -> u32 {
    let mut s = 0u32;
    for c in xs {
        s = s.wrapping_mul(131).wrapping_add(*c as u32);
    }
    s
}
#[no_mangle]
pub extern "C" fn e_chars(k: u32) -> u32 {
    let a = [
        'a',
        'é',
        '€',
        '𝄞',
        char::from_u32(k % 0xd800).unwrap_or('x'),
    ];
    char_sum(&a[(k % 6) as usize..])
}
