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
struct State {
    a: [u32; 8],
    n: u64,
    tag: u8,
}

#[inline(never)]
fn step(mut s: State, k: u32) -> State {
    for i in 0..8 {
        s.a[i] = s.a[i].rotate_left(k).wrapping_add(i as u32);
    }
    s.n += k as u64;
    s.tag ^= k as u8;
    s
}

#[inline(never)]
fn mutate_param(mut s: State) -> u32 {
    s.a[0] = 0xdead;
    s.a[7] = 0xbeef;
    s.n = 0;
    s.a.iter().fold(0, |x, y| x ^ y)
}

#[inline(never)]
fn digest(s: &State) -> u64 {
    let mut h = s.n ^ (s.tag as u64) << 56;
    for &x in s.a.iter() {
        h = h.rotate_left(9) ^ x as u64;
    }
    h
}

#[no_mangle]
pub extern "C" fn byval_chain(x: u32, k: u32) -> u64 {
    let mut s = State {
        a: [x; 8],
        n: 1,
        tag: 3,
    };
    let orig = s;
    for j in 0..(k % 10) {
        s = step(s, j + 1);
    }
    let m = mutate_param(s);
    let m2 = mutate_param(orig);
    digest(&s) ^ digest(&orig).rotate_left(1) ^ (m as u64) << 3 ^ (m2 as u64) << 17
}

#[inline(never)]
fn arr_param(mut a: [i16; 12], k: usize) -> i32 {
    a[k % 12] = -1;
    a.swap(0, 11);
    let mut s = 0i32;
    for &x in a.iter() {
        s = s * 3 + x as i32;
    }
    s
}

#[no_mangle]
pub extern "C" fn byval_array(x: i32, k: u32) -> i64 {
    let mut a = [0i16; 12];
    for i in 0..12 {
        a[i] = (x >> i) as i16;
    }
    let r1 = arr_param(a, k as usize);
    let r2 = arr_param(a, (k + 1) as usize);
    let mut s = 0i64;
    for &v in a.iter() {
        s = s * 5 + v as i64;
    }
    s ^ (r1 as i64) << 20 ^ (r2 as i64) << 40
}

#[derive(Clone, Copy, PartialEq)]
struct Pair {
    lo: u64,
    hi: u64,
}

#[inline(never)]
fn add_pair(a: Pair, b: Pair) -> Pair {
    let (lo, c) = a.lo.overflowing_add(b.lo);
    Pair {
        lo,
        hi: a.hi.wrapping_add(b.hi).wrapping_add(c as u64),
    }
}

#[inline(never)]
fn fib_pair(n: u32) -> Pair {
    let mut a = Pair { lo: 0, hi: 0 };
    let mut b = Pair { lo: 1, hi: 0 };
    for _ in 0..n {
        let t = add_pair(a, b);
        a = b;
        b = t;
    }
    a
}

#[no_mangle]
pub extern "C" fn fib128(n: u32) -> u64 {
    let p = fib_pair(n % 200);
    p.lo ^ p.hi.rotate_left(32)
}

#[inline(never)]
fn swap_fields(p: Pair) -> Pair {
    Pair { lo: p.hi, hi: p.lo }
}

#[no_mangle]
pub extern "C" fn pair_loop(a: u64, b: u64) -> u64 {
    let mut p = Pair { lo: a, hi: b };
    let mut q = Pair { lo: b, hi: a };
    for i in 0..7 {
        if i % 2 == 0 {
            p = swap_fields(p);
        } else {
            let t = p;
            p = q;
            q = t;
        }
        q = add_pair(q, p);
    }
    p.lo ^ p.hi.rotate_left(7) ^ q.lo.rotate_left(13) ^ q.hi.rotate_left(19) ^ (p == q) as u64
}

#[inline(never)]
fn by_ptr(p: *mut u32, n: usize) {
    unsafe {
        for i in 0..n {
            let v = core::ptr::read(p.add(i));
            core::ptr::write(p.add(i), v.wrapping_mul(3) + 1);
        }
        let first = *p;
        *p.add(n - 1) ^= first;
    }
}

#[no_mangle]
pub extern "C" fn raw_ptrs(x: u32, n: u32) -> u32 {
    let mut a = [x, x + 1, x + 2, x + 3, x + 4, x + 5];
    let n = (n % 6) as usize + 1;
    by_ptr(a.as_mut_ptr(), n);
    let mut b = [0u32; 6];
    unsafe {
        core::ptr::copy_nonoverlapping(a.as_ptr(), b.as_mut_ptr().add(1), 5);
        core::ptr::copy(b.as_ptr(), b.as_mut_ptr().add(2), 3);
    }
    let mut h = 0u32;
    for i in 0..6 {
        h = h.wrapping_mul(31) ^ a[i] ^ b[i].rotate_left(i as u32);
    }
    h
}

#[no_mangle]
pub extern "C" fn local_alias(x: i32, y: i32) -> i32 {
    let mut v = x;
    let p = &mut v as *mut i32;
    unsafe {
        *p = (*p).wrapping_add(y);
    }
    let a = v;
    let r = &mut v;
    *r = r.wrapping_mul(3);
    let b = v;
    unsafe {
        *p ^= 0x55;
    }
    a ^ (b << 3) ^ (v << 9)
}

#[inline(never)]
fn split_update(xs: &mut [u64], k: usize) -> u64 {
    let (l, r) = xs.split_at_mut(k);
    for (i, x) in l.iter_mut().enumerate() {
        *x = x.wrapping_add(r.get(i).copied().unwrap_or(7));
    }
    for x in r.iter_mut() {
        *x = x.rotate_left(3);
    }
    xs.iter().fold(0u64, |h, &x| h.wrapping_mul(1_000_003) ^ x)
}

#[no_mangle]
pub extern "C" fn split_mut(x: u64, k: u32) -> u64 {
    let mut a = [x, x ^ 1, x.wrapping_mul(3), 7, 8, !x, x >> 3];
    split_update(&mut a, (k % 8) as usize)
}
