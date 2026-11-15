#![no_std]
#![feature(unsized_fn_params)]
use unsized_arguments_types::*;
fn fold(s: &[u64], seed: u64) -> u64 {
    let mut h = seed ^ s.len() as u64;
    let mut i = 0;
    while i < s.len() {
        h = h.wrapping_mul(0x100000001b3).wrapping_add(s[i]);
        i += 1;
    }
    h ^ s.as_ptr() as usize as u64
}
fn alter(s: &mut [u64], seed: u64) {
    if s.len() > 1 {
        s[0] ^= seed;
        let last = s.len() - 1;
        s[last] = s[last].wrapping_add(seed);
    }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn receive0(mut s: [u64], tail: u64, guard: u64) -> u64 {
    let salt = tail ^ guard;
    alter(&mut s, salt);
    fold(&s, salt)
}
#[unsafe(no_mangle)]
pub fn send0(s: [u64], seed: u64) -> u64 {
    unsafe { external0(s, seed, !seed) }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn receive1(p0: u64, mut s: [u64], tail: u64, guard: u64) -> u64 {
    let salt = tail ^ guard ^ p0.wrapping_mul(3);
    alter(&mut s, salt);
    fold(&s, salt)
}
#[unsafe(no_mangle)]
pub fn send1(s: [u64], seed: u64) -> u64 {
    unsafe { external1(seed.wrapping_add(79225), s, seed, !seed) }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn receive2(p0: u64, p1: u64, mut s: [u64], tail: u64, guard: u64) -> u64 {
    let salt = tail ^ guard ^ p0.wrapping_mul(3) ^ p1.wrapping_mul(5);
    alter(&mut s, salt);
    fold(&s, salt)
}
#[unsafe(no_mangle)]
pub fn send2(s: [u64], seed: u64) -> u64 {
    unsafe {
        external2(
            seed.wrapping_add(79225),
            seed.wrapping_add(79302),
            s,
            seed,
            !seed,
        )
    }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn receive3(p0: u64, p1: u64, p2: u64, mut s: [u64], tail: u64, guard: u64) -> u64 {
    let salt = tail ^ guard ^ p0.wrapping_mul(3) ^ p1.wrapping_mul(5) ^ p2.wrapping_mul(7);
    alter(&mut s, salt);
    fold(&s, salt)
}
#[unsafe(no_mangle)]
pub fn send3(s: [u64], seed: u64) -> u64 {
    unsafe {
        external3(
            seed.wrapping_add(79225),
            seed.wrapping_add(79302),
            seed.wrapping_add(79379),
            s,
            seed,
            !seed,
        )
    }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn receive4(p0: u64, p1: u64, p2: u64, p3: u64, mut s: [u64], tail: u64, guard: u64) -> u64 {
    let salt = tail
        ^ guard
        ^ p0.wrapping_mul(3)
        ^ p1.wrapping_mul(5)
        ^ p2.wrapping_mul(7)
        ^ p3.wrapping_mul(9);
    alter(&mut s, salt);
    fold(&s, salt)
}
#[unsafe(no_mangle)]
pub fn send4(s: [u64], seed: u64) -> u64 {
    unsafe {
        external4(
            seed.wrapping_add(79225),
            seed.wrapping_add(79302),
            seed.wrapping_add(79379),
            seed.wrapping_add(79456),
            s,
            seed,
            !seed,
        )
    }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn receive5(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    mut s: [u64],
    tail: u64,
    guard: u64,
) -> u64 {
    let salt = tail
        ^ guard
        ^ p0.wrapping_mul(3)
        ^ p1.wrapping_mul(5)
        ^ p2.wrapping_mul(7)
        ^ p3.wrapping_mul(9)
        ^ p4.wrapping_mul(11);
    alter(&mut s, salt);
    fold(&s, salt)
}
#[unsafe(no_mangle)]
pub fn send5(s: [u64], seed: u64) -> u64 {
    unsafe {
        external5(
            seed.wrapping_add(79225),
            seed.wrapping_add(79302),
            seed.wrapping_add(79379),
            seed.wrapping_add(79456),
            seed.wrapping_add(79533),
            s,
            seed,
            !seed,
        )
    }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn receive6(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    mut s: [u64],
    tail: u64,
    guard: u64,
) -> u64 {
    let salt = tail
        ^ guard
        ^ p0.wrapping_mul(3)
        ^ p1.wrapping_mul(5)
        ^ p2.wrapping_mul(7)
        ^ p3.wrapping_mul(9)
        ^ p4.wrapping_mul(11)
        ^ p5.wrapping_mul(13);
    alter(&mut s, salt);
    fold(&s, salt)
}
#[unsafe(no_mangle)]
pub fn send6(s: [u64], seed: u64) -> u64 {
    unsafe {
        external6(
            seed.wrapping_add(79225),
            seed.wrapping_add(79302),
            seed.wrapping_add(79379),
            seed.wrapping_add(79456),
            seed.wrapping_add(79533),
            seed.wrapping_add(79610),
            s,
            seed,
            !seed,
        )
    }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn receive7(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    mut s: [u64],
    tail: u64,
    guard: u64,
) -> u64 {
    let salt = tail
        ^ guard
        ^ p0.wrapping_mul(3)
        ^ p1.wrapping_mul(5)
        ^ p2.wrapping_mul(7)
        ^ p3.wrapping_mul(9)
        ^ p4.wrapping_mul(11)
        ^ p5.wrapping_mul(13)
        ^ p6.wrapping_mul(15);
    alter(&mut s, salt);
    fold(&s, salt)
}
#[unsafe(no_mangle)]
pub fn send7(s: [u64], seed: u64) -> u64 {
    unsafe {
        external7(
            seed.wrapping_add(79225),
            seed.wrapping_add(79302),
            seed.wrapping_add(79379),
            seed.wrapping_add(79456),
            seed.wrapping_add(79533),
            seed.wrapping_add(79610),
            seed.wrapping_add(79687),
            s,
            seed,
            !seed,
        )
    }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn receive8(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    p7: u64,
    mut s: [u64],
    tail: u64,
    guard: u64,
) -> u64 {
    let salt = tail
        ^ guard
        ^ p0.wrapping_mul(3)
        ^ p1.wrapping_mul(5)
        ^ p2.wrapping_mul(7)
        ^ p3.wrapping_mul(9)
        ^ p4.wrapping_mul(11)
        ^ p5.wrapping_mul(13)
        ^ p6.wrapping_mul(15)
        ^ p7.wrapping_mul(17);
    alter(&mut s, salt);
    fold(&s, salt)
}
#[unsafe(no_mangle)]
pub fn send8(s: [u64], seed: u64) -> u64 {
    unsafe {
        external8(
            seed.wrapping_add(79225),
            seed.wrapping_add(79302),
            seed.wrapping_add(79379),
            seed.wrapping_add(79456),
            seed.wrapping_add(79533),
            seed.wrapping_add(79610),
            seed.wrapping_add(79687),
            seed.wrapping_add(79764),
            s,
            seed,
            !seed,
        )
    }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn receive9(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    p7: u64,
    p8: u64,
    mut s: [u64],
    tail: u64,
    guard: u64,
) -> u64 {
    let salt = tail
        ^ guard
        ^ p0.wrapping_mul(3)
        ^ p1.wrapping_mul(5)
        ^ p2.wrapping_mul(7)
        ^ p3.wrapping_mul(9)
        ^ p4.wrapping_mul(11)
        ^ p5.wrapping_mul(13)
        ^ p6.wrapping_mul(15)
        ^ p7.wrapping_mul(17)
        ^ p8.wrapping_mul(19);
    alter(&mut s, salt);
    fold(&s, salt)
}
#[unsafe(no_mangle)]
pub fn send9(s: [u64], seed: u64) -> u64 {
    unsafe {
        external9(
            seed.wrapping_add(79225),
            seed.wrapping_add(79302),
            seed.wrapping_add(79379),
            seed.wrapping_add(79456),
            seed.wrapping_add(79533),
            seed.wrapping_add(79610),
            seed.wrapping_add(79687),
            seed.wrapping_add(79764),
            seed.wrapping_add(79841),
            s,
            seed,
            !seed,
        )
    }
}
unsafe extern "Rust" {
    fn external0(s: [u64], tail: u64, guard: u64) -> u64;
    fn external1(p0: u64, s: [u64], tail: u64, guard: u64) -> u64;
    fn external2(p0: u64, p1: u64, s: [u64], tail: u64, guard: u64) -> u64;
    fn external3(p0: u64, p1: u64, p2: u64, s: [u64], tail: u64, guard: u64) -> u64;
    fn external4(p0: u64, p1: u64, p2: u64, p3: u64, s: [u64], tail: u64, guard: u64) -> u64;
    fn external5(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        s: [u64],
        tail: u64,
        guard: u64,
    ) -> u64;
    fn external6(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        p5: u64,
        s: [u64],
        tail: u64,
        guard: u64,
    ) -> u64;
    fn external7(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        p5: u64,
        p6: u64,
        s: [u64],
        tail: u64,
        guard: u64,
    ) -> u64;
    fn external8(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        p5: u64,
        p6: u64,
        p7: u64,
        s: [u64],
        tail: u64,
        guard: u64,
    ) -> u64;
    fn external9(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        p5: u64,
        p6: u64,
        p7: u64,
        p8: u64,
        s: [u64],
        tail: u64,
        guard: u64,
    ) -> u64;
}
#[unsafe(no_mangle)]
pub fn owned_text(s: str, seed: u64) -> u64 {
    let b = s.as_bytes();
    let mut h = seed ^ b.len() as u64;
    let mut i = 0;
    while i < b.len() {
        h = h.wrapping_mul(257).wrapping_add(b[i] as u64);
        i += 1;
    }
    h ^ b.as_ptr() as usize as u64
}
#[unsafe(no_mangle)]
pub fn owned_wide(s: [Wide], seed: u64) -> u64 {
    let mut h = seed ^ s.len() as u64;
    let mut i = 0;
    while i < s.len() {
        h = h.wrapping_mul(257).wrapping_add(s[i].a ^ s[i].b);
        i += 1;
    }
    h ^ s.as_ptr() as usize as u64
}
#[unsafe(no_mangle)]
pub fn owned_zero(s: [Zero], seed: u64) -> u64 {
    seed ^ s.len() as u64 ^ s.as_ptr() as usize as u64
}
#[unsafe(no_mangle)]
pub fn through_pointer(f: fn([u64], u64) -> u64, s: [u64], seed: u64) -> u64 {
    f(s, seed)
}
#[unsafe(no_mangle)]
pub fn through_virtual(t: &dyn Sink, s: [u64], seed: u64) -> u64 {
    t.consume(s, seed)
}
