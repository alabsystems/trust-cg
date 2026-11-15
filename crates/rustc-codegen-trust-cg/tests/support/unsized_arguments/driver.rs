#![feature(unsized_fn_params)]
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicIsize, Ordering};
use unsized_arguments_types::*;
static LIVE: AtomicIsize = AtomicIsize::new(0);
struct Count;
unsafe impl GlobalAlloc for Count {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let p = unsafe { System.alloc(l) };
        if !p.is_null() {
            LIVE.fetch_add(1, Ordering::SeqCst);
        }
        p
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        LIVE.fetch_sub(1, Ordering::SeqCst);
        unsafe { System.dealloc(p, l) }
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        unsafe { System.realloc(p, l, n) }
    }
}
#[global_allocator]
static ALLOC: Count = Count;
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

unsafe extern "Rust" {
    fn receive0(s: [u64], tail: u64, guard: u64) -> u64;
    fn send0(s: [u64], seed: u64) -> u64;
    fn receive1(p0: u64, s: [u64], tail: u64, guard: u64) -> u64;
    fn send1(s: [u64], seed: u64) -> u64;
    fn receive2(p0: u64, p1: u64, s: [u64], tail: u64, guard: u64) -> u64;
    fn send2(s: [u64], seed: u64) -> u64;
    fn receive3(p0: u64, p1: u64, p2: u64, s: [u64], tail: u64, guard: u64) -> u64;
    fn send3(s: [u64], seed: u64) -> u64;
    fn receive4(p0: u64, p1: u64, p2: u64, p3: u64, s: [u64], tail: u64, guard: u64) -> u64;
    fn send4(s: [u64], seed: u64) -> u64;
    fn receive5(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        s: [u64],
        tail: u64,
        guard: u64,
    ) -> u64;
    fn send5(s: [u64], seed: u64) -> u64;
    fn receive6(
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
    fn send6(s: [u64], seed: u64) -> u64;
    fn receive7(
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
    fn send7(s: [u64], seed: u64) -> u64;
    fn receive8(
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
    fn send8(s: [u64], seed: u64) -> u64;
    fn receive9(
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
    fn send9(s: [u64], seed: u64) -> u64;
    fn owned_text(s: str, seed: u64) -> u64;
    fn owned_wide(s: [Wide], seed: u64) -> u64;
    fn owned_zero(s: [Zero], seed: u64) -> u64;
    fn through_pointer(f: fn([u64], u64) -> u64, s: [u64], seed: u64) -> u64;
    fn through_virtual(t: &dyn Sink, s: [u64], seed: u64) -> u64;
}
#[unsafe(no_mangle)]
pub fn external0(mut s: [u64], tail: u64, guard: u64) -> u64 {
    let salt = tail ^ guard;
    alter(&mut s, salt);
    fold(&s, salt)
}
#[unsafe(no_mangle)]
pub fn external1(p0: u64, mut s: [u64], tail: u64, guard: u64) -> u64 {
    let salt = tail ^ guard ^ p0.wrapping_mul(3);
    alter(&mut s, salt);
    fold(&s, salt)
}
#[unsafe(no_mangle)]
pub fn external2(p0: u64, p1: u64, mut s: [u64], tail: u64, guard: u64) -> u64 {
    let salt = tail ^ guard ^ p0.wrapping_mul(3) ^ p1.wrapping_mul(5);
    alter(&mut s, salt);
    fold(&s, salt)
}
#[unsafe(no_mangle)]
pub fn external3(p0: u64, p1: u64, p2: u64, mut s: [u64], tail: u64, guard: u64) -> u64 {
    let salt = tail ^ guard ^ p0.wrapping_mul(3) ^ p1.wrapping_mul(5) ^ p2.wrapping_mul(7);
    alter(&mut s, salt);
    fold(&s, salt)
}
#[unsafe(no_mangle)]
pub fn external4(p0: u64, p1: u64, p2: u64, p3: u64, mut s: [u64], tail: u64, guard: u64) -> u64 {
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
pub fn external5(
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
pub fn external6(
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
pub fn external7(
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
pub fn external8(
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
pub fn external9(
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
fn expected_words(b: &[u64], salt: u64) -> u64 {
    let ptr = b.as_ptr() as usize as u64;
    let mut copy = b.to_vec();
    alter(&mut copy, salt);
    fold(&copy, salt) ^ copy.as_ptr() as usize as u64 ^ ptr
}
fn pointer_a(mut s: [u64], seed: u64) -> u64 {
    alter(&mut s, seed);
    fold(&s, seed)
}
fn pointer_b(mut s: [u64], seed: u64) -> u64 {
    alter(&mut s, !seed);
    fold(&s, !seed)
}
struct Impl(u64);
impl Sink for Impl {
    fn consume(&self, mut s: [u64], seed: u64) -> u64 {
        let salt = self.0 ^ seed;
        alter(&mut s, salt);
        fold(&s, salt)
    }
}
fn main() {
    let mut checks = 0u64;
    for seed in 0..128u64 {
        let words = core::array::from_fn::<_, 40, _>(|i| {
            seed.wrapping_mul(0x9e3779b97f4a7c15) ^ (i as u64).wrapping_mul(0xd6e8feb86659fd93)
        });
        let wides = core::array::from_fn::<_, 40, _>(|i| Wide {
            a: words[i],
            b: words[i].rotate_left(23),
        });
        for len in 0..=32usize {
            let start = seed as usize % 8;
            let before = LIVE.load(Ordering::SeqCst);
            {
                let salt = seed ^ !seed;
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(unsafe { receive0(*b, seed, !seed) }, expected, "receive0");
                checks += 1;
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(unsafe { send0(*b, seed) }, expected, "send0");
                checks += 1;
            }
            {
                let salt = seed ^ !seed ^ seed.wrapping_add(79225).wrapping_mul(3);
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(
                    unsafe { receive1(seed.wrapping_add(79225), *b, seed, !seed) },
                    expected,
                    "receive1"
                );
                checks += 1;
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(unsafe { send1(*b, seed) }, expected, "send1");
                checks += 1;
            }
            {
                let salt = seed
                    ^ !seed
                    ^ seed.wrapping_add(79225).wrapping_mul(3)
                    ^ seed.wrapping_add(79302).wrapping_mul(5);
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(
                    unsafe {
                        receive2(
                            seed.wrapping_add(79225),
                            seed.wrapping_add(79302),
                            *b,
                            seed,
                            !seed,
                        )
                    },
                    expected,
                    "receive2"
                );
                checks += 1;
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(unsafe { send2(*b, seed) }, expected, "send2");
                checks += 1;
            }
            {
                let salt = seed
                    ^ !seed
                    ^ seed.wrapping_add(79225).wrapping_mul(3)
                    ^ seed.wrapping_add(79302).wrapping_mul(5)
                    ^ seed.wrapping_add(79379).wrapping_mul(7);
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(
                    unsafe {
                        receive3(
                            seed.wrapping_add(79225),
                            seed.wrapping_add(79302),
                            seed.wrapping_add(79379),
                            *b,
                            seed,
                            !seed,
                        )
                    },
                    expected,
                    "receive3"
                );
                checks += 1;
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(unsafe { send3(*b, seed) }, expected, "send3");
                checks += 1;
            }
            {
                let salt = seed
                    ^ !seed
                    ^ seed.wrapping_add(79225).wrapping_mul(3)
                    ^ seed.wrapping_add(79302).wrapping_mul(5)
                    ^ seed.wrapping_add(79379).wrapping_mul(7)
                    ^ seed.wrapping_add(79456).wrapping_mul(9);
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(
                    unsafe {
                        receive4(
                            seed.wrapping_add(79225),
                            seed.wrapping_add(79302),
                            seed.wrapping_add(79379),
                            seed.wrapping_add(79456),
                            *b,
                            seed,
                            !seed,
                        )
                    },
                    expected,
                    "receive4"
                );
                checks += 1;
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(unsafe { send4(*b, seed) }, expected, "send4");
                checks += 1;
            }
            {
                let salt = seed
                    ^ !seed
                    ^ seed.wrapping_add(79225).wrapping_mul(3)
                    ^ seed.wrapping_add(79302).wrapping_mul(5)
                    ^ seed.wrapping_add(79379).wrapping_mul(7)
                    ^ seed.wrapping_add(79456).wrapping_mul(9)
                    ^ seed.wrapping_add(79533).wrapping_mul(11);
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(
                    unsafe {
                        receive5(
                            seed.wrapping_add(79225),
                            seed.wrapping_add(79302),
                            seed.wrapping_add(79379),
                            seed.wrapping_add(79456),
                            seed.wrapping_add(79533),
                            *b,
                            seed,
                            !seed,
                        )
                    },
                    expected,
                    "receive5"
                );
                checks += 1;
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(unsafe { send5(*b, seed) }, expected, "send5");
                checks += 1;
            }
            {
                let salt = seed
                    ^ !seed
                    ^ seed.wrapping_add(79225).wrapping_mul(3)
                    ^ seed.wrapping_add(79302).wrapping_mul(5)
                    ^ seed.wrapping_add(79379).wrapping_mul(7)
                    ^ seed.wrapping_add(79456).wrapping_mul(9)
                    ^ seed.wrapping_add(79533).wrapping_mul(11)
                    ^ seed.wrapping_add(79610).wrapping_mul(13);
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(
                    unsafe {
                        receive6(
                            seed.wrapping_add(79225),
                            seed.wrapping_add(79302),
                            seed.wrapping_add(79379),
                            seed.wrapping_add(79456),
                            seed.wrapping_add(79533),
                            seed.wrapping_add(79610),
                            *b,
                            seed,
                            !seed,
                        )
                    },
                    expected,
                    "receive6"
                );
                checks += 1;
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(unsafe { send6(*b, seed) }, expected, "send6");
                checks += 1;
            }
            {
                let salt = seed
                    ^ !seed
                    ^ seed.wrapping_add(79225).wrapping_mul(3)
                    ^ seed.wrapping_add(79302).wrapping_mul(5)
                    ^ seed.wrapping_add(79379).wrapping_mul(7)
                    ^ seed.wrapping_add(79456).wrapping_mul(9)
                    ^ seed.wrapping_add(79533).wrapping_mul(11)
                    ^ seed.wrapping_add(79610).wrapping_mul(13)
                    ^ seed.wrapping_add(79687).wrapping_mul(15);
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(
                    unsafe {
                        receive7(
                            seed.wrapping_add(79225),
                            seed.wrapping_add(79302),
                            seed.wrapping_add(79379),
                            seed.wrapping_add(79456),
                            seed.wrapping_add(79533),
                            seed.wrapping_add(79610),
                            seed.wrapping_add(79687),
                            *b,
                            seed,
                            !seed,
                        )
                    },
                    expected,
                    "receive7"
                );
                checks += 1;
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(unsafe { send7(*b, seed) }, expected, "send7");
                checks += 1;
            }
            {
                let salt = seed
                    ^ !seed
                    ^ seed.wrapping_add(79225).wrapping_mul(3)
                    ^ seed.wrapping_add(79302).wrapping_mul(5)
                    ^ seed.wrapping_add(79379).wrapping_mul(7)
                    ^ seed.wrapping_add(79456).wrapping_mul(9)
                    ^ seed.wrapping_add(79533).wrapping_mul(11)
                    ^ seed.wrapping_add(79610).wrapping_mul(13)
                    ^ seed.wrapping_add(79687).wrapping_mul(15)
                    ^ seed.wrapping_add(79764).wrapping_mul(17);
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(
                    unsafe {
                        receive8(
                            seed.wrapping_add(79225),
                            seed.wrapping_add(79302),
                            seed.wrapping_add(79379),
                            seed.wrapping_add(79456),
                            seed.wrapping_add(79533),
                            seed.wrapping_add(79610),
                            seed.wrapping_add(79687),
                            seed.wrapping_add(79764),
                            *b,
                            seed,
                            !seed,
                        )
                    },
                    expected,
                    "receive8"
                );
                checks += 1;
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(unsafe { send8(*b, seed) }, expected, "send8");
                checks += 1;
            }
            {
                let salt = seed
                    ^ !seed
                    ^ seed.wrapping_add(79225).wrapping_mul(3)
                    ^ seed.wrapping_add(79302).wrapping_mul(5)
                    ^ seed.wrapping_add(79379).wrapping_mul(7)
                    ^ seed.wrapping_add(79456).wrapping_mul(9)
                    ^ seed.wrapping_add(79533).wrapping_mul(11)
                    ^ seed.wrapping_add(79610).wrapping_mul(13)
                    ^ seed.wrapping_add(79687).wrapping_mul(15)
                    ^ seed.wrapping_add(79764).wrapping_mul(17)
                    ^ seed.wrapping_add(79841).wrapping_mul(19);
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(
                    unsafe {
                        receive9(
                            seed.wrapping_add(79225),
                            seed.wrapping_add(79302),
                            seed.wrapping_add(79379),
                            seed.wrapping_add(79456),
                            seed.wrapping_add(79533),
                            seed.wrapping_add(79610),
                            seed.wrapping_add(79687),
                            seed.wrapping_add(79764),
                            seed.wrapping_add(79841),
                            *b,
                            seed,
                            !seed,
                        )
                    },
                    expected,
                    "receive9"
                );
                checks += 1;
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(unsafe { send9(*b, seed) }, expected, "send9");
                checks += 1;
            }
            {
                let b = "αß€🙂Z".repeat(len).into_boxed_str();
                let bytes = b.as_bytes();
                let mut expected = seed ^ bytes.len() as u64;
                for &v in bytes {
                    expected = expected.wrapping_mul(257).wrapping_add(v as u64);
                }
                expected ^= bytes.as_ptr() as usize as u64;
                assert_eq!(unsafe { owned_text(*b, seed) }, expected);
                checks += 1;
            }
            {
                let b = wides[start..start + len].to_vec().into_boxed_slice();
                let mut expected = seed ^ len as u64;
                for v in &*b {
                    expected = expected.wrapping_mul(257).wrapping_add(v.a ^ v.b);
                }
                expected ^= b.as_ptr() as usize as u64;
                assert_eq!(unsafe { owned_wide(*b, seed) }, expected);
                checks += 1;
            }
            {
                let b = vec![Zero; len].into_boxed_slice();
                let expected = seed ^ len as u64 ^ b.as_ptr() as usize as u64;
                assert_eq!(unsafe { owned_zero(*b, seed) }, expected);
                checks += 1;
            }
            for (f, salt) in [
                (pointer_a as fn([u64], u64) -> u64, seed),
                (pointer_b as fn([u64], u64) -> u64, !seed),
            ] {
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, salt);
                assert_eq!(unsafe { through_pointer(f, *b, seed) }, expected);
                checks += 1;
            }
            {
                let t = Impl(seed ^ 0xfedcba9876543210);
                let b = words[start..start + len].to_vec().into_boxed_slice();
                let expected = expected_words(&b, t.0 ^ seed);
                assert_eq!(unsafe { through_virtual(&t, *b, seed) }, expected);
                checks += 1;
            }
            assert_eq!(
                LIVE.load(Ordering::SeqCst),
                before,
                "owned buffers leaked or freed twice"
            );
            checks += 1;
        }
    }
    assert_eq!(checks, 114048);
    println!("PASS unsized_arguments checks={checks}");
}
