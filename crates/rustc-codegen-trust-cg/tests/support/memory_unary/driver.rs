mod types;
use types::{Outer, Pair};
macro_rules! operation {
    ($name:ident, $ty:ty, $method:ident) => {
        mod $name {
            use super::{Outer, Pair};
            #[allow(unused_imports)]
            use std::ops::Not;
            unsafe extern "Rust" {
                #[link_name = concat!(stringify!($name), "_scalar")]
                fn scalar(value: $ty) -> $ty;
                #[link_name = concat!(stringify!($name), "_pair")]
                fn pair(value: Pair<$ty>) -> Pair<$ty>;
                #[link_name = concat!(stringify!($name), "_borrowed")]
                fn borrowed(value: Outer<$ty>) -> Outer<$ty>;
                #[link_name = concat!(stringify!($name), "_through")]
                fn through(value: &mut Outer<$ty>);
            }
            static mut EXPECTED: Outer<$ty> = Outer {
                lead: 0,
                inner: Pair { hi: 0, lo: 0 },
                tail: 0,
            };
            static mut OBSERVED: u64 = 0;
            fn oracle(x: $ty) -> $ty {
                x.$method()
            }
            #[unsafe(export_name = concat!(stringify!($name), "_observe"))]
            fn observe(value: &mut Outer<$ty>) {
                let expected = unsafe { EXPECTED };
                assert_eq!(
                    value.lead,
                    expected.lead,
                    "{} assertion 1",
                    stringify!($name)
                );
                assert_eq!(
                    value.inner.hi,
                    expected.inner.hi,
                    "{} assertion 2",
                    stringify!($name)
                );
                assert_eq!(
                    value.inner.lo,
                    oracle(expected.inner.lo),
                    "{} assertion 3",
                    stringify!($name)
                );
                assert_eq!(
                    value.tail,
                    expected.tail,
                    "{} assertion 4",
                    stringify!($name)
                );
                value.inner.hi ^= 0x55;
                value.lead ^= 0x5a;
                value.tail ^= 0x195a_3d87_12be_a530;
                unsafe {
                    OBSERVED += 1;
                }
            }
            pub fn test(x: u128, y: u128) -> u64 {
                let a = x as $ty;
                let b = y as $ty;
                assert_eq!(
                    unsafe { scalar(a) },
                    oracle(a),
                    "{} assertion 5",
                    stringify!($name)
                );
                let out = unsafe { pair(Pair { hi: a, lo: b }) };
                assert_eq!(out.hi, oracle(a), "{} assertion 6", stringify!($name));
                assert_eq!(out.lo, oracle(b), "{} assertion 7", stringify!($name));
                let input = Outer {
                    lead: (x >> 48) as u8,
                    inner: Pair { hi: a, lo: b },
                    tail: (y >> 32) as u64,
                };
                let before = unsafe {
                    EXPECTED = input;
                    OBSERVED
                };
                let out = unsafe { borrowed(input) };
                assert_eq!(
                    unsafe { OBSERVED },
                    before + 1,
                    "{} assertion 8",
                    stringify!($name)
                );
                assert_eq!(
                    out.lead,
                    input.lead ^ 0x5a,
                    "{} assertion 9",
                    stringify!($name)
                );
                assert_eq!(
                    out.inner.hi,
                    oracle(a ^ 0x55),
                    "{} assertion 10",
                    stringify!($name)
                );
                assert_eq!(
                    out.inner.lo,
                    oracle(b),
                    "{} assertion 11",
                    stringify!($name)
                );
                assert_eq!(
                    out.tail,
                    input.tail ^ 0x195a_3d87_12be_a530,
                    "{} assertion 12",
                    stringify!($name)
                );
                let mut out = input;
                unsafe {
                    through(&mut out);
                }
                assert_eq!(out.lead, input.lead, "{} assertion 13", stringify!($name));
                assert_eq!(
                    out.inner.hi,
                    oracle(a),
                    "{} assertion 14",
                    stringify!($name)
                );
                assert_eq!(
                    out.inner.lo,
                    oracle(b),
                    "{} assertion 15",
                    stringify!($name)
                );
                assert_eq!(out.tail, input.tail, "{} assertion 16", stringify!($name));
                16 // Twelve caller assertions and four callback assertions.
            }
        }
    };
}
operation!(not_u8, u8, not);
operation!(not_i8, i8, not);
operation!(not_u16, u16, not);
operation!(not_i16, i16, not);
operation!(not_u32, u32, not);
operation!(not_i32, i32, not);
operation!(not_u64, u64, not);
operation!(not_i64, i64, not);
operation!(not_u128, u128, not);
operation!(not_i128, i128, not);
operation!(neg_i8, i8, wrapping_neg);
operation!(neg_i16, i16, wrapping_neg);
operation!(neg_i32, i32, wrapping_neg);
operation!(neg_i64, i64, wrapping_neg);
operation!(neg_i128, i128, wrapping_neg);
fn main() {
    let mut checks = 0u64;
    let mut value = |x, y| {
        checks += not_u8::test(x, y)
            + not_i8::test(x, y)
            + not_u16::test(x, y)
            + not_i16::test(x, y)
            + not_u32::test(x, y)
            + not_i32::test(x, y)
            + not_u64::test(x, y)
            + not_i64::test(x, y)
            + not_u128::test(x, y)
            + not_i128::test(x, y)
            + neg_i8::test(x, y)
            + neg_i16::test(x, y)
            + neg_i32::test(x, y)
            + neg_i64::test(x, y)
            + neg_i128::test(x, y);
    };
    for x in 0..65536u128 {
        value(x, !x);
    }
    for bit in 0..128 {
        for delta in -4i128..=4 {
            let x = (1u128 << bit).wrapping_add(delta as u128);
            value(x, x.rotate_left(49));
        }
    }
    let mut seed = 0x354c_c817_259d_fe81u64;
    for _ in 0..8192 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        let hi = seed;
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        let x = ((hi as u128) << 64) | seed as u128;
        value(x, x.rotate_left(71));
    }
    for x in 0..65536u64 {
        checks += small_test(x);
    }
    println!("PASS memory_unary checks={checks}");
}

unsafe extern "Rust" {
    fn small_calls(
        value: Outer<u8>,
        function: fn(Outer<u8>) -> u64,
        object: &dyn types::Observe,
    ) -> u64;
    fn small_spilled(
        a: u64,
        b: u64,
        c: u64,
        d: u64,
        e: u64,
        f: u64,
        g: u64,
        h: u64,
        value: Outer<u8>,
    ) -> u64;
}
fn score(v: Outer<u8>) -> u64 {
    v.tail ^ v.lead as u64 ^ (v.inner.hi as u64) << 8 ^ (v.inner.lo as u64) << 16
}
#[inline(never)]
#[unsafe(no_mangle)]
fn take_small(mut value: Outer<u8>) -> u64 {
    value.lead ^= 0x85;
    value.inner.hi = !value.inner.hi;
    value.inner.lo ^= 0x64;
    value.tail ^= 0x89274d918e61c5fa;
    std::hint::black_box(&mut value);
    score(value)
}
#[unsafe(no_mangle)]
fn take_small_spilled(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    h: u64,
    value: Outer<u8>,
) -> u64 {
    a ^ b ^ c ^ d ^ e ^ f ^ g ^ h ^ take_small(value)
}
struct Observer;
impl types::Observe for Observer {
    fn take(&self, value: Outer<u8>) -> u64 {
        take_small(value) ^ 0xa943278654198531
    }
}
fn small_test(x: u64) -> u64 {
    let value = Outer {
        lead: x as u8,
        inner: Pair {
            hi: (x >> 8) as u8,
            lo: !(x as u8),
        },
        tail: x.wrapping_mul(0x182749c918ab735a),
    };
    let mut mutated = value;
    mutated.lead ^= 0x85;
    mutated.inner.hi = !mutated.inner.hi;
    mutated.inner.lo ^= 0x64;
    mutated.tail ^= 0x89274d918e61c5fa;
    let t = score(mutated);
    let want = t
        ^ t.rotate_left(7)
        ^ (t ^ 0xa943278654198531).rotate_left(19)
        ^ (t ^ 255).rotate_left(31)
        ^ score(value);
    assert_eq!(
        unsafe { small_calls(value, take_small, &Observer) },
        want,
        "small direct/indirect/virtual arguments"
    );
    let mut complemented = value;
    complemented.inner.hi = !complemented.inner.hi;
    complemented.inner.lo = !complemented.inner.lo;
    assert_eq!(
        unsafe { small_spilled(1, 2, 4, 8, 16, 32, 64, 128, value) },
        score(complemented) ^ 255,
        "stack pointer argument"
    );
    2
}
