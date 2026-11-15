macro_rules! mutation {
    ($name:ident, $ty:ty) => {
        #[unsafe(no_mangle)]
        pub fn $name(value: &mut ($ty, bool), mask: $ty) {
            value.0 ^= mask;
            value.1 = !value.1;
        }
    };
}
mutation!(mutate_u128, u128);
mutation!(mutate_i128, i128);
mutation!(mutate_u64, u64);
mutation!(mutate_i64, i64);

macro_rules! operation {
    ($name:ident, $ty:ty, $method:ident) => {
        mod $name {
            unsafe extern "Rust" {
                #[link_name = concat!(stringify!($name), "_returned")]
                fn returned(a: $ty, b: $ty) -> ($ty, bool);
                #[link_name = concat!(stringify!($name), "_intrinsic")]
                fn intrinsic(a: $ty, b: $ty) -> ($ty, bool);
                #[link_name = concat!(stringify!($name), "_borrowed")]
                fn borrowed(a: $ty, b: $ty, mask: $ty) -> ($ty, bool);
                #[link_name = concat!(stringify!($name), "_folded")]
                fn folded(a: $ty, b: $ty) -> $ty;
            }
            pub fn check(a: u128, b: u128, mask: u128) -> usize {
                let (a, b, mask) = (a as $ty, b as $ty, mask as $ty);
                let expected = a.$method(b);
                unsafe {
                    assert_eq!(
                        returned(a, b),
                        expected,
                        "returned {} {a} {b}",
                        stringify!($name)
                    );
                    assert_eq!(
                        intrinsic(a, b),
                        expected,
                        "intrinsic {} {a} {b}",
                        stringify!($name)
                    );
                    assert_eq!(
                        borrowed(a, b, mask),
                        (expected.0 ^ mask, !expected.1),
                        "borrowed {} {a} {b}",
                        stringify!($name)
                    );
                    assert_eq!(
                        folded(a, b),
                        expected.0 ^ if expected.1 { !0 } else { 0 },
                        "folded {} {a} {b}",
                        stringify!($name)
                    );
                }
                4
            }
        }
    };
}
operation!(u128_add, u128, overflowing_add);
operation!(u128_sub, u128, overflowing_sub);
operation!(u128_mul, u128, overflowing_mul);
operation!(i128_add, i128, overflowing_add);
operation!(i128_sub, i128, overflowing_sub);
operation!(i128_mul, i128, overflowing_mul);
operation!(u64_add, u64, overflowing_add);
operation!(u64_sub, u64, overflowing_sub);
operation!(u64_mul, u64, overflowing_mul);
operation!(i64_add, i64, overflowing_add);
operation!(i64_sub, i64, overflowing_sub);
operation!(i64_mul, i64, overflowing_mul);

fn check(a: u128, b: u128) -> usize {
    let mask = a.rotate_left(17) ^ b.rotate_right(23) ^ 0xface_8765_0123_abcd;
    u128_add::check(a, b, mask)
        + u128_sub::check(a, b, mask)
        + u128_mul::check(a, b, mask)
        + i128_add::check(a, b, mask)
        + i128_sub::check(a, b, mask)
        + i128_mul::check(a, b, mask)
        + u64_add::check(a, b, mask)
        + u64_sub::check(a, b, mask)
        + u64_mul::check(a, b, mask)
        + i64_add::check(a, b, mask)
        + i64_sub::check(a, b, mask)
        + i64_mul::check(a, b, mask)
}
fn main() {
    let edges = [
        0,
        1,
        2,
        3,
        u64::MAX as u128,
        (1 << 64) + 1,
        u64::MAX as u128 - 1,
        1 << 63,
        (1 << 63) - 1,
        1 << 64,
        (1 << 127) - 1,
        1 << 127,
        (1 << 127) + 1,
        u128::MAX,
        u128::MAX - 1,
        1 << 126,
    ];
    let mut checks = 0;
    for a in edges {
        for b in edges {
            checks += check(a, b);
        }
    }
    let mut state = 0x91e10da5c79e7b1du64;
    let mut random = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state as u128
    };
    for index in 0..4096 {
        let a = (random() << 64) | random();
        let b = (random() << 64) | random();
        let (a, b) = match index % 8 {
            0 => (a, b),
            1 => (a as u64 as u128, b as u64 as u128),
            2 => (0u128.wrapping_sub(a as u64 as u128), b as u64 as u128),
            3 => ((1u128 << 127).wrapping_add(a & 3), u128::MAX),
            4 => (1 << (a % 128), 1 << (b % 128)),
            5 => (a, b & 1),
            6 => ((a << 64) | u64::MAX as u128, b & 3),
            _ => (a, a.wrapping_neg()),
        };
        checks += check(a, b);
    }
    assert_eq!(checks, 208896);
    println!("PASS wide_overflow_returns checks={checks}");
}
