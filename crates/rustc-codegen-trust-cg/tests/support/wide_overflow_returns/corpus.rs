#![no_std]
#![feature(core_intrinsics)]
#![allow(internal_features)]

unsafe extern "Rust" {
    fn mutate_u128(value: &mut (u128, bool), mask: u128);
    fn mutate_i128(value: &mut (i128, bool), mask: i128);
    fn mutate_u64(value: &mut (u64, bool), mask: u64);
    fn mutate_i64(value: &mut (i64, bool), mask: i64);
}

// Both public methods and direct intrinsic MIR must materialize the returned
// tuple. The callback observes and modifies a local through an LLVM-built alias.
// The folded variant retains the existing scalarized result path.
macro_rules! operation {
    ($name:ident, $ty:ty, $method:ident, $intrinsic:ident, $mutate:ident) => {
        mod $name {
            #[unsafe(export_name = concat!(stringify!($name), "_returned"))]
            pub fn returned(a: $ty, b: $ty) -> ($ty, bool) {
                a.$method(b)
            }
            #[unsafe(export_name = concat!(stringify!($name), "_intrinsic"))]
            pub fn intrinsic(a: $ty, b: $ty) -> ($ty, bool) {
                core::intrinsics::$intrinsic(a, b)
            }
            #[unsafe(export_name = concat!(stringify!($name), "_borrowed"))]
            pub fn borrowed(a: $ty, b: $ty, mask: $ty) -> ($ty, bool) {
                let mut value = a.$method(b);
                unsafe { super::$mutate(&mut value, mask) };
                value
            }
            #[unsafe(export_name = concat!(stringify!($name), "_folded"))]
            pub fn folded(a: $ty, b: $ty) -> $ty {
                let (value, overflow) = a.$method(b);
                value ^ if overflow { !0 } else { 0 }
            }
        }
    };
}
operation!(
    u128_add,
    u128,
    overflowing_add,
    add_with_overflow,
    mutate_u128
);
operation!(
    u128_sub,
    u128,
    overflowing_sub,
    sub_with_overflow,
    mutate_u128
);
operation!(
    u128_mul,
    u128,
    overflowing_mul,
    mul_with_overflow,
    mutate_u128
);
operation!(
    i128_add,
    i128,
    overflowing_add,
    add_with_overflow,
    mutate_i128
);
operation!(
    i128_sub,
    i128,
    overflowing_sub,
    sub_with_overflow,
    mutate_i128
);
operation!(
    i128_mul,
    i128,
    overflowing_mul,
    mul_with_overflow,
    mutate_i128
);
operation!(u64_add, u64, overflowing_add, add_with_overflow, mutate_u64);
operation!(u64_sub, u64, overflowing_sub, sub_with_overflow, mutate_u64);
operation!(u64_mul, u64, overflowing_mul, mul_with_overflow, mutate_u64);
operation!(i64_add, i64, overflowing_add, add_with_overflow, mutate_i64);
operation!(i64_sub, i64, overflowing_sub, sub_with_overflow, mutate_i64);
operation!(i64_mul, i64, overflowing_mul, mul_with_overflow, mutate_i64);
