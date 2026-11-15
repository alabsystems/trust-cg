#![no_std]
mod types;
use types::Outer;
macro_rules! checked {
    ($name:ident, $ty:ty) => {
        #[unsafe(no_mangle)]
        pub fn $name(mut value: Outer<$ty>) -> Outer<$ty> {
            value.inner.hi = -value.inner.hi;
            value.inner.lo = -value.inner.lo;
            value
        }
    };
}
checked!(checked_i8, i8);
checked!(checked_i16, i16);
checked!(checked_i32, i32);
checked!(checked_i64, i64);
checked!(checked_i128, i128);
