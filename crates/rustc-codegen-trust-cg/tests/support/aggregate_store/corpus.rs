#![no_std]
use aggregate_store_types::*;
#[inline(never)]
fn assign<T>(dst: &mut T, src: T) {
    *dst = src;
}
macro_rules! case {
    ($name:ident,$ty:ty) => {
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $name(dst: *mut $ty, src: *const $ty, out: *mut $ty, mode: u8) {
            unsafe {
                match mode {
                    0 => assign(&mut *dst, *src),
                    1 => *dst = *src,
                    2 => *out = core::mem::replace(&mut *dst, *src),
                    3 => {
                        let value = *dst;
                        assign(&mut *dst, value)
                    }
                    _ => {
                        let old = core::ptr::read(dst);
                        core::ptr::write(dst, *src);
                        *out = old
                    }
                }
            }
        }
    };
}
case!(store_pad, Pad);
case!(store_nested, Nested);
case!(store_rustnested, RustNested);
case!(store_tuple, Tuple);
case!(store_array, Array);
case!(store_packed, Packed);
case!(store_wide, Wide);
case!(store_tagged, Tagged);
case!(store_niche, Niche);
case!(store_fat, Fat);
case!(store_zst, Zst);
case!(store_single, Single);
