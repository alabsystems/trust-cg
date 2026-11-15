#![no_std]
extern crate wide_owner_types;
use wide_owner_types::*;
macro_rules! family {
    ($identity:ident, $relay:ident, $cycle:ident, $stack:ident, $call_stack:ident, $wrap:ident, $ty:ty) => {
        #[unsafe(no_mangle)]
        #[inline(never)]
        pub fn $wrap(value: $ty, callback: fn(&mut Envelope<$ty>)) -> $ty {
            let mut outer = Envelope {
                head: 11,
                owner: Carrier {
                    marker: core::marker::PhantomData,
                    value,
                },
                tail: 29,
            };
            callback(&mut outer);
            outer.owner.value
        }
        #[unsafe(no_mangle)]
        #[inline(never)]
        pub fn $identity(value: $ty) -> $ty {
            value
        }
        #[unsafe(no_mangle)]
        #[inline(never)]
        pub fn $relay(value: $ty, callback: fn($ty) -> $ty) -> $ty {
            callback(value)
        }
        #[unsafe(no_mangle)]
        #[inline(never)]
        pub fn $cycle(mut value: $ty, callback: fn($ty) -> $ty, n: usize) -> $ty {
            let mut i = 0;
            while i < n {
                value = callback(value);
                i = i.wrapping_add(1);
            }
            value
        }
        #[unsafe(no_mangle)]
        #[inline(never)]
        pub fn $call_stack(
            value: $ty,
            n: u64,
            result: &mut u64,
            callback: fn(u64, u64, u64, u64, u64, u64, u64, $ty, u64, &mut u64) -> $ty,
        ) -> $ty {
            callback(
                n,
                u64::MAX,
                0xdead_beef,
                23,
                0x8765_4321_fedc_ba98,
                0,
                19,
                value,
                0x8123,
                result,
            )
        }
        #[unsafe(no_mangle)]
        #[inline(never)]
        pub fn $stack(
            a: u64,
            b: u64,
            c: u64,
            d: u64,
            e: u64,
            f: u64,
            g: u64,
            value: $ty,
            suffix: u64,
            result: &mut u64,
            callback: fn($ty) -> $ty,
        ) -> $ty {
            let returned = callback(value);
            *result = a.rotate_left(1)
                ^ b.rotate_left(7)
                ^ c.rotate_left(13)
                ^ d.rotate_left(19)
                ^ e.rotate_left(23)
                ^ f.rotate_left(29)
                ^ g.rotate_left(31)
                ^ suffix.rotate_left(41);
            returned
        }
    };
}
family!(
    box_bytes,
    box_bytes_relay,
    box_bytes_cycle,
    box_bytes_stack,
    box_bytes_call_stack,
    box_bytes_wrap,
    Box<[u8]>
);
family!(
    box_words,
    box_words_relay,
    box_words_cycle,
    box_words_stack,
    box_words_call_stack,
    box_words_wrap,
    Box<[u64]>
);
family!(
    box_str,
    box_str_relay,
    box_str_cycle,
    box_str_stack,
    box_str_call_stack,
    box_str_wrap,
    Box<str>
);
family!(
    box_cstr,
    box_cstr_relay,
    box_cstr_cycle,
    box_cstr_stack,
    box_cstr_call_stack,
    box_cstr_wrap,
    Box<CStr>
);
family!(
    rc_bytes,
    rc_bytes_relay,
    rc_bytes_cycle,
    rc_bytes_stack,
    rc_bytes_call_stack,
    rc_bytes_wrap,
    Rc<[u8]>
);
family!(
    rc_words,
    rc_words_relay,
    rc_words_cycle,
    rc_words_stack,
    rc_words_call_stack,
    rc_words_wrap,
    Rc<[u64]>
);
family!(
    rc_str,
    rc_str_relay,
    rc_str_cycle,
    rc_str_stack,
    rc_str_call_stack,
    rc_str_wrap,
    Rc<str>
);
family!(
    arc_bytes,
    arc_bytes_relay,
    arc_bytes_cycle,
    arc_bytes_stack,
    arc_bytes_call_stack,
    arc_bytes_wrap,
    Arc<[u8]>
);
family!(
    arc_words,
    arc_words_relay,
    arc_words_cycle,
    arc_words_stack,
    arc_words_call_stack,
    arc_words_wrap,
    Arc<[u64]>
);
family!(
    arc_str,
    arc_str_relay,
    arc_str_cycle,
    arc_str_stack,
    arc_str_call_stack,
    arc_str_wrap,
    Arc<str>
);
family!(
    cstring,
    cstring_relay,
    cstring_cycle,
    cstring_stack,
    cstring_call_stack,
    cstring_wrap,
    CString
);

#[unsafe(no_mangle)]
pub fn borrowed_stack(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    value: &[u8],
    suffix: u64,
) -> u64 {
    a ^ b ^ c ^ d ^ e ^ f ^ g ^ suffix ^ value.len() as u64
}
#[unsafe(no_mangle)]
pub fn borrowed_call_stack(
    value: &[u8],
    callback: fn(u64, u64, u64, u64, u64, u64, u64, &[u8], u64) -> u64,
) -> u64 {
    callback(1, 2, 4, 8, 16, 32, 64, value, 128)
}
