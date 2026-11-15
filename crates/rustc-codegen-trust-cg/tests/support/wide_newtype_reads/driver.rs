use core::ptr::NonNull;
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Wrapped(NonNull<[u32]>);
unsafe extern "C" {
    fn nonnull_str(data: *mut u8, len: usize, index: usize) -> u64;
    fn load_str_slot(slot: *const NonNull<str>, index: usize) -> u64;
    fn load_slice_slot(slot: *const NonNull<[u32]>, index: usize) -> u64;
    fn load_wrapped_slot(slot: *const Wrapped, index: usize) -> u64;
}
#[repr(C)]
struct Guarded<T> {
    before: u64,
    value: T,
    after: u64,
}
fn main() {
    let mut checks = 0;
    let bytes: [u8; 36] = core::array::from_fn(|i| b'a' + (i % 26) as u8);
    let words: [u32; 36] =
        core::array::from_fn(|i| (i as u32).wrapping_mul(0x1234567) ^ 0xdeadbeef);
    for len in 0..=32 {
        let ss = NonNull::from(core::str::from_utf8(&bytes[2..2 + len]).unwrap());
        let us = NonNull::from(&words[2..2 + len]);
        let slot_s = Guarded {
            before: 0x12345678,
            value: ss,
            after: 0xfeedface,
        };
        let slot_u = Guarded {
            before: 0xaabbccdd,
            value: us,
            after: 0xdead0123,
        };
        let slot_w = Guarded {
            before: 0x77778888,
            value: Wrapped(us),
            after: 0xabcdef12,
        };
        for index in 0..=len {
            let es = ((len as u64) << 32)
                | if index < len {
                    bytes[2 + index] as u64
                } else {
                    0
                };
            let eu = ((len as u64) << 32)
                | if index < len {
                    words[2 + index] as u64
                } else {
                    0
                };
            assert_eq!(unsafe { load_str_slot(&slot_s.value, index) }, es);
            checks += 1;
            assert_eq!(unsafe { load_slice_slot(&slot_u.value, index) }, eu);
            checks += 1;
            assert_eq!(unsafe { load_wrapped_slot(&slot_w.value, index) }, eu);
            checks += 1;
            assert_eq!((slot_s.before, slot_s.after), (0x12345678, 0xfeedface));
            checks += 1;
            assert_eq!((slot_u.before, slot_u.after), (0xaabbccdd, 0xdead0123));
            checks += 1;
            assert_eq!((slot_w.before, slot_w.after), (0x77778888, 0xabcdef12));
            checks += 1;
            assert_eq!(slot_s.value.as_ptr(), ss.as_ptr());
            checks += 1;
            assert_eq!(slot_u.value.as_ptr(), us.as_ptr());
            checks += 1;
            assert_eq!(slot_w.value.0.as_ptr(), us.as_ptr());
            checks += 1;
        }
    }
    for len in 1..=32 {
        for index in 0..len {
            let mut data = bytes;
            assert_eq!(
                unsafe { nonnull_str(data.as_mut_ptr().add(2), len, index) },
                ((len as u64) << 32) | bytes[2 + index] as u64
            );
            checks += 1;
            assert_eq!(data, bytes);
            checks += 1;
        }
    }
    println!("PASS wide_newtype_read checks={checks}");
}
