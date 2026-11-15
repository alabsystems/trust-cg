#![feature(f16)]
use core::arch::aarch64::{float16x4_t, float16x8_t};
unsafe extern "C" {
    fn array_mut4(p: *mut float16x4_t) -> *mut u16;
    fn array_mut8(p: *mut float16x8_t) -> *mut u16;
    fn offset16(p: *mut f16, index: usize) -> *mut u16;
    fn array4(p: *const float16x4_t) -> *const u16;
    fn array8(p: *const float16x8_t) -> *const u16;
}
#[repr(C, align(16))]
struct Guarded {
    before: [u16; 8],
    values: [u16; 8],
    after: [u16; 8],
}
fn main() {
    let mut checks = 0;
    for seed in 0..256u16 {
        let mut data = Guarded {
            before: [0x1357; 8],
            values: [0; 8],
            after: [0x9753; 8],
        };
        for i in 0..8 {
            data.values[i] = seed
                .wrapping_mul(257)
                .wrapping_add((i as u16).wrapping_mul(8191));
        }
        let copy = data.values;
        unsafe {
            let a = array4(data.values.as_ptr().cast());
            let b = array8(data.values.as_ptr().cast());
            assert_eq!(a, data.values.as_ptr());
            assert_eq!(b, data.values.as_ptr());
            checks += 2;
            for i in 0..4 {
                assert_eq!(*a.add(i), copy[i]);
                checks += 1;
            }
            for i in 0..8 {
                assert_eq!(*b.add(i), copy[i]);
                checks += 1;
            }
        }
        assert_eq!(data.before, [0x1357; 8]);
        assert_eq!(data.after, [0x9753; 8]);
        assert_eq!(data.values, copy);
        checks += 3;
        let mut expected = copy;
        unsafe {
            let a = array_mut4(data.values.as_mut_ptr().cast());
            let b = array_mut8(data.values.as_mut_ptr().cast());
            assert_eq!(a, data.values.as_mut_ptr());
            assert_eq!(b, data.values.as_mut_ptr());
            checks += 2;
            for i in 0..8 {
                let cell = offset16(data.values.as_mut_ptr().cast(), i);
                assert_eq!(cell, data.values.as_mut_ptr().add(i));
                assert_eq!(*cell, copy[i]);
                *cell = copy[i] ^ 0x7c01;
                expected[i] = copy[i] ^ 0x7c01;
                assert_eq!(*b.add(i), expected[i]);
                checks += 3;
            }
        }
        assert_eq!(data.before, [0x1357; 8]);
        assert_eq!(data.after, [0x9753; 8]);
        assert_eq!(data.values, expected);
        checks += 3;
    }
    println!("PASS f16_pointee_shell checks={checks}");
}
