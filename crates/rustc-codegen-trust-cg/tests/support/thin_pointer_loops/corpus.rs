#![no_std]

use core::ptr::NonNull;

#[repr(transparent)]
struct Cursor(*mut u8);

#[unsafe(no_mangle)]
pub unsafe extern "C" fn nonnull_cursor(base: *mut u8, n: usize) -> *mut u8 {
    let mut p = unsafe { NonNull::new_unchecked(base) };
    let mut i = 0usize;
    while i < n {
        p = unsafe { p.add(1) };
        i += 1;
    }
    p.as_ptr()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn nonnull_sum(base: *mut u64, n: usize) -> u64 {
    let mut p = unsafe { NonNull::new_unchecked(base) };
    let mut sum = 0u64;
    let mut i = 0usize;
    while i < n {
        sum = sum.wrapping_add(unsafe { p.read() });
        p = unsafe { p.add(1) };
        i += 1;
    }
    sum
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn raw_write(mut p: *mut u8, n: usize) -> *mut u8 {
    let mut i = 0usize;
    while i < n {
        unsafe { p.write((i as u8).wrapping_mul(7)) };
        p = unsafe { p.add(1 + (i & 1)) };
        i += 1;
    }
    p
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn raw_reverse(mut p: *const u16, n: usize) -> u64 {
    let mut sum = 0u64;
    let mut i = 0usize;
    while i < n {
        p = unsafe { p.sub(1) };
        sum = sum.wrapping_add(unsafe { *p } as u64);
        i += 1;
    }
    sum
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wrapper_whole(base: *mut u8, n: usize) -> *mut u8 {
    let mut p = Cursor(base);
    let mut i = 0usize;
    while i < n {
        p = Cursor(unsafe { p.0.add(1) });
        i += 1;
    }
    p.0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn wrapper_field(base: *mut u8, n: usize) -> *mut u8 {
    let mut p = Cursor(base);
    let mut i = 0usize;
    while i < n {
        p.0 = unsafe { p.0.add(1) };
        i += 1;
    }
    p.0
}

// A fat pointer must keep both its moving data pointer and shrinking length.
// It cannot use the thin-pointer admission merely because its data is Ptr.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn slice_tail(base: *const u8, len: usize, n: usize) -> usize {
    let mut slice = unsafe { core::slice::from_raw_parts(base, len) };
    let mut i = 0usize;
    while i < n {
        slice = unsafe { core::slice::from_raw_parts(slice.as_ptr().add(1), slice.len() - 1) };
        i += 1;
    }
    slice
        .len()
        .wrapping_mul(257)
        .wrapping_add(unsafe { *slice.as_ptr() } as usize)
}
