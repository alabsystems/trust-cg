#![no_std]
use core::ptr::NonNull;
#[unsafe(no_mangle)]
pub unsafe extern "C" fn replace_slice(slot: *mut NonNull<[u32]>, data: *mut u32, len: usize) {
    let raw = core::ptr::slice_from_raw_parts_mut(data, len);
    unsafe {
        *slot = NonNull::new_unchecked(raw);
    }
}
