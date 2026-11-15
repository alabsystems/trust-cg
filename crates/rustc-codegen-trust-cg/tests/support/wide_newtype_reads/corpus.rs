#![no_std]
use core::ptr::NonNull;
#[inline(never)]
unsafe fn inner(p: &NonNull<str>, index: usize) -> u64 {
    let s = unsafe { p.as_ref() };
    ((s.len() as u64) << 32) | s.as_bytes()[index] as u64
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nonnull_str(data: *mut u8, len: usize, index: usize) -> u64 {
    let raw = core::ptr::slice_from_raw_parts_mut(data, len) as *mut str;
    let p = unsafe { NonNull::new_unchecked(raw) };
    unsafe { inner(&p, index) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn load_str_slot(slot: *const NonNull<str>, index: usize) -> u64 {
    let p = unsafe { *slot };
    let s = unsafe { p.as_ref() };
    ((s.len() as u64) << 32)
        | if index < s.len() {
            s.as_bytes()[index] as u64
        } else {
            0
        }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn load_slice_slot(slot: *const NonNull<[u32]>, index: usize) -> u64 {
    let p = unsafe { *slot };
    let s = unsafe { p.as_ref() };
    ((s.len() as u64) << 32) | if index < s.len() { s[index] as u64 } else { 0 }
}
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct Wrapped(NonNull<[u32]>);
#[unsafe(no_mangle)]
pub unsafe extern "C" fn load_wrapped_slot(slot: *const Wrapped, index: usize) -> u64 {
    let p = unsafe { *slot };
    let s = unsafe { p.0.as_ref() };
    ((s.len() as u64) << 32) | if index < s.len() { s[index] as u64 } else { 0 }
}
