#![no_std]
use core::{fmt::Debug, marker::PhantomData, ptr::NonNull};
#[repr(C)]
pub struct Cursor<'a> {
    pub ptr: NonNull<&'a dyn Debug>,
    pub end_or_len: *const &'a dyn Debug,
    pub marker: PhantomData<&'a &'a dyn Debug>,
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn next_debug<'a>(it: &mut Cursor<'a>) -> Option<&'a &'a dyn Debug> {
    let ptr = it.ptr;
    let end_or_len = it.end_or_len;
    unsafe {
        if ptr == core::mem::transmute::<*const &dyn Debug, NonNull<&dyn Debug>>(end_or_len) {
            return None;
        }
        it.ptr = ptr.add(1);
        Some(local_as_ref(ptr))
    }
}

#[inline(never)]
unsafe fn local_as_ref<'a>(ptr: NonNull<&'a dyn Debug>) -> &'a &'a dyn Debug {
    unsafe { &*ptr.as_ptr() }
}
