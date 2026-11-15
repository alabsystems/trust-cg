#![no_std]
#![feature(lang_items, fundamental, ptr_internals, coerce_unsized, unsize)]
#![allow(internal_features)]
use core::{marker::Unsize, ops::CoerceUnsized, ptr::Unique};
// A crate-local owned_box lang item exercises rustc's actual Box drop glue,
// without the imported alloc Box interception or an LLVM alloc implementation.
#[lang = "owned_box"]
#[fundamental]
pub struct Box<T: ?Sized>(Unique<T>);
impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<Box<U>> for Box<T> {}
unsafe extern "C" {
    fn released(p: *mut u8, size: usize, align: usize);
    fn dropped(value: u64);
}
impl<T: ?Sized> Drop for Box<T> {
    fn drop(&mut self) {
        unsafe {
            let p = self.0.as_ptr();
            released(
                p as *mut u8,
                core::mem::size_of_val(&*p),
                core::mem::align_of_val(&*p),
            );
        }
    }
}
pub trait Value {
    fn value(&self) -> u64;
}
#[repr(C)]
pub struct Small(pub u64);
#[repr(C, align(64))]
pub struct Aligned(pub u64, pub u64);
#[repr(C)]
pub struct Plain(pub u64);
#[repr(align(32))]
pub struct Zero;
macro_rules! payload {
    ($t:ty) => {
        impl Value for $t {
            fn value(&self) -> u64 {
                self.0
            }
        }
    };
}
payload!(Small);
impl Value for Aligned {
    fn value(&self) -> u64 {
        self.0 ^ self.1
    }
}
payload!(Plain);
impl Value for Zero {
    fn value(&self) -> u64 {
        0xface1234
    }
}
impl Drop for Small {
    fn drop(&mut self) {
        unsafe { dropped(self.0) }
    }
}
impl Drop for Aligned {
    fn drop(&mut self) {
        unsafe { dropped(self.0 ^ self.1) }
    }
}
impl Drop for Zero {
    fn drop(&mut self) {
        unsafe { dropped(0xface1234) }
    }
}
macro_rules! destroy {
    ($name:ident,$t:ty) => {
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $name(p: *mut $t) {
            let owner: Box<dyn Value> = Box(unsafe { Unique::new_unchecked(p) });
            drop(owner);
        }
    };
}
destroy!(destroy_small, Small);
destroy!(destroy_aligned, Aligned);
destroy!(destroy_plain, Plain);
destroy!(destroy_zero, Zero);
#[unsafe(no_mangle)]
pub unsafe extern "C" fn destroy_slice(p: *mut [Plain; 7]) {
    let owner: Box<[Plain]> = Box(unsafe { Unique::new_unchecked(p) });
    drop(owner);
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn destroy_empty(p: *mut [Plain; 0]) {
    let owner: Box<[Plain]> = Box(unsafe { Unique::new_unchecked(p) });
    drop(owner);
}
