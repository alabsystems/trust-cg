#![no_std]
#![feature(coerce_unsized, unsize)]
use core::{
    marker::{PhantomData, Unsize},
    ops::CoerceUnsized,
    ptr::NonNull,
    sync::atomic::{AtomicUsize, Ordering},
};
#[repr(transparent)]
pub struct Ptr<T: ?Sized>(pub NonNull<T>);
impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<Ptr<U>> for Ptr<T> {}
pub struct Owner<T: ?Sized>(pub PhantomData<T>, pub NonNull<T>, pub ());
impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<Owner<U>> for Owner<T> {}
#[repr(C)]
pub struct Tail<T: ?Sized> {
    pub tag: u64,
    pub items: T,
}
pub trait Left {
    fn left(&self) -> u64;
}
pub trait Right {
    fn right(&self) -> u64;
}
pub trait Both: Left + Right {
    fn both(&self) -> u64;
}
pub struct Value(pub u64);
impl Left for Value {
    fn left(&self) -> u64 {
        self.0.wrapping_mul(13)
    }
}
impl Right for Value {
    fn right(&self) -> u64 {
        self.0.rotate_left(9)
    }
}
impl Both for Value {
    fn both(&self) -> u64 {
        self.0 ^ 0x1234abcd5678
    }
}
pub static DROPS: AtomicUsize = AtomicUsize::new(0);
impl Drop for Value {
    fn drop(&mut self) {
        DROPS.fetch_add(1, Ordering::Relaxed);
    }
}
pub static NUMS: [u64; 7] = [1, 9, 0, u64::MAX, 98765, 0x123456789abcdef, 17];
