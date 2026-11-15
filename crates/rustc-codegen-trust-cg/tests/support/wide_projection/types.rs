#![no_std]
use core::{marker::PhantomData, ptr::NonNull};
#[repr(transparent)]
pub struct Ptr<T: ?Sized>(pub NonNull<T>);
impl<T: ?Sized> Copy for Ptr<T> {}
impl<T: ?Sized> Clone for Ptr<T> {
    fn clone(&self) -> Self {
        *self
    }
}
pub struct Owner<T: ?Sized>(pub (), pub Ptr<T>, pub PhantomData<T>);
impl<T: ?Sized> Copy for Owner<T> {}
impl<T: ?Sized> Clone for Owner<T> {
    fn clone(&self) -> Self {
        *self
    }
}
#[repr(C)]
pub struct Holder<T: ?Sized> {
    pub before: u8,
    pub item: Owner<T>,
    pub after: u64,
}
pub struct Outer<T: ?Sized> {
    pub top: u16,
    pub inner: Holder<T>,
    pub bottom: u8,
}
pub enum Choice<T: ?Sized> {
    Empty,
    Some {
        before: u8,
        item: Owner<T>,
        after: u64,
    },
}
pub trait Eval {
    fn eval(&self) -> u64;
}
pub struct A(pub u64);
pub struct B(pub u64);
impl Eval for A {
    fn eval(&self) -> u64 {
        self.0.wrapping_mul(13)
    }
}
impl Eval for B {
    fn eval(&self) -> u64 {
        self.0.rotate_left(17) ^ 0x123456789abcdef
    }
}
