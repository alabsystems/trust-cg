#![no_std]
extern crate alloc;
use alloc::{boxed::Box, rc::Rc, sync::Arc};
use core::ptr::NonNull;
use pointer_coercion_types::*;
#[unsafe(no_mangle)]
pub fn ptr_slice(v: Ptr<[u64; 7]>) -> Ptr<[u64]> {
    v
}
#[unsafe(no_mangle)]
pub fn ptr_empty(v: Ptr<[u64; 0]>) -> Ptr<[u64]> {
    v
}
#[unsafe(no_mangle)]
pub fn ptr_zst(v: Ptr<[(); 17]>) -> Ptr<[()]> {
    v
}
#[unsafe(no_mangle)]
pub fn nonnull_slice(v: NonNull<[u64; 7]>) -> NonNull<[u64]> {
    v
}
#[unsafe(no_mangle)]
pub fn owner_slice(v: Owner<[u64; 7]>) -> Owner<[u64]> {
    v
}
#[unsafe(no_mangle)]
pub fn tail_slice(v: Ptr<Tail<[u64; 7]>>) -> Ptr<Tail<[u64]>> {
    v
}
#[unsafe(no_mangle)]
pub fn ptr_dyn(v: Ptr<Value>) -> Ptr<dyn Both + Send + Sync> {
    v
}
#[unsafe(no_mangle)]
pub fn ptr_auto(v: Ptr<dyn Both + Send + Sync>) -> Ptr<dyn Both> {
    v
}
#[unsafe(no_mangle)]
pub fn ptr_upcast(v: Ptr<dyn Both>) -> Ptr<dyn Right> {
    v
}
#[unsafe(no_mangle)]
pub fn tail_dyn(v: Ptr<Tail<Value>>) -> Ptr<Tail<dyn Both>> {
    v
}
#[unsafe(no_mangle)]
pub fn box_slice(v: Box<[u64; 7]>) -> Box<[u64]> {
    v
}
#[unsafe(no_mangle)]
pub fn rc_slice(v: Rc<[u64; 7]>) -> Rc<[u64]> {
    v
}
#[unsafe(no_mangle)]
pub fn arc_slice(v: Arc<[u64; 7]>) -> Arc<[u64]> {
    v
}
#[unsafe(no_mangle)]
pub fn box_dyn(v: Box<Value>) -> Box<dyn Both> {
    v
}
#[unsafe(no_mangle)]
pub fn rc_dyn(v: Rc<Value>) -> Rc<dyn Both> {
    v
}
#[unsafe(no_mangle)]
pub fn arc_dyn(v: Arc<Value>) -> Arc<dyn Both> {
    v
}
#[inline(never)]
fn pass(v: Ptr<[u64]>) -> Ptr<[u64]> {
    v
}
#[unsafe(no_mangle)]
pub fn ptr_via_call(v: Ptr<[u64; 7]>) -> Ptr<[u64]> {
    let p: Ptr<[u64]> = v;
    pass(p)
}
#[unsafe(no_mangle)]
pub fn const_empty() -> Owner<[u8]> {
    let p: Owner<[u8]> = Owner(
        core::marker::PhantomData,
        NonNull::<[u8; 0]>::dangling(),
        (),
    );
    p
}
#[unsafe(no_mangle)]
pub fn const_static() -> Ptr<[u64]> {
    Ptr(unsafe { NonNull::new_unchecked(core::ptr::addr_of!(NUMS).cast_mut()) })
}
