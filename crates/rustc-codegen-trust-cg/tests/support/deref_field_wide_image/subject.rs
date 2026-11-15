//! Root-2 differential SUBJECT: compiled by the backend under test.
//! Every function stores (or drops) a `Box<[T]>` / `Box<str>` that sits in a
//! FIELD of an aggregate reached through a pointer: `(*r).f.. = move b`
//! (S1) and `drop_glue::<Box<[T]>>` (S2), the two shapes behind alloc root 2.
#![allow(clippy::missing_safety_doc)]

pub struct W { pub tag: u8, pub inner: Box<[u8]>, pub n: u32 }
pub struct WS { pub k: u16, pub inner: Box<str> }
pub struct W64 { pub inner: Box<[u64]>, pub z: u64 }
pub struct Outer { pub a: u64, pub w: W }

/// S1 + S2: `drop((*t).1); (*t).1 = move b` (the CString::clone_into store).
#[inline(never)]
pub fn set_field(t: &mut W, b: Box<[u8]>) { t.inner = b; }

/// S1 through a two-step field chain.
#[inline(never)]
pub fn set_nested(o: &mut Outer, b: Box<[u8]>) { o.w.inner = b; }

/// S1 + a read of the old image through the same pointer (mem::replace).
#[inline(never)]
pub fn replace_field(t: &mut W, b: Box<[u8]>) -> Box<[u8]> { core::mem::replace(&mut t.inner, b) }

/// S1 through a raw pointer (with the drop of the old value).
#[inline(never)]
pub unsafe fn set_raw(p: *mut W, b: Box<[u8]>) { unsafe { (*p).inner = b; } }

/// S1 through a raw pointer, no drop (`ptr::write`).
#[inline(never)]
pub unsafe fn write_raw(p: *mut W, b: Box<[u8]>) { unsafe { core::ptr::write(&raw mut (*p).inner, b); } }

/// `str` metadata (same Length kind).
#[inline(never)]
pub fn set_str(t: &mut WS, b: Box<str>) { t.inner = b; }

/// 8-byte elements: a wrong length lane is a wrong dealloc SIZE.
#[inline(never)]
pub fn set_u64(t: &mut W64, b: Box<[u64]>) { t.inner = b; }

/// S2 alone: rustc's `drop_glue::<Box<[u8]>>` on a by-value box.
#[inline(never)]
pub fn drop_box(b: Box<[u8]>) { drop(b) }

/// The clone_into body shape (else-branch): take the old box out, build a new
/// one of a DIFFERENT length, store it back through the pointer.
#[inline(never)]
pub fn regrow(t: &mut W, src: &[u8], make: fn(&[u8]) -> Box<[u8]>) {
    if t.inner.len() == src.len() {
        t.inner.copy_from_slice(src);
    } else {
        let old = core::mem::take(&mut t.inner);
        drop(old);
        t.inner = make(src);
    }
}
