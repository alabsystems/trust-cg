// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
#![no_std]

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Inner {
    pub first: i64,
    pub second: u32,
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Outer {
    pub inner: Inner,
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct OffsetOuter {
    pub prefix: u64,
    pub inner: Inner,
    pub suffix: u8,
}

#[inline(never)]
fn read_inner(value: &Inner) -> u64 {
    value.first as u64 ^ u64::from(value.second)
}

// At O0 this retains the two real MIR borrows:
// `_outer = &((_value as Some).0); _inner = &((*_outer).0)`.
// The first producer must bind its byte address with `_outer`'s mapped type;
// the second borrow must keep the adapter's actual-source-type check.
#[inline(never)]
pub fn borrowed_payload(value: Option<Outer>) -> u64 {
    match value {
        Some(ref outer) => {
            let inner = &outer.inner;
            read_inner(inner)
        }
        None => 0x77,
    }
}

#[inline(never)]
pub fn borrowed_offset_payload(value: Option<OffsetOuter>) -> u64 {
    match value {
        Some(ref outer) => {
            let inner = &outer.inner;
            read_inner(inner) ^ outer.prefix ^ u64::from(outer.suffix)
        }
        None => 0x88,
    }
}

#[inline(never)]
pub fn borrowed_mutable_payload(mut value: Option<Outer>) -> u64 {
    match value {
        Some(ref mut outer) => {
            let inner = &mut outer.inner;
            inner.first = inner.first.wrapping_add(17);
            inner.second = inner.second.wrapping_add(3);
            read_inner(inner)
        }
        None => 0x99,
    }
}

#[inline(never)]
pub fn field_identity(value: &Option<Outer>) -> bool {
    match value {
        Some(outer) => core::ptr::eq(&outer.inner, outer as *const Outer as *const Inner),
        None => true,
    }
}

#[inline(never)]
pub fn offset_field_identity(value: &Option<OffsetOuter>) -> bool {
    match value {
        Some(outer) => {
            let inner = &outer.inner as *const Inner as usize;
            let base = outer as *const OffsetOuter as usize;
            inner.wrapping_sub(base) == core::mem::offset_of!(OffsetOuter, inner)
        }
        None => true,
    }
}

// Independent typed entry-reference control; it is not a projected-payload
// address producer and must retain the same reference and field layout.
#[inline(never)]
pub fn entry_field(value: &Outer) -> u64 {
    read_inner(&value.inner)
}
