// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
#![no_std]

pub struct Marker;

#[repr(C)]
pub struct IntegerTail {
    pub value: u64,
    pub marker: Marker,
}

#[repr(C)]
pub struct IntegerHead {
    pub marker: Marker,
    pub value: u64,
}

#[repr(C)]
pub struct PointerTail {
    pub value: *mut u64,
    pub marker: Marker,
}

#[repr(transparent)]
pub struct Wrapped<T> {
    pub inner: T,
}

#[repr(align(64))]
pub struct AlignedMarker;

#[repr(C)]
pub struct Padded {
    pub value: u64,
    pub marker: AlignedMarker,
}

#[repr(C)]
pub struct FunctionItem<F> {
    pub value: u64,
    pub marker: F,
}

pub fn marker_function() {}

#[inline(never)]
pub fn function_item(value: u64) -> u64 {
    let mut owner = FunctionItem {
        value,
        marker: marker_function,
    };
    let base = core::ptr::addr_of!(owner) as usize;
    let raw = core::ptr::addr_of!(owner.marker) as usize;
    let repeated = core::ptr::addr_of_mut!(owner.marker) as usize;
    let shared = &owner.marker as *const _ as usize;
    let mutable = &mut owner.marker as *mut _ as usize;
    flags(base, raw, repeated, shared, mutable, 8, 1)
}

unsafe extern "C" {
    fn scalar_zst_address_flags(
        base: usize,
        raw: usize,
        repeated: usize,
        shared: usize,
        mutable: usize,
        offset: usize,
        align: usize,
    ) -> u64;
    fn scalar_zst_replace(
        cell: *mut *mut u64,
        marker: *const core::ffi::c_void,
        replacement: *mut u64,
    );
}

#[inline(never)]
fn flags(
    base: usize,
    raw: usize,
    repeated: usize,
    shared: usize,
    mutable: usize,
    offset: usize,
    align: usize,
) -> u64 {
    // All address observations are consumed by the independent LLVM caller.
    unsafe { scalar_zst_address_flags(base, raw, repeated, shared, mutable, offset, align) }
}

macro_rules! addresses {
    ($owner:ident, $($field:ident).+, $leaf:ty, $offset:expr) => {{
        let base = core::ptr::addr_of!($owner) as usize;
        let raw = core::ptr::addr_of!($owner.$($field).+) as usize;
        let repeated = core::ptr::addr_of_mut!($owner.$($field).+) as usize;
        let shared = &$owner.$($field).+ as *const $leaf as usize;
        let mutable = &mut $owner.$($field).+ as *mut $leaf as usize;
        flags(base, raw, repeated, shared, mutable, $offset, core::mem::align_of::<$leaf>())
    }};
}

#[inline(never)]
pub fn integer_tail(value: u64) -> u64 {
    let mut owner = IntegerTail {
        value,
        marker: Marker,
    };
    addresses!(
        owner,
        marker,
        Marker,
        core::mem::offset_of!(IntegerTail, marker)
    )
}

#[inline(never)]
pub fn integer_head(value: u64) -> u64 {
    let mut owner = IntegerHead {
        marker: Marker,
        value,
    };
    addresses!(
        owner,
        marker,
        Marker,
        core::mem::offset_of!(IntegerHead, marker)
    )
}

#[inline(never)]
pub fn nested_integer_tail(value: u64) -> u64 {
    let mut owner = Wrapped {
        inner: Wrapped {
            inner: IntegerTail {
                value,
                marker: Marker,
            },
        },
    };
    addresses!(
        owner,
        inner.inner.marker,
        Marker,
        core::mem::offset_of!(IntegerTail, marker)
    )
}

#[inline(never)]
pub fn pointer_tail(value: *mut u64) -> u64 {
    let mut owner = PointerTail {
        value,
        marker: Marker,
    };
    addresses!(
        owner,
        marker,
        Marker,
        core::mem::offset_of!(PointerTail, marker)
    )
}

#[inline(never)]
pub fn nested_pointer_tail(value: *mut u64) -> u64 {
    let mut owner = Wrapped {
        inner: Wrapped {
            inner: PointerTail {
                value,
                marker: Marker,
            },
        },
    };
    addresses!(
        owner,
        inner.inner.marker,
        Marker,
        core::mem::offset_of!(PointerTail, marker)
    )
}

#[inline(never)]
pub fn reference_only(value: u64) -> u64 {
    let mut owner = IntegerTail {
        value,
        marker: Marker,
    };
    let base = &owner as *const IntegerTail as usize;
    let shared = &owner.marker as *const Marker as usize;
    let repeated = &owner.marker as *const Marker as usize;
    let mutable = &mut owner.marker as *mut Marker as usize;
    flags(
        base,
        shared,
        repeated,
        shared,
        mutable,
        core::mem::offset_of!(IntegerTail, marker),
        1,
    )
}

#[inline(never)]
pub fn padded(value: u64) -> u64 {
    let mut owner = Padded {
        value,
        marker: AlignedMarker,
    };
    addresses!(
        owner,
        marker,
        AlignedMarker,
        core::mem::offset_of!(Padded, marker)
    )
}

#[inline(never)]
pub fn integer_alias(value: u64) -> u64 {
    let mut owner = IntegerTail {
        value,
        marker: Marker,
    };
    let marker = core::ptr::addr_of!(owner.marker);
    core::hint::black_box(marker);
    let cell = core::ptr::addr_of_mut!(owner.value);
    unsafe {
        *cell = value.wrapping_add(5);
    }
    owner.value
}

#[inline(never)]
pub fn pointer_alias(value: *mut u64, replacement: *mut u64) -> u64 {
    let mut owner = PointerTail {
        value,
        marker: Marker,
    };
    let marker = core::ptr::addr_of!(owner.marker);
    let cell = core::ptr::addr_of_mut!(owner.value);
    unsafe {
        // The LLVM caller checks both addresses, then changes the retained
        // pointer field. The direct field read must reload the same cell.
        scalar_zst_replace(cell, marker as *const core::ffi::c_void, replacement);
        *owner.value
    }
}
