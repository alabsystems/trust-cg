// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
extern crate scalar_zst_field_fixture;
use scalar_zst_field_fixture::*;
use std::sync::atomic::{AtomicUsize, Ordering};

static CALLBACK_CHECKS: AtomicUsize = AtomicUsize::new(0);
static ADDRESS_OBSERVATIONS: AtomicUsize = AtomicUsize::new(0);
static EXPECTED_OFFSET: AtomicUsize = AtomicUsize::new(usize::MAX);
static EXPECTED_ALIGN: AtomicUsize = AtomicUsize::new(0);

#[unsafe(no_mangle)]
pub extern "C" fn scalar_zst_address_flags(
    base: usize,
    raw: usize,
    repeated: usize,
    shared: usize,
    mutable: usize,
    offset: usize,
    align: usize,
) -> u64 {
    assert_eq!(offset, EXPECTED_OFFSET.load(Ordering::Relaxed));
    assert_eq!(align, EXPECTED_ALIGN.load(Ordering::Relaxed));
    ADDRESS_OBSERVATIONS.fetch_add(1, Ordering::Relaxed);
    u64::from(raw.wrapping_sub(base) == offset)
        | (u64::from(raw == repeated) << 1)
        | (u64::from(raw == shared) << 2)
        | (u64::from(raw == mutable) << 3)
        | (u64::from(raw % align == 0) << 4)
}

macro_rules! flags {
    ($offset:expr, $align:expr, $call:expr) => {{
        EXPECTED_OFFSET.store($offset, Ordering::Relaxed);
        EXPECTED_ALIGN.store($align, Ordering::Relaxed);
        assert_eq!($call, 31);
    }};
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn scalar_zst_replace(
    cell: *mut *mut u64,
    marker: *const core::ffi::c_void,
    replacement: *mut u64,
) {
    assert_eq!(marker as usize - cell as usize, 8);
    assert_eq!(cell as usize % core::mem::align_of::<*mut u64>(), 0);
    CALLBACK_CHECKS.fetch_add(2, Ordering::Relaxed);
    unsafe { *cell = replacement };
}

fn main() {
    // This LLVM-only caller derives layouts independently of the bridge's
    // address producer and checks both pointer observations and value aliases.
    assert_eq!(core::mem::size_of::<Marker>(), 0);
    assert_eq!(core::mem::align_of::<Marker>(), 1);
    assert_eq!(core::mem::size_of::<IntegerTail>(), 8);
    assert_eq!(core::mem::offset_of!(IntegerTail, marker), 8);
    assert_eq!(core::mem::size_of::<IntegerHead>(), 8);
    assert_eq!(core::mem::offset_of!(IntegerHead, marker), 0);
    assert_eq!(core::mem::size_of::<PointerTail>(), 8);
    assert_eq!(core::mem::offset_of!(PointerTail, marker), 8);
    assert_eq!(core::mem::offset_of!(Wrapped<IntegerTail>, inner), 0);
    assert_eq!(core::mem::offset_of!(Wrapped<PointerTail>, inner), 0);
    assert_eq!(core::mem::size_of::<Padded>(), 64);
    assert_eq!(core::mem::align_of::<Padded>(), 64);
    assert_eq!(core::mem::offset_of!(Padded, marker), 64);
    let item_owner = FunctionItem {
        value: 0,
        marker: marker_function,
    };
    assert_eq!(core::mem::size_of_val(&item_owner.marker), 0);
    assert_eq!(core::mem::align_of_val(&item_owner.marker), 1);
    assert_eq!(
        core::ptr::addr_of!(item_owner.marker) as usize - core::ptr::addr_of!(item_owner) as usize,
        8
    );
    let mut checks = 0;
    for value in [0_u64, 1, u64::MAX, 0x8000_0000_0000_0000, 0x1379_2468] {
        let mut left = value;
        let mut right = value.wrapping_add(17);
        flags!(
            core::mem::offset_of!(IntegerTail, marker),
            core::mem::align_of::<Marker>(),
            integer_tail(value)
        );
        flags!(
            core::mem::offset_of!(IntegerHead, marker),
            core::mem::align_of::<Marker>(),
            integer_head(value)
        );
        flags!(
            core::mem::offset_of!(IntegerTail, marker),
            core::mem::align_of::<Marker>(),
            nested_integer_tail(value)
        );
        flags!(
            core::mem::offset_of!(PointerTail, marker),
            core::mem::align_of::<Marker>(),
            pointer_tail(&mut left)
        );
        flags!(
            core::mem::offset_of!(PointerTail, marker),
            core::mem::align_of::<Marker>(),
            nested_pointer_tail(&mut left)
        );
        flags!(
            core::mem::offset_of!(IntegerTail, marker),
            core::mem::align_of::<Marker>(),
            reference_only(value)
        );
        flags!(
            core::mem::offset_of!(Padded, marker),
            core::mem::align_of::<AlignedMarker>(),
            padded(value)
        );
        flags!(8, 1, function_item(value));
        assert_eq!(integer_alias(value), value.wrapping_add(5));
        assert_eq!(pointer_alias(&mut left, &mut right), right);
        assert_eq!(
            left, value,
            "changing the pointer field must not write its old pointee"
        );
        checks += 11;
    }
    let callback_checks = CALLBACK_CHECKS.load(Ordering::Relaxed);
    assert_eq!(callback_checks, 10);
    checks += 1;
    let address_observations = ADDRESS_OBSERVATIONS.load(Ordering::Relaxed);
    assert_eq!(
        address_observations, 40,
        "each field address must reach the LLVM observer"
    );
    checks += 1;
    println!(
        "SCALAR_ZST_FIELD checks={checks} layouts=16 callback_checks={callback_checks} address_observations={address_observations} offsets=0,8,64 refs=shared,mut raw=const,mut aliases=integer,pointer"
    );
}
