// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg(target_arch = "aarch64")]
mod compiler;

#[test]
fn common_copy_preflight_keeps_exact_byte_and_lane_refusals() {
    // These are byte-image contract controls, not fabricated rustc layouts
    // or native ABI evidence. Actual compiler layouts are tested below.
    let mut layout = MemoryAggregateLayout {
        slot_ty: memory_slot_lane_ty(16, 8).unwrap(),
        size: 16,
        align: 8,
        tag: None,
        has_fat_pointer_leaf: false,
        has_nested_enum_leaf: false,
        has_nested_niche_enum_leaf: false,
    };
    assert!(byte_copy_shape(&layout).is_ok());
    assert!(lane_copy_shape(&layout).is_ok());
    layout.size = 15;
    assert_eq!(
        byte_copy_shape(&layout).unwrap_err(),
        "[TCG-SRET-ABI] aggregate buffer of 15 bytes does not tile into 8-byte lanes; failing closed rather than copying a partial trailing lane."
    );
    let error = lane_copy_shape(&layout)
        .err()
        .expect("non-covering lane image");
    assert!(error.starts_with("[TCG-ARG-ABI] the 15-byte / align-8 slot "));
    assert!(error.ends_with("is not a uniform tuple of 8-byte lanes, so a lane copy would not reproduce its bytes; failing closed"));
}
