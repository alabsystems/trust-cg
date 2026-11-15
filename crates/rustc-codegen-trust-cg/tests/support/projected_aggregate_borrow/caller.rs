// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
extern crate projected_borrow_fixture;
use projected_borrow_fixture::{
    Inner, OffsetOuter, Outer, borrowed_mutable_payload, borrowed_offset_payload, borrowed_payload,
    entry_field, field_identity, offset_field_identity,
};

fn main() {
    // This caller always uses LLVM and independently checks real Rust layouts.
    assert_eq!(core::mem::size_of::<Inner>(), 16);
    assert_eq!(core::mem::align_of::<Inner>(), 8);
    assert_eq!(core::mem::offset_of!(Inner, first), 0);
    assert_eq!(core::mem::offset_of!(Inner, second), 8);
    assert_eq!(core::mem::size_of::<Outer>(), 16);
    assert_eq!(core::mem::align_of::<Outer>(), 8);
    assert_eq!(core::mem::offset_of!(Outer, inner), 0);
    assert_eq!(core::mem::size_of::<OffsetOuter>(), 32);
    assert_eq!(core::mem::align_of::<OffsetOuter>(), 8);
    assert_eq!(core::mem::offset_of!(OffsetOuter, prefix), 0);
    assert_eq!(core::mem::offset_of!(OffsetOuter, inner), 8);
    assert_eq!(core::mem::offset_of!(OffsetOuter, suffix), 24);
    assert_eq!(core::mem::size_of::<Option<Outer>>(), 24);
    assert_eq!(core::mem::align_of::<Option<Outer>>(), 8);
    assert_eq!(core::mem::size_of::<Option<OffsetOuter>>(), 40);
    assert_eq!(core::mem::align_of::<Option<OffsetOuter>>(), 8);
    let mut checked = 0;
    for (first, second) in [(i64::MIN, 5_u32), (-1, 17), (0, 0), (9, u32::MAX), (i64::MAX, 11)] {
        let outer = Outer { inner: Inner { first, second } };
        let offset = OffsetOuter { prefix: 0x1379_2468, inner: outer.inner, suffix: 0x5a };
        let expected = first as u64 ^ u64::from(second);
        assert_eq!(borrowed_payload(Some(outer)), expected);
        assert_eq!(borrowed_offset_payload(Some(offset)), expected ^ offset.prefix ^ u64::from(offset.suffix));
        assert_eq!(borrowed_mutable_payload(Some(outer)), first.wrapping_add(17) as u64 ^ u64::from(second.wrapping_add(3)));
        assert!(field_identity(&Some(outer)));
        assert!(offset_field_identity(&Some(offset)));
        assert_eq!(entry_field(&outer), expected);
        checked += 6;
    }
    assert_eq!(borrowed_payload(None), 0x77);
    assert_eq!(borrowed_offset_payload(None), 0x88);
    assert_eq!(borrowed_mutable_payload(None), 0x99);
    assert!(field_identity(&None));
    assert!(offset_field_identity(&None));
    checked += 5;
    println!("PROJECTED_AGGREGATE_BORROW checks={checked} layouts=16 some_none=both offsets=0,8 mutable=yes entry=yes");
}
