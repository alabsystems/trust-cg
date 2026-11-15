#[repr(C)]
pub struct Ordered { pub small: u8, pub wide: u64 }
pub struct Reordered { pub small: u8, pub wide: u64 }
#[repr(C, packed)]
pub struct Packed { pub small: u8, pub wide: u64 }
#[repr(C)]
pub struct Nested { pub values: [u64; 2], pub last: u64 }
fn main() {
    use std::mem::{size_of, align_of, offset_of};
    println!("ordered {} {} {} {}", size_of::<Ordered>(), align_of::<Ordered>(), offset_of!(Ordered, small), offset_of!(Ordered, wide));
    println!("reordered {} {} {} {}", size_of::<Reordered>(), align_of::<Reordered>(), offset_of!(Reordered, small), offset_of!(Reordered, wide));
    println!("packed {} {} {} {}", size_of::<Packed>(), align_of::<Packed>(), offset_of!(Packed, small), offset_of!(Packed, wide));
    println!("nested {} {} {} {}", size_of::<Nested>(), align_of::<Nested>(), offset_of!(Nested, values), offset_of!(Nested, last));
}
