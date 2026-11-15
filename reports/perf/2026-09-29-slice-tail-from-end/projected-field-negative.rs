#![no_std]
#[repr(C)]
pub struct Pair { pub a:u64, pub b:u64 }
#[repr(C)]
pub struct Head { pub marker:u64, pub tail:[Pair] }
#[unsafe(no_mangle)]
pub fn projected_last(data:&Head)->u64 {
    match &data.tail { [..,last]=>last.b,_=>data.marker }
}
