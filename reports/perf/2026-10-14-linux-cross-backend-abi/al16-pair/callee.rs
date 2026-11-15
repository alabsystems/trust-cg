#![crate_type = "rlib"]
#![crate_name = "al16bcallee"]

// 16 bytes, repr(align(16)); its natural (unadjusted) alignment is 8.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct Al16 {
    pub a: u64,
    pub b: u64,
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn take_al16(p0: u64, p1: Al16, p2: u64) -> u64 {
    p0 * 1_000_000 + p1.a * 10_000 + p1.b * 100 + p2
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn give_al16(p0: u64, p1: Al16) -> Al16 {
    Al16 { a: p0 + p1.b, b: p1.a * 2 }
}
