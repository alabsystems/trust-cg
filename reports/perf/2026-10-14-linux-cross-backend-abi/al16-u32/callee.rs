#![crate_type = "rlib"]
#![crate_name = "al16callee"]

// 16 bytes, repr(align(16)), natural (unadjusted) alignment 4.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct Al16s {
    pub a: u32,
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn take_al16s(p0: u64, p1: Al16s, p2: u32) -> u64 {
    p0 * 1_000_000 + (p1.a as u64) * 1_000 + p2 as u64
}

// Eight u64 fill x0-x7: Al16s goes to the stack, then a u32 after it.
#[no_mangle]
#[inline(never)]
pub extern "C" fn take_al16s_stack(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64, a6: u64, a7: u64,
                                   p0: u8, p1: Al16s, p2: u32) -> u64 {
    let s = a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7;
    s * 1_000_000_000 + (p0 as u64) * 1_000_000 + (p1.a as u64) * 1_000 + p2 as u64
}
