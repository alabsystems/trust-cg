#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
static U64S: [u64; 6] = [
    u64::MAX,
    1,
    0x8000_0000_0000_0000,
    0x1_0000_0000,
    77,
    0xdead_beef_cafe_babe,
];
static U16S: [u16; 9] = [0, 65535, 1, 32768, 4660, 22136, 7, 65534, 300];

#[no_mangle]
pub extern "C" fn e_offset_from(a: u32, b: u32) -> i64 {
    let p = U64S.as_ptr();
    let x = unsafe { p.add((a % 7) as usize) };
    let y = unsafe { p.add((b % 7) as usize) };
    unsafe { x.offset_from(y) as i64 }
}
#[no_mangle]
pub extern "C" fn e_ptr_read(a: u32) -> u64 {
    let p = U64S.as_ptr();
    unsafe { *p.add((a % 6) as usize) }
}
#[no_mangle]
pub extern "C" fn e_ptr_wrapping(a: u32) -> u32 {
    let p = U16S.as_ptr();
    let q = p.wrapping_add(a as usize).wrapping_sub(a as usize);
    (q == p) as u32 | ((p.wrapping_add(a as usize) as usize).wrapping_sub(p as usize) as u32) << 1
}
#[no_mangle]
pub extern "C" fn e_from_raw_parts(a: u32, b: u32) -> u32 {
    let lo = (a % 10) as usize;
    let n = (b % 10) as usize;
    if lo + n > 9 {
        return 1;
    }
    let s = unsafe { core::slice::from_raw_parts(U16S.as_ptr().add(lo), n) };
    let mut h = 0u32;
    for x in s {
        h = h.wrapping_mul(31).wrapping_add(*x as u32);
    }
    h ^ (s.len() as u32) << 24
}
#[no_mangle]
pub extern "C" fn e_read_unaligned(a: u32) -> u64 {
    let bytes: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    let off = (a % 9) as usize;
    unsafe { core::ptr::read_unaligned(bytes.as_ptr().add(off) as *const u64) }
}
#[no_mangle]
pub extern "C" fn e_u32_from_le(a: u32) -> u32 {
    let bytes: [u8; 8] = [0xef, 0xbe, 0xad, 0xde, 1, 2, 3, 4];
    let off = (a % 5) as usize;
    let mut w = [0u8; 4];
    let mut i = 0;
    while i < 4 {
        w[i] = bytes[off + i];
        i += 1;
    }
    u32::from_le_bytes(w) ^ u32::from_be_bytes(w).rotate_left(3)
}
#[no_mangle]
pub extern "C" fn e_u64_to_bytes(a: i64) -> u32 {
    let b = (a as u64).to_le_bytes();
    let c = (a as u64).to_be_bytes();
    let mut h = 0u32;
    let mut i = 0;
    while i < 8 {
        h = h
            .wrapping_mul(257)
            .wrapping_add(b[i] as u32 ^ (c[i] as u32) << 8);
        i += 1;
    }
    h
}
#[no_mangle]
pub extern "C" fn e_ptr_iter_manual(a: u32) -> u64 {
    let lo = (a % 7) as usize;
    let s = &U64S[lo..];
    let mut p = s.as_ptr();
    let end = unsafe { p.add(s.len()) };
    let mut h = 0u64;
    let mut guard = 0;
    while p != end && guard < 10 {
        h = h.rotate_left(9) ^ unsafe { *p };
        p = unsafe { p.add(1) };
        guard += 1;
    }
    h
}
#[no_mangle]
pub extern "C" fn e_get_unchecked(a: u32) -> u32 {
    let i = (a % 9) as usize;
    unsafe { *U16S.get_unchecked(i) as u32 + *U16S.get_unchecked(8 - i) as u32 * 65536 }
}
#[no_mangle]
pub extern "C" fn e_usize_ptr_cast(a: u32) -> u32 {
    let p = &U16S[(a % 9) as usize] as *const u16;
    let base = U16S.as_ptr() as usize;
    ((p as usize - base) / 2) as u32 | ((p as usize & 1) as u32) << 16
}
