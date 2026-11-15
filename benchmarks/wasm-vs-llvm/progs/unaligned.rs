#![no_std]
#![allow(dead_code)]

use core::convert::TryInto;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[inline(never)]
fn fill(seed: u32, b: &mut [u8; 40]) {
    let mut s = seed | 1;
    for x in b.iter_mut() {
        s ^= s << 13;
        s ^= s >> 17;
        s ^= s << 5;
        *x = (s >> 3) as u8;
    }
}

#[repr(C)]
union Bits {
    f: f32,
    u: u32,
    b: [u8; 4],
    h: [u16; 2],
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Header {
    magic: [u8; 4],
    version: u16,
    flags: u8,
    kind: u8,
    len: u32,
    crc: u32,
}

#[inline(never)]
fn parse(b: &[u8]) -> Option<Header> {
    if b.len() < 16 {
        return None;
    }
    let mut magic = [0u8; 4];
    magic.copy_from_slice(&b[0..4]);
    Some(Header {
        magic,
        version: u16::from_le_bytes([b[4], b[5]]),
        flags: b[6],
        kind: b[7],
        len: u32::from_le_bytes([b[8], b[9], b[10], b[11]]),
        crc: u32::from_le_bytes([b[12], b[13], b[14], b[15]]),
    })
}

#[inline(never)]
fn serialize(h: &Header, out: &mut [u8; 16]) {
    out[0..4].copy_from_slice(&h.magic);
    out[4..6].copy_from_slice(&h.version.to_le_bytes());
    out[6] = h.flags;
    out[7] = h.kind;
    out[8..12].copy_from_slice(&h.len.to_le_bytes());
    out[12..16].copy_from_slice(&h.crc.to_le_bytes());
}

#[repr(transparent)]
#[derive(Clone, Copy)]
struct Meters(f64);

#[repr(C)]
#[derive(Clone, Copy)]
struct Vec3 {
    x: f32,
    y: f32,
    z: f32,
}

#[inline(never)]
fn cross(a: Vec3, b: Vec3) -> Vec3 {
    Vec3 {
        x: a.y * b.z - a.z * b.y,
        y: a.z * b.x - a.x * b.z,
        z: a.x * b.y - a.y * b.x,
    }
}

#[inline(never)]
fn scale(m: Meters, k: f64) -> Meters {
    Meters(m.0 * k)
}

#[no_mangle]
pub extern "C" fn unaligned(seed: u32, off: u32) -> u64 {
    let mut b = [0u8; 40];
    fill(seed, &mut b);
    let o = (off % 30) as usize;
    unsafe {
        let p = b.as_ptr().add(o);
        let x = core::ptr::read_unaligned(p as *const u32) as u64;
        let y = core::ptr::read_unaligned(p.add(1) as *const u64);
        let z = core::ptr::read_unaligned(p.add(3) as *const u16) as u64;
        let f = core::ptr::read_unaligned(p.add(2) as *const f32).to_bits() as u64;
        let q = b.as_mut_ptr().add(o + 1);
        core::ptr::write_unaligned(q as *mut u32, 0xdeadbeef);
        core::ptr::write_unaligned(q.add(5) as *mut u16, 0x1234);
    }
    let mut h = 0u64;
    for &v in b.iter() {
        h = h.wrapping_mul(131) ^ v as u64;
    }
    h
}
