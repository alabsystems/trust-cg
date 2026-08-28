// byte conversions: to/from le/be bytes (u64/u32/u16), from_le_bytes with array
// literals, bit packing — ubiquitous in serialization/hashing/parsing.
use std::hint::black_box as bb;
fn main() {
    let mut acc: u64 = 0;
    let vals = [bb(0x0123456789abcdefu64), bb(0xdeadbeef), bb(1), bb(u64::MAX)];
    for &v in vals.iter() {
        let le = v.to_le_bytes();
        let be = v.to_be_bytes();
        for i in 0..8 { acc = acc.wrapping_add((le[i] as u64).wrapping_mul(i as u64 + 1)); }
        acc = acc.wrapping_add(u64::from_le_bytes(le)).wrapping_add(u64::from_be_bytes(be));
        acc = acc.wrapping_add(u32::from_le_bytes([le[0], le[1], le[2], le[3]]) as u64);
        // bit packing
        let packed = ((v & 0xff) << 24) | ((v & 0xff00) << 8) | ((v >> 8) & 0xff00) | ((v >> 24) & 0xff);
        acc = acc.wrapping_add(packed);
    }
    let a: u16 = bb(0xabcd); let b = a.to_be_bytes();
    acc = acc.wrapping_add(u16::from_be_bytes(b) as u64);
    std::process::exit((acc % 233) as i32);
}
