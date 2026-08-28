// #[repr(packed)] unaligned field access: a u64/u32/u16 at a non-natural offset
// must be read/written with the correct (byte/unaligned) load/store, not an
// aligned access (which would fault or read wrong bytes).
use std::hint::black_box as bb;
#[repr(packed)] #[derive(Clone, Copy)] struct Pk { a: u8, b: u64, c: u16, d: u32 }
#[repr(packed)] #[derive(Clone, Copy)] struct Pk2 { x: u32, y: u64 }
fn main() {
    let mut acc: u64 = 0;
    let mut arr = [Pk { a: 0, b: 0, c: 0, d: 0 }; 6];
    for i in 0..6 {
        arr[i] = Pk { a: bb(i as u8), b: bb(i as u64 * 0x1000_0001), c: bb(i as u16 * 7), d: bb(i as u32 * 13) };
    }
    for i in 0..6 {
        let b = arr[i].b; let c = arr[i].c; let d = arr[i].d; let a = arr[i].a;
        acc = acc.wrapping_add(b).wrapping_add(c as u64).wrapping_add(d as u64).wrapping_add(a as u64);
    }
    let mut p2 = Pk2 { x: bb(0x12345678), y: bb(0xdeadbeef_cafebabe) };
    p2.x = p2.x.wrapping_add(bb(1)); p2.y = p2.y.wrapping_mul(bb(3));
    let x = p2.x; let y = p2.y;
    acc = acc.wrapping_add(x as u64).wrapping_add(y);
    std::process::exit((acc % 241) as i32);
}
