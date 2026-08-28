// nested aggregates: struct-of-struct, array-of-struct field writes, enum payload match.
use std::hint::black_box as bb;
#[derive(Clone, Copy)] struct Inner { a: u64, b: u32 }
#[derive(Clone, Copy)] struct Outer { x: Inner, y: [u64; 3], tag: u8 }
enum E { Za(u64), Zb(Inner), Zc { p: u64, q: u32 } }
fn ev(e: &E) -> u64 { match e { E::Za(v) => *v, E::Zb(i) => i.a.wrapping_add(i.b as u64), E::Zc { p, q } => p.wrapping_mul(*q as u64) } }
fn main() {
    let mut arr = [Outer { x: Inner { a: bb(1), b: 2 }, y: [3,4,5], tag: 1 }; 8];
    let mut acc: u64 = 0;
    for i in 0..bb(8usize) { arr[i].x.a = (i as u64).wrapping_mul(7); arr[i].y[i % 3] = i as u64; }
    for o in arr.iter() { acc = acc.wrapping_add(o.x.a).wrapping_add(o.y[o.tag as usize % 3]).wrapping_add(o.x.b as u64); }
    let es = [E::Za(bb(9)), E::Zb(Inner { a: 10, b: 11 }), E::Zc { p: 12, q: 13 }];
    for e in es.iter() { acc = acc.wrapping_add(ev(e)); }
    std::process::exit((acc % 233) as i32);
}
