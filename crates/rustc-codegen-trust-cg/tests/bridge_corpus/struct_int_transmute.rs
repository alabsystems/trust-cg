// CORPUS FIXTURE — `transmute` between a DENSE (padding-free) struct / tuple and a
// same-width integer (`transmute::<Pair, u64>` and back, `transmute::<u32,(u16,u16)>`).
// The two carriers share the same bytes, so it lowers to a store / load through the
// aggregate's memory slot — exactly the existing `int <-> [u8; N]` path generalized
// to a dense struct / tuple. Before this it failed closed ("Ty::Adt multi-field
// struct P" at type mapping, or "memory-backed aggregate assignment Rvalue::Cast"
// for the int -> struct direction).
//
// SAFETY: only PADDING-FREE aggregates qualify (`transmute_aggregate_is_dense`): a
// padded struct has `undef` padding bytes that could differ between backends, so it
// stays fail-closed (never miscompiles). Multi-variant enums / unions are excluded.
//
// (a) struct -> u64 -> struct round-trip; (b) u64 -> struct field read; (c)
// (u16,u16) <-> u32; (d) a nested dense struct -> u64; (e) a struct of f32 fields
// (the leaves can be floats). All correct -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;
use core::mem::transmute;

#[repr(C)]
#[derive(Clone, Copy)]
struct Pair {
    a: u32,
    b: u32,
}
#[repr(C)]
#[derive(Clone, Copy)]
struct Inner {
    x: u16,
    y: u16,
}
#[repr(C)]
#[derive(Clone, Copy)]
struct Outer {
    i: Inner,
    z: u32,
}
#[repr(C)]
#[derive(Clone, Copy)]
struct V2 {
    x: f32,
    y: f32,
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) struct -> u64 -> struct. Little-endian: a at bits 0..32, b at 32..64.
    let p = Pair {
        a: black_box(0x10u32),
        b: black_box(0x2Au32),
    };
    let x: u64 = unsafe { transmute(p) };
    let ok_a = x == 0x0000_002A_0000_0010;
    let p2: Pair = unsafe { transmute(x) };
    let ok_a2 = p2.a == 0x10 && p2.b == 0x2A;

    // (b) u64 -> struct field read.
    let y = black_box(0x0000_0003_0000_0004u64);
    let p3: Pair = unsafe { transmute(y) };
    let ok_b = p3.a == 4 && p3.b == 3;

    // (c) (u16,u16) <-> u32.
    let t: (u16, u16) = (black_box(7u16), black_box(9u16));
    let tx: u32 = unsafe { transmute(t) };
    let ok_c1 = tx == ((9u32 << 16) | 7);
    let t2: (u16, u16) = unsafe { transmute(black_box(0x0002_0001u32)) };
    let ok_c2 = t2.0 == 1 && t2.1 == 2;

    // (d) nested dense struct -> u64.
    let o = Outer {
        i: Inner {
            x: black_box(1),
            y: black_box(2),
        },
        z: black_box(3),
    };
    let ov: u64 = unsafe { transmute(o) };
    let ok_d = (ov & 0xffff) == 1 && ((ov >> 16) & 0xffff) == 2 && (ov >> 32) == 3;

    // (e) struct of f32 leaves -> u64 -> struct.
    let v = V2 {
        x: black_box(1.5f32),
        y: black_box(2.5f32),
    };
    let vb: u64 = unsafe { transmute(v) };
    let v2: V2 = unsafe { transmute(vb) };
    let ok_e = v2.x == 1.5 && v2.y == 2.5;

    if ok_a && ok_a2 && ok_b && ok_c1 && ok_c2 && ok_d && ok_e {
        7
    } else {
        13
    }
}
