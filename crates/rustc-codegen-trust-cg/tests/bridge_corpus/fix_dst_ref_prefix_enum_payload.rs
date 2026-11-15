// [TCG-DEREF-BASE-ADDR] REGRESSION PIN — an aggregate ENUM PAYLOAD read out of a
// slice-tail DST's sized prefix (`match h.e { E::A(i) => .. }` on `h: &H<[u8]>`).
//
// # What this fixture is for
//
// `lower_memory_nested_enum_field_use` copies `(((*h).1: E) as A).0` out of a
// memory slot. It walked that `Deref`-led place over `h`'s OWN type, so
// `Field(1)` landed on the reference's `usize` LENGTH and the next projection
// step asked a primitive for a field: the BACKEND PANICKED at
// `-Copt-level=0` (`FieldsShape::offset: Primitive`s have no fields`) on the
// unpatched lane tip — and at `-Copt-level=2` a sibling reader of the same bytes
// printed `payload 0 0` where LLVM printed `payload 405 7`.
//
// # HOW THIS FAILS IF THE FIX IS REVERTED
//
// Revert the walk to the local's own type and the `-Copt-level=0` row is a
// backend panic with no `[TCG-…]` diagnostic, which this harness counts as a
// HARD FAIL. (With the fix the `-O0` row is an honest INCOMPLETE on the
// host-wide `[TCG-PROOF-465]` opcode-proof gap in `payload` itself, and the
// `-O2` row COMPILES and MATCHES.)
#![allow(dead_code)]

#[derive(Clone, Copy)]
struct Inner {
    a: u64,
    b: u64,
}
#[derive(Clone, Copy)]
enum E {
    A(Inner),
    B,
}
struct H<T: ?Sized> {
    n: u64,
    e: E,
    tail: T,
}

#[inline(never)]
fn payload(h: &H<[u8]>) -> u64 {
    match h.e {
        E::A(i) => i.a * 100 + i.b,
        E::B => 7,
    }
}

fn main() {
    let o: H<[u8; 3]> = H {
        n: 1,
        e: E::A(Inner { a: 4, b: 5 }),
        tail: [1, 2, 3],
    };
    let p: H<[u8; 3]> = H {
        n: 1,
        e: E::B,
        tail: [1, 2, 3],
    };
    let x = payload(&o);
    let y = payload(&p);
    println!("payload {} {}", x, y);
}
