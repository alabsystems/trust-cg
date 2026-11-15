// (o) S2, second observable — GARBAGE HIGH BYTES. A 3-byte `#[repr(C)]`
// aggregate sits immediately before five `0xFF` guard bytes; the 8-byte load
// the single-register argument lane used to emit pulls whatever follows the
// object into the argument register's high half.
//
// WATCHED AND IT DID NOT FIRE, and the reason is measured: the CALLEE side
// (`lower_formal_arguments`, `ArgLocation::Reg`) gives a by-value aggregate a
// frame slot of `ty.bytes().max(8)` and stores the whole incoming X register
// into it, then reads only the fields the type declares. Bits above the
// object's own width are therefore never observable through the type, so a
// correct callee cannot see the difference. Kept as the paired CONTROL for the
// page-boundary row: the sum must stay 6 and the guard 255 before and after.
//
// Must print `6 255` and exit 0 under both backends at -O0 and -O2.
#[repr(C)]
#[derive(Clone, Copy)]
struct P3 {
    a: u8,
    b: u8,
    c: u8,
}

#[repr(C)]
struct Framed {
    s: P3,
    guard: [u8; 5],
}

#[inline(never)]
fn sum3(s: P3) -> u32 {
    s.a as u32 + s.b as u32 + s.c as u32
}

#[inline(never)]
fn guard_of(f: &Framed) -> u32 {
    f.guard[0] as u32
}

fn main() {
    let framed = Framed {
        s: P3 { a: 1, b: 2, c: 3 },
        guard: [0xFF; 5],
    };
    let s = framed.s;
    println!("{} {}", sum3(s), guard_of(&framed));
}
