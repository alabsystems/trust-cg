// CONTROL for `fix_p_fnshim_projected_arg.rs`: an `Fn*`-call shim that refuses
// for a DIFFERENT, model-shaped reason must STILL refuse.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// This is the shape of the ONE root in the `Fn*-call shim over a fn ITEM has an
// unlowerable body` family that is not the projected-operand defect: the census's
// `<<dyn Error>::source as FnOnce<(&&dyn Error,)>>::call_once`, whose inner error
// is about the shim's RETURN, not its argument —
//
//   virtual call returning a by-value aggregate into a memory-backed destination
//   is not yet supported
//
// The argument normalization hoists this shim's projected argument too, and must
// leave that refusal exactly where it was. A row that COMPILES here has admitted
// a shape nobody modelled.

#[derive(Clone, Copy)]
struct Triple {
    a: u64,
    b: u64,
    c: u64,
}

trait Shape {
    fn triple(&self) -> Triple;
}

struct Square(u64);

impl Shape for Square {
    fn triple(&self) -> Triple {
        Triple {
            a: self.0,
            b: self.0 + 1,
            c: self.0 + 2,
        }
    }
}

fn once<A, R, F: FnOnce(A) -> R>(f: F, a: A) -> R {
    f(a)
}

fn main() {
    let sq = Square(7);
    let d: &dyn Shape = &sq;
    let t = once(<dyn Shape as Shape>::triple, d);
    println!("{}", t.a + t.b * 10 + t.c * 100);
}
