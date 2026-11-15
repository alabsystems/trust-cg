// Corpus: an ADDRESS-TAKEN local `&dyn Trait`, and a `&&dyn Trait` passed as a
// real function argument.
//
// A `&dyn Trait` is ordinarily SCALARIZED into its `{data, vtable}` projected
// halves, which have no address. `&d` therefore needs the local to occupy a real
// 16-byte slot (memory-backing rule 4-fat) AND needs the unsize that produced
// the value to mirror both halves into that slot — otherwise `&d` points at
// uninitialized bytes and `thru` dispatches through a garbage vtable.
//
// Both arms of the `if` coerce a DIFFERENT concrete type, so the vtable must
// survive the branch merge and reach the slot; `thru(r) + d.val()` then reads
// the SAME fat pointer through both representations (the slot and the register
// pair), so a disagreement between them shows up as a wrong value.
#![allow(dead_code)]

trait Shape {
    fn val(&self) -> i64;
}
struct Square(i64);
struct Circle(i64);
impl Shape for Square {
    fn val(&self) -> i64 {
        self.0 * self.0
    }
}
impl Shape for Circle {
    fn val(&self) -> i64 {
        self.0 * 3
    }
}

#[inline(never)]
fn thru(r: &&dyn Shape) -> i64 {
    r.val()
}

#[inline(never)]
fn go(which: i64) -> i64 {
    let sq = Square(7);
    let ci = Circle(5);
    let d: &dyn Shape = if which == 0 { &sq } else { &ci };
    let r: &&dyn Shape = &d;
    thru(r) + d.val()
}

fn main() {
    println!("a {} {}", go(0), go(1));
}
