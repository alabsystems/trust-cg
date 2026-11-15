// (m-class, found by the sweep) The bridge's name-keyed primitive recognizers
// (`overflowing_*`, `wrapping_*`, `saturating_*`, `overflowing_shl/shr`,
// `overflowing_div/rem`, the bitmanip family) each claimed in its doc comment
// that a primitive-integer RECEIVER made a user method of the same name safe
// from interception. It does not: a user TRAIT with `Self = i32`/`u8` has a
// primitive receiver too, so every one of them fired and the program ran the
// BUILT-IN semantics instead of the user's body (`Ovf::overflowing_add(10i32, 3)`
// printed `13 false` for the impl's `(7, true)`). Pre-existing — the pre-lane
// baseline dylib reproduces it. Interception is now additionally gated on the
// callee being one of `core`'s own INHERENT primitive methods
// (`is_core_inherent_primitive_method`). Differential-OK at -O0 and -O2.
trait Ovf { fn overflowing_add(self, o: Self) -> (Self, bool) where Self: Sized;
            fn wrapping_add(self, o: Self) -> Self where Self: Sized;
            fn saturating_add(self, o: Self) -> Self where Self: Sized;
            fn leading_zeros(self) -> u32 where Self: Sized;
            fn rotate_left(self, n: u32) -> Self where Self: Sized; }
impl Ovf for i32 {
    fn overflowing_add(self, o: i32) -> (i32, bool) { (self - o, true) }
    fn wrapping_add(self, o: i32) -> i32 { self * o }
    fn saturating_add(self, o: i32) -> i32 { self - o - 1 }
    fn leading_zeros(self) -> u32 { self as u32 + 7 }
    fn rotate_left(self, n: u32) -> i32 { self + n as i32 }
}
fn main() {
    let (a, b) = Ovf::overflowing_add(10i32, 3);
    println!("{a} {b} {} {} {} {}", Ovf::wrapping_add(10i32, 3), Ovf::saturating_add(10i32, 3),
             Ovf::leading_zeros(4i32), Ovf::rotate_left(10i32, 3));
    // the REAL inherent methods, for contrast — these MUST still be intercepted
    let (ra, rb) = 10i32.overflowing_add(3);
    println!("{ra} {rb} {} {} {} {}", 250u8.wrapping_add(10), 250u8.saturating_add(10),
             4i32.leading_zeros(), 0x8000_0001u32.rotate_left(1));
}
