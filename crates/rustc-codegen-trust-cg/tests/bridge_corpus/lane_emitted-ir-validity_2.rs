// CORPUS FIXTURE — lane emitted-ir-validity, shape 2: a generic fn that
// BUILDS AND RETURNS A CLOSURE BY VALUE whose every upvar is itself a
// non-capturing (zero-sized) closure — `core::iter::adapters::map::map_fold`,
// `NeverShortCircuit::wrap_mut_2`, `Filter::count`'s `to_usize`,
// `Iterator::cmp_by`'s `compare` — and a generic caller that receives such a
// closure BY VALUE and borrows it to call it (`Map::fold`, `apply` here).
// The closure's trust-ir type is `Tuple([Unit, ..])`: not `Unit`, so it used
// to keep an ABI slot in the signature while nothing ever bound a value for
// it, and the `Return` fell back to the never-defined `ValueId(0)` that
// trust-cg's SSA gate rejects ([TCG-SSA-071] "value ValueId(0) used in bb0 is
// never defined"). A zero-sized aggregate is now dropped from every ABI slot
// by one predicate, on the signature and the body's edges alike.
// The printed values depend on the composed closures running in order.
use std::hint::black_box;

#[inline(never)]
fn wrap<F: Fn(u32) -> u32>(f: F) -> impl Fn(u32) -> u32 {
    move |x| f(x) + 1
}

#[inline(never)]
fn wrap2<F: Fn(u32) -> u32, G: Fn(u32) -> u32>(f: F, g: G) -> impl Fn(u32) -> u32 {
    move |x| g(f(x))
}

#[inline(never)]
fn apply<H: Fn(u32) -> u32>(h: H, v: u32) -> u32 {
    h(v)
}

fn main() {
    // (a) returned closure passed straight through by value
    println!("{}", apply(wrap(|x| x * 2), black_box(5)));
    // (b) two ZST upvars, composed in order (g after f)
    println!("{}", apply(wrap2(|x| x + 3, |x| x * 10), black_box(4)));
    // (c) returned closure held in a local, then passed by value
    let g = wrap(|x| x * 2);
    println!("{}", apply(g, black_box(6)));
    // (d) returned closure held in a local and called directly
    let h = wrap(|x| x + 7);
    println!("{}", h(black_box(1)));
}
