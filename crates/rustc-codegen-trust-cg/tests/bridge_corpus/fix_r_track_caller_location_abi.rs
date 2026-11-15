// Corpus: the hidden `#[track_caller]` `&'static Location` ABI parameter.
//
// `core::panic::Location::caller` is `#[track_caller]` and its whole body is
// `caller_location()`, an intrinsic declared WITHOUT a fallback body — it reads
// the enclosing function's hidden trailing `&'static Location` argument. This
// backend used to thread that argument only for callees it did NOT codegen
// locally, keeping a consistent no-hidden-param ABI for local ones; the cost was
// that `caller_location()` in a local body had nothing to read, so
// `Location::caller` itself was a failed root.
//
// The parameter is now threaded on BOTH sides for every instance, keyed on ONE
// predicate (`instance_abi_has_caller_location`) that the declaration, the entry block
// and every call site ask — they cannot drift apart.
//
// WHY THE INDIRECT PATHS ARE SAFE, AND IT IS NOT THIS BACKEND'S JUDGEMENT:
// rustc decides what sits at the far end of a fn pointer or a vtable slot, and it
// decides so that (its own words, `Instance::expect_resolve_for_vtable`) "the
// caller and callee ABI will always match":
//   * a fn pointer to a track_caller fn resolves to `Shim(ShimKind::Reify(..))`,
//     which is NOT in `requires_caller_location`'s match — plain ABI both sides;
//   * a vtable slot gets a track-caller shim, and this backend splices whatever
//     `tcx.vtable_entries` returns rather than resolving the method itself.
// The residual case — `#[track_caller]` on the TRAIT METHOD, where rustc emits no
// shim — fails closed in `lower_virtual_call_terminator` instead of calling with
// a garbage Location register. That is a separate fixture; this one is the
// supported surface.
//
// WHY EVERY ROW IS A WRONG LINE NUMBER, NOT A CRASH, IF THE ABI IS WRONG: a
// mismatched hidden argument leaves whatever happened to be in that register, and
// `Location::line()` reads through it. The values below are all distinct, so a
// dropped, duplicated or mis-ordered argument moves a number rather than trapping.
//   * `direct` — two calls to the SAME track_caller fn from DIFFERENT lines must
//     report those two different lines. A callee that ignored the parameter and
//     used its own span would print one repeated number.
//   * `chain` — a track_caller fn calling ANOTHER track_caller fn must FORWARD its
//     incoming Location, not synthesize its own. This is the row that fails if the
//     call site passes a call-site const while the frame already has a parameter:
//     it would report the intermediate hop's line instead of the original caller's.
//   * `fnptr` / `virt` — reached through rustc's reify / vtable shims, which
//     report the shim's own location. Pinned here so that a future change which
//     "fixes" them into call-site lines is caught as the ABI divergence it is.
//   * `arg` — a track_caller fn with REAL arguments, so the hidden parameter is
//     appended after them and a wrong insertion position corrupts an ordinary
//     argument instead of the Location.
#![allow(dead_code)]

use std::panic::Location;

#[track_caller]
#[inline(never)]
fn line_here() -> u32 {
    Location::caller().line()
}

#[track_caller]
#[inline(never)]
fn forwards() -> u32 {
    // Not a call SITE for the reported location: this frame is itself
    // `#[track_caller]`, so it must hand its own incoming Location onward.
    line_here()
}

#[track_caller]
#[inline(never)]
fn with_args(a: i64, b: i64) -> (i64, u32) {
    (a * 10 + b, Location::caller().line())
}

trait T {
    fn m(&self) -> u32;
}
struct S;
impl T for S {
    // On the IMPL, so rustc emits an ABI-matching vtable shim.
    #[track_caller]
    fn m(&self) -> u32 {
        Location::caller().line()
    }
}

#[inline(never)]
fn via_dyn(t: &dyn T) -> u32 {
    t.m()
}

fn main() {
    let d1 = line_here();
    let d2 = line_here();
    println!("direct {} {}", d1, d2);

    let c1 = forwards();
    let c2 = forwards();
    println!("chain {} {}", c1, c2);

    let f: fn() -> u32 = line_here;
    println!("fnptr {}", f());

    let s = S;
    println!("virt {}", via_dyn(&s));

    let (v, l) = with_args(3, 4);
    println!("arg {} {}", v, l);
}
