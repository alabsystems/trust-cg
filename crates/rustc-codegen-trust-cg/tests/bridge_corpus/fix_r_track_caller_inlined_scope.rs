// Corpus: `#[track_caller]` read from an INLINED frame.
//
// The sibling fixture `fix_r_track_caller_location_abi` pins the hidden
// `&'static Location` parameter across ordinary calls. This one pins the case
// that parameter alone CANNOT answer.
//
// At `-O2`/`-O3` rustc's MIR inliner folds a `#[track_caller] #[inline]` callee
// into its caller. `caller_location()` then appears in a body that may have no
// hidden parameter at all — `main` here is not `#[track_caller]` — and the right
// answer is the span of the INLINED CALL, which lives in the source SCOPE, not in
// the call terminator's `fn_span`. Reading `fn_span` yields a span inside the
// inlined callee: a silently wrong line number, no crash, no refusal.
//
// The lowering therefore defers the entire decision to rustc's own
// `Body::caller_location_span`, which climbs out through inlined
// `#[track_caller]` frames to the call site that reified them and stops at the
// first callee that is not `#[track_caller]`. That is why the terminator's
// `SourceInfo` is plumbed through `DirectCallTerminator` rather than just its span.
//
// MEASURED, and the reason this fixture exists: an earlier version read the
// parameter directly and failed closed when it was absent. That was sound, but it
// refused this file outright at `-O2` and `-O3` — the inliner makes the
// absent-parameter case ORDINARY, not exceptional. A code comment asserting the
// case was "unreachable in practice" was wrong, and only running it said so.
//
// WHY EVERY ROW IS A WRONG LINE NUMBER, NOT A CRASH, IF THE WALK IS WRONG:
//   * `inl` — two calls to an `#[inline(always)] #[track_caller]` fn from
//     DIFFERENT lines. Both are inlined into `main`, so both must still report
//     their own call sites; a `fn_span` read collapses them to one number inside
//     the callee.
//   * the third value crosses an inlined track_caller fn that calls ANOTHER
//     track_caller fn, so the walk has to climb TWO frames, not one.
//   * `deep` — the same through a non-inlined hop, so the scope walk and the
//     parameter forwarding have to agree with each other.
// At `-O0` nothing is inlined and these are ordinary parameter reads, so the file
// also pins that both paths give the SAME answers.
#![allow(dead_code)]

use std::panic::Location;

#[track_caller]
#[inline(always)]
fn inl() -> u32 {
    Location::caller().line()
}

#[track_caller]
#[inline(always)]
fn chain_inl() -> u32 {
    inl()
}

#[track_caller]
#[inline(never)]
fn chain_outlined() -> u32 {
    inl()
}

fn main() {
    let a = inl();
    let b = inl();
    let c = chain_inl();
    println!("inl {} {} {}", a, b, c);

    let d = chain_outlined();
    let e = chain_outlined();
    println!("deep {} {}", d, e);
}
