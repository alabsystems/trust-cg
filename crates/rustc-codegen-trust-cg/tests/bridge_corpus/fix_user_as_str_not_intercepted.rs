// CORPUS FIXTURE — a USER function named `as_str` over a `&core::str::Chars`.
//
// THE MISCOMPILE THIS PINS. `lower_str_chars_as_str` models `<Chars>::as_str()`
// from the bridge's own `{ ptr@0, end@8 }` cursor. Its first two tests are a
// NAME (`opt_item_name == "as_str"`) and a RECEIVER TYPE (`is_str_chars_ty`),
// and a user's own free function `fn as_str(&Chars) -> &str` satisfies BOTH.
// Measured 2026-09-25 without the provenance conjunct: the user's body was
// DISCARDED and the call answered with the cursor remainder —
// `hash("bcdef") = 11585393754820217191` where LLVM prints
// `hash("SENTINEL") = 15763585847121849335`. A silent wrong answer, not a
// refusal.
//
// WHAT THIS FILE DOES *NOT* PIN — read before treating it as the whole guard.
// The `as_str` here is LOCAL to the compiled crate, so the SELF-HOST rule
// (`std_def_is_interceptable`, which is locality and nothing else) already
// refuses it. The first provenance conjunct shipped for this lowering was
// `is_std_collection_method_callee` — locality PLUS a crate-NAME string compare —
// and it passed this row while still being REFUTED by an rlib built with
// `--crate-name hashbrown`. The row that separates the refuted conjunct from the
// identity one (`is_real_str_chars_as_str_callee`) is therefore NOT here; it is
// `a_crate_named_hashbrown_does_not_get_its_as_str_intercepted` in
// `tests/unsized_value_measurement_differential.rs`, which needs a second crate
// and so cannot be a single-file corpus fixture.
//
// HOW THIS FIXTURE BEHAVES, AND WHY THAT IS THE PIN. With the conjunct in place
// the call is NOT intercepted, falls through to the `[TCG-STRIDE-ITER-METHOD]`
// soundness guard (whose receiver-type test still matches), and is REFUSED by
// name — an INCOMPLETE row in the differential lane, which is a correct
// fail-closed outcome. Remove the conjunct and the row COMPILES and its stdout
// diverges from LLVM, which the same lane reports as a HARD FAILURE. So this
// file is live evidence either way: it can never go quiet.
//
// If a later change makes the genuine std `Chars::as_str` reachable THROUGH a
// user wrapper, this row may legitimately start compiling — but only with the
// LLVM-matching `sentinel` hash. The MATCH assertion is what must hold, not the
// refusal.
//
// Edition 2015: no inline format captures.

fn hash(s: &str) -> u64 {
    let mut h: u64 = 1469598103934665603;
    for b in s.as_bytes() {
        h = (h ^ *b as u64).wrapping_mul(1099511628211);
    }
    h
}

// Same NAME and same RECEIVER TYPE as `core::str::Chars::as_str`, different
// definition site and a body that ignores the cursor entirely.
#[inline(never)]
fn as_str<'a>(_it: &std::str::Chars<'a>) -> &'a str {
    "SENTINEL"
}

fn main() {
    let s = "abcdef";
    let mut it = s.chars();
    it.next();
    println!("user_as_str hash={}", hash(as_str(&it)));
    println!("sentinel hash={}", hash("SENTINEL"));
    println!("remainder hash={}", hash("bcdef"));
}
