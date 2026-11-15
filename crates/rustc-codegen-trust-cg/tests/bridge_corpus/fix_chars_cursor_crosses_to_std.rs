// CORPUS FIXTURE — the LAYOUT-AGREEMENT CERTIFICATE for the bridge's `Chars`
// cursor: a cursor the BRIDGE wrote, read by STD's OWN bodies.
//
// WHAT IT PINS. `lower_str_chars_ctor` writes `{ ptr@0, end@8 }` into the `Chars`
// slot and `lower_str_chars_next` advances `ptr` by the decoded UTF-8 width. Until
// 2026-09-26 the `[TCG-STRIDE-ITER-METHOD]` guard refused EVERY call whose first
// argument was such a cursor except `next`/`spec_next`/`into_iter`, because nothing
// in the tree pinned that those two words are where std keeps them —
// `core::str::Chars` merely HAPPENED to be `{ptr, end}`. `chars_cursor_layout_
// disagreement` now PROVES it from rustc's own layout (field names, offsets, sizes,
// and the absence of any state field the bridge does not maintain), and the guard
// withdraws only when that certificate holds.
//
// Every row below hands a bridge-written cursor to a body the bridge did NOT
// synthesize, and the answer is only right if the words are where the certificate
// says:
//
//   * `drain_by_value`     — the cursor crosses a FUNCTION BOUNDARY by value (the
//                            `alloc::str::map_uppercase_sigma` ->
//                            `case_ignorable_then_cased(from.chars())` shape, a
//                            `library/alloc` census root).
//   * `first_after_spaces` — `Iterator::skip_while` (a pure adapter constructor)
//                            then `SkipWhile::next` -> `Chars::find` ->
//                            `Chars::try_fold`: the REAL trait-default `try_fold`
//                            body, a `next` loop, which `lower_iter_try_fold` now
//                            falls through to for a certified cursor.
//   * `last_cp` / `back`   — `Chars::next_back`, std's own BACKWARD UTF-8 decode. It
//                            reads the `end` word and walks back over continuation
//                            bytes, so a swapped or misplaced word cannot produce
//                            the right code point by accident.
//   * `rev0` / `rev1`      — `Iterator::rev` (a byte move) then `Rev<Chars>::next`
//                            -> `Chars::next_back`, twice, so the cursor must be
//                            correctly UPDATED by std and not merely read once.
//   * `asstr`/`backhash`   — the bridge's OWN modeled `Chars::as_str` read AFTER
//                            std's bodies have advanced the cursor: the two models
//                            must agree on the same bytes, in both directions.
//
// The string mixes 1-, 2-, 3- and 4-byte code points, so a cursor measured in chars
// instead of bytes, or a backward decode that mistakes a continuation byte for a
// lead byte, diverges at the first multi-byte boundary. Empty and all-match rows
// cover the `ptr == end` boundary.
//
// HOW IT FAILS IF THE CHANGE IS REVERTED. With the guard restored to its
// unconditional form this file does not compile at all: the first `it.clone()`
// is refused with `[TCG-STRIDE-ITER-METHOD] `clone` on a ... Chars iterator`
// (measured), so the row becomes INCOMPLETE and the lane's COMPILED floor is
// missed — a hard failure that names this fixture.
//
// WHY THERE IS NO `size_hint` ROW. `Chars::size_hint` DOES lower under the
// certificate (it is one of the four `library/alloc` roots this change clears, via
// `alloc::string::Drain::size_hint`), but its `len.div_ceil(4)` emits an
// `AArch64::CSet` and this host's opcode-proof inventory has no mapping for it —
// `[TCG-PROOF-465]`, the same pre-existing host-wide gap that makes every `-O2` row
// of this lane INCOMPLETE. It is measured by the census lane instead, which runs
// with `no-proof-certs`. Do not add it here to "improve coverage": it would make
// this fixture measure the proof inventory rather than the certificate.
//
// The remainders are compared by an order-sensitive FNV HASH over the bytes rather
// than by printing the `&str` or its length — both were refused by unrelated
// pre-existing format-lane gates (`[TCG-FMT-RTSTR]`, and `[TCG-FMT-LEN]` until
// 2026-10-03), and a tuple field read straight into a format placeholder is
// refused by `[TCG-FMT-ARGPLACE]`.
//
// Edition 2015: no inline format captures.

fn hash(s: &str) -> u64 {
    let mut h: u64 = 1469598103934665603;
    for b in s.as_bytes() {
        h = (h ^ *b as u64).wrapping_mul(1099511628211);
    }
    h
}

// The cursor crosses a function boundary BY VALUE and is driven to exhaustion by
// the bridge's own modeled `next` on the far side.
#[inline(never)]
fn drain_by_value(it: std::str::Chars) -> u64 {
    let mut n: u64 = 0;
    let mut it2 = it;
    loop {
        match it2.next() {
            Some(c) => n = n.wrapping_mul(131).wrapping_add(c as u64),
            None => break,
        }
    }
    n
}

// `skip_while` is a pure adapter CONSTRUCTOR (it moves `self` into field 0 and
// writes `flag: false`); the work happens in `SkipWhile::next` -> `Chars::find` ->
// the real `Chars::try_fold`.
#[inline(never)]
fn first_after_spaces(it: std::str::Chars) -> u32 {
    match it.skip_while(|c| *c == ' ').next() {
        Some(c) => c as u32,
        None => 0,
    }
}

// std's own backward UTF-8 decode over the bridge-written `end` word.
#[inline(never)]
fn last_cp(it: std::str::Chars) -> u32 {
    let mut b = it;
    match b.next_back() {
        Some(c) => c as u32,
        None => 0,
    }
}

fn main() {
    let s = "a\u{e9}\u{4e2d}\u{1f600}z";
    let mut it = s.chars();
    it.next();
    it.next();
    println!("byval={}", drain_by_value(it.clone()));
    println!("asstr={}", hash(it.as_str()));
    println!("back2={}", last_cp(it.clone()));
    println!("spaces={}", first_after_spaces("  \u{4e2d}q".chars()));
    println!("nospaces={}", first_after_spaces("\u{1f600}x".chars()));
    println!("allspaces={}", first_after_spaces("   ".chars()));
    let mut b = s.chars();
    let bk = match b.next_back() {
        Some(c) => c as u32,
        None => 0,
    };
    println!("back={}", bk);
    println!("backhash={}", hash(b.as_str()));
    let mut r = s.chars().rev();
    let r0 = match r.next() {
        Some(c) => c as u32,
        None => 0,
    };
    let r1 = match r.next() {
        Some(c) => c as u32,
        None => 0,
    };
    println!("rev0={} rev1={}", r0, r1);
    println!("emptyback={}", last_cp("".chars()));
}
