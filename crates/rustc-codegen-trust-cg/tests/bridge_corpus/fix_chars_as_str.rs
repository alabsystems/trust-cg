// CORPUS FIXTURE — `<core::str::Chars>::as_str()`, the unyielded remainder of a
// `str::chars()` cursor.
//
// WHY THIS SHAPE. `lower_str_chars_ctor` replaces std's `Chars(slice::Iter<u8>)`
// with the bridge's own `{ ptr@0, end@8 }` byte cursor, and the
// `[TCG-STRIDE-ITER-METHOD]` guard therefore refuses every method whose answer
// would read std's layout. `as_str` is the one method whose answer is EXACTLY
// the two words the bridge wrote — `&str{ data: ptr, len: end - ptr }` — so it
// is modeled rather than refused (`lower_str_chars_as_str`). This fixture is the
// differential pin for that: `alloc::string::Drain::as_str` forwards straight to
// it, and it is a `library/alloc` census root.
//
// The string mixes 1-, 2-, 3- and 4-byte code points so that a remainder
// computed in CHARS instead of BYTES, or one that fails to track `next`'s
// variable advance, diverges from LLVM at the first multi-byte boundary. The
// rows also read the remainder of an EXHAUSTED cursor (which must be empty, not
// one-past-end) and of an EMPTY source.
//
// The remainder is checked by an order-sensitive FNV HASH over its bytes rather
// than by printing the `&str` itself or its length: both of those were refused by
// unrelated, pre-existing format-lane gates (`[TCG-FMT-RTSTR]` and
// `[TCG-FMT-LEN]`, the latter removed 2026-10-03), which would have made this
// fixture measure those gates instead of `as_str`. Nothing is given up — FNV over the byte sequence distinguishes a
// wrong ADDRESS, a wrong byte COUNT (a different count hashes differently) and a
// wrong OFFSET, and the hash is computed by iterating `as_bytes()`, so no length
// value ever reaches a format placeholder.
//
// Edition 2015: no inline format captures.

fn hash(s: &str) -> u64 {
    let mut h: u64 = 1469598103934665603;
    for b in s.as_bytes() {
        h = (h ^ *b as u64).wrapping_mul(1099511628211);
    }
    h
}

fn main() {
    let s = "a\u{e9}\u{4e2d}\u{1f600}z";
    let mut it = s.chars();
    println!("start hash={}", hash(it.as_str()));
    loop {
        let c = it.next();
        if c.is_none() {
            break;
        }
        println!("cp={} hash={}", c.unwrap() as u32, hash(it.as_str()));
    }
    println!("drained hash={}", hash(it.as_str()));

    // A SECOND cursor over the same source, advanced a different number of
    // times, so the remainder is read at an offset the first loop never held.
    // (A row that threaded the cursor through a USER helper -- `fn rest(it:
    // &Chars) -> &str` -- was dropped on purpose: the `[TCG-STRIDE-ITER-METHOD]`
    // guard refuses ANY call whose receiver is one of the bridge's cursors,
    // including a local helper, and that over-rejection is PRE-EXISTING and
    // deliberately left in place -- see the "DELIBERATELY NOT GATED ON THE
    // CALLEE" comment at the guard. Keeping the row here would make this
    // fixture measure that guard instead of `as_str`.)
    let mut it2 = s.chars();
    it2.next();
    it2.next();
    println!("twoadvanced hash={}", hash(it2.as_str()));

    // An empty source: `ptr == end` from the start.
    let mut it3 = "".chars();
    println!("empty hash={}", hash(it3.as_str()));
    println!("emptynone={}", it3.next().is_none());
}
