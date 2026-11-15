// Corpus: ONE function that must be refused for TWO reasons of the same class,
// so the refusal it reports depends on which one the bridge meets first.
//
// Both `&a` and `&n` escape as bare call arguments, so the memory-backed
// analysis (step 0h, "an aggregate whose reference value escapes") asks for a
// slot for `a: Nat` and for `n: Name`, and each owns a slot-modeled collection
// (`Vec<u64>`, `String`), which `[TCG-COLLECTION-IMAGE]` refuses. The analysis
// used to walk its `ref -> referent` map in HASH order, so the refusal named
// `Vec<u64>` in some compiles of this file and `String` in others (measured
// 3 : 5 over eight compiles); the Trust run-make test
// `trust-ir-cg-collection-owner-image` asserts the `Vec<u64` text and failed
// at random. It now walks in local order: `a` is declared first, so the
// refusal always names `Vec<u64>`.
pub struct Nat {
    limbs: Vec<u64>,
}

pub struct Name {
    s: String,
}

#[inline(never)]
pub fn nat_len(n: &Nat) -> usize {
    n.limbs.len()
}

#[inline(never)]
pub fn name_len(n: &Name) -> usize {
    n.s.len()
}

fn main() {
    let a = Nat { limbs: vec![1, 2] };
    let n = Name {
        s: String::from("abc"),
    };
    println!("{} {}", nat_len(&a), name_len(&n));
}
