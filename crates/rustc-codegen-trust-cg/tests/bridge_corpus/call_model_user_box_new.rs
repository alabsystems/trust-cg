// Corpus: user items that share a NAME, arity and result type with the
// `Box::new` / `Box::new_uninit` constructors the bridge synthesizes. Each
// runs its own body; the genuine `Box::new` beside them is still synthesized.
#![allow(dead_code)]

#[inline(never)]
fn new(x: u32) -> Box<u32> {
    Box::new(x.wrapping_add(7))
}

struct W;

impl W {
    #[inline(never)]
    fn new_uninit() -> Box<u64> {
        Box::new(99)
    }
}

fn main() {
    let mut acc = 0u64;
    for x in [0u32, 1, 2, 3, 250, 65_535, u32::MAX] {
        let a = *new(x) ^ *Box::new(x.wrapping_mul(3));
        let b = *W::new_uninit() ^ u64::from(x);
        println!("{x}: {a} {b}");
        acc = acc.wrapping_mul(31).wrapping_add(u64::from(a) ^ b);
    }
    println!("acc {acc}");
}
