// (k) A struct whose FIRST field is an all-ZST newtype (`Tag(PhantomData)`),
// read through `&S`: the ZST lane was dropped from the flattened tuple while the
// by-ref field read used the MIR field index (`s.a` read `b`). Same root and
// same fix as (e): the pointee lane tuple is refused for a ZST-before-sized
// shape and the reference takes the rustc-layout byte walker.
#![allow(dead_code)]
struct Tag(std::marker::PhantomData<u8>);
struct S { t: Tag, a: u32, b: u32 }
struct N(Tag);
struct T2 { n: N, x: u64, y: u16 }
#[inline(never)] fn sa(s: &S) -> u32 { s.a }
#[inline(never)] fn sb(s: &S) -> u32 { s.b }
#[inline(never)] fn tx(t: &T2) -> u64 { t.x }
#[inline(never)] fn ty(t: &T2) -> u16 { t.y }
#[inline(never)] fn mk(a: u32, b: u32) -> S { S { t: Tag(std::marker::PhantomData), a, b } }
fn main() {
    let s = mk(3, 5);
    let t = T2 { n: N(Tag(std::marker::PhantomData)), x: 70, y: 9 };
    println!("{} {} {} {}", sa(&s), sb(&s), tx(&t), ty(&t));
}
