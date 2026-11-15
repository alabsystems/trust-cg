// (e)/(k) A struct / tuple with a ZERO-SIZED field BEFORE a sized field, read
// THROUGH A REFERENCE: the by-ref lane tuple drops ZST lanes but field reads
// indexed by MIR field number (`s.a` read `b`: `4 6` for `3 5`). Now
// `aggregate_reference_pointee_to_trust_ir_ty` refuses the lane tuple for such
// a pointee (`[TCG-ZST-LANE-INDEX]`), which routes a STRUCT reference to the
// rustc-layout byte walker — every read lands at its real offset. (Since
// 2026-09-14 a by-ref TUPLE with the same shape takes that byte walker too and
// no longer refuses — `fix_e_zst_tuple_by_ref.rs` carries the measurement.)
#![allow(dead_code)]
#[repr(align(16))] struct W16(());
struct Tag(std::marker::PhantomData<u8>);
struct S1 { w: W16, a: u8, b: u8 }
struct S2 { a: u8, w: W16, b: u8 }
struct S4 { t: Tag, a: u32, b: u64, t2: Tag, c: u16 }
struct P2 { z: [u8; 0], a: u32, b: u32 }
#[inline(never)] fn s1a(s: &S1) -> u8 { s.a }
#[inline(never)] fn s2a(s: &S2) -> u8 { s.a }
#[inline(never)] fn s2b(s: &S2) -> u8 { s.b }
#[inline(never)] fn s4a(s: &S4) -> u32 { s.a }
#[inline(never)] fn s4b(s: &S4) -> u64 { s.b }
#[inline(never)] fn s4c(s: &S4) -> u16 { s.c }
#[inline(never)] fn p2a(p: &P2) -> u32 { p.a }
#[inline(never)] fn p2b(p: &P2) -> u32 { p.b }
#[inline(never)] fn mk1(a: u8, b: u8) -> S1 { S1 { w: W16(()), a, b } }
#[inline(never)] fn by_val1(s: S1) -> u32 { s.a as u32 * 10 + s.b as u32 }
fn main() {
    let s1 = mk1(3, 4);
    let s2 = S2 { a: 7, w: W16(()), b: 8 };
    let s4 = S4 { t: Tag(std::marker::PhantomData), a: 11, b: 12, t2: Tag(std::marker::PhantomData), c: 13 };
    let p2 = P2 { z: [], a: 10, b: 20 };
    println!("{} {} {} {} {} {} {} {} v1={}", s1a(&s1), s2a(&s2), s2b(&s2), s4a(&s4), s4b(&s4), s4c(&s4), p2a(&p2), p2b(&p2), by_val1(s1));
}
