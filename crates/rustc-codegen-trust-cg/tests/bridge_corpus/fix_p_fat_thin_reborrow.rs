// Corpus: a REBORROW of the thin pointer the fat -> thin cast seam produced.
//
// The seam binds the narrowed destination to the fat pointer's DATA lane. That
// lane is a plain `Ptr`, while a reborrow of the destination (`&*p`) retypes the
// bound value through a `PtrToPtr` whose declared source type is the thin
// LOCAL's type (`PtrConst([u8; N])`, `PtrConst(u8)`). Binding the lane untyped
// therefore refused every such reborrow at the adapter's cast-source gate:
//
//     CastOp::PtrToPtr source type mismatch: declared src_ty=PtrConst(Tuple([U8,
//     ..])), operand ValueId(38) has type Ptr
//
// which is `<[T]>::as_array` (`_6 = copy _8 as *const [T; N] (PtrToPtr); _7 =
// &(*_6)`) and so every `<[T] as PartialEq<[T; N]>>::eq` — any `slice == b"..."`
// (Trust run-make `trust-ir-cg-scalarized-fat-leaf` and `-box-dyn-param`,
// 2026-09-28).
//
// WHAT EACH ROW WOULD CATCH. Every printed value is read THROUGH the reborrowed
// thin pointer, so a data lane taken from the wrong half, or a reference bound
// to the wrong address, changes stdout rather than merely refusing.
//  * `head4`: `as_array::<4>` then a whole-array read (`u32::from_le_bytes`),
//    for a slice that has the length and one that does not.
//  * `is_hello`: the slice-vs-array `==`, both outcomes.
//  * `raw_reborrow`: the explicit `*const [u8] as *const u8` cast and `&*p`.
//  * `dyn_reborrow`: the TRAIT-OBJECT twin, `*const dyn Get as *const u8`
//    and `&*p`, which reads the first byte of the object's data.
#![allow(dead_code)]

trait Get {
    fn get(&self) -> u8;
}

struct Two([u8; 2]);

impl Get for Two {
    fn get(&self) -> u8 {
        self.0[1]
    }
}

#[inline(never)]
fn head4(s: &[u8]) -> u32 {
    match s.as_array::<4>() {
        Some(a) => u32::from_le_bytes(*a),
        None => 0,
    }
}

#[inline(never)]
fn is_hello(s: &[u8]) -> bool {
    s == b"hello world"
}

#[inline(never)]
fn raw_reborrow(s: &[u8]) -> u8 {
    let p = s as *const [u8] as *const u8;
    let r: &u8 = unsafe { &*p };
    *r
}

#[inline(never)]
fn dyn_reborrow(x: &dyn Get) -> (u8, u8) {
    let p = x as *const dyn Get as *const u8;
    let r: &u8 = unsafe { &*p };
    (*r, x.get())
}

fn main() {
    let hay: &[u8] = std::hint::black_box(b"hello world");
    println!("r1 {}", head4(&hay[..4]));
    println!("r2 {}", head4(hay));
    println!("r3 {}", head4(&hay[7..]));
    println!("r4 {}", is_hello(hay));
    println!("r5 {}", is_hello(&hay[..5]));
    println!("r6 {}", raw_reborrow(&hay[4..]));
    let two = Two([41, 42]);
    let (first, second) = dyn_reborrow(&two);
    println!("r7 {} {}", first, second);
}
