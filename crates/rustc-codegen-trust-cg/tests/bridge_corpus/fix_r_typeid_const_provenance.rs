// Corpus: a `TypeId` CONST with POINTER PROVENANCE stored as a whole aggregate.
//
// `core::any::TypeId` is `[*const (); 16 / size_of::<*const ()>()]`, and its own
// definition explains why: "there is provenance in the first array field. This
// provenance knows exactly which type the TypeId actually is, allowing CTFE and
// miri to operate based off it. At runtime all the pointers in the array contain
// bits of the hash."
//
// The const byte-copy path refused ANY allocation carrying a pointer relocation,
// on the correct general argument that a raw byte copy would DROP the relocation
// and store an offset into an allocation whose address is not known until link
// time. `GlobalAlloc::TypeId` is the one kind for which that argument does not
// hold, and again it is not ours to decide — rustc's own LLVM backend says so in
// `rustc_codegen_llvm::common`:
//
//     GlobalAlloc::TypeId { .. } => {
//         // Drop the provenance, the offset contains the bytes of the hash
//         let llval = self.const_usize(offset.bytes());
//
// and `const_alloc_to_llvm` reads that same offset straight back out of the
// allocation's raw bytes. So for THIS provenance kind the bytes already in the
// allocation ARE the runtime value, and a byte copy reproduces LLVM bit-for-bit.
// Every other `GlobalAlloc` kind still fails closed.
//
// WHY EVERY ROW IS A WRONG ANSWER, NOT A CRASH, IF THE BYTES ARE WRONG: a dropped
// or corrupted relocation does not trap — it yields a TypeId holding the wrong
// bits, and every comparison below silently flips.
//   * `same 1 1 1` — a type's id equals ITSELF across two independent calls. A
//     zeroed relocation still passes this one (0 == 0), which is exactly why the
//     next row exists.
//   * `diff 0 0 0` — DISTINCT types have DISTINCT ids. If the relocation were
//     dropped to a constant, every id would collide and these become `1 1 1`.
//   * `rt 1 0` — an id round-tripped through a by-value struct field across two
//     ABI boundaries (the whole-aggregate memory store this fixture is about)
//     still compares equal to a freshly computed one, and still unequal to
//     another type's.
//   * `pair 1 0` — two ids side by side in one aggregate, so a copy that got the
//     OFFSET wrong (right bytes, wrong slot) is caught rather than masked.
#![allow(dead_code)]

use std::any::TypeId;

struct Wrap {
    id: TypeId,
    tag: i64,
}

struct Pair {
    a: TypeId,
    b: TypeId,
}

#[inline(never)]
fn id_of<T: 'static>() -> TypeId {
    TypeId::of::<T>()
}

#[inline(never)]
fn wrap<T: 'static>(tag: i64) -> Wrap {
    Wrap {
        id: id_of::<T>(),
        tag,
    }
}

#[inline(never)]
fn unwrap_id(w: Wrap) -> TypeId {
    w.id
}

#[inline(never)]
fn pair_of<A: 'static, B: 'static>() -> Pair {
    Pair {
        a: id_of::<A>(),
        b: id_of::<B>(),
    }
}

struct Local(i64);
struct Other(i64);

fn main() {
    // A type's id equals itself, computed twice through separate calls.
    let s1 = (id_of::<u32>() == id_of::<u32>()) as i32;
    let s2 = (id_of::<Local>() == id_of::<Local>()) as i32;
    let s3 = (id_of::<(i64, u8)>() == id_of::<(i64, u8)>()) as i32;
    println!("same {} {} {}", s1, s2, s3); // 1 1 1

    // Distinct types have distinct ids. This is the row a dropped relocation
    // fails: collapse every id to a constant and all three become 1.
    let d1 = (id_of::<u32>() == id_of::<i64>()) as i32;
    let d2 = (id_of::<Local>() == id_of::<Other>()) as i32;
    let d3 = (id_of::<(i64, u8)>() == id_of::<(u8, i64)>()) as i32;
    println!("diff {} {} {}", d1, d2, d3); // 0 0 0

    // Round-trip through a by-value aggregate field across two ABI boundaries.
    let w = wrap::<Local>(5);
    let t = w.tag;
    let got = unwrap_id(w);
    let r1 = (got == id_of::<Local>()) as i32;
    let r2 = (got == id_of::<Other>()) as i32;
    println!("rt {} {}", r1, r2); // 1 0
    println!("tag {}", t); // 5

    // Two ids in ONE aggregate: catches a copy that wrote the right bytes at the
    // wrong offset (both fields would then read as the same id).
    let p = pair_of::<Local, Other>();
    let q1 = (p.a == id_of::<Local>()) as i32;
    let q2 = (p.a == p.b) as i32;
    println!("pair {} {}", q1, q2); // 1 0
}
