// Corpus: a `&[T]` / `&str` FAT LEAF inside an aggregate that carries NO `&dyn`
// field — the ISOLATION `dyn_leaf_fat_in_aggregate.rs` lacks.
//
// That program's `struct Both` holds a `&dyn Shape` beside its slice/`&str`
// fields. `rust_ty_to_trust_ir_ty` has no `dyn` mapping, so the by-reference
// pointee FLATTENING fails on that field and the whole aggregate falls onto the
// rustc-layout byte path — which is correct, and which is why the slice/`str`
// half of the two-lane leaf model was never exercised on its own there.
//
// Without a `&dyn` field the flattening SUCCEEDS, and it mapped each `&[T]` /
// `&str` field to ONE `Ptr` lane: the pointee tuple was then 8 bytes short per
// fat field and every later field sat at the wrong byte offset, while the callee
// read `(*r).field` at rustc's real offsets. Measured before the fix: `read`
// below returned a text-segment ADDRESS where LLVM returned `26`.
//
// Every read here goes THROUGH A THIN REFERENCE (`&Rec`), which is the shape
// that disagreed; the owned-local reads are kept beside them so a fix that
// merely refused the reference shape would still show as a difference here.
#![allow(dead_code)]

struct Rec<'a> {
    head: i64,
    slice: &'a [i64],
    name: &'a str,
    tail: i64,
}

// A fat leaf FIRST, so the lane/offset disagreement shows up on the very next
// field rather than only at the end of the aggregate.
struct FatFirst<'a> {
    name: &'a str,
    tail: i64,
}

#[inline(never)]
fn store_and_reload<'a>(s: &'a [i64], n: &'a str) -> Rec<'a> {
    Rec {
        head: 1,
        slice: s,
        name: n,
        tail: 2,
    }
}

// Reads BOTH the scalar fields and both fat leaves through the reference: the
// scalar fields are what a short lane tuple mis-addresses, the fat leaves are
// what it truncates.
#[inline(never)]
fn read(b: &Rec<'_>) -> i64 {
    let mut acc = b.head + b.tail;
    acc += b.slice.len() as i64;
    for v in b.slice {
        acc += *v;
    }
    acc += b.name.len() as i64;
    acc
}

#[inline(never)]
fn scalars_only(b: &Rec<'_>) -> i64 {
    b.head * 100 + b.tail
}

#[inline(never)]
fn read_fat_first(b: &FatFirst<'_>) -> i64 {
    b.name.len() as i64 * 100 + b.tail
}

fn main() {
    let data = [3i64, 5, 7];
    let b = store_and_reload(&data, "hello");
    println!("a {}", read(&b));
    println!("b {}", scalars_only(&b));
    println!("c {}", read(&store_and_reload(&data[1..], "hi")));
    let f = FatFirst {
        name: "hello",
        tail: 22,
    };
    println!("d {}", read_fat_first(&f));
}
