// Corpus: a FAT POINTER (`&[T]` / `&str`) inside a UNION field — the
// `MaybeUninit<T>` shape, whose slot is opaque bytes and whose active field is
// written at offset 0.
//
// `union_memory_layout` used to refuse ANY union whose field subtree contained a
// fat-pointer leaf ("union field … is a fat pointer … not yet supported"), which
// on a `library/core` census was 19 failed roots (rank 4), every one of them
// `MaybeUninit<core::num::fmt::Part<'_>>` — the buffer `core::fmt::float`'s
// decimal/exponential formatters build their output parts in.
//
// The refusal was an ADMISSION gate, not a model: a union slot carries no
// per-field leaf information at all (it is `size` raw bytes at one lane group),
// and every access re-derives its own leaf types through machinery that gates
// fat pointers on its own (`memory_scalar_leaf_ty` rejects a `ScalarPair`
// unconditionally; the whole-value copy is a raw lane copy). Lifting it can
// only turn an early refusal into a correct emission or a later, precise one.
//
// What a WRONG lowering would look like, and what pins it here:
//   * a one-lane store of the fat leaf writes `data` and leaves `len` stale, so
//     the read-back slice has the WRONG LENGTH — every case below prints the
//     length AND the elements;
//   * a fat leaf bound into a single lane SHIFTS every later field, so each
//     shape carries an ordinary scalar field AFTER the fat one (`tail`), whose
//     value is printed;
//   * `Part`-like enums put the fat payload in a non-zero variant, so a dropped
//     metadata lane survives a `Zero`/`Num` read and only shows on `Copy`.
#![allow(dead_code)]

use core::mem::MaybeUninit;

// The exact shape of `core::num::fmt::Part<'_>`.
enum Part<'a> {
    Zero(usize),
    Num(u16),
    Copy(&'a [u8]),
}

fn part_val(p: &Part<'_>) -> i64 {
    match p {
        Part::Zero(n) => 1_000_000 + *n as i64,
        Part::Num(n) => 2_000_000 + *n as i64,
        Part::Copy(s) => {
            let mut acc = 3_000_000 + s.len() as i64 * 1000;
            for b in *s {
                acc += *b as i64;
            }
            acc
        }
    }
}

// A fat leaf FOLLOWED by a scalar — a lane shift moves `tail`.
struct Rec<'a> {
    s: &'a [u8],
    tail: i64,
}

struct Named<'a> {
    name: &'a str,
    tail: i64,
}

#[inline(never)]
fn build_part<'a>(s: &'a [u8]) -> MaybeUninit<Part<'a>> {
    MaybeUninit::new(Part::Copy(s))
}

#[inline(never)]
fn build_rec<'a>(s: &'a [u8], tail: i64) -> MaybeUninit<Rec<'a>> {
    MaybeUninit::new(Rec { s, tail })
}

#[inline(never)]
fn build_named<'a>(name: &'a str, tail: i64) -> MaybeUninit<Named<'a>> {
    MaybeUninit::new(Named { name, tail })
}

#[inline(never)]
fn rec_val(r: &Rec<'_>) -> i64 {
    let mut acc = r.s.len() as i64 * 1_000_000 + r.tail;
    for b in r.s {
        acc += *b as i64;
    }
    acc
}

#[inline(never)]
fn named_val(n: &Named<'_>) -> i64 {
    let mut acc = n.name.len() as i64 * 1_000_000 + n.tail;
    for b in n.name.as_bytes() {
        acc += *b as i64;
    }
    acc
}

// The read side is `assume_init_ref` (a pointer CAST through the slot), which
// IS the union access model: the slot is opaque bytes and every typed access
// casts a pointer to the field type. `assume_init`'s by-value `Transmute` out
// of the slot is a SEPARATE, still-fail-closed path ("memory-backed enum
// assignment Transmute from non-int / width mismatch") and is deliberately not
// exercised here — this row pins the lane placement, not that transmute.
fn main() {
    let a = [3u8, 5, 7, 11];
    let b = [1u8, 2];

    // 1. a fat-payload enum through a union slot, three different LENGTHS
    let m = build_part(&a);
    println!("a {}", part_val(unsafe { m.assume_init_ref() }));
    let m2 = build_part(&b[..1]);
    println!("b {}", part_val(unsafe { m2.assume_init_ref() }));
    let m3 = build_part(&[]);
    println!("c {}", part_val(unsafe { m3.assume_init_ref() }));

    // 2. the scalar-payload variants of the same enum: a dropped metadata lane
    //    survives these, so they are the control, not the subject.
    let z: MaybeUninit<Part<'_>> = MaybeUninit::new(Part::Zero(9));
    println!("d {}", part_val(unsafe { z.assume_init_ref() }));
    let n: MaybeUninit<Part<'_>> = MaybeUninit::new(Part::Num(1234));
    println!("e {}", part_val(unsafe { n.assume_init_ref() }));

    // 3. a struct whose fat leaf is FOLLOWED by a scalar — a fat pointer bound
    //    into one lane shifts `tail`.
    let r = build_rec(&a, 77);
    println!("f {}", rec_val(unsafe { r.assume_init_ref() }));
    let r2 = build_rec(&b, -5);
    println!("g {}", rec_val(unsafe { r2.assume_init_ref() }));

    // 4. `&str` metadata, same shape
    let nm = build_named("hello", 21);
    println!("h {}", named_val(unsafe { nm.assume_init_ref() }));
    let nm2 = build_named("hi", -3);
    println!("i {}", named_val(unsafe { nm2.assume_init_ref() }));
}
