// Guest program of `mir_families_aarch64` (ledger L06-P8): `Rvalue::Discriminant`
// over every enum layout class, written as custom MIR so each read is one
// statement on a named place, compiled by the bridge and by rustc's LLVM
// backend and compared.
//
// Layouts: Direct tags whose discriminants are not the variant index
// (`#[repr(i16)]` negative and wide, `#[repr(u8)]` above 127, with payloads),
// a fieldless enum (`#[repr(u8)]`), niches in a `bool`, a `char`, a reference,
// a `NonZeroU64`, an explicit-discriminant tag (`Option<R8>`) and a nested
// `Option<Option<bool>>` (outer and inner), and a single-variant layout.
// Places: through a reference, a field through a reference, a variant field
// through a reference, an array element at a runtime index, and a by-value
// argument.
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
use core::intrinsics::mir::*;
use std::hint::black_box;
use std::num::NonZeroU64;

#[derive(Clone, Copy)]
#[repr(i16)]
pub enum Wide {
    A(u8) = -1,
    B(u32) = -300,
    C = 7,
}

#[derive(Clone, Copy)]
#[repr(u8)]
pub enum R8 {
    A(u8) = 10,
    B(u16) = 200,
    C = 3,
}

#[derive(Clone, Copy)]
#[repr(u8)]
pub enum F8 {
    A = 10,
    B = 200,
    C = 3,
}

#[derive(Clone, Copy)]
pub enum Single {
    Only(u32),
}

#[derive(Clone, Copy)]
pub struct Holder {
    pub p: u8,
    pub r: R8,
    pub w: Wide,
}

#[derive(Clone, Copy)]
pub enum Outer {
    O0(Wide),
    O1,
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn disc_wide(x: &Wide) -> i16 {
    mir! {
        { RET = Discriminant(*x); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn disc_wide_value(x: Wide) -> i16 {
    mir! {
        { RET = Discriminant(x); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn disc_r8_field(x: &Holder) -> u8 {
    mir! {
        { RET = Discriminant((*x).r); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn disc_wide_field(x: &Holder) -> i16 {
    mir! {
        { RET = Discriminant((*x).w); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn disc_variant_field(x: &Outer) -> i16 {
    mir! {
        { RET = Discriminant(Field::<Wide>(Variant(*x, 0), 0)); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn disc_index(x: &[Wide; 4], i: usize) -> i16 {
    mir! {
        { RET = Discriminant((*x)[i]); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn disc_f8(x: &F8) -> u8 {
    mir! {
        { RET = Discriminant(*x); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn disc_opt_r8(x: &Option<R8>) -> isize {
    mir! {
        { RET = Discriminant(*x); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn disc_opt_bool(x: &Option<bool>) -> isize {
    mir! {
        { RET = Discriminant(*x); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn disc_opt_char(x: &Option<char>) -> isize {
    mir! {
        { RET = Discriminant(*x); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn disc_opt_ref(x: &Option<&u32>) -> isize {
    mir! {
        { RET = Discriminant(*x); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn disc_opt_nonzero(x: &Option<NonZeroU64>) -> isize {
    mir! {
        { RET = Discriminant(*x); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn disc_nested_outer(x: &Option<Option<bool>>) -> isize {
    mir! {
        { RET = Discriminant(*x); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn disc_nested_inner(x: &Option<Option<bool>>) -> isize {
    mir! {
        { RET = Discriminant(Field::<Option<bool>>(Variant(*x, 1), 0)); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn disc_single(x: &Single) -> isize {
    mir! {
        { RET = Discriminant(*x); Return() }
    }
}

#[inline(never)]
fn pick<T: Copy>(z: u32, items: &[T]) -> T {
    items[z as usize % items.len()]
}

/// The values read, in order (no heap: the line is the whole observation).
struct Out {
    values: [i64; 64],
    len: usize,
}

impl Out {
    fn push(&mut self, value: i64) {
        self.values[self.len] = value;
        self.len += 1;
    }
}

fn main() {
    let z = black_box(0u32);
    let mut out = Out { values: [0; 64], len: 0 };

    for w in [Wide::A(3), Wide::B(70_000), Wide::C] {
        let w = pick(z, &[w]);
        out.push(disc_wide(&w) as i64);
        out.push(disc_wide_value(w) as i64);
    }
    for (r, w) in [(R8::A(1), Wide::C), (R8::B(513), Wide::A(2)), (R8::C, Wide::B(9))] {
        let h = Holder { p: 5, r: pick(z, &[r]), w: pick(z, &[w]) };
        out.push(disc_r8_field(&h) as i64);
        out.push(disc_wide_field(&h) as i64);
    }
    for o in [Outer::O0(Wide::B(4)), Outer::O0(Wide::A(1))] {
        out.push(disc_variant_field(&pick(z, &[o])) as i64);
    }
    let arr = [Wide::C, Wide::A(8), Wide::B(1), Wide::C];
    for i in 0..4 {
        out.push(disc_index(&arr, black_box(i)) as i64);
    }
    for f in [F8::A, F8::B, F8::C] {
        out.push(disc_f8(&pick(z, &[f])) as i64);
    }
    for r in [None, Some(R8::A(0)), Some(R8::B(2)), Some(R8::C)] {
        out.push(disc_opt_r8(&pick(z, &[r])) as i64);
    }
    for b in [None, Some(false), Some(true)] {
        out.push(disc_opt_bool(&pick(z, &[b])) as i64);
    }
    for c in [None, Some('\0'), Some('\u{10FFFF}')] {
        out.push(disc_opt_char(&pick(z, &[c])) as i64);
    }
    let cell = black_box(17u32);
    for r in [None, Some(&cell)] {
        out.push(disc_opt_ref(&pick(z, &[r])) as i64);
    }
    for n in [None, NonZeroU64::new(u64::MAX)] {
        out.push(disc_opt_nonzero(&pick(z, &[n])) as i64);
    }
    for n in [None, Some(None), Some(Some(false)), Some(Some(true))] {
        let n = pick(z, &[n]);
        out.push(disc_nested_outer(&n) as i64);
        if n.is_some() {
            out.push(disc_nested_inner(&n) as i64);
        }
    }
    let single = Single::Only(black_box(3));
    out.push(disc_single(&single) as i64);

    let len = out.len;
    print!("{len}");
    for i in 0..len {
        let value = out.values[i];
        print!(" {value}");
    }
    println!();
}
