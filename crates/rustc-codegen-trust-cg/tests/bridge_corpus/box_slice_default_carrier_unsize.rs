// Corpus: a `PointerCoercion::Unsize` whose DESTINATION is a
// `#[repr(transparent)]` CARRIER of a slice fat pointer rather than the bare
// pointer — `Unique<[T; 0]> -> Unique<[T]>`, which is the entire body of
// `<Box<[T]> as Default>::default`:
//
//     fn default() -> Self {
//         let ptr: Unique<[T]> = Unique::<[T; 0]>::dangling();
//         Box(ptr, Global)
//     }
//
// `lower_pointer_unsize` keyed its slice arm on `is_slice_reference_ty(dst_ty)`,
// which answers `false` for a carrier, so this fell through to the generic
// refusal "PointerCoercion::Unsize destination is not a slice or trait-object
// reference: core::ptr::Unique<[u8]>" — one `library/alloc` root.
//
// `repr(transparent)` is why the carrier coerces exactly as its payload does:
// rustc guarantees the carrier has the LAYOUT and ABI of its single non-ZST
// field at offset 0, so `Unique<[T]>` IS the `{ data, len }` `ScalarPair`, and
// its `CoerceUnsized` impl forwards to the payload's coercion. The data half is
// unchanged; the metadata is the SOURCE array's element count.
//
// WHAT A REGRESSION LOOKS LIKE. Both rows print a LENGTH read back out of the
// coerced pointer, which is the only thing the coercion supplies:
//   * `0` for `Box<[u8]>` and `0` for `Box<[i64]>` — the length of a `[T; 0]`.
//     A length taken from the DESTINATION element type rather than the source
//     array, or a byte count instead of an element count, prints a non-zero
//     number; a metadata lane left uninitialized prints garbage (and, unlike a
//     wrong number, usually a different one on each run).
//   * TWO element widths, so a length accidentally scaled by `size_of::<T>()`
//     diverges on at least one row.
//
// `mem::forget` keeps the zero-length deallocation (a `size != 0` test, i.e. an
// `AArch64::CSet` this host's opcode-proof inventory does not map) out of the
// row, so a `[TCG-PROOF-465]` refusal cannot hide the verdict. The lengths are
// funnelled through `#[inline(never)]` helpers because a `.len()` read INSIDE a
// `format!` argument was refused for an unrelated reason (`[TCG-FMT-LEN]`,
// removed 2026-10-03).
#![allow(dead_code)]

#[inline(never)]
fn mk_u8() -> Box<[u8]> {
    Box::default()
}
#[inline(never)]
fn mk_i64() -> Box<[i64]> {
    Box::default()
}
#[inline(never)]
fn len_u8(b: &[u8]) -> i64 {
    b.len() as i64
}
#[inline(never)]
fn len_i64(b: &[i64]) -> i64 {
    b.len() as i64
}
#[inline(never)]
fn emit(x: i64) {
    println!("{}", x);
}

fn main() {
    let b = mk_u8();
    let c = mk_i64();
    emit(len_u8(&b));
    emit(len_i64(&c));
    core::mem::forget(b);
    core::mem::forget(c);
}
