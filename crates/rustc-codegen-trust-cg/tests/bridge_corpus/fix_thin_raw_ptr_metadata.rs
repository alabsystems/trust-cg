// THIN-POINTER metadata: `<T as Pointee>::Metadata` is `()` for every `T: Sized`,
// so `PtrMetadata(*const T)` produces NO BITS and `from_raw_parts_mut(data, ())`
// IS the data pointer.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Both shapes are `library/core` census roots at `-Copt-level=0`:
//   core::ptr::metadata::<()>             -> "pointer metadata unsupported operand type *const ()"
//   core::ptr::from_raw_parts_mut::<(),()> -> "AggregateKind::RawPtr"
// The first died in the slice-LENGTH resolver (which only knows the fat forms);
// the second in the generic `AggregateKind::RawPtr` refusal. A wrong answer here
// is SILENT — the rebuilt pointer would address the wrong object — so the store
// through it is read back and printed.
#![feature(ptr_metadata)]

use std::ptr;

#[inline(never)]
fn thin_meta(p: *const u64) -> i32 {
    let () = ptr::metadata(p);
    7
}

#[inline(never)]
fn rebuild(p: *mut u64) -> *mut u64 {
    ptr::from_raw_parts_mut(p as *mut (), ())
}

fn main() {
    let mut x = 5u64;
    let q = rebuild(std::hint::black_box(&mut x as *mut u64));
    unsafe { *q = 9 };
    // 7 + 9 == 16: the metadata call is a no-op AND the rebuilt pointer really
    // addressed `x`.
    println!("{}", thin_meta(std::hint::black_box(&x as *const u64)) + (x as i32));
}
