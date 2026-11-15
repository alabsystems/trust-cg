// CONTROL for `fix_refret_cell_nonprimitive.rs`: an INTERCEPTED collection
// referent must STILL be refused, with the same diagnostic.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// `Vec` models as a single `Ptr` whose value IS the address of a synthesized
// `{ptr,cap,len}` slot produced by the interception, not by a cell slot; celling
// the `Vec` local puts a second slot in front of it and the intercept's value is
// never defined at its use. That is exactly why the reference-escaping cell pass
// was originally narrowed to `Int/Uint/Float/Bool/Char`, and the widening keeps
// it out by the interception PREDICATE (`vec_element_ty`/`is_string_ty`/… in
// `cellable_reference_referent_ty`) rather than by a typed heuristic — a typed
// guard is defeatable (`&mut *(p as *mut NonNull<u8> as *mut u8)`).
//
// Compiled with the bridge this program must FAIL CLOSED with
//
//   promoted mutable scalar reference return is unsupported
//
// A row that COMPILES here is a regression, not a win.
#[inline(never)]
fn first_mut(v: &mut Vec<u64>) -> &mut u64 {
    &mut v[0]
}

fn main() {
    let mut v: Vec<u64> = Vec::new();
    v.push(3);
    let r = first_mut(&mut v);
    *r = 8;
    println!("{}", v[0]);
}
