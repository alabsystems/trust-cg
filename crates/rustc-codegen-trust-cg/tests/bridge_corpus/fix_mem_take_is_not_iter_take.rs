// CORPUS FIXTURE — `mem::take` is NOT `Iterator::take`: the structural-adapter
// interceptor's DESTINATION-IDENTITY gate.
//
// WHAT IT PINS. `lower_iterator_call`'s structural-adapter dispatch matched on the
// callee's ITEM NAME (`copied`/`cloned`/`rev`/`take`/`skip`/`step_by`/`enumerate`)
// plus two provenance checks plus `resolve_iter_chain(dest_ty).is_some()`. That
// last clause is satisfied by ANY modelled chain — a BARE base iterator included —
// so it does not establish that the call is the adapter constructor its name
// suggests. Measured 2026-09-26 at `-Copt-level=0`:
// `core::mem::take::<slice::Iter<'_, u8>>(&mut self.iter)` satisfies all of them
// (item name `take`, defined in the real `core`, destination `slice::Iter<u8>`
// which resolves as a chain) and was routed into `lower_iter_structural_ctor` as
// if it were `Iterator::take`. It survived there only because `&mut Iter` is not
// memory-backed, refusing as
// `iterator take inner argument is not memory-backed` — 1 of `library/alloc`'s
// 37 failed roots, `<alloc::vec::Drain<u8> as Drop>::drop`, whose `let iter =
// mem::take(&mut self.iter)` is exactly this call.
//
// Had that argument been memory-backed, the adapter constructor would have copied
// `size_of::<&mut Iter>()` = 8 bytes — the POINTER — into a 24-byte `slice::Iter`
// slot as its "inner iterator state", left `*src` un-defaulted, and written no
// count field at all (`chain.adapters` is empty for a base iterator, so the `Take`
// initializer never runs). NOT A DEMONSTRATED MISCOMPILE: `mem::take`'s signature
// takes `&mut T`, and no rule memory-backs a reference-typed local, so on this
// tree the refusal is unconditional. The gate is what makes that a property of the
// DISPATCH rather than of an unrelated representation check.
//
// `Iterator::take` returns `Take<Self>`, `skip` returns `Skip<Self>`, and so on
// for every name in that list, with no exception in the standard surface. So the
// gate requires the destination's own outermost ADT to BE the adapter the name
// constructs, by `adapter_kind_of`'s def-path identity — never a type-name
// compare. It only ever NARROWS interception: a call that fails it falls through
// to the general, itself-fail-closed call path and is lowered from its real body,
// which is what `split_off` below now does.
//
// `real_take` / `real_skip` are in the same program so the row also pins that the
// narrowing did not withdraw the adapters this lane models.
//
// MUTATION-MEASURED. Disabling the gate returns this fixture to
// `iterator take inner argument is not memory-backed` and returns the
// `library/alloc` root. Mapping `"take"` to the WRONG `AdapterTag` does NOT
// produce a divergence — the real `.take(3)` simply stops being intercepted and
// its own body is correct at `-O0` — so the per-name mapping is defence in depth,
// and the clause that closes the measured hole is "the destination is an adapter
// at all".
#![allow(dead_code)]

#[inline(never)]
fn split_off(v: &[u8]) -> (usize, usize) {
    let mut it = v.iter();
    let _ = it.next();
    let taken = core::mem::take(&mut it);
    (taken.len(), it.len())
}

#[inline(never)]
fn real_take(n: u32) -> u32 {
    let mut s = 0u32;
    for x in (0u32..n).take(3) {
        s = s + x;
    }
    s
}

#[inline(never)]
fn real_skip(n: u32) -> u32 {
    let mut s = 0u32;
    for x in (0u32..n).skip(2) {
        s = s + x;
    }
    s
}

fn main() {
    let data: [u8; 5] = [1, 2, 3, 4, 5];
    let (a, b) = split_off(&data);
    println!("take {} {}", a, b);
    let r = real_take(10);
    let k = real_skip(6);
    println!("adapters {} {}", r, k);
}
