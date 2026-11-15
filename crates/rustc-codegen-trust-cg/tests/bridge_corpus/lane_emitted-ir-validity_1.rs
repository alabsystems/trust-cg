// CORPUS FIXTURE — lane emitted-ir-validity, shape 1: a thin-pointer REBORROW
// `&*p` / `&mut *p` of a RAW pointer returned as a REFERENCE. The bridge used
// to bind the returned `&T` to the raw pointer's own value (typed
// `PtrConst(T)` / `PtrMut(T)`), so trust-cg's return-signature check refused
// every `<[T]>::get_unchecked`, `NonNull::as_ref`, `MaybeUninit::assume_init_mut`
// … in `core` with "operand has PtrConst(U32), expected Ref(U32)".
// The values printed depend on the reborrowed reference being the SAME address
// (writes through `&mut *p` are observed through the original local).
// The `&mut`-returning callees are reached through a fn POINTER: a DIRECT call
// of a `-> &mut T` fn is a separate (call-site) refusal owned by another lane.
use std::hint::black_box;

#[inline(never)]
fn deref_const(p: *const u32) -> &'static u32 {
    unsafe { &*p }
}

#[inline(never)]
fn deref_mut(p: *mut u32) -> &'static mut u32 {
    unsafe { &mut *p }
}

#[inline(never)]
fn deref_mut_as_shared(p: *mut u64) -> &'static u64 {
    unsafe { &*p }
}

#[inline(never)]
fn reborrow_ref(r: &u32) -> &u32 {
    &*r
}

#[inline(never)]
fn reborrow_mut(r: &mut u32) -> &mut u32 {
    &mut *r
}

fn main() {
    let x: u32 = black_box(41);
    let r = deref_const(&x as *const u32);
    println!("{}", *r + 1);

    let mut y: u32 = black_box(5);
    let dm: fn(*mut u32) -> &'static mut u32 = black_box(deref_mut);
    let m = dm(&mut y as *mut u32);
    *m += 3;
    println!("{}", y);

    let z: u64 = black_box(1 << 40);
    let mut z2 = z;
    let s = deref_mut_as_shared(&mut z2 as *mut u64);
    println!("{}", *s >> 40);

    let a: u32 = black_box(7);
    println!("{}", *reborrow_ref(&a) * 2);
    let mut b: u32 = black_box(10);
    let rm: fn(&mut u32) -> &mut u32 = black_box(reborrow_mut);
    *rm(&mut b) += 5;
    println!("{}", b);
}
