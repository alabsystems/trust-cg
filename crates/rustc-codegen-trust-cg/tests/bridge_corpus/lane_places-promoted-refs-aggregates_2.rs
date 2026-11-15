// Lane places-promoted-refs-aggregates, program 2: ZST newtypes whose every
// field is zero-sized (`Tag(PhantomData<..>)`, `Unit(())`) flowing as values,
// args and returns; and FAT -> FAT `PtrToPtr` casts of slice raw pointers
// (`&mut [T] as *mut [T] as *const [T]`) into
// memory-backed slots, read back through `len`.
#![allow(dead_code)]
use std::marker::PhantomData;

struct Tag<'a>(PhantomData<&'a ()>);
struct Unit(());

#[inline(never)]
fn mk_tag<'a>() -> Tag<'a> {
    Tag(PhantomData)
}

#[inline(never)]
fn mk_unit() -> Unit {
    Unit(())
}

#[inline(never)]
fn use_tag(_t: &Tag<'_>, x: u32) -> u32 {
    x + 1
}

#[inline(never)]
fn take_unit(_u: Unit, y: u32) -> u32 {
    y * 2
}

#[inline(never)]
fn cast_const_len(s: &mut [u32]) -> usize {
    let p = s as *mut [u32];
    let q: *const [u32] = p as *const [u32];
    q.len()
}

#[inline(never)]
fn opaque(x: usize) -> u64 {
    (x as u64) * 3 + 1
}

fn main() {
    let t = mk_tag();
    let u = mk_unit();
    let a = use_tag(&t, 41);
    let b = take_unit(u, a);
    println!("a={} b={}", a, b);

    let mut arr = [10u32, 20, 30, 40, 50];
    let mut arr3 = [7u32, 8, 9];
    let l5 = opaque(cast_const_len(&mut arr));
    let l3 = opaque(cast_const_len(&mut arr3));
    let l2 = opaque(cast_const_len(&mut arr3[1..]));
    println!("len5={} len3={} len2={}", l5, l3, l2);
}
