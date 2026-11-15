// A whole-object store of an aggregate holding a `NonNull<dyn Tr>` WIDE leaf beside
// an enum byte, an fn pointer and a `u16`, nested at depth 1 (`S1`), stored by
// `*dst = v` through `&mut T` and read back through `&T` and `*const T`. The
// scalar-leaf flattener refuses the wide leaf, so the pointee is typed as a
// uniform lane tiling and the store must take the whole-image lane copy
// (`wide_leaf_lane_tiling_store_differential.rs`).
#![allow(dead_code, unused_unsafe)]
use std::ptr::NonNull;
trait Tr { fn v(&self) -> u64; }
struct A(u64);
impl Tr for A { fn v(&self) -> u64 { self.0 * 3 + 1 } }
struct B(u64, u32);
impl Tr for B { fn v(&self) -> u64 { self.0 * 1000 + self.1 as u64 } }
type Leaf = NonNull<dyn Tr>;
static mut GA: [A; 128] = [const { A(0) }; 128];
static mut GB: [B; 128] = [const { B(0, 7) }; 128];
static mut ARR16: [u16; 4] = [2, 3, 5, 8];
static ARR32: [u32; 3] = [4, 11, 13];
static STR8: &str = "abcdefgh";
/// A `*mut dyn Tr` whose unsize source is a runtime PLACE (`black_box`). The
/// impl is chosen through a fn pointer, so both vtables are exercised without
/// a CFG merge of two fat values.
#[inline(never)]
fn dyn_ptr_a(i: u64) -> *mut dyn Tr {
    let k = (i % 128) as usize;
    unsafe { GA[k].0 = i };
    let q: *mut A = core::hint::black_box(unsafe { &raw mut GA[k] });
    q
}
#[inline(never)]
fn dyn_ptr_b(i: u64) -> *mut dyn Tr {
    let k = (i % 128) as usize;
    unsafe { GB[k].0 = i };
    let q: *mut B = core::hint::black_box(unsafe { &raw mut GB[k] });
    q
}
static DYN_PTR: [fn(u64) -> *mut dyn Tr; 2] = [dyn_ptr_a, dyn_ptr_b];
#[inline(never)]
fn dyn_ptr(i: u64) -> *mut dyn Tr {
    let f = DYN_PTR[(i % 2) as usize];
    f(i)
}
#[inline(never)]
fn mk_leaf(i: u64) -> Leaf { unsafe { NonNull::new_unchecked(dyn_ptr(i)) } }
#[inline(never)]
fn read_leaf(l: &Leaf) -> u64 { unsafe { l.as_ref().v() } }

#[derive(Clone, Copy)]
#[repr(u8)]
enum Kind { X = 1, Y = 7 }
fn f_a(x: u64) -> u64 { x * 5 + 3 }
fn f_b(x: u64) -> u64 { x * 11 + 2 }
struct S1 { kind: Kind, leaf: Leaf, f1: fn(u64) -> u64, tag: u16 }

type T = S1;
#[inline(never)]
fn mk(i: u64) -> T { S1 { kind: if i % 3 == 0 { Kind::X } else { Kind::Y }, leaf: mk_leaf(i), f1: if i % 2 == 0 { f_a } else { f_b }, tag: (i * 7) as u16 } }
#[inline(never)]
fn read_ref(t: &T) -> u64 {
    let i = 4u64;
    let s1 = &t;
    0u64.wrapping_add(((s1.kind as u64) * 100000).wrapping_add(read_leaf(&s1.leaf).wrapping_mul(10)).wrapping_add((s1.f1)(i % 13) * 3).wrapping_add(s1.tag as u64))
}
#[inline(never)]
fn read_ptr(p: *const T) -> u64 {
    let t = unsafe { &*p };
    let i = 6u64;
    let s1 = unsafe { &(*p) };
    0u64.wrapping_add(((s1.kind as u64) * 100000).wrapping_add(read_leaf(&s1.leaf).wrapping_mul(10)).wrapping_add((s1.f1)(i % 13) * 3).wrapping_add(s1.tag as u64))
}
#[inline(never)]
fn store(dst: &mut T, v: T) { *dst = v; }
#[inline(never)]
fn run(i: u64) -> u64 {
    let v = mk(i);
    let mut d = mk(90); store(&mut d, v); let r = read_ref(&d).wrapping_mul(7).wrapping_add(read_ptr(&d as *const T)); std::mem::forget(d); r
}
fn main() {
    let mut acc = 0u64;
    for i in 1..6u64 {
        let r = run(i);
        println!("{}", r);
        acc = acc.wrapping_mul(31).wrapping_add(r);
    }
    let size = std::mem::size_of::<T>();
    println!("acc {}", acc);
    println!("size {}", size);
}
