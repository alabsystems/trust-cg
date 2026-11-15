// Corpus: a one-lane local a loop changes ONLY through a mutable borrow of it.
//
// A `&mut x` call argument of a scalarized one-lane local is lowered by value:
// the bridge stores `x` into a borrow home, passes the home, and reloads and
// rebinds `x` after the call. A store through a `&mut x` taken before the loop
// rebinds `x` the same way. Neither is an assignment of `x`, so a local whose
// only pre-loop definition is a CALL result (`let mut p = first(xs)`) got no
// loop-header phi: each iteration re-stored the pre-loop value into the home
// and the loop exit read it.
//
// WHAT EACH ROW WOULD CATCH. Every printed value depends on the LAST
// write-back, so a dropped one prints the pre-loop value instead.
//  * `raw_ptr`, `ref`, `fn_ptr`, `non_null`, `newtype`: the pointer-like kinds
//    the hunt confirmed (`*const u64`, `&u64`, `fn(u64) -> u64`, `NonNull<u64>`,
//    a one-field pointer newtype).
//  * `ref_mut`: a stale `&mut u64` the loop re-seats; a later write through it
//    must land in the second array, not the first.
//  * `while_ptr`, `nested`, `two_borrows`, `header_borrow`, `loop_break`: the
//    loop forms (a `while`, the borrow in an inner loop only, two write-backs
//    in one iteration, the borrow in the loop condition, `loop` + `break`).
//    `header_borrow` is the one whose loop condition reads the write-back; it
//    is capped so a dropped write-back cannot spin forever.
//  * `generic`, `via_struct`: the `&mut` reaches the callee through a generic
//    helper and through a struct field.
//  * `preloop_store`: the borrow is taken BEFORE the loop and written through
//    inside it.
//  * `box_swap`, `box_user`: a `Box` replaced through `&mut` (the callee frees
//    the old box); a dropped write-back reads and frees a freed box again.
//  * `cond_borrow`: the borrow is taken on some iterations only.
//  * `two_args`: ONE call takes `&mut` of two such locals (both written back).
//  * `newtype_field`: the borrow names a FIELD of a one-field pointer newtype
//    (`&mut w.0`), which changes the newtype's one lane.
//  * `rc`: an `Rc` replaced through `&mut` (the -O2/-O3 exit reads its field).
//  * `reborrow_through` (CONTROL): `&mut *h.0` reborrows the pointee of a
//    one-field `&mut u64` newtype; that changes the pointee, never `h`, so it
//    must neither be threaded as a change of `h` nor refused.
use std::hint::black_box as bb;
use std::ptr::NonNull;
use std::rc::Rc;

#[inline(never)]
fn first(xs: &[u64]) -> *const u64 {
    xs.as_ptr()
}

#[inline(never)]
fn set(p: &mut *const u64, xs: &[u64], i: usize) {
    *p = &xs[i];
}

#[inline(never)]
fn last_is_last(xs: &[u64]) -> bool {
    let mut p = first(xs);
    for i in 0..xs.len() {
        set(&mut p, xs, i);
    }
    std::ptr::eq(p, &xs[xs.len() - 1])
}

#[inline(never)]
fn first_ref(xs: &[u64]) -> &u64 {
    &xs[0]
}

#[inline(never)]
fn set_ref<'a>(p: &mut &'a u64, xs: &'a [u64], i: usize) {
    *p = &xs[i];
}

#[inline(never)]
fn ref_call(xs: &[u64]) -> u64 {
    let mut r = first_ref(xs);
    for i in 0..xs.len() {
        set_ref(&mut r, xs, i);
    }
    *r
}

#[inline(never)]
fn f_a(x: u64) -> u64 {
    x + 1
}

#[inline(never)]
fn f_b(x: u64) -> u64 {
    x * 100
}

#[inline(never)]
fn pick_fn() -> fn(u64) -> u64 {
    f_a
}

#[inline(never)]
fn set_fn(f: &mut fn(u64) -> u64, i: usize) {
    *f = if i % 2 == 0 { f_b } else { f_a };
}

#[inline(never)]
fn fnptr_call(n: usize) -> u64 {
    let mut f = pick_fn();
    for i in 0..n {
        set_fn(&mut f, i);
    }
    f(7)
}

#[inline(never)]
fn nn0(xs: &mut [u64]) -> NonNull<u64> {
    NonNull::from(&mut xs[0])
}

#[inline(never)]
fn nnset(p: &mut NonNull<u64>, xs: &mut [u64], i: usize) {
    *p = NonNull::from(&mut xs[i]);
}

#[inline(never)]
fn nonnull_call(xs: &mut [u64]) -> u64 {
    let n = xs.len();
    let mut p = nn0(xs);
    for i in 0..n {
        nnset(&mut p, xs, i);
    }
    unsafe { *p.as_ptr() }
}

#[inline(never)]
fn mr0(xs: &mut [u64]) -> &mut u64 {
    &mut xs[0]
}

#[inline(never)]
fn mrset<'a>(p: &mut &'a mut u64, xs: &'a mut [u64]) {
    *p = xs.last_mut().unwrap();
}

#[inline(never)]
fn refmut_call(a: &mut [u64], b: &mut [u64]) -> u64 {
    let mut r = mr0(a);
    let mut once = Some(b);
    for _ in 0..2 {
        if let Some(b) = once.take() {
            mrset(&mut r, b);
        }
    }
    *r += 1;
    *r
}

#[derive(Clone, Copy)]
struct W(*const u64);

#[inline(never)]
fn w0(xs: &[u64]) -> W {
    W(xs.as_ptr())
}

#[inline(never)]
fn wset(w: &mut W, xs: &[u64], i: usize) {
    w.0 = &xs[i];
}

#[inline(never)]
fn newtype_call(xs: &[u64]) -> u64 {
    let mut w = w0(xs);
    for i in 0..xs.len() {
        wset(&mut w, xs, i);
    }
    unsafe { *w.0 }
}

#[inline(never)]
fn ptr_while(xs: &[u64]) -> u64 {
    let mut p = first(xs);
    let mut i = 0;
    while i < xs.len() {
        set(&mut p, xs, i);
        i += 1;
    }
    unsafe { *p }
}

#[inline(never)]
fn nested(xs: &[u64], n: usize) -> u64 {
    let mut p = first(xs);
    let mut acc = 0u64;
    for _ in 0..n {
        for i in 0..xs.len() {
            set(&mut p, xs, i);
        }
        acc += unsafe { *p };
        set(&mut p, xs, 0);
        acc += unsafe { *p };
    }
    acc * 100 + unsafe { *p }
}

#[inline(never)]
fn two_borrows(xs: &[u64]) -> u64 {
    let mut p = first(xs);
    let mut acc = 0u64;
    for i in 0..xs.len() - 1 {
        set(&mut p, xs, i);
        acc = acc * 10 + unsafe { *p };
        set(&mut p, xs, i + 1);
    }
    acc * 100 + unsafe { *p }
}

#[inline(never)]
fn adv(p: &mut *const u64, end: *const u64) -> bool {
    if *p == end {
        false
    } else {
        *p = unsafe { (*p).add(1) };
        true
    }
}

#[inline(never)]
fn header_borrow(xs: &[u64]) -> u64 {
    let mut p = first(xs);
    let end = &xs[xs.len() - 1] as *const u64;
    let mut n = 0u64;
    // Bounded, so a dropped write-back (the cursor never advances) prints a
    // wrong count instead of spinning forever.
    while adv(&mut p, end) {
        n += 1;
        if n == 50 {
            break;
        }
    }
    n * 100 + unsafe { *p }
}

#[inline(never)]
fn gset<T: Copy>(d: &mut T, v: T) {
    *d = v;
}

#[inline(never)]
fn generic(xs: &[u64]) -> u64 {
    let mut p = first(xs);
    for i in 0..xs.len() {
        gset(&mut p, &xs[i] as *const u64);
    }
    unsafe { *p }
}

#[inline(never)]
fn loop_break(xs: &[u64]) -> u64 {
    let mut p = first(xs);
    let mut i = 0;
    loop {
        if i == xs.len() {
            break;
        }
        set(&mut p, xs, i);
        i += 1;
    }
    unsafe { *p }
}

struct Holder<'a> {
    p: &'a mut *const u64,
}

#[inline(never)]
fn set_h(h: Holder<'_>, xs: &[u64], i: usize) {
    *h.p = &xs[i];
}

#[inline(never)]
fn via_struct(xs: &[u64]) -> u64 {
    let mut p = first(xs);
    for i in 0..xs.len() {
        set_h(Holder { p: &mut p }, xs, i);
    }
    unsafe { *p }
}

#[inline(never)]
fn preloop_store(xs: &[u64]) -> u64 {
    let mut p = first(xs);
    {
        let r = &mut p;
        for i in 0..xs.len() {
            *r = &xs[i];
        }
    }
    unsafe { *p }
}

#[inline(never)]
fn swap_in<T>(b: &mut Box<T>, v: T) -> T {
    *std::mem::replace(b, Box::new(v))
}

#[inline(never)]
fn box_swap(n: u64) -> u64 {
    let mut cur = Box::new(0u64);
    let mut acc = 0u64;
    for i in 0..n {
        acc = acc * 7 + swap_in(&mut cur, i * 10 + 5);
    }
    acc * 1000 + *cur
}

#[inline(never)]
fn box_new(v: u64) -> Box<u64> {
    Box::new(v)
}

#[inline(never)]
fn box_bump(b: &mut Box<u64>, i: u64) {
    let old = std::mem::replace(b, Box::new(**b * 3 + i));
    drop(old);
}

#[inline(never)]
fn box_user(n: u64) -> u64 {
    let mut b = box_new(1);
    for i in 0..n {
        box_bump(&mut b, i);
    }
    *b
}

#[inline(never)]
fn cond_borrow(xs: &[u64]) -> u64 {
    let mut p = first(xs);
    for i in 0..xs.len() {
        if i % 2 == 1 {
            set(&mut p, xs, i);
        }
    }
    unsafe { *p }
}

#[inline(never)]
fn swap_ptrs(a: &mut *const u64, b: &mut *const u64) {
    let t = *a;
    *a = *b;
    *b = t;
}

#[inline(never)]
fn two_args(xs: &[u64]) -> u64 {
    let mut a = first(xs);
    let mut b = first(&xs[3..]);
    for _ in 0..3 {
        swap_ptrs(&mut a, &mut b);
    }
    unsafe { *a * 10 + *b }
}

#[inline(never)]
fn newtype_field(xs: &[u64]) -> u64 {
    let mut w = w0(xs);
    for i in 0..xs.len() {
        set(&mut w.0, xs, i);
    }
    unsafe { *w.0 }
}

#[inline(never)]
fn rc0(x: u64) -> Rc<u64> {
    Rc::new(x)
}

#[inline(never)]
fn rc_step(r: &mut Rc<u64>, i: u64) {
    let v = **r * 3 + i;
    *r = Rc::new(v);
}

#[inline(never)]
fn rc_user(n: u64) -> u64 {
    let mut r = rc0(2);
    for i in 0..n {
        rc_step(&mut r, i);
    }
    *r
}

struct MutHolder<'a>(&'a mut u64);

#[inline(never)]
fn hold(x: &mut u64) -> MutHolder<'_> {
    MutHolder(x)
}

#[inline(never)]
fn bump(x: &mut u64, i: u64) {
    *x = *x * 3 + i;
}

#[inline(never)]
fn reborrow_through(n: u64) -> u64 {
    let mut x = 1u64;
    let h = hold(&mut x);
    for i in 0..n {
        bump(&mut *h.0, i);
    }
    *h.0
}

fn main() {
    // Every printed value is bound to a plain local first: the bridge's
    // `format!` interception reads bare locals.
    let xs = [3u64, 4, 5, 6];
    let raw1 = last_is_last(bb(&xs[..1])) as u8;
    let raw2 = last_is_last(bb(&xs[..2])) as u8;
    let raw4 = last_is_last(bb(&xs)) as u8;
    println!("raw_ptr {} {} {}", raw1, raw2, raw4);
    let r = ref_call(bb(&xs));
    println!("ref {}", r);
    let f1 = fnptr_call(bb(1));
    let f2 = fnptr_call(bb(2));
    println!("fn_ptr {} {}", f1, f2);
    let mut ys = [3u64, 4, 5, 6];
    let nn = nonnull_call(bb(&mut ys));
    println!("non_null {}", nn);
    let mut a = [3u64, 4, 5, 6];
    let mut b = [30u64, 40, 50];
    let v = refmut_call(bb(&mut a), bb(&mut b));
    let a_image = a[0] * 1000 + a[1] * 100 + a[2] * 10 + a[3];
    let b_image = b[0] * 10000 + b[1] * 100 + b[2];
    println!("ref_mut {} {} {}", v, a_image, b_image);
    let w = newtype_call(bb(&xs));
    println!("newtype {}", w);
    let wp = ptr_while(bb(&xs));
    println!("while_ptr {}", wp);
    let n3 = nested(bb(&xs), bb(3));
    println!("nested {}", n3);
    let tb = two_borrows(bb(&xs));
    println!("two_borrows {}", tb);
    let h4 = header_borrow(bb(&xs));
    let h1 = header_borrow(bb(&xs[..1]));
    println!("header_borrow {} {}", h4, h1);
    let g = generic(bb(&xs));
    println!("generic {}", g);
    let lb = loop_break(bb(&xs));
    println!("loop_break {}", lb);
    let vs = via_struct(bb(&xs));
    println!("via_struct {}", vs);
    let ps = preloop_store(bb(&xs));
    println!("preloop_store {}", ps);
    let bs1 = box_swap(bb(1));
    let bs3 = box_swap(bb(3));
    println!("box_swap {} {}", bs1, bs3);
    let bu0 = box_user(bb(0));
    let bu3 = box_user(bb(3));
    println!("box_user {} {}", bu0, bu3);
    let cb = cond_borrow(bb(&xs));
    println!("cond_borrow {}", cb);
    let ta = two_args(bb(&xs));
    println!("two_args {}", ta);
    let nf = newtype_field(bb(&xs));
    println!("newtype_field {}", nf);
    let rc0v = rc_user(bb(0));
    let rc3v = rc_user(bb(3));
    println!("rc {} {}", rc0v, rc3v);
    let rt = reborrow_through(bb(3));
    println!("reborrow_through {}", rt);
}
