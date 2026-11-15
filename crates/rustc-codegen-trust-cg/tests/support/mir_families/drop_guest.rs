// Guest of `mir_families_aarch64`'s drop differential (ledger L06-P8),
// compiled by the bridge and by LLVM: user `Drop` impls reached through
// rustc's own drop glue, with cleanup edges taken by real panics.
//
// * a singly linked list of boxed nodes with a user `Drop` (`Option<Box<Rec>>`:
//   the payload's glue runs through the box, recursively), torn down normally
//   and with a node whose `Drop` panics mid-chain (the box's nested cleanup
//   frees it, the rest of the chain is still dropped, the panic is caught);
// * `Vec<E>` of an enum with a droppable payload, dropped normally and with an
//   element whose `Drop` panics (`drop_in_place::<[E]>`'s nested cleanup loop
//   drops the rest of the slice);
// * a guard and a `Vec<(u32, Noisy)>` live across a loop when a later call
//   unwinds (the cleanup pad is entered from inside and outside the loop);
// * `Option<Box<u64>>` elements (a box dropped through a projection);
// * an enum cons list and an enum tree linked through `Box<Self>` variant
//   fields (`drop_glue::<List>` calls itself on each box), torn down normally
//   and with a leaf whose `Drop` panics (the siblings are still dropped and
//   every box freed);
// * indirect calls with a live cleanup edge: a `thread_local!` access
//   (`LocalKey::try_with` calls its accessor through a function pointer), a
//   `Box<dyn Fn>` call that unwinds, and a `Box<dyn Trait>` whose payload's
//   `Drop` panics (the vtable drop slot), each with a guard live.
//
// Every scenario prints whether it panicked, the allocations it left live and
// the running drop log, so a missed or doubled drop or free shows up as a
// different line.
extern crate drop_harness;
use std::cell::Cell;
use std::hint::black_box;

static mut LOG: u64 = 0;

#[inline(never)]
fn log(v: u64) {
    unsafe {
        LOG = LOG.wrapping_mul(131).wrapping_add(v);
    }
}

struct Noisy(u64);

impl Drop for Noisy {
    fn drop(&mut self) {
        log(self.0);
        if self.0 == 666 {
            panic!("element drop panics");
        }
    }
}

struct Rec {
    val: u64,
    next: Option<Box<Rec>>,
}

impl Drop for Rec {
    fn drop(&mut self) {
        log(self.val);
        if self.val == 777 {
            panic!("node drop panics");
        }
    }
}

enum E {
    One(Noisy),
    Zero,
}

enum List {
    Cons(Noisy, Box<List>),
    Nil,
}

enum Tree {
    Leaf(Noisy),
    Node(Box<Tree>, Box<Tree>),
}

#[inline(never)]
fn cons_list(n: u64) -> u64 {
    let mut list = List::Nil;
    for k in 0..n {
        list = List::Cons(Noisy(k + 50), Box::new(list));
    }
    match &list {
        List::Cons(head, _) => head.0,
        List::Nil => 0,
    }
}

#[inline(never)]
fn tree(depth: u64, next: &mut u64, bad: u64) -> Tree {
    if depth == 0 {
        *next += 1;
        Tree::Leaf(Noisy(if *next == bad { 666 } else { *next + 60 }))
    } else {
        let left = tree(depth - 1, next, bad);
        let right = tree(depth - 1, next, bad);
        Tree::Node(Box::new(left), Box::new(right))
    }
}

#[inline(never)]
fn tree_size(depth: u64, bad: u64) -> u64 {
    let mut next = 0;
    let t = tree(black_box(depth), &mut next, bad);
    black_box(&t);
    next
}

#[inline(never)]
fn chain(vals: &[u64]) -> u64 {
    let mut head: Option<Box<Rec>> = None;
    for &v in vals {
        head = Some(Box::new(Rec { val: v, next: head }));
    }
    head.as_ref().map(|r| r.val).unwrap_or(0)
}

#[inline(never)]
fn may_panic(i: u64) -> u64 {
    if black_box(i) == 99 {
        panic!("call unwinds")
    }
    i + 1
}

#[inline(never)]
fn vec_enum(n: u64, bad: u64) {
    let mut v: Vec<E> = Vec::new();
    for k in 0..n {
        v.push(if k % 3 == 2 {
            E::Zero
        } else {
            E::One(Noisy(if k == bad { 666 } else { k + 20 }))
        });
    }
    black_box(&v);
}

#[inline(never)]
fn vec_pairs(n: u64) -> u64 {
    let _guard = Noisy(5);
    let mut v: Vec<(u32, Noisy)> = Vec::new();
    for k in 0..n {
        v.push((k as u32, Noisy(k + 30)));
    }
    may_panic(n)
}

#[inline(never)]
fn optional_boxes(n: u64) -> u64 {
    let mut v: Vec<Option<Box<u64>>> = Vec::new();
    for k in 0..n {
        v.push(if k % 2 == 0 { Some(Box::new(k)) } else { None });
    }
    let mut sum = 0;
    for b in &v {
        sum += match b {
            Some(b) => **b,
            None => 1,
        };
    }
    sum
}

thread_local! {
    static TLS_COUNT: Cell<u64> = const { Cell::new(0) };
}

#[inline(never)]
fn tls_bump(fail: u64) -> u64 {
    let _guard = Noisy(40);
    TLS_COUNT.with(|c| c.set(c.get() + 1));
    may_panic(fail);
    TLS_COUNT.with(|c| c.get())
}

#[inline(never)]
fn boxed_closure(x: u64) -> u64 {
    let _guard = Noisy(41);
    let f: Box<dyn Fn(u64) -> u64> = Box::new(move |v| may_panic(v) + x);
    f(x)
}

trait Shape {
    fn area(&self) -> u64;
}

struct Square(Noisy, u64);

impl Shape for Square {
    fn area(&self) -> u64 {
        self.1 * self.1
    }
}

#[inline(never)]
fn boxed_trait_object(n: u64) -> u64 {
    let _guard = Noisy(42);
    let shape: Box<dyn Shape> = Box::new(Square(Noisy(if n == 99 { 666 } else { 43 }), n));
    shape.area()
}

fn chain_ok() {
    log(chain(&[1, 2, 3, 4]));
}

fn chain_panics_mid() {
    log(chain(&[1, 777, 3, 4]));
}

fn vec_enum_ok() {
    vec_enum(6, 100);
}

fn vec_enum_panics() {
    vec_enum(6, 1);
}

fn pairs_ok() {
    log(vec_pairs(4));
}

fn pairs_unwind() {
    log(vec_pairs(99));
}

fn boxes() {
    log(optional_boxes(7));
}

fn tls_ok() {
    log(tls_bump(1));
}

fn tls_unwind() {
    log(tls_bump(99));
}

fn closure_ok() {
    log(boxed_closure(3));
}

fn closure_unwind() {
    log(boxed_closure(99));
}

fn trait_ok() {
    log(boxed_trait_object(5));
}

fn trait_drop_panics() {
    log(boxed_trait_object(99));
}

fn cons_ok() {
    log(cons_list(5));
}

fn tree_ok() {
    log(tree_size(3, 100));
}

fn tree_leaf_panics() {
    log(tree_size(3, 3));
}

fn main() {
    drop_harness::quiet();
    let base = drop_harness::live();
    let scenarios: [fn(); 16] = [
        chain_ok,
        chain_panics_mid,
        vec_enum_ok,
        vec_enum_panics,
        pairs_ok,
        pairs_unwind,
        boxes,
        tls_ok,
        tls_unwind,
        closure_ok,
        closure_unwind,
        trait_ok,
        trait_drop_panics,
        cons_ok,
        tree_ok,
        tree_leaf_panics,
    ];
    // Every row is recorded before anything is printed: printing allocates
    // (stdout's buffer), which would count against the next scenario.
    let mut panicked = [0u64; 16];
    let mut live = [0isize; 16];
    let mut logs = [0u64; 16];
    for i in 0..16 {
        panicked[i] = drop_harness::caught(scenarios[i]) as u64;
        live[i] = drop_harness::live() - base;
        logs[i] = unsafe { LOG };
    }
    for i in 0..16 {
        let (p, l, g) = (panicked[i], live[i], logs[i]);
        println!("{p} {l} {g}");
    }
}
