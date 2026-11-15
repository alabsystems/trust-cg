// CORPUS FIXTURE — under `panic=unwind`, a `Vec::resize_with` shrink whose
// element `Drop` panics drops the rest of the tail and leaves the Vec as std's
// `truncate` does.
//
// WHAT IT PINS. std's shrink is `truncate`: it stores the shorter length
// first, then `drop_in_place::<[T]>` drops the tail front to back. When one
// drop panics, the slice drop glue drops the rest of the tail in cleanup (a
// second panic would abort), and the unwind continues through the caller's
// cleanup. Here the tail is `[3, 4, 5]` and the drop of 4 panics. std drops
// 3, 4 and 5, then the shrinking function's `Local`, and the caller's guard
// sees `len == 2`. Dropping the Vec then drops 1 and 2. The intercepted
// `resize_with` drops the tail with the same nested cleanup, on its call's
// unwind edge.
//
// HOW IT FAILS IF THE FIX IS REVERTED. Without the shrink's nested cleanup,
// the bridge refused this shrink by name (formerly [TCG-VEC-ELEMENT-DROP]). The
// upstream bridge (origin/main c8b07006b) compiles it and DIVERGES at
// -O0..-O3: it drops no element of the tail, so nothing panics (`1 1000`,
// `5 0`, then the Vec's own drops).

use std::hint::black_box as bb;
use std::sync::atomic::{AtomicU32, Ordering::SeqCst};

static ARM: AtomicU32 = AtomicU32::new(4);

#[inline(never)]
fn line(tag: u32, value: u32) {
    println!("{tag} {value}");
}

struct W(u32);

impl Drop for W {
    fn drop(&mut self) {
        line(0, self.0);
        if self.0 == ARM.load(SeqCst) {
            ARM.store(0, SeqCst);
            panic!("drop");
        }
    }
}

struct Local;

impl Drop for Local {
    fn drop(&mut self) {
        line(1, 1000);
    }
}

// Runs during the unwind, before the Vec is dropped.
struct Guard(*mut Vec<W>);

impl Drop for Guard {
    fn drop(&mut self) {
        let v = unsafe { &*self.0 };
        let mut s = v.len() as u32;
        let mut i = 0;
        while i < v.len() {
            s = s.wrapping_mul(31).wrapping_add(v[i].0);
            i += 1;
        }
        line(2, v.len() as u32);
        line(3, s);
    }
}

// Declared before the Vec, so it runs after the Vec's drop.
struct After;

impl Drop for After {
    fn drop(&mut self) {
        line(4, 0);
        std::process::exit(0);
    }
}

#[inline(never)]
fn shrink(v: &mut Vec<W>) {
    let _local = Local;
    v.resize_with(bb(2), || W(99));
}

fn main() {
    let _after = After;
    let mut v = Vec::new();
    for x in [1u32, 2, 3, 4, 5] {
        v.push(W(bb(x)));
    }
    let p: *mut Vec<W> = &mut v;
    let g = Guard(p);
    shrink(unsafe { &mut *p });
    std::mem::forget(g);
    line(5, 0);
}
