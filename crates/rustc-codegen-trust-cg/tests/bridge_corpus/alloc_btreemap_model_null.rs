// CORPUS FIXTURE — the bridge models a `BTreeMap<u64, u64>` as a growable
// entry buffer (`emit_btreemap_empty_slot`, which allocates nothing, and the
// `__trustcg_btm_*` helpers, which allocate it on the first insert and grow
// it), so its allocation SIZES differ from std's B-tree nodes by design. Once the
// allocator fails (`FAIL`, armed before insert number `k`), both binaries must
// still end in std's allocation-error path ("memory allocation of N bytes
// failed", abort), never store through the null buffer. The row is the first
// byte of `ALLOC_SHAPE`: `a` arms before the first insert, `b` before the
// second, `c` before the thirteenth; `z` arms nothing.
use std::alloc::{GlobalAlloc, Layout, System};
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering::Relaxed};

static FAIL: AtomicBool = AtomicBool::new(false);

struct FailWhenArmed;

unsafe impl GlobalAlloc for FailWhenArmed {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        if FAIL.load(Relaxed) {
            std::ptr::null_mut()
        } else {
            unsafe { System.alloc(l) }
        }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        unsafe { System.dealloc(p, l) }
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        if FAIL.load(Relaxed) {
            std::ptr::null_mut()
        } else {
            unsafe { System.realloc(p, l, n) }
        }
    }
}

#[global_allocator]
static GLOBAL: FailWhenArmed = FailWhenArmed;

unsafe extern "C" {
    fn getenv(name: *const u8) -> *const u8;
}

fn shape() -> u8 {
    unsafe {
        let p = getenv(b"ALLOC_SHAPE\0".as_ptr());
        if p.is_null() { 0 } else { *p }
    }
}

#[inline(never)]
fn fill(arm_at: u64) -> u64 {
    let mut m: BTreeMap<u64, u64> = BTreeMap::new();
    for i in 0..40u64 {
        if i == arm_at {
            FAIL.store(true, Relaxed);
        }
        m.insert(i, i * 3);
    }
    FAIL.store(false, Relaxed);
    let seven = match m.get(&7) {
        Some(v) => *v,
        None => 0,
    };
    m.len() as u64 + seven
}

fn main() {
    let r = match shape() {
        b'a' => fill(0),
        b'b' => fill(1),
        b'c' => fill(12),
        _ => fill(99),
    };
    println!("r={r}");
}
