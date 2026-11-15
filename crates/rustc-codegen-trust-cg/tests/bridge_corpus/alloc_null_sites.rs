// CORPUS FIXTURE — every allocation the bridge synthesizes in place of a std
// constructor must treat a NULL result from the allocator exactly as std does:
// `handle_alloc_error(layout)`, i.e. `__rust_alloc_error_handler(size, align)`,
// whose std hook prints "memory allocation of N bytes failed" and aborts. A
// missing check stores through null (SIGSEGV) or, for a bridge-built Vec, hands
// a null buffer to the fill loop.
//
// The `#[global_allocator]` fails the first request of one size once armed (the
// size the row's own allocation asks for, identical under both backends), then
// disarms; everything else is served by `System`. The row is chosen by the first byte of
// `ALLOC_SHAPE`; `z` runs every row's allocation with nothing armed (the
// control: the success paths compute LLVM's checksum). `n` allocates inside an
// `extern "C"` frame: under `panic=unwind` its edge is a terminate edge.
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::Relaxed};

static FAIL_SIZE: AtomicUsize = AtomicUsize::new(0);
static ARMING: AtomicBool = AtomicBool::new(false);

struct FailOneSize;

unsafe impl GlobalAlloc for FailOneSize {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        if l.size() == FAIL_SIZE.load(Relaxed) {
            // One-shot: the failure path's own allocations must succeed.
            FAIL_SIZE.store(0, Relaxed);
            std::ptr::null_mut()
        } else {
            unsafe { System.alloc(l) }
        }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        unsafe { System.dealloc(p, l) }
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        if n == FAIL_SIZE.load(Relaxed) {
            FAIL_SIZE.store(0, Relaxed);
            std::ptr::null_mut()
        } else {
            unsafe { System.realloc(p, l, n) }
        }
    }
}

#[global_allocator]
static GLOBAL: FailOneSize = FailOneSize;

struct Pair {
    x: i64,
    y: i64,
}

#[inline(never)]
fn arm(n: usize) {
    if ARMING.load(Relaxed) {
        FAIL_SIZE.store(n, Relaxed);
    }
}

#[inline(never)]
fn box_scalar() -> u64 {
    arm(8);
    let b = Box::new(41u64);
    *b + 1
}

#[inline(never)]
fn box_pair() -> i64 {
    arm(16);
    let b = Box::new(Pair { x: 40, y: 2 });
    b.x + b.y
}

#[inline(never)]
fn box_big() -> u64 {
    arm(4104);
    let b = Box::new([3u64; 513]);
    b[512]
}

#[inline(never)]
fn box_uninit() -> u32 {
    arm(28);
    let mut b = Box::<[u32; 7]>::new_uninit();
    b.write([5; 7]);
    let b = unsafe { b.assume_init() };
    b[6]
}

#[inline(never)]
fn vec_literal() -> u64 {
    arm(40);
    let v = vec![1u64, 2, 3, 4, 5];
    v[4]
}

#[inline(never)]
fn vec_with_capacity() -> usize {
    arm(36);
    let v: Vec<u32> = Vec::with_capacity(9);
    v.capacity()
}

#[inline(never)]
fn vec_growth() -> u64 {
    arm(64);
    let mut v: Vec<u64> = Vec::new();
    for i in 0..9u64 {
        v.push(i);
    }
    v[8]
}

#[inline(never)]
fn vec_from_elem() -> u16 {
    arm(22);
    let v = vec![7u16; 11];
    v[10]
}

#[inline(never)]
fn string_growth() -> usize {
    arm(10);
    let mut s = String::new();
    s.push_str("abcdefghij");
    s.len()
}

#[inline(never)]
fn rc_new() -> u64 {
    arm(24);
    let r = std::rc::Rc::new(5u64);
    *r
}

#[inline(never)]
fn slice_to_vec() -> u32 {
    arm(12);
    let v = [1u32, 2, 3].to_vec();
    v[2]
}

#[inline(never)]
fn slice_repeat() -> u8 {
    arm(10);
    let v = [1u8, 2].repeat(5);
    v[9]
}

#[inline(never)]
fn vec_split_off(n: u64) -> u64 {
    let mut v: Vec<u64> = (0..n).collect();
    arm(48);
    let t = v.split_off(4);
    t[5]
}

// The frame drops nothing and holds no `Assert`, so under panic=unwind the
// `Box::new` call's terminate edge is its only kind of unwind edge (a local
// box's drop would add a cleanup edge, an `Assert` a terminate edge of its
// own, and either turns EH on regardless of the allocation).
#[inline(never)]
extern "C" fn box_in_nounwind_frame() -> Box<u64> {
    arm(8);
    Box::new(41u64)
}

/// The box comes back and is dropped at the end of this frame's scope.
#[inline(never)]
fn box_from_nounwind_frame() -> u64 {
    let _b = box_in_nounwind_frame();
    41
}

unsafe extern "C" {
    fn getenv(name: *const u8) -> *const u8;
}

fn shape() -> u8 {
    unsafe {
        let p = getenv(b"ALLOC_SHAPE\0".as_ptr());
        if p.is_null() { 0 } else { *p }
    }
}

fn main() {
    let which = shape();
    println!("start {which}");
    ARMING.store(which != b'z', Relaxed);
    let r: u64 = match which {
        b'a' => box_scalar(),
        b'b' => box_pair() as u64,
        b'c' => box_big(),
        b'd' => box_uninit() as u64,
        b'e' => vec_literal(),
        b'f' => vec_with_capacity() as u64,
        b'g' => vec_growth(),
        b'h' => vec_from_elem() as u64,
        b'i' => string_growth() as u64,
        b'j' => rc_new(),
        b'k' => slice_to_vec() as u64,
        b'l' => slice_repeat() as u64,
        b'm' => vec_split_off(10),
        b'n' => box_from_nounwind_frame(),
        _ => {
            box_scalar()
                + box_pair() as u64
                + box_big()
                + box_uninit() as u64
                + vec_literal()
                + vec_with_capacity() as u64
                + vec_growth()
                + vec_from_elem() as u64
                + string_growth() as u64
                + rc_new()
                + slice_to_vec() as u64
                + slice_repeat() as u64
                + vec_split_off(10)
                + box_from_nounwind_frame()
        }
    };
    FAIL_SIZE.store(0, Relaxed);
    println!("unreachable unless z: {r}");
}
