use std::sync::{
    Mutex,
    atomic::{AtomicBool, Ordering},
};
static LOG: Mutex<Vec<(u64, u64)>> = Mutex::new(Vec::new());
static PANIC: AtomicBool = AtomicBool::new(false);
#[repr(C)]
pub struct Words {
    pub a: u64,
    pub b: u64,
    pub c: u64,
    pub d: u64,
}
#[repr(C)]
pub struct Pair {
    pub a: u64,
    pub b: u64,
}
#[repr(C)]
pub struct Floats {
    pub a: f64,
    pub b: f64,
    pub c: f64,
}
#[unsafe(no_mangle)]
pub extern "C" fn aggregate_event(kind: u64, value: u64) {
    LOG.lock().unwrap().push((kind, value));
}
fn start(cell: &mut u64, v: u64) {
    assert_eq!(*cell, v ^ 0x55);
    *cell = v.wrapping_add(0x1122);
    aggregate_event(1, *cell);
    if PANIC.load(Ordering::Relaxed) {
        panic!("aggregate call")
    }
}
#[unsafe(no_mangle)]
pub fn aggregate_rust_pair(cell: &mut u64, v: u64) -> (u64, u64) {
    start(cell, v);
    (v.rotate_left(13), v ^ 0x11)
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn aggregate_words(cell: &mut u64, v: u64) -> Words {
    start(cell, v);
    Words {
        a: v.rotate_left(13),
        b: v ^ 0x11,
        c: v.wrapping_mul(3),
        d: !v,
    }
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn aggregate_pair(cell: &mut u64, v: u64) -> Pair {
    start(cell, v);
    Pair {
        a: v.rotate_left(13),
        b: v ^ 0x11,
    }
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn aggregate_floats(cell: &mut u64, v: u64) -> Floats {
    start(cell, v);
    let x = (v & 255) as f64;
    Floats {
        a: x + 0.25,
        b: -x - 0.5,
        c: x * 2.0 + 0.125,
    }
}
#[unsafe(no_mangle)]
pub fn aggregate_union(cell: &mut u64, v: u64) -> core::mem::MaybeUninit<u64> {
    start(cell, v);
    core::mem::MaybeUninit::new(v.rotate_left(13))
}
#[unsafe(no_mangle)]
pub fn aggregate_read_union(slot: &mut core::mem::MaybeUninit<u64>) -> u64 {
    unsafe { slot.assume_init_read() }
}
unsafe extern "C-unwind" {
    fn check_rust_pair(v: u64) -> u64;
    fn check_words(v: u64) -> u64;
    fn check_pair(v: u64) -> u64;
    fn check_floats(v: u64) -> u64;
    fn check_union(v: u64) -> u64;
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut checks = 0;
    for i in 0..256_u64 {
        let v = i.wrapping_mul(0x9e3779b97f4a7c15);
        let cell = v.wrapping_add(0x1122);
        for panic in [false, true] {
            PANIC.store(panic, Ordering::Relaxed);
            for case in 0..5 {
                let result = std::panic::catch_unwind(|| unsafe {
                    match case {
                        0 => check_rust_pair(v),
                        1 => check_words(v),
                        2 => check_pair(v),
                        3 => check_floats(v),
                        _ => check_union(v),
                    }
                });
                if panic {
                    assert!(result.is_err());
                    assert_eq!(*LOG.lock().unwrap(), [(1, cell), (5, cell)]);
                } else {
                    let base = v.rotate_left(13) ^ (v ^ 0x11);
                    let x = (v & 255) as f64;
                    let expected = match case {
                        0 | 2 => base,
                        1 => base ^ v.wrapping_mul(3) ^ !v,
                        4 => v.rotate_left(13),
                        _ => {
                            (x + 0.25).to_bits()
                                ^ (-x - 0.5).to_bits()
                                ^ (x * 2.0 + 0.125).to_bits()
                        }
                    } ^ cell;
                    assert_eq!(result.unwrap(), expected, "case={case} seed={i}");
                    assert_eq!(*LOG.lock().unwrap(), [(1, cell), (2, cell), (5, cell)]);
                }
                LOG.lock().unwrap().clear();
                checks += 1;
            }
        }
    }
    println!("PASS aggregate_unwind checks={checks}");
}
