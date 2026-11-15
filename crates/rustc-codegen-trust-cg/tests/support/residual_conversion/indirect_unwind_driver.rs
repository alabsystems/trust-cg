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
    fn check_many(
        callback: unsafe extern "C-unwind" fn(
            &mut u64,
            u64,
            u64,
            u64,
            u64,
            u64,
            u64,
            u64,
            u64,
            u64,
            f64,
            f64,
            f64,
            f64,
            f64,
            f64,
            f64,
            f64,
            f64,
        ) -> u64,
        v: u64,
    ) -> u64;
    fn check_rust_pair(
        callback: unsafe extern "Rust" fn(&mut u64, u64) -> (u64, u64),
        v: u64,
    ) -> u64;
    fn check_wide(callback: unsafe extern "C-unwind" fn(&mut u64, u64) -> u128, v: u64) -> u64;
    fn check_scalar(callback: unsafe extern "C-unwind" fn(&mut u64, u64) -> u64, v: u64) -> u64;
    fn check_pair(callback: unsafe extern "C-unwind" fn(&mut u64, u64) -> Pair, v: u64) -> u64;
    fn check_floats(callback: unsafe extern "C-unwind" fn(&mut u64, u64) -> Floats, v: u64) -> u64;
    fn check_union(
        callback: unsafe extern "Rust" fn(&mut u64, u64) -> core::mem::MaybeUninit<u64>,
        v: u64,
    ) -> u64;
}
fn main() {
    std::panic::set_hook(Box::new(|info| {
        if info.payload().downcast_ref::<&str>() != Some(&"aggregate call") {
            eprintln!("{info}");
        }
    }));
    let mut checks = 0;
    for i in 0..256_u64 {
        let v = i.wrapping_mul(0x9e3779b97f4a7c15);
        let cell = v.wrapping_add(0x1122);
        for panic in [false, true] {
            PANIC.store(panic, Ordering::Relaxed);
            for case in 0..7 {
                let result = std::panic::catch_unwind(|| unsafe {
                    match case {
                        0 => check_rust_pair(std::hint::black_box(aggregate_rust_pair), v),
                        1 => check_wide(std::hint::black_box(aggregate_wide), v),
                        2 => check_pair(std::hint::black_box(aggregate_pair), v),
                        3 => check_floats(std::hint::black_box(aggregate_floats), v),
                        6 => check_many(std::hint::black_box(aggregate_many), v),
                        4 => check_scalar(std::hint::black_box(aggregate_scalar), v),
                        _ => check_union(std::hint::black_box(aggregate_union), v),
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
                        1 => base,
                        4 | 5 | 6 => v.rotate_left(13),
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
    println!("PASS indirect_aggregate_unwind checks={checks}");
}

unsafe extern "C-unwind" fn aggregate_wide(cell: &mut u64, v: u64) -> u128 {
    start(cell, v);
    ((v ^ 0x11) as u128) << 64 | v.rotate_left(13) as u128
}
unsafe extern "C-unwind" fn aggregate_scalar(cell: &mut u64, v: u64) -> u64 {
    start(cell, v);
    v.rotate_left(13)
}

unsafe extern "C-unwind" fn aggregate_many(
    cell: &mut u64,
    v: u64,
    a1: u64,
    a2: u64,
    a3: u64,
    a4: u64,
    a5: u64,
    a6: u64,
    a7: u64,
    a8: u64,
    f1: f64,
    f2: f64,
    f3: f64,
    f4: f64,
    f5: f64,
    f6: f64,
    f7: f64,
    f8: f64,
    f9: f64,
) -> u64 {
    assert_eq!(a1, v.wrapping_add(1));
    assert_eq!(a2, v.wrapping_add(2));
    assert_eq!(a3, v.wrapping_add(3));
    assert_eq!(a4, v.wrapping_add(4));
    assert_eq!(a5, v.wrapping_add(5));
    assert_eq!(a6, v.wrapping_add(6));
    assert_eq!(a7, v.wrapping_add(7));
    assert_eq!(a8, v.wrapping_add(8));
    assert_eq!(f1, 1.25);
    assert_eq!(f2, 2.25);
    assert_eq!(f3, 3.25);
    assert_eq!(f4, 4.25);
    assert_eq!(f5, 5.25);
    assert_eq!(f6, 6.25);
    assert_eq!(f7, 7.25);
    assert_eq!(f8, 8.25);
    assert_eq!(f9, 9.25);
    start(cell, v);
    v.rotate_left(13)
}
