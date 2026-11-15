use std::sync::{
    Mutex,
    atomic::{AtomicU64, Ordering},
};
static ALLOCS: Mutex<Vec<(usize, u64, u64)>> = Mutex::new(Vec::new());
static LOG: Mutex<Vec<(u64, u64)>> = Mutex::new(Vec::new());
static PANIC: AtomicU64 = AtomicU64::new(0);
#[unsafe(no_mangle)]
pub extern "C" fn store_allocate(id: u64, value: u64) -> *mut u64 {
    let p = Box::into_raw(Box::new(value));
    ALLOCS.lock().unwrap().push((p as usize, id, value));
    p
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn store_release(ptr: *mut u64, id: u64) {
    let mut a = ALLOCS.lock().unwrap();
    let i = a
        .iter()
        .position(|&(p, k, _)| p == ptr as usize && k == id)
        .expect("missing or duplicate free");
    let (_, _, value) = a.remove(i);
    assert_eq!(unsafe { *ptr }, value);
    unsafe {
        drop(Box::from_raw(ptr));
    }
    LOG.lock().unwrap().push((id, value));
}
#[unsafe(no_mangle)]
pub extern "C" fn store_event(id: u64, value: u64) {
    LOG.lock().unwrap().push((id, value));
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn store_may_panic(id: u64) {
    if PANIC.load(Ordering::Relaxed) == id {
        panic!("drop")
    }
}
unsafe extern "C-unwind" {
    fn store_owned(v: u64, replace: bool);
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut checks = 0;
    for i in 0..256_u64 {
        let v = i.wrapping_mul(0x9e3779b97f4a7c15);
        let new = v ^ 0x123456789;
        for replace in [false, true] {
            for panic in [0, 10, 11, 20, 21] {
                PANIC.store(panic, Ordering::Relaxed);
                let result = std::panic::catch_unwind(|| unsafe { store_owned(v, replace) });
                assert_eq!(result.is_err(), panic != 0);
                assert!(ALLOCS.lock().unwrap().is_empty());
                let mut expected = Vec::new();
                if replace {
                    expected.push((30, v ^ v.rotate_left(17) ^ !v));
                }
                expected.extend([(10, v), (11, !v)]);
                if panic != 10 && panic != 11 {
                    expected.push((40, new ^ new.rotate_left(17) ^ !new));
                }
                expected.extend([(20, new), (21, !new), (90, 0)]);
                assert_eq!(
                    *LOG.lock().unwrap(),
                    expected,
                    "seed={i} replace={replace} panic={panic}"
                );
                LOG.lock().unwrap().clear();
                checks += 1;
            }
        }
    }
    println!("PASS aggregate_store_owned checks={checks}");
}
