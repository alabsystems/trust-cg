use std::sync::{
    Mutex,
    atomic::{AtomicU64, Ordering},
};
static LOG: Mutex<Vec<u64>> = Mutex::new(Vec::new());
static PANIC_ID: AtomicU64 = AtomicU64::new(u64::MAX);
#[unsafe(no_mangle)]
pub extern "C" fn associated_record(id: u64) {
    LOG.lock().unwrap().push(id);
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn associated_may_panic(id: u64) {
    if PANIC_ID.load(Ordering::Relaxed) == id {
        panic!("selected destructor");
    }
}
unsafe extern "C-unwind" {
    fn associated_cleanup(mode: u64);
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut checks = 0;
    for _ in 0..128 {
        for id in [u64::MAX, 0, 1, 2, 3, 4] {
            PANIC_ID.store(id, Ordering::Relaxed);
            let result = std::panic::catch_unwind(|| unsafe {
                associated_cleanup(if id == 0 { 0 } else { 1 });
            });
            assert_eq!(result.is_err(), id != u64::MAX);
            assert_eq!(*LOG.lock().unwrap(), [1, 2, 3, 4]);
            LOG.lock().unwrap().clear();
            checks += 1;
        }
    }
    println!("PASS associated_drop_unwind checks={checks}");
}
