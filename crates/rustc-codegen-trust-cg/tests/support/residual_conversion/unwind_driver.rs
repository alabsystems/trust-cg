use std::sync::{
    Mutex,
    atomic::{AtomicBool, Ordering},
};
static LOG: Mutex<Vec<(u64, u64)>> = Mutex::new(Vec::new());
static PANIC: AtomicBool = AtomicBool::new(false);
#[unsafe(no_mangle)]
pub extern "C" fn residual_event(kind: u64, value: u64) {
    LOG.lock().unwrap().push((kind, value));
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn residual_may_panic(_: u64) {
    if PANIC.load(Ordering::Relaxed) {
        panic!("conversion")
    }
}
unsafe extern "C-unwind" {
    fn residual_unwind(v: u64, fail: bool) -> u64;
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut checks = 0;
    for i in 0..256_u64 {
        let v = i.wrapping_mul(0x9e3779b97f4a7c15);
        for fail in [false, true] {
            for panic in [false, true] {
                PANIC.store(panic, Ordering::Relaxed);
                let outcome = std::panic::catch_unwind(|| unsafe { residual_unwind(v, fail) });
                if fail && panic {
                    assert!(outcome.is_err());
                    assert_eq!(*LOG.lock().unwrap(), [(1, v), (4, 0), (3, v), (9, 0)]);
                } else {
                    assert_eq!(outcome.unwrap(), if fail { v ^ 0x4321 } else { v ^ 123 });
                    if fail {
                        assert_eq!(
                            *LOG.lock().unwrap(),
                            [(1, v), (2, v), (4, 0), (3, v), (9, 0)]
                        );
                    } else {
                        assert_eq!(*LOG.lock().unwrap(), [(9, 0)]);
                    }
                }
                LOG.lock().unwrap().clear();
                checks += 1;
            }
        }
    }
    println!("PASS residual_conversion_unwind checks={checks}");
}
