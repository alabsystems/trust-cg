use std::sync::{Mutex, atomic::{AtomicBool, Ordering}};
static LOG: Mutex<Vec<(u64,u64)>> = Mutex::new(Vec::new());
static PANIC: AtomicBool = AtomicBool::new(false);
#[unsafe(no_mangle)]
pub extern "C" fn indirect_event(kind: u64, value: u64) { LOG.lock().unwrap().push((kind,value)); }
unsafe extern "C-unwind" fn callback(cell: &mut u64, value: u64) -> u64 {
    assert_eq!(*cell, value ^ 0x55);
    *cell = value.wrapping_add(0x1122);
    indirect_event(1, *cell);
    if PANIC.load(Ordering::Relaxed) { panic!("indirect callback"); }
    value.rotate_left(13)
}
unsafe extern "C-unwind" {
    fn check_indirect(callback: unsafe extern "C-unwind" fn(&mut u64,u64)->u64, value:u64)->u64;
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut checks = 0;
    for i in 0..256_u64 {
        let value = i.wrapping_mul(0x9e3779b97f4a7c15);
        let cell = value.wrapping_add(0x1122);
        for panic in [false,true] {
            PANIC.store(panic,Ordering::Relaxed);
            let result = std::panic::catch_unwind(|| unsafe {check_indirect(std::hint::black_box(callback),value)});
            if panic {
                assert!(result.is_err());
                assert_eq!(*LOG.lock().unwrap(),[(1,cell),(5,cell)]);
            } else {
                assert_eq!(result.unwrap(),value.rotate_left(13)^cell);
                assert_eq!(*LOG.lock().unwrap(),[(1,cell),(2,cell),(5,cell)]);
            }
            LOG.lock().unwrap().clear();
            checks+=1;
        }
    }
    println!("PASS indirect_cleanup checks={checks}");
}
