use std::sync::atomic::{AtomicU64, Ordering};
static EVENTS: AtomicU64 = AtomicU64::new(0);
#[unsafe(no_mangle)]
pub extern "C" fn virtual_event(code: u64) {
    EVENTS.fetch_add(code, Ordering::Relaxed);
}
#[unsafe(no_mangle)]
pub extern "C" fn forced_events() -> u64 {
    EVENTS.load(Ordering::Relaxed)
}
trait Operation {
    fn run(&mut self, value: u64, fail: bool) -> u64;
}
unsafe extern "C" {
    fn virtual_terminate(op: &mut dyn Operation, value: u64) -> u64;
}
unsafe extern "C-unwind" {
    fn forced_begin();
}
struct Guard;
impl Drop for Guard {
    fn drop(&mut self) {
        virtual_event(2);
    }
}
struct Forced;
impl Operation for Forced {
    #[inline(never)]
    fn run(&mut self, _: u64, _: bool) -> u64 {
        let _guard = Guard;
        unsafe {
            forced_begin();
        }
        std::process::exit(85);
    }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn forced_outer() {
    unsafe {
        virtual_terminate(&mut Forced, 0);
    }
    std::process::exit(86);
}
fn main() {
    std::panic::set_hook(Box::new(|_| {
        std::process::exit(87);
    }));
    forced_outer();
}
