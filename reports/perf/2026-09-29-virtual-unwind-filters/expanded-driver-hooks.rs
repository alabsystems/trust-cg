use std::sync::atomic::{AtomicU64, Ordering};
use std::os::unix::process::ExitStatusExt;
static EVENTS: AtomicU64 = AtomicU64::new(0);
#[unsafe(no_mangle)]
pub extern "C" fn virtual_event(code: u64) {
    let old = EVENTS.load(Ordering::Relaxed);
    EVENTS.store(old * 10 + code, Ordering::Relaxed);
}
struct Guard;
impl Drop for Guard { fn drop(&mut self) { virtual_event(2); } }
trait Operation { fn run(&mut self, value: u64, fail: bool) -> u64; }
#[repr(C)]
struct Pair { a: u64, b: u64 }
trait PairOperation { fn run(&mut self, value: u64, fail: bool) -> Pair; }
trait Mutation { fn run(&self, out: &mut u64, value: u64, fail: bool) -> u64; }
trait Tracked { #[track_caller] fn run(&self, value: u64, fail: bool) -> u64; }
#[repr(C)]
#[derive(Clone, Copy)]
struct Large { words: [u64; 4] }
trait LargeOperation { fn run(&self, value: Large, fail: bool) -> u64; }
struct Method;
impl Operation for Method {
    fn run(&mut self, value: u64, fail: bool) -> u64 {
        let _guard = Guard;
        if fail { std::panic::panic_any(value); }
        value.wrapping_add(13)
    }
}
impl PairOperation for Method {
    fn run(&mut self, value: u64, fail: bool) -> Pair {
        let _guard = Guard;
        if fail { std::panic::panic_any(value); }
        Pair { a: value.wrapping_add(13), b: !value }
    }
}
impl Mutation for Method {
    fn run(&self, out: &mut u64, value: u64, fail: bool) -> u64 {
        let _guard = Guard;
        *out = value.wrapping_add(17);
        if fail { std::panic::panic_any(value); }
        value.wrapping_add(13)
    }
}
impl Tracked for Method {
    #[track_caller]
    fn run(&self, value: u64, fail: bool) -> u64 {
        let _guard = Guard;
        let location = std::panic::Location::caller();
        assert!(location.file().ends_with("corpus.rs"));
        if fail { std::panic::panic_any(value); }
        value.wrapping_add(location.line() as u64)
    }
}
impl LargeOperation for Method {
    fn run(&self, mut value: Large, fail: bool) -> u64 {
        let _guard = Guard;
        let seed = value.words[0];
        let result = value.words[0] ^ value.words[1] ^ value.words[2] ^ value.words[3];
        value.words[1] = 0;
        std::hint::black_box(&mut value);
        if fail { std::panic::panic_any(seed); }
        result
    }
}
unsafe extern "Rust" {
    fn virtual_scalar(op: &mut dyn Operation, value: u64, fail: bool) -> u64;
    fn virtual_pair(op: &mut dyn PairOperation, value: u64, fail: bool) -> u64;
    fn virtual_fn(op: &dyn Fn(u64, bool) -> u64, value: u64, fail: bool) -> u64;
    fn virtual_fn_mut(op: &mut dyn FnMut(u64, bool) -> u64, value: u64, fail: bool) -> u64;
    fn virtual_mutation(op: &dyn Mutation, out: &mut u64, value: u64, fail: bool) -> u64;
    fn virtual_tracked(op: &dyn Tracked, value: u64, fail: bool) -> u64;
    fn virtual_large(op: &dyn LargeOperation, value: u64, fail: bool) -> u64;
}
unsafe extern "C" { fn virtual_terminate(op: &mut dyn Operation, value: u64) -> u64; }
struct UnexpectedUnwind;
impl Drop for UnexpectedUnwind { fn drop(&mut self) { std::process::exit(93); } }
fn main() {
    if std::env::args().nth(1).as_deref() == Some("--terminate") {
        std::panic::set_hook(Box::new(|info| {
            if info.payload().downcast_ref::<u64>() != Some(&1234) {
                eprintln!("second hook: {info}"); return;
            }
            println!("virtual hook");
        }));
        let _ = std::panic::catch_unwind(|| {
            let _guard = UnexpectedUnwind;
            unsafe { virtual_terminate(&mut Method, 1234); }
            std::process::exit(96);
        });
        std::process::exit(97);
    }
    std::panic::set_hook(Box::new(|_| {}));
    let closure = |value: u64, fail: bool| {
        let _guard = Guard;
        if fail { std::panic::panic_any(value); }
        value.wrapping_add(13)
    };
    let mut checks = 0;
    let mut panics = 0;
    for index in 0..128u64 {
        let value = index.wrapping_mul(0x9e3779b97f4a7c15);
        for kind in 0..7 {
            for fail in [false, true] {
                if fail && cfg!(panic = "abort") { continue; }
                EVENTS.store(0, Ordering::Relaxed);
                let mut method = Method;
                let mut out = 0;
                let mut hits = 0;
                let mut mutable = |v, f| { hits += 1; closure(v, f) };
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
                    match kind {
                        0 => virtual_scalar(&mut method, value, fail),
                        1 => virtual_pair(&mut method, value, fail),
                        2 => virtual_fn(&closure, value, fail),
                        3 => virtual_fn_mut(&mut mutable, value, fail),
                        4 => virtual_mutation(&method, &mut out, value, fail),
                        5 => virtual_tracked(&method, value, fail),
                        _ => virtual_large(&method, value, fail),
                    }
                }));
                if fail {
                    assert_eq!(*result.unwrap_err().downcast::<u64>().unwrap(), value);
                    panics += 1;
                } else {
                    let expected = match kind {
                        1 => value.wrapping_add(13) ^ !value,
                        5 => value,
                        6 => value ^ value.rotate_left(13) ^ value.wrapping_add(17),
                        _ => value.wrapping_add(13),
                    };
                    assert_eq!(result.unwrap(), expected);
                }
                assert_eq!(EVENTS.load(Ordering::Relaxed), 21);
                checks += 2;
                if kind == 3 { assert_eq!(hits, 1); checks += 1; }
                if kind == 4 { assert_eq!(out, value.wrapping_add(17)); checks += 1; }
            }
        }
    }
    let output = std::process::Command::new(std::env::current_exe().unwrap()).arg("--terminate").output().unwrap();
    assert_eq!(output.status.signal(), Some(6));
    assert_eq!(output.stdout, b"virtual hook\n");
    println!("PASS virtual_unwind checks={checks} panics={panics} aborts=1");
}
