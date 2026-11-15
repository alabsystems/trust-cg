#![feature(panic_internals, fmt_arguments_from_str)]
#![allow(internal_features)]
use std::sync::atomic::{AtomicUsize, Ordering};
static DROPS: AtomicUsize = AtomicUsize::new(0);
struct Guard;
impl Drop for Guard {
    fn drop(&mut self) { DROPS.fetch_add(1, Ordering::SeqCst); }
}
#[inline(never)]
fn fail(kind: usize) {
    let _guard = Guard;
    match kind % 3 {
        0 => core::panicking::panic(std::hint::black_box("core runtime literal")),
        1 => core::panicking::panic_fmt(core::fmt::Arguments::from_str(std::hint::black_box("core runtime dynamic"))),
        _ => core::panicking::panic_fmt(format_args!("core runtime value={kind}")),
    }
}
fn payload(value: &(dyn core::any::Any + Send)) -> &str {
    if let Some(s) = value.downcast_ref::<String>() { s }
    else { value.downcast_ref::<&str>().unwrap() }
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    for kind in 0..96 {
        let p = std::panic::catch_unwind(|| fail(kind)).unwrap_err();
        let expected = match kind % 3 {
            0 => "core runtime literal".to_owned(),
            1 => "core runtime dynamic".to_owned(),
            _ => format!("core runtime value={kind}"),
        };
        if payload(&*p) != expected { eprintln!("expected={expected:?} actual={:?}",payload(&*p)); }
        assert_eq!(payload(&*p),expected);
        assert_eq!(DROPS.load(Ordering::SeqCst),kind+1);
    }
    println!("PASS real_core_runtime panics=96 drops=96");
}
