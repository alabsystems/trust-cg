use std::sync::atomic::{AtomicBool, Ordering};
static PANIC: AtomicBool = AtomicBool::new(false);
#[repr(C)]
pub struct Words {
    pub a: u64,
    pub b: u64,
    pub c: u64,
    pub d: u64,
}
fn result(v: u64) -> u64 {
    v.rotate_left(17) ^ 0xabcdef5678994321
}
fn start(v: u64) {
    if PANIC.load(Ordering::Relaxed) {
        println!("CALL {v}");
        panic!("terminate callback");
    }
}
#[unsafe(no_mangle)]
pub fn term_step(v: u64) -> u64 {
    start(v);
    result(v)
}
#[unsafe(no_mangle)]
pub fn term_mut(v: &mut u64) -> u64 {
    let old = *v;
    *v = v.wrapping_add(7);
    start(old);
    result(old)
}
#[unsafe(no_mangle)]
pub fn term_pair(v: u64) -> (u64, u64) {
    start(v);
    (result(v), !v)
}
#[unsafe(no_mangle)]
pub fn term_words(v: u64) -> Words {
    start(v);
    Words {
        a: result(v),
        b: !v,
        c: v.wrapping_mul(31),
        d: v ^ 0x55,
    }
}
#[unsafe(no_mangle)]
pub fn term_union(v: u64) -> core::mem::MaybeUninit<u64> {
    start(v);
    core::mem::MaybeUninit::new(result(v))
}
#[unsafe(no_mangle)]
pub fn term_read_union(slot: &mut core::mem::MaybeUninit<u64>) -> u64 {
    unsafe { slot.assume_init_read() }
}
unsafe extern "C-unwind" {
    fn term_scalar(v: u64) -> u64;
    fn term_indirect(v: u64) -> u64;
    fn term_indirect_union(v: u64) -> u64;
    fn term_indirect_double_panic(v: u64) -> u64;
    fn term_alias(v: u64) -> u64;
    fn term_pair_result(v: u64) -> u64;
    fn term_words_result(v: u64) -> u64;
    fn term_closure_scalar(v: u64) -> u64;
    fn term_closure_pair(v: u64) -> u64;
    fn term_closure_words(v: u64) -> u64;
    fn term_drop(v: u64) -> u64;
    fn term_iter(v: u64) -> u64;
    fn term_double_panic(v: u64) -> u64;
    fn term_union_result(v: u64) -> u64;
}
fn expected(case: usize, v: u64) -> u64 {
    match case {
        2 | 5 => result(v) ^ !v,
        3 | 6 => result(v) ^ !v ^ v.wrapping_mul(31) ^ (v ^ 0x55),
        7 => v,
        8 => (0..4u64).fold(0, |acc, i| acc.wrapping_add(result(v.wrapping_add(i)))),
        _ => result(v),
    }
}
fn main() {
    std::panic::set_hook(Box::new(|info| {
        let message = info
            .payload()
            .downcast_ref::<&str>()
            .copied()
            .or_else(|| info.payload().downcast_ref::<String>().map(String::as_str))
            .unwrap_or("non-string panic");
        eprintln!("PANIC_HOOK {message}");
    }));
    let functions = [
        term_scalar,
        term_alias,
        term_pair_result,
        term_words_result,
        term_closure_scalar,
        term_closure_pair,
        term_closure_words,
        term_drop,
        term_iter,
        term_double_panic,
        term_union_result,
        term_indirect,
        term_indirect_union,
        term_indirect_double_panic,
    ];
    if let Some(case) = std::env::args().nth(1) {
        let case: usize = case.parse().unwrap();
        PANIC.store(true, Ordering::Relaxed);
        let outcome = std::panic::catch_unwind(|| unsafe { functions[case](42) });
        println!("ESCAPED {}", outcome.is_err());
        std::process::exit(77);
    }
    let mut checks = 0;
    for seed in 0..512u64 {
        let v = seed.wrapping_mul(0x9e3779b97f4a7c15);
        for (case, f) in functions.iter().enumerate() {
            assert_eq!(
                unsafe { f(v) },
                expected(case, v),
                "case={case} seed={seed}"
            );
            checks += 1;
        }
    }
    println!("PASS terminate_pad checks={checks}");
}

#[unsafe(no_mangle)]
pub fn term_callback() -> fn(u64) -> u64 {
    std::hint::black_box(term_step)
}
#[unsafe(no_mangle)]
pub fn term_union_callback() -> fn(u64) -> core::mem::MaybeUninit<u64> {
    std::hint::black_box(term_union)
}
