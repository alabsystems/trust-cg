extern crate vapad;
use std::hint::black_box as bb;
use vapad::Oa16U64;

// A call through a C-variadic `fn` pointer with NO anonymous argument: the
// argument count equals the pointer's input count, so the fn-pointer call
// route takes it (no count refusal). Right answer: 10203.
fn main() {
    let f: unsafe extern "C" fn(u64, Oa16U64, u64, ...) -> u64 = bb(vapad::va_pad_u64_ptr());
    let r = unsafe { f(bb(1), Oa16U64 { a: bb(2) }, bb(3)) };
    println!("{}", r);
    std::process::exit(if r == 10_203 { 42 } else { 1 });
}
