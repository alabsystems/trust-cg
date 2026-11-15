// (i) An `FnPtrShim` whose SELF is a fn POINTER (`<fn(&u32) -> bool as
// FnOnce>::call_once`), reached by STATIC dispatch through a generic `FnOnce`
// bound: when its body failed to lower the bridge emitted a TRAPPING STUB, and
// the stub was reached (LLVM prints `1 2 1`, trust-cg aborted). Now such a shim
// is a hard refusal (failed root), exactly like `ClosureOnceShim`. This program
// is DIFFERENTIAL-OK or REFUSED — never a trap.
fn is_even(x: &u32) -> bool { *x % 2 == 0 }
fn count_bits(x: &u32) -> bool { x.count_ones() > 1 }
fn apply_ref_arg<F: FnOnce(&u32) -> bool>(f: F, v: &u32) -> bool { f(v) }
fn main() {
    let p = is_even as fn(&u32) -> bool;
    let q = count_bits as fn(&u32) -> bool;
    let v = 8u32;
    let a = apply_ref_arg(p, &v) as u32;
    let b = apply_ref_arg(q, &v) as u32 + 1;
    let c = apply_ref_arg(is_even, &v) as u32;
    println!("{} {} {}", a, b, c);
}
