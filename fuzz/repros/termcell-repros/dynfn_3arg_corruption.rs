// P0 (2026-07-17 trap-claim hunt, task #63): &dyn Fn with 3+ args mis-marshals
// arguments at ALL opt levels (silent wrong values): the virtual Fn-trait call
// passes the tupled args as ONE SysV aggregate while the vtable target uses the
// UNTUPLED closure convention; 24B tuples go by-memory vs 3 registers.
// std gt: b=6 -> exit 6*... (t03 shape: returning param b gave 40 instead of 6).
fn main() {
    let f: &dyn Fn(i64, i64, i64) -> i64 = &|_a, b, _c| b;
    std::process::exit((f(9, 6, 3)).rem_euclid(128) as i32)
}
