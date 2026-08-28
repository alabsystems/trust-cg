// recursion: single (fib), MUTUAL (is_even/is_odd), accumulator, and nested
// (Ackermann) — exercises call/return, the stack, and self/mutual back-edges.
use std::hint::black_box as bb;
fn fib(n: u64) -> u64 { if n < 2 { n } else { fib(n-1).wrapping_add(fib(n-2)) } }
fn is_even(n: u64) -> bool { if n == 0 { true } else { is_odd(n-1) } }
fn is_odd(n: u64) -> bool { if n == 0 { false } else { is_even(n-1) } }
fn acc(n: u64, a: u64) -> u64 { if n == 0 { a } else { acc(n-1, a.wrapping_add(n).wrapping_mul(3)) } }
fn ack(m: u64, n: u64) -> u64 { if m == 0 { n+1 } else if n == 0 { ack(m-1, 1) } else { ack(m-1, ack(m, n-1)) } }
fn main() {
    let mut s: u64 = 0;
    for i in 0..bb(28u64) { s = s.wrapping_add(fib(i)); }
    for i in 0..bb(100u64) { s = s.wrapping_add(is_even(i) as u64 * 2).wrapping_add(is_odd(i) as u64); }
    s = s.wrapping_add(acc(bb(500), 1));
    s = s.wrapping_add(ack(bb(2), bb(7)));
    std::process::exit((s % 251) as i32);
}
