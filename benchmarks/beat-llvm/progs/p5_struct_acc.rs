use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
struct St { a: u64, b: u64, c: u64 }
fn main() {
    let mut st = St { a: bb(1u64), b: bb(2u64), c: bb(3u64) };
    let n = bb(300_000_000u64);
    let mut i = 0u64;
    while i < n {
        st.a = st.a.wrapping_mul(31).wrapping_add(st.c ^ i);
        st.b = st.b.wrapping_add(st.a >> 3);
        st.c = st.c ^ (st.b.wrapping_mul(7)).rotate_left(9);
        i += 1;
    }
    done((st.a ^ st.b ^ st.c));
}
