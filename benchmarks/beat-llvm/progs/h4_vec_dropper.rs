// heap: per-rep fresh Vec that is DROPPED at the end of every loop iteration —
// exercises drop_in_place glue in a hot loop (the COMPLETE-4 gap). Committed per
// intent-to-treat: if the bridge fails closed this is an INCOMPLETE row in the
// coverage denominator, and it flips to MATCH when Drop support lands.
use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
fn main() {
    let reps = bb(50_000u32);
    let mut x: u64 = bb(0x9E3779B97F4A7C15u64);
    let mut acc: u64 = 0;
    let mut r = 0u32;
    while r < reps {
        let mut v: Vec<u64> = Vec::new();
        let mut i = 0usize;
        while i < 100 {
            x ^= x << 13; x ^= x >> 7; x ^= x << 17;
            v.push(x);
            i += 1;
        }
        let mut k = 0usize;
        while k < v.len() {
            acc = acc.wrapping_add(v[k]);
            k += 1;
        }
        r += 1;
        // v drops here (dealloc in-loop)
    }
    done(acc);
}
