use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
enum Op { Add, Xor, Mul, Rot, Sub, Shr, Mix }
fn main() {
    let mut s: u64 = bb(88172645463325252u64);
    let mut acc: u64 = bb(0u64);
    let n = bb(200_000_000u64);
    let mut i = 0u64;
    while i < n {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        let op = match s % 7 {
            0 => Op::Add, 1 => Op::Xor, 2 => Op::Mul, 3 => Op::Rot,
            4 => Op::Sub, 5 => Op::Shr, _ => Op::Mix,
        };
        acc = match op {
            Op::Add => acc.wrapping_add(s),
            Op::Xor => acc ^ s,
            Op::Mul => acc.wrapping_mul(s | 1),
            Op::Rot => acc.rotate_left((s & 63) as u32),
            Op::Sub => acc.wrapping_sub(s >> 5),
            Op::Shr => acc.wrapping_add(s >> (s & 31)),
            Op::Mix => acc.wrapping_add(s ^ (acc >> 11)),
        };
        i += 1;
    }
    done(acc);
}
