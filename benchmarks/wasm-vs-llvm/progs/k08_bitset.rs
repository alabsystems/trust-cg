#![no_std]
#![allow(dead_code)]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

const W: usize = usize::BITS as usize;
const NW: usize = 256 / W;

struct BitSet {
    w: [usize; NW],
}

impl BitSet {
    #[inline(never)]
    fn new() -> Self {
        BitSet { w: [0; NW] }
    }
    #[inline(never)]
    fn insert(&mut self, i: usize) -> bool {
        let (q, r) = (i / W, i % W);
        let m = 1usize << r;
        let was = self.w[q] & m != 0;
        self.w[q] |= m;
        !was
    }
    #[inline(never)]
    fn remove(&mut self, i: usize) {
        self.w[i / W] &= !(1usize << (i % W));
    }
    #[inline(never)]
    fn count(&self) -> u32 {
        self.w.iter().map(|x| x.count_ones()).sum()
    }
    #[inline(never)]
    fn first(&self) -> Option<usize> {
        for (k, &x) in self.w.iter().enumerate() {
            if x != 0 {
                return Some(k * W + x.trailing_zeros() as usize);
            }
        }
        None
    }
    #[inline(never)]
    fn last(&self) -> Option<usize> {
        for k in (0..NW).rev() {
            let x = self.w[k];
            if x != 0 {
                return Some(k * W + (W - 1 - x.leading_zeros() as usize));
            }
        }
        None
    }
    #[inline(never)]
    fn next_after(&self, i: usize) -> Option<usize> {
        let mut i = i + 1;
        while i < 256 {
            let q = i / W;
            let x = self.w[q] >> (i % W);
            if x != 0 {
                return Some(i + x.trailing_zeros() as usize);
            }
            i = (q + 1) * W;
        }
        None
    }
}

#[no_mangle]
pub extern "C" fn bs_ops(seed: u32, n: u32) -> u32 {
    let mut b = BitSet::new();
    let mut s = seed | 1;
    let mut fresh = 0u32;
    for _ in 0..(n % 90) {
        s ^= s << 13;
        s ^= s >> 17;
        s ^= s << 5;
        if b.insert((s % 256) as usize) {
            fresh += 1;
        }
        if s & 7 == 0 {
            b.remove(((s >> 8) % 256) as usize);
        }
    }
    let f = b.first().map(|x| x as u32).unwrap_or(999);
    let l = b.last().map(|x| x as u32).unwrap_or(999);
    let mut walk = 0u32;
    let mut cur = b.first();
    let mut guard = 0;
    while let Some(c) = cur {
        walk = walk.wrapping_mul(3).wrapping_add(c as u32);
        cur = b.next_after(c);
        guard += 1;
        if guard > 300 {
            break;
        }
    }
    b.count() ^ (fresh << 8) ^ (f << 12) ^ (l << 20) ^ walk.rotate_left(3)
}

#[no_mangle]
pub extern "C" fn usize_bits(x: u32, y: u32) -> u64 {
    let a = x as usize;
    let b = y as usize;
    let lz = a.leading_zeros() as u64;
    let tz = b.trailing_zeros() as u64;
    let co = (a ^ b).count_ones() as u64;
    let lo = (!a).leading_ones() as u64;
    let rl = a.rotate_left(y) as u64;
    let rr = b.rotate_right(x) as u64;
    let sb = a.swap_bytes() as u64;
    let rb = b.reverse_bits() as u64;
    lz | tz << 8 | co << 16 | lo << 24 | (rl ^ rr ^ sb ^ rb) << 32
}

#[no_mangle]
pub extern "C" fn usize_arith(x: u32, y: u32) -> i64 {
    let a = x as usize;
    let b = y as usize;
    let m = a.checked_mul(b).map(|v| v as i64).unwrap_or(-1);
    let s = a.checked_add(b).map(|v| v as i64).unwrap_or(-2);
    let p = a.checked_pow(y % 5).map(|v| v as i64).unwrap_or(-3);
    let np = a
        .checked_next_power_of_two()
        .map(|v| v as i64)
        .unwrap_or(-4);
    let lg = if a > 0 { a.ilog2() as i64 } else { -5 };
    let sat = a.saturating_mul(b) as i64;
    let wr = a.wrapping_mul(b).wrapping_add(usize::MAX) as i64;
    let ov = a.overflowing_sub(b);
    m ^ s.rotate_left(8)
        ^ p.rotate_left(16)
        ^ np.rotate_left(24)
        ^ lg.rotate_left(32)
        ^ sat.rotate_left(40)
        ^ wr.rotate_left(44)
        ^ (ov.0 as i64).rotate_left(50)
        ^ (ov.1 as i64)
}

#[no_mangle]
pub extern "C" fn isize_arith(x: i32, y: i32) -> i64 {
    let a = x as isize;
    let b = y as isize;
    let d = a.checked_div(b).map(|v| v as i64).unwrap_or(-1);
    let r = a.checked_rem(b).map(|v| v as i64).unwrap_or(-2);
    let e = a.checked_div_euclid(b).map(|v| v as i64).unwrap_or(-3);
    let abs = a.checked_abs().map(|v| v as i64).unwrap_or(-4);
    let neg = a.wrapping_neg() as i64;
    let sh = a.wrapping_shr(y as u32) as i64;
    let sg = a.signum() as i64;
    let ua = a.unsigned_abs() as u64 as i64;
    let sat = a.saturating_sub(b) as i64;
    d ^ r << 4 ^ e << 8 ^ abs << 12 ^ neg << 16 ^ sh << 20 ^ sg << 24 ^ ua << 28 ^ sat << 32
}

#[no_mangle]
pub extern "C" fn usize_bytes(x: u32) -> u64 {
    let a = x as usize;
    let le = a.to_le_bytes();
    let be = a.to_be_bytes();
    let mut h = le.len() as u64;
    for i in 0..le.len() {
        h = h * 257 + le[i] as u64 * 3 + be[i] as u64;
    }
    let back = usize::from_ne_bytes(le);
    h ^ ((back == a) as u64) << 63
}

#[no_mangle]
pub extern "C" fn usize_mix64(x: u64, y: u64) -> u64 {
    let a = x as usize;
    let b = y as isize;
    let c = (a as u64) ^ ((b as i64) as u64).rotate_left(1);
    let d = (a.wrapping_add(b as usize)) as u64;
    let e = (b >> 3) as i64 as u64;
    let f = (a as isize) < 0;
    c ^ d.rotate_left(20) ^ e.rotate_left(40) ^ f as u64
}

#[no_mangle]
pub extern "C" fn sizes() -> u32 {
    use core::mem::{align_of, size_of};
    (size_of::<usize>() as u32)
        | (align_of::<u64>() as u32) << 4
        | (align_of::<f64>() as u32) << 8
        | (align_of::<i128>() as u32) << 12
        | (size_of::<Option<&u8>>() as u32) << 17
        | (size_of::<&[u8]>() as u32) << 21
        | (size_of::<(u8, u64)>() as u32) << 26
}

#[no_mangle]
pub extern "C" fn sieve(n: u32) -> u32 {
    let n = (n % 256) as usize;
    let mut comp = BitSet::new();
    let mut count = 0u32;
    let mut last = 0u32;
    for i in 2..n {
        if comp.w[i / W] >> (i % W) & 1 == 0 {
            count += 1;
            last = i as u32;
            let mut j = i * i;
            while j < 256 {
                comp.insert(j);
                j += i;
            }
        }
    }
    count << 16 | last
}

#[no_mangle]
pub extern "C" fn collatz_max(n: u64) -> u64 {
    let mut x = n % 100000 + 1;
    let mut peak = x;
    let mut steps = 0u64;
    while x != 1 && steps < 1000 {
        x = if x % 2 == 0 { x / 2 } else { 3 * x + 1 };
        peak = peak.max(x);
        steps += 1;
    }
    peak << 12 | steps
}
