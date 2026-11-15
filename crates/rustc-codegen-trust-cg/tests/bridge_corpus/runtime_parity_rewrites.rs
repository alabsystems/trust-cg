// Fixture for runtime_parity_rewrites_aarch64.rs: the loop shapes four
// trust-cg-opt rewrites target, each over many constants and trip counts.
//
// * `xorshift_pair::<A, B, C>`: a loop-carried `x ^= x << A; x ^= x >> B`
//   pair (xorshift-pair-fusion), for shift pairs with A < B, A == B, A > B
//   and both ends of 1..=63; `xorshift128p` the same pair on a copy of the
//   carried state; `xorshift32` the 32-bit shape the pass refuses.
// * `box_sum`: `acc += *v[k]` under `while k < v.len()` (scalar-unroll's
//   unsigned top-tested gather with lane-offset loads), twice over, at every
//   length from 0 to 9 and around the 4-lane block.
// * `madd_chain::<K>`: `a = a * K + (c ^ i)` on a loop recurrence
//   (mul-shift-reduce's late addend), for `2^k - 1`, `1 - 2^k` and the
//   `2^k + 1` / `2^k` controls.
// * `vec_push_sum` / `vec_grow`: a `Vec` built and read in one function
//   (SROA and LICM through a constant-register field address).
// * `rem_i32::<D>` / `div_u64::<D>` / `rem_u32::<D>`: division and remainder
//   by constants, among them the even ones whose magic needs the add-back
//   form at full width (the selector pre-shifts the dividend), and
//   `(x % D) as i32`, whose remainder tail is written in the W form.
// * `lcg_twice`: `p3_gcd`'s two LCG steps per iteration, whose repeated
//   64-bit constants const-chain-dedup materializes once.
//
// Every input derives from one `black_box` value and every measured function
// is `#[inline(never)]`; each row prints one line.

#[inline(never)]
fn xorshift_pair<const A: u32, const B: u32, const C: u32>(seed: u64, n: u64) -> u64 {
    let mut x = seed;
    let mut acc = 0u64;
    let mut i = 0u64;
    while i < n {
        x ^= x << A;
        x ^= x >> B;
        x ^= x << C;
        acc = acc.wrapping_add(x);
        i += 1;
    }
    acc ^ x
}

#[inline(never)]
fn xorshift128p(seed: u64, n: u64) -> u64 {
    let (mut s0, mut s1) = (seed, seed.rotate_left(29) ^ 0x2545_F491_4F6C_DD1D);
    let mut acc = 0u64;
    let mut i = 0u64;
    while i < n {
        let mut t = s0;
        let s = s1;
        s0 = s;
        t ^= t << 23;
        t ^= t >> 17;
        t ^= s ^ (s >> 26);
        s1 = t;
        acc = acc.wrapping_add(t.wrapping_add(s));
        i += 1;
    }
    acc
}

#[inline(never)]
fn xorshift32(seed: u32, n: u32) -> u32 {
    let mut x = seed | 1;
    let mut acc = 0u32;
    let mut i = 0u32;
    while i < n {
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        acc = acc.wrapping_add(x);
        i += 1;
    }
    acc ^ x
}

/// `h3_box_leak`'s shape: the `Vec` is built in the function (so it lives in
/// registers) and summed by an inner `while k < v.len()` loop.
#[inline(never)]
fn box_sum(len: usize, seed: u64, passes: u32) -> u64 {
    let mut v: Vec<Box<u64>> = Vec::new();
    let mut i = 0usize;
    while i < len {
        v.push(Box::new(seed.rotate_left(i as u32 % 64) ^ (i as u64)));
        i += 1;
    }
    let mut acc = 0u64;
    let mut p = 0u32;
    while p < passes {
        let mut k = 0usize;
        while k < v.len() {
            acc = acc.wrapping_add(*v[k]);
            k += 1;
        }
        p += 1;
    }
    acc
}

#[inline(never)]
fn madd_chain<const K: u64>(seed: u64, n: u64) -> u64 {
    let (mut a, mut b, mut c) = (seed, seed.rotate_left(17), seed ^ 0x5555);
    let mut i = 0u64;
    while i < n {
        a = a.wrapping_mul(K).wrapping_add(c ^ i);
        b = b.wrapping_add(a >> 7);
        c = b ^ (c << 3);
        i += 1;
    }
    a ^ b ^ c
}

#[inline(never)]
fn vec_push_sum(n: usize, seed: u64) -> u64 {
    let mut v: Vec<u64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        v.push(seed.wrapping_mul(i as u64 + 1));
        i += 1;
    }
    let mut s = 0u64;
    let mut k = 0usize;
    while k < v.len() {
        s = s.wrapping_add(v[k] ^ (k as u64));
        k += 1;
    }
    s ^ (v.len() as u64)
}

#[inline(never)]
fn vec_grow(n: usize, seed: u64) -> u64 {
    let mut v: Vec<u64> = Vec::new();
    let mut last = seed;
    let mut i = 0usize;
    while i < n {
        last = last.rotate_left(7) ^ (i as u64);
        v.push(last);
        if v.len() > 3 && v[v.len() - 2] & 1 == 0 {
            v.pop();
        }
        i += 1;
    }
    let mut s = v.len() as u64;
    let mut k = 0usize;
    while k < v.len() {
        s = s.wrapping_mul(31).wrapping_add(v[k]);
        k += 1;
    }
    s
}

#[inline(never)]
fn rem_i32<const D: u64>(x: u64) -> i32 {
    (x % D) as i32
}

#[inline(never)]
fn div_u64<const D: u64>(x: u64) -> u64 {
    x / D
}

#[inline(never)]
fn rem_u32<const D: u32>(x: u32) -> u32 {
    x % D
}

#[inline(never)]
fn lcg_twice(seed: u64, n: u64) -> u64 {
    let mut s = seed;
    let mut acc = 0u64;
    let mut i = 0u64;
    while i < n {
        s = s
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let a = s >> 16;
        s = s
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        acc = acc.wrapping_add(a ^ (s >> 16));
        i += 1;
    }
    acc ^ s
}

macro_rules! divisor_rows {
    ($xs:expr; $f:ident, $t:ty; $($d:literal),* $(,)?) => {
        $(
            let mut j = 0;
            while j < $xs.len() {
                let x = $xs[j] as $t;
                j += 1;
                println!("{} {} x={} {}", stringify!($f), stringify!($d), x, $f::<$d>(x));
            }
        )*
    };
}

macro_rules! xorshift_rows {
    ($seed:expr, $n:expr; $(($a:literal, $b:literal, $c:literal)),* $(,)?) => {
        $(
            println!(
                "xorshift_pair {} {} {} n={} {}",
                $a, $b, $c, $n, xorshift_pair::<$a, $b, $c>($seed, $n)
            );
        )*
    };
}

macro_rules! madd_rows {
    ($seed:expr, $n:expr; $($k:expr),* $(,)?) => {
        $(
            let k: u64 = $k;
            println!("madd_chain {} n={} {}", k, $n, madd_chain::<{ $k }>($seed, $n));
        )*
    };
}

fn main() {
    // 1, through `black_box` as the beat-llvm corpus does. Each measured
    // function is `#[inline(never)]`, so its loop is compiled for a run-time
    // argument either way.
    let rt = std::hint::black_box(1u64);
    let seed = 0x9E37_79B9_7F4A_7C15u64 ^ rt;
    let trips = [rt - 1, rt, rt + 2, 1000 + rt];
    let mut t = 0;
    while t < trips.len() {
        let n = trips[t];
        t += 1;
        xorshift_rows!(seed, n;
            (13, 7, 17), (7, 13, 17), (12, 25, 27), (21, 35, 4), (1, 63, 1),
            (63, 1, 63), (32, 32, 32), (1, 1, 1), (63, 63, 63), (5, 60, 2),
            (60, 5, 2), (33, 31, 9), (31, 33, 9), (2, 3, 1), (40, 40, 7),
        );
        println!("xorshift128p n={n} {}", xorshift128p(seed, n));
        println!("lcg_twice n={n} {}", lcg_twice(seed, n));
        println!("xorshift32 n={n} {}", xorshift32(seed as u32, n as u32));
        madd_rows!(seed, n;
            3, 7, 31, 127, 255, 0x7fff, 0xffff_ffff, 0x7fff_ffff_ffff_ffff,
            1u64.wrapping_sub(1 << 1), 1u64.wrapping_sub(1 << 5), 1u64.wrapping_sub(1 << 12),
            1u64.wrapping_sub(1 << 40), 33, 9, 32,
        );
    }
    let dividends = [
        rt - 1,
        rt,
        125 + rt,
        126 + rt - 1,
        u64::MAX - rt + 1,
        (u64::MAX >> 1) + rt,
        seed,
        seed.rotate_left(31),
        u64::from(u32::MAX) + rt,
        13_999 + rt,
    ];
    divisor_rows!(dividends; rem_i32, u64; 7, 14, 28, 100, 126, 255, 257, 1000);
    divisor_rows!(dividends; div_u64, u64; 14, 126, 1000, 0x7FFF_FFFF_FFFF_FFFE);
    divisor_rows!(dividends; rem_u32, u32; 14, 28, 126);
    let lens = [0usize, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 63, 64, 65, 1001];
    let mut l = 0;
    while l < lens.len() {
        let len = lens[l] + rt as usize - 1;
        l += 1;
        println!("box_sum len={len} {}", box_sum(len, seed, rt as u32 + 1));
        println!("vec_push_sum n={len} {}", vec_push_sum(len, seed));
        println!("vec_grow n={len} {}", vec_grow(len, seed));
    }
}
