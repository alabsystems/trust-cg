// CORPUS FIXTURE — an intercepted `collect::<Vec<T>>()` writes the header its
// destination OWNS.
//
// WHAT IT PINS. `lower_vec_collect` builds an empty scratch `{cap,ptr,len}`
// header, binds the destination, then pushes every yielded element. Since the
// real-layout header change (b56846c55) a `Vec` local is memory-backed and the
// bind (`finish_assign_target`) COPIES the scratch header into the local's own
// slot. The push loop kept writing the SCRATCH, so the destination stayed at the
// bind-time snapshot (len 0, cap 0, dangling): every read of it saw an empty Vec
// and its drop freed nothing (the grown buffer leaked). Measured on aarch64
// with origin/main 7b2412bc8, every row below printed 0 at -O0..-O3 (or
// panicked "index out of bounds" / "`at` split index is greater than length")
// where LLVM prints the values shown in the trailing comments.
//
// HOW IT FAILS IF THE FIX IS REVERTED. It COMPILES and DIVERGES from LLVM on
// every row — a hard failure of `vec_collect_header_identity_differential`.

use std::hint::black_box as bb;

/// Order-sensitive checksum read through `len()` and indexing, so both the
/// length and every element of the collected Vec are observed.
#[inline(never)]
fn ck<T: Copy + Into<u64>>(v: &[T]) -> u64 {
    let mut s = 0u64;
    let mut i = 0;
    while i < v.len() {
        s = s.wrapping_mul(31).wrapping_add(v[i].into());
        i += 1;
    }
    s
}
#[inline(never)]
fn cki(v: &[i32]) -> u64 {
    let mut s = 0u64;
    let mut i = 0;
    while i < v.len() {
        s = s.wrapping_mul(31).wrapping_add(v[i] as i64 as u64);
        i += 1;
    }
    s
}

// Range sources, every unsigned width plus signed and usize.
#[inline(never)]
fn range_u8(n: u8) -> u64 {
    let v: Vec<u8> = (0..n).collect();
    v.len() as u64 * 1000 + ck(&v)
}
#[inline(never)]
fn range_u16(n: u16) -> u64 {
    let v: Vec<u16> = (0..n).collect();
    v.len() as u64 * 1000 + ck(&v)
}
#[inline(never)]
fn range_u32(n: u32) -> u64 {
    let v: Vec<u32> = (0..n).collect();
    v.len() as u64 * 1000 + ck(&v)
}
#[inline(never)]
fn range_u64(n: u64) -> u64 {
    let v: Vec<u64> = (3..n).collect();
    v.len() as u64 * 1000 + ck(&v)
}
#[inline(never)]
fn range_i32(n: i32) -> u64 {
    let v: Vec<i32> = (-2..n).collect();
    v.len() as u64 * 1000 + cki(&v)
}
#[inline(never)]
fn range_usize(n: usize) -> u64 {
    let v: Vec<usize> = (0..n).collect();
    (v.len() + v[n - 1]) as u64
}
// A literal-bound source rustc passes as a constant `Range`.
#[inline(never)]
fn range_const() -> u64 {
    let v: Vec<u32> = (0..8).collect();
    v.len() as u64 * 1000 + ck(&v)
}
#[inline(never)]
fn range_inclusive(n: u32) -> u64 {
    let v: Vec<u32> = (1..=n).collect();
    v.len() as u64 * 1000 + ck(&v)
}
#[inline(never)]
fn range_inclusive_i32(n: i32) -> u64 {
    let v: Vec<i32> = (-n..=n).collect();
    v.len() as u64 * 1000 + cki(&v)
}
#[inline(never)]
fn from_iter(n: u32) -> u64 {
    let v = Vec::from_iter(0..n);
    v.len() as u64 * 1000 + ck(&v)
}

// Slice sources and adapters.
#[inline(never)]
fn slice_map(s: &[u32]) -> u64 {
    let v: Vec<u32> = s.iter().map(|x| x + 1).collect();
    v.len() as u64 * 1000 + ck(&v)
}
#[inline(never)]
fn slice_copied(s: &[u64]) -> u64 {
    let v: Vec<u64> = s.iter().copied().collect();
    v.len() as u64 * 1000 + ck(&v)
}
#[inline(never)]
fn slice_cloned(s: &[u32]) -> u64 {
    let v: Vec<u32> = s.iter().cloned().collect();
    v.len() as u64 * 1000 + ck(&v)
}
#[inline(never)]
fn filter(n: u32) -> u64 {
    let v: Vec<u32> = (0..n).filter(|x| x % 3 == 0).collect();
    v.len() as u64 * 1000 + ck(&v)
}
#[inline(never)]
fn filter_map(s: &[u32]) -> u64 {
    let v: Vec<u32> = s.iter().filter(|x| **x > 2).map(|x| x + 100).collect();
    v.len() as u64 * 1000 + ck(&v)
}
#[inline(never)]
fn chain(s: &[u32]) -> u64 {
    let v: Vec<u32> = s.iter().chain(s[1..].iter()).copied().collect();
    v.len() as u64 * 1000 + ck(&v)
}
#[inline(never)]
fn rev(n: u64) -> u64 {
    let v: Vec<u64> = (0..n).rev().collect();
    v.len() as u64 * 1000 + ck(&v)
}
#[inline(never)]
fn take_skip(n: u32) -> u64 {
    let a: Vec<u32> = (0..n).take(4).collect();
    let b: Vec<u32> = (0..n).skip(3).collect();
    (a.len() * 100 + b.len()) as u64 * 1000 + ck(&a) + ck(&b)
}
#[inline(never)]
fn enumerate_map(s: &[u32]) -> u64 {
    let v: Vec<u32> = s.iter().enumerate().map(|(i, x)| i as u32 * x).collect();
    v.len() as u64 * 1000 + ck(&v)
}

// The collected Vec then flows on: mutated, iterated, moved, returned, passed.
#[inline(never)]
fn then_push(n: u32) -> u64 {
    let mut v: Vec<u32> = (0..n).collect();
    v.push(100);
    v.push(200);
    v.len() as u64 * 1000 + ck(&v)
}
#[inline(never)]
fn then_truncate_extend(n: u64) -> u64 {
    let mut v: Vec<u64> = (0..n).collect();
    v.truncate(2);
    v.extend_from_slice(&[9, 9]);
    v.len() as u64 * 1000 + ck(&v)
}
#[inline(never)]
fn then_sum(n: u32) -> u64 {
    let v: Vec<u32> = (0..n).map(|x| x * x).collect();
    v.iter().sum::<u32>() as u64
}
#[inline(never)]
fn then_split_off(n: u32) -> u64 {
    let mut v: Vec<u32> = (0..n).collect();
    let w = v.split_off(2);
    (v.len() * 100 + w.len()) as u64 * 1000 + ck(&w)
}
#[inline(never)]
fn then_clone(n: u32) -> u64 {
    let v: Vec<u32> = (0..n).collect();
    let w = v.clone();
    w.len() as u64 * 1000 + ck(&w)
}
#[inline(never)]
fn branch(n: u32) -> u64 {
    let v: Vec<u32> = if n > 2 {
        (0..n).collect()
    } else {
        (0..n + 2).collect()
    };
    v.len() as u64 * 1000 + ck(&v)
}
#[inline(never)]
fn in_loop(n: u32) -> u64 {
    let mut total = 0usize;
    for k in 0..n {
        let v: Vec<u32> = (0..k).collect();
        total += v.len();
    }
    total as u64
}
#[inline(never)]
fn make(n: u32) -> Vec<u32> {
    (0..n).collect()
}
#[inline(never)]
fn returned(n: u32) -> u64 {
    let v = make(n);
    v.len() as u64 * 1000 + ck(&v)
}
#[inline(never)]
fn consume(v: Vec<u32>) -> u64 {
    v.len() as u64 * 1000 + ck(&v)
}
#[inline(never)]
fn passed(n: u32) -> u64 {
    consume((0..n).collect())
}
#[inline(never)]
fn to_vec_then_map(s: &[u64]) -> u64 {
    let v = s.to_vec();
    let w: Vec<u64> = v.iter().map(|x| x + 1).collect();
    w.len() as u64 * 1000 + ck(&w)
}
// Not a TrustedLen source: std grows from MIN_NON_ZERO_CAP exactly as the
// bridge's push loop does, so capacity is part of the pinned image here.
#[inline(never)]
fn filter_capacity(n: u32) -> u64 {
    let v: Vec<u32> = (0..n).filter(|x| x % 2 == 0).collect();
    (v.len() * 1000 + v.capacity()) as u64
}

fn main() {
    let r = range_u8(bb(5)); //                 36810
    println!("{r}");
    let r = range_u16(bb(6)); //                992115
    println!("{r}");
    let r = range_u32(bb(7)); //                30576571
    println!("{r}");
    let r = range_u64(bb(9)); //                89742483
    println!("{r}");
    let r = range_i32(bb(4)); //                18446744073651376819
    println!("{r}");
    let r = range_usize(bb(5)); //              9
    println!("{r}");
    let r = range_const(); //                   947664708
    println!("{r}");
    let r = range_inclusive(bb(6)); //          30575571
    println!("{r}");
    let r = range_inclusive_i32(bb(3)); //      18446744070988866776
    println!("{r}");
    let r = from_iter(bb(5)); //                36810
    println!("{r}");
    let r = slice_map(bb(&[1, 2, 3])); //       5019
    println!("{r}");
    let r = slice_copied(bb(&[9, 8, 7, 6, 5])); // 8561935
    println!("{r}");
    let r = slice_cloned(bb(&[4, 4])); //       2128
    println!("{r}");
    let r = filter(bb(20)); //                  91715713
    println!("{r}");
    let r = filter_map(bb(&[1, 5, 2, 7])); //   5362
    println!("{r}");
    let r = chain(bb(&[1, 2, 3])); //           991051
    println!("{r}");
    let r = rev(bb(6)); //                      146937165
    println!("{r}");
    let r = take_skip(bb(7)); //               498404
    println!("{r}");
    let r = enumerate_map(bb(&[5, 6, 7])); //   3200
    println!("{r}");
    let r = then_push(bb(3)); //                40013
    println!("{r}");
    let r = then_truncate_extend(bb(5)); //     5249
    println!("{r}");
    let r = then_sum(bb(4)); //                 14
    println!("{r}");
    let r = then_split_off(bb(5)); //           205019
    println!("{r}");
    let r = then_clone(bb(6)); //               992115
    println!("{r}");
    let r = branch(bb(3)); //                   3033
    println!("{r}");
    let r = in_loop(bb(5)); //                  10
    println!("{r}");
    let r = returned(bb(4)); //                 5026
    println!("{r}");
    let r = passed(bb(4)); //                   5026
    println!("{r}");
    let r = to_vec_then_map(bb(&[1, 2])); //    2065
    println!("{r}");
    let r = filter_capacity(bb(10)); //         5008
    println!("{r}");
}
