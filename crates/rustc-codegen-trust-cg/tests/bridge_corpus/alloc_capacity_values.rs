// CORPUS FIXTURE — the `capacity()` std reports after the constructors the
// bridge models, with the default allocator. Each value is std's own sizing:
//
//   * `vec![x; n]`, `<[T]>::repeat(n)`, `str::repeat(n)` and a `split_off`
//     tail reserve exactly `n` (resp. `len * n`, `len - at`) elements, so an
//     empty result has capacity 0 (no allocation at all);
//   * `collect()` from an iterator whose size hint is exact reserves the
//     remaining count up front when the iterator is `TrustedLen` (slice, range,
//     `skip`/`take` over them, `rev`, `enumerate`), and
//     `max(MIN_NON_ZERO_CAP, n)` at the first element otherwise (`inspect`);
//   * `collect()` from an iterator whose lower bound is 0 (`filter`) starts at
//     `MIN_NON_ZERO_CAP` and doubles.
//
// Before the fix the bridge reserved `max(n, 1)` for the constructors (an
// empty result reported capacity 1) and grew every `collect()` by doubling
// from `MIN_NON_ZERO_CAP` (3 elements reported 4, 9 reported 16).
//
// Every row prints `tag = value` lines; `ALLOC_SHAPE` (first byte) selects the
// row, `z` runs all of them.
unsafe extern "C" {
    fn getenv(name: *const u8) -> *const u8;
}

fn shape() -> u8 {
    unsafe {
        let p = getenv(b"ALLOC_SHAPE\0".as_ptr());
        if p.is_null() { 0 } else { *p }
    }
}

#[inline(never)]
fn show(tag: u64, v: u64) {
    println!("{tag} = {v}");
}

#[inline(never)]
fn from_elem(n: usize) {
    let v = vec![7u32; n];
    let c = v.capacity() as u64;
    let l = v.len() as u64;
    show(1, c);
    show(2, l);
}

#[inline(never)]
fn repeat(n: usize) {
    let v = [1u8, 2].repeat(n);
    let c = v.capacity() as u64;
    show(3, c);
}

#[inline(never)]
fn str_repeat(n: usize) {
    let s = "ab".repeat(n);
    let c = s.capacity() as u64;
    show(4, c);
}

#[inline(never)]
fn split_off(at: usize) {
    let mut v: Vec<u64> = Vec::with_capacity(10);
    v.push(1);
    v.push(2);
    v.push(3);
    let t = v.split_off(at);
    let tc = t.capacity() as u64;
    let tl = t.len() as u64;
    let vc = v.capacity() as u64;
    let vl = v.len() as u64;
    show(5, tc);
    show(6, tl);
    show(7, vc);
    show(8, vl);
}

#[inline(never)]
fn collect_slice(a: &[u64]) {
    let v: Vec<u64> = a.iter().copied().collect();
    let c = v.capacity() as u64;
    let l = v.len() as u64;
    show(9, c);
    show(10, l);
}

#[inline(never)]
fn collect_range(n: u64) {
    let v: Vec<u64> = (0..n).collect();
    let c = v.capacity() as u64;
    show(11, c);
}

#[inline(never)]
fn collect_range_inclusive(n: u64) {
    let v: Vec<u64> = (1..=n).collect();
    let c = v.capacity() as u64;
    show(12, c);
}

#[inline(never)]
fn collect_skip_take(a: &[u64]) {
    let s: Vec<u64> = a.iter().copied().skip(2).collect();
    let t: Vec<u64> = a.iter().copied().take(4).collect();
    let sc = s.capacity() as u64;
    let tc = t.capacity() as u64;
    show(13, sc);
    show(14, tc);
}

#[inline(never)]
fn collect_inspect(a: &[u64]) {
    let v: Vec<u64> = a.iter().copied().inspect(|_| ()).collect();
    let c = v.capacity() as u64;
    show(15, c);
}

#[inline(never)]
fn collect_filter(a: &[u64]) {
    let v: Vec<u64> = a.iter().copied().filter(|x| x % 2 == 1).collect();
    let c = v.capacity() as u64;
    let l = v.len() as u64;
    show(16, c);
    show(17, l);
}

#[inline(never)]
fn collect_rev_enumerate(a: &[u64]) {
    let r: Vec<u64> = a.iter().rev().copied().collect();
    let e: Vec<u64> = a.iter().enumerate().map(|(i, x)| i as u64 + x).collect();
    let rc = r.capacity() as u64;
    let ec = e.capacity() as u64;
    show(18, rc);
    show(19, ec);
}

/// Row `j`: a `Skip` ABOVE a `.rev()` is not `TrustedLen` (`Rev` has no
/// `TrustedRandomAccess`), so std sizes these by the nested route,
/// `max(MIN_NON_ZERO_CAP, n)` — not exactly `n`. (`StepBy` above a `.rev()`
/// and a reversed RANGE under `skip` are row `k` of `alloc_collect_routes_o0.rs`:
/// the bridge admits `StepBy` only at -O0, and refuses `(0..n).rev()` by name
/// at -O1.)
#[inline(never)]
fn collect_rev_skip(a: &[u64], b: &[u8]) {
    let v1: Vec<u64> = a.iter().rev().skip(3).copied().collect();
    let v4: Vec<u8> = b.iter().rev().skip(2).copied().collect();
    let v5: Vec<u64> = a.iter().rev().map(|x| x + 1).skip(3).collect();
    let v6: Vec<u64> = a.iter().skip(1).rev().skip(2).copied().collect();
    show(20, v1.capacity() as u64);
    show(23, v4.capacity() as u64);
    show(24, v5.capacity() as u64);
    show(25, v6.capacity() as u64);
}

fn main() {
    let w = shape();
    let z = (w as usize) & 0;
    let nine = [1u64, 2, 3, 4, 5, 6, 7, 8, 9];
    let seven = &nine[..7];
    let all = w == b'z';
    if w == b'a' || all {
        from_elem(z);
        from_elem(3 + z);
    }
    if w == b'b' || all {
        repeat(z);
        repeat(2 + z);
        str_repeat(z);
        str_repeat(3 + z);
    }
    if w == b'c' || all {
        split_off(3 + z);
        split_off(z);
        split_off(1 + z);
    }
    if w == b'd' || all {
        collect_slice(&nine[..3 + z]);
        collect_slice(&nine[..9 + z]);
        collect_slice(&nine[..z]);
    }
    if w == b'e' || all {
        collect_range(10 + z as u64);
        collect_range(z as u64);
        collect_range_inclusive(10 + z as u64);
        collect_range_inclusive(z as u64);
    }
    if w == b'f' || all {
        collect_skip_take(seven);
        collect_skip_take(&nine[..1 + z]);
    }
    if w == b'g' || all {
        collect_inspect(seven);
        collect_inspect(&nine[..2 + z]);
        collect_inspect(&nine[..z]);
    }
    if w == b'h' || all {
        collect_filter(&nine);
        collect_filter(&nine[..z]);
    }
    if w == b'i' || all {
        collect_rev_enumerate(&nine[..6 + z]);
    }
    if w == b'j' || all {
        collect_rev_skip(&nine[..5 + z], b"helloo");
    }
    println!("end");
}
