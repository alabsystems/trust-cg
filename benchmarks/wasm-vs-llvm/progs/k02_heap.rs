#![no_std]
#![allow(dead_code)]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[inline(never)]
fn next(s: &mut u32) -> u32 {
    *s ^= *s << 13;
    *s ^= *s >> 17;
    *s ^= *s << 5;
    *s
}

struct Heap {
    data: [i64; 64],
    len: usize,
}

impl Heap {
    #[inline(never)]
    fn new() -> Heap {
        Heap {
            data: [0; 64],
            len: 0,
        }
    }
    #[inline(never)]
    fn push(&mut self, v: i64) -> bool {
        if self.len == self.data.len() {
            return false;
        }
        let mut i = self.len;
        self.data[i] = v;
        self.len += 1;
        while i > 0 {
            let p = (i - 1) / 2;
            if self.data[p] >= self.data[i] {
                break;
            }
            self.data.swap(p, i);
            i = p;
        }
        true
    }
    #[inline(never)]
    fn pop(&mut self) -> Option<i64> {
        if self.len == 0 {
            return None;
        }
        let top = self.data[0];
        self.len -= 1;
        self.data[0] = self.data[self.len];
        let mut i = 0;
        loop {
            let l = 2 * i + 1;
            let r = l + 1;
            let mut m = i;
            if l < self.len && self.data[l] > self.data[m] {
                m = l;
            }
            if r < self.len && self.data[r] > self.data[m] {
                m = r;
            }
            if m == i {
                break;
            }
            self.data.swap(i, m);
            i = m;
        }
        Some(top)
    }
}

#[no_mangle]
pub extern "C" fn heap_drain(seed: u32, n: u32) -> i64 {
    let mut h = Heap::new();
    let mut s = seed | 1;
    let n = n % 70;
    for _ in 0..n {
        let v = next(&mut s) as i32 as i64 * 3;
        h.push(v);
    }
    let mut acc = 0i64;
    let mut prev = i64::MAX;
    let mut sorted = 1;
    while let Some(x) = h.pop() {
        if x > prev {
            sorted = 0;
        }
        prev = x;
        acc = acc.wrapping_mul(1000003).wrapping_add(x);
    }
    acc ^ sorted
}

#[inline(never)]
fn quickselect(a: &mut [u32], k: usize) -> u32 {
    let mut lo = 0usize;
    let mut hi = a.len() - 1;
    let mut guard = 0;
    while lo < hi && guard < 200 {
        guard += 1;
        let pivot = a[(lo + hi) / 2];
        let mut i = lo;
        let mut j = hi;
        loop {
            while a[i] < pivot {
                i += 1;
            }
            while a[j] > pivot {
                j -= 1;
            }
            if i >= j {
                break;
            }
            a.swap(i, j);
            i += 1;
            j -= 1;
        }
        if k <= j {
            hi = j;
        } else {
            lo = j + 1;
        }
    }
    a[k]
}

#[no_mangle]
pub extern "C" fn qselect(seed: u32, k: u32) -> u32 {
    let mut a = [0u32; 41];
    let mut s = seed | 1;
    for x in a.iter_mut() {
        *x = next(&mut s) % 97;
    }
    quickselect(&mut a, (k % 41) as usize)
}

#[inline(never)]
fn insertion_sort<T: PartialOrd + Copy>(a: &mut [T]) {
    for i in 1..a.len() {
        let x = a[i];
        let mut j = i;
        while j > 0 && a[j - 1] > x {
            a[j] = a[j - 1];
            j -= 1;
        }
        a[j] = x;
    }
}

#[no_mangle]
pub extern "C" fn isort_f64(a: f64, b: f64) -> u64 {
    let mut v = [a, b, a + b, a - b, a * b, -a, 1.0, -0.0, 0.0, b * 0.5];
    if v.iter().any(|x| x.is_nan()) {
        return 1;
    }
    insertion_sort(&mut v);
    let mut h = 0u64;
    for x in v.iter() {
        h = h.rotate_left(7) ^ (*x as i64 as u64);
    }
    h
}

#[inline(never)]
fn bsearch(a: &[i32], t: i32) -> Result<usize, usize> {
    let mut lo = 0usize;
    let mut hi = a.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        match a[mid].cmp(&t) {
            core::cmp::Ordering::Less => lo = mid + 1,
            core::cmp::Ordering::Greater => hi = mid,
            core::cmp::Ordering::Equal => return Ok(mid),
        }
    }
    Err(lo)
}

#[no_mangle]
pub extern "C" fn bsearch_hand(t: i32, n: u32) -> i32 {
    let mut a = [0i32; 50];
    let n = (n % 51) as usize;
    for i in 0..n {
        a[i] = (i as i32) * 7 - 100;
    }
    match bsearch(&a[..n], t) {
        Ok(i) => i as i32,
        Err(i) => -(i as i32) - 1,
    }
}

#[inline(never)]
fn lower_bound_f64(a: &[f64], t: f64) -> usize {
    let mut size = a.len();
    let mut base = 0usize;
    while size > 1 {
        let half = size / 2;
        let mid = base + half;
        base = if a[mid] <= t { mid } else { base };
        size -= half;
    }
    base + (size == 1 && a[base] <= t) as usize
}

#[no_mangle]
pub extern "C" fn lb_f64(t: f64, n: u32) -> u32 {
    let mut a = [0f64; 40];
    let n = (n % 41) as usize;
    for i in 0..n {
        a[i] = (i as f64) * 0.75 - 10.0;
    }
    lower_bound_f64(&a[..n], t) as u32
}

#[inline(never)]
fn heapsort(a: &mut [u64]) {
    let n = a.len();
    fn sift(a: &mut [u64], mut root: usize, end: usize) {
        loop {
            let mut child = 2 * root + 1;
            if child >= end {
                break;
            }
            if child + 1 < end && a[child] < a[child + 1] {
                child += 1;
            }
            if a[root] >= a[child] {
                break;
            }
            a.swap(root, child);
            root = child;
        }
    }
    let mut i = n / 2;
    while i > 0 {
        i -= 1;
        sift(a, i, n);
    }
    let mut end = n;
    while end > 1 {
        end -= 1;
        a.swap(0, end);
        sift(a, 0, end);
    }
}

#[no_mangle]
pub extern "C" fn hsort(seed: u64, n: u32) -> u64 {
    let mut a = [0u64; 33];
    let n = (n % 34) as usize;
    let mut s = seed;
    for i in 0..n {
        s = s.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(i as u64);
        a[i] = s >> 40;
    }
    heapsort(&mut a[..n]);
    let mut h = 0u64;
    for i in 1..n {
        h = h.wrapping_add((a[i] - a[i - 1]) ^ a[i - 1]);
    }
    h
}

#[no_mangle]
pub extern "C" fn median3(a: i32, b: i32) -> i32 {
    let c = a.wrapping_mul(b);
    let mut v = [a, b, c, a ^ b, b.wrapping_sub(a)];
    insertion_sort(&mut v);
    v[2] ^ (v[0] >> 3)
}
