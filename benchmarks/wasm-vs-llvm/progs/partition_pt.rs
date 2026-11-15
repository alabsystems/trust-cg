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

#[inline(never)]
fn bsearch(a: &[i32], t: i32) -> Result<usize, usize> {
    a.binary_search_by(|p| p.cmp(&t))
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
pub extern "C" fn partition_pt(t: u32, n: u32) -> u32 {
    let mut a = [0u32; 64];
    let n = (n % 65) as usize;
    for i in 0..n {
        a[i] = (i as u32) * (i as u32);
    }
    a[..n].partition_point(|&x| x < t) as u32
}
