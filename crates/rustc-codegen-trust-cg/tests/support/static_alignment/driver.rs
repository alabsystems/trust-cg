#![feature(thread_local)]
use std::sync::{
    Barrier,
    atomic::{AtomicUsize, Ordering},
};
static CHECKS: AtomicUsize = AtomicUsize::new(0);
fn check(v: bool) {
    assert!(v);
    CHECKS.fetch_add(1, Ordering::Relaxed);
}
unsafe extern "C" {
    static SA_RO_16: [u64; 2];
    fn sa_ro_16() -> *const u64;
    static mut SA_RW_16: [u64; 2];
    fn sa_rw_16() -> *mut u64;
    static mut SA_ZERO_16: [u64; 2];
    fn sa_zero_16() -> *mut u64;
    #[thread_local]
    static mut SA_TLS_16: [u64; 2];
    fn sa_tls_16() -> *mut u64;
    #[thread_local]
    static mut SA_TZ_16: [u64; 2];
    fn sa_tz_16() -> *mut u64;
    static SA_REL_16: [u64; 2];
    fn sa_rel_16() -> *const u64;
    static SA_MID_16: [u64; 1];
    fn sa_mid_16() -> *const u64;
    fn sa_write_16(zero: bool, i: usize, value: u64) -> u64;
    static SA_RO_64: [u64; 8];
    fn sa_ro_64() -> *const u64;
    static mut SA_RW_64: [u64; 8];
    fn sa_rw_64() -> *mut u64;
    static mut SA_ZERO_64: [u64; 8];
    fn sa_zero_64() -> *mut u64;
    #[thread_local]
    static mut SA_TLS_64: [u64; 8];
    fn sa_tls_64() -> *mut u64;
    #[thread_local]
    static mut SA_TZ_64: [u64; 8];
    fn sa_tz_64() -> *mut u64;
    static SA_REL_64: [u64; 8];
    fn sa_rel_64() -> *const u64;
    static SA_MID_64: [u64; 1];
    fn sa_mid_64() -> *const u64;
    fn sa_write_64(zero: bool, i: usize, value: u64) -> u64;
    static SA_RO_256: [u64; 32];
    fn sa_ro_256() -> *const u64;
    static mut SA_RW_256: [u64; 32];
    fn sa_rw_256() -> *mut u64;
    static mut SA_ZERO_256: [u64; 32];
    fn sa_zero_256() -> *mut u64;
    #[thread_local]
    static mut SA_TLS_256: [u64; 32];
    fn sa_tls_256() -> *mut u64;
    #[thread_local]
    static mut SA_TZ_256: [u64; 32];
    fn sa_tz_256() -> *mut u64;
    static SA_REL_256: [u64; 32];
    fn sa_rel_256() -> *const u64;
    static SA_MID_256: [u64; 1];
    fn sa_mid_256() -> *const u64;
    fn sa_write_256(zero: bool, i: usize, value: u64) -> u64;
    static SA_RO_4096: [u64; 512];
    fn sa_ro_4096() -> *const u64;
    static mut SA_RW_4096: [u64; 512];
    fn sa_rw_4096() -> *mut u64;
    static mut SA_ZERO_4096: [u64; 512];
    fn sa_zero_4096() -> *mut u64;
    #[thread_local]
    static mut SA_TLS_4096: [u64; 512];
    fn sa_tls_4096() -> *mut u64;
    #[thread_local]
    static mut SA_TZ_4096: [u64; 512];
    fn sa_tz_4096() -> *mut u64;
    static SA_REL_4096: [u64; 512];
    fn sa_rel_4096() -> *const u64;
    static SA_MID_4096: [u64; 1];
    fn sa_mid_4096() -> *const u64;
    fn sa_write_4096(zero: bool, i: usize, value: u64) -> u64;
}
fn seed(thread: usize, kind: usize) -> u64 {
    0x1234_5678_0000_0000 | ((thread as u64) << 16) | kind as u64
}
unsafe fn tls(
    a: usize,
    n: usize,
    id: usize,
    functions: [unsafe extern "C" fn() -> *mut u64; 2],
    direct: [*mut u64; 2],
) -> [usize; 2] {
    let mut addresses = [0; 2];
    for kind in 0..2 {
        let p = unsafe { functions[kind]() };
        addresses[kind] = p as usize;
        check((p as usize) % a == 0);
        check(p == direct[kind]);
        for i in 0..n {
            check(
                unsafe { p.add(i).read_volatile() }
                    == if kind == 0 { 0x3000 + a as u64 } else { 0 },
            );
        }
        let value = seed(id, kind);
        unsafe {
            p.write_volatile(value);
            p.add(n - 1).write_volatile(!value);
        }
        for _ in 0..256 {
            let current = unsafe { functions[kind]() };
            check(current == p);
            check(unsafe { current.read_volatile() } == value);
            check(unsafe { current.add(n - 1).read_volatile() } == !value);
        }
    }
    addresses
}
fn main() {
    unsafe {
        let n = 2;
        let a = 16;
        for (p, direct, value) in [
            (sa_ro_16(), (&raw const SA_RO_16).cast::<u64>(), 4112),
            (
                sa_rw_16().cast_const(),
                (&raw const SA_RW_16).cast::<u64>(),
                8208,
            ),
            (
                sa_zero_16().cast_const(),
                (&raw const SA_ZERO_16).cast::<u64>(),
                0,
            ),
        ] {
            check(p == direct);
            check((p as usize) % a == 0);
            for i in 0..n {
                check(p.add(i).read_volatile() == value);
            }
        }
        for zero in [false, true] {
            for i in [0, n - 1] {
                for value in 1..=32 {
                    check(sa_write_16(zero, i, value) == value);
                    let p = if zero {
                        (&raw const SA_ZERO_16).cast::<u64>()
                    } else {
                        (&raw const SA_RW_16).cast::<u64>()
                    };
                    check(p.add(i).read_volatile() == value);
                }
            }
        }
        let r = sa_rel_16();
        check(r == (&raw const SA_REL_16).cast());
        check((r as usize) % a == 0);
        let first = r.cast::<*const u64>().read();
        let second = r.add(1).cast::<*const u64>().read();
        check(first != second);
        for (ptr, value) in [(first, 16400), (second, 20496)] {
            check((ptr as usize) % a == 0);
            for i in 0..n {
                check(ptr.add(i).read_volatile() == value);
            }
        }
        for i in 2..n {
            check(r.add(i).read_volatile() == 24592);
        }
        let mid = sa_mid_16().cast::<*const u64>().read();
        check(mid == (&raw const SA_RO_16).cast::<u64>().add(1));
        check(mid.read() == 4112);
        let parent = tls(
            a,
            n,
            0,
            [sa_tls_16, sa_tz_16],
            [(&raw mut SA_TLS_16).cast(), (&raw mut SA_TZ_16).cast()],
        );
        let barrier = Barrier::new(9);
        let addresses = std::thread::scope(|scope| {
            let mut workers = Vec::new();
            for id in 1..=8 {
                let barrier = &barrier;
                workers.push(scope.spawn(move || {
                    let result = tls(
                        a,
                        n,
                        id,
                        [sa_tls_16, sa_tz_16],
                        [(&raw mut SA_TLS_16).cast(), (&raw mut SA_TZ_16).cast()],
                    );
                    barrier.wait();
                    result
                }));
            }
            barrier.wait();
            workers
                .into_iter()
                .map(|w| w.join().unwrap())
                .collect::<Vec<_>>()
        });
        for i in 0..8 {
            for j in i + 1..8 {
                for kind in 0..2 {
                    check(addresses[i][kind] != addresses[j][kind]);
                }
            }
        }
        for kind in 0..2 {
            let p = parent[kind] as *const u64;
            check(p.read() == seed(0, kind));
            check(p.add(n - 1).read() == !seed(0, kind));
        }
    }
    unsafe {
        let n = 8;
        let a = 64;
        for (p, direct, value) in [
            (sa_ro_64(), (&raw const SA_RO_64).cast::<u64>(), 4160),
            (
                sa_rw_64().cast_const(),
                (&raw const SA_RW_64).cast::<u64>(),
                8256,
            ),
            (
                sa_zero_64().cast_const(),
                (&raw const SA_ZERO_64).cast::<u64>(),
                0,
            ),
        ] {
            check(p == direct);
            check((p as usize) % a == 0);
            for i in 0..n {
                check(p.add(i).read_volatile() == value);
            }
        }
        for zero in [false, true] {
            for i in [0, n - 1] {
                for value in 1..=32 {
                    check(sa_write_64(zero, i, value) == value);
                    let p = if zero {
                        (&raw const SA_ZERO_64).cast::<u64>()
                    } else {
                        (&raw const SA_RW_64).cast::<u64>()
                    };
                    check(p.add(i).read_volatile() == value);
                }
            }
        }
        let r = sa_rel_64();
        check(r == (&raw const SA_REL_64).cast());
        check((r as usize) % a == 0);
        let first = r.cast::<*const u64>().read();
        let second = r.add(1).cast::<*const u64>().read();
        check(first != second);
        for (ptr, value) in [(first, 16448), (second, 20544)] {
            check((ptr as usize) % a == 0);
            for i in 0..n {
                check(ptr.add(i).read_volatile() == value);
            }
        }
        for i in 2..n {
            check(r.add(i).read_volatile() == 24640);
        }
        let mid = sa_mid_64().cast::<*const u64>().read();
        check(mid == (&raw const SA_RO_64).cast::<u64>().add(1));
        check(mid.read() == 4160);
        let parent = tls(
            a,
            n,
            0,
            [sa_tls_64, sa_tz_64],
            [(&raw mut SA_TLS_64).cast(), (&raw mut SA_TZ_64).cast()],
        );
        let barrier = Barrier::new(9);
        let addresses = std::thread::scope(|scope| {
            let mut workers = Vec::new();
            for id in 1..=8 {
                let barrier = &barrier;
                workers.push(scope.spawn(move || {
                    let result = tls(
                        a,
                        n,
                        id,
                        [sa_tls_64, sa_tz_64],
                        [(&raw mut SA_TLS_64).cast(), (&raw mut SA_TZ_64).cast()],
                    );
                    barrier.wait();
                    result
                }));
            }
            barrier.wait();
            workers
                .into_iter()
                .map(|w| w.join().unwrap())
                .collect::<Vec<_>>()
        });
        for i in 0..8 {
            for j in i + 1..8 {
                for kind in 0..2 {
                    check(addresses[i][kind] != addresses[j][kind]);
                }
            }
        }
        for kind in 0..2 {
            let p = parent[kind] as *const u64;
            check(p.read() == seed(0, kind));
            check(p.add(n - 1).read() == !seed(0, kind));
        }
    }
    unsafe {
        let n = 32;
        let a = 256;
        for (p, direct, value) in [
            (sa_ro_256(), (&raw const SA_RO_256).cast::<u64>(), 4352),
            (
                sa_rw_256().cast_const(),
                (&raw const SA_RW_256).cast::<u64>(),
                8448,
            ),
            (
                sa_zero_256().cast_const(),
                (&raw const SA_ZERO_256).cast::<u64>(),
                0,
            ),
        ] {
            check(p == direct);
            check((p as usize) % a == 0);
            for i in 0..n {
                check(p.add(i).read_volatile() == value);
            }
        }
        for zero in [false, true] {
            for i in [0, n - 1] {
                for value in 1..=32 {
                    check(sa_write_256(zero, i, value) == value);
                    let p = if zero {
                        (&raw const SA_ZERO_256).cast::<u64>()
                    } else {
                        (&raw const SA_RW_256).cast::<u64>()
                    };
                    check(p.add(i).read_volatile() == value);
                }
            }
        }
        let r = sa_rel_256();
        check(r == (&raw const SA_REL_256).cast());
        check((r as usize) % a == 0);
        let first = r.cast::<*const u64>().read();
        let second = r.add(1).cast::<*const u64>().read();
        check(first != second);
        for (ptr, value) in [(first, 16640), (second, 20736)] {
            check((ptr as usize) % a == 0);
            for i in 0..n {
                check(ptr.add(i).read_volatile() == value);
            }
        }
        for i in 2..n {
            check(r.add(i).read_volatile() == 24832);
        }
        let mid = sa_mid_256().cast::<*const u64>().read();
        check(mid == (&raw const SA_RO_256).cast::<u64>().add(1));
        check(mid.read() == 4352);
        let parent = tls(
            a,
            n,
            0,
            [sa_tls_256, sa_tz_256],
            [(&raw mut SA_TLS_256).cast(), (&raw mut SA_TZ_256).cast()],
        );
        let barrier = Barrier::new(9);
        let addresses = std::thread::scope(|scope| {
            let mut workers = Vec::new();
            for id in 1..=8 {
                let barrier = &barrier;
                workers.push(scope.spawn(move || {
                    let result = tls(
                        a,
                        n,
                        id,
                        [sa_tls_256, sa_tz_256],
                        [(&raw mut SA_TLS_256).cast(), (&raw mut SA_TZ_256).cast()],
                    );
                    barrier.wait();
                    result
                }));
            }
            barrier.wait();
            workers
                .into_iter()
                .map(|w| w.join().unwrap())
                .collect::<Vec<_>>()
        });
        for i in 0..8 {
            for j in i + 1..8 {
                for kind in 0..2 {
                    check(addresses[i][kind] != addresses[j][kind]);
                }
            }
        }
        for kind in 0..2 {
            let p = parent[kind] as *const u64;
            check(p.read() == seed(0, kind));
            check(p.add(n - 1).read() == !seed(0, kind));
        }
    }
    unsafe {
        let n = 512;
        let a = 4096;
        for (p, direct, value) in [
            (sa_ro_4096(), (&raw const SA_RO_4096).cast::<u64>(), 8192),
            (
                sa_rw_4096().cast_const(),
                (&raw const SA_RW_4096).cast::<u64>(),
                12288,
            ),
            (
                sa_zero_4096().cast_const(),
                (&raw const SA_ZERO_4096).cast::<u64>(),
                0,
            ),
        ] {
            check(p == direct);
            check((p as usize) % a == 0);
            for i in 0..n {
                check(p.add(i).read_volatile() == value);
            }
        }
        for zero in [false, true] {
            for i in [0, n - 1] {
                for value in 1..=32 {
                    check(sa_write_4096(zero, i, value) == value);
                    let p = if zero {
                        (&raw const SA_ZERO_4096).cast::<u64>()
                    } else {
                        (&raw const SA_RW_4096).cast::<u64>()
                    };
                    check(p.add(i).read_volatile() == value);
                }
            }
        }
        let r = sa_rel_4096();
        check(r == (&raw const SA_REL_4096).cast());
        check((r as usize) % a == 0);
        let first = r.cast::<*const u64>().read();
        let second = r.add(1).cast::<*const u64>().read();
        check(first != second);
        for (ptr, value) in [(first, 20480), (second, 24576)] {
            check((ptr as usize) % a == 0);
            for i in 0..n {
                check(ptr.add(i).read_volatile() == value);
            }
        }
        for i in 2..n {
            check(r.add(i).read_volatile() == 28672);
        }
        let mid = sa_mid_4096().cast::<*const u64>().read();
        check(mid == (&raw const SA_RO_4096).cast::<u64>().add(1));
        check(mid.read() == 8192);
        let parent = tls(
            a,
            n,
            0,
            [sa_tls_4096, sa_tz_4096],
            [(&raw mut SA_TLS_4096).cast(), (&raw mut SA_TZ_4096).cast()],
        );
        let barrier = Barrier::new(9);
        let addresses = std::thread::scope(|scope| {
            let mut workers = Vec::new();
            for id in 1..=8 {
                let barrier = &barrier;
                workers.push(scope.spawn(move || {
                    let result = tls(
                        a,
                        n,
                        id,
                        [sa_tls_4096, sa_tz_4096],
                        [(&raw mut SA_TLS_4096).cast(), (&raw mut SA_TZ_4096).cast()],
                    );
                    barrier.wait();
                    result
                }));
            }
            barrier.wait();
            workers
                .into_iter()
                .map(|w| w.join().unwrap())
                .collect::<Vec<_>>()
        });
        for i in 0..8 {
            for j in i + 1..8 {
                for kind in 0..2 {
                    check(addresses[i][kind] != addresses[j][kind]);
                }
            }
        }
        for kind in 0..2 {
            let p = parent[kind] as *const u64;
            check(p.read() == seed(0, kind));
            check(p.add(n - 1).read() == !seed(0, kind));
        }
    }
    println!(
        "PASS static_alignment checks={}",
        CHECKS.load(Ordering::Relaxed)
    );
}
