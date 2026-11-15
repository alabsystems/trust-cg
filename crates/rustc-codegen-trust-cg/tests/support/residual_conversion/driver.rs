use std::sync::Mutex;
static LOG: Mutex<Vec<(u64, u64, u64)>> = Mutex::new(Vec::new());
static OWNED: Mutex<Vec<usize>> = Mutex::new(Vec::new());
static COUNTS: Mutex<(usize, usize)> = Mutex::new((0, 0));
#[unsafe(no_mangle)]
pub extern "C" fn residual_record(kind: u64, a: u64, b: u64) {
    LOG.lock().unwrap().push((kind, a, b));
}
#[unsafe(no_mangle)]
pub extern "C" fn residual_allocate(value: u64) -> *mut u64 {
    let p = Box::into_raw(Box::new(value));
    OWNED.lock().unwrap().push(p as usize);
    COUNTS.lock().unwrap().0 += 1;
    p
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn residual_release(p: *mut u64) {
    let mut owned = OWNED.lock().unwrap();
    let i = owned
        .iter()
        .position(|&q| q == p as usize)
        .expect("exactly-once release");
    owned.swap_remove(i);
    unsafe {
        residual_record(7, *p, 0);
        drop(Box::from_raw(p));
    }
    COUNTS.lock().unwrap().1 += 1;
}
unsafe extern "C" {
    fn residual_scalar(v: u64, fail: bool) -> u64;
    fn residual_narrow(v: u64, fail: bool) -> u64;
    fn residual_pair(v: u64, fail: bool) -> u64;
    fn residual_enum(v: u64, fail: bool) -> u64;
    fn residual_zero(v: u64, fail: bool) -> u64;
    fn residual_owned(v: u64, fail: bool) -> u64;
    fn residual_chain(v: u64, fail: bool) -> u64;
    fn residual_identity(v: u64, fail: bool) -> u64;
    fn residual_direct(v: u64, fail: bool) -> u64;
    fn residual_indirect(v: u64, fail: bool) -> u64;
}
fn check(got: u64, want: u64, trace: &[(u64, u64, u64)], checks: &mut usize) {
    assert_eq!(got, want, "case {checks}");
    let mut log = LOG.lock().unwrap();
    assert_eq!(&*log, trace, "trace {checks}");
    log.clear();
    *checks += 1;
}
fn main() {
    let mut checks = 0;
    for i in 0..1024_u64 {
        let v = i.wrapping_mul(0x9e3779b97f4a7c15);
        for fail in [false, true] {
            unsafe {
                for f in [residual_scalar, residual_direct, residual_indirect] {
                    let got = f(v, fail);
                    if fail {
                        check(got, v.wrapping_add(17), &[(1, v, 0)], &mut checks)
                    } else {
                        check(got, v ^ 123, &[], &mut checks)
                    }
                }
                let got = residual_narrow(v, fail);
                let x = v as u8 as u64;
                if fail {
                    check(
                        got,
                        (x + 1) ^ (x ^ 0xfedcba9876543210),
                        &[(2, x, 0)],
                        &mut checks,
                    )
                } else {
                    check(got, 123, &[], &mut checks)
                }
                let got = residual_pair(v, fail);
                if fail {
                    check(
                        got,
                        (v | 1) ^ v.wrapping_add(123) ^ 0x7351,
                        &[(3, v | 1, v.wrapping_add(123))],
                        &mut checks,
                    )
                } else {
                    check(got, 123, &[], &mut checks)
                }
                let got = residual_enum(v, fail);
                let a = v as u32 as u64;
                let b = if v & 1 == 0 {
                    0
                } else {
                    (v >> 32) as u8 as u64
                };
                if fail {
                    check(got, a.wrapping_mul(17) ^ b, &[(4, a, b)], &mut checks)
                } else {
                    check(got, 123, &[], &mut checks)
                }
                let got = residual_zero(v, fail);
                if fail {
                    check(got, 0x12345678, &[(5, 0, 0)], &mut checks)
                } else {
                    check(got, 123, &[], &mut checks)
                }
                let got = residual_owned(v, fail);
                if fail {
                    check(got, v ^ 0xdead, &[(6, v, 0), (7, v, 0)], &mut checks)
                } else {
                    check(got, v ^ 123, &[], &mut checks)
                }
                let got = residual_chain(v, fail);
                if fail {
                    check(
                        got,
                        (v ^ 0x4567).wrapping_add(37),
                        &[(8, v, 0), (9, v ^ 0x4567, 0)],
                        &mut checks,
                    )
                } else {
                    check(got, v ^ 123, &[], &mut checks)
                }
                let got = residual_identity(v, fail);
                check(got, if fail { v } else { v ^ 123 }, &[], &mut checks);
                assert!(OWNED.lock().unwrap().is_empty());
            }
        }
        assert_eq!(
            *COUNTS.lock().unwrap(),
            ((i + 1) as usize, (i + 1) as usize)
        );
    }
    println!("PASS residual_conversion checks={checks}");
}
