use std::sync::{
    Mutex,
    atomic::{AtomicU64, Ordering},
};
static LOG: Mutex<Vec<(u64, u64)>> = Mutex::new(Vec::new());
static PANIC_AT: AtomicU64 = AtomicU64::new(0);
static CALLS: AtomicU64 = AtomicU64::new(0);
#[unsafe(no_mangle)]
pub extern "C" fn unwind_event(kind: u64, value: u64) {
    LOG.lock().unwrap().push((kind, value));
}
fn result(v: u64) -> u64 {
    v.rotate_left(13) ^ 0x1122334455667788
}
fn start(v: u64) {
    unwind_event(1, v);
    let n = CALLS.fetch_add(1, Ordering::Relaxed) + 1;
    if n == PANIC_AT.load(Ordering::Relaxed) {
        panic!("call continuation");
    }
}
#[unsafe(no_mangle)]
pub fn unwind_step(v: u64) -> u64 {
    start(v);
    result(v)
}
#[unsafe(no_mangle)]
pub fn unwind_mut_step(cell: &mut u64, v: u64) -> u64 {
    assert_eq!(*cell, v ^ 0x55);
    *cell = cell.wrapping_add(0x1234);
    start(*cell);
    result(v)
}
#[unsafe(no_mangle)]
pub fn unwind_lt(a: u64, b: u64) -> bool {
    start(a);
    a < b
}
unsafe extern "C-unwind" {
    fn check_cell(v: u64) -> u64;
    fn check_projected(v: u64) -> u64;
    fn check_reload(v: u64) -> u64;
    fn check_closure_cell(v: u64) -> u64;
    fn check_closure_pair(v: u64) -> u64;
    fn check_closure_words(v: u64) -> u64;
    fn check_alias_destination(v: u64) -> u64;
    fn check_select_min(v: u64) -> u64;
    fn check_loop(v: u64) -> u64;
    fn check_scalarized_projected(v: u64) -> u64;
    fn check_closure_projected(v: u64) -> u64;
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut checks = 0;
    let abort = std::env::args().nth(1).as_deref() == Some("abort");
    for seed in 0..256u64 {
        let v = seed.wrapping_mul(0x9e3779b97f4a7c15);
        for (case, f) in [
            check_cell,
            check_projected,
            check_reload,
            check_closure_cell,
            check_closure_pair,
            check_closure_words,
            check_loop,
            check_scalarized_projected,
            check_closure_projected,
            check_select_min,
            check_alias_destination,
        ]
        .iter()
        .enumerate()
        {
            for panic_at in 0..=if abort {
                0
            } else if case == 6 {
                4
            } else {
                1
            } {
                PANIC_AT.store(panic_at, Ordering::Relaxed);
                CALLS.store(0, Ordering::Relaxed);
                let actual = std::panic::catch_unwind(|| unsafe { f(v) });
                let mut expected = Vec::new();
                let mut value = v ^ 0x55;
                if case == 0 || case == 3 {
                    expected.push((3, value));
                }
                if case == 6 {
                    for i in 0..4 {
                        let input = if i & 1 == 0 { value } else { value ^ i };
                        expected.push((1, input));
                        if panic_at == i + 1 {
                            break;
                        }
                        value = result(input);
                    }
                    if panic_at == 0 {
                        expected.push((2, value));
                    }
                    expected.push((5, value));
                } else {
                    let mutated = (v ^ 0x55).wrapping_add(0x1234);
                    expected.push((1, if case == 2 || case == 10 { mutated } else { v }));
                    if case == 10 {
                        value = mutated;
                    }
                    if panic_at == 0 {
                        value = match case {
                            9 => v.min(v.rotate_left(31) ^ 0xabcdef),
                            2 => mutated,
                            4 => result(v) ^ (v ^ 0x77),
                            5 => result(v) ^ (v ^ 0x11) ^ !v ^ v.wrapping_mul(31),
                            _ => result(v),
                        };
                        expected.push((2, value));
                    }
                    expected.push((
                        5,
                        if matches!(case, 0 | 1 | 3 | 10) {
                            value
                        } else {
                            0
                        },
                    ));
                    if panic_at == 0 {
                        value = match case {
                            1 | 7 | 8 => value ^ v,
                            2 => result(v) ^ mutated,
                            _ => value,
                        };
                    }
                }
                if panic_at != 0 {
                    assert!(
                        actual.is_err(),
                        "missing panic case={case} seed={seed} at={panic_at}"
                    );
                } else {
                    assert_eq!(actual.unwrap(), value, "result case={case} seed={seed}");
                }
                assert_eq!(
                    *LOG.lock().unwrap(),
                    expected,
                    "events case={case} seed={seed} at={panic_at}"
                );
                LOG.lock().unwrap().clear();
                checks += 1;
            }
        }
    }
    println!("PASS unwind_call checks={checks}");
}
