// P0 (2026-07-17 trap-claim hunt): .enumerate() + find_map/any/all at O2/O3
// ships the trap-stubbed Enumerate::try_fold check-glue as a reachable ud2
// (SIGILL 132). O0 fail-closes. 5th instance of the deadness-claim class.
fn main() {
    let a = [10i64, 20, 33, 40, 55];
    let fm = a.iter().enumerate()
        .find_map(|(i, &v)| if v % 2 == 1 { Some(i as i64 * 100 + v) } else { None });
    std::process::exit((fm.unwrap_or(-7) % 90).rem_euclid(128) as i32)
}
