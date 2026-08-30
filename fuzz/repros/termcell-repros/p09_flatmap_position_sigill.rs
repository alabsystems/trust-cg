// NEW P0 (found 2026-07-17 by the terminal-cell-fix class fuzz, task #62,
// NOT yet fixed): flat_map+position at O2/O3 ships FlattenCompat::iter_try_fold
// as a bare ud2 while its call survives -> deterministic SIGILL vs std exit 32.
// O0 correctly fail-closes. Unlowerable-body-shipped class (cf. by_ref().take()).
fn main() {
    let pos = (0..20i64).flat_map(|x| 0..x).position(|y| y == 5);
    let d = pos.map(|v| v as i64).unwrap_or(-1);
    let f = || d + 100; // captures d by ref
    let r = f() - d + d * 3;
    std::process::exit((r).rem_euclid(128) as i32);
}
