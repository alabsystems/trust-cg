// CORPUS FIXTURE — the LOCATION a synthesized panic reports: `Option::unwrap`
// (an intercepted `#[track_caller]` std panic) reports the `.unwrap()` call
// site. LLVM oracle 129 at O0/O2; before the fix the bridge reported
// core/src/option.rs (179).
// The panic hook exits with a code derived from the reported file / line /
// column (the harness compares exit codes; panic text goes to stderr), and runs
// before `panic=abort` would. Before, every synthesized raise passed a raw span
// instead of rustc's `get_caller_location(site)` walk.
use std::hint::black_box;
#[inline(never)]
fn run() -> u32 {
    let o: Option<u32> = black_box(None);
    o.unwrap()
}
fn main() {
    std::panic::set_hook(Box::new(|info| {
        let l = info.location().expect("a location");
        let code = (l.line() * 7 + l.column() * 3 + l.file().len() as u32) % 251;
        std::process::exit(code as i32);
    }));
    let x = run();
    std::process::exit((x % 200) as i32 + 1);
}
