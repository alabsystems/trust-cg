#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: ONE HOME PER LOCAL — a local that is both memory-backed
// (it has a stack SLOT) and address-captured (it would also get a scalar CELL)
// must be read and written through ONE of the two, never both.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE DEFECT. `compute_memory_backed_locals` and `compute_scalar_cell_locals`
// are independent analyses, and a type both accept got two entry-block allocas:
// a closure environment with exactly ONE capture (a memory-backed closure AND a
// single scalar leaf), or an address-taken `MaybeUninit<u64>` that a closure
// also captures. The lowering arms then split between the two homes: the
// entry-block store of a by-value PARAMETER, the by-value closure receiver and
// the return use the SLOT, while `&local` / `&mut local` and whole-local
// assignments use the CELL. So
//
//     fn outer<F: FnMut(u64) -> u64>(mut f: F, n: u64) -> u64 {
//         inner(|x| f(x).wrapping_mul(3), n)
//     }
//
// stored the incoming `f` into its slot and handed `inner` a closure whose
// `&mut f` capture was the NEVER-WRITTEN cell: SIGSEGV on the null environment
// of a `&`/`&mut`-capturing `f`, and a `move` closure's state silently restarted
// from zero for a by-value capture.
//
// MEASURED before the fix, by this test on its consolidation base (origin/main
// `5828b4ce6`, aarch64-apple-darwin, Trust pack 9192, `no-proof-certs`); the
// `landA/nullenv` worktree first measured the same rows on `ad7ee9c4e`:
//
//     row                  LLVM         pre-fix trust-cg (O0 / O3)
//     ref_mut_capture      90 11        SIGSEGV / SIGSEGV
//     shared_capture       78 5         SIGSEGV / SIGSEGV
//     move_state_then_call 1101         1036 / 1036
//     param_after_scalars  90 11        SIGSEGV / SIGSEGV
//     param_on_stack       240 11       SIGSEGV / 80 5
//     move_then_fn_once    901011       garbage (735393440941005) / 301005
//     reborrowed_again     900042       300027 / 300027
//     move_u32_state       900018       300013 / 300013
//     move_u8_state        900018       300013 / 300013
//     local_move_closure   901011       [TCG-MIR-UNSUPPORTED] (O0 only; O3 refuses
//                                       with and without the fix)
//     maybe_uninit_capture 34012        10006 (O0 only; O3 likewise refuses)
//
// The CONTROL rows (zero and two captures; a plain scalar parameter; a
// two-field tuple parameter) matched before and must keep matching: they pin
// that the fix did not move a local that only ever had one home.
//
// COUNTS. 15 rows: 13 at O0 and O3, and 2 (`local_move_closure`,
// `maybe_uninit_capture`) at O0 only, so 28 row x opt-level cells. Before the
// fix, 20 cells were wrong or refused (the 9 two-level defect rows above at
// both levels, plus the 2 O0-only rows) and the 8 control cells matched; with
// the fix all 28 compile and match. Re-measured with the bridge source of
// origin/main `e7f950a1e` (same host, trustc 1.99.0-dev 321aaeda7): the same
// 20 cells fail with the same values, except the never-written cell's garbage
// in `move_then_fn_once` at O0, which differs from run to run.
//
// THE GATE. Each row is compiled BY THE BRIDGE and BY LLVM at the same
// optimization level, run, and compared on STDOUT and EXIT STATUS (a signal is
// a status too). Every row MUST compile on the bridge at the levels it lists —
// a refusal there is a failure, because `local_move_closure` refused before the
// fix and a harness that tolerated refusals would pass against that half of the
// defect.
//
// HOST-NATIVE: no `--target` is passed. `no-proof-certs` isolates MIR lowering
// from the per-compile proof certificates, as the other lowering differentials
// here do.

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;

const PRELUDE: &str = "\
#[inline(never)]
fn inner<G: FnMut(u64) -> u64>(mut g: G, n: u64) -> u64 {
    let mut s = 0u64;
    let mut i = 0u64;
    while i < n { s = s.wrapping_add(g(i)); i += 1; }
    s
}
#[inline(never)]
fn once<F: FnOnce(u64) -> u64>(f: F) -> u64 { f(1000) }
";

struct Case {
    name: &'static str,
    /// Opt levels at which the bridge MUST compile and match LLVM.
    opts: &'static [&'static str],
    body: &'static str,
}

const BOTH: &[&str] = &["0", "3"];
const O0_ONLY: &[&str] = &["0"];

fn cases() -> Vec<Case> {
    vec![
        // --- rows that were wrong before the fix ---
        Case {
            name: "ref_mut_capture",
            opts: BOTH,
            body: "#[inline(never)]
fn outer<F: FnMut(u64) -> u64>(mut f: F, n: u64) -> u64 { inner(|x| f(x).wrapping_mul(3), n) }
fn main() { let mut h = 5u64; let r = outer(|x| { h = h.wrapping_add(x); h }, 4); println!(\"{} {}\", r, h); }",
        },
        Case {
            name: "shared_capture",
            opts: BOTH,
            body: "#[inline(never)]
fn outer<F: Fn(u64) -> u64>(f: F, n: u64) -> u64 { inner(|x| f(x).wrapping_mul(3), n) }
fn main() { let h = 5u64; let r = outer(|x| h.wrapping_add(x), 4); println!(\"{} {}\", r, h); }",
        },
        Case {
            name: "move_state_then_call",
            opts: BOTH,
            body: "#[inline(never)]
fn outer<F: FnMut(u64) -> u64>(mut f: F, n: u64) -> u64 { let a = inner(|x| f(x).wrapping_mul(3), n); a.wrapping_add(f(1000)) }
fn main() { let mut c = 5u64; let r = outer(move |x| { c = c.wrapping_add(x); c }, 4); println!(\"{}\", r); }",
        },
        Case {
            name: "param_after_scalars",
            opts: BOTH,
            body: "#[inline(never)]
fn outer<F: FnMut(u64) -> u64>(n: u64, m: u64, mut f: F) -> u64 { inner(|x| f(x).wrapping_mul(m), n) }
fn main() { let mut h = 5u64; let r = outer(4, 3, |x| { h = h.wrapping_add(x); h }); println!(\"{} {}\", r, h); }",
        },
        Case {
            name: "param_on_stack",
            opts: BOTH,
            body: "#[inline(never)]
fn outer<F: FnMut(u64) -> u64>(a: u64, b: u64, c: u64, d: u64, e: u64, g: u64, h2: u64, i: u64, mut f: F) -> u64 { inner(|x| f(x).wrapping_mul(a+b+c+d+e+g+h2+i), 4) }
fn main() { let mut h = 5u64; let r = outer(1,1,1,1,1,1,1,1, |x| { h = h.wrapping_add(x); h }); println!(\"{} {}\", r, h); }",
        },
        Case {
            name: "move_then_fn_once",
            opts: BOTH,
            body: "#[inline(never)]
fn outer<F: FnMut(u64) -> u64>(mut f: F, n: u64) -> u64 { let a = inner(|x| f(x).wrapping_mul(3), n); a.wrapping_mul(10000).wrapping_add(once(f)) }
fn main() { let mut c = 5u64; println!(\"{}\", outer(move |x| { c = c.wrapping_add(x); c }, 4)); }",
        },
        Case {
            name: "reborrowed_again",
            opts: BOTH,
            body: "#[inline(never)]
fn outer<F: FnMut(u64) -> u64>(mut f: F, n: u64) -> u64 { let a = inner(|x| f(x).wrapping_mul(3), n); let b = inner(&mut f, 2); a.wrapping_mul(10000).wrapping_add(b).wrapping_add(f(7)) }
fn main() { let mut c = 5u64; println!(\"{}\", outer(move |x| { c = c.wrapping_add(x); c }, 4)); }",
        },
        Case {
            name: "move_u32_state",
            opts: BOTH,
            body: "#[inline(never)]
fn outer<F: FnMut(u64) -> u64>(mut f: F, n: u64) -> u64 { let a = inner(|x| f(x).wrapping_mul(3), n); a.wrapping_mul(10000).wrapping_add(f(7)) }
fn main() { let mut c = 5u32; println!(\"{}\", outer(move |x| { c = c.wrapping_add(x as u32); c as u64 }, 4)); }",
        },
        Case {
            name: "move_u8_state",
            opts: BOTH,
            body: "#[inline(never)]
fn outer<F: FnMut(u64) -> u64>(mut f: F, n: u64) -> u64 { let a = inner(|x| f(x).wrapping_mul(3), n); a.wrapping_mul(10000).wrapping_add(f(7)) }
fn main() { let mut c = 5u8; println!(\"{}\", outer(move |x| { c = c.wrapping_add(x as u8); c as u64 }, 4)); }",
        },
        Case {
            name: "local_move_closure",
            opts: O0_ONLY,
            body: "#[inline(never)]
fn run(n: u64) -> u64 { let mut c = 5u64; let mut f = move |x: u64| { c = c.wrapping_add(x); c }; let a = inner(|x| f(x).wrapping_mul(3), n); a.wrapping_mul(10000).wrapping_add(once(f)) }
fn main() { println!(\"{}\", run(4)); }",
        },
        Case {
            name: "maybe_uninit_capture",
            opts: O0_ONLY,
            body: "use std::mem::MaybeUninit;
#[inline(never)]
fn run(n: u64) -> u64 { let mut m = MaybeUninit::<u64>::new(5); let p = &raw mut m; unsafe { *(p as *mut u64) += 1; } let a = inner(|x| unsafe { let q = m.as_mut_ptr(); *q = (*q).wrapping_add(x); *q }, n); a.wrapping_mul(1000).wrapping_add(unsafe { m.assume_init() }) }
fn main() { println!(\"{}\", run(4)); }",
        },
        // --- controls: one home already, must keep matching ---
        Case {
            name: "control_zero_captures",
            opts: BOTH,
            body: "#[inline(never)]
fn outer<F: FnMut(u64) -> u64>(mut f: F, n: u64) -> u64 { inner(|x| f(x).wrapping_mul(3), n) }
fn main() { let r = outer(|x| x.wrapping_add(7), 4); println!(\"{}\", r); }",
        },
        Case {
            name: "control_two_captures",
            opts: BOTH,
            body: "#[inline(never)]
fn outer<F: FnMut(u64) -> u64>(mut f: F, n: u64) -> u64 { inner(|x| f(x).wrapping_mul(3), n) }
fn main() { let mut h = 5u64; let k = 100u64; let r = outer(|x| { h = h.wrapping_add(x); h.wrapping_add(k) }, 4); println!(\"{} {}\", r, h); }",
        },
        Case {
            name: "control_scalar_param",
            opts: BOTH,
            body: "#[inline(never)]
fn outer(mut v: u64, n: u64) -> u64 { let a = inner(|x| { v = v.wrapping_add(x); v }, n); a.wrapping_mul(1000).wrapping_add(v) }
fn main() { println!(\"{}\", outer(5, 4)); }",
        },
        Case {
            name: "control_tuple_param",
            opts: BOTH,
            body: "#[inline(never)]
fn outer(mut v: (u64, u64), n: u64) -> u64 { let a = inner(|x| { v.0 = v.0.wrapping_add(x); v.1 = v.1.wrapping_mul(2); v.0.wrapping_add(v.1) }, n); a.wrapping_mul(1000).wrapping_add(v.0).wrapping_add(v.1) }
fn main() { println!(\"{}\", outer((5, 3), 4)); }",
        },
    ]
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_one_home_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile `src` at `-Copt-level=<opt>` (with the bridge when `backend` is
/// `Some`), run it, and return `(status, stdout)`, where the status spells a
/// signal death as `signal N`. `Err` carries the compiler's stderr.
fn compile_and_run(
    dir: &Path,
    name: &str,
    src: &str,
    opt: &str,
    backend: Option<&Path>,
) -> Result<(String, String), String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "-Cpanic=abort", "-Ccodegen-units=1"]);
    cmd.arg(format!("-Copt-level={opt}"));
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.arg("-o").arg(&bin).arg(&src_path);
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    let run = Command::new(&bin).output().expect("run compiled binary");
    let status = match (run.status.code(), run.status.signal()) {
        (Some(code), _) => format!("exit {code}"),
        (None, Some(signal)) => format!("signal {signal}"),
        (None, None) => "unknown status".to_owned(),
    };
    Ok((status, String::from_utf8_lossy(&run.stdout).into_owned()))
}

#[test]
fn a_local_with_a_slot_and_a_cell_has_one_home() {
    if toolchain_support::skip_without_backend_knobs("a_local_with_a_slot_and_a_cell_has_one_home")
    {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let mut failures: Vec<String> = Vec::new();
    for case in cases() {
        let src = format!("{PRELUDE}{}\n", case.body);
        for opt in case.opts {
            let dir = workdir(&format!("{}_o{opt}", case.name));
            let oracle = compile_and_run(&dir, case.name, &src, opt, None).unwrap_or_else(|e| {
                panic!(
                    "{} (O{opt}): the LLVM oracle failed to compile: <<<{e}>>>",
                    case.name
                )
            });
            match compile_and_run(&dir, case.name, &src, opt, Some(&dylib)) {
                Ok(bridge) if bridge == oracle => {}
                Ok(bridge) => failures.push(format!(
                    "{} (O{opt}): LLVM {:?} / {:?}, trust-cg {:?} / {:?}",
                    case.name, oracle.0, oracle.1, bridge.0, bridge.1
                )),
                Err(stderr) => {
                    let first = stderr
                        .lines()
                        .find(|line| line.contains("[TCG-") || line.starts_with("error"))
                        .unwrap_or("<no diagnostic>");
                    failures.push(format!(
                        "{} (O{opt}): trust-cg refused a row that must compile: {first}",
                        case.name
                    ));
                }
            }
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
    assert!(
        failures.is_empty(),
        "{} row(s) differ from LLVM or were refused:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}
