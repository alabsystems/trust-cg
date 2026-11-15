//! Linux AArch64 cross-backend closure-return regressions; `rust-call` and
//! by-value closure-environment shapes the bridge lowers on rustc's convention
//! (every rlib x driver cell must agree); and independently executable controls
//! for the shapes here the bridge still refuses by name.
//! Diagnostic emission uses the tracked no-proof-certs option; no proof claim.
#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
const TARGET: &str = "aarch64-unknown-linux-gnu";
/// The float-pair closure-return lanes run at O0, O2 and O3: rustc inlines and
/// specializes differently at O3 than at O2.
const OPT_LEVELS: [u32; 3] = [0, 2, 3];
const KEEP_ARTIFACTS: &str = "RUST_CALL_SHIMS_LINUX_KEEP_ARTIFACTS";
fn run_bounded(command: &mut Command, seconds: u32, log: &Path) -> (Output, String) {
    let mut bounded = Command::new("timeout");
    bounded.args(["--kill-after=5", &seconds.to_string()]);
    bounded.arg(command.get_program()).args(command.get_args());
    for (key, value) in command.get_envs() {
        if let Some(value) = value {
            bounded.env(key, value);
        } else {
            bounded.env_remove(key);
        }
    }
    let output = bounded.output().expect("execute bounded native step");
    let transcript = format!(
        "command: {command:?}\nstatus: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::write(log, &transcript).expect("retain complete step log");
    (output, transcript)
}

/// A rustc invocation for `backend` (`None` is LLVM) at `opt`.
fn rustc_for(backend: Option<&Path>, opt: u32) -> Command {
    let mut command = toolchain_support::rustc_command();
    if let Some(backend) = backend {
        command.arg(format!("-Zcodegen-backend={}", backend.display()));
        command.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    command
        .args(["-Ccodegen-units=1", "-Cpanic=abort", "--target", TARGET])
        .arg(format!("-Copt-level={opt}"));
    command
}

fn compiler_name(backend: Option<&Path>) -> &'static str {
    if backend.is_some() { "cg" } else { "llvm" }
}

/// Compile the fixture rlib with `backend` at `opt`.
fn build_fixture(artifacts: &Path, opt: u32, backend: Option<&Path>) -> PathBuf {
    let dir = artifacts.join(format!("fixture_{}_O{opt}", compiler_name(backend)));
    std::fs::create_dir(&dir).unwrap();
    let rlib = dir.join("libfixture.rlib");
    let mut command = rustc_for(backend, opt);
    command
        .args(["--crate-type", "rlib", "--crate-name", "fixture"])
        .arg("-o")
        .arg(&rlib)
        .arg(artifacts.join("fixture.rs"));
    let (output, transcript) = run_bounded(&mut command, 600, &dir.join("compile.log"));
    assert!(
        output.status.success(),
        "{} O{opt}: the fixture did not compile: {transcript}",
        compiler_name(backend)
    );
    rlib
}

/// Compile `source` as a binary with `backend` against `rlib`; returns the
/// compile's output and transcript, and the executable's path.
fn build_driver(
    artifacts: &Path,
    lane: &str,
    source: &str,
    opt: u32,
    backend: Option<&Path>,
    rlib: &Path,
) -> (Output, String, PathBuf) {
    let dir = artifacts.join(lane);
    std::fs::create_dir(&dir).unwrap();
    let executable = dir.join("driver.elf");
    let mut command = rustc_for(backend, opt);
    command
        .arg("--extern")
        .arg(format!("fixture={}", rlib.display()))
        .arg("-o")
        .arg(&executable)
        .arg(artifacts.join(source));
    let (output, transcript) = run_bounded(&mut command, 600, &dir.join("compile.log"));
    (output, transcript, executable)
}

/// Build and run one driver lane; returns its stdout.
fn run_lane(
    artifacts: &Path,
    lane: &str,
    source: &str,
    opt: u32,
    backend: Option<&Path>,
    rlib: &Path,
    lines: usize,
) -> String {
    let (output, transcript, executable) =
        build_driver(artifacts, lane, source, opt, backend, rlib);
    assert!(
        output.status.success(),
        "{lane}: the driver did not compile: {transcript}"
    );
    let (run, transcript) = run_bounded(
        &mut Command::new(&executable),
        60,
        &artifacts.join(lane).join("run.log"),
    );
    assert_eq!(
        run.status.code(),
        Some(0),
        "{lane}: the program failed: {transcript}"
    );
    let stdout = String::from_utf8(run.stdout).expect("driver output");
    assert_eq!(stdout.lines().count(), lines, "{lane}: {stdout}");
    stdout
}

const FLOAT_FIXTURE: &str = r#"
use std::hint::black_box as bb;
#[derive(Clone, Copy)] #[repr(C)] pub struct D2 { pub a: f64, pub b: f64 }
#[inline(never)] pub fn direct64(k: u64) -> (f64, f64) {
    let c = |x: u64| ((x + k) as f64, -2.25); c(bb(k + 1))
}
#[inline(never)] pub fn direct32(k: u64) -> (f32, f32) {
    let c = |x: u64| ((x * k) as f32, -1.5); c(bb(k + 1))
}
#[inline(never)] pub fn direct_struct(k: u64) -> D2 {
    let c = |x: u64| D2 { a: (x ^ k) as f64, b: 0.25 }; c(bb(k + 1))
}
#[inline(never)] pub fn apply64<F: Fn(u64) -> (f64, f64)>(c: &F, x: u64) -> (f64, f64) { c(x) }
#[inline(never)] pub fn generic64(k: u64) -> (f64, f64) {
    let c = |x: u64| ((x + k * 3) as f64, 7.5); apply64(&c, bb(k + 1))
}
// `move` closures, including the round-4 L06-P14/P15/P16 report's shapes. The
// rust-call rewrite `483974058` refused these and the by-reference closures above
// with an internal [TCG-IR-LOWER] `ExtractField` type error; the `9e6ff1714`
// merge archived its code instead of taking it. A bridge trace shows every
// one-argument closure call here taking the closure `PassMode::Pair` return of
// `finish_closure_call_aggregate_return`.
#[derive(Clone, Copy)] pub struct F2 { pub a: f32, pub b: f32 }
pub struct Nc(pub u64, pub f64);
#[inline(never)] pub fn move64(k: u64) -> (f64, f64) {
    let c = move |x: u64| -> (f64, f64) { ((x ^ k) as f64, 7.5) }; c(k + 1)
}
#[inline(never)] pub fn move32(k: u64) -> (f32, f32) {
    let c = move |x: u64| ((x ^ k) as f32, 7.5f32); c(k + 1)
}
#[inline(never)] pub fn move_struct(k: u64) -> D2 {
    let c = move |x: u64| -> D2 { D2 { a: (x ^ k) as f64, b: 7.5 } }; c(k + 1)
}
#[inline(never)] pub fn move_rust_struct(k: u64) -> F2 {
    let c = move |x: u64| F2 { a: (x ^ k) as f32, b: -0.75 }; c(k + 1)
}
#[inline(never)] pub fn move_float_env(a: f64, b: f64) -> (f64, f64) {
    let c = move |x: u64| (a + x as f64, b - x as f64); c(bb(3))
}
#[inline(never)] pub fn fn_mut64(k: u64) -> (f64, f64) {
    let mut acc = k;
    let mut c = move |x: u64| { acc = acc.wrapping_mul(3) ^ x; (acc as f64, 0.5) };
    let _ = c(1);
    c(k)
}
#[inline(never)] pub fn once64<F: FnOnce(u64) -> (f64, f64)>(f: F, x: u64) -> (f64, f64) { f(x) }
#[inline(never)] pub fn fn_once64(k: u64) -> (f64, f64) {
    let n = Nc(k, 0.5);
    let c = move |x: u64| -> (f64, f64) { let m = n; (m.0 as f64 + x as f64, m.1) };
    once64(c, k)
}
#[inline(never)] pub fn apply32<F: Fn(u64) -> (f32, f32)>(f: F, x: u64) -> (f32, f32) { f(x) }
#[inline(never)] pub fn generic_move32(k: u64) -> (f32, f32) {
    let c = move |x: u64| ((x + k) as f32, 0.5f32); apply32(c, k)
}
#[inline(never)] pub fn dyn32(f: &dyn Fn(u64) -> (f32, f32), x: u64) -> (f32, f32) { f(x) }
#[inline(never)] pub fn dyn64(f: &dyn Fn(u64) -> (f64, f64), x: u64) -> (f64, f64) { f(x) }
#[inline(never)] pub fn dyn_move32(k: u64) -> (f32, f32) {
    let d = move |x: u64| ((x * k) as f32, -1.5f32); dyn32(&d, k)
}
pub fn make_box64(k: u64) -> Box<dyn Fn(u64) -> (f64, f64)> { Box::new(move |x| ((x * k) as f64, -1.5)) }
pub fn make_impl32(k: u64) -> impl Fn(u64) -> (f32, f32) { move |x| ((x + k) as f32, 3.25) }
// Capturing zero-argument closures. A bridge trace shows each of these calls
// taking the float-carrier `hfa_return` return of
// `finish_closure_call_aggregate_return`, not the `PassMode::Pair` return the
// one-argument closures above take.
#[inline(never)] pub fn zero64(k: u64) -> (f64, f64) { let c = move || ((k ^ 3) as f64, 7.5); c() }
#[inline(never)] pub fn zero32(k: u64) -> (f32, f32) { let c = move || ((k * 3) as f32, -0.25f32); c() }
#[inline(never)] pub fn zero_ref64(k: u64) -> (f64, f64) { let c = || ((k + 9) as f64, 0.125); c() }
#[inline(never)] pub fn zero_struct(k: u64) -> D2 { let c = move || D2 { a: (k + 2) as f64, b: -4.5 }; c() }
#[inline(never)] pub fn zero_rust_struct(k: u64) -> F2 { let c = move || F2 { a: (k + 5) as f32, b: 1.75 }; c() }
#[inline(never)] pub fn zero_mut64(k: u64) -> (f64, f64) {
    let mut n = k;
    let mut c = move || { n = n * 3 + 1; (n as f64, -1.0) };
    let _ = c();
    c()
}
#[inline(never)] pub fn applyz<F: Fn() -> (f64, f64)>(f: F) -> (f64, f64) { f() }
#[inline(never)] pub fn zero_generic(k: u64) -> (f64, f64) { applyz(move || ((k << 1) as f64, 2.0)) }
#[inline(never)] pub fn dynz(f: &dyn Fn() -> (f64, f64)) -> (f64, f64) { f() }
#[inline(never)] pub fn zero_dyn(k: u64) -> (f64, f64) { let c = move || ((k + 11) as f64, 3.0); dynz(&c) }
pub fn make_zero_impl(k: u64) -> impl Fn() -> (f32, f32) { move || ((k + 1) as f32, 0.5) }
"#;
/// The float driver prints one line per `k` for the four by-reference lanes
/// and one per `k` for each of the 24 `chk64` / `chk32` lanes.
const FLOAT_LINES: usize = 5 * (1 + 24);
const FLOAT_DRIVER: &str = r#"extern crate fixture;
use fixture::*;
// Print one lane's bits under its number, then require the value the source
// computes. (A lane number, not a name: the bridge refuses a runtime-length
// `&str` format argument, [TCG-FMT-RTSTR].)
#[inline(never)] fn chk64(k: u64, lane: u32, got: (f64, f64), want: (f64, f64)) {
    println!("{k} {lane} {} {}", got.0.to_bits(), got.1.to_bits());
    assert_eq!(got.0.to_bits(), want.0.to_bits());
    assert_eq!(got.1.to_bits(), want.1.to_bits());
}
#[inline(never)] fn chk32(k: u64, lane: u32, got: (f32, f32), want: (f32, f32)) {
    println!("{k} {lane} {} {}", got.0.to_bits(), got.1.to_bits());
    assert_eq!(got.0.to_bits(), want.0.to_bits());
    assert_eq!(got.1.to_bits(), want.1.to_bits());
}
#[inline(never)] fn call_box(b: &Box<dyn Fn(u64) -> (f64, f64)>, x: u64) -> (f64, f64) { b(x) }
fn main() {
    for k in [0, 1, 17, 41, 1001] {
        let a = direct64(k); assert_eq!(a.0.to_bits(), ((2*k+1) as f64).to_bits()); assert_eq!(a.1.to_bits(), (-2.25f64).to_bits());
        let b = direct32(k); assert_eq!(b.0.to_bits(), ((k*(k+1)) as f32).to_bits()); assert_eq!(b.1.to_bits(), (-1.5f32).to_bits());
        let c = direct_struct(k); assert_eq!(c.a.to_bits(), (((k+1)^k) as f64).to_bits()); assert_eq!(c.b.to_bits(), 0.25f64.to_bits());
        let d = generic64(k); assert_eq!(d.0.to_bits(), ((4*k+1) as f64).to_bits()); assert_eq!(d.1.to_bits(), 7.5f64.to_bits());
        println!("{k} {} {} {} {}", a.0.to_bits(), b.0.to_bits(), c.a.to_bits(), d.0.to_bits());
        chk64(k, 1, move64(k), (((k+1)^k) as f64, 7.5));
        chk32(k, 2, move32(k), (((k+1)^k) as f32, 7.5));
        let s = move_struct(k);
        chk64(k, 3, (s.a, s.b), (((k+1)^k) as f64, 7.5));
        let r = move_rust_struct(k);
        chk32(k, 4, (r.a, r.b), (((k+1)^k) as f32, -0.75));
        chk64(k, 5, move_float_env(k as f64, 0.5), (k as f64 + 3.0, -2.5));
        chk64(k, 6, fn_mut64(k), (((k.wrapping_mul(3) ^ 1).wrapping_mul(3) ^ k) as f64, 0.5));
        chk64(k, 7, fn_once64(k), (k as f64 + k as f64, 0.5));
        chk32(k, 8, generic_move32(k), ((2*k) as f32, 0.5));
        chk32(k, 9, dyn_move32(k), ((k*k) as f32, -1.5));
        // This crate's closures through the library's `&dyn Fn` and generic.
        let e = move |x: u64| ((x ^ k) as f64, 0.25f64);
        chk64(k, 10, dyn64(&e, k + 5), (((k+5)^k) as f64, 0.25));
        let f = move |x: u64| ((x + 2*k) as f32, -0.5f32);
        chk32(k, 11, apply32(f, k), ((3*k) as f32, -0.5));
        // The library's closures called here.
        let g = make_box64(k);
        chk64(k, 12, call_box(&g, k + 2), (((k+2)*k) as f64, -1.5));
        let h = make_impl32(k);
        chk32(k, 13, h(k + 3), ((2*k+3) as f32, 3.25));
        // Zero-argument closures (the float-carrier return lane).
        chk64(k, 14, zero64(k), ((k ^ 3) as f64, 7.5));
        chk32(k, 15, zero32(k), ((k * 3) as f32, -0.25));
        chk64(k, 16, zero_ref64(k), ((k + 9) as f64, 0.125));
        let t = zero_struct(k);
        chk64(k, 17, (t.a, t.b), ((k + 2) as f64, -4.5));
        let u = zero_rust_struct(k);
        chk32(k, 18, (u.a, u.b), ((k + 5) as f32, 1.75));
        chk64(k, 19, zero_mut64(k), (((k * 3 + 1) * 3 + 1) as f64, -1.0));
        chk64(k, 20, zero_generic(k), ((k << 1) as f64, 2.0));
        chk64(k, 21, zero_dyn(k), ((k + 11) as f64, 3.0));
        let i = make_zero_impl(k);
        chk32(k, 22, i(), ((k + 1) as f32, 0.5));
        let l = move || ((k * 7) as f64, -8.0);
        chk64(k, 23, dynz(&l), ((k * 7) as f64, -8.0));
        chk64(k, 24, applyz(move || ((k + 100) as f64, 9.0)), ((k + 100) as f64, 9.0));
    }
}
"#;
fn artifacts(prefix: &str) -> PathBuf {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", prefix])
        .output()
        .expect("mktemp");
    assert!(temp.status.success());
    PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim())
}
fn cleanup(path: &Path) {
    if std::env::var_os(KEEP_ARTIFACTS).is_some_and(|value| value == "1") {
        eprintln!("retained artifacts: {}", path.display());
    } else {
        std::fs::remove_dir_all(path).unwrap();
    }
}
#[test]
fn closure_float_return_carriers_cross_backend_linux() {
    assert!(
        toolchain_support::backend_knobs_supported(),
        "test compiler must support tracked backend knobs"
    );
    let dir = artifacts("trust-cg-closure-float.XXXXXX");
    eprintln!("closure float artifacts: {}", dir.display());
    let backend = backend_artifact_support::current_test_backend();
    std::fs::write(dir.join("fixture.rs"), FLOAT_FIXTURE).unwrap();
    std::fs::write(dir.join("driver.rs"), FLOAT_DRIVER).unwrap();
    for opt in OPT_LEVELS {
        let llvm = build_fixture(&dir, opt, None);
        let cg = build_fixture(&dir, opt, Some(&backend));
        let expected = run_lane(
            &dir,
            &format!("llvm_llvm_O{opt}"),
            "driver.rs",
            opt,
            None,
            &llvm,
            FLOAT_LINES,
        );
        for (fixture, rlib) in [("llvm", &llvm), ("cg", &cg)] {
            for (driver, selected) in [("llvm", None), ("cg", Some(backend.as_path()))] {
                if fixture == "llvm" && driver == "llvm" {
                    continue;
                }
                let lane = format!("{fixture}_{driver}_O{opt}");
                assert_eq!(
                    run_lane(&dir, &lane, "driver.rs", opt, selected, rlib, FLOAT_LINES),
                    expected,
                    "{lane}"
                );
            }
        }
    }
    cleanup(&dir);
}
/// A shape the bridge USED to refuse by name and now lowers on rustc's own
/// convention: every rlib x driver cell (LLVM or bridge on either side) must
/// compile and print `ok` (the driver asserts the values). The first two are a
/// `Box<dyn Fn*>` over a fn ITEM, whose vtable slot is the `FnPtrShim` the bridge
/// declared with its argument TUPLE as one parameter (refused at the vtable,
/// "UNTUPLED"); `exported_rust_call_item` is an exported `extern "rust-call"`
/// fn (refused "BY SYMBOL"). Since round 10's F2 every `rust-call` callable is
/// declared with the tuple's elements, as rustc's `FnAbi` lists them
/// (`rust_call_spread`). `shared_fn_once_environment` is an exported `FnOnce`
/// closure body whose by-value environment rustc passes as an ordinary argument
/// (refused "BY VALUE ... environment ... EXPORTS" until round 10's F-env
/// declared it by rustc's own mode). MEASURED 2026-09-30 with the same fixtures
/// and drivers on aarch64-apple-darwin (the host lane, F2's dylib): every cell
/// `ok` at O0 and O2, where the round's pre-F2 dylib refused the vtable and
/// symbol rows by name. `fn_item_float_pair_vtable` is a `&dyn Fn(u64) -> (f64,
/// f64)` over a fn item: while the shim was declared tupled the slot held a
/// spread entry admitted only for scalar and thin-pointer elements and returns
/// (`[TCG-FN-DYN-ENTRY]`, pinned here from 2026-10-02); the vtable now holds the
/// untupled `FnPtrShim` itself. All five re-measured 2026-10-08 on
/// aarch64-apple-darwin with this merge's dylib (the same fixtures and drivers,
/// `-Cpanic=abort`, one codegen unit): every cell `ok` at each row's levels.
/// Not run on a Linux AArch64 host for this merge.
struct AgreeCase {
    name: &'static str,
    fixture: &'static str,
    driver: &'static str,
    opts: &'static [u32],
}
const AGREES: &[AgreeCase] = &[
    AgreeCase {
        name: "three_register_vtable",
        fixture: "#[inline(never)] pub fn f(a:u64,b:u64,c:u64)->u64 {a+b*3+c*5} pub fn make()->Box<dyn Fn(u64,u64,u64)->u64> {Box::new(f)}",
        driver: "fn main(){assert_eq!(fixture::make()(1,2,3),22);println!(\"ok\");}",
        opts: &[0, 2],
    },
    AgreeCase {
        name: "byref_array_vtable",
        fixture: "#[inline(never)] pub fn f(a:[f32;4])->f32 {a[0]+a[1]*2.0+a[2]*3.0+a[3]*4.0} pub fn make()->Box<dyn Fn([f32;4])->f32> {Box::new(f)}",
        driver: "fn main(){assert_eq!(fixture::make()([1.0,2.0,3.0,4.0]),30.0);println!(\"ok\");}",
        opts: &[0, 2],
    },
    AgreeCase {
        name: "shared_fn_once_environment",
        fixture: "pub struct Nc(pub u64); #[inline(never)] fn consume(n:Nc)->u64 {n.0} pub fn make(k:u64)->impl FnOnce(u64)->u64 {let n=Nc(k);move |x| x+consume(n)} pub fn inside(k:u64,x:u64)->u64 {make(k)(x)}",
        driver: "fn main(){assert_eq!(fixture::make(11)(7),18);assert_eq!(fixture::inside(11,7),18);println!(\"ok\");}",
        opts: &[0],
    },
    AgreeCase {
        name: "exported_rust_call_item",
        fixture: "#![feature(unboxed_closures)] #[inline(never)] pub extern \"rust-call\" fn rc(t:(u64,u64,u64))->u64 {t.0+t.1*3+t.2*5}",
        driver: "fn main(){assert_eq!(fixture::rc((1,2,3)),22);println!(\"ok\");}",
        opts: &[0, 2],
    },
    AgreeCase {
        name: "fn_item_float_pair_vtable",
        fixture: "#[inline(never)] pub fn item(k:u64)->(f64,f64) {(k as f64,2.5)} #[inline(never)] pub fn call(f:&dyn Fn(u64)->(f64,f64),k:u64)->(f64,f64) {f(k)} pub fn run(k:u64)->(f64,f64) {call(&item,k)}",
        driver: "fn main(){let r=fixture::run(41);assert_eq!((r.0.to_bits(),r.1.to_bits()),(41f64.to_bits(),2.5f64.to_bits()));println!(\"ok\");}",
        opts: &[0, 2, 3],
    },
];
#[test]
fn rust_call_shapes_agree_across_backends_linux() {
    assert!(
        toolchain_support::backend_knobs_supported(),
        "test compiler must support tracked backend knobs"
    );
    let dir = artifacts("trust-cg-rust-call-agree.XXXXXX");
    eprintln!("rust-call agreement artifacts: {}", dir.display());
    let backend = backend_artifact_support::current_test_backend();
    for case in AGREES {
        let cell = dir.join(case.name);
        std::fs::create_dir(&cell).unwrap();
        std::fs::write(cell.join("fixture.rs"), case.fixture).unwrap();
        std::fs::write(
            cell.join("driver.rs"),
            format!("extern crate fixture; {}", case.driver),
        )
        .unwrap();
        for &opt in case.opts {
            let llvm = build_fixture(&cell, opt, None);
            let cg = build_fixture(&cell, opt, Some(&backend));
            for (fixture, rlib) in [("llvm", &llvm), ("cg", &cg)] {
                for (driver, selected) in [("llvm", None), ("cg", Some(backend.as_path()))] {
                    let lane = format!("{fixture}_{driver}_O{opt}");
                    assert_eq!(
                        run_lane(&cell, &lane, "driver.rs", opt, selected, rlib, 1),
                        "ok\n",
                        "{} {lane}",
                        case.name
                    );
                }
            }
        }
    }
    cleanup(&dir);
}
struct RefusalCase {
    name: &'static str,
    fixture: &'static str,
    driver: &'static str,
    diagnostic: &'static [&'static str],
    opts: &'static [u32],
}
/// Shapes the bridge refuses by name, each beside its LLVM x LLVM control:
/// a `Box<dyn FnOnce>` over a capturing closure (the vtable's `call_once` shim
/// moves the closure out of its box, which the bridge does not lower: a
/// reachable trapping stub, refused); a non-capturing closure coerced to `fn(u64)
/// -> (f64, f64)` (its module-local fn-pointer entry, `closure_fn_pointer_entry`,
/// does not forward a float-pair carrier plan, `[TCG-CLOSURE-FNPTR]`); and a
/// `[f64; 2]` returned through a `&dyn Fn` (an indirect return at an indirect
/// call, `[TCG-SRET-ABI]`). None is an argument-placement question; each stays
/// refused after F2 (re-measured 2026-10-08 on aarch64-apple-darwin with the
/// same fixtures: the bridge-built rlib is refused with these texts at every
/// listed level).
const REFUSALS: &[RefusalCase] = &[
    RefusalCase {
        name: "boxed_fn_once_vtable",
        fixture: "pub fn make(k:u64)->Box<dyn FnOnce(u64)->u64> {Box::new(move |x| k+x)}",
        driver: "fn main(){assert_eq!(fixture::make(11)(7),18);println!(\"ok\");}",
        diagnostic: &[
            "[TCG-MIR-UNSUPPORTED]",
            "vtable shim",
            "reachable trapping stub",
        ],
        opts: &[0, 2],
    },
    RefusalCase {
        name: "closure_float_pair_fn_pointer",
        fixture: "#[inline(never)] pub fn fp64()->fn(u64)->(f64,f64) {|x| (x as f64,2.5)} pub fn run(k:u64)->(f64,f64) {fp64()(k)}",
        driver: "fn main(){let r=fixture::run(41);assert_eq!((r.0.to_bits(),r.1.to_bits()),(41f64.to_bits(),2.5f64.to_bits()));println!(\"ok\");}",
        diagnostic: &[
            "[TCG-CLOSURE-FNPTR]",
            "fn(..)` pointer to closure",
            "HFA / float-pair carrier plan",
        ],
        opts: &[0, 2, 3],
    },
    RefusalCase {
        name: "closure_array_pair_dyn",
        fixture: "#[inline(never)] pub fn call(f:&dyn Fn(u64)->[f64;2],k:u64)->[f64;2] {f(k)} pub fn run(k:u64)->[f64;2] {let c=move |x:u64| [(x^k) as f64,1.25]; call(&c,k+1)}",
        driver: "fn main(){let r=fixture::run(41);assert_eq!((r[0].to_bits(),r[1].to_bits()),(3f64.to_bits(),1.25f64.to_bits()));println!(\"ok\");}",
        diagnostic: &["[TCG-SRET-ABI]", "[f64; 2_usize]", "INDIRECT call"],
        opts: &[0, 2, 3],
    },
];
#[test]
fn unimplemented_rust_call_shapes_refuse_with_independent_llvm_controls() {
    assert!(
        toolchain_support::backend_knobs_supported(),
        "test compiler must support tracked backend knobs"
    );
    let dir = artifacts("trust-cg-rust-call-refusals.XXXXXX");
    eprintln!("rust-call refusal artifacts: {}", dir.display());
    let backend = backend_artifact_support::current_test_backend();
    for case in REFUSALS {
        let cell = dir.join(case.name);
        std::fs::create_dir(&cell).unwrap();
        std::fs::write(cell.join("fixture.rs"), case.fixture).unwrap();
        std::fs::write(
            cell.join("driver.rs"),
            format!("extern crate fixture; {}", case.driver),
        )
        .unwrap();
        for &opt in case.opts {
            let llvm = build_fixture(&cell, opt, None);
            assert_eq!(
                run_lane(
                    &cell,
                    &format!("oracle_O{opt}"),
                    "driver.rs",
                    opt,
                    None,
                    &llvm,
                    1
                ),
                "ok\n"
            );
            let refused_dir = cell.join(format!("refused_O{opt}"));
            std::fs::create_dir(&refused_dir).unwrap();
            let output_file = refused_dir.join("libfixture.rlib");
            let mut command = rustc_for(Some(&backend), opt);
            command
                .args(["--crate-type", "rlib", "--crate-name", "fixture"])
                .arg("-o")
                .arg(&output_file)
                .arg(cell.join("fixture.rs"));
            let (out, transcript) =
                run_bounded(&mut command, 300, &refused_dir.join("compile.log"));
            assert!(
                !out.status.success(),
                "{} O{opt} must refuse: {transcript}",
                case.name
            );
            for diagnostic in case.diagnostic {
                assert!(
                    transcript.contains(diagnostic),
                    "{} O{opt} missing {diagnostic:?}: {transcript}",
                    case.name
                );
            }
            assert!(
                !output_file.exists(),
                "{} O{opt} emitted a refused artifact",
                case.name
            );
        }
    }
    cleanup(&dir);
}
