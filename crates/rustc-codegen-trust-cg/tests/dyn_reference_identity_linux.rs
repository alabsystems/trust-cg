//! Shared trait-object unsizing must preserve the concrete referent address
//! and interior writes. LLVM-built callers supply canonical storage; local
//! scalarized references without a real home must refuse instead of copying.
//! Native diagnostic differentials are testing evidence without certificates.
#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
const TARGET: &str = "aarch64-unknown-linux-gnu";
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

const FIXTURE: &str = r#"
use std::cell::UnsafeCell;
#[repr(transparent)] pub struct Counter { pub value: UnsafeCell<u64> }
pub trait Read { fn get(&self) -> u64; fn put(&self, value:u64); }
impl Read for Counter {
 #[inline(never)] fn get(&self)->u64 {unsafe {*self.value.get()}}
 #[inline(never)] fn put(&self,v:u64) {unsafe {*self.value.get()=v;}}
}
#[inline(never)] pub fn view(c:&Counter)->&dyn Read {c}
#[inline(never)] pub fn identity_and_write(c:&Counter,v:u64)->u64 {
 let a=view(c); let b=view(c);
 let aa=a as *const dyn Read as *const () as usize;
 let bb=b as *const dyn Read as *const () as usize;
 let cc=c as *const Counter as usize;
 a.put(v);
 ((aa==cc) as u64) | (((bb==cc) as u64)<<1) | (((aa==bb) as u64)<<2)
 | (((a.get()==v) as u64)<<3) | (((b.get()==v) as u64)<<4)
 | (((unsafe{*c.value.get()}==v) as u64)<<5)
}
"#;
const DRIVER: &str = r#"extern crate fixture;
use fixture::*;
fn main() {
 for k in [0u64,1,41,0x1234_5678_9abc_def0,u64::MAX] {
  let c=Counter {value:std::cell::UnsafeCell::new(k)};
  assert_eq!(identity_and_write(&c,k^0x5555),63);
  // repr(transparent) preserves the UnsafeCell storage at offset zero.
  // Read the original allocation without a projected borrow of the wrapper.
  let visible=unsafe{*(std::ptr::addr_of!(c) as *const u64)};
  assert_eq!(visible,k^0x5555);
  println!("ok");
 }
}"#;
const LOCAL: &str = r#"
use std::hint::black_box;
pub trait Read {fn get(&self)->u64;}
impl Read for u64 {#[inline(never)] fn get(&self)->u64 {*self}}
#[inline(never)] fn same(a:&dyn Read,b:&dyn Read)->bool {
 let a=black_box(a as *const dyn Read as *const () as usize);
 let b=black_box(b as *const dyn Read as *const () as usize); a==b
}
#[inline(never)] pub fn local_identity(k:u64)->bool {
 let n=black_box(k);let a:&dyn Read=&n;let b:&dyn Read=&n;same(a,b)
}
"#;
const LOCAL_DRIVER: &str = r#"extern crate fixture;
fn main(){for k in [0,1,41,u64::MAX] {assert!(fixture::local_identity(k));}println!("ok");}"#;
fn artifacts() -> PathBuf {
    let out = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-dyn-identity.XXXXXX"])
        .output()
        .unwrap();
    assert!(out.status.success());
    PathBuf::from(String::from_utf8(out.stdout).unwrap().trim())
}
#[test]
fn dyn_reference_identity_and_interior_writes_across_backends() {
    assert!(toolchain_support::backend_knobs_supported());
    let dir = artifacts();
    eprintln!("dyn identity artifacts: {}", dir.display());
    let backend = backend_artifact_support::current_test_backend();
    std::fs::write(dir.join("fixture.rs"), FIXTURE).unwrap();
    std::fs::write(dir.join("driver.rs"), DRIVER).unwrap();
    for opt in 0..=3 {
        let llvm = build_fixture(&dir, opt, None);
        let cg = build_fixture(&dir, opt, Some(&backend));
        let expected = run_lane(
            &dir,
            &format!("llvm_llvm_O{opt}"),
            "driver.rs",
            opt,
            None,
            &llvm,
            5,
        );
        for (fixture, rlib) in [("llvm", &llvm), ("cg", &cg)] {
            for (driver, selected) in [("llvm", None), ("cg", Some(backend.as_path()))] {
                if fixture == "llvm" && driver == "llvm" {
                    continue;
                }
                let lane = format!("{fixture}_{driver}_O{opt}");
                assert_eq!(
                    run_lane(&dir, &lane, "driver.rs", opt, selected, rlib, 5),
                    expected,
                    "{lane}"
                );
            }
        }
    }
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn local_dyn_snapshot_refuses_or_preserves_identity_at_every_optimization_level() {
    assert!(toolchain_support::backend_knobs_supported());
    let dir = artifacts();
    eprintln!("local dyn artifacts: {}", dir.display());
    let backend = backend_artifact_support::current_test_backend();
    std::fs::write(dir.join("fixture.rs"), LOCAL).unwrap();
    std::fs::write(dir.join("driver.rs"), LOCAL_DRIVER).unwrap();
    for opt in 0..=3 {
        let llvm = build_fixture(&dir, opt, None);
        assert_eq!(
            run_lane(
                &dir,
                &format!("oracle_O{opt}"),
                "driver.rs",
                opt,
                None,
                &llvm,
                1
            ),
            "ok\n"
        );
        let cell = dir.join(format!("local_cg_O{opt}"));
        std::fs::create_dir(&cell).unwrap();
        let rlib = cell.join("libfixture.rlib");
        let mut command = rustc_for(Some(&backend), opt);
        command
            .args(["--crate-type", "rlib", "--crate-name", "fixture"])
            .arg("-o")
            .arg(&rlib)
            .arg(dir.join("fixture.rs"));
        let (out, text) = run_bounded(&mut command, 300, &cell.join("compile.log"));
        if out.status.success() {
            assert_eq!(
                run_lane(
                    &dir,
                    &format!("admitted_O{opt}"),
                    "driver.rs",
                    opt,
                    None,
                    &rlib,
                    1
                ),
                "ok\n"
            );
        } else {
            assert!(
                text.contains("[TCG-DYN-REF-IDENTITY]"),
                "O{opt}: local reference must refuse at the identity boundary: {text}"
            );
            assert!(!rlib.exists());
        }
    }
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn ordinary_main_retains_lang_start_after_fn_shim_refusal() {
    assert!(toolchain_support::backend_knobs_supported());
    let dir = artifacts();
    let backend = backend_artifact_support::current_test_backend();
    std::fs::write(dir.join("main.rs"),"#[inline(never)]fn f(x:u64)->u64{x+1} fn main(){assert_eq!(f(std::hint::black_box(41)),42);println!(\"ok\");}").unwrap();
    for opt in 0..=3 {
        let cell = dir.join(format!("main_O{opt}"));
        std::fs::create_dir(&cell).unwrap();
        let bin = cell.join("main.elf");
        let mut command = rustc_for(Some(&backend), opt);
        command.arg("-o").arg(&bin).arg(dir.join("main.rs"));
        let (out, text) = run_bounded(&mut command, 300, &cell.join("compile.log"));
        assert!(out.status.success(), "{text}");
        let (out, text) = run_bounded(&mut Command::new(&bin), 60, &cell.join("run.log"));
        assert!(out.status.success(), "{text}");
        assert_eq!(String::from_utf8(out.stdout).unwrap(), "ok\n");
    }
    std::fs::remove_dir_all(dir).unwrap();
}
