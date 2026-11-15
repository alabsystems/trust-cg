#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: Trust-VERIFIED code compiles through the x86-64 bridge and
// executes identically to the same source built by rustc's LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS TEST EXISTS. Every other test in this suite compiles through
// `toolchain_support::rustc_command*`, which passes `-Ztrust-verify=off` on the
// trust channel — the explicit UNVERIFIED frontend lane. That is deliberate and
// documented, but it means the suite had NO coverage of the lane the completion
// objective's "Trust program" clause actually names: source compiled WITH Trust
// verification and lowered by trust-cg. This test is that coverage, and it is the
// first of its kind here, so it builds its command from
// `rustc_driver_command()` and omits the off-switch rather than starting from the
// shared constructor.
//
// WHAT IT PINS. A corpus of 23 `extern "C"` functions that all discharge their
// obligations STATICALLY (Trust's strict mode rejects a retained runtime check),
// spanning 18 shape families: scalar ALU across u32/u64/i32, wrapping
// add/sub/mul, masked shifts, xor, a three-step xorshift, `count_ones`, a
// conditional select, a struct, a tuple, a fixed array, an `Option` niche, a
// 3-variant enum with payloads, a 4-way `match`, a cross-function call, a bounded
// loop, an f64 COMPARISON, an instantiated generic at a `Copy` bound, a `u128`
// multiply, a statically dispatched trait, and `saturating_sub`.
//
// The corpus is compiled TWICE from one source — once through this backend and
// once through the LLVM backend, both with verification ON — each archive is
// linked against the same C driver, and the two binaries must print the SAME
// checksum. A backend divergence is a P0; a frontend refusal shows up in BOTH
// lanes and fails the test as an environment/pin change rather than silently
// passing.
//
// WHAT IS DELIBERATELY ABSENT, because Trust's Level 0 verification refuses it
// and refuses it IDENTICALLY through the LLVM backend (so none of it is a
// trust-cg gap): floating-point ARITHMETIC, generic `T: Add`, slice indexing in a
// loop, `dyn` dispatch, `checked_*`, `rotate_left`, and raw-pointer loops. Adding
// any of them here would pin a frontend limit, not this backend's behaviour.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = host_target_support::X86_64_TARGET;

/// Expected driver checksum. Both lanes must print exactly this.
///
/// It is pinned rather than only compared across lanes so that a change which
/// breaks BOTH lanes the same way — a frontend pin move, a corpus edit — is a
/// failure here instead of a silently agreeing pair.
const EXPECTED_CHECKSUM: &str = "267826962111695130";

const CORPUS: &str = r#"
#[unsafe(no_mangle)] pub extern "C" fn t_add_wrapping(a: u32, b: u32) -> u32 { a.wrapping_add(b) }
#[unsafe(no_mangle)] pub extern "C" fn t_xor(a: u64, b: u64) -> u64 { a ^ b }
#[unsafe(no_mangle)] pub extern "C" fn t_shl_masked(a: u64, s: u32) -> u64 { a << (s & 63) }
#[unsafe(no_mangle)] pub extern "C" fn t_shr_masked(a: u64, s: u32) -> u64 { a >> (s & 63) }
#[unsafe(no_mangle)] pub extern "C" fn t_mul_wrapping(a: u64, b: u64) -> u64 { a.wrapping_mul(b) }
#[unsafe(no_mangle)] pub extern "C" fn t_xorshift(mut x: u64) -> u64 {
    x ^= x << 13; x ^= x >> 7; x ^= x << 17; x
}
#[unsafe(no_mangle)] pub extern "C" fn t_cond_select(a: u64, b: u64, f: u32) -> u64 {
    if f & 1 == 0 { a.wrapping_add(b) } else { a ^ b }
}
pub struct P { pub a: u64, pub b: u64 }
#[unsafe(no_mangle)] pub extern "C" fn s01(a: u64, b: u64) -> u64 { let p = P { a, b }; p.a ^ p.b }
#[unsafe(no_mangle)] pub extern "C" fn s02(a: u64, b: u64) -> u64 { let t = (a, b); t.0.wrapping_add(t.1) }
fn inner(x: u64) -> u64 { x ^ 0x5555 }
#[unsafe(no_mangle)] pub extern "C" fn s03(a: u64) -> u64 { inner(a).wrapping_mul(3) }
#[unsafe(no_mangle)] pub extern "C" fn s04(a: u64) -> u64 {
    let mut acc = a; let mut i = 0u32;
    while i < 8 { acc = acc.wrapping_mul(3).wrapping_add(i as u64); i += 1; }
    acc
}
#[unsafe(no_mangle)] pub extern "C" fn s05(a: u64) -> u64 {
    let t: [u64; 4] = [a, a ^ 1, a ^ 2, a ^ 3];
    t[0] ^ t[1] ^ t[2] ^ t[3]
}
#[unsafe(no_mangle)] pub extern "C" fn s06(a: u64, k: u32) -> u64 {
    match k & 3 { 0 => a.wrapping_add(1), 1 => a ^ 2, 2 => a.wrapping_mul(3), _ => a >> 1 }
}
#[unsafe(no_mangle)] pub extern "C" fn s07(a: i32, b: i32) -> i32 { a.wrapping_sub(b) }
#[unsafe(no_mangle)] pub extern "C" fn s08(a: u64, b: u64) -> u32 { (a > b) as u32 }
#[unsafe(no_mangle)] pub extern "C" fn s09(a: u64, f: u32) -> u64 {
    let o = if f & 1 == 0 { Some(a) } else { None };
    match o { Some(v) => v ^ 7, None => 0 }
}
#[unsafe(no_mangle)] pub extern "C" fn s10(a: u64) -> u64 {
    let mut x = a; x ^= x << 13; x ^= x >> 7; x ^= x << 17; x.count_ones() as u64 ^ x
}
pub enum E { X(u64), Y(u32), Z }
#[unsafe(no_mangle)] pub extern "C" fn e01(v: u64, k: u32) -> u64 {
    let e = match k & 3 { 0 => E::X(v), 1 => E::Y(v as u32), _ => E::Z };
    match e { E::X(a) => a ^ 1, E::Y(b) => b as u64, E::Z => 7 }
}
#[unsafe(no_mangle)] pub extern "C" fn f03(a: f64, b: f64) -> u32 { (a < b) as u32 }
fn pick<T: Copy>(a: T, b: T, f: bool) -> T { if f { a } else { b } }
#[unsafe(no_mangle)] pub extern "C" fn g02(a: u64, b: u64, f: u32) -> u64 { pick(a, b, f & 1 == 0) }
#[unsafe(no_mangle)] pub extern "C" fn i01(a: u64, b: u64) -> u64 {
    let w = (a as u128).wrapping_mul(b as u128); (w >> 64) as u64 ^ (w as u64)
}
trait Op2 { fn go2(&self, x: u64) -> u64; }
struct C;
impl Op2 for C { fn go2(&self, x: u64) -> u64 { x >> 3 } }
#[unsafe(no_mangle)] pub extern "C" fn tr02(x: u64) -> u64 { C.go2(x) }
#[unsafe(no_mangle)] pub extern "C" fn u02(a: u32, b: u32) -> u32 { a.saturating_sub(b) }
"#;

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
uint32_t t_add_wrapping(uint32_t,uint32_t); uint64_t t_xor(uint64_t,uint64_t);
uint64_t t_shl_masked(uint64_t,uint32_t); uint64_t t_shr_masked(uint64_t,uint32_t);
uint64_t t_mul_wrapping(uint64_t,uint64_t); uint64_t t_xorshift(uint64_t);
uint64_t t_cond_select(uint64_t,uint64_t,uint32_t);
uint64_t s01(uint64_t,uint64_t); uint64_t s02(uint64_t,uint64_t); uint64_t s03(uint64_t);
uint64_t s04(uint64_t); uint64_t s05(uint64_t); uint64_t s06(uint64_t,uint32_t);
int32_t s07(int32_t,int32_t); uint32_t s08(uint64_t,uint64_t);
uint64_t s09(uint64_t,uint32_t); uint64_t s10(uint64_t);
uint64_t e01(uint64_t,uint32_t); uint32_t f03(double,double);
uint64_t g02(uint64_t,uint64_t,uint32_t); uint64_t i01(uint64_t,uint64_t);
uint64_t tr02(uint64_t); uint32_t u02(uint32_t,uint32_t);
int main(void){
  uint64_t acc=0,x=0x123456789ABCDEFull;
  for(int i=0;i<64;i++){
    x=t_xorshift(x);
    acc^=(uint64_t)t_add_wrapping((uint32_t)x,(uint32_t)i);
    acc+=t_xor(x,acc); acc^=t_shl_masked(x,(uint32_t)i);
    acc+=t_shr_masked(x,(uint32_t)i); acc^=t_mul_wrapping(x,0x2545F4914F6CDD1Dull);
    acc+=t_cond_select(x,acc,(uint32_t)i);
    acc^=s01(x,acc); acc+=s02(x,acc); acc^=s03(x); acc+=s04(x);
    acc^=s05(x); acc+=s06(x,(uint32_t)i);
    acc^=(uint64_t)(int64_t)s07((int32_t)x,(int32_t)i);
    acc+=(uint64_t)s08(x,acc); acc^=s09(x,(uint32_t)i); acc+=s10(x);
    acc^=e01(x,(uint32_t)i); acc+=(uint64_t)f03((double)i,(double)(i^3));
    acc^=g02(x,acc,(uint32_t)i); acc+=i01(x,acc); acc^=tr02(x);
    acc+=(uint64_t)u02((uint32_t)x,(uint32_t)i);
  }
  printf("%llu\n",(unsigned long long)acc); return 0;
}
"#;

/// A `trustc` invocation with verification LEFT ON.
///
/// Deliberately NOT `toolchain_support::rustc_command*`: those add
/// `-Ztrust-verify=off` on the trust channel, which is the whole thing this test
/// exists to avoid. Everything else — the driver binary, the edition — matches.
fn verified_rustc() -> Command {
    let mut cmd = toolchain_support::rustc_driver_command();
    cmd.arg("--edition=2024");
    cmd
}

/// Build the corpus into a static archive in `dir`, returning its path.
fn build_archive(dir: &Path, src: &Path, backend: Option<&Path>) -> Result<PathBuf, String> {
    let mut cmd = verified_rustc();
    if let Some(backend) = backend {
        cmd.arg(format!("-Zcodegen-backend={}", backend.display()));
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    let output = cmd
        .arg("--crate-type=staticlib")
        .arg("--crate-name=tvc")
        .arg(format!("--target={TARGET}"))
        .arg("-Cpanic=abort")
        .arg("-Copt-level=2")
        .arg("--out-dir")
        .arg(dir)
        .arg(src)
        .output()
        .map_err(|e| format!("spawn trustc: {e}"))?;
    if !output.status.success() {
        return Err(format!(
            "compile failed ({}):\n{}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let archive = dir.join("libtvc.a");
    if !archive.is_file() {
        return Err(format!("no archive at {}", archive.display()));
    }
    Ok(archive)
}

/// Link `archive` with the C driver and return the binary's stdout.
fn link_and_run(dir: &Path, archive: &Path, tag: &str) -> Result<String, String> {
    let driver = dir.join("driver.c");
    std::fs::write(&driver, DRIVER).map_err(|e| format!("write driver: {e}"))?;
    let bin = dir.join(format!("run_{tag}"));
    let cc = Command::new("cc")
        .arg("-O2")
        .arg("-o")
        .arg(&bin)
        .arg(&driver)
        .arg(archive)
        .output()
        .map_err(|e| format!("spawn cc: {e}"))?;
    if !cc.status.success() {
        return Err(format!(
            "cc failed ({}):\n{}",
            cc.status,
            String::from_utf8_lossy(&cc.stderr)
        ));
    }
    let run = Command::new(&bin)
        .output()
        .map_err(|e| format!("spawn {}: {e}", bin.display()))?;
    if !run.status.success() {
        return Err(format!("{tag} exited {}", run.status));
    }
    Ok(String::from_utf8_lossy(&run.stdout).trim().to_string())
}

#[test]
fn trust_verified_corpus_matches_llvm_through_the_x86_bridge() {
    if toolchain_support::skip_without_backend_knobs(
        "trust_verified_corpus_matches_llvm_through_the_x86_bridge",
    ) {
        return;
    }
    if !toolchain_support::target_std_available(TARGET) {
        eprintln!("SKIP: no rust-std for {TARGET} on the pinned channel, so NEITHER lane ran");
        return;
    }
    if Command::new("cc").arg("--version").output().is_err() {
        eprintln!("SKIP: no `cc` to link the driver, so the EXECUTED comparison did NOT run");
        return;
    }

    let root = std::env::temp_dir().join(format!("tvc-{}", std::process::id()));
    let src = root.join("tvc.rs");
    std::fs::create_dir_all(&root).expect("create scratch dir");
    std::fs::write(&src, CORPUS).expect("write corpus");

    let backend = backend_artifact_support::current_test_backend();

    let llvm_dir = root.join("llvm");
    let tcg_dir = root.join("tcg");
    std::fs::create_dir_all(&llvm_dir).expect("create llvm dir");
    std::fs::create_dir_all(&tcg_dir).expect("create tcg dir");

    // Both lanes compile the SAME source with verification ON. A frontend
    // refusal therefore fails BOTH, and the panic names which lane saw it so a
    // pin move is not mistaken for a backend defect.
    let llvm_archive = build_archive(&llvm_dir, &src, None)
        .unwrap_or_else(|e| panic!("LLVM lane failed to build the Trust-verified corpus: {e}"));
    let tcg_archive = build_archive(&tcg_dir, &src, Some(&backend))
        .unwrap_or_else(|e| panic!("trust-cg lane failed to build the Trust-verified corpus: {e}"));

    let llvm_out =
        link_and_run(&llvm_dir, &llvm_archive, "llvm").unwrap_or_else(|e| panic!("LLVM lane: {e}"));
    let tcg_out = link_and_run(&tcg_dir, &tcg_archive, "tcg")
        .unwrap_or_else(|e| panic!("trust-cg lane: {e}"));

    assert_eq!(
        tcg_out, llvm_out,
        "trust-cg and LLVM disagree on the Trust-VERIFIED corpus: a backend divergence (P0)"
    );
    assert_eq!(
        tcg_out, EXPECTED_CHECKSUM,
        "both lanes agree but the checksum moved from the pinned value; the corpus or the \
         frontend pin changed, so this is not a silently-agreeing pair"
    );

    let _ = std::fs::remove_dir_all(&root);
}
