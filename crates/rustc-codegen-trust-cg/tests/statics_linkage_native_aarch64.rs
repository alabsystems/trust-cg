// Other hosts compile no native test; a Darwin host must meet every prerequisite.
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Native execution differential (aarch64-apple-darwin): statics, constants and
// multi-CGU linkage, rustc/LLVM against this backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// One `no_std` staticlib is compiled by both backends at `-Copt-level=0` and
// `2`, with one and with sixteen codegen units, linked with the same C driver
// and run; the two outputs must be identical. The crate covers:
//
// * `const` fn pointers (plain, associated, a raw `*const ()`) used as values
//   and called directly;
// * statics pointing into one promoted allocation, and (single-CGU only, see
//   `CONST_ALLOC`) a `const` pointing into it;
// * `extern`-block statics the C driver defines;
// * 16- and 64-byte aligned statics;
// * `Clone::clone_from` of structs whose scalar leaves are not their fields;
// * `#[inline]` functions used from several modules, which rustc copies into
//   every codegen unit that uses them.
//
// With sixteen codegen units the crate's own objects must also combine under
// `ld -r` without a duplicate symbol: each CGU-private copy is one weak
// crate-private definition, not a strong symbol per object.
//
// PROOF GATE: compiled with `no-proof-certs`; this is an execution
// differential, not a certification claim.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "aarch64-apple-darwin";

const CRATE: &str = r#"
#![no_std]
extern "C" { fn abort() -> !; }
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { unsafe { abort() } }

#[inline(never)]
fn double(x: u32) -> u32 { x.wrapping_mul(2) }
#[inline(never)]
fn triple(x: u32) -> u32 { x.wrapping_mul(3) }
const F: fn(u32) -> u32 = double;
const RAW: *const () = triple as *const ();
trait Op { const OP: fn(u32) -> u32; }
struct D; struct T;
impl Op for D { const OP: fn(u32) -> u32 = double; }
impl Op for T { const OP: fn(u32) -> u32 = triple; }
#[inline(never)]
fn via<O: Op>(x: u32) -> u32 { (O::OP)(x) }
#[inline(never)]
fn call_raw(p: *const (), x: u32) -> u32 {
    let f: fn(u32) -> u32 = unsafe { core::mem::transmute(p) };
    f(x)
}
#[no_mangle]
pub extern "C" fn fnptr_call(x: u32) -> u32 { F(x) ^ (D::OP)(x.wrapping_add(1)) ^ via::<T>(x) }
#[no_mangle]
pub extern "C" fn fnptr_raw(x: u32) -> u32 { call_raw(RAW, x) ^ core::hint::black_box(F)(x) }

mod st {
    pub static A: &[u32; 5] = &[10, 20, 30, 40, 50];
    pub static B: &u32 = &A[2];
    pub static C: &[u32; 5] = A;
}
#[no_mangle]
pub extern "C" fn nested(i: u32) -> u32 {
    let off = unsafe { (st::B as *const u32).offset_from(st::A.as_ptr()) } as u32;
    let same = core::ptr::eq(st::A, st::C) as u32;
    let eq = (st::A.as_ptr().wrapping_add(2) == st::B as *const u32) as u32;
    off | same << 8 | eq << 9 | st::C[(i % 5) as usize] << 12
}
#[cfg(single_cgu)]
const K: &u32 = &st::A[3];
#[no_mangle]
pub extern "C" fn const_alloc(i: u32) -> u32 {
    #[cfg(single_cgu)]
    {
        let off = unsafe { (K as *const u32).offset_from(st::A.as_ptr()) } as u32;
        off | (core::ptr::eq(K, &st::C[3]) as u32) << 4 | (*K).wrapping_add(i) << 8
    }
    #[cfg(not(single_cgu))]
    {
        i
    }
}

extern "C" { static HOST_V: u32; static HOST_T: [u16; 4]; }
#[no_mangle]
pub extern "C" fn foreign(i: u32) -> u32 {
    let p = core::ptr::addr_of!(HOST_T) as *const u16;
    unsafe { HOST_V + *p.add((i % 4) as usize) as u32 }
}

#[repr(C, align(16))]
pub struct A16(pub [u32; 4]);
#[repr(C, align(64))]
pub struct A64(pub u8, pub u32);
pub static BIG: u128 = 0x0123_4567_89ab_cdef_fedc_ba98_7654_3210;
pub static V16: A16 = A16([1, 2, 3, 4]);
pub static mut M64: A64 = A64(7, 9);
pub static R16: &A16 = &A16([5, 6, 7, 8]);
#[no_mangle]
pub extern "C" fn aligned(i: u32) -> u64 {
    let a = (&BIG as *const u128 as usize % 16) as u64
        | ((&V16 as *const A16 as usize % 16) as u64) << 8
        | ((unsafe { core::ptr::addr_of!(M64) } as usize % 64) as u64) << 16
        | ((R16 as *const A16 as usize % 16) as u64) << 24;
    unsafe { M64.1 = M64.1.wrapping_add(i); }
    let v = (BIG >> (i % 128)) as u64;
    a ^ v.rotate_left(32) ^ V16.0[(i % 4) as usize] as u64 ^ R16.0[(i % 4) as usize] as u64
        ^ unsafe { M64.1 } as u64
}

#[derive(Clone, Copy)]
pub struct Arr(pub [u16; 7]);
#[derive(Clone, Copy)]
pub struct ArrZst(pub [u8; 2], pub core::marker::PhantomData<u8>, pub u32);
#[derive(Clone, Copy)]
pub struct Nested(pub (u8, u8), pub u16);
#[inline(never)]
fn cf_arr(a: &mut Arr, b: &Arr) { a.clone_from(b) }
#[inline(never)]
fn cf_arr_zst(a: &mut ArrZst, b: &ArrZst) { a.clone_from(b) }
#[inline(never)]
fn cf_nested(a: &mut Nested, b: &Nested) { a.clone_from(b) }
#[no_mangle]
pub extern "C" fn clone_from(x: u32, i: u32) -> u64 {
    let mut a = Arr([1; 7]);
    cf_arr(&mut a, &Arr([x as u16, 2, 3, 4, 5, 6, (x >> 16) as u16]));
    let mut b = ArrZst([9, 9], core::marker::PhantomData, 9);
    cf_arr_zst(&mut b, &ArrZst([x as u8, (x >> 8) as u8], core::marker::PhantomData, x ^ i));
    let mut c = Nested((9, 9), 9);
    cf_nested(&mut c, &Nested((x as u8, (x >> 8) as u8), (x >> 16) as u16));
    a.0[(i % 7) as usize] as u64
        ^ (b.0[0] as u64 | (b.0[1] as u64) << 8 | (b.2 as u64) << 16).rotate_left(16)
        ^ (c.0 .0 as u64 | (c.0 .1 as u64) << 8 | (c.1 as u64) << 16).rotate_left(40)
}

#[inline]
fn mix(x: u64) -> u64 { x.rotate_left(13) ^ x.wrapping_mul(0x9e37_79b9) }
pub struct Guard<'a>(pub &'a core::cell::Cell<u64>, pub u64);
impl Drop for Guard<'_> {
    #[inline]
    fn drop(&mut self) { self.0.set(mix(self.0.get() ^ self.1)); }
}
pub mod lc_a {
    #[inline(never)]
    pub fn f(x: u64) -> u64 {
        let c = core::cell::Cell::new(x);
        { let _g = super::Guard(&c, 3); }
        super::mix(x) ^ c.get()
    }
}
pub mod lc_b {
    #[inline(never)]
    pub fn g(x: u64) -> u64 {
        let c = core::cell::Cell::new(x);
        { let _g = super::Guard(&c, 4); }
        super::mix(x ^ 1) ^ c.get()
    }
}
#[no_mangle]
pub extern "C" fn local_copies(x: u64) -> u64 { lc_a::f(x) ^ lc_b::g(x).rotate_left(7) }
"#;

const DRIVER_C: &str = r#"
#include <stdio.h>
#include <stdint.h>
const uint32_t HOST_V = 1000;
const uint16_t HOST_T[4] = {1, 22, 333, 4444};
void rust_eh_personality(void) {}
extern uint32_t fnptr_call(uint32_t), fnptr_raw(uint32_t), nested(uint32_t);
extern uint32_t const_alloc(uint32_t), foreign(uint32_t);
extern uint64_t aligned(uint32_t), clone_from(uint32_t, uint32_t), local_copies(uint64_t);
static const uint32_t G[] = {0, 1, 7, 255, 256, 65535, 65536, 0x7fffffffu, 0x80000000u, 0xffffffffu};
int main(void) {
    unsigned n = sizeof(G) / sizeof(G[0]);
    for (unsigned i = 0; i < n; i++) {
        uint32_t a = G[i];
        printf("%u %u %u %u %u %llu %llu\n", fnptr_call(a), fnptr_raw(a), nested(a),
               const_alloc(a), foreign(a), (unsigned long long)aligned(a),
               (unsigned long long)local_copies(((uint64_t)a << 17) ^ a));
        for (unsigned j = 0; j < n; j++) {
            printf(" %llu", (unsigned long long)clone_from(a, G[j]));
        }
        printf("\n");
    }
    return 0;
}
"#;

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_sl_a64_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile the crate as a staticlib with LLVM (`backend: None`) or this
/// backend, link it with the C driver, run it, and return its stdout.
fn build_and_run(
    dir: &Path,
    label: &str,
    backend: Option<&Path>,
    opt: u32,
    cgus: u32,
    driver: &Path,
    source: &Path,
) -> String {
    let lib = dir.join(format!("lib{label}.a"));
    let mut command = toolchain_support::rustc_command();
    command
        .args(["--crate-type", "staticlib", "--crate-name", "sl"])
        .args(["--target", TARGET, "-Cpanic=abort"])
        .arg(format!("-Copt-level={opt}"))
        .arg(format!("-Ccodegen-units={cgus}"));
    if cgus == 1 {
        command.args(["--cfg", "single_cgu"]);
    }
    if let Some(backend) = backend {
        let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
        arg.push(backend);
        command
            .arg(arg)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    let output = command
        .arg("-o")
        .arg(&lib)
        .arg(source)
        .output()
        .expect("spawn rustc");
    assert!(
        output.status.success(),
        "{label}: compile failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let exe = dir.join(format!("{label}.bin"));
    let link = Command::new("cc")
        .arg(driver)
        .arg(&lib)
        .arg("-o")
        .arg(&exe)
        .output()
        .expect("spawn cc");
    assert!(
        link.status.success(),
        "{label}: link failed:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = Command::new(&exe).output().expect("run driver");
    assert!(
        run.status.success(),
        "{label}: driver exited {:?}",
        run.status
    );
    String::from_utf8(run.stdout).expect("utf-8 stdout")
}

/// `ld -r` over this crate's own objects in the staticlib `lib` (the sysroot
/// crates' members excluded) must find no duplicate symbol.
fn assert_crate_objects_combine(dir: &Path, lib: &Path, label: &str) {
    let members = dir.join(format!("{label}.members"));
    std::fs::create_dir_all(&members).expect("members dir");
    let extract = Command::new("ar")
        .arg("x")
        .arg(lib)
        .current_dir(&members)
        .output()
        .expect("spawn ar");
    assert!(extract.status.success(), "{label}: ar x failed");
    let objects: Vec<PathBuf> = std::fs::read_dir(&members)
        .expect("read members")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| {
                    name.ends_with(".o")
                        && !name.starts_with("core-")
                        && !name.starts_with("compiler_builtins-")
                })
        })
        .collect();
    assert!(objects.len() > 1, "{label}: expected several crate objects");
    let combined = Command::new("ld")
        .args(["-r", "-arch", "arm64"])
        .args(&objects)
        .arg("-o")
        .arg(members.join("combined.o"))
        .output()
        .expect("spawn ld");
    let stderr = String::from_utf8_lossy(&combined.stderr);
    assert!(
        combined.status.success() && !stderr.contains("duplicate symbol"),
        "{label}: the crate's objects define a symbol twice:\n{stderr}"
    );
}

#[test]
fn statics_constants_and_multi_cgu_linkage_agree_with_llvm_aarch64() {
    darwin_native::require("statics_linkage_native_aarch64", &["cc"]);
    let backend = backend_artifact_support::current_test_backend();
    let dir = workdir("diff");
    let source = dir.join("sl.rs");
    std::fs::write(&source, CRATE).expect("write crate");
    let driver = dir.join("driver.c");
    std::fs::write(&driver, DRIVER_C).expect("write driver");
    for opt in [0, 2] {
        for cgus in [1, 16] {
            let config = format!("O{opt}-cgu{cgus}");
            let llvm = build_and_run(
                &dir,
                &format!("llvm-{config}"),
                None,
                opt,
                cgus,
                &driver,
                &source,
            );
            let label = format!("tcg-{config}");
            let ours = build_and_run(&dir, &label, Some(&backend), opt, cgus, &driver, &source);
            assert_eq!(ours, llvm, "{config}: output differs from LLVM");
            if cgus > 1 {
                assert_crate_objects_combine(&dir, &dir.join(format!("lib{label}.a")), &label);
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    eprintln!(
        "STATICS_LINKAGE cells=4 llvm_runs=4 cg_runs=4 combined_object_sets=2 opts=0,2 cgus=1,16"
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
