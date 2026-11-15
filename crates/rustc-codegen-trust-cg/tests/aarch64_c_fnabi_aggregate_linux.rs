//! Native C/LLVM oracle for the bridge's bounded Linux AArch64 HFA carrier.
//!
//! This is intentionally mandatory on its named host, not a portable skip.
//! The separate bridge runner binds a freshly built backend by path and SHA256.
//! A standalone invocation instead loads, and hashes, the library Cargo built
//! for this test build; it never builds into the shared target directory. Native
//! evidence here does not qualify all rustc FnAbi modes or promote proof status.

#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/closure_body_boundary.rs"]
mod closure_body_boundary;
#[path = "support/closure_wrappers.rs"]
mod closure_wrappers;
#[path = "support/control_flow_residuals.rs"]
mod control_flow_residuals;
#[path = "support/cross_crate_definitions.rs"]
mod cross_crate_definitions;
#[path = "support/dyn_tail.rs"]
mod dyn_tail;
#[path = "support/function_linkage.rs"]
mod function_linkage;
#[path = "support/inlined_closure_bodies.rs"]
mod inlined_closure_bodies;
#[path = "support/maximal_suffix.rs"]
mod maximal_suffix;
#[path = "support/mono_cfg.rs"]
mod mono_cfg;
#[path = "support/rust_call_pointer_calls.rs"]
mod rust_call_pointer_calls;
#[path = "support/scalar_cell_runtime.rs"]
mod scalar_cell_runtime;
#[path = "support/scalar_union_joins.rs"]
mod scalar_union_joins;
#[path = "support/slice_tail.rs"]
mod slice_tail;
#[path = "support/thin_pointer_loops.rs"]
mod thin_pointer_loops;
#[path = "support/toolchain.rs"]
mod toolchain_support;
#[path = "support/track_caller.rs"]
mod track_caller;
#[path = "support/trait_pointer_values.rs"]
mod trait_pointer_values;

#[path = "support/aarch64_fp_asm.rs"]
mod aarch64_fp_asm;
#[path = "support/aggregate_array_iter.rs"]
mod aggregate_array_iter;
#[path = "support/aggregate_store.rs"]
mod aggregate_store;
#[path = "support/assert_pointer.rs"]
mod assert_pointer;
#[path = "support/associated_drop.rs"]
mod associated_drop;
#[path = "support/borrowed_slice.rs"]
mod borrowed_slice;
#[path = "support/enum_discriminant.rs"]
mod enum_discriminant;
#[path = "support/f16_pointee_images.rs"]
mod f16_pointee_images;
#[path = "support/foreign_statics.rs"]
mod foreign_statics;
#[path = "support/foreign_tls_linkage.rs"]
mod foreign_tls_linkage;
#[path = "support/format_reference_cells.rs"]
mod format_reference_cells;
#[path = "support/linux_relocations.rs"]
mod linux_relocations;
#[path = "support/live_pointer.rs"]
mod live_pointer;
#[path = "support/memory_unary.rs"]
mod memory_unary;
#[path = "support/optimized_alloc.rs"]
mod optimized_alloc;
#[path = "support/overaligned_c_arguments.rs"]
mod overaligned_c_arguments;
#[path = "support/panic_runtime.rs"]
mod panic_runtime;
#[path = "support/pointer_bytes.rs"]
mod pointer_bytes;
#[path = "support/pointer_coercions.rs"]
mod pointer_coercions;
#[path = "support/pointer_image.rs"]
mod pointer_image;
#[path = "support/projected_aggregate.rs"]
mod projected_aggregate;
#[path = "support/residual_conversion.rs"]
mod residual_conversion;
#[path = "support/scalar_union_storage.rs"]
mod scalar_union_storage;
#[path = "support/static_alignment.rs"]
mod static_alignment;
#[path = "support/structural_drop.rs"]
mod structural_drop;
#[path = "support/synthesized_visibility.rs"]
mod synthesized_visibility;
#[path = "support/sysroot_native_layout.rs"]
mod sysroot_native_layout;
#[path = "support/terminate_pad.rs"]
mod terminate_pad;
#[path = "support/trait_leaf_memory.rs"]
mod trait_leaf_memory;
#[path = "support/trait_upcasts.rs"]
mod trait_upcasts;
#[path = "support/tuple_memory_elements.rs"]
mod tuple_memory_elements;
#[path = "support/type_id_constants.rs"]
mod type_id_constants;
#[path = "support/uninhabited_arguments.rs"]
mod uninhabited_arguments;
#[path = "support/union_constants.rs"]
mod union_constants;
#[path = "support/unsized_arguments.rs"]
mod unsized_arguments;
#[path = "support/untagged_try_fold.rs"]
mod untagged_try_fold;
#[path = "support/unwind_call.rs"]
mod unwind_call;
#[path = "support/value_layout.rs"]
mod value_layout;
#[path = "support/wide_int_float.rs"]
mod wide_int_float;
#[path = "support/wide_loop_threading.rs"]
mod wide_loop_threading;
#[path = "support/wide_newtype_reads.rs"]
mod wide_newtype_reads;
#[path = "support/wide_overflow_returns.rs"]
mod wide_overflow_returns;
#[path = "support/wide_owner.rs"]
mod wide_owner;
#[path = "support/wide_projection.rs"]
mod wide_projection;
#[path = "support/wide_scalar_pair_arguments.rs"]
mod wide_scalar_pair_arguments;
#[path = "support/x86_64_unspelled_binding.rs"]
mod x86_64_unspelled_binding;
#[path = "support/zero_sized_drop.rs"]
mod zero_sized_drop;

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const TARGET: &str = "aarch64-unknown-linux-gnu";
const DATASETS: usize = 4;
const PREFIXES: [usize; 3] = [0, 7, 8];
const KEEP_ARTIFACTS: &str = "C_FNABI_LINUX_KEEP_ARTIFACTS";

/// The test's artifacts directory, created under `$TMPDIR` (or `/tmp`) and
/// removed when the test ends, passing or failing; every failure message
/// carries its complete step transcript. `C_FNABI_LINUX_KEEP_ARTIFACTS=1`
/// retains it.
struct Artifacts(PathBuf);

impl Drop for Artifacts {
    fn drop(&mut self) {
        if std::env::var_os(KEEP_ARTIFACTS).is_some_and(|value| value == "1") {
            eprintln!("retained artifacts: {}", self.0.display());
        } else if let Err(error) = std::fs::remove_dir_all(&self.0) {
            eprintln!("could not remove artifacts {}: {error}", self.0.display());
        }
    }
}

// Keep this corpus on edition 2024 while sharing the exact build compiler
// and Trust differential lane with the other bridge integration targets.
fn rustc_command() -> Command {
    let mut command = toolchain_support::rustc_command_with_edition("2024");
    command
        .env_remove("TCG_TEST_BACKEND_PATH")
        .env_remove("TCG_TEST_BACKEND_SHA256");
    command
}

fn run_bounded(command: &mut Command, seconds: u32, log: &Path) -> (Output, String) {
    // GNU timeout bounds the complete child process group. output() drains both
    // pipes concurrently, including a verbose failed compiler diagnostic.
    let mut bounded = Command::new("timeout");
    bounded.args(["--kill-after=5", &seconds.to_string()]);
    bounded.arg(command.get_program()).args(command.get_args());
    if let Some(dir) = command.get_current_dir() {
        bounded.current_dir(dir);
    }
    for (key, value) in command.get_envs() {
        if let Some(value) = value {
            bounded.env(key, value);
        } else {
            bounded.env_remove(key);
        }
    }
    let output = bounded.output().expect("execute bounded native ABI step");
    let transcript = format!(
        "command: {command:?}\nstatus: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::write(log, &transcript).expect("retain complete step log");
    (output, transcript)
}

fn checked(command: &mut Command, seconds: u32, log: &Path) -> Output {
    let (output, transcript) = run_bounded(command, seconds, log);
    assert!(
        output.status.success(),
        "{transcript}\nartifacts: {}",
        log.display()
    );
    output
}

/// A scalarized HFA formal whose whole value and nested leaf are both
/// borrowed by C before the leaf is read back.
const PROJECTED_BORROW_HFA: &str = r#"#![no_std]
#[repr(C)] pub struct Inner {pub value:f64}
#[repr(C)] pub struct Outer {pub inner:Inner}
unsafe extern "C" {fn c_change(p:*mut Outer,value:f64);fn c_change_leaf(p:*mut f64,value:f64);}
#[unsafe(no_mangle)] pub unsafe extern "C" fn projected_borrow(mut a:Outer,value:f64)->f64{unsafe{c_change(&raw mut a,value);c_change_leaf(&mut a.inner.value,value);}a.inner.value}
"#;

/// A local over-aligned single-f64 record whose address C writes through.
const OVERALIGNED_CELL: &str = r#"#![no_std]
#[repr(C,align(16))] pub struct Bad {pub value:f64}
unsafe extern "C" {fn c_change(p:*mut Bad,value:f64);}
#[unsafe(no_mangle)] pub unsafe extern "C" fn overaligned_cell(value:f64)->f64{let mut b=Bad{value:-21.5};unsafe{c_change(&raw mut b,value);}b.value}
"#;

/// A local f64 record with a trailing zero-sized field, written through by C.
const ZST_SIBLING_CELL: &str = r#"#![no_std]
#[repr(C)] pub struct WithZst {pub value:f64,pub z:()}
unsafe extern "C" {fn c_change(p:*mut WithZst,value:f64);}
#[unsafe(no_mangle)] pub unsafe extern "C" fn zst_sibling_cell(value:f64)->f64{let mut b=WithZst{value:-21.5,z:()};unsafe{c_change(&raw mut b,value);}b.value}
"#;

/// A local packed (1-byte aligned) single-f64 record whose address C writes
/// through.
const PACKED_CELL: &str = r#"#![no_std]
#[repr(C,packed)] pub struct P {pub value:f64}
unsafe extern "C" {fn c_change(p:*mut P,value:f64);}
#[unsafe(no_mangle)] pub unsafe extern "C" fn packed_cell(value:f64)->f64{let mut b=P{value:-21.5};unsafe{c_change(&raw mut b,value);}b.value}
"#;

/// A scalarized HFA formal whose middle aggregate (not the whole value or the
/// scalar leaf) C writes through before the leaf is read back.
const HFA_MIDDLE_BORROW: &str = r#"#![no_std]
#[repr(C)] pub struct Inner {pub value:f64}
#[repr(C)] pub struct Outer {pub inner:Inner}
unsafe extern "C" {fn c_change_inner(p:*mut Inner,value:f64);}
#[unsafe(no_mangle)] pub unsafe extern "C" fn hfa_middle_borrow(mut a:Outer,value:f64)->f64{unsafe{c_change_inner(&raw mut a.inner,value);}a.inner.value}
"#;

/// These valid Rust/C ABI signatures must compile with LLVM but must be
/// refused by the bounded CG path. Neither a timeout nor an unrelated Rust
/// syntax/type error is accepted as a successful fail-closed control.
fn rejected_boundaries(artifacts: &Path, backend: &Path) -> Vec<String> {
    let mut cases = Vec::new();
    // Every formerly rejected scalar-cell source is retained below as a
    // REQUIRED native positive. Mixed aggregate return is a different ABI
    // obligation and remains explicitly unsupported.
    cases.push(("mixed_return".to_owned(), r#"#![no_std]
#[repr(C)] pub struct Hfa {pub x:f64,pub y:f64}
#[repr(C)] pub struct Pair {pub x:u64,pub y:u64}
#[unsafe(no_mangle)] pub unsafe extern "C" fn mixed_return(f:unsafe extern "C" fn(Hfa)->Pair,a:Hfa,out:*mut u64){let p=unsafe{f(a)};unsafe{*out=p.x;*out.add(1)=p.y;}}
"#.to_owned(), "[TCG-AAPCS64-HFA-MIXED-RETURN]"));
    // The bridge now lowers these two sources at O0-O3: the nested address
    // projection of a scalarized HFA formal (formerly
    // [TCG-AAPCS64-HFA-ALIASED-SCALAR] at O0 and an `Rvalue::RawPtr` refusal
    // above O0) and the over-aligned local cell (formerly
    // [TCG-SCALAR-CELL-LAYOUT]). Their no-proof-certs lowering is the native
    // positive `c_fnabi_hfa_lowered_boundaries_no_proof_match_llvm`. Under
    // this test's certificate-required policy each stays refused, by the
    // proof-promotion opcode-inventory gate ([TCG-PROOF-465], L06-P1): the
    // scalar-cell caller owner stops at its source check or admission filter
    // (`scalar_cell_caller_controls_stop_where_the_ruling_says`). The
    // ZST-sibling local cell, formerly a third refusal here, is a REQUIRED
    // POSITIVE (`zst_sibling_cell_promoted`; ruling
    // LD-93).
    for (name, source) in [
        ("projected_borrow", PROJECTED_BORROW_HFA),
        ("overaligned_cell", OVERALIGNED_CELL),
    ] {
        cases.push((name.to_owned(), source.to_owned(), "[TCG-PROOF-465]"));
    }
    // The scalar-cell layout guard keeps its Linux controls: an exact cell
    // projection must still select the cell's own scalar extent, so the packed
    // record and the HFA formal's middle-aggregate borrow are refused by
    // [TCG-SCALAR-CELL-LAYOUT] at O0-O3, during lowering and so before any
    // proof gate.
    for (name, source) in [
        ("packed_cell", PACKED_CELL),
        ("hfa_middle_borrow", HFA_MIDDLE_BORROW),
    ] {
        cases.push((
            name.to_owned(),
            source.to_owned(),
            "[TCG-SCALAR-CELL-LAYOUT]",
        ));
    }
    assert_eq!(cases.len(), 5);
    let mut refused = Vec::new();
    for (name, source, diagnostic) in cases {
        let source_path = artifacts.join(format!("{name}.rs"));
        std::fs::write(&source_path, source).unwrap();
        for opt in 0..=3 {
            for compiler in ["llvm", "cg"] {
                let stem = format!("{name}_{compiler}_O{opt}");
                let object_dir = artifacts.join(&stem);
                std::fs::create_dir(&object_dir).unwrap();
                let mut command = rustc_command();
                command.args([
                    "--crate-type=lib",
                    "--emit=obj",
                    "-Cpanic=abort",
                    "--target",
                    TARGET,
                ]);
                command.arg(format!("-Copt-level={opt}"));
                if compiler == "cg" {
                    command.arg(format!("-Zcodegen-backend={}", backend.display()));
                }
                command.arg(&source_path).arg("--out-dir").arg(&object_dir);
                let (output, transcript) =
                    run_bounded(&mut command, 60, &artifacts.join(format!("{stem}.log")));
                if compiler == "llvm" {
                    assert!(
                        output.status.success(),
                        "valid-Rust control failed: {transcript}"
                    );
                    assert!(
                        std::fs::read_dir(&object_dir).unwrap().any(|entry| entry
                            .unwrap()
                            .path()
                            .extension()
                            .is_some_and(|ext| ext == "o")),
                        "LLVM control must emit an object"
                    );
                } else {
                    let stderr = String::from_utf8_lossy(&output.stderr);
                    assert_eq!(
                        output.status.code(),
                        Some(1),
                        "expected compiler refusal, not timeout/crash: {transcript}"
                    );
                    assert!(
                        stderr.contains("[TCG-MIR-UNSUPPORTED]")
                            && stderr.contains(diagnostic)
                            && stderr.contains(&name),
                        "wrong refusal boundary: {transcript}"
                    );
                    refused.push(format!("{{\"name\":\"{name}\",\"opt_level\":{opt},\"cg_refusals\":1,\"llvm_objects\":1}}"));
                }
            }
        }
    }
    assert_eq!(refused.len(), 20);
    refused
}

/// The PASS line of `support/hfa_scalar_cell_driver.c`: 4,001 calls, each
/// cell seeded and at its alignment.
const CELL_DRIVER_PASS: &str = "PASS cell checks=4001 calls=4001 misaligned=0 unseeded=0\n";

/// `zst_sibling_cell` is a REQUIRED POSITIVE (ruling
/// LD-93, option (b), lead ruling 2026-10-16).
/// The bridge lowers `WithZst { value: f64, z: () }` to TrustIR byte-identical
/// to `local_cell_read`'s `One { value: f64 }` apart from the function name,
/// so the control stands or falls with the scalar-cell caller route. At
/// O0-O3 the certificates-on, no-knob compile must emit an object (a refusal
/// fails here); a census compile must emit the same object bytes and show
/// the owner's promotion (`assert_scalar_cell_caller_promoted`); and the
/// promoted object and the LLVM twin must each run the control's own C driver
/// (`support/hfa_scalar_cell_driver.c`, `CELL_ALIGN` 8) to the exact PASS
/// line with empty stderr, equal. Returns the eight native rows.
fn zst_sibling_cell_promoted(
    artifacts: &Path,
    backend: &Path,
    digest: &str,
    runtime: &scalar_cell_runtime::Runtime,
) -> Vec<String> {
    let name = "zst_sibling_cell";
    let source = artifacts.join(format!("{name}.rs"));
    let driver = artifacts.join(format!("{name}_driver.c"));
    std::fs::write(&source, ZST_SIBLING_CELL).unwrap();
    std::fs::write(&driver, include_str!("support/hfa_scalar_cell_driver.c")).unwrap();
    let mut rows = Vec::new();
    for opt in 0..=3 {
        let compile = |stem: &str, compiler: &str, knobs: Option<&str>| {
            let object_dir = artifacts.join(stem);
            std::fs::create_dir(&object_dir).unwrap();
            let mut command = rustc_command();
            command.args([
                "--crate-type=lib",
                "--emit=obj",
                "-Cpanic=abort",
                "--target",
                TARGET,
            ]);
            command.arg(format!("-Copt-level={opt}"));
            if compiler == "cg" {
                command.arg(format!("-Zcodegen-backend={}", backend.display()));
            }
            if let Some(knobs) = knobs {
                command.arg(format!("-Ztrust-ir-cg-args={knobs}"));
            }
            command.arg(&source).arg("--out-dir").arg(&object_dir);
            let (output, transcript) = run_bounded(
                &mut command,
                60,
                &artifacts.join(format!("{stem}.compile.log")),
            );
            assert!(
                output.status.success(),
                "{name} O{opt}: the required positive did not compile ({compiler}, knobs \
                 {knobs:?}; ruling LD-93): {transcript}"
            );
            (object_dir, output)
        };
        let (cg_dir, _) = compile(&format!("{name}_cg_O{opt}"), "cg", None);
        let (census_dir, census) = compile(
            &format!("{name}_census_O{opt}"),
            "cg",
            Some("opcode-inventory-trace solve-trace"),
        );
        let promoted = object_digests(&cg_dir);
        assert!(!promoted.is_empty(), "{name} O{opt}: no promoted object");
        assert_eq!(
            object_digests(&census_dir),
            promoted,
            "{name} O{opt}: the census compile emitted other object bytes"
        );
        let parts =
            assert_scalar_cell_caller_promoted(&String::from_utf8_lossy(&census.stderr), name, opt);
        let (llvm_dir, _) = compile(&format!("{name}_llvm_O{opt}"), "llvm", None);
        let mut outputs = Vec::new();
        for (compiler, dir) in [("cg", &cg_dir), ("llvm", &llvm_dir)] {
            let stem = format!("{name}_{compiler}_O{opt}");
            let mut objects = std::fs::read_dir(dir)
                .unwrap()
                .map(|entry| entry.unwrap().path())
                .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
                .collect::<Vec<_>>();
            objects.sort();
            assert!(!objects.is_empty(), "{stem}: no object");
            let executable = artifacts.join(format!("{stem}.elf"));
            let mut linker = Command::new("cc");
            linker
                .arg(format!("-O{opt}"))
                .args(["-std=c11", "-Wall", "-Wextra", "-Werror"])
                .arg(format!("-DCELL={name}"))
                .arg("-DCELL_ALIGN=8")
                .arg(&driver)
                .args(&objects);
            runtime.link_into(&mut linker);
            checked(
                linker.arg("-o").arg(&executable),
                60,
                &artifacts.join(format!("{stem}.link.log")),
            );
            let output = checked(
                &mut Command::new(&executable),
                20,
                &artifacts.join(format!("{stem}.native.log")),
            );
            assert_eq!(
                String::from_utf8(output.stdout.clone()).unwrap(),
                CELL_DRIVER_PASS,
                "{stem}"
            );
            assert!(output.stderr.is_empty(), "{stem}");
            outputs.push(output.stdout);
            rows.push(format!("{{\"family\":\"{name}\",\"compiler\":\"{compiler}\",\"opt_level\":{opt},\"calls\":4001,\"checks\":4001}}"));
        }
        assert_eq!(outputs[0], outputs[1], "{name} O{opt}: CG and LLVM differ");
        assert_eq!(sha256(backend), digest, "scalar-cell backend changed");
        println!(
            "ZST_SIBLING_CELL_PROMOTED opt_level={opt} parts={parts} objects={}",
            promoted
                .iter()
                .map(|(name, sha)| format!("{name}:{sha}"))
                .collect::<Vec<_>>()
                .join(",")
        );
    }
    assert_eq!(rows.len(), 8);
    rows
}

struct ScalarCellCase {
    family: String,
    source: String,
    driver: String,
    calls: usize,
    checks: usize,
}

/// C only observes the live scalar object's own bytes, never neighboring CG
/// stack storage. Canaries below surround C-owned inputs/outputs. Callback
/// addresses are compared as uintptr_t values while the Rust cell is alive;
/// no callback retains or dereferences a pointer after the Rust call returns.
fn scalar_cell_driver(lane: &str) -> String {
    let c_lane = match lane {
        "f32" => "float",
        "f64" => "double",
        "u64" => "uint64_t",
        _ => unreachable!("closed scalar-cell fixture lanes"),
    };
    let bits = if lane == "f32" {
        "static const uint32_t bits[17]={0x41fc0000,0x3fa00000,0xc0200000,0x40700000,0xc0880000,0x80000000,0,0x7f800000,0xff800000,0x7fc12345,0xffc54321,0x3f000001,0xbf000003,0x00800001,0x80800003,1,0x80000001};"
    } else {
        "static const uint64_t bits[17]={UINT64_C(0x403f800000000000),UINT64_C(0x3ff4000000000000),UINT64_C(0xc004000000000000),UINT64_C(0x400e000000000000),UINT64_C(0xc011000000000000),UINT64_C(0x8000000000000000),0,UINT64_C(0x7ff0000000000000),UINT64_C(0xfff0000000000000),UINT64_C(0x7ff8123456789abc),UINT64_C(0xfff8543210fedcba),UINT64_C(0x3fe0000000000001),UINT64_C(0xbfe0000000000003),UINT64_C(0x0010000000000001),UINT64_C(0x8010000000000003),1,UINT64_C(0x8000000000000001)};"
    };
    r#"#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef @LANE@ Scalar;
typedef struct {Scalar value;} Inner;
typedef struct {Inner inner;} Outer;
typedef struct {uint64_t before;Outer data;uint64_t after;} Guard;
typedef struct {uint64_t before;Scalar data[6];uint64_t after;} Output;
_Static_assert(sizeof(Outer)==sizeof(Scalar),"full scalar cell extent");
_Static_assert(_Alignof(Outer)==_Alignof(Scalar),"full scalar cell alignment");
_Static_assert(offsetof(Outer,inner.value)==0,"nested zero-offset scalar");
static const uint64_t CANARY1=UINT64_C(0x75182ab3c69def04),CANARY2=UINT64_C(0xb4e69d721ac3580f);
static unsigned calls,checks,events,changes,records;
static uintptr_t seen,forbidden;
static Scalar expected_memory[16],expected_argument[16],observed[16];
static unsigned expected_tag[16];
static void check(int ok,const char*name){checks++;if(!ok){fprintf(stderr,"FAIL scalar-cell %s check=%u events=%u\n",name,checks,events);exit(1);}}
static void bytes(const void*actual,const void*expected,const char*name){check(memcmp(actual,expected,sizeof(Scalar))==0,name);}
static void canaries(const uint64_t*before,const uint64_t*after){check(*before==CANARY1,"C-before-canary");check(*after==CANARY2,"C-after-canary");}
@BITS@
static Scalar pattern(unsigned i){Scalar value;memcpy(&value,&bits[i%17],sizeof value);return value;}
static void reset(const void*input){events=changes=records=0;seen=0;forbidden=(uintptr_t)input;}
static void observe(void*p){
 if(events>=16){fputs("too many callbacks\n",stderr);exit(1);}
 check((uintptr_t)p%_Alignof(Scalar)==0,"actual-cell-alignment");
 if(events==0)seen=(uintptr_t)p;
 check((uintptr_t)p==seen,"same-live-cell-address");
 check((uintptr_t)p!=forbidden,"by-value-cell-not-C-input");
 memcpy(&observed[events],p,sizeof(Scalar));
 bytes(&observed[events],&expected_memory[events],"opaque-memory-observation");
 events++;
}
void c_change(void*p,Scalar value){unsigned event=events;observe(p);bytes(&value,&expected_argument[event],"opaque-write-argument");memcpy(p,&value,sizeof value);changes++;}
void c_record(void*p,uint32_t tag){if(events>=16){fputs("too many callbacks\n",stderr);exit(1);}check(tag==expected_tag[events],"observation-order");observe(p);records++;}
"#
    .replace("@LANE@", c_lane)
    .replace("@BITS@", bits)
}

fn scalar_cell_case(lane: &str, mode: &str) -> ScalarCellCase {
    let family = match mode {
        "read" | "write" => format!("aliased_{lane}_{mode}"),
        "local" if lane == "f64" => "local_cell_read".to_owned(),
        "local" => format!("local_cell_read_{lane}"),
        "repeated" => format!("repeated_cell_{lane}"),
        "branch_loop" => format!("branch_loop_cell_{lane}"),
        _ => unreachable!("closed scalar-cell fixture modes"),
    };
    let mut source = format!(
        "#![no_std]\n#[repr(C)] pub struct Inner{{pub value:{lane}}}\n#[repr(C)] pub struct Outer{{pub inner:Inner}}\nunsafe extern \"C\"{{fn c_change(p:*mut Outer,value:{lane});fn c_record(p:*mut Outer,tag:u32);}}\n"
    );
    let mut driver = scalar_cell_driver(lane);
    let (calls, checks) = match mode {
        "read" | "write" | "local" => {
            if mode == "local" {
                // The F64 source and body are the former mandatory local-cell
                // refusal, not a simplified replacement that avoids its slot.
                source = format!(
                    "#![no_std]\n#[repr(C)] pub struct One{{pub value:{lane}}}\nunsafe extern \"C\"{{fn c_change(p:*mut One,value:{lane});}}\n#[unsafe(no_mangle)] pub unsafe extern \"C\" fn {family}(value:{lane})->{lane}{{let mut b=One{{value:-21.5}};unsafe{{c_change(&raw mut b,value);}}b.value}}\n"
                );
                writeln!(driver, "extern Scalar {family}(Scalar);").unwrap();
            } else {
                let (ret, body) = if mode == "read" {
                    (lane, "unsafe{c_change(&raw mut a,value);}a.inner.value")
                } else {
                    (
                        "Outer",
                        "a.inner.value=value;unsafe{c_change(&raw mut a,value);}a",
                    )
                };
                writeln!(source,"#[unsafe(no_mangle)] pub unsafe extern \"C\" fn {family}(mut a:Outer,value:{lane})->{ret}{{{body}}}").unwrap();
                writeln!(
                    driver,
                    "extern {} {family}(Outer,Scalar);",
                    if mode == "write" { "Outer" } else { "Scalar" }
                )
                .unwrap();
            }
            driver.push_str("int main(void){for(unsigned data=0;data<17;data++){Guard input={CANARY1,{{-21.5}},CANARY2},output={CANARY1,{{0}},CANARY2};Scalar value=pattern(data),original=input.data.inner.value;reset(&input.data);expected_argument[0]=value;");
            driver.push_str(if mode == "write" {
                "expected_memory[0]=value;"
            } else {
                "expected_memory[0]=original;"
            });
            match mode {
                "write" => writeln!(driver, "output.data={family}(input.data,value);").unwrap(),
                "read" => writeln!(
                    driver,
                    "output.data.inner.value={family}(input.data,value);"
                )
                .unwrap(),
                "local" => writeln!(driver, "output.data.inner.value={family}(value);").unwrap(),
                _ => unreachable!(),
            }
            driver.push_str("calls++;check(events==1,\"callback-count\");check(changes==1,\"write-count\");bytes(&output.data.inner.value,&value,\"returned-live-value\");bytes(&input.data.inner.value,&original,\"C-input-unchanged\");Scalar expected=pattern(data);bytes(&value,&expected,\"replacement-unchanged\");canaries(&input.before,&input.after);canaries(&output.before,&output.after);}");
            (17, 17 * 14)
        }
        "repeated" => {
            writeln!(source,"#[unsafe(no_mangle)] pub unsafe extern \"C\" fn {family}(mut a:Outer,first:{lane},second:{lane},own:{lane},out:*mut {lane})->Outer{{unsafe{{c_record(&raw mut a,0);*out=a.inner.value;c_change(&raw mut a,first);*out.add(1)=a.inner.value;a.inner.value=own;c_record(&raw mut a,1);*out.add(2)=a.inner.value;c_change(&raw mut a,second);*out.add(3)=a.inner.value;}}a}}").unwrap();
            writeln!(
                driver,
                "extern Outer {family}(Outer,Scalar,Scalar,Scalar,Scalar*);"
            )
            .unwrap();
            driver.push_str("int main(void){for(unsigned data=0;data<17;data++){Guard input={CANARY1,{{0}},CANARY2},returned={CANARY1,{{0}},CANARY2};Output output={CANARY1,{0},CANARY2};Scalar initial=pattern(data+2),first=pattern(data),second=pattern(data+5),own=pattern(data+9);input.data.inner.value=initial;reset(&input.data);expected_memory[0]=initial;expected_memory[1]=initial;expected_memory[2]=own;expected_memory[3]=own;expected_argument[1]=first;expected_argument[3]=second;expected_tag[0]=0;expected_tag[2]=1;");
            writeln!(
                driver,
                "returned.data={family}(input.data,first,second,own,output.data);calls++;"
            )
            .unwrap();
            driver.push_str("check(events==4,\"callback-count\");check(changes==2,\"repeated-writes\");check(records==2,\"observation-count\");bytes(&output.data[0],&initial,\"read-before-mutation\");bytes(&output.data[1],&first,\"read-after-first-mutation\");bytes(&output.data[2],&own,\"read-after-projected-store\");bytes(&output.data[3],&second,\"read-after-second-mutation\");bytes(&returned.data.inner.value,&second,\"nested-whole-return\");bytes(&input.data.inner.value,&initial,\"C-input-unchanged\");canaries(&input.before,&input.after);canaries(&returned.before,&returned.after);canaries(&output.before,&output.after);Scalar zero=0;bytes(&output.data[4],&zero,\"unused-output4\");bytes(&output.data[5],&zero,\"unused-output5\");Scalar expected=pattern(data);bytes(&first,&expected,\"first-unchanged\");expected=pattern(data+5);bytes(&second,&expected,\"second-unchanged\");expected=pattern(data+9);bytes(&own,&expected,\"own-unchanged\");}");
            (17, 17 * 40)
        }
        "branch_loop" => {
            writeln!(source,"#[unsafe(no_mangle)] pub unsafe extern \"C\" fn {family}(mut a:Outer,left:{lane},right:{lane},rounds:u32,flag:bool,out:*mut {lane})->Outer{{unsafe{{c_record(&raw mut a,0);let mut i=0;while i<rounds{{if i&1==0{{a.inner.value=left;}}else{{a.inner.value=right;}}c_record(&raw mut a,1);c_change(&raw mut a,if flag{{right}}else{{left}});*out.add(i as usize)=a.inner.value;i=i.wrapping_add(1);}}}}a}}").unwrap();
            writeln!(
                driver,
                "extern Outer {family}(Outer,Scalar,Scalar,uint32_t,_Bool,Scalar*);"
            )
            .unwrap();
            driver.push_str("int main(void){static const unsigned rounds_list[3]={0,1,3};for(unsigned data=0;data<17;data++)for(unsigned r=0;r<3;r++)for(unsigned flag=0;flag<2;flag++){unsigned rounds=rounds_list[r];Guard input={CANARY1,{{0}},CANARY2},returned={CANARY1,{{0}},CANARY2};Output output={CANARY1,{0},CANARY2};Scalar initial=pattern(data+2),left=pattern(data),right=pattern(data+7),chosen=flag?right:left;input.data.inner.value=initial;reset(&input.data);expected_memory[0]=initial;expected_tag[0]=0;for(unsigned i=0;i<rounds;i++){Scalar assigned=i%2?right:left;expected_memory[1+2*i]=assigned;expected_memory[2+2*i]=assigned;expected_tag[1+2*i]=1;expected_argument[2+2*i]=chosen;}");
            writeln!(
                driver,
                "returned.data={family}(input.data,left,right,rounds,flag,output.data);calls++;"
            )
            .unwrap();
            driver.push_str("check(events==1+2*rounds,\"loop-callback-count\");check(changes==rounds,\"loop-mutations\");check(records==1+rounds,\"loop-observations\");for(unsigned i=0;i<6;i++){Scalar expected=i<rounds?chosen:0;bytes(&output.data[i],&expected,\"loop-live-load-or-unused\");}Scalar expected=rounds?chosen:initial;bytes(&returned.data.inner.value,&expected,\"loop-whole-return\");bytes(&input.data.inner.value,&initial,\"C-input-unchanged\");canaries(&input.before,&input.after);canaries(&returned.before,&returned.after);canaries(&output.before,&output.after);expected=pattern(data);bytes(&left,&expected,\"left-unchanged\");expected=pattern(data+7);bytes(&right,&expected,\"right-unchanged\");}");
            (17 * 3 * 2, 17 * 2 * (24 + 34 + 54))
        }
        _ => unreachable!(),
    };
    writeln!(driver,"if(calls!={calls}||checks!={checks}){{fprintf(stderr,\"wrong counts calls=%u checks=%u\\n\",calls,checks);return 2;}}printf(\"PASS scalar_cell family={family} calls=%u checks=%u\\n\",calls,checks);return 0;}}").unwrap();
    ScalarCellCase {
        family,
        source,
        driver,
        calls,
        checks,
    }
}

fn projected_cell_case() -> ScalarCellCase {
    let source = r#"#![no_std]
#[repr(C)] pub struct Hfa {pub x:f64,pub y:f64}
#[repr(C)] pub struct One {pub value:f64}
unsafe extern "C" {fn c_observe(p:*mut One);}
#[unsafe(no_mangle)] pub unsafe extern "C" fn projected_cell_result(f:unsafe extern "C" fn(Hfa)->f64,a:Hfa)->f64{let mut b=One{value:-21.5};unsafe{c_observe(&raw mut b);b.value=f(a);c_observe(&raw mut b);}b.value}
"#.to_owned();
    let mut driver = scalar_cell_driver("f64");
    driver.push_str(r#"typedef struct {double x,y;} Hfa;
extern double projected_cell_result(double(*f)(Hfa),Hfa);
static unsigned called;
static double desired;
void c_observe(void*p){observe(p);}
static double result(Hfa a){double x=3.0,y=7.0;bytes(&a.x,&x,"indirect-HFA-x");bytes(&a.y,&y,"indirect-HFA-y");called++;return desired;}
int main(void){for(unsigned data=0;data<17;data++){
 struct {uint64_t before;Hfa data;uint64_t after;} input={CANARY1,{3.0,7.0},CANARY2};
 Guard output={CANARY1,{{0}},CANARY2};double initial=-21.5;desired=pattern(data);
 reset(&input.data);called=0;expected_memory[0]=initial;expected_memory[1]=desired;
 output.data.inner.value=projected_cell_result(result,input.data);calls++;
 check(events==2,"callback-count");check(called==1,"callee-count");
 bytes(&observed[0],&initial,"initial-cell");bytes(&observed[1],&desired,"updated-cell");bytes(&output.data.inner.value,&desired,"returned-value");
 canaries(&input.before,&input.after);canaries(&output.before,&output.after);
 double x=3.0,y=7.0;bytes(&input.data.x,&x,"input-x-unchanged");bytes(&input.data.y,&y,"input-y-unchanged");
 }if(calls!=17||checks!=357){fprintf(stderr,"wrong projected counts calls=%u checks=%u\n",calls,checks);return 2;}
 printf("PASS scalar_cell family=projected_cell_result calls=17 checks=357\n");return 0;}
"#);
    ScalarCellCase {
        family: "projected_cell_result".to_owned(),
        source,
        driver,
        calls: 17,
        checks: 357,
    }
}

/// Every named family executes with BOTH compilers at EVERY tier. No accepted
/// refusal, early-return skip, or partial positive family is credited here.
fn scalar_cell_boundaries(
    artifacts: &Path,
    backend: &Path,
    digest: &str,
    runtime: &scalar_cell_runtime::Runtime,
) -> Vec<String> {
    let mut cases = Vec::new();
    for lane in ["f32", "f64"] {
        for mode in ["read", "write", "local", "repeated", "branch_loop"] {
            cases.push(scalar_cell_case(lane, mode));
        }
    }
    cases.push(scalar_cell_case("u64", "repeated"));
    cases.push(projected_cell_case());
    assert_eq!(cases.len(), 12);
    let mut rows = Vec::new();
    for case in cases {
        let source = artifacts.join(format!("{}.rs", case.family));
        let driver = artifacts.join(format!("{}.c", case.family));
        std::fs::write(&source, &case.source).unwrap();
        std::fs::write(&driver, &case.driver).unwrap();
        for opt in 0..=3 {
            for compiler in ["llvm", "cg"] {
                let stem = format!("{}_{compiler}_O{opt}", case.family);
                let object_dir = artifacts.join(&stem);
                std::fs::create_dir(&object_dir).unwrap();
                let mut command = rustc_command();
                command.args([
                    "--crate-type=lib",
                    "--emit=obj",
                    "-Cpanic=abort",
                    "--target",
                    TARGET,
                ]);
                command.arg(format!("-Copt-level={opt}"));
                if compiler == "cg" {
                    command.arg(format!("-Zcodegen-backend={}", backend.display()));
                }
                command.arg(&source).arg("--out-dir").arg(&object_dir);
                checked(
                    &mut command,
                    60,
                    &artifacts.join(format!("{stem}.compile.log")),
                );
                let mut objects = std::fs::read_dir(&object_dir)
                    .unwrap()
                    .map(|entry| entry.unwrap().path())
                    .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
                    .collect::<Vec<_>>();
                objects.sort();
                assert!(!objects.is_empty());
                let executable = artifacts.join(format!("{stem}.elf"));
                let mut linker = Command::new("cc");
                linker
                    .arg(format!("-O{opt}"))
                    .arg("-std=c11")
                    .arg(&driver)
                    .args(&objects);
                runtime.link_into(&mut linker);
                checked(
                    linker.arg("-o").arg(&executable),
                    60,
                    &artifacts.join(format!("{stem}.link.log")),
                );
                let output = checked(
                    &mut Command::new(&executable),
                    20,
                    &artifacts.join(format!("{stem}.native.log")),
                );
                assert_eq!(
                    String::from_utf8(output.stdout).unwrap(),
                    format!(
                        "PASS scalar_cell family={} calls={} checks={}\n",
                        case.family, case.calls, case.checks
                    )
                );
                assert!(output.stderr.is_empty());
                assert_eq!(sha256(backend), digest, "scalar-cell backend changed");
                rows.push(format!("{{\"family\":\"{}\",\"compiler\":\"{compiler}\",\"opt_level\":{opt},\"calls\":{},\"checks\":{}}}",case.family,case.calls,case.checks));
            }
        }
    }
    assert_eq!(rows.len(), 96);
    rows
}

/// The whole-call theorem's name (`SCALAR_CELL_CALLER_OBLIGATION_NAME` in
/// `trust-cg-verify`); each replayed part is named `<this> -- part k of n`.
const SCALAR_CELL_CALLER_THEOREM: &str =
    "Source-bound AArch64 scalar-cell caller: whole-call theorem under the AAPCS64 callee contract";

/// The SHA-256 of every `.o` in `dir`, sorted by file name.
fn object_digests(dir: &Path) -> Vec<(String, String)> {
    let mut objects = std::fs::read_dir(dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
        .map(|path| {
            (
                path.file_name().unwrap().to_string_lossy().into_owned(),
                sha256(&path),
            )
        })
        .collect::<Vec<_>>();
    objects.sort();
    objects
}

/// The scalar-cell caller owner's promotion of `function`, read from the
/// stderr of a certificates-on compile with `opcode-inventory-trace
/// solve-trace`: the census reads `blocking=0`, the owner is bound with a
/// Valid replay, every part of its whole-call theorem has a
/// `TCG_SOLVE_TRACE promotion_result … result=Verified` line (an AY proof
/// Clean accepted, the per-function checked-replay evidence), and no part
/// was produced by the constructive closed-definition producer. Returns the
/// theorem's part count.
fn assert_scalar_cell_caller_promoted(stderr: &str, function: &str, opt: u32) -> usize {
    assert!(
        stderr.lines().any(|line| line.starts_with(&format!(
            "[TCG-OPCODE-INVENTORY] v1\tsummary\tfunction={function}\t"
        )) && line.ends_with("\tblocking=0\tpromotable=true")),
        "{function} O{opt}: no blocking=0 census line:\n{stderr}"
    );
    let bound = stderr
        .lines()
        .find(|line| {
            line.starts_with(&format!(
                "[TCG-SCALAR-CELL-CALLER] v1\tbound\tfunction={function}\t"
            ))
        })
        .unwrap_or_else(|| panic!("{function} O{opt}: the owner is unbound:\n{stderr}"));
    assert!(bound.contains("\treplay=Valid\t"), "{bound}");
    let parts: usize = bound
        .split('\t')
        .find_map(|field| field.strip_prefix("parts="))
        .and_then(|parts| parts.parse().ok())
        .unwrap_or_else(|| panic!("{bound}"));
    assert!(parts > 0);
    for k in 1..=parts {
        let verified = format!(
            "TCG_SOLVE_TRACE promotion_result obligation=\"{SCALAR_CELL_CALLER_THEOREM} -- part {k} of {parts}\" result=Verified"
        );
        assert!(
            stderr.lines().any(|line| line == verified),
            "{function} O{opt}: part {k} of {parts} has no checked-proof replay:\n{stderr}"
        );
    }
    assert!(
        !stderr.lines().any(|line| line.starts_with(&format!(
            "TCG_SOLVE_TRACE closed_definition_proof obligation=\"{SCALAR_CELL_CALLER_THEOREM}"
        ))),
        "{function} O{opt}: a part was produced without AY"
    );
    parts
}

/// LA-11's distinguishing test (L06-P1, L09): the six scalar-cell caller
/// families the AArch64 scalar-cell caller owner binds, at O0-O3, compiled
/// with certificates on and no knob, must each emit a promoted object. A
/// second compile with the diagnostic census knobs must emit the same object
/// bytes and show the census reading `blocking=0`, the owner bound with a
/// Valid replay, and every part of its whole-call theorem `Verified` (an AY
/// proof Clean accepted; no constructive closed-definition producer). Both
/// the promoted object and the LLVM twin run the family's C driver to the
/// exact PASS line with empty stderr. The backend bytes must not change.
#[test]
fn scalar_cell_caller_owner_promotes_six_families_equal_to_llvm() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-cell-caller.XXXXXX"])
        .output()
        .unwrap();
    assert!(temp.status.success());
    let artifacts_dir = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let artifacts = artifacts_dir.0.clone();
    let (backend, digest) = backend(&artifacts);
    let runtime = scalar_cell_runtime::Runtime::build(&artifacts);
    let mut rows = Vec::new();
    for lane in ["f32", "f64"] {
        for mode in ["read", "write", "local"] {
            let case = scalar_cell_case(lane, mode);
            let source = artifacts.join(format!("{}.rs", case.family));
            let driver = artifacts.join(format!("{}.c", case.family));
            std::fs::write(&source, &case.source).unwrap();
            std::fs::write(&driver, &case.driver).unwrap();
            for opt in 0..=3 {
                let compile = |stem: &str, compiler: &str, knobs: Option<&str>| {
                    let object_dir = artifacts.join(stem);
                    std::fs::create_dir(&object_dir).unwrap();
                    let mut command = rustc_command();
                    command.args([
                        "--crate-type=lib",
                        "--emit=obj",
                        "-Cpanic=abort",
                        "--target",
                        TARGET,
                    ]);
                    command.arg(format!("-Copt-level={opt}"));
                    if compiler == "cg" {
                        command.arg(format!("-Zcodegen-backend={}", backend.display()));
                    }
                    if let Some(knobs) = knobs {
                        command.arg(format!("-Ztrust-ir-cg-args={knobs}"));
                    }
                    command.arg(&source).arg("--out-dir").arg(&object_dir);
                    // The lane's own per-compile bound (`scalar_cell_boundaries`).
                    let output = checked(
                        &mut command,
                        60,
                        &artifacts.join(format!("{stem}.compile.log")),
                    );
                    (object_dir, output)
                };
                let family = &case.family;
                let (cg_dir, _) = compile(&format!("{family}_cg_O{opt}"), "cg", None);
                let (census_dir, census) = compile(
                    &format!("{family}_census_O{opt}"),
                    "cg",
                    Some("opcode-inventory-trace solve-trace"),
                );
                let promoted = object_digests(&cg_dir);
                assert!(!promoted.is_empty(), "{family} O{opt}: no promoted object");
                assert_eq!(
                    object_digests(&census_dir),
                    promoted,
                    "{family} O{opt}: the census compile emitted other object bytes"
                );
                let parts = assert_scalar_cell_caller_promoted(
                    &String::from_utf8_lossy(&census.stderr),
                    family,
                    opt,
                );
                let (llvm_dir, _) = compile(&format!("{family}_llvm_O{opt}"), "llvm", None);
                let mut outputs = Vec::new();
                for (compiler, dir) in [("cg", &cg_dir), ("llvm", &llvm_dir)] {
                    let stem = format!("{family}_{compiler}_O{opt}");
                    let mut objects = std::fs::read_dir(dir)
                        .unwrap()
                        .map(|entry| entry.unwrap().path())
                        .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
                        .collect::<Vec<_>>();
                    objects.sort();
                    let executable = artifacts.join(format!("{stem}.elf"));
                    let mut linker = Command::new("cc");
                    linker
                        .arg(format!("-O{opt}"))
                        .arg("-std=c11")
                        .arg(&driver)
                        .args(&objects);
                    runtime.link_into(&mut linker);
                    checked(
                        linker.arg("-o").arg(&executable),
                        60,
                        &artifacts.join(format!("{stem}.link.log")),
                    );
                    let output = checked(
                        &mut Command::new(&executable),
                        20,
                        &artifacts.join(format!("{stem}.native.log")),
                    );
                    assert_eq!(
                        String::from_utf8(output.stdout.clone()).unwrap(),
                        format!(
                            "PASS scalar_cell family={family} calls={} checks={}\n",
                            case.calls, case.checks
                        )
                    );
                    assert!(output.stderr.is_empty());
                    outputs.push(output.stdout);
                }
                assert_eq!(
                    outputs[0], outputs[1],
                    "{family} O{opt}: CG and LLVM differ"
                );
                assert_eq!(sha256(&backend), digest, "scalar-cell backend changed");
                println!(
                    "SCALAR_CELL_CALLER_PROMOTED family={family} opt_level={opt} parts={parts} \
                     objects={}",
                    promoted
                        .iter()
                        .map(|(name, sha)| format!("{name}:{sha}"))
                        .collect::<Vec<_>>()
                        .join(",")
                );
                rows.push((family.clone(), opt));
            }
        }
    }
    assert_eq!(rows.len(), 24);
}

/// Where the scalar-cell caller owner stops on the three scalar-cell
/// controls the bridge now lowers, as the ruling
/// LD-93 states it. Each is compiled at O0-O3
/// with certificates on plus the diagnostic census knobs, and the owner's
/// `[TCG-SCALAR-CELL-CALLER]` trace must name: `projected_borrow` (two calls)
/// refused by the source check at O0 and by the admission filter at O1-O3,
/// never by the qualified-domain bound (no compile reaches it);
/// `overaligned_cell` refused by the source check at O0-O3; both compiles
/// refused with `[TCG-PROOF-465]`, as `rejected_boundaries` requires.
/// `zst_sibling_cell` (TrustIR equal to `local_cell_read`'s) is promoted:
/// the owner bound with a Valid replay, every part `Verified` and the census
/// `blocking=0` (`assert_scalar_cell_caller_promoted`), the lane's required
/// positive `zst_sibling_cell_promoted` under the lead's ruling (b).
#[test]
fn scalar_cell_caller_controls_stop_where_the_ruling_says() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-cell-controls.XXXXXX"])
        .output()
        .unwrap();
    assert!(temp.status.success());
    let artifacts_dir = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let artifacts = artifacts_dir.0.clone();
    let (backend, digest) = backend(&artifacts);
    let source_check = "reason=scalar-cell caller source: ";
    let admission = "reason=scalar-cell caller admission filter: ";
    let mut stops = Vec::new();
    for (name, source) in [
        ("projected_borrow", PROJECTED_BORROW_HFA),
        ("overaligned_cell", OVERALIGNED_CELL),
        ("zst_sibling_cell", ZST_SIBLING_CELL),
    ] {
        let source_path = artifacts.join(format!("{name}.rs"));
        std::fs::write(&source_path, source).unwrap();
        for opt in 0..=3 {
            let stem = format!("{name}_census_O{opt}");
            let object_dir = artifacts.join(&stem);
            std::fs::create_dir(&object_dir).unwrap();
            let mut command = rustc_command();
            command.args([
                "--crate-type=lib",
                "--emit=obj",
                "-Cpanic=abort",
                "--target",
                TARGET,
            ]);
            command.arg(format!("-Copt-level={opt}"));
            command.arg(format!("-Zcodegen-backend={}", backend.display()));
            command.arg("-Ztrust-ir-cg-args=opcode-inventory-trace solve-trace");
            command.arg(&source_path).arg("--out-dir").arg(&object_dir);
            let (output, transcript) =
                run_bounded(&mut command, 60, &artifacts.join(format!("{stem}.log")));
            let stderr = String::from_utf8_lossy(&output.stderr);
            let trace: Vec<&str> = stderr
                .lines()
                .filter(|line| {
                    line.starts_with("[TCG-SCALAR-CELL-CALLER] v1\t")
                        && line.contains(&format!("\tfunction={name}\t"))
                })
                .collect();
            assert!(
                !stderr.contains("outside the qualified scalar-cell caller domain"),
                "{name} O{opt}: the qualified-domain bound was reached: {transcript}"
            );
            let expected = match (name, opt) {
                ("projected_borrow", 0) | ("overaligned_cell", _) => Some(source_check),
                ("projected_borrow", _) => Some(admission),
                _ => None,
            };
            match expected {
                Some(stage) => {
                    assert_eq!(
                        output.status.code(),
                        Some(1),
                        "{name} O{opt}: expected a refusal: {transcript}"
                    );
                    assert!(
                        stderr.contains("[TCG-PROOF-465]"),
                        "{name} O{opt}: {transcript}"
                    );
                    assert!(
                        matches!(trace.as_slice(), [line] if line.contains("\tunbound\t") && line.contains(stage)),
                        "{name} O{opt}: expected one unbound trace with `{stage}`: {trace:?}"
                    );
                    stops.push(format!("{name} O{opt}: {stage}"));
                }
                None => {
                    assert!(
                        output.status.success(),
                        "{name} O{opt}: expected a promoted object: {transcript}"
                    );
                    assert!(
                        matches!(trace.first(), Some(line) if line.contains("\tbound\t") && line.contains("\treplay=Valid\t")),
                        "{name} O{opt}: expected the owner bound with a Valid replay: {trace:?}"
                    );
                    let parts = assert_scalar_cell_caller_promoted(&stderr, name, opt);
                    stops.push(format!("{name} O{opt}: bound replay=Valid parts={parts}"));
                }
            }
        }
    }
    assert_eq!(sha256(&backend), digest, "scalar-cell backend changed");
    println!("SCALAR_CELL_CALLER_CONTROL_STOPS {stops:?}");
    assert_eq!(stops.len(), 12);
}

/// The lane's required `zst_sibling_cell` positive (`zst_sibling_cell_promoted`,
/// ruling LD-93 (b)) with a verdict of its own.
/// The lane test runs the same function after `rejected_boundaries` and puts
/// its eight native rows in the runner's marker; this test fails or passes
/// whatever the lane test's later steps do.
#[test]
fn zst_sibling_cell_is_a_required_promoted_positive() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-zst-cell.XXXXXX"])
        .output()
        .unwrap();
    assert!(temp.status.success());
    let artifacts_dir = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let artifacts = artifacts_dir.0.clone();
    let (backend, digest) = backend(&artifacts);
    let runtime = scalar_cell_runtime::Runtime::build(&artifacts);
    let rows = zst_sibling_cell_promoted(&artifacts, &backend, &digest, &runtime);
    assert_eq!(rows.len(), 8);
}

#[test]
fn llvm_scalar_cell_debug_runtime_links_and_aborts_on_panic() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-cell-runtime.XXXXXX"])
        .output()
        .unwrap();
    assert!(temp.status.success());
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let runtime = scalar_cell_runtime::Runtime::build(&artifacts.0);
    for mode in ["repeated", "branch_loop"] {
        let case = scalar_cell_case("f32", mode);
        let directory = artifacts.0.join(&case.family);
        std::fs::create_dir(&directory).unwrap();
        let source = directory.join("caller.rs");
        let driver = directory.join("driver.c");
        std::fs::write(&source, &case.source).unwrap();
        std::fs::write(&driver, &case.driver).unwrap();
        checked(
            rustc_command()
                .args([
                    "--crate-type=lib",
                    "--emit=obj",
                    "-Cpanic=abort",
                    "--target",
                    TARGET,
                    "-Copt-level=0",
                ])
                .arg(&source)
                .arg("--out-dir")
                .arg(&directory),
            60,
            &directory.join("compile.log"),
        );
        let mut objects = std::fs::read_dir(&directory)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
            .collect::<Vec<_>>();
        objects.sort();
        assert!(!objects.is_empty());
        let executable = directory.join("linked.elf");
        let mut linker = Command::new("cc");
        linker.args(["-O0", "-std=c11"]).arg(&driver).args(objects);
        runtime.link_into(&mut linker);
        checked(
            linker.arg("-o").arg(&executable),
            60,
            &directory.join("link.log"),
        );
        let output = checked(
            &mut Command::new(&executable),
            20,
            &directory.join("native.log"),
        );
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            format!(
                "PASS scalar_cell family={} calls={} checks={}\n",
                case.family, case.calls, case.checks
            )
        );
        assert!(output.stderr.is_empty());
    }
}

/// Diagnostic (no-proof-certs) native positives for the three scalar-cell
/// controls the bridge now lowers: `projected_borrow` and `overaligned_cell`,
/// which the certificate-required policy still refuses (`rejected_boundaries`),
/// and `zst_sibling_cell`, which it promotes (`zst_sibling_cell_promoted`,
/// the lane's required positive). Against an independent C oracle
/// and the LLVM twin at O0-O3: both C callees of the HFA formal must see its
/// single storage and the leaf read must observe both writes; each local cell
/// must reach C seeded, at its alignment, and be read back after the write.
#[test]
fn c_fnabi_hfa_lowered_boundaries_no_proof_match_llvm() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-hfa-lowered-boundaries.XXXXXX"])
        .output()
        .unwrap();
    assert!(temp.status.success());
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    let runtime = scalar_cell_runtime::Runtime::build(root);
    let borrow_driver = root.join("projected_borrow_driver.c");
    let cell_driver = root.join("scalar_cell_driver.c");
    std::fs::write(
        &borrow_driver,
        include_str!("support/hfa_projected_borrow_driver.c"),
    )
    .unwrap();
    std::fs::write(
        &cell_driver,
        include_str!("support/hfa_scalar_cell_driver.c"),
    )
    .unwrap();
    let mut checks = 0;
    for (name, rust, driver, defines, expected, case_checks) in [
        (
            "projected_borrow",
            PROJECTED_BORROW_HFA,
            &borrow_driver,
            &[][..],
            "PASS projected_borrow checks=48681 change=48681 leaf=48681 aliased=48681\n",
            48681,
        ),
        (
            "overaligned_cell",
            OVERALIGNED_CELL,
            &cell_driver,
            &["-DCELL=overaligned_cell", "-DCELL_ALIGN=16"][..],
            CELL_DRIVER_PASS,
            4001,
        ),
        (
            "zst_sibling_cell",
            ZST_SIBLING_CELL,
            &cell_driver,
            &["-DCELL=zst_sibling_cell", "-DCELL_ALIGN=8"][..],
            CELL_DRIVER_PASS,
            4001,
        ),
    ] {
        let source = root.join(format!("{name}.rs"));
        std::fs::write(&source, rust).unwrap();
        for opt in 0..=3 {
            for compiler in ["llvm", "cg"] {
                let dir = root.join(format!("{name}-{compiler}-O{opt}"));
                std::fs::create_dir(&dir).unwrap();
                let mut command = rustc_command();
                command.args([
                    "--crate-type=lib",
                    "--emit=obj",
                    "-Cpanic=abort",
                    "--target",
                    TARGET,
                ]);
                command.arg(format!("-Copt-level={opt}"));
                if compiler == "cg" {
                    command
                        .arg(format!("-Zcodegen-backend={}", backend.display()))
                        .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
                }
                command.arg(&source).arg("--out-dir").arg(&dir);
                checked(&mut command, 60, &dir.join("compile.log"));
                let mut objects = std::fs::read_dir(&dir)
                    .unwrap()
                    .map(|entry| entry.unwrap().path())
                    .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
                    .collect::<Vec<_>>();
                objects.sort();
                assert!(!objects.is_empty());
                let executable = dir.join("native.elf");
                let mut linker = Command::new("cc");
                linker
                    .args(["-O2", "-std=c11", "-Wall", "-Wextra", "-Werror"])
                    .args(defines)
                    .arg(driver)
                    .args(&objects);
                runtime.link_into(&mut linker);
                checked(linker.arg("-o").arg(&executable), 60, &dir.join("link.log"));
                let output = checked(&mut Command::new(&executable), 20, &dir.join("native.log"));
                assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
                assert!(output.stderr.is_empty());
                checks += case_checks;
                assert_eq!(
                    sha256(&backend),
                    digest,
                    "backend changed during {name}-{compiler}-O{opt}"
                );
            }
        }
    }
    assert_eq!(checks, 453464);
    println!(
        "TCG_HFA_LOWERED_BOUNDARIES cases=3 executions=24 checks={checks} backend_sha256={digest}"
    );
}

/// The backend arguments of every bridge compile in the shared
/// `rust_call_pointer_calls` and `inlined_closure_bodies` modules.
fn cg_knobs() -> String {
    "-Ztrust-ir-cg-args=no-proof-certs".to_owned()
}

#[test]
fn no_proof_rust_call_pointer_calls_match_llvm() {
    rust_call_pointer_calls::no_proof_rust_call_pointer_calls_match_llvm();
}

#[test]
fn no_proof_inlined_closure_bodies_match_llvm() {
    inlined_closure_bodies::no_proof_inlined_closure_bodies_match_llvm();
}

fn sha256(path: &Path) -> String {
    let output = Command::new("sha256sum")
        .arg(path)
        .output()
        .expect("sha256sum");
    assert!(output.status.success(), "hash {}", path.display());
    let text = String::from_utf8(output.stdout).expect("SHA256 output");
    let hash = text.split_whitespace().next().expect("SHA256 digest");
    assert!(hash.len() == 64 && hash.bytes().all(|b| b.is_ascii_hexdigit()));
    hash.to_owned()
}

fn backend(_artifacts: &Path) -> (PathBuf, String) {
    let path = std::env::var_os("TCG_TEST_BACKEND_PATH");
    let hash = std::env::var("TCG_TEST_BACKEND_SHA256").ok();
    match (path, hash) {
        (Some(path), Some(expected)) => {
            let path = PathBuf::from(path);
            assert!(
                path.is_absolute() && path.is_file(),
                "exact backend path required"
            );
            let actual = sha256(&path);
            assert_eq!(actual, expected, "runner's fresh backend identity changed");
            (path, actual)
        }
        (None, None) => {
            // No runner binding: the library Cargo built for this test build,
            // never a nested build into the shared target directory.
            let path = backend_artifact_support::current_test_backend();
            let hash = sha256(&path);
            (path, hash)
        }
        _ => panic!("backend path and SHA256 must be supplied together"),
    }
}

#[derive(Clone)]
struct Shape {
    name: String,
    rust_lane: &'static str,
    c_lane: &'static str,
    bytes: usize,
    lanes: usize,
    form: usize,
}

impl Shape {
    fn member(&self, base: &str, lane: usize) -> String {
        match self.form {
            0 => format!("{base}.a{lane}"),
            1 => format!("{base}.inner.a{lane}"),
            2 => format!("{base}.lanes[{lane}]"),
            _ => unreachable!("generator has three explicit forms"),
        }
    }
}

fn shapes() -> Vec<Shape> {
    let mut shapes = Vec::new();
    for (rust_lane, c_lane, bytes) in [("f32", "float", 4), ("f64", "double", 8)] {
        for lanes in 1..=4 {
            for form in 0..3 {
                shapes.push(Shape {
                    name: format!("H{bytes}_{lanes}_{form}"),
                    rust_lane,
                    c_lane,
                    bytes,
                    lanes,
                    form,
                });
            }
        }
    }
    shapes
}

fn declarations(shape: &Shape, rust: &mut String, c: &mut String) {
    let Shape {
        name,
        rust_lane,
        c_lane,
        lanes,
        form,
        bytes,
    } = shape;
    let fields = (0..*lanes)
        .map(|i| format!("pub a{i}:{rust_lane},"))
        .collect::<String>();
    let c_fields = (0..*lanes)
        .map(|i| format!("{c_lane} a{i};"))
        .collect::<String>();
    let (rust_fields, c_fields) = match form {
        0 => (fields, c_fields),
        1 => {
            writeln!(
                rust,
                "#[repr(C)] #[derive(Clone,Copy)] pub struct {name}Inner {{{fields}}}"
            )
            .unwrap();
            writeln!(c, "typedef struct {{{c_fields}}} {name}Inner;").unwrap();
            (
                format!("pub inner:{name}Inner"),
                format!("{name}Inner inner;"),
            )
        }
        2 => (
            format!("pub lanes:[{rust_lane};{lanes}]"),
            format!("{c_lane} lanes[{lanes}];"),
        ),
        _ => unreachable!(),
    };
    writeln!(
        rust,
        "#[repr(C)] #[derive(Clone,Copy)] pub struct {name} {{{rust_fields}}}"
    )
    .unwrap();
    writeln!(c, "typedef struct {{{c_fields}}} {name};").unwrap();
    writeln!(
        c,
        "_Static_assert(sizeof({name})=={},\"HFA size\");",
        lanes * bytes
    )
    .unwrap();
    writeln!(
        c,
        "_Static_assert(_Alignof({name})=={bytes},\"HFA alignment\");"
    )
    .unwrap();
    for lane in 0..*lanes {
        let member = shape.member("", lane);
        writeln!(
            c,
            "_Static_assert(offsetof({name},{})=={},\"HFA member offset\");",
            &member[1..],
            lane * bytes
        )
        .unwrap();
    }
}

fn consumer(shape: &Shape, prefix: usize, rust: &mut String, c: &mut String, main: &mut String) {
    let Shape {
        name,
        rust_lane,
        c_lane,
        lanes,
        ..
    } = shape;
    let id = format!("{name}_p{prefix}");
    let rust_prefix = (0..prefix)
        .map(|i| format!("p{i}:f64,"))
        .collect::<String>();
    let c_prefix = (0..prefix)
        .map(|i| format!("double p{i},"))
        .collect::<String>();
    let values = (0..prefix)
        .map(|i| format!("{}.25,", 101 + i))
        .collect::<String>();
    let rust_params = format!(
        "{rust_prefix}a:{name},tail:f64,guard:u64,out:*mut {rust_lane},sent:*mut f64,gout:*mut u64"
    );
    let c_params = format!(
        "{c_prefix}{name} a,double tail,uint64_t guard,{c_lane}*out,double*sent,uint64_t*gout"
    );
    let mut rust_body = String::new();
    let mut c_body = String::new();
    for lane in 0..*lanes {
        let member = shape.member("a", lane);
        write!(rust_body, "*out.add({lane})={member};").unwrap();
        write!(c_body, "out[{lane}]={member};").unwrap();
    }
    for i in 0..prefix {
        write!(rust_body, "*sent.add({i})=p{i};").unwrap();
        write!(c_body, "sent[{i}]=p{i};").unwrap();
    }
    write!(rust_body, "*sent.add({prefix})=tail;*gout=guard;").unwrap();
    write!(c_body, "sent[{prefix}]=tail;*gout=guard;").unwrap();
    writeln!(rust, "#[unsafe(no_mangle)] pub unsafe extern \"C\" fn cg_take_{id}({rust_params}){{unsafe{{{rust_body}}}}}").unwrap();
    writeln!(
        rust,
        "unsafe extern \"C\" {{fn c_take_{id}({rust_params});}}"
    )
    .unwrap();
    writeln!(
        rust,
        "pub type Take_{id}=unsafe extern \"C\" fn({rust_params});"
    )
    .unwrap();
    writeln!(
        c,
        "__attribute__((noinline)) void c_take_{id}({c_params}){{{c_body}}}"
    )
    .unwrap();
    writeln!(
        c,
        "extern void cg_take_{id}({c_params});\ntypedef void(*Take_{id})({c_params});"
    )
    .unwrap();
    for indirect in [false, true] {
        let mode = if indirect { "indirect" } else { "direct" };
        let fn_param = if indirect {
            format!("f:Take_{id},")
        } else {
            String::new()
        };
        let c_fn_param = if indirect {
            format!("Take_{id} f,")
        } else {
            String::new()
        };
        let callee = if indirect {
            "f".to_owned()
        } else {
            format!("c_take_{id}")
        };
        writeln!(rust, "#[unsafe(no_mangle)] pub unsafe extern \"C\" fn cg_call_{mode}_{id}({fn_param}a:*const {name},out:*mut {rust_lane},sent:*mut f64,gout:*mut u64){{unsafe{{{callee}({values}*a,-127.5,0xd3a59c276b18e04f,out,sent,gout);}}}}").unwrap();
        writeln!(c, "extern void cg_call_{mode}_{id}({c_fn_param}const {name}*,{c_lane}*,double*,uint64_t*);").unwrap();
    }
    for mode in ["incoming", "direct", "indirect"] {
        writeln!(
            main,
            "{{ struct {{uint64_t before;{c_lane} data[4];uint64_t after;}} ob={{CANARY1,{{0}},CANARY2}};{c_lane}*out=ob.data;struct {{uint64_t before;double data[9];uint64_t after;}} sb={{CANARY1,{{0}},CANARY2}};double*sent=sb.data;struct {{uint64_t before,data,after;}} gb={{CANARY1,0,CANARY2}};"
        )
        .unwrap();
        match mode {
            "incoming" => writeln!(
                main,
                "cg_take_{id}({values}a,-127.5,GUARD,out,sent,&gb.data);"
            )
            .unwrap(),
            "direct" => writeln!(main, "cg_call_direct_{id}(&a,out,sent,&gb.data);").unwrap(),
            "indirect" => writeln!(
                main,
                "cg_call_indirect_{id}(c_take_{id},&a,out,sent,&gb.data);"
            )
            .unwrap(),
            _ => unreachable!(),
        }
        writeln!(main, "calls++;").unwrap();
        for lane in 0..*lanes {
            writeln!(
                main,
                "check_bytes(\"{id}/{mode}/lane{lane}\",&out[{lane}],&bits{}[data][{lane}],sizeof(out[0]));",
                shape.bytes
            )
            .unwrap();
        }
        for i in 0..prefix {
            writeln!(main, "{{double expected={}.25;check_bytes(\"{id}/{mode}/prefix{i}\",&sent[{i}],&expected,8);}}", 101 + i).unwrap();
        }
        writeln!(main, "{{double expected=-127.5;check_bytes(\"{id}/{mode}/tail\",&sent[{prefix}],&expected,8);}}\ncheck_bytes(\"{id}/{mode}/guard\",&gb.data,&GUARD,8);").unwrap();
        for buffer in ["ob", "sb", "gb"] {
            writeln!(
                main,
                "check_canaries(\"{id}/{mode}/{buffer}\",&{buffer}.before,&{buffer}.after);"
            )
            .unwrap();
        }
        for lane in *lanes..4 {
            writeln!(
                main,
                "check_bytes(\"{id}/{mode}/unused-out{lane}\",&out[{lane}],&ZERO,sizeof(out[0]));"
            )
            .unwrap();
        }
        for lane in prefix + 1..9 {
            writeln!(
                main,
                "check_bytes(\"{id}/{mode}/unused-sent{lane}\",&sent[{lane}],&ZERO,8);"
            )
            .unwrap();
        }
        writeln!(main, "}}").unwrap();
    }
}

fn returned(shape: &Shape, rust: &mut String, c: &mut String, main: &mut String) {
    let Shape {
        name,
        rust_lane,
        c_lane,
        lanes,
        ..
    } = shape;
    writeln!(rust, "#[unsafe(no_mangle)] pub unsafe extern \"C\" fn cg_make_{name}(p:*const {name})->{name}{{unsafe{{*p}}}}\nunsafe extern \"C\"{{fn c_make_{name}(p:*const {name})->{name};}}\npub type Make_{name}=unsafe extern \"C\" fn(*const {name})->{name};").unwrap();
    writeln!(c, "__attribute__((noinline)) {name} c_make_{name}(const {name}*p){{return *p;}}\nextern {name} cg_make_{name}(const {name}*);\ntypedef {name}(*Make_{name})(const {name}*);").unwrap();
    let rust_store = (0..*lanes)
        .map(|i| format!("*out.add({i})={};", shape.member("a", i)))
        .collect::<String>();
    for indirect in [false, true] {
        let mode = if indirect { "indirect" } else { "direct" };
        let fn_param = if indirect {
            format!("f:Make_{name},")
        } else {
            String::new()
        };
        let c_fn_param = if indirect {
            format!("Make_{name} f,")
        } else {
            String::new()
        };
        let callee = if indirect {
            "f".to_owned()
        } else {
            format!("c_make_{name}")
        };
        writeln!(rust, "#[unsafe(no_mangle)] pub unsafe extern \"C\" fn cg_result_{mode}_{name}({fn_param}p:*const {name},out:*mut {rust_lane}){{unsafe{{let a={callee}(p);{rust_store}}}}}").unwrap();
        writeln!(
            c,
            "extern void cg_result_{mode}_{name}({c_fn_param}const {name}*,{c_lane}*);"
        )
        .unwrap();
    }
    writeln!(main, "{{{name} got=cg_make_{name}(&a);calls++;").unwrap();
    for lane in 0..*lanes {
        writeln!(
            main,
            "check_bytes(\"{name}/return/lane{lane}\",&{},&bits{}[data][{lane}],sizeof({c_lane}));",
            shape.member("got", lane),
            shape.bytes
        )
        .unwrap();
    }
    writeln!(main, "}}").unwrap();
    for mode in ["direct", "indirect"] {
        let farg = if mode == "indirect" {
            format!("c_make_{name},")
        } else {
            String::new()
        };
        writeln!(
            main,
            "{{struct {{uint64_t before;{c_lane} data[4];uint64_t after;}} ob={{CANARY1,{{0}},CANARY2}};{c_lane}*out=ob.data;cg_result_{mode}_{name}({farg}&a,out);calls++;"
        )
        .unwrap();
        for lane in 0..*lanes {
            writeln!(main, "check_bytes(\"{name}/result-{mode}/lane{lane}\",&out[{lane}],&bits{}[data][{lane}],sizeof({c_lane}));", shape.bytes).unwrap();
        }
        writeln!(
            main,
            "check_canaries(\"{name}/result-{mode}/out\",&ob.before,&ob.after);"
        )
        .unwrap();
        for lane in *lanes..4 {
            writeln!(main, "check_bytes(\"{name}/result-{mode}/unused-out{lane}\",&out[{lane}],&ZERO,sizeof(out[0]));").unwrap();
        }
        writeln!(main, "}}").unwrap();
    }
}

/// Exercise the checked scalarized-formal WRITE route, then both kinds of
/// reads: the nested float leaf and the whole HFA returned across the C ABI.
/// The existing read-only argument/result matrix remains separately counted.
fn nested_formal_mutation(shape: &Shape, rust: &mut String, c: &mut String, main: &mut String) {
    assert_eq!((shape.lanes, shape.form), (1, 1));
    let Shape {
        name,
        rust_lane,
        c_lane,
        bytes,
        ..
    } = shape;
    writeln!(rust, "#[unsafe(no_mangle)] pub extern \"C\" fn cg_mutate_return_{name}(mut a:{name},value:{rust_lane})->{name}{{a.inner.a0=value;a}}").unwrap();
    writeln!(rust, "#[unsafe(no_mangle)] pub extern \"C\" fn cg_mutate_read_{name}(mut a:{name},value:{rust_lane})->{rust_lane}{{a.inner.a0=value;a.inner.a0}}").unwrap();
    writeln!(c, "extern {name} cg_mutate_return_{name}({name},{c_lane});\nextern {c_lane} cg_mutate_read_{name}({name},{c_lane});").unwrap();
    writeln!(main, "{{struct {{uint64_t before;{name} data;uint64_t after;}} input={{CANARY1,{{0}},CANARY2}},returned={{CANARY1,{{0}},CANARY2}};struct {{uint64_t before;{c_lane} data;uint64_t after;}} scalar={{CANARY1,0,CANARY2}};const {c_lane} original=-21.5;{c_lane} replacement;").unwrap();
    writeln!(main, "memcpy(&input.data.inner.a0,&original,{bytes});memcpy(&replacement,&bits{bytes}[data][pattern],{bytes});returned.data=cg_mutate_return_{name}(input.data,replacement);calls++;scalar.data=cg_mutate_read_{name}(input.data,replacement);calls++;").unwrap();
    for (label, actual, expected) in [
        (
            "whole-return",
            "returned.data.inner.a0",
            format!("bits{bytes}[data][pattern]"),
        ),
        (
            "scalar-read",
            "scalar.data",
            format!("bits{bytes}[data][pattern]"),
        ),
        (
            "input-unchanged",
            "input.data.inner.a0",
            "original".to_owned(),
        ),
        (
            "replacement-unchanged",
            "replacement",
            format!("bits{bytes}[data][pattern]"),
        ),
    ] {
        writeln!(
            main,
            "check_bytes(\"{name}/mutation/{label}\",&{actual},&{expected},{bytes});"
        )
        .unwrap();
    }
    for buffer in ["input", "returned", "scalar"] {
        writeln!(
            main,
            "check_canaries(\"{name}/mutation/{buffer}\",&{buffer}.before,&{buffer}.after);"
        )
        .unwrap();
    }
    writeln!(main, "}}").unwrap();
}

struct CorpusCounts {
    matrix_calls: usize,
    matrix_checks: usize,
    mutation_calls: usize,
    mutation_checks: usize,
}

impl CorpusCounts {
    fn calls(&self) -> usize {
        self.matrix_calls + self.mutation_calls
    }
    fn checks(&self) -> usize {
        self.matrix_checks + self.mutation_checks
    }
    fn stdout(&self) -> String {
        format!(
            "PASS calls={} checks={} matrix_calls={} matrix_checks={} mutation_calls={} mutation_checks={}\n",
            self.calls(),
            self.checks(),
            self.matrix_calls,
            self.matrix_checks,
            self.mutation_calls,
            self.mutation_checks
        )
    }
}

fn corpus() -> (String, String, CorpusCounts) {
    let mut rust = "#![no_std]\n#![allow(non_camel_case_types,non_snake_case)]\n".to_owned();
    let mut c = r#"#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static const uint64_t GUARD=UINT64_C(0xd3a59c276b18e04f);
static const uint64_t CANARY1=UINT64_C(0x75182ab3c69def04),CANARY2=UINT64_C(0xb4e69d721ac3580f),ZERO=0;
static unsigned calls,checks;
static void check_bytes(const char*name,const void*actual,const void*expected,size_t n){
 checks++;
 if(memcmp(actual,expected,n)){
  fprintf(stderr,"FAIL %s check=%u actual=",name,checks);
  for(size_t i=0;i<n;i++)fprintf(stderr,"%02x",((const unsigned char*)actual)[i]);
  fprintf(stderr," expected=");
  for(size_t i=0;i<n;i++)fprintf(stderr,"%02x",((const unsigned char*)expected)[i]);
  fputc('\n',stderr);exit(1);
 }
}
static void check_canaries(const char*name,const uint64_t*before,const uint64_t*after){
 check_bytes(name,before,&CANARY1,8);check_bytes(name,after,&CANARY2,8);
}
static const uint32_t bits4[4][4]={
 {0x3fa00000,0xc0200000,0x40700000,0xc0880000},
 {0x80000000,0x00000000,0x7f800000,0xff800000},
 {0x7fc12345,0xffc54321,0x3f000001,0xbf000003},
 {0x00800001,0x80800003,0x00000001,0x80000001}};
static const uint64_t bits8[4][4]={
 {UINT64_C(0x3ff4000000000000),UINT64_C(0xc004000000000000),UINT64_C(0x400e000000000000),UINT64_C(0xc011000000000000)},
 {UINT64_C(0x8000000000000000),0,UINT64_C(0x7ff0000000000000),UINT64_C(0xfff0000000000000)},
 {UINT64_C(0x7ff8123456789abc),UINT64_C(0xfff8543210fedcba),UINT64_C(0x3fe0000000000001),UINT64_C(0xbfe0000000000003)},
 {UINT64_C(0x0010000000000001),UINT64_C(0x8010000000000003),1,UINT64_C(0x8000000000000001)}};
"#.to_owned();
    let mut main = format!("int main(void){{for(unsigned data=0;data<{DATASETS};data++){{\n");
    let mut checks = 0;
    let mut calls = 0;
    for shape in shapes() {
        declarations(&shape, &mut rust, &mut c);
        writeln!(main, "{{{} a;", shape.name).unwrap();
        for lane in 0..shape.lanes {
            writeln!(
                main,
                "memcpy(&{},&bits{}[data][{lane}],{});",
                shape.member("a", lane),
                shape.bytes,
                shape.bytes
            )
            .unwrap();
        }
        for prefix in PREFIXES {
            consumer(&shape, prefix, &mut rust, &mut c, &mut main);
            // All written values, six surrounding canaries, and every unused
            // output/sentinel element: twenty byte-value checks per call.
            checks += 3 * 20;
            calls += 3;
        }
        returned(&shape, &mut rust, &mut c, &mut main);
        checks += shape.lanes + 2 * 6;
        calls += 3;
        writeln!(main, "}}").unwrap();
    }
    checks *= DATASETS;
    calls *= DATASETS;
    assert_eq!(
        (calls, checks),
        (1152, 18672),
        "retain every original matrix case"
    );
    writeln!(main, "}}if(calls!={calls}||checks!={checks})return 2;const unsigned matrix_calls=calls,matrix_checks=checks;for(unsigned data=0;data<{DATASETS};data++){{for(unsigned pattern=0;pattern<4;pattern++){{").unwrap();
    let mut mutation_shapes = 0;
    for shape in shapes()
        .into_iter()
        .filter(|shape| shape.lanes == 1 && shape.form == 1)
    {
        nested_formal_mutation(&shape, &mut rust, &mut c, &mut main);
        mutation_shapes += 1;
    }
    assert_eq!(
        mutation_shapes, 2,
        "both f32 and f64 nested formals are required"
    );
    let counts = CorpusCounts {
        matrix_calls: calls,
        matrix_checks: checks,
        mutation_calls: mutation_shapes * DATASETS * 4 * 2,
        mutation_checks: mutation_shapes * DATASETS * 4 * 10,
    };
    writeln!(main, "}}}}const unsigned mutation_calls=calls-matrix_calls,mutation_checks=checks-matrix_checks;if(mutation_calls!={}||mutation_checks!={})return 3;printf(\"PASS calls=%u checks=%u matrix_calls=%u matrix_checks=%u mutation_calls=%u mutation_checks=%u\\n\",calls,checks,matrix_calls,matrix_checks,mutation_calls,mutation_checks);return 0;}}", counts.mutation_calls, counts.mutation_checks).unwrap();
    c.push_str(&main);
    (rust, c, counts)
}

#[test]
fn c_fnabi_hfa_all_members_both_directions_and_llvm_twin() {
    assert!(
        cfg!(all(
            target_arch = "aarch64",
            target_os = "linux",
            target_env = "gnu"
        )),
        "this required target executes only on native Linux GNU AArch64"
    );
    for name in [
        "TCG_NO_PROOF_CERTS",
        "TCG_JIT_UNCHECKED",
        "TCG_OPT_LEVEL",
        "TRUST_CG_DISABLE_PASSES",
        "TRUST_CG_DISABLE_CFGSIMPLIFY_SUBPASSES",
        "TCG_DATAFLOW_INTEGRITY",
    ] {
        assert!(
            std::env::var_os(name).is_none(),
            "qualification rejects {name}"
        );
    }
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-c-fnabi-linux.XXXXXX"])
        .output()
        .expect("mktemp artifacts");
    assert!(temp.status.success());
    let artifacts_dir = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let artifacts = artifacts_dir.0.clone();
    eprintln!("native bridge ABI artifacts: {}", artifacts.display());
    let host = checked(
        toolchain_support::rustc_driver_command().arg("-vV"),
        30,
        &artifacts.join("rustc.log"),
    );
    assert!(
        String::from_utf8_lossy(&host.stdout)
            .lines()
            .any(|line| line == format!("host: {TARGET}"))
    );
    let (backend, digest) = backend(&artifacts);
    let runtime = scalar_cell_runtime::Runtime::build(&artifacts);
    let unsupported = rejected_boundaries(&artifacts, &backend);
    let mut scalar_native = zst_sibling_cell_promoted(&artifacts, &backend, &digest, &runtime);
    scalar_native.extend(scalar_cell_boundaries(
        &artifacts, &backend, &digest, &runtime,
    ));
    let projected = projected_cell_case();
    let (rust, c, counts) = corpus();
    std::fs::write(artifacts.join("corpus.rs"), rust).unwrap();
    std::fs::write(artifacts.join("driver.c"), c).unwrap();
    for opt in 0..=3 {
        for compiler in ["llvm", "cg"] {
            let stem = format!("{compiler}_O{opt}");
            let object_dir = artifacts.join(&stem);
            std::fs::create_dir(&object_dir).unwrap();
            let mut command = rustc_command();
            command.args([
                "--crate-type=lib",
                "--emit=obj",
                "-Cpanic=abort",
                "--target",
                TARGET,
            ]);
            command.arg(format!("-Copt-level={opt}"));
            if compiler == "cg" {
                command.arg(format!("-Zcodegen-backend={}", backend.display()));
            }
            command
                .arg(artifacts.join("corpus.rs"))
                .arg("--out-dir")
                .arg(&object_dir);
            checked(
                &mut command,
                180,
                &artifacts.join(format!("{stem}.compile.log")),
            );
            // This backend may emit one .rcgu.o per CGU instead of rustc's
            // requested single object. Link every freshly emitted object from
            // this unique empty directory, never a stale artifact/glob.
            let mut objects = std::fs::read_dir(&object_dir)
                .unwrap()
                .map(|entry| entry.unwrap().path())
                .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
                .collect::<Vec<_>>();
            objects.sort();
            assert!(!objects.is_empty(), "compiler produced no object files");
            let executable = artifacts.join(format!("{stem}.elf"));
            let mut linker = Command::new("cc");
            linker
                .arg(format!("-O{opt}"))
                .arg("-std=c11")
                .arg(artifacts.join("driver.c"))
                .args(&objects);
            runtime.link_into(&mut linker);
            checked(
                linker.arg("-o").arg(&executable),
                60,
                &artifacts.join(format!("{stem}.link.log")),
            );
            let elf = checked(
                Command::new("readelf").arg("-h").arg(&executable),
                10,
                &artifacts.join(format!("{stem}.elf.log")),
            );
            let elf = String::from_utf8_lossy(&elf.stdout);
            assert!(elf.contains("ELF64") && elf.contains("AArch64"));
            let output = checked(
                &mut Command::new(&executable),
                20,
                &artifacts.join(format!("{stem}.native.log")),
            );
            assert_eq!(String::from_utf8(output.stdout).unwrap(), counts.stdout());
            assert!(output.stderr.is_empty());
            assert_eq!(
                sha256(&backend),
                digest,
                "backend changed during native qualification"
            );
        }
    }
    println!(
        "\nTCG_BRIDGE_NATIVE_EXECUTION {{\"target\":\"{TARGET}\",\"opt_levels\":[0,1,2,3],\"executions\":8,\"calls\":{},\"checks\":{},\"matrix_calls\":{},\"matrix_checks\":{},\"mutation_calls\":{},\"mutation_checks\":{},\"refusals\":{},\"projected_cell_controls\":4,\"projected_cell_refusals\":0,\"projected_cell_native_executions\":8,\"projected_cell_native_calls\":{},\"projected_cell_native_checks\":{},\"scalar_cell\":{{\"schema\":1,\"native\":[{}],\"unsupported\":[{}]}},\"backend_sha256\":\"{digest}\"}}",
        counts.calls() * 8,
        counts.checks() * 8,
        counts.matrix_calls * 8,
        counts.matrix_checks * 8,
        counts.mutation_calls * 8,
        counts.mutation_checks * 8,
        unsupported.len(),
        projected.calls * 8,
        projected.checks * 8,
        scalar_native.join(","),
        unsupported.join(","),
    );
}

#[path = "support/fat_reference_returns.rs"]
mod fat_reference_returns;

#[path = "support/atomic128_loads.rs"]
mod atomic128_loads;

#[path = "support/u128_carrying_mul.rs"]
mod u128_carrying_mul;

#[path = "support/option_aggregate_map.rs"]
mod option_aggregate_map;

#[path = "support/borrowed_aggregate_captures.rs"]
mod borrowed_aggregate_captures;

#[path = "support/scalar_cell_returns.rs"]
mod scalar_cell_returns;

#[path = "support/overflow_loop_threading.rs"]
mod overflow_loop_threading;

#[path = "support/projected_aggregate_borrows.rs"]
mod projected_aggregate_borrows;

#[path = "support/raw_reference_storage.rs"]
mod raw_reference_storage;

#[path = "support/captured_closure_storage.rs"]
mod captured_closure_storage;
