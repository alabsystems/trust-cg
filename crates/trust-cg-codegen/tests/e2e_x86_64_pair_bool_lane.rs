// trust-cg-codegen/tests/e2e_x86_64_pair_bool_lane.rs - the bool lane of a pair call
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// A `bool` lane of a call that returns two scalars defines bit 0 of its byte
// alone. rustc returns a `ScalarPair` as the LLVM struct `{ T, i1 }` (or
// `{ i1, T }`) with no `zeroext`, so LLVM any-extends the lane: measured with
// trustc stage-1 (d7f143f3b, LLVM 22.1.2) on x86_64-apple-darwin at -O3,
//
//   fn gb(x: u64) -> (u64, bool) { (x, transmute::<u8, bool>(x as u8 & 1)) }
//
// is `movq %rdi, %rax; movl %eax, %edx; retq`, leaving bits 1..7 of DL as
// those of `x`, and the `(bool, u64)` twin leaves AL = x. The callees below are
// exactly those instruction sequences, and `bg` is the LLVM callee of a `bool`
// argument (`fn bg(b: bool) -> u64 { b as u64 }` is `movl %edi, %eax`, relying
// on the caller's clean 32-bit bool). trust-cg callers compiled at every
// optimization level must see only bit 0 of the lane, wherever they use it:
// widened, forwarded in a pair, passed as a `bool` argument, or stored.
//
// Host: x86-64 (macOS or Linux) with a C compiler to link the driver.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::Ty;
use trust_ir_build::ModuleBuilder;

fn host_enabled() -> bool {
    if !cfg!(target_arch = "x86_64") {
        eprintln!("SKIP: the pair bool-lane link-and-run test needs an x86-64 host");
        return false;
    }
    let cc = Command::new("cc")
        .arg("--version")
        .output()
        .is_ok_and(|output| output.status.success());
    if !cc {
        eprintln!("SKIP: cc not available");
    }
    cc
}

/// The trust-ir callers of the pair callees `gb: u64 -> (u64, bool)` and
/// `gf: u64 -> (bool, u64)`.
fn module() -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("e2e_x86_64_pair_bool_lane");
    let gb_ty = builder.add_func_type(vec![Ty::U64], vec![Ty::U64, Ty::Bool]);
    let gb = builder.declare_function("gb", gb_ty);
    let gf_ty = builder.add_func_type(vec![Ty::U64], vec![Ty::Bool, Ty::U64]);
    let gf = builder.declare_function("gf", gf_ty);
    let bg_ty = builder.add_func_type(vec![Ty::Bool], vec![Ty::U64]);
    let bg = builder.declare_function("bg", bg_ty);
    let u64_to_u64 = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);

    // pb_lane1(x) = gb(x).1 as u64
    let mut f = builder.function("pb_lane1", u64_to_u64);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let [_, lane] = f.call_results::<2>(gb, vec![x]);
    let widened = f.zext(Ty::Bool, Ty::U64, lane);
    f.ret(vec![widened]);
    f.build();

    // pb_lane0(x) = gf(x).0 as u64
    let mut f = builder.function("pb_lane0", u64_to_u64);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let [lane, _] = f.call_results::<2>(gf, vec![x]);
    let widened = f.zext(Ty::Bool, Ty::U64, lane);
    f.ret(vec![widened]);
    f.build();

    // pb_forward(x) = gb(x)
    let forward_ty = builder.add_func_type(vec![Ty::U64], vec![Ty::U64, Ty::Bool]);
    let mut f = builder.function("pb_forward", forward_ty);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let [first, lane] = f.call_results::<2>(gb, vec![x]);
    f.ret(vec![first, lane]);
    f.build();

    // pb_argument(x) = bg(gb(x).1)
    let mut f = builder.function("pb_argument", u64_to_u64);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let [_, lane] = f.call_results::<2>(gb, vec![x]);
    let result = f.call(bg, vec![lane]);
    f.ret(vec![result]);
    f.build();

    // pb_store(p, x) { *p = gb(x).1 }
    let store_ty = builder.add_func_type(vec![Ty::PtrMut(Box::new(Ty::Bool)), Ty::U64], vec![]);
    let mut f = builder.function("pb_store", store_ty);
    let entry = f.create_block();
    let p = f.add_block_param(entry, Ty::PtrMut(Box::new(Ty::Bool)));
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let [_, lane] = f.call_results::<2>(gb, vec![x]);
    f.store(Ty::Bool, p, lane);
    f.ret(vec![]);
    f.build();

    builder.build().expect("ModuleBuilder::build: test fixture")
}

/// The callees, as the instruction sequences LLVM emits for them (header),
/// and a driver that checks every caller against `x & 1`.
const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>

#ifdef __APPLE__
#define SYM(name) "_" #name
#else
#define SYM(name) #name
#endif

__asm__(".text\n"
        ".globl " SYM(gb) "\n" SYM(gb) ":\n"
        "  movq %rdi, %rax\n  movl %eax, %edx\n  retq\n"
        ".globl " SYM(gf) "\n" SYM(gf) ":\n"
        "  movq %rdi, %rax\n  movq %rdi, %rdx\n  retq\n"
        ".globl " SYM(bg) "\n" SYM(bg) ":\n"
        "  movl %edi, %eax\n  retq\n");

struct pair { uint64_t first; uint64_t second; };

extern uint64_t pb_lane1(uint64_t);
extern uint64_t pb_lane0(uint64_t);
extern struct pair pb_forward(uint64_t);
extern uint64_t pb_argument(uint64_t);
extern void pb_store(uint8_t *, uint64_t);

int main(void) {
    static const uint64_t xs[] = {0, 1, 2, 3, 0x7e, 0x7f, 0x80, 0xfe, 0xff,
                                  0x100, 0x1ff, 0xdeadbeef, 0xffffffffffffffffull};
    int wrong = 0;
    for (unsigned i = 0; i < sizeof xs / sizeof xs[0]; i++) {
        uint64_t x = xs[i];
        uint64_t want = x & 1;
        uint64_t lane1 = pb_lane1(x);
        uint64_t lane0 = pb_lane0(x);
        struct pair forward = pb_forward(x);
        uint64_t argument = pb_argument(x);
        uint8_t stored = 0xaa;
        pb_store(&stored, x);
        /* The backend returns a bool lane as a clean 32-bit bool in EDX. */
        uint32_t forwarded = (uint32_t)forward.second;
        if (lane1 != want || lane0 != want || forward.first != x || forwarded != want
            || argument != want || stored != want) {
            printf("x=0x%llx want=%llu lane1=%llu lane0=%llu forward=(0x%llx,%u) "
                   "argument=%llu stored=%u\n",
                   (unsigned long long)x, (unsigned long long)want,
                   (unsigned long long)lane1, (unsigned long long)lane0,
                   (unsigned long long)forward.first, forwarded,
                   (unsigned long long)argument, stored);
            wrong++;
        }
    }
    printf("wrong=%d\n", wrong);
    return wrong == 0 ? 0 : 1;
}
"#;

fn run_at(opt_level: OptLevel, dir: &std::path::Path) -> Result<(), String> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level,
        target: Target::X86_64,
        emit_proofs: false,
        parallel: false,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed());
    let result = compiler
        .compile(&module())
        .map_err(|error| format!("{opt_level:?}: compile: {error}"))?;
    let object = dir.join(format!("pair_bool_lane_{opt_level:?}.o"));
    fs::write(&object, &result.object_code).map_err(|error| error.to_string())?;
    let driver = dir.join("driver.c");
    fs::write(&driver, DRIVER).map_err(|error| error.to_string())?;
    let binary = dir.join(format!("pair_bool_lane_{opt_level:?}"));
    let mut link = Command::new("cc");
    if cfg!(target_os = "macos") {
        link.args(["-arch", "x86_64"]);
    }
    let link = link
        .arg("-O0")
        .arg("-o")
        .arg(&binary)
        .arg(&driver)
        .arg(&object)
        .output()
        .map_err(|error| format!("{opt_level:?}: cc: {error}"))?;
    if !link.status.success() {
        return Err(format!(
            "{opt_level:?}: link failed: {}",
            String::from_utf8_lossy(&link.stderr)
        ));
    }
    let run = Command::new(&binary)
        .output()
        .map_err(|error| format!("{opt_level:?}: run: {error}"))?;
    let stdout = String::from_utf8_lossy(&run.stdout);
    eprintln!("{opt_level:?}: {}", stdout.trim());
    if run.status.success() && stdout.trim_end().ends_with("wrong=0") {
        return Ok(());
    }
    let (disassembler, flag) = if cfg!(target_os = "macos") {
        ("otool", "-tv")
    } else {
        ("objdump", "-d")
    };
    let disassembly = Command::new(disassembler)
        .arg(flag)
        .arg(&object)
        .output()
        .map(|output| String::from_utf8_lossy(&output.stdout).into_owned())
        .unwrap_or_default();
    Err(format!(
        "{opt_level:?}: a caller used bits 1..7 of a pair call's bool lane:\n{stdout}\n{disassembly}"
    ))
}

#[test]
fn a_bool_lane_of_a_pair_call_is_bit_zero_at_every_opt_level() {
    if !host_enabled() {
        return;
    }
    let dir: PathBuf = std::env::temp_dir().join(format!(
        "trust_cg_e2e_x86_64_pair_bool_lane_{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create the test directory");
    let failures: Vec<String> = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3]
        .into_iter()
        .filter_map(|opt_level| run_at(opt_level, &dir).err())
        .collect();
    let _ = fs::remove_dir_all(&dir);
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// This file's fixture is hand-built and carries no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compile states `Permit` explicitly, so the test
/// never passes (or fails by name) because it was silently refused. The test
/// runs only on an x86-64 host, so a Darwin AArch64 landing never sees it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
