// trust-cg-codegen/tests/aarch64_function_target_features.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Per-function target features, the modeled AArch64 feature vocabulary and
//! runtime feature dispatch (ledger L03-P9), executed on this host.
//!
//! * Host truth: the Darwin `hw.optional.arm.FEAT_*` resolution equals the
//!   standard library's detection, and on the qualifying Apple M4 Max every
//!   modeled feature is present.
//! * A function that states `lse` selects LSE atomics under the baseline
//!   profile while its attribute-free twin in the same module keeps the LL/SC
//!   loop; both execute and agree with C11 `<stdatomic.h>`. `fp16` likewise
//!   admits half-precision arithmetic in the stating function only.
//! * `llvm.aarch64.crc32*` selects one CRC32 instruction in a function that
//!   states `crc` and a shift/XOR expansion in one that does not (on every
//!   profile, the Apple AOT contract included); both agree with the
//!   LLVM-compiled intrinsic (`core::arch::aarch64::__crc32*`) and a
//!   bit-serial reference over edge and pseudo-random inputs. The CRC32 rows
//!   carry no value obligation and block proof promotion.
//! * Runtime dispatch reads the host features and chooses the feature-gated
//!   variant here, the baseline fallback on a host view without the feature.
//! * Refusals: an unmodeled feature is refused by name on every entry.
//!
//! Instruction words are read from the emitted code, not from the compiler's
//! own decoder. All of this is native testing evidence, not a proof.
#![cfg(all(target_arch = "aarch64", target_os = "macos"))]

#[path = "common/rosetta.rs"]
mod process;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::collections::HashMap;
use std::fs;
use std::process::Command;

use trust_cg_codegen::aarch64_dispatch::{
    AArch64DispatchError, AArch64FeatureDispatch, AArch64FeatureSet, AArch64FeatureSource,
    aarch64_host_features, darwin_hw_optional, resolve_aarch64_features,
    std_detected_aarch64_features,
};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig, PipelineError};
use trust_cg_codegen::target::{AArch64IsaFeature, AArch64IsaProfile, TargetSpec};
use trust_cg_codegen::{Compiler, CompilerConfig, Target};
use trust_ir::{AtomicRMWOp, BinOp, ICmpOp, Module, Ordering, Ty};
use trust_ir_build::{ModuleBuilder, validate_module};

const TRIPLE: &str = "aarch64-apple-darwin";
const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn target_info() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: TRIPLE.into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}

/// Give the function named `name` the stated target features.
fn state_features(module: &mut Module, name: &str, features: &[&str]) {
    let function = module
        .functions
        .iter_mut()
        .find(|function| function.name == name)
        .unwrap_or_else(|| panic!("no function `{name}`"));
    function.attrs.target_features = features.iter().map(|f| (*f).to_owned()).collect();
}

// ---------------------------------------------------------------------------
// Instruction-word classes (Arm ARM encodings, independent of the compiler)
// ---------------------------------------------------------------------------

/// CRC32{B,H,W,X} / CRC32C{B,H,W,X}: `sf 0011010110 Rm 010 C sz Rn Rd`.
fn crc32_word(word: u32) -> Option<(bool, u32)> {
    (word & 0x7fe0_e000 == 0x1ac0_4000).then_some(((word >> 12) & 1 == 1, (word >> 10) & 0b11))
}

/// LSE CAS family or atomic memory operations (LDADD/LDCLR/.../SWP).
fn is_lse(word: u32) -> bool {
    word & 0x3fa0_7c00 == 0x08a0_7c00 || word & 0x3f20_0c00 == 0x3820_0000
}

/// Single-register load/store exclusive (LDXR/LDAXR/STXR/STLXR).
fn is_exclusive(word: u32) -> bool {
    word & 0x3fa0_7c00 == 0x0800_7c00
}

/// FADD (scalar) on H registers: `00011110 11 1 Rm 001010 Rn Rd`.
fn is_fadd_h(word: u32) -> bool {
    word & 0xffe0_fc00 == 0x1ee0_2800
}

fn words(code: &[u8]) -> Vec<u32> {
    assert_eq!(code.len() % 4, 0);
    code.as_chunks::<4>()
        .0
        .iter()
        .map(|word| u32::from_le_bytes(*word))
        .collect()
}

/// Instruction words of each symbol of a JIT image, bounded by the next
/// higher symbol offset (the last by the code length). A symbol and its
/// Mach-O `_` alias share one offset.
fn jit_function_words(
    buffer: &trust_cg_codegen::jit::ExecutableBuffer,
) -> HashMap<String, Vec<u32>> {
    let code = buffer.code_slice();
    let mut starts: Vec<u64> = buffer.symbol_offsets().values().copied().collect();
    starts.sort_unstable();
    starts.dedup();
    buffer
        .symbol_offsets()
        .iter()
        .map(|(name, &start)| {
            let end = starts
                .iter()
                .copied()
                .find(|&offset| offset > start)
                .unwrap_or(buffer.code_len() as u64);
            (name.clone(), words(&code[start as usize..end as usize]))
        })
        .collect()
}

/// The single text section of a one-function Mach-O object.
fn object_words(object: &[u8]) -> Vec<u32> {
    const LC_SEGMENT_64: u32 = 0x19;
    let at32 = |at: usize| u32::from_le_bytes(object[at..at + 4].try_into().unwrap());
    let at64 = |at: usize| u64::from_le_bytes(object[at..at + 8].try_into().unwrap());
    assert_eq!(at32(0), 0xfeed_facf, "MH_MAGIC_64");
    let mut command = 32;
    for _ in 0..at32(16) {
        if at32(command) == LC_SEGMENT_64 {
            for section in 0..at32(command + 64) as usize {
                let header = command + 72 + section * 80;
                if &object[header..header + 7] == b"__text\0" {
                    let size = at64(header + 40) as usize;
                    let offset = at32(header + 48) as usize;
                    return words(&object[offset..offset + size]);
                }
            }
        }
        command += at32(command + 4) as usize;
    }
    panic!("no __text section");
}

// ---------------------------------------------------------------------------
// Host truth
// ---------------------------------------------------------------------------

/// The Darwin sysctl resolution is the process's host report, agrees with
/// the standard library's detection for every feature it names, and reads a
/// key that exists for every modeled feature. On the qualifying Apple M4 Max
/// (the host `docs/darwin-aarch64-completion.md` records) every modeled
/// feature is present.
#[test]
fn darwin_sysctl_resolution_is_the_host_truth() {
    let host = aarch64_host_features();
    assert_eq!(host.source(), AArch64FeatureSource::DarwinSysctl);
    let resolved = resolve_aarch64_features(darwin_hw_optional);
    assert_eq!(host.features(), resolved);
    for feature in AArch64IsaFeature::ALL {
        for key in feature.darwin_sysctl_keys() {
            assert!(
                darwin_hw_optional(key).is_some(),
                "{feature:?}: this kernel has no `{key}`"
            );
        }
    }
    let flagm2 = AArch64FeatureSet::from_aarch64_features([AArch64IsaFeature::FlagM2]);
    assert_eq!(
        std_detected_aarch64_features(),
        resolved.difference(flagm2),
        "std detection must agree with the sysctls (it has no flagm2 name)"
    );
    assert!(AArch64IsaProfile::APPLE_ARM64.is_supported_by_host());
    let brand = Command::new("/usr/sbin/sysctl")
        .args(["-n", "machdep.cpu.brand_string"])
        .output()
        .expect("run sysctl");
    let brand = String::from_utf8_lossy(&brand.stdout).trim().to_owned();
    eprintln!("host {brand}: {:?}", host.names());
    if brand == "Apple M4 Max" {
        assert_eq!(
            host.names(),
            AArch64IsaFeature::ALL.map(AArch64IsaFeature::name),
            "the recorded M4 Max implements every modeled feature"
        );
    }
}

// ---------------------------------------------------------------------------
// Per-function LSE and FP16 under the baseline profile (AOT, linked, run)
// ---------------------------------------------------------------------------

/// `fetch_add_{lse,base}(p, v) -> old` and `cas_{lse,base}(p, e, d) -> old`,
/// all SeqCst on u64; the `_lse` twins state `lse`.
fn atomics_module() -> Module {
    let mut m = ModuleBuilder::new_with_target_info("per_function_lse", target_info());
    let rmw = m.add_func_type(vec![Ty::PtrMut(Box::new(Ty::U64)), Ty::U64], vec![Ty::U64]);
    let cas = m.add_func_type(
        vec![Ty::PtrMut(Box::new(Ty::U64)), Ty::U64, Ty::U64],
        vec![Ty::U64],
    );
    for name in ["fetch_add_lse", "fetch_add_base"] {
        let mut f = m.function(name, rmw);
        let entry = f.create_block();
        let pointer = f.add_block_param(entry, Ty::PtrMut(Box::new(Ty::U64)));
        let value = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let old = f.atomic_rmw(AtomicRMWOp::Add, Ty::U64, pointer, value, Ordering::SeqCst);
        f.ret(vec![old]);
        f.build();
    }
    for name in ["cas_lse", "cas_base"] {
        let mut f = m.function(name, cas);
        let entry = f.create_block();
        let pointer = f.add_block_param(entry, Ty::PtrMut(Box::new(Ty::U64)));
        let expected = f.add_block_param(entry, Ty::U64);
        let desired = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let (old, _) = f.cmpxchg(
            Ty::U64,
            pointer,
            expected,
            desired,
            Ordering::SeqCst,
            Ordering::SeqCst,
        );
        f.ret(vec![old]);
        f.build();
    }
    let mut module = m.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), []);
    state_features(&mut module, "fetch_add_lse", &["neon", "lse"]);
    state_features(&mut module, "cas_lse", &["lse"]);
    module
}

fn baseline_pipeline(opt_level: OptLevel) -> Pipeline {
    Pipeline::new(PipelineConfig {
        opt_level,
        target_triple: TRIPLE.into(),
        ..PipelineConfig::default()
    })
    .with_aarch64_isa_profile(AArch64IsaProfile::BASELINE)
}

/// One object per function, compiled through a baseline-profile pipeline.
fn compile_each(module: &Module, pipeline: &Pipeline) -> Vec<(String, Vec<u8>)> {
    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect("module translates");
    lowered
        .iter()
        .map(|(function, _)| {
            let object = pipeline
                .compile_function(function)
                .unwrap_or_else(|error| panic!("{}: {error}", function.name));
            (function.name.clone(), object)
        })
        .collect()
}

/// Link `objects` with a C `driver` and run it; the scratch directory is
/// removed on success and kept for inspection on failure.
fn link_and_run(tag: &str, objects: &[(String, Vec<u8>)], driver: &str) -> String {
    let root = fresh_dir::create(&format!("trust-cg-l03p9-{tag}-"));
    let driver_path = root.join("driver.c");
    fs::write(&driver_path, driver).unwrap();
    let mut link = Command::new("/usr/bin/clang");
    link.args(["-O1", "-std=c11"]).arg(&driver_path);
    for (index, (_, object)) in objects.iter().enumerate() {
        let path = root.join(format!("f{index}.o"));
        fs::write(&path, object).unwrap();
        link.arg(path);
    }
    let executable = root.join("driver");
    link.arg("-o").arg(&executable);
    let linked =
        process::command_output_with_timeout(&mut link, process::codegen_link_timeout()).unwrap();
    assert!(
        !linked.timed_out && linked.output.status.success(),
        "{tag}: link failed in {}: {}",
        root.display(),
        String::from_utf8_lossy(&linked.output.stderr)
    );
    let run =
        process::run_executable_with_timeout(&executable, process::codegen_run_timeout()).unwrap();
    let stdout = String::from_utf8_lossy(&run.output.stdout).into_owned();
    assert!(
        !run.timed_out && run.output.status.success(),
        "{tag}: native run failed in {}: {stdout}{}",
        root.display(),
        String::from_utf8_lossy(&run.output.stderr)
    );
    fs::remove_dir_all(root).unwrap();
    stdout
}

const ATOMICS_DRIVER: &str = r#"
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
typedef uint64_t u64;
u64 fetch_add_lse(u64 *, u64); u64 fetch_add_base(u64 *, u64);
u64 cas_lse(u64 *, u64, u64); u64 cas_base(u64 *, u64, u64);
static const u64 V[] = {0, 1, 2, 0x7fffffffffffffffULL, 0x8000000000000000ULL,
  0xfffffffffffffffeULL, 0xffffffffffffffffULL, 0xa5a55a5a0f0ff0f0ULL};
#define N (sizeof V / sizeof V[0])
int main(void) {
  unsigned long cases = 0;
  u64 (*adds[2])(u64 *, u64) = {fetch_add_lse, fetch_add_base};
  u64 (*cass[2])(u64 *, u64, u64) = {cas_lse, cas_base};
  for (int k = 0; k < 2; k++)
  for (unsigned i = 0; i < N; i++) for (unsigned j = 0; j < N; j++) {
    _Atomic u64 oracle = V[i]; u64 want_old = atomic_fetch_add(&oracle, V[j]);
    u64 cell = V[i]; u64 old = adds[k](&cell, V[j]); cases++;
    if (old != want_old || cell != atomic_load(&oracle)) { printf("add k=%d i=%u j=%u\n", k, i, j); return 1; }
    for (unsigned d = 0; d < N; d++) {
      _Atomic u64 o2 = V[i]; u64 seen = V[j];
      atomic_compare_exchange_strong(&o2, &seen, V[d]);
      u64 c2 = V[i]; u64 got = cass[k](&c2, V[j], V[d]); cases++;
      if (got != seen || c2 != atomic_load(&o2)) { printf("cas k=%d i=%u j=%u d=%u\n", k, i, j, d); return 1; }
    }
  }
  printf("ok %lu\n", cases);
  return 0;
}
"#;

/// Under the BASELINE profile, the function stating `lse` emits LSE words
/// and no exclusive loop; its attribute-free twin emits the LL/SC loop and no
/// LSE word. Both link into one executable and agree with C11 atomics.
#[test]
fn stated_lse_selects_lse_only_in_the_stating_function_and_both_execute() {
    let module = atomics_module();
    for opt_level in OPT_LEVELS {
        let pipeline = baseline_pipeline(opt_level);
        assert_eq!(pipeline.aarch64_isa_profile(), AArch64IsaProfile::BASELINE);
        let objects = compile_each(&module, &pipeline);
        for (name, object) in &objects {
            let words = object_words(object);
            let lse = words.iter().filter(|word| is_lse(**word)).count();
            let exclusive = words.iter().filter(|word| is_exclusive(**word)).count();
            if name.ends_with("_lse") {
                assert!(
                    lse == 1 && exclusive == 0,
                    "{opt_level:?} {name}: {lse} LSE / {exclusive} exclusive words"
                );
            } else {
                assert!(
                    lse == 0 && exclusive == 2,
                    "{opt_level:?} {name}: {lse} LSE / {exclusive} exclusive words"
                );
            }
        }
        let out = link_and_run(&format!("lse-{opt_level:?}"), &objects, ATOMICS_DRIVER);
        assert_eq!(out.trim(), "ok 1152", "{opt_level:?}");
    }
}

fn half_module() -> Module {
    let mut m = ModuleBuilder::new_with_target_info("per_function_fp16", target_info());
    let sig = m.add_func_type(vec![Ty::F16, Ty::F16], vec![Ty::F16]);
    for name in ["half_add_fp16", "half_add_base"] {
        let mut f = m.function(name, sig);
        let entry = f.create_block();
        let a = f.add_block_param(entry, Ty::F16);
        let b = f.add_block_param(entry, Ty::F16);
        f.switch_to_block(entry);
        let sum = f.binop(BinOp::FAdd, Ty::F16, a, b);
        f.ret(vec![sum]);
        f.build();
    }
    let mut module = m.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), []);
    state_features(&mut module, "half_add_fp16", &["fp16"]);
    module
}

/// FEAT_FP16 scalar arithmetic is admitted by the function's own `fp16`
/// under the baseline profile; the attribute-free twin is refused by the
/// feature's name (the baseline has no FP16 arithmetic and no widening
/// fallback is selected silently). The admitted function executes.
#[test]
fn stated_fp16_admits_half_arithmetic_only_in_the_stating_function() {
    let module = half_module();
    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect("translates");
    let pipeline = baseline_pipeline(OptLevel::O2);
    let mut admitted = Vec::new();
    for (function, _) in &lowered {
        match pipeline.compile_function(function) {
            Ok(object) => {
                assert_eq!(function.name, "half_add_fp16");
                let words = object_words(&object);
                assert_eq!(
                    words.iter().filter(|word| is_fadd_h(**word)).count(),
                    1,
                    "one FADD H"
                );
                admitted.push((function.name.clone(), object));
            }
            Err(error) => {
                assert_eq!(function.name, "half_add_base");
                let text = error.to_string();
                assert!(text.contains("FP16"), "{text}");
            }
        }
    }
    let out = link_and_run(
        "fp16",
        &admitted,
        r#"
#include <stdio.h>
_Float16 half_add_fp16(_Float16, _Float16);
int main(void) {
  _Float16 a = (_Float16)1.5, b = (_Float16)2.25;
  if (half_add_fp16(a, b) != (_Float16)3.75) { printf("bad\n"); return 1; }
  if (half_add_fp16((_Float16)65504.0, (_Float16)65504.0) != (_Float16)__builtin_inff()) { printf("inf\n"); return 1; }
  printf("ok\n");
  return 0;
}
"#,
    );
    assert_eq!(out.trim(), "ok");
}

// ---------------------------------------------------------------------------
// CRC32 intrinsics: feature instruction vs baseline expansion (JIT)
// ---------------------------------------------------------------------------

const CRC_FORMS: [(&str, u32, bool); 8] = [
    ("crc32b", 0b00, false),
    ("crc32h", 0b01, false),
    ("crc32w", 0b10, false),
    ("crc32x", 0b11, false),
    ("crc32cb", 0b00, true),
    ("crc32ch", 0b01, true),
    ("crc32cw", 0b10, true),
    ("crc32cx", 0b11, true),
];

/// For each form, `hw_<form>(crc, data)` stating `crc` and `sw_<form>`
/// without it, each one call of `llvm.aarch64.<form>`.
fn crc_module() -> Module {
    let mut m = ModuleBuilder::new_with_target_info("per_function_crc", target_info());
    let sig32 = m.add_func_type(vec![Ty::U32, Ty::U32], vec![Ty::U32]);
    let sig64 = m.add_func_type(vec![Ty::U32, Ty::U64], vec![Ty::U32]);
    let mut intrinsics = Vec::new();
    for (form, sz, _) in CRC_FORMS {
        let sig = if sz == 0b11 { sig64 } else { sig32 };
        intrinsics.push((
            form,
            sz,
            sig,
            m.declare_function(format!("llvm.aarch64.{form}"), sig),
        ));
    }
    for (form, sz, sig, intrinsic) in intrinsics {
        let data_ty = if sz == 0b11 { Ty::U64 } else { Ty::U32 };
        for prefix in ["hw", "sw"] {
            let mut f = m.function(format!("{prefix}_{form}"), sig);
            let entry = f.create_block();
            let crc = f.add_block_param(entry, Ty::U32);
            let data = f.add_block_param(entry, data_ty.clone());
            f.switch_to_block(entry);
            let out = f.call(intrinsic, vec![crc, data]);
            f.ret(vec![out]);
            f.build();
        }
    }
    let mut module = m.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), []);
    for (form, _, _) in CRC_FORMS {
        state_features(&mut module, &format!("hw_{form}"), &["crc"]);
    }
    module
}

/// Bit-serial reflected CRC over the low `bits` of `data` (the Arm ARM
/// `CRC32()` definition), independent of every implementation under test.
fn crc_reference(mut crc: u32, data: u64, bits: u32, castagnoli: bool) -> u32 {
    let poly = if castagnoli { 0x82f6_3b78 } else { 0xedb8_8320 };
    for bit in 0..bits {
        let input = ((data >> bit) & 1) as u32;
        let mix = (crc ^ input) & 1;
        crc = (crc >> 1) ^ if mix == 1 { poly } else { 0 };
    }
    crc
}

/// The LLVM-compiled intrinsic (this test binary is built by trustc's LLVM
/// backend), the differential oracle.
fn crc_llvm(form: &str, crc: u32, data: u64) -> u32 {
    use std::arch::aarch64::*;
    assert!(std::arch::is_aarch64_feature_detected!("crc"));
    // SAFETY: the host implements FEAT_CRC32 (asserted above).
    unsafe {
        match form {
            "crc32b" => __crc32b(crc, data as u8),
            "crc32h" => __crc32h(crc, data as u16),
            "crc32w" => __crc32w(crc, data as u32),
            "crc32x" => __crc32d(crc, data),
            "crc32cb" => __crc32cb(crc, data as u8),
            "crc32ch" => __crc32ch(crc, data as u16),
            "crc32cw" => __crc32cw(crc, data as u32),
            "crc32cx" => __crc32cd(crc, data),
            other => panic!("{other}"),
        }
    }
}

fn crc_inputs() -> Vec<(u32, u64)> {
    let mut inputs = Vec::new();
    for crc in [0, 1, 0xffff_ffff, 0x8000_0000, 0xdead_beef] {
        for data in [
            0,
            1,
            0xff,
            0x100,
            0xffff,
            0xffff_ffff,
            0x1_0000_0000,
            u64::MAX,
            0x8000_0000_0000_0000,
            0x0123_4567_89ab_cdef,
        ] {
            inputs.push((crc, data));
        }
    }
    let mut state = 0x9e37_79b9_7f4a_7c15_u64;
    for _ in 0..500 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let crc = (state >> 32) as u32;
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        inputs.push((crc, state));
    }
    inputs
}

/// `hw_*` emits exactly one CRC32 word of its form and `sw_*` none, at every
/// optimization level, through the in-process JIT (whose profile does not
/// admit `crc`: the hardware form comes from the function's own feature).
/// Both agree with the LLVM intrinsic and the bit-serial reference.
#[test]
fn crc32_intrinsics_select_crc32_only_where_crc_is_stated_and_agree_with_llvm() {
    let module = crc_module();
    let inputs = crc_inputs();
    for opt_level in OPT_LEVELS {
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = opt_level;
        let result = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        let buffer = result.buffer;
        let function_words = jit_function_words(&buffer);
        for (form, sz, castagnoli) in CRC_FORMS {
            let hw: Vec<_> = function_words[&format!("hw_{form}")]
                .iter()
                .filter_map(|word| crc32_word(*word))
                .collect();
            assert_eq!(hw, [(castagnoli, sz)], "{opt_level:?} hw_{form}");
            let sw = function_words[&format!("sw_{form}")]
                .iter()
                .filter(|word| crc32_word(**word).is_some())
                .count();
            assert_eq!(sw, 0, "{opt_level:?} sw_{form} must not emit CRC32");
            eprintln!(
                "{opt_level:?} {form}: hw {} words, sw {} words",
                function_words[&format!("hw_{form}")].len(),
                function_words[&format!("sw_{form}")].len()
            );
            let bits = 8 << sz;
            for prefix in ["hw", "sw"] {
                let name = format!("{prefix}_{form}");
                for &(crc, data) in &inputs {
                    let got = if sz == 0b11 {
                        type F = extern "C" fn(u32, u64) -> u32;
                        // SAFETY: exact C signature of the compiled function.
                        let f = unsafe { buffer.get_fn_bound::<F>(&name) }.unwrap();
                        f.as_ref()(crc, data)
                    } else {
                        type F = extern "C" fn(u32, u32) -> u32;
                        // SAFETY: exact C signature of the compiled function.
                        let f = unsafe { buffer.get_fn_bound::<F>(&name) }.unwrap();
                        f.as_ref()(crc, data as u32)
                    };
                    let reference = crc_reference(crc, data, bits, castagnoli);
                    assert_eq!(crc_llvm(form, crc, data), reference, "{form} oracle");
                    assert_eq!(got, reference, "{opt_level:?} {name}({crc:#x}, {data:#x})");
                }
            }
        }
    }
}

/// A serialized copy of a buffer whose functions state `crc` carries it in
/// its target contract (`serialized_target_contract`), so replay checks this
/// CPU implements it; the republished stated function runs and agrees with
/// the reference. A contract naming an unmodeled feature is refused before
/// anything is mapped.
#[test]
fn serialized_replay_names_the_stated_features_in_its_contract() {
    use trust_cg_codegen::jit::{JitError, publish_serialized_buffer_for_target};
    use trust_cg_codegen::jit_contract::TargetDescriptor;
    use trust_cg_codegen::target::TargetFeatureSet;

    let crc = TargetFeatureSet::from_aarch64_features([AArch64IsaFeature::Crc]);
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = OptLevel::O1;
    let buffer = Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(&crc_module(), &HashMap::new())
        .unwrap()
        .buffer;
    assert_eq!(buffer.aarch64_function_target_features(), crc);
    let contract = buffer.serialized_target_contract();
    let host = TargetDescriptor::for_trust_cg_host_jit();
    assert!(!host.features.iter().any(|feature| feature == "crc"));
    let mut without_crc = contract.clone();
    without_crc.features.retain(|feature| feature != "crc");
    assert_eq!(
        without_crc, host,
        "the contract is the host-JIT one plus crc"
    );

    let republish = |contract: &TargetDescriptor| {
        // SAFETY: the bytes and symbol table are exactly those this test
        // compiled for this host a moment ago, under `contract` (or a
        // contract the call must refuse before mapping anything).
        unsafe {
            publish_serialized_buffer_for_target(
                buffer.code_slice(),
                buffer.canonical_symbols().to_vec(),
                buffer.symbol_offsets().clone(),
                buffer.function_ranges().to_vec(),
                contract,
            )
        }
        .map_err(Box::new)
    };
    let replayed = republish(&contract).expect("this CPU implements crc");
    assert_eq!(replayed.aarch64_function_target_features(), crc);
    assert_eq!(replayed.code_slice(), buffer.code_slice());
    type F = extern "C" fn(u32, u64) -> u32;
    // SAFETY: exact C signature of the compiled function.
    let hw = unsafe { replayed.get_fn_bound::<F>("hw_crc32cx") }.unwrap();
    for (seed, data) in crc_inputs().into_iter().take(64) {
        assert_eq!(
            hw.as_ref()(seed, data),
            crc_reference(seed, data, 64, true),
            "replayed hw_crc32cx({seed:#x}, {data:#x})"
        );
    }

    let mut unmodeled = contract.clone();
    unmodeled.features.push("sve".to_owned());
    let unmodeled = unmodeled.clone().with_features(unmodeled.features);
    let refused = republish(&unmodeled).expect_err("`sve` is not a modeled feature");
    assert!(
        matches!(*refused, JitError::SerializedBufferTargetMismatch { .. }),
        "{refused}"
    );
}

/// The Apple AOT contract does not admit `crc` module-wide, so an
/// attribute-free function lowers the intrinsic to the expansion there too,
/// and the stating function to one CRC32 word.
#[test]
fn apple_aot_selects_crc32_only_in_functions_that_state_it() {
    let module = crc_module();
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O2,
        target_triple: TRIPLE.into(),
        ..PipelineConfig::default()
    });
    assert_eq!(
        pipeline.aarch64_isa_profile(),
        AArch64IsaProfile::APPLE_ARM64
    );
    for (name, object) in compile_each(&module, &pipeline) {
        let crc = object_words(&object)
            .iter()
            .filter(|word| crc32_word(**word).is_some())
            .count();
        let want = usize::from(name.starts_with("hw_"));
        assert_eq!(crc, want, "{name}");
    }
}

/// The eight CRC32 forms are credited by the opcode coverage gate only as
/// accepted regression evidence: each form's decoded-word obligation
/// (`aarch64_crc32_proofs`) is decided in process for every register value,
/// which is testing grade, so the function verifier reports a holding CRC32
/// instruction UNVERIFIED and a proof-required consumer still refuses a body
/// that selected one. The native agreement above is testing evidence only.
///
/// The assertions read the gate's own classification and audit rows, and a
/// credited control (`AddRR`, `EorRR`, `SubRR`) runs through the same row
/// assertions; the walk over the eight instructions must name the CRC32
/// obligation and credit none of them, so the test fails if a CRC32 row is
/// ever credited as proof without this file changing.
#[test]
fn crc32_words_block_proof_promotion() {
    use trust_cg_ir::inst::AArch64Opcode as O;
    use trust_cg_verify::aarch64_crc32_proofs::{
        CRC32_DECIDED_IS_NOT_CREDIT, Crc32Form, representative_instruction,
    };
    use trust_cg_verify::coverage_gate::{
        CoverageGate, GateArch, OpcodeClass, aarch64_deferred_value_op_reason, classify_aarch64,
    };
    use trust_cg_verify::function_verifier::{InstructionVerificationResult, verify_function};
    let crc = [
        O::Crc32B,
        O::Crc32H,
        O::Crc32W,
        O::Crc32X,
        O::Crc32Cb,
        O::Crc32Ch,
        O::Crc32Cw,
        O::Crc32Cx,
    ];
    let credited = [O::AddRR, O::EorRR, O::SubRR];
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(move || {
            let report = CoverageGate::new().audit(GateArch::AArch64);
            let row = |opcode: O| {
                let display = format!("AArch64::{opcode:?}");
                report
                    .rows
                    .iter()
                    .find(|row| row.opcode_display == display)
                    .unwrap_or_else(|| panic!("{display} has no coverage-gate row"))
                    .clone()
            };
            for opcode in crc.into_iter().chain(credited) {
                assert_eq!(
                    classify_aarch64(opcode),
                    OpcodeClass::EmittableNeedsProof,
                    "{opcode:?}"
                );
                assert_eq!(aarch64_deferred_value_op_reason(opcode), None, "{opcode:?}");
                let row = row(opcode);
                assert!(!row.is_failure(), "{opcode:?} must be accepted: {row:?}");
            }
            for opcode in crc {
                let note = row(opcode).note;
                assert!(
                    note.contains("CRC32 DECODED-WORD") && note.contains("NOT a formal proof"),
                    "{opcode:?}: {note}"
                );
            }
            let mut function = trust_cg_ir::MachFunction::new(
                "crc32_walk".into(),
                trust_cg_ir::Signature::new(vec![], vec![]),
            );
            for form in Crc32Form::ALL {
                let id = function.push_inst(representative_instruction(form, 3, 4, 5));
                function.append_inst(function.entry, id);
            }
            let walk = verify_function(&function);
            assert_eq!(walk.instructions.len(), crc.len());
            for row in &walk.instructions {
                match &row.result {
                    InstructionVerificationResult::Unverified { reason } => {
                        assert!(reason.starts_with(CRC32_DECIDED_IS_NOT_CREDIT), "{reason}");
                    }
                    other => panic!("a CRC32 instruction must not be credited: {other:?}"),
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

// ---------------------------------------------------------------------------
// Runtime dispatch
// ---------------------------------------------------------------------------

/// `checksum_{fast,base}(words: *const u64, n: u64, seed: u32) -> u32`: a
/// CRC32C loop over `n` doublewords; `checksum_fast` states `crc`.
fn dispatch_module() -> Module {
    let mut m = ModuleBuilder::new_with_target_info("feature_dispatch", target_info());
    let step = m.add_func_type(vec![Ty::U32, Ty::U64], vec![Ty::U32]);
    let crc32cx = m.declare_function("llvm.aarch64.crc32cx", step);
    let sig = m.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::U32], vec![Ty::U32]);
    for name in ["checksum_fast", "checksum_base"] {
        let mut f = m.function(name, sig);
        let entry = f.create_block();
        let words = f.add_block_param(entry, Ty::Ptr);
        let n = f.add_block_param(entry, Ty::U64);
        let seed = f.add_block_param(entry, Ty::U32);
        let head = f.create_block();
        let i = f.add_block_param(head, Ty::U64);
        let crc = f.add_block_param(head, Ty::U32);
        let body = f.create_block();
        let exit = f.create_block();
        let result = f.add_block_param(exit, Ty::U32);
        f.switch_to_block(entry);
        let zero = f.iconst(Ty::U64, 0);
        f.br(head, vec![zero, seed]);
        f.switch_to_block(head);
        let done = f.icmp(ICmpOp::Eq, Ty::U64, i, n);
        f.condbr(done, exit, vec![crc], body, vec![]);
        f.switch_to_block(body);
        let address = f.gep(Ty::U64, words, vec![i]);
        let word = f.load(Ty::U64, address);
        let next = f.call(crc32cx, vec![crc, word]);
        let one = f.iconst(Ty::U64, 1);
        let i_next = f.add(Ty::U64, i, one);
        f.br(head, vec![i_next, next]);
        f.switch_to_block(exit);
        f.ret(vec![result]);
        f.build();
    }
    let mut module = m.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), []);
    state_features(&mut module, "checksum_fast", &["crc"]);
    module
}

/// The dispatch reads each variant's requirement from its own stated
/// features, chooses `checksum_fast` on this host (which implements `crc`)
/// and `checksum_base` on a host view without `crc`; both chosen paths
/// execute from the JIT image and agree with the reference.
#[test]
fn runtime_dispatch_chooses_the_fast_path_here_and_the_fallback_without_crc() {
    let module = dispatch_module();
    let dispatch =
        AArch64FeatureDispatch::from_trust_ir_module(&module, &["checksum_fast"], "checksum_base")
            .expect("dispatch builds from the stated features");
    let crc = AArch64FeatureSet::from_aarch64_features([AArch64IsaFeature::Crc]);
    assert_eq!(dispatch.variants()[0].required(), crc);

    let host = aarch64_host_features();
    assert!(host.implements(AArch64IsaFeature::Crc), "this host has crc");
    let here = dispatch.select_for_host();
    assert_eq!((here.symbol, here.variant), ("checksum_fast", Some(0)));
    let without_crc = dispatch.select(host.features().difference(crc));
    assert_eq!(without_crc.symbol, "checksum_base");
    assert!(without_crc.is_baseline());

    let data: Vec<u64> = (0..257_u64)
        .map(|k| k.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ (k << 7))
        .collect();
    let reference = data.iter().fold(0xffff_ffff_u32, |crc, word| {
        crc_reference(crc, *word, 64, true)
    });
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = opt_level;
        let buffer = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
            .buffer;
        let function_words = jit_function_words(&buffer);
        for choice in [here, without_crc] {
            let crc_words = function_words[choice.symbol]
                .iter()
                .filter(|word| crc32_word(**word).is_some())
                .count();
            assert_eq!(
                crc_words,
                usize::from(!choice.is_baseline()),
                "{}",
                choice.symbol
            );
            type F = extern "C" fn(*const u64, u64, u32) -> u32;
            // SAFETY: exact C signature; the chosen variant's features are
            // implemented by this host (the dispatch's contract).
            let f = unsafe { buffer.get_fn_bound::<F>(choice.symbol) }.unwrap();
            let got = f.as_ref()(data.as_ptr(), data.len() as u64, 0xffff_ffff);
            assert_eq!(got, reference, "{opt_level:?} {}", choice.symbol);
        }
    }
}

/// A baseline that states a feature is not a fallback; a variant that
/// states none gates nothing; a missing body and a repeated symbol are
/// refused.
#[test]
fn dispatch_construction_refuses_malformed_variant_sets() {
    let module = dispatch_module();
    assert!(matches!(
        AArch64FeatureDispatch::from_trust_ir_module(&module, &["checksum_base"], "checksum_fast"),
        Err(AArch64DispatchError::BaselineStatesFeatures { features, .. }) if features == ["crc"]
    ));
    let mut twin = module.clone();
    state_features(&mut twin, "checksum_fast", &[]);
    assert!(matches!(
        AArch64FeatureDispatch::from_trust_ir_module(&twin, &["checksum_fast"], "checksum_base"),
        Err(AArch64DispatchError::VariantStatesNoFeature { .. })
    ));
    assert!(matches!(
        AArch64FeatureDispatch::from_trust_ir_module(&module, &["missing"], "checksum_base"),
        Err(AArch64DispatchError::MissingFunction { .. })
    ));
    assert!(matches!(
        AArch64FeatureDispatch::from_trust_ir_module(&module, &["checksum_base"], "checksum_base"),
        Err(AArch64DispatchError::DuplicateSymbol { .. })
    ));
    let mut unmodeled = module;
    state_features(&mut unmodeled, "checksum_fast", &["crc", "sve2"]);
    assert!(matches!(
        AArch64FeatureDispatch::from_trust_ir_module(
            &unmodeled,
            &["checksum_fast"],
            "checksum_base"
        ),
        Err(AArch64DispatchError::UnmodeledFeature { feature, .. }) if feature == "sve2"
    ));
}

// ---------------------------------------------------------------------------
// Refusals
// ---------------------------------------------------------------------------

/// An unmodeled feature is refused by its name on the AOT compiler and the
/// in-process JIT (the adapter floor), including features this CPU has but
/// the backend does not model (`bti`, `paca`) and another architecture's.
#[test]
fn unmodeled_features_are_refused_by_name_on_every_entry() {
    for feature in ["sve2", "bti", "paca", "mte", "avx2", "+crc", "CRC"] {
        let mut module = crc_module();
        state_features(&mut module, "hw_crc32b", &["crc", feature]);
        let aot = Compiler::new_for_target_spec(
            CompilerConfig::default(),
            TargetSpec::parse(TRIPLE).unwrap(),
        )
        .with_codegen_license(permit_unlicensed())
        .compile(&module)
        .err()
        .unwrap_or_else(|| panic!("AOT accepted `{feature}`"))
        .to_string();
        assert!(aot.contains(feature), "AOT `{feature}`: {aot}");
        let jit = Compiler::new(CompilerConfig::jit_fast(Target::Aarch64))
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &HashMap::new())
            .err()
            .unwrap_or_else(|| panic!("JIT accepted `{feature}`"))
            .to_string();
        assert!(jit.contains(feature), "JIT `{feature}`: {jit}");
    }
}

/// The pipeline re-checks an LIR function's stated features itself, so a
/// function that reached it without the adapter floor is refused by name.
#[test]
fn the_pipeline_refuses_an_unmodeled_feature_on_raw_lir() {
    let module = crc_module();
    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect("translates");
    let (mut function, _) = lowered
        .into_iter()
        .find(|(function, _)| function.name == "sw_crc32w")
        .unwrap();
    function.target_features = vec!["neon".into(), "mte".into()];
    let error = baseline_pipeline(OptLevel::O0)
        .compile_function(&function)
        .expect_err("mte is not modeled");
    assert!(
        matches!(
            &error,
            PipelineError::Aarch64FunctionTargetFeature { function, feature, .. }
                if function == "sw_crc32w" && feature == "mte"
        ),
        "{error}"
    );
}

/// An intrinsic declared with a signature other than LLVM's is refused, not
/// guessed.
#[test]
fn a_misdeclared_crc32_intrinsic_is_refused() {
    let mut m = ModuleBuilder::new_with_target_info("bad_crc", target_info());
    let sig = m.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let intrinsic = m.declare_function("llvm.aarch64.crc32w", sig);
    let mut f = m.function("bad", sig);
    let entry = f.create_block();
    let a = f.add_block_param(entry, Ty::U64);
    let b = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let out = f.call(intrinsic, vec![a, b]);
    f.ret(vec![out]);
    f.build();
    let module = m.build().expect("ModuleBuilder::build: test fixture");
    let error = Compiler::new_for_target_spec(
        CompilerConfig::default(),
        TargetSpec::parse(TRIPLE).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&module)
    .expect_err("a (u64, u64) -> u64 crc32w is not LLVM's intrinsic")
    .to_string();
    assert!(error.contains("TCG-CRC32-INTRINSIC"), "{error}");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
