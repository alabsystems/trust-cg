// Copyright 2026 Andrew Yates | Apache-2.0
//! Real compiler-captured signed IR, lowered through the full codegen pipeline.
//! Native comparisons are implementation checks, not verification certificates.
#[path = "common/a64_interp.rs"]
mod a64;
#[path = "common/rosetta.rs"]
mod process;

use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};
use trust_cg_codegen::{Compiler, CompilerConfig, pipeline::OptLevel, target::TargetSpec};
use trust_cg_lower::{CodegenLicensePolicy, UnlicensedBodyPolicy};
use trust_ir::{CallingConv, Module};

const MODEL: &str = include_str!("fixtures/darwin_signed_tail/module.json");
const DRIVER: &str = include_str!("fixtures/darwin_signed_tail/driver.c");
const OBSERVE: &str = include_str!("fixtures/darwin_signed_tail/observe.S");
const BASELINE: &[u8] = include_bytes!("fixtures/darwin_signed_tail/baseline.o");

fn compile(module: &Module, opt_level: OptLevel) -> Vec<u8> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            emit_proofs: false,
            emit_debug: false,
            parallel: false,
            panic_unwind: false,
            never_inline: ["trust_c_i8_not".into(), "trust_c_i16_not".into()].into(),
            ..CompilerConfig::default()
        },
        TargetSpec::parse("aarch64-apple-darwin").unwrap(),
    )
    .with_codegen_license(
        CodegenLicensePolicy::default()
            .with_recognized_authority("trust-direct-lane-structural")
            .with_unlicensed(UnlicensedBodyPolicy::Permit),
    )
    .compile(module)
    .expect("captured module codegen")
    .object_code
}

fn check_wrappers(object: &[u8], tail: bool, population: usize) -> serde_json::Value {
    let text = a64::extract_text(object);
    let symbols = a64::symbol_addrs(object);
    let starts: std::collections::BTreeSet<_> = symbols
        .iter()
        .filter(|(n, _)| n.starts_with("_trust_c_i"))
        .map(|(_, v)| *v)
        .collect();
    assert_eq!(
        starts.len(),
        population,
        "complete emitted function population"
    );
    let targets = a64::text_branch_relocs(object);
    let mut rows = vec![];
    for width in [8, 16] {
        let name = format!("_trust_c_i{width}_tail");
        let start = *symbols.get(&name).expect("wrapper symbol");
        let end = starts
            .range((std::ops::Bound::Excluded(start), std::ops::Bound::Unbounded))
            .next()
            .copied()
            .unwrap_or(text.addr + text.bytes.len() as u64);
        let words: Vec<u32> = text.bytes[(start - text.addr) as usize..(end - text.addr) as usize]
            .as_chunks::<4>()
            .0
            .iter()
            .map(|b| u32::from_le_bytes(*b))
            .collect();
        let calls: Vec<_> = words
            .iter()
            .enumerate()
            .filter(|(_, w)| **w & 0xfc00_0000 == 0x9400_0000)
            .collect();
        let tails: Vec<_> = words
            .iter()
            .enumerate()
            .filter(|(_, w)| **w & 0xfc00_0000 == 0x1400_0000)
            .collect();
        assert_eq!(calls.len(), usize::from(!tail), "{name}: {words:08x?}");
        assert_eq!(tails.len(), usize::from(tail), "{name}: {words:08x?}");
        if tail {
            assert!(!words.contains(&0xd65f03c0), "true tail has no return");
        }
        let site = (start - text.addr) as usize + 4 * if tail { tails[0].0 } else { calls[0].0 };
        let callee = symbols.get(&format!("_trust_c_i{width}_not")).unwrap();
        assert_eq!(
            targets.get(&site),
            Some(&((*callee - text.addr) as usize)),
            "exact named callee relocation"
        );
        rows.push(serde_json::json!({"name":name,"words":words,"site":site,"tail":tail}));
    }
    serde_json::json!(rows)
}

fn output(name: &str) -> (PathBuf, Option<tempfile::TempDir>) {
    if let Some(root) = std::env::var_os("TRUST_CG_SIGNED_TAIL_OUTPUT_DIR") {
        let p = PathBuf::from(root).join(name);
        fs::create_dir_all(&p).unwrap();
        (p, None)
    } else {
        let d = tempfile::tempdir().unwrap();
        (d.path().to_path_buf(), Some(d))
    }
}
fn native(dir: &Path, object: &[u8], driver: &str, extra_asm: &str) {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        return;
    }
    fs::write(dir.join("module.o"), object).unwrap();
    fs::write(dir.join("driver.c"), driver).unwrap();
    fs::write(dir.join("observe.S"), format!("{OBSERVE}\n{extra_asm}")).unwrap();
    let bin = dir.join("native");
    let result = process::command_output_with_timeout(
        Command::new("/usr/bin/cc")
            .args(["-O2", "-Wall", "-Wextra", "-Werror"])
            .arg(dir.join("driver.c"))
            .arg(dir.join("observe.S"))
            .arg(dir.join("module.o"))
            .arg("-o")
            .arg(&bin),
        process::codegen_link_timeout(),
    )
    .unwrap();
    fs::write(dir.join("link.stderr"), &result.output.stderr).unwrap();
    assert!(
        !result.timed_out && result.output.status.success(),
        "{}",
        String::from_utf8_lossy(&result.output.stderr)
    );
    let result =
        process::run_executable_with_timeout(&bin, process::codegen_run_timeout()).unwrap();
    fs::write(dir.join("native.stdout"), &result.output.stdout).unwrap();
    fs::write(dir.join("native.stderr"), &result.output.stderr).unwrap();
    assert!(
        !result.timed_out && result.output.status.success(),
        "native {}: {} {}",
        result.output.status,
        String::from_utf8_lossy(&result.output.stdout),
        String::from_utf8_lossy(&result.output.stderr)
    );
}
#[test]
fn actual_signed_eight_function_module_emits_real_tail_transfers_and_preserves_w0() {
    let module: Module = serde_json::from_str(MODEL).unwrap();
    assert_eq!(module.functions.len(), 8);
    let (base, _hold) = output("captured-eight");
    fs::write(
        base.join("old-o3-shapes.json"),
        serde_json::to_vec_pretty(&check_wrappers(BASELINE, false, 8)).unwrap(),
    )
    .unwrap();
    for (opt, name, tail) in [(OptLevel::O0, "O0", false), (OptLevel::O3, "O3", true)] {
        let object = compile(&module, opt);
        let dir = base.join(name);
        fs::create_dir(&dir).unwrap();
        fs::write(
            dir.join("shapes.json"),
            serde_json::to_vec_pretty(&check_wrappers(&object, tail, 8)).unwrap(),
        )
        .unwrap();
        native(&dir, &object, DRIVER, "");
    }
}
#[test]
fn weaker_rust_result_keeps_sign_extension_and_ordinary_call() {
    let mut module: Module = serde_json::from_str(MODEL).unwrap();
    module
        .functions
        .retain(|f| f.name.ends_with("_tail") || f.name.ends_with("_not"));
    for f in &mut module.functions {
        if f.name.ends_with("_not") {
            f.calling_conv = CallingConv::Rust;
            f.blocks.clear();
            f.value_names = None;
        }
    }
    let object = compile(&module, OptLevel::O3);
    // Bodyless callees have symbol values zero: inspect the two real wrappers
    // independently of the same-object target check used for the positive.
    let text = a64::extract_text(&object);
    let calls = text
        .bytes
        .as_chunks::<4>()
        .0
        .iter()
        .filter(|b| u32::from_le_bytes(**b) & 0xfc00_0000 == 0x9400_0000)
        .count();
    let tails = text
        .bytes
        .as_chunks::<4>()
        .0
        .iter()
        .filter(|b| u32::from_le_bytes(**b) & 0xfc00_0000 == 0x1400_0000)
        .count();
    assert_eq!((calls, tails), (2, 0));
    let (dir, _hold) = output("weaker-rust");
    native(
        &dir,
        &object,
        r#"#include <stdint.h>
extern int8_t trust_c_i8_tail(int8_t);extern int16_t trust_c_i16_tail(int16_t);
extern uint32_t observe_signed_w0(uintptr_t,uint64_t);
int main(void){return observe_signed_w0((uintptr_t)trust_c_i8_tail,0x1234567800000000ULL)!=0xffffff80U || observe_signed_w0((uintptr_t)trust_c_i16_tail,0xabcdef0100000000ULL)!=0xffff8000U;}
"#,
        r#".text
.globl _trust_c_i8_not
_trust_c_i8_not:
 mov w0,#128
 ret
.globl _trust_c_i16_not
_trust_c_i16_not:
 mov w0,#32768
 ret
"#,
    );
}
