// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Linux AArch64 execution of B1 sign extension, including the I128 low-half
//! repair. LLVM's `sext i1` is the control: true means -1, unlike a Rust bool
//! cast. Each copied I128 object also restores the old low-half Copy selection;
//! it must link and pass false, then fail true with a value mismatch.
//! Set LLVM_LLC to the native LLVM `llc` executable. No proof credit is claimed.

#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]

mod common;

use std::fs;
use std::path::Path;
use std::process::Command;

use common::rosetta::{
    codegen_link_timeout, codegen_run_timeout, command_output_with_timeout,
    run_executable_with_timeout,
};
use sha2::{Digest, Sha256};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::Ty;
use trust_ir_build::ModuleBuilder;

fn module(width: u32) -> trust_ir::Module {
    let to = match width {
        32 => Ty::I32,
        64 => Ty::I64,
        128 => Ty::I128,
        _ => panic!("unsupported fixture width"),
    };
    let mut builder = ModuleBuilder::new("native_bool_sign_extension");
    let ty = builder.add_func_type(vec![Ty::Bool], vec![to.clone()]);
    let mut f = builder.function("cg_sext", ty);
    let block = f.create_block();
    let b = f.add_block_param(block, Ty::Bool);
    f.switch_to_block(block);
    let wide = f.sext(Ty::Bool, to, b);
    f.ret(vec![wide]);
    f.build();
    let mut module = builder.build().expect("valid bool sign-extension fixture");
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    module
}

fn compile(module: &trust_ir::Module, opt_level: OptLevel) -> Vec<u8> {
    // Hand-written IR has no source license. This is a native differential,
    // with the same explicit fixture admission as the other native suites.
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap(),
    )
    .with_codegen_license(
        trust_cg_lower::CodegenLicensePolicy::default()
            .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
    )
    .compile(module)
    .expect("bool sign extension must compile")
    .object_code
}

fn checked(command: &mut Command) -> std::process::Output {
    let result = command_output_with_timeout(command, codegen_link_timeout())
        .expect("qualification command must launch");
    assert!(
        !result.timed_out && result.output.status.success(),
        "{command:?}: {}\n{}",
        result.output.status,
        String::from_utf8_lossy(&result.output.stderr)
    );
    result.output
}

/// This ELF contains exactly one function. Change its sole bit-0 SBFM Xd,Xn
/// into MOV Xd,Xn, the previous I128 low-half selection. Keep the destination
/// and source registers, all metadata, and the following ASR high-half step.
fn old_low_half_selection(object: &[u8]) -> Vec<u8> {
    let u16_at = |i| u16::from_le_bytes(object[i..i + 2].try_into().unwrap());
    let u64_at = |i| u64::from_le_bytes(object[i..i + 8].try_into().unwrap());
    assert_eq!(&object[..6], b"\x7fELF\x02\x01");
    assert_eq!(u16_at(16), 1, "relocatable object required");
    assert_eq!(u16_at(18), 183, "AArch64 object required");
    assert_eq!(u16_at(58), 64);
    let section_headers = usize::try_from(u64_at(40)).unwrap();
    let mut matches = Vec::new();
    for i in 0..usize::from(u16_at(60)) {
        let section = section_headers + i * 64;
        if u64_at(section + 8) & 4 == 0 {
            continue;
        }
        let start = usize::try_from(u64_at(section + 24)).unwrap();
        let size = usize::try_from(u64_at(section + 32)).unwrap();
        assert_eq!(size % 4, 0);
        for offset in (start..start + size).step_by(4) {
            let word = u32::from_le_bytes(object[offset..offset + 4].try_into().unwrap());
            if word & 0xffff_fc00 == 0x9340_0000 {
                matches.push((offset, word));
            }
        }
    }
    assert_eq!(
        matches.len(),
        1,
        "exactly one low-half bit-0 sign extension required"
    );
    let (offset, original) = matches[0];
    let source = (original >> 5) & 31;
    let destination = original & 31;
    let copy = 0xaa00_03e0 | (source << 16) | destination;
    let mut mutant = object.to_vec();
    mutant[offset..offset + 4].copy_from_slice(&copy.to_le_bytes());
    eprintln!("old-selection mutation offset={offset} word={original:08x}->{copy:08x}");
    mutant
}

fn link_run(directory: &Path, object: &[u8], tag: &str, width: u32, expected_exit: i32) {
    let cg = directory.join(format!("{tag}.o"));
    let binary = directory.join(tag);
    fs::write(&cg, object).unwrap();
    checked(
        Command::new("cc")
            .arg("-O2")
            .arg(directory.join("driver.c"))
            .arg(&cg)
            .arg(directory.join("reference.o"))
            .arg("-o")
            .arg(&binary),
    );
    let run = run_executable_with_timeout(&binary, codegen_run_timeout()).unwrap();
    assert!(!run.timed_out, "{tag}: native execution timed out");
    assert_eq!(
        run.output.status.code(),
        Some(expected_exit),
        "{tag}, I{width}: stdout={} stderr={}",
        String::from_utf8_lossy(&run.output.stdout),
        String::from_utf8_lossy(&run.output.stderr)
    );
    let stdout = String::from_utf8(run.output.stdout).unwrap();
    assert!(
        stdout.contains("b=0 match"),
        "false must still match: {stdout}"
    );
    if expected_exit == 0 {
        assert!(stdout.contains("b=1 match"), "true must match: {stdout}");
    } else {
        assert!(
            stdout.contains("b=1 mismatch"),
            "must kill a value mismatch: {stdout}"
        );
    }
}

#[test]
fn bool_sign_extension_matches_llvm_and_kills_the_old_i128_selection() {
    let llc = std::env::var_os("LLVM_LLC").unwrap_or_else(|| "llc".into());
    let version = checked(Command::new(&llc).arg("--version"));
    eprintln!("LLVM control: {}", String::from_utf8_lossy(&version.stdout));
    if Path::new(&llc).is_absolute() {
        eprintln!(
            "LLVM llc SHA256: {:x}",
            Sha256::digest(fs::read(&llc).unwrap())
        );
    }
    let mut cells = 0;
    let mut mutations = 0;
    for (number, opt) in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3]
        .into_iter()
        .enumerate()
    {
        for width in [32, 64, 128] {
            let directory = tempfile::tempdir().unwrap();
            let path = directory.path();
            fs::write(path.join("reference.ll"), format!(
                "target triple = \"aarch64-unknown-linux-gnu\"\ndefine i{width} @llvm_sext(i1 %b) {{\n  %r = sext i1 %b to i{width}\n  ret i{width} %r\n}}\n"
            )).unwrap();
            checked(
                Command::new(&llc)
                    .arg(format!("-O={number}"))
                    .arg("-filetype=obj")
                    .arg(path.join("reference.ll"))
                    .arg("-o")
                    .arg(path.join("reference.o")),
            );
            let c_type = match width {
                32 => "int32_t",
                64 => "int64_t",
                128 => "__int128",
                _ => unreachable!(),
            };
            fs::write(
                path.join("driver.c"),
                format!(
                    r#"
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
extern {c_type} cg_sext(bool);
extern {c_type} llvm_sext(bool);
int main(void) {{
    for (int b = 0; b < 2; ++b) {{
        {c_type} want = llvm_sext((bool)b);
        if (want != ({c_type})(-b)) return 42;
        {c_type} got = cg_sext((bool)b);
        if (got != want) {{ printf("b=%d mismatch\n", b); return 41; }}
        printf("b=%d match\n", b);
    }}
    return 0;
}}
"#
                ),
            )
            .unwrap();
            let object = compile(&module(width), opt);
            link_run(path, &object, "positive", width, 0);
            cells += 1;
            if width == 128 {
                link_run(
                    path,
                    &old_low_half_selection(&object),
                    "old-selection",
                    width,
                    41,
                );
                mutations += 1;
            }
            eprintln!(
                "O{number} B1->I{width}: false/true match LLVM; old-selection mutation={}",
                width == 128
            );
        }
    }
    assert_eq!((cells, mutations), (12, 4));
    eprintln!(
        "LA-17: 12 build cells, 24 native comparisons, 4 old-selection mutants killed; zero skips"
    );
}
