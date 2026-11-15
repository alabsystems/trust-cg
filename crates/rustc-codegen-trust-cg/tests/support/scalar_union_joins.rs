//! Native regression for preserved union field indices at branch joins.
//! This explicitly disables codegen proof certificates to isolate MIR lowering;
//! the separate proof-required ABI test remains required.

use super::{Artifacts, TARGET, backend, checked, rustc_command, scalar_cell_runtime, sha256};
use std::fmt::Write as _;
use std::path::PathBuf;
use std::process::Command;

fn corpus() -> (String, String, usize) {
    let mut rust = String::from(
        "#![no_std]\nuse core::mem::MaybeUninit;\n\
         #[inline(never)] fn select<T>(flag:bool,a:T,b:T)->T {if flag {a} else {b}}\n",
    );
    let mut cases = Vec::new();
    for (ty, cty) in [
        ("u32", "uint32_t"),
        ("u64", "uint64_t"),
        ("i64", "int64_t"),
        ("f32", "float"),
        ("f64", "double"),
    ] {
        let name = format!("maybe_{ty}");
        writeln!(rust, "#[unsafe(no_mangle)] pub extern \"C\" fn {name}(flag:u8,a:{ty},b:{ty})->{ty} {{let x=MaybeUninit::new(a);let y=MaybeUninit::new(b);unsafe{{select(flag!=0,x,y).assume_init()}}}}").unwrap();
        cases.push((name, cty));
    }
    // Read each non-ZST sibling after selecting either initializer. Leading,
    // interspersed and trailing ZSTs must preserve the original field numbers;
    // the no-ZST control preserves the existing behavior.
    for (name, fields) in [
        ("First", "z:(),a:u64,b:u64"),
        ("Middle", "a:u64,z:(),b:u64"),
        ("Last", "a:u64,b:u64,z:()"),
        ("Plain", "a:u64,b:u64"),
    ] {
        writeln!(rust, "#[derive(Clone,Copy)] union {name} {{{fields}}}").unwrap();
        for field in ["a", "b"] {
            let function = format!("union_{}_{field}", name.to_lowercase());
            writeln!(rust, "#[unsafe(no_mangle)] pub extern \"C\" fn {function}(flag:u8,a:u64,b:u64)->u64 {{let x={name}{{a}};let y={name}{{b}};unsafe {{ select(flag!=0,x,y).{field} }} }}").unwrap();
            cases.push((function, "uint64_t"));
        }
    }
    assert_eq!(cases.len(), 13);
    let mut c = String::from("#include <stdint.h>\n#include <stdio.h>\n#include <string.h>\n");
    for (name, cty) in &cases {
        writeln!(c, "extern {cty} {name}(uint8_t,{cty},{cty});").unwrap();
    }
    c.push_str("int main(void){unsigned checks=0;const uint64_t bits[10]={0,1,UINT64_MAX,0x8000000080000000ULL,0x3ff000003f800000ULL,0xbff80000c0200000ULL,0x7ff000007f800000ULL,0xfff00000ff800000ULL,0x7ff812347fc12345ULL,0x0123456789abcdefULL};const uint8_t flags[3]={0,1,255};for(unsigned i=0;i<10;i++){for(unsigned j=0;j<10;j++){for(unsigned k=0;k<3;k++){uint8_t flag=flags[k];\n");
    for (name, cty) in &cases {
        writeln!(c, "{{{cty} a,b;memcpy(&a,&bits[i],sizeof(a));memcpy(&b,&bits[j],sizeof(b));{cty} result={name}(flag,a,b);const void *expected=flag?(const void*)&a:(const void*)&b;if(memcmp(&result,expected,sizeof(result))!=0){{fprintf(stderr,\"{name} i=%u j=%u flag=%u\\n\",i,j,flag);return 1;}}checks++;}}").unwrap();
    }
    let checks = cases.len() * 10 * 10 * 3;
    writeln!(c, "}}}}}}if(checks!={checks})return 2;printf(\"PASS scalar_union_joins checks=%u\\n\",checks);return 0;}}").unwrap();
    (rust, c, checks)
}

#[test]
fn no_proof_scalar_union_joins_match_llvm() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-union-joins.XXXXXX"])
        .output()
        .expect("mktemp union artifacts");
    assert!(temp.status.success());
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    let runtime = scalar_cell_runtime::Runtime::build(root);
    let (rust, c, checks) = corpus();
    std::fs::write(root.join("corpus.rs"), rust).unwrap();
    std::fs::write(root.join("driver.c"), c).unwrap();
    for opt in 0..=3 {
        for lane in ["llvm", "cg"] {
            let stem = format!("{lane}-O{opt}");
            let dir = root.join(&stem);
            std::fs::create_dir(&dir).unwrap();
            let mut command = rustc_command();
            command.args([
                "--crate-type=lib",
                "--emit=obj",
                "-Cpanic=abort",
                "-Ccodegen-units=1",
                "--target",
                TARGET,
            ]);
            command.arg(format!("-Copt-level={opt}"));
            if lane == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
            }
            checked(
                command
                    .arg(root.join("corpus.rs"))
                    .arg("--out-dir")
                    .arg(&dir),
                180,
                &dir.join("compile.log"),
            );
            let mut objects: Vec<_> = std::fs::read_dir(&dir)
                .unwrap()
                .map(|entry| entry.unwrap().path())
                .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
                .collect();
            objects.sort();
            assert!(!objects.is_empty(), "no objects from {stem}");
            let executable = dir.join("native.elf");
            let mut linker = Command::new("cc");
            linker
                .args(["-std=c11", "-O2"])
                .arg(root.join("driver.c"))
                .args(&objects);
            runtime.link_into(&mut linker);
            checked(linker.arg("-o").arg(&executable), 60, &dir.join("link.log"));
            let output = checked(&mut Command::new(&executable), 20, &dir.join("native.log"));
            assert_eq!(
                String::from_utf8(output.stdout).unwrap(),
                format!("PASS scalar_union_joins checks={checks}\n")
            );
            assert!(output.stderr.is_empty());
            assert_eq!(sha256(&backend), digest, "backend changed during {stem}");
        }
    }
    println!(
        "TCG_UNION_JOIN_DIAGNOSTIC executions=8 functions=13 checks={} backend_sha256={digest}",
        checks * 8
    );
}
