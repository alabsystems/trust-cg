// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Full Compiler::compile binding of x86-64 Darwin module-local references.
//! Object/native controls grant no NoUB, body licence or formal linker proof.

#[path = "common/module_local_binding_fixture.rs"]
mod module_local_binding_fixture;
use module_local_binding_fixture::local_binding_module;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::{Linkage, Visibility};

fn compiler(opt_level: OptLevel, emit_proofs: bool) -> Compiler {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            emit_proofs,
            ..Default::default()
        },
        TargetSpec::parse("x86_64-apple-darwin").unwrap(),
    )
    // This explicit test-only licence permits raw fixture IR. Certificate
    // promotion remains the real public Compiler policy when requested.
    .with_codegen_license(
        trust_cg_lower::CodegenLicensePolicy::default()
            .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
    )
}

fn u32_at(bytes: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
}

/// Independent nlist/relocation reader: do not use emitter or production reader.
fn local_helper_references(object: &[u8]) {
    assert_eq!(u32_at(object, 0), 0xfeed_facf);
    assert_eq!(u32_at(object, 4), 0x0100_0007);
    let mut at = 32;
    let mut symtab = None;
    let mut sections = Vec::new();
    for _ in 0..u32_at(object, 16) {
        let kind = u32_at(object, at);
        if kind == 2 {
            symtab = Some((
                u32_at(object, at + 8) as usize,
                u32_at(object, at + 12) as usize,
                u32_at(object, at + 16) as usize,
                u32_at(object, at + 20) as usize,
            ));
        } else if kind == 0x19 {
            for i in 0..u32_at(object, at + 64) as usize {
                let sec = at + 72 + 80 * i;
                let end = object[sec..sec + 16]
                    .iter()
                    .position(|&b| b == 0)
                    .unwrap_or(16);
                sections.push((
                    String::from_utf8(object[sec..sec + end].to_vec()).unwrap(),
                    u32_at(object, sec + 56) as usize,
                    u32_at(object, sec + 60) as usize,
                ));
            }
        }
        at += u32_at(object, at + 4) as usize;
    }
    let (symbols, count, strings, string_bytes) = symtab.unwrap();
    let mut helpers = Vec::new();
    for i in 0..count {
        let n = symbols + 16 * i;
        let name_start = strings + u32_at(object, n) as usize;
        assert!(name_start < strings + string_bytes);
        let end = object[name_start..strings + string_bytes]
            .iter()
            .position(|&b| b == 0)
            .unwrap();
        if &object[name_start..name_start + end] == b"_helper" {
            helpers.push((i, object[n + 4]));
        }
    }
    assert_eq!(helpers.len(), 1);
    assert_eq!(
        helpers[0].1, 0x0e,
        "helper must be one genuinely local N_SECT definition"
    );
    let mut branch = false;
    let mut pointer = false;
    for (section, start, count) in sections {
        for i in 0..count {
            let packed = u32_at(object, start + 8 * i + 4);
            if packed & 0x00ff_ffff != helpers[0].0 as u32 {
                continue;
            }
            assert_ne!(
                packed & (1 << 27),
                0,
                "record must name the exact helper symbol"
            );
            let kind = packed >> 28;
            branch |= section == "__text" && kind == 2;
            pointer |= section == "__data" && kind == 0;
        }
    }
    assert!(branch, "direct call must reach the local helper");
    assert!(
        pointer,
        "source pointer slot must reach the same local helper"
    );
}

#[test]
fn compiler_binds_local_calls_and_data_pointers_on_x86_64_macho() {
    for linkage in [Linkage::Internal, Linkage::Private] {
        for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let m = local_binding_module("a", linkage, Visibility::Default, Linkage::External, 7);
            let result = compiler(opt, false)
                .compile(&m)
                .unwrap_or_else(|e| panic!("{linkage:?}/{opt:?}: {e}"));
            local_helper_references(&result.object_code);
        }
    }
}

#[test]
fn proof_required_local_references_compile_with_the_real_proof_policy() {
    let m = local_binding_module(
        "a",
        Linkage::Internal,
        Visibility::Default,
        Linkage::External,
        7,
    );
    let result = compiler(OptLevel::O0, true)
        .compile(&m)
        .expect("this supported fixture must compile with the unchanged real proof gate enabled");
    let proofs = result
        .proofs
        .as_ref()
        .expect("requested proof reports must exist");
    assert!(!proofs.is_empty());
    assert!(proofs.iter().all(|p| p.verified));
    assert!(
        proofs
            .iter()
            .any(|p| p.verified && p.category == "relocation_inventory"),
        "proof-enabled objects must carry the actual verified relocation inventory"
    );
    let mut categories = std::collections::BTreeMap::new();
    for proof in proofs {
        *categories.entry(proof.category.as_str()).or_insert(0usize) += 1;
    }
    // These are the real compiler's existing certificate categories, not a new
    // whole-body, source-to-ISA, NoUB or licence claim for the fixture.
    eprintln!(
        "ACTUAL_PROOF_REQUEST_ACCEPTED {}",
        serde_json::json!({
            "certificates": proofs.len(), "categories": categories,
            "object_bytes": result.object_code.len(),
        })
    );
    local_helper_references(&result.object_code);
}

#[cfg(target_os = "macos")]
#[test]
fn two_native_x86_64_modules_reach_their_own_private_helpers() {
    use std::process::Command;
    let dir = tempfile::tempdir().unwrap();
    for linkage in [Linkage::Internal, Linkage::Private] {
        for opt in [OptLevel::O0, OptLevel::O3] {
            for (name, offset) in [("a", 7), ("b", 100)] {
                let m = local_binding_module(
                    name,
                    linkage,
                    Visibility::Default,
                    Linkage::External,
                    offset,
                );
                let object = compiler(opt, false).compile(&m).unwrap().object_code;
                local_helper_references(&object);
                std::fs::write(dir.path().join(format!("{name}.o")), object).unwrap();
            }
            let driver = dir.path().join("driver.c");
            std::fs::write(
                &driver,
                r#"
#include <stdint.h>
extern uint64_t a_direct(uint64_t), b_direct(uint64_t);
extern uint64_t a_via_global(uint64_t), b_via_global(uint64_t);
extern uint64_t a_calls(void), b_calls(void);
uint64_t helper(uint64_t x) { return x + 9999; }
int main(void) {
    const uint64_t xs[] = {0, 1, 7, UINT64_MAX};
    for (unsigned i=0; i<4; ++i) {
        uint64_t x=xs[i];
        if (a_direct(x)!=x+7 || a_via_global(x)!=x+7) return 1;
        if (b_direct(x)!=x+100 || b_via_global(x)!=x+100) return 2;
    }
    if (a_calls()!=8 || b_calls()!=8 || helper(1)!=10000) return 3;
    return 0;
}
"#,
            )
            .unwrap();
            let exe = dir.path().join("driver");
            let linked = Command::new("/usr/bin/clang")
                .args(["-arch", "x86_64"])
                .arg(&driver)
                .arg(dir.path().join("a.o"))
                .arg(dir.path().join("b.o"))
                .arg("-o")
                .arg(&exe)
                .output()
                .unwrap();
            assert!(
                linked.status.success(),
                "link: {}",
                String::from_utf8_lossy(&linked.stderr)
            );
            let ran = Command::new("/usr/bin/arch")
                .arg("-x86_64")
                .arg(&exe)
                .output()
                .unwrap();
            assert!(ran.status.success(), "native {linkage:?}/{opt:?}: {ran:?}");
        }
    }
}
