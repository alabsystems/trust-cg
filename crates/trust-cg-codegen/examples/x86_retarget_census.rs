// trust-cg-codegen/examples/x86_retarget_census.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Compile TrustIR modules for the two System V x86-64 object formats at O0-O3
// and print one line per (module, triple, level): the SHA-256 and length of the
// emitted object, or the first line of the refusal. Two builds of this example
// run over one corpus give a byte-identity diff of the x86-64 backend.
//
//   scripts/trust_cargo.sh run --release -p trust-cg-codegen --example x86_retarget_census -- \
//       [--externalize] <module-or-dir>...
//
// A module's `target_info` (when present) is rewritten to the triple compiled
// for, keeping its declared struct-passing policy, so a module collected on
// another host is asked the x86-64 question instead of refused for its triple.
// `--externalize` gives every bodied `Internal`/`Private` function `External`
// linkage first: the x86-64 object path cannot yet bind a reference to a
// module-local function (`AotDirectModuleFunctionBindingUnsupported`), and
// linkage does not change a function's calling convention, so this is how a
// JIT-shaped module (TY's semantic images) reaches the x86-64 selector and
// register allocator on a host without an x86-64 JIT.

use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::{OptLevel, load_module_from_bytes};
use trust_cg_codegen::target::TargetSpec;

const TRIPLES: [&str; 2] = ["x86_64-apple-darwin", "x86_64-unknown-linux-gnu"];
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn modules(paths: &[PathBuf]) -> Vec<PathBuf> {
    let mut out = Vec::new();
    for path in paths {
        if path.is_dir() {
            let mut entries: Vec<PathBuf> = std::fs::read_dir(path)
                .unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
                .map(|entry| entry.expect("dir entry").path())
                .collect();
            entries.sort();
            out.extend(modules(&entries));
        } else if path.extension().is_some_and(|x| x == "trust_irbin") {
            out.push(path.clone());
        }
    }
    out
}

fn retarget(module: &mut trust_ir::Module, triple: &str, externalize: bool) {
    if let Some(info) = &mut module.target_info {
        info.triple = triple.into();
        info.pointer_size = 8;
        info.endianness = trust_ir::Endianness::Little;
        info.abi = None;
    }
    if externalize {
        for function in &mut module.functions {
            if function.has_body() && function.linkage.is_module_local() {
                function.linkage = trust_ir::Linkage::External;
            }
        }
    }
}

fn label(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .into_owned()
}

fn main() {
    let mut externalize = false;
    let mut inputs = Vec::new();
    for arg in std::env::args().skip(1) {
        if arg == "--externalize" {
            externalize = true;
        } else {
            inputs.push(PathBuf::from(arg));
        }
    }
    let root = std::env::current_dir().expect("cwd");
    for path in modules(&inputs) {
        let bytes = std::fs::read(&path).expect("read module");
        let name = label(&root, &path);
        let base = match load_module_from_bytes(&bytes) {
            Ok(module) => module,
            Err(error) => {
                println!("{name} - - load-error {error}");
                continue;
            }
        };
        for triple in TRIPLES {
            let mut module = base.clone();
            retarget(&mut module, triple, externalize);
            let spec = TargetSpec::parse(triple).expect("known triple");
            for opt in LEVELS {
                let config = CompilerConfig {
                    opt_level: opt,
                    parallel: false,
                    ..CompilerConfig::default()
                };
                match Compiler::new_for_target_spec(config, spec)
                    .with_codegen_license(permit_unlicensed())
                    .compile(&module)
                {
                    Ok(result) => println!(
                        "{name} {triple} {opt:?} ok {:x} {}",
                        Sha256::digest(&result.object_code),
                        result.object_code.len()
                    ),
                    Err(error) => {
                        let text = format!("{error}");
                        let first = text.lines().next().unwrap_or("").trim();
                        println!("{name} {triple} {opt:?} err {first}");
                    }
                }
            }
        }
    }
}

/// The census modules (dumps and fixtures) carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). This example states `Permit` explicitly, so a row
/// records the retargeted compile, never the same license refusal on every
/// target.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
