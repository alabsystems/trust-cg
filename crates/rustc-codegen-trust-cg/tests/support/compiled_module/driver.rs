// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
// Exercise the real production carrier against actual compiler metadata.
// This is a data-transfer check, not CG guest execution or proof evidence.
#![feature(rustc_private)]
extern crate rustc_codegen_ssa;
extern crate rustc_driver;

#[path = "../../../src/compiled_module.rs"]
mod compiled_module;

use compiled_module::{FreshModule, fresh};
use rustc_codegen_ssa::ModuleKind;
use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt;
use std::path::PathBuf;

fn main() {
    let mut cases = 0;
    for mask in 0u8..64 {
        for kind_index in 0..2 {
            let name = format!("CGU {mask:02X} / Name-{kind_index}");
            let paths: [Option<PathBuf>; 6] = std::array::from_fn(|slot| {
                (mask & (1 << slot) != 0).then(|| {
                    let mut bytes = format!("artifact {slot} / MASK-{mask:02X}-").into_bytes();
                    bytes.push(0xff);
                    PathBuf::from(OsString::from_vec(bytes))
                })
            });
            let [
                object,
                global_asm_object,
                dwarf_object,
                bytecode,
                assembly,
                llvm_ir,
            ] = paths.clone();
            let kind = match kind_index {
                0 => ModuleKind::Regular,
                1 => ModuleKind::Allocator,
                _ => unreachable!(),
            };
            let module = fresh(FreshModule {
                name: name.clone(),
                kind,
                object,
                global_asm_object,
                dwarf_object,
                bytecode,
                assembly,
                llvm_ir,
            });
            assert_eq!(
                module.name, name,
                "module name mask={mask} kind={kind_index}"
            );
            assert_eq!(
                module.kind, kind,
                "module kind mask={mask} kind={kind_index}"
            );
            let actual = [
                module.object,
                module.global_asm_object,
                module.dwarf_object,
                module.bytecode,
                module.assembly,
                module.llvm_ir,
            ];
            assert_eq!(
                actual, paths,
                "artifact paths mask={mask} kind={kind_index}"
            );
            #[cfg(rustc_compiled_module_cache_links)]
            assert!(
                module.links_from_incr_cache.is_empty(),
                "fresh cached links"
            );
            cases += 1;
        }
    }
    assert_eq!(cases, 128);
    println!(
        "FRESH_MODULE_CARRIER cases={cases} masks=64 kinds=2 artifacts=6 paths=nonutf8 cache_links={}",
        if cfg!(rustc_compiled_module_cache_links) {
            "empty"
        } else {
            "absent"
        }
    );
}
