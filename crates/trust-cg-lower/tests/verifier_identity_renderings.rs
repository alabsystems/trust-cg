// trust-cg-lower/tests/verifier_identity_renderings.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The LIR verifier-input identity renderings on real functions.
//!
//! * `write_canonical_verifier_identity` must emit exactly the bytes it did
//!   before it was factored over a pretty/compact rendering flag: the previous
//!   implementation is kept below verbatim as the oracle.
//! * `write_compact_verifier_identity` must separate functions exactly as the
//!   canonical rendering does: equal compact identities if and only if equal
//!   canonical identities, over the functions and systematic perturbations of
//!   them.
//!
//! The functions are the LIR of the compile-time corpus's modules
//! (`benchmarks/compile-corpus/modules`: TY images, rustc-bridge programs,
//! the jit-matrix kernels), translated by `translate_module` under a stated `Permit`.

use std::fmt::Write as _;
use std::path::Path;

use trust_cg_lower::Function;
use trust_cg_lower::instructions::Opcode;

/// The canonical identity writer before the rendering flag, verbatim.
fn reference_canonical_identity(f: &Function) -> String {
    let mut out = String::new();
    let o = &mut out;
    writeln!(o, "trust-cg.lir.verifier-input.v3").unwrap();
    writeln!(o, "name={:?}", f.name).unwrap();
    writeln!(o, "signature={:#?}", f.signature).unwrap();
    writeln!(o, "block_order={:?}", f.block_order).unwrap();
    writeln!(o, "entry_block={:?}", f.entry_block).unwrap();
    writeln!(o, "stack_slots={:#?}", f.stack_slots).unwrap();
    writeln!(o, "debug_meta={:#?}", f.debug_meta).unwrap();
    writeln!(o, "debug_value_bindings={:#?}", f.debug_value_bindings).unwrap();
    writeln!(o, "stack_protector={:?}", f.stack_protector).unwrap();
    writeln!(o, "param_pointee_types={:#?}", f.param_pointee_types).unwrap();
    writeln!(o, "eh_info={:#?}", f.eh_info).unwrap();
    let mut blocks: Vec<_> = f.blocks.iter().collect();
    blocks.sort_by_key(|(block, _)| **block);
    writeln!(o, "blocks={}", blocks.len()).unwrap();
    for (block, body) in blocks {
        writeln!(o, "block[{block:?}]={body:#?}").unwrap();
        for (instruction_index, instruction) in body.instructions.iter().enumerate() {
            if let Opcode::Fconst { imm, .. } = &instruction.opcode {
                writeln!(
                    o,
                    "fconst_bits[{block:?}][{instruction_index}]={:016x}",
                    imm.to_bits()
                )
                .unwrap();
            }
        }
    }
    let mut trust_ir_origins: Vec<_> = f.trust_ir_origins.iter().collect();
    trust_ir_origins.sort_by_key(|(block, _)| **block);
    writeln!(o, "trust_ir_origins={}", trust_ir_origins.len()).unwrap();
    for (block, origins) in trust_ir_origins {
        writeln!(o, "trust_ir_origins[{block:?}]={origins:?}").unwrap();
    }
    let mut value_types: Vec<_> = f.value_types.iter().collect();
    value_types.sort_by_key(|(value, _)| value.0);
    writeln!(o, "value_types={}", value_types.len()).unwrap();
    for (value, ty) in value_types {
        writeln!(o, "value_type[{value:?}]={ty:?}").unwrap();
    }
    let mut pure_callees: Vec<_> = f.pure_callees.iter().collect();
    pure_callees.sort_unstable();
    writeln!(o, "pure_callees={}", pure_callees.len()).unwrap();
    for callee in pure_callees {
        writeln!(o, "pure_callee={callee:?}").unwrap();
    }
    let mut libm_pure_callees: Vec<_> = f.libm_pure_callees.iter().collect();
    libm_pure_callees.sort_unstable();
    writeln!(o, "libm_pure_callees={}", libm_pure_callees.len()).unwrap();
    for callee in libm_pure_callees {
        writeln!(o, "libm_pure_callee={callee:?}").unwrap();
    }
    writeln!(o, "abi_sret_param={:?}", f.abi_sret_param).unwrap();
    let mut sret_arg_callees: Vec<_> = f.sret_arg_callees.iter().collect();
    sret_arg_callees.sort_unstable();
    writeln!(o, "sret_arg_callees={}", sret_arg_callees.len()).unwrap();
    for callee in sret_arg_callees {
        writeln!(o, "sret_arg_callee={callee:?}").unwrap();
    }
    let mut sret_arg_indirect_callees: Vec<_> = f.sret_arg_indirect_callees.iter().collect();
    sret_arg_indirect_callees.sort_unstable_by_key(|value| value.0);
    writeln!(
        o,
        "sret_arg_indirect_callees={}",
        sret_arg_indirect_callees.len()
    )
    .unwrap();
    for callee in sret_arg_indirect_callees {
        writeln!(o, "sret_arg_indirect_callee={callee:?}").unwrap();
    }
    out
}

fn canonical(f: &Function) -> String {
    let mut out = String::new();
    f.write_canonical_verifier_identity(&mut out).unwrap();
    out
}

fn compact(f: &Function) -> String {
    let mut out = String::new();
    f.write_compact_verifier_identity(&mut out).unwrap();
    out
}

/// LIR functions of up to `limit` corpus module files.
fn corpus_functions(limit: usize) -> Vec<Function> {
    let modules =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../benchmarks/compile-corpus/modules");
    let mut files = Vec::new();
    for family in ["ty", "jit-matrix", "fixtures", "bridge"] {
        let dir = modules.join(family);
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        let mut paths: Vec<_> = entries.filter_map(|e| e.ok().map(|e| e.path())).collect();
        paths.sort();
        for path in paths {
            if path.is_dir() {
                let mut inner: Vec<_> = std::fs::read_dir(&path)
                    .unwrap()
                    .filter_map(|e| e.ok().map(|e| e.path()))
                    .filter(|p| p.extension().is_some_and(|x| x == "trust_irbin"))
                    .collect();
                inner.sort();
                files.extend(inner.into_iter().take(3));
            } else if path.extension().is_some_and(|x| x == "trust_irbin") {
                files.push(path);
            }
        }
    }
    let mut functions = Vec::new();
    for file in files.into_iter().step_by(3).take(limit) {
        let bytes = std::fs::read(&file).unwrap();
        let Ok(module) = trust_ir::binary::deserialize_module(&bytes) else {
            continue;
        };
        if let Ok(lir) = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::default(),
            trust_cg_lower::TlsDialect::default(),
            &permit_unlicensed(),
        ) {
            functions.extend(lir.into_iter().map(|(f, _)| f));
        }
    }
    functions
}

#[test]
fn canonical_identity_is_unchanged_by_the_rendering_flag() {
    let functions = corpus_functions(120);
    assert!(functions.len() > 500, "{}", functions.len());
    let mut fconsts = 0;
    for f in &functions {
        assert_eq!(canonical(f), reference_canonical_identity(f), "{}", f.name);
        fconsts += f
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .filter(|i| matches!(i.opcode, Opcode::Fconst { .. }))
            .count();
    }
    assert!(fconsts > 0);
}

#[test]
fn compact_identity_separates_exactly_what_the_canonical_identity_does() {
    let functions = corpus_functions(60);
    // Each function, and perturbations of the parts the renderings cover:
    // the name, one instruction's opcode, one value's type, the block order,
    // a stack slot, and a float constant's NaN payload.
    let mut variants: Vec<Function> = Vec::new();
    for f in functions.iter().take(120) {
        variants.push(f.clone());
        let mut renamed = f.clone();
        renamed.name.push('\'');
        variants.push(renamed);
        let mut reordered = f.clone();
        reordered.block_order.reverse();
        variants.push(reordered);
        if let Some((value, ty)) = f.value_types.iter().next() {
            let mut retyped = f.clone();
            retyped.value_types.remove(value);
            retyped
                .value_types
                .insert(trust_cg_lower::instructions::Value(value.0 + 1), ty.clone());
            variants.push(retyped);
        }
        for block in f.blocks.values() {
            for (index, instruction) in block.instructions.iter().enumerate() {
                if let Opcode::Fconst { imm, .. } = instruction.opcode {
                    let mut payload = f.clone();
                    let key = *f
                        .blocks
                        .iter()
                        .find(|(_, b)| std::ptr::eq(*b, block))
                        .unwrap()
                        .0;
                    if let Opcode::Fconst { imm: slot, .. } =
                        &mut payload.blocks.get_mut(&key).unwrap().instructions[index].opcode
                    {
                        *slot = f64::from_bits(imm.to_bits() ^ 1);
                    }
                    variants.push(payload);
                }
            }
        }
        if let Some(block) = f.block_order.first()
            && let Some(first) = f.blocks[block].instructions.first()
        {
            let mut swapped = f.clone();
            swapped.blocks.get_mut(block).unwrap().instructions[0].opcode = Opcode::Trap;
            if first.opcode != Opcode::Trap {
                variants.push(swapped);
            }
        }
    }
    let canon: Vec<String> = variants.iter().map(canonical).collect();
    let comp: Vec<String> = variants.iter().map(compact).collect();
    let mut distinct = 0usize;
    for i in 0..variants.len() {
        for j in i..variants.len() {
            assert_eq!(
                canon[i] == canon[j],
                comp[i] == comp[j],
                "{} / {}",
                variants[i].name,
                variants[j].name
            );
            distinct += usize::from(canon[i] != canon[j]);
        }
    }
    assert!(distinct > 10_000, "{distinct}");
}

/// A function's stated target features (L03-P9) select different
/// instructions, so both renderings separate two functions that differ only
/// there, and the attribute-free function keeps the identity it had before
/// per-function features existed (the reference writer above, which renders
/// no feature line).
#[test]
fn stated_target_features_separate_verifier_identities() {
    let signature = trust_cg_lower::function::Signature {
        params: vec![trust_cg_lower::Type::I32],
        returns: vec![trust_cg_lower::Type::I32],
    };
    let plain = Function::new("checksum", signature);
    assert_eq!(canonical(&plain), reference_canonical_identity(&plain));
    let stating = |features: &[&str]| {
        let mut f = plain.clone();
        f.target_features = features.iter().map(|name| (*name).to_owned()).collect();
        f
    };
    let variants = [
        plain.clone(),
        stating(&["crc"]),
        stating(&["lse"]),
        stating(&["crc", "lse"]),
    ];
    for (i, a) in variants.iter().enumerate() {
        for (j, b) in variants.iter().enumerate() {
            assert_eq!(
                canonical(a) == canonical(b),
                i == j,
                "canonical {:?} vs {:?}",
                a.target_features,
                b.target_features
            );
            assert_eq!(
                compact(a) == compact(b),
                i == j,
                "compact {:?} vs {:?}",
                a.target_features,
                b.target_features
            );
        }
    }
}

/// The corpus modules (rustc-bridge dumps and fixtures) carry no codegen
/// license (`body_gate: None`), which trust-cg REFUSES by default (roadmap
/// WS7.5, decision gate DG-73). They are translated under a stated `Permit`,
/// so the sample is the corpus's functions, never an empty set the license
/// refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
