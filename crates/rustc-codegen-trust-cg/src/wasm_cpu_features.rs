// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0

//! WebAssembly CPU configuration data, independent of LLVM target registration.
//!
//! The profiles and backend bits follow LLVM 22.1.2's WebAssembly.td.
//! These are configuration facts, not instruction admission or proof authority.
//! Rust feature implications are applied separately by rustc_codegen_ssa.

use std::collections::BTreeSet;

const FEATURES: &[&str] = &[
    "atomics",
    "bulk-memory-opt",
    "bulk-memory",
    "call-indirect-overlong",
    "multivalue",
    "reference-types",
    "exception-handling",
    "extended-const",
    "fp16",
    "gc",
    "multimemory",
    "mutable-globals",
    "nontrapping-fptoint",
    "relaxed-simd",
    "sign-ext",
    "simd128",
    "tail-call",
    "wide-arithmetic",
];

#[derive(Default)]
pub(crate) struct Features(BTreeSet<&'static str>);

impl Features {
    pub(crate) fn for_cpu(cpu: &str) -> (Self, bool) {
        let defaults: &[&str] = match cpu {
            "mvp" => &[],
            "generic" => &[
                "bulk-memory",
                "bulk-memory-opt",
                "call-indirect-overlong",
                "multivalue",
                "mutable-globals",
                "nontrapping-fptoint",
                "reference-types",
                "sign-ext",
            ],
            "lime1" => &[
                "bulk-memory-opt",
                "call-indirect-overlong",
                "extended-const",
                "multivalue",
                "mutable-globals",
                "nontrapping-fptoint",
                "sign-ext",
            ],
            "bleeding-edge" => &[
                "atomics",
                "bulk-memory",
                "bulk-memory-opt",
                "call-indirect-overlong",
                "exception-handling",
                "extended-const",
                "fp16",
                "gc",
                "multimemory",
                "multivalue",
                "mutable-globals",
                "nontrapping-fptoint",
                "relaxed-simd",
                "reference-types",
                "simd128",
                "sign-ext",
                "tail-call",
            ],
            // LLVM ignores an unrecognized CPU instead of selecting generic.
            _ => return (Self::default(), false),
        };
        let mut result = Self::default();
        for feature in defaults {
            result.set(feature, true);
        }
        (result, true)
    }

    pub(crate) fn knows(feature: &str) -> bool {
        FEATURES.contains(&feature)
    }

    pub(crate) fn has(&self, feature: &str) -> bool {
        self.0.contains(feature)
    }

    /// LLVM 22.1.2 declares independent Wasm feature bits. Later LLVM
    /// catalogs add backend implications, which must not be imported into
    /// this cohort. Rust-level implications remain owned by rustc_codegen_ssa.
    pub(crate) fn set(&mut self, feature: &str, enabled: bool) -> bool {
        let Some(&name) = FEATURES.iter().find(|&&name| name == feature) else {
            return false;
        };
        if enabled {
            self.0.insert(name);
        } else {
            self.0.remove(name);
        }
        true
    }
}
