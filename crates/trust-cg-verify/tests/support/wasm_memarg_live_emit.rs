// trust-cg-verify/tests/support/wasm_memarg_live_emit.rs - the memarg-offset corpus, re-derived from the live backend
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! FRESHNESS for the memarg-offset binding of the load / store credits.
//!
//! Those rows require [`MEMARG_FIELDS_WASM`], a CAPTURE of the closed module
//! the real backend emits for [`MEMARG_FIELDS_TIR`], because `trust-cg-verify`
//! cannot call `trust-cg-codegen` outside tests. The capture is recompiled
//! here through the LIVE backend and required byte-identical. The module is
//! shared via `#[path]` by `wasm_value_domain_gate`, so a backend change that
//! moves a field offset cannot leave that target green over frozen bytes.

#![allow(dead_code)]

use trust_cg_codegen::wasm;
use trust_cg_verify::wasm_abi_proofs::{Imm, decode_insts, decode_module};
use trust_cg_verify::wasm_memarg_offset_proofs::{MEMARG_FIELDS_TIR, MEMARG_FIELDS_WASM};

/// The module the live backend emits for the corpus text.
pub fn live_memarg_module() -> Vec<u8> {
    let module = trust_ir::parser::parse_module(MEMARG_FIELDS_TIR).expect("the corpus parses");
    wasm::compile_module_with_license(&module, &permit_unlicensed())
        .unwrap_or_else(|e| panic!("the corpus must compile: {e}"))
}

/// Recompile the corpus through the live backend and require it to be
/// byte-identical to the capture.
pub fn assert_memarg_corpus_is_what_the_live_backend_emits() {
    let live = live_memarg_module();
    assert_eq!(
        live.as_slice(),
        MEMARG_FIELDS_WASM,
        "the live backend emits {live:02x?} for the memarg corpus but the capture says \
         {MEMARG_FIELDS_WASM:02x?} — the corpus has rotted, or the lowering changed"
    );
}

/// `wasm` with every load / store memarg offset `o` for which `pick(o)` holds
/// replaced by `o + delta`: a lowering that emits a field at the wrong offset,
/// as bytes. Every offset involved must stay a one-byte LEB (the corpus's are
/// all below 64), so the module keeps its length and its structure.
pub fn shift_memarg_offsets(wasm: &[u8], pick: impl Fn(u32) -> bool, delta: u32) -> Vec<u8> {
    let module = decode_module(wasm).expect("the module decodes");
    let mut out = wasm.to_vec();
    let mut shifted = 0usize;
    for body in &module.bodies {
        let base = wasm
            .windows(body.code.len())
            .position(|w| w == body.code.as_slice())
            .expect("the body occurs in the module");
        for inst in decode_insts(&body.code).expect("the body decodes") {
            let Imm::Memarg { align, offset } = inst.imm else {
                continue;
            };
            if !pick(offset) {
                continue;
            }
            assert!(align < 0x80 && offset + delta < 0x80, "one-byte LEBs only");
            let at = base + inst.at + 2;
            assert_eq!(u32::from(out[at]), offset, "the memarg offset byte");
            out[at] = (offset + delta) as u8;
            shifted += 1;
        }
    }
    assert!(shifted > 0, "no memarg offset was shifted");
    out
}

/// This module's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
