// trust-cg-verify/tests/support/wasm_float_live_emit.rs - the wasm float corpora, re-derived from the live backend
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! FRESHNESS for the wasm float credits, in one place.
//!
//! The `f32.const` / `f64.const` rows are credited over
//! [`EMITTED_FLOAT_CONST_IMMEDIATES`] and the `f.min` / `f.max` / `copysign`
//! rows over [`EMITTED_FLOAT_BINOP_BODIES`]: CAPTURES of what the real backend
//! emitted, because `trust-cg-verify` cannot call `trust-cg-codegen` outside
//! tests. A capture can rot, so each entry is recompiled here through the LIVE
//! backend and required byte-identical. The module is shared via `#[path]` by
//! `wasm_encoding_gate` and the ratio-pinning `coverage_gate_tests`, so a
//! backend change that alters these bytes cannot
//! leave those targets green over frozen bytes.

#![allow(dead_code)]

use trust_cg_codegen::wasm;
use trust_cg_verify::wasm_encoding_proofs as enc;
use trust_cg_verify::wasm_float_binop_proofs as fb;

use enc::{EMITTED_FLOAT_CONST_IMMEDIATES, Imm, OP_F32_CONST, OP_F64_CONST, decode_module};
use fb::{EMITTED_FLOAT_BINOP_BODIES, FloatBinopKind};
use trust_ir::{BinOp, Ty};
use trust_ir_build::ModuleBuilder;

fn finish_wasm32(mb: ModuleBuilder) -> trust_ir::Module {
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.target_info = Some(wasm::wasm32_target_info());
    m
}

fn float_ty(bits: u32) -> Ty {
    if bits == 32 { Ty::F32 } else { Ty::F64 }
}

/// The trust-ir `() -> fN { ret <carrier> }`.
pub fn float_const_ir(bits: u32, carrier: u64) -> trust_ir::Module {
    let ty = float_ty(bits);
    let mut mb = ModuleBuilder::new("k");
    let ft = mb.add_func_type(vec![], vec![ty.clone()]);
    let mut f = mb.function("k", ft);
    let e = f.create_block();
    f.switch_to_block(e);
    let c = f.fconst(ty, f64::from_bits(carrier));
    f.ret(vec![c]);
    f.build();
    finish_wasm32(mb)
}

/// `() -> fN { ret <carrier> }` compiled by the live backend.
pub fn float_const_module(bits: u32, carrier: u64) -> Vec<u8> {
    wasm::compile_module_with_license(&float_const_ir(bits, carrier), &permit_unlicensed())
        .expect("float const module must compile")
}

/// The opcode and raw payload of the first float const in a module, as the
/// independent module decoder reads them.
pub fn first_float_const_immediate(bytes: &[u8]) -> (u8, Vec<u8>) {
    let m = decode_module(bytes).expect("emitted module must decode");
    let body = m.code.first().expect("at least one defined body");
    let ins = body
        .instrs
        .iter()
        .find(|i| matches!(i.imm, Imm::F32(_) | Imm::F64(_)))
        .expect("the shape carries a float const");
    let payload = match &ins.imm {
        Imm::F32(b) => b.to_vec(),
        Imm::F64(b) => b.to_vec(),
        _ => unreachable!("filtered above"),
    };
    (ins.opcode, payload)
}

/// Recompile every captured float const through the live backend and require
/// the emitted opcode and payload to be byte-identical to the capture.
/// Returns the number of entries checked.
pub fn assert_float_const_corpus_is_what_the_live_backend_emits() -> usize {
    for &(carrier, bits, captured) in EMITTED_FLOAT_CONST_IMMEDIATES {
        let want_op = if bits == 32 {
            OP_F32_CONST
        } else {
            OP_F64_CONST
        };
        let (op, live) = first_float_const_immediate(&float_const_module(bits, carrier));
        assert_eq!(
            op, want_op,
            "f{bits}.const carrier 0x{carrier:016x}: the live backend emitted opcode 0x{op:02x}"
        );
        assert_eq!(
            live.as_slice(),
            captured,
            "f{bits}.const carrier 0x{carrier:016x}: the live backend emits {live:02x?} but the \
             capture says {captured:02x?} — the corpus has rotted, or the lowering changed"
        );
    }
    EMITTED_FLOAT_CONST_IMMEDIATES.len()
}

/// `(a: fN, b: fN) -> fN { ret op(a, b) }` compiled by the live backend.
pub fn float_binop_module(kind: FloatBinopKind, bits: u32) -> Vec<u8> {
    let ty = float_ty(bits);
    let op = match kind {
        FloatBinopKind::Min => BinOp::FMin,
        FloatBinopKind::Max => BinOp::FMax,
        FloatBinopKind::CopySign => BinOp::FCopySign,
    };
    let mut mb = ModuleBuilder::new("fb");
    let ft = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
    let mut f = mb.function("fb", ft);
    let e = f.create_block();
    let a = f.add_block_param(e, ty.clone());
    let b = f.add_block_param(e, ty.clone());
    f.switch_to_block(e);
    let r = f.binop(op, ty, a, b);
    f.ret(vec![r]);
    f.build();
    wasm::compile_module_with_license(&finish_wasm32(mb), &permit_unlicensed())
        .expect("float binop module must compile")
}

/// The raw bytes of every code ENTRY (locals vector and expression, without
/// the entry's size prefix), walked from the section headers with the
/// independent spec LEB decoder.
pub fn code_entries(bytes: &[u8]) -> Vec<Vec<u8>> {
    let uleb = |at: &mut usize| -> usize {
        let (v, used) = enc::spec_decode_unsigned(&bytes[*at..], 32).expect("u32 LEB");
        *at += used;
        v as usize
    };
    let mut at = 8usize;
    while at < bytes.len() {
        let id = bytes[at];
        at += 1;
        let size = uleb(&mut at);
        if id == 10 {
            let mut c = at;
            let n = uleb(&mut c);
            let mut out = Vec::with_capacity(n);
            for _ in 0..n {
                let len = uleb(&mut c);
                out.push(bytes[c..c + len].to_vec());
                c += len;
            }
            return out;
        }
        at += size;
    }
    Vec::new()
}

/// Recompile every captured float binop body through the live backend and
/// require the function's code entry to be byte-identical to the capture.
/// Returns the number of bodies checked.
pub fn assert_float_binop_bodies_are_what_the_live_backend_emits() -> usize {
    for &(kind, bits, captured) in EMITTED_FLOAT_BINOP_BODIES {
        let entries = code_entries(&float_binop_module(kind, bits));
        let live = entries
            .first()
            .unwrap_or_else(|| panic!("{kind:?} f{bits}: the module has no code entry"));
        assert_eq!(
            live.as_slice(),
            captured,
            "{kind:?} f{bits}: the live backend emits {live:02x?} but the capture says \
             {captured:02x?} — the corpus has rotted, or the lowering changed"
        );
    }
    EMITTED_FLOAT_BINOP_BODIES.len()
}

/// This module's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
