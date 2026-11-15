// trust-cg-verify/tests/support/wasm_bulk_memory_live_emit.rs - the wasm bulk-memory bodies, re-derived from the live backend
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! FRESHNESS for the `memory.copy` / `memory.fill` credits.
//!
//! Those rows are credited over [`EMITTED_BULK_MEMORY_BODIES`], CAPTURES of
//! the code entries the real backend emits for `MemCopy` / `MemSet`, because
//! `trust-cg-verify` cannot call `trust-cg-codegen` outside tests. Each capture
//! is recompiled here through the LIVE backend and required byte-identical.
//! The module is shared via `#[path]` by `wasm_encoding_gate` and the
//! ratio-pinning `coverage_gate_tests`, so a backend
//! change that alters these bytes (dropping the zero-length guard, say) cannot
//! leave those targets green over frozen bytes.

#![allow(dead_code)]

use trust_cg_codegen::wasm;
use trust_cg_verify::wasm_bulk_memory_proofs::{
    BulkMemoryShape, EMITTED_BULK_MEMORY_BODIES, EmittedBulkMemoryBody,
};
use trust_cg_verify::wasm_encoding_proofs::spec_decode_unsigned;
use trust_ir::Ty;
use trust_ir_build::ModuleBuilder;

/// The trust-ir function a captured body lowers: `(dst: ptr, src: ptr, n:
/// usize) -> () { memcopy [overlap] dst, src, n }` or `(dst: ptr, byte: u8, n:
/// usize) -> () { memset dst, byte, n }`.
pub fn bulk_memory_ir(shape: BulkMemoryShape) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("bulk");
    let second = match shape {
        BulkMemoryShape::MemSet => Ty::U8,
        BulkMemoryShape::MemCopy | BulkMemoryShape::MemMove => Ty::Ptr,
    };
    let ft = mb.add_func_type(vec![Ty::Ptr, second.clone(), Ty::Usize], vec![]);
    let mut f = mb.function("bulk", ft);
    let e = f.create_block();
    let dst = f.add_block_param(e, Ty::Ptr);
    let b = f.add_block_param(e, second);
    let n = f.add_block_param(e, Ty::Usize);
    f.switch_to_block(e);
    match shape {
        BulkMemoryShape::MemCopy => f.memcopy(dst, b, n, false),
        BulkMemoryShape::MemMove => f.memcopy(dst, b, n, true),
        BulkMemoryShape::MemSet => f.memset(dst, b, n),
    }
    f.ret(vec![]);
    f.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.target_info = Some(wasm::wasm32_target_info());
    m
}

/// The code ENTRY (locals vector and expression) the live backend emits for
/// `shape`.
pub fn live_bulk_memory_body(shape: BulkMemoryShape) -> Vec<u8> {
    let bytes = wasm::compile_module_with_license(&bulk_memory_ir(shape), &permit_unlicensed())
        .unwrap_or_else(|e| panic!("{shape:?} module must compile: {e}"));
    first_code_entry(&bytes).unwrap_or_else(|| panic!("{shape:?}: the module has no code entry"))
}

/// The raw bytes of the first code ENTRY (locals vector and expression,
/// without the entry's size prefix), walked from the section headers with the
/// independent spec LEB decoder.
fn first_code_entry(bytes: &[u8]) -> Option<Vec<u8>> {
    let uleb = |at: &mut usize| -> usize {
        let (v, used) = spec_decode_unsigned(&bytes[*at..], 32).expect("u32 LEB");
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
            if uleb(&mut c) == 0 {
                return None;
            }
            let len = uleb(&mut c);
            return Some(bytes[c..c + len].to_vec());
        }
        at += size;
    }
    None
}

/// Recompile every captured bulk-memory body through the live backend and
/// require the code entry to be byte-identical to the capture. Returns the
/// number of bodies checked.
pub fn assert_bulk_memory_bodies_are_what_the_live_backend_emits() -> usize {
    assert_bodies_match(EMITTED_BULK_MEMORY_BODIES);
    EMITTED_BULK_MEMORY_BODIES.len()
}

fn assert_bodies_match(bodies: &[EmittedBulkMemoryBody]) {
    for &(shape, captured) in bodies {
        let live = live_bulk_memory_body(shape);
        assert_eq!(
            live.as_slice(),
            captured,
            "{shape:?}: the live backend emits {live:02x?} but the capture says {captured:02x?} \
             — the corpus has rotted, or the lowering changed"
        );
    }
}

/// Aggregate moves the memory-carried-value layer lowers with its own
/// constant-size `memory.copy` (`emit_copy`): a struct load/store, a by-value
/// aggregate parameter and result, and an aggregate rebound on a back edge.
const AGGREGATE_MOVES: &str = r#"; TrustIr text format v1
module "aggregate_moves"
target "wasm32-unknown-unknown" 4 little

struct @P { : i64 @0, : i64 @8, : i64 @16 } size=24 align=8 id=0

functy.0 = (ptr, ptr) -> (i32)
functy.1 = (struct.0, i64) -> (struct.0)

fn @mv(functy.0) {
bb0(%0: ptr, %1: ptr):
    %2 = load struct.0, ptr %0
    store struct.0 %2, ptr %1
    %3 = const i32 0
    ret %3
}

fn @spin(functy.1) {
bb0(%0: struct.0, %1: i64):
    %2 = const i64 0
    %3 = icmp eq i64 %1, %2
    condbr %3, bb2, bb1
bb1:
    %4 = const i64 1
    %5 = sub i64 %1, %4
    %6 = make_aggregate struct.0 (%1, %5, %4)
    br bb0(%6, %5)
bb2:
    ret %0
}
"#;

/// How one emitted bulk-memory instruction is reached.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BulkMemorySite {
    /// Inside `local.get n; if; ... local.get n; <op>; end`: the guarded
    /// trust-ir `MemCopy` / `MemSet` lowering the captured bodies credit.
    Guarded,
    /// `... i32.const k; memory.copy` with a constant `k > 0`: the
    /// memory-carried-value layer's aggregate / lane / sret move, which the
    /// captured bodies do NOT credit.
    ConstantNonzeroCopy,
}

/// Classify every `memory.copy` / `memory.fill` in `bytes` as a guarded
/// trust-ir bulk op or a constant-nonzero-size aggregate move, panicking on
/// any other form: the premise the `memory.copy` / `memory.fill` row notes
/// state (no emitted bulk op can see a zero count unguarded).
pub fn bulk_memory_sites(bytes: &[u8]) -> Vec<BulkMemorySite> {
    use trust_cg_verify::wasm_abi_proofs::{Imm, decode_insts, decode_module};
    let module = decode_module(bytes).expect("the module decodes");
    let mut out = Vec::new();
    for (f, body) in module.bodies.iter().enumerate() {
        let insts = decode_insts(&body.code).expect("the body decodes");
        for (k, i) in insts.iter().enumerate() {
            let Imm::Fc(sub @ (10 | 11)) = i.imm else {
                continue;
            };
            let count = k.checked_sub(1).map(|j| &insts[j]);
            // The count operand is the instruction just before the op.
            let site = match count.map(|c| (c.op, &c.imm)) {
                Some((0x41, Imm::I32(v))) if *v > 0 && sub == 10 => {
                    BulkMemorySite::ConstantNonzeroCopy
                }
                Some((0x20, Imm::Idx(n))) => {
                    // The guard: the op's `if` opens on `local.get n` and
                    // nothing between it and the op leaves the arm.
                    let guarded = insts[..k]
                        .iter()
                        .rposition(|x| x.op == 0x04)
                        .is_some_and(|at| {
                            at >= 1
                                && insts[at - 1].op == 0x20
                                && insts[at - 1].imm == Imm::Idx(*n)
                                && insts[at + 1..k]
                                    .iter()
                                    .all(|x| !matches!(x.op, 0x02..=0x05 | 0x0b | 0x21 | 0x22))
                        });
                    assert!(
                        guarded,
                        "function {f}: bulk op 0xfc {sub} at instruction {k} reads its count \
                         from local {n} outside an `if (n != 0)` guard"
                    );
                    BulkMemorySite::Guarded
                }
                other => panic!(
                    "function {f}: bulk op 0xfc {sub} at instruction {k} has an unrecognised \
                     count operand {other:?} — neither guarded nor a constant nonzero copy"
                ),
            };
            out.push(site);
        }
    }
    out
}

/// PINS the scope of the `memory.copy` / `memory.fill` credits on the live
/// backend: `memory.fill` is emitted only by the guarded `MemSet` lowering;
/// `memory.copy` is emitted by the guarded `MemCopy` lowering AND, with a
/// constant nonzero size, by the aggregate moves (which the captured bodies
/// do not credit). The aggregate moves are pinned on the lowering's own bytes
/// (O0); at the default level the emission pass turns a copy of at most 32
/// bytes into loads and stores, and every copy it leaves is still of one of
/// the two forms. Returns the number of constant-size copies the lowering
/// emits.
pub fn assert_bulk_memory_emission_is_guarded_or_constant_sized() -> usize {
    for shape in BulkMemoryShape::ALL {
        let bytes = wasm::compile_module_with_license(&bulk_memory_ir(shape), &permit_unlicensed())
            .unwrap_or_else(|e| panic!("{shape:?} module must compile: {e}"));
        assert_eq!(
            bulk_memory_sites(&bytes),
            vec![BulkMemorySite::Guarded],
            "{shape:?}: the trust-ir bulk op must lower to exactly one guarded op"
        );
    }
    let module = trust_ir::parser::parse_module(AGGREGATE_MOVES).expect("parses");
    let (bytes, _) = wasm::compile_module_with_evidence_policy_license_optimized(
        &module,
        &wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
        trust_cg_codegen::pipeline::OptLevel::O0,
    )
    .expect("aggregate moves compile");
    let sites = bulk_memory_sites(&bytes);
    assert!(
        !sites.is_empty()
            && sites
                .iter()
                .all(|s| *s == BulkMemorySite::ConstantNonzeroCopy),
        "aggregate moves must lower to constant-nonzero-size memory.copy only: {sites:?}"
    );
    let optimized = wasm::compile_module_with_license(&module, &permit_unlicensed())
        .expect("aggregate moves compile");
    assert!(
        bulk_memory_sites(&optimized)
            .iter()
            .all(|s| *s == BulkMemorySite::ConstantNonzeroCopy),
        "the emission pass leaves only constant-nonzero-size memory.copy"
    );
    sites.len()
}

/// The site classifier has teeth: the live guarded `MemCopy` module with its
/// `if` / `end` replaced by `nop`s (length-preserving) is refused as an
/// unguarded count, and a zero-size constant copy is refused as neither form.
pub fn assert_the_site_classifier_refuses_unguarded_and_zero_sized_ops() {
    let bytes = wasm::compile_module_with_license(
        &bulk_memory_ir(BulkMemoryShape::MemCopy),
        &permit_unlicensed(),
    )
    .expect("MemCopy module compiles");
    let patch = |needle: &[u8], with: &[u8]| {
        let at = bytes
            .windows(needle.len())
            .position(|w| w == needle)
            .expect("the guarded body occurs in the module");
        let mut out = bytes.clone();
        out[at..at + with.len()].copy_from_slice(with);
        out
    };
    // local.get 2; if; local.get 0; local.get 1; local.get 2; memory.copy; end
    let guarded = [
        0x20, 0x02, 0x04, 0x40, 0x20, 0x00, 0x20, 0x01, 0x20, 0x02, 0xfc, 0x0a, 0x00, 0x00, 0x0b,
    ];
    let mut unguarded = guarded;
    unguarded[2..4].copy_from_slice(&[0x01, 0x01]);
    unguarded[14] = 0x01;
    let mut zero_const = unguarded;
    zero_const[8..10].copy_from_slice(&[0x41, 0x00]);
    for (what, candidate) in [
        ("an unguarded count", patch(&guarded, &unguarded)),
        ("a zero-size constant copy", patch(&guarded, &zero_const)),
    ] {
        let refused = std::panic::catch_unwind(|| bulk_memory_sites(&candidate)).is_err();
        assert!(refused, "the site classifier accepted {what}");
    }
}

/// This module's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
