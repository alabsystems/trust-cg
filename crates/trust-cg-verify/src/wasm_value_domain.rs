// trust-cg-verify/wasm_value_domain.rs - P3 wasm value-domain obligations
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: WebAssembly Core Specification, Release 2.0 — §5.4.4 (Memory
//            Instructions, opcode bytes 0x28..=0x40) and §5.4.6 (Numeric
//            Instructions, the 0xc0..=0xc4 sign-extension operators).
//
// P3 ("the value domain") opens the wasm backend to sub-word and FP values: byte
// and half-word loads/stores, f32/f64 memory traffic, and `i32`/`i64`-CARRIED
// narrow integers. Every one of those is a new opcode byte or a new
// representation invariant, and the coverage gate's honesty rests on each of them
// carrying an obligation the verifier can REFUTE. An opcode the backend emits
// with no obligation is uncredited debt, not silent trust — so this module grows
// the verify side to match, keyed on the SPEC OPCODE BYTE (the authority) rather
// than on a `trust_cg_ir::WasmOpcode` variant, which does not yet enumerate the
// sub-word/FP memory surface.
//
// WHAT EACH OBLIGATION BUYS (and what it does NOT):
//
//   * LOADS carry TWO obligations. The first pins the EXTENSION: the memory is
//     pre-filled by a full-width store of a symbolic value, the machine side
//     DECODES the real emitted byte to (access width, zero/sign extension) and
//     rebuilds the little-endian read + extension, and the source side is the
//     INTENDED narrow value extended independently. `i32.load8_u` (0x2d) and
//     `i32.load8_s` (0x2c) differ by ONE BIT of the opcode and produce different
//     values for every byte with bit 7 set, so a slipped byte REFUTES. The
//     second pins the WIDTH INVARIANT of the loaded carrier (`x == zext_n(x)`
//     for `_u`, `x == sext_n(x)` for `_s`) — the property the narrow-arithmetic
//     family then depends on.
//   * STORES carry TWO obligations. The first pins the TRUNCATION (`i32.store8`
//     writes `v & 0xff`, not `v`); the second pins the WIDTH by reading the byte
//     just past the intended access and demanding it is untouched — that is the
//     obligation a `store16`-for-`store8` slip refutes, which the value
//     obligation alone cannot see.
//   * The f32/f64 accesses are, at the VALUE level, bit-identical to the
//     same-width integer accesses (wasm does not canonicalize NaN on load or
//     store). A `f32.load`(0x2a)-for-`i32.load`(0x28) slip is therefore NOT
//     refutable by a value obligation; the discriminator is the wasm TYPE,
//     checked by module validation. The audit row says so rather than implying
//     coverage it does not have.
//   * NARROW ARITHMETIC is not an opcode but a REPRESENTATION: wasm has no type
//     below `i32`, so a `u8`/`i8`/`u16`/`i16` rides in an `i32` and the backend
//     must RE-NORMALIZE after each wrapping op. `narrow_width_proofs` states that
//     obligation directly, over inputs CONSTRUCTED to satisfy the invariant (not
//     constrained by a precondition random sampling would satisfy ~never).
//
// WHAT IS NEVER SELECTED: the `i64` sub-word loads (0x30..=0x35) and stores
// (0x3c..=0x3e) and the `i64` sign-extensions (0xc2..=0xc4). No trust-ir type
// reaches a narrow `i64` carrier, so the lowerer emits none of them; their
// obligations stay built and discharging, and the coverage gate excludes them
// as never selected ([`WASM_VALUE_DOMAIN_UNSELECTED`]) rather than crediting
// evidence for code no module contains. That premise is checked, not assumed:
// [`never_selected_opcodes_in`] scans a module for every excluded byte (and
// the `0xfd` prefix of the v128 forms `GateArch::Wasm` excludes), and the gates
// that pin the exclusions run it over a corpus compiled by the live backend.
//
// WHAT IS DEFERRED, BY NAME: `br_table`, `memory.size`/`memory.grow`, and data
// segments. Each has an entry in [`WASM_VALUE_DOMAIN_DEFERRALS`] naming the
// family that must answer for it and why the per-instruction SMT layer cannot.
// They stay RED IN the denominator — never allowlisted out, never given a weak
// obligation that would launder them green.
//
// WHAT THESE OBLIGATIONS DO NOT COVER, said plainly rather than left implicit:
//
//   * Which `memarg` STATIC OFFSET the lowering CHOSE, in general. The scalar
//     `Load` / `Store` arms emit offset 0, while struct fields, enum tags and
//     lanes, the high half of a 128-bit value, sret slots and parameter /
//     return lanes use a NONZERO offset. The OFFSET obligations below
//     ([`mem_load_offset_obligation`], [`mem_store_offset_obligation`]) state
//     what an offset MEANS — the access at `(base, offset)` reads / writes the
//     bytes trust-ir addresses at `base + offset`, with the spec's no-wrap
//     effective address — over a SYMBOLIC offset, and a skew between the
//     emitted and the intended offset refutes. In this per-byte set the skew
//     is 0: it reads no emitted module. The CREDIT of a selected load / store
//     byte ([`value_domain_discharges_valid`]) additionally requires
//     `wasm_memarg_offset_proofs`, which instantiates the same obligation from
//     a captured module's DECODED memarg offsets against the trust-ir layout
//     offsets of struct field reads and writes. Other nonzero-offset sites
//     (enum tags, niches, nested lanes, i128 halves, sret and parameter lanes)
//     are outside that corpus; the lane differentials (`wasm_g1_lane_semantics`,
//     `wasm_g3_lane_frames`) are their only evidence.
//   * The BOUNDS CHECK. wasm loads and stores TRAP when the effective address
//     leaves the memory, and the model memory is an unbounded array, so nothing
//     here says the backend emits (or the host performs) a bounds check. These
//     are value/width obligations over an in-bounds access, exactly as the
//     div/rem obligations are value obligations over a non-trapping divisor.
//   * The ALIGNMENT hint. wasm's `align` memarg field is advisory (it changes no
//     result), so it carries no value obligation by construction.
//   * The int/FP TYPE distinction, per the note above.

//! P3 value-domain obligations for the WebAssembly backend: sub-word / FP
//! linear-memory accesses, the sign-extension operators, the `i32`-carried
//! narrow-width invariant, and the named deferrals.

use crate::lowering_proof::{
    MachineSideProvenance, ProofObligation, TransvalCheckKind, VerificationConfig,
    verify_by_evaluation_with_config,
};
use crate::smt::SmtExpr;
use crate::verify::VerificationResult;
use crate::wasm_semantics as w;

/// Address width of wasm32 linear memory.
const ADDR_BITS: u32 = 32;

// ===========================================================================
// The P3 opcode inventory
// ===========================================================================

/// Every wasm LOAD opcode byte (spec §5.4.4, 0x28..=0x35), in spec order.
pub const WASM_LOAD_BYTES: &[u8] = &[
    0x28, 0x29, 0x2a, 0x2b, // i32/i64/f32/f64.load
    0x2c, 0x2d, 0x2e, 0x2f, // i32.load8_s/8_u/16_s/16_u
    0x30, 0x31, 0x32, 0x33, 0x34, 0x35, // i64.load8_s..load32_u
];

/// Every wasm STORE opcode byte (spec §5.4.4, 0x36..=0x3e), in spec order.
pub const WASM_STORE_BYTES: &[u8] = &[
    0x36, 0x37, 0x38, 0x39, // i32/i64/f32/f64.store
    0x3a, 0x3b, // i32.store8/store16
    0x3c, 0x3d, 0x3e, // i64.store8/store16/store32
];

/// Every wasm SIGN-EXTENSION operator byte (spec §5.4.6, 0xc0..=0xc4).
pub const WASM_SIGN_EXTEND_BYTES: &[u8] = &[0xc0, 0xc1, 0xc2, 0xc3, 0xc4];

/// The complete P3 value-domain opcode surface, in spec order: the 14 loads, the
/// 9 stores, and the 5 sign-extension operators. Every byte keeps its
/// obligation set, but the 12 in [`WASM_VALUE_DOMAIN_UNSELECTED`] are never
/// selected by the lowerer and are excluded from the credited denominator
/// (see [`value_domain_unselected`]). Deferred forms
/// (`br_table`, `memory.size`, `memory.grow`, data segments) are NOT here — they
/// are enumerated by [`WASM_VALUE_DOMAIN_DEFERRALS`] instead, so a row can never
/// be both "has an obligation" and "deferred".
pub fn all_wasm_value_domain_bytes() -> Vec<u8> {
    let mut v = WASM_LOAD_BYTES.to_vec();
    v.extend_from_slice(WASM_STORE_BYTES);
    v.extend_from_slice(WASM_SIGN_EXTEND_BYTES);
    v
}

/// The P3 bytes the current wasm lowerer NEVER selects: the `i64` sub-word
/// loads (0x30..=0x35) and stores (0x3c..=0x3e), and the `i64` sign-extension
/// operators (0xc2..=0xc4).
///
/// Their obligations are built and required to discharge exactly like the
/// selected bytes' (`tests/wasm_value_domain_gate.rs`), so each row re-enters
/// the credited denominator unchanged the moment the lowering selects it. They
/// are not credited today because a credit for an opcode no emitted module
/// contains covers no emitted code.
pub const WASM_VALUE_DOMAIN_UNSELECTED: &[u8] = &[
    0x30, 0x31, 0x32, 0x33, 0x34, 0x35, // i64.load8_s..load32_u
    0x3c, 0x3d, 0x3e, // i64.store8/store16/store32
    0xc2, 0xc3, 0xc4, // i64.extend8_s/extend16_s/extend32_s
];

/// Why a P3 byte is excluded as never selected, or `None` for a byte the
/// lowerer emits (or one outside the surface).
pub fn value_domain_unselected(byte: u8) -> Option<&'static str> {
    if !WASM_VALUE_DOMAIN_UNSELECTED.contains(&byte) {
        return None;
    }
    Some(if w::decode_sign_extend(byte).is_some() {
        "i64 sign-extension operator, never selected by the current wasm lowerer: a narrow \
         integer rides in an i32 carrier, so re-canonicalization emits only i32.extend8_s / \
         i32.extend16_s (emit_canonicalize refuses a narrow non-i32 carrier) and the lowerer has \
         no i64.extendN_s emitter; not in the emitted set. Its obligations stay built and \
         discharging, so the row re-enters the denominator unchanged when selection lands"
    } else {
        "i64 sub-word memory access, never selected by the current wasm lowerer: int_repr_of \
         gives an i64 carrier only to the 64-bit integers, so mem_ops never reaches the (i64, \
         8|16|32) arms of mem_ops_for (pinned by the lane's \
         no_scalar_type_selects_an_i64_sub_word_access); not in the emitted set. Its obligations \
         stay built and discharging, so the row re-enters the denominator unchanged when \
         selection lands"
    })
}

/// The `0xfd` prefix of every v128 / SIMD instruction. The coverage gate's
/// never-selected wasm rows (`v128.load` / `store` / `const` and the lane-wise
/// ops) all sit under it.
pub const SIMD_PREFIX: u8 = 0xfd;

/// Every never-selected instruction an emitted module contains, as `(defined
/// function ordinal, byte offset in its body, description)`: each instruction
/// whose opcode byte is in [`WASM_VALUE_DOMAIN_UNSELECTED`], and each
/// `0xfd`-prefixed (v128 / SIMD) instruction.
///
/// This is the check that keeps the never-selected EXCLUSIONS honest: an
/// excluded row is outside the credited denominator only while no emitted
/// module contains it, so the gates that pin those exclusions run it over
/// modules compiled by the live backend. `Err` when the module, or a body,
/// stops decoding at any other opcode — absence cannot be claimed over bytes
/// the walk did not read. A `0xfd` instruction ends the walk of its body (its
/// immediates are not modelled) after it is reported.
pub fn never_selected_opcodes_in(wasm: &[u8]) -> Result<Vec<(usize, usize, String)>, String> {
    use crate::wasm_abi_proofs::{AbiDecodeError, decode_insts_until_unknown, decode_module};
    let module = decode_module(wasm).map_err(|e| format!("the module does not decode: {e:?}"))?;
    let mut hits = Vec::new();
    for (f, body) in module.bodies.iter().enumerate() {
        let (insts, stop) = decode_insts_until_unknown(&body.code);
        for i in &insts {
            if WASM_VALUE_DOMAIN_UNSELECTED.contains(&i.op) {
                let what = value_domain_mnemonic(i.op).unwrap_or("<unnamed>");
                hits.push((f, i.at, format!("{what} (0x{:02x})", i.op)));
            }
        }
        match stop {
            None => {}
            Some(AbiDecodeError::UnknownOpcode { at, opcode }) if opcode == SIMD_PREFIX => {
                hits.push((f, at, "a 0xfd-prefixed v128 / SIMD instruction".to_string()));
            }
            Some(e) => return Err(format!("function {f} does not decode: {e:?}")),
        }
    }
    Ok(hits)
}

/// The spec mnemonic for a P3 value-domain opcode byte, for report rows.
/// `None` for a byte outside the P3 surface.
pub fn value_domain_mnemonic(byte: u8) -> Option<&'static str> {
    if let Some(op) = w::decode_mem_op(byte) {
        return Some(op.mnemonic);
    }
    w::decode_sign_extend(byte).map(|op| op.mnemonic)
}

// ===========================================================================
// Named deferrals — debt with a name and a reason, never a weak obligation
// ===========================================================================

/// One honestly DEFERRED P3 construct: what it is, which evidence family owes an
/// answer for it, and why the per-instruction SMT layer cannot supply one.
///
/// These stay RED IN the value-domain denominator. Inventing a weak
/// per-instruction obligation for any of them (e.g. proving only `br_table`'s
/// index CLAMP while saying nothing about which block a label denotes) would
/// launder the row green while refuting none of the wrong lowerings that matter,
/// which is precisely the dishonesty the gate exists to prevent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WasmValueDomainDeferral {
    /// Display name, including the opcode byte where the construct has one.
    pub name: &'static str,
    /// The opcode byte, when the construct is a single instruction. `None` for
    /// module-level constructs (data segments).
    pub opcode_byte: Option<u8>,
    /// The evidence family that must ultimately discharge this.
    pub family: &'static str,
    /// Why the per-instruction value/SMT layer cannot express it today.
    pub reason: &'static str,
}

/// The four named P3 deferrals. Pinned by `tests/wasm_value_domain_gate.rs`:
/// removing one requires landing its evidence, and adding one is a deliberate,
/// reviewable admission of debt.
pub const WASM_VALUE_DOMAIN_DEFERRALS: &[WasmValueDomainDeferral] = &[
    WasmValueDomainDeferral {
        name: "br_table (0x0e)",
        opcode_byte: Some(0x0e),
        family: "relooper / CFG structural bisimulation (crate::cfg_proofs, \
                 crate::switch_proofs)",
        reason: "br_table is a CONTROL-FLOW instruction: its immediate is a vector of LABEL \
                 indices plus a default label, and a label denotes a block boundary determined \
                 by the enclosing block/loop NESTING DEPTH at the emission point. The \
                 per-instruction SMT layer sees values, not label scopes, so it cannot state \
                 which block a label denotes and therefore cannot refute the wrong lowering that \
                 matters (a correct index-to-label table wired to the wrong depth). The only \
                 part that IS value-expressible — the spec's `i >= n => default` clamp — would, \
                 on its own, be a weak obligation: it passes for every mis-wired table, so \
                 crediting it would launder the row green. The index-to-label SELECTION function \
                 belongs to the switch/jump-table family and the label-to-block binding to the \
                 relooper bisimulation; until the relooper argument is extended to the n-way \
                 br_table edge this row is RED",
    },
    WasmValueDomainDeferral {
        name: "memory.size (0x3f)",
        opcode_byte: Some(0x3f),
        family: "wasm memory model (crate::wasm_semantics linear memory)",
        reason: "memory.size pushes the current linear-memory size in 64 KiB pages. The memory \
                 model here is an UNBOUNDED byte array `(Array (BitVec 32) (BitVec 8))` with no \
                 page-count and no bound component, so the instruction's result is not a function \
                 of anything the model represents; any obligation written against the current \
                 model would be vacuous. Promotion requires a memory model carrying an explicit \
                 page count alongside the byte array",
    },
    WasmValueDomainDeferral {
        name: "memory.grow (0x40)",
        opcode_byte: Some(0x40),
        family: "wasm memory model (crate::wasm_semantics linear memory)",
        reason: "memory.grow pops a page delta, may grow the memory, and pushes the PREVIOUS page \
                 count or -1 when growth is refused. Both the state change (page count) and the \
                 refusal are outside the unbounded-byte-array model, and the refusal is a HOST \
                 decision the module cannot determine, so neither the returned value nor the \
                 zero-initialization of the new pages is expressible here. Promotion requires a \
                 page-counted memory model plus a host-growth-policy assumption stated as such",
    },
    WasmValueDomainDeferral {
        name: "data segments (module section 11; memory.init 0xfc 8 / data.drop 0xfc 9)",
        opcode_byte: None,
        family: "module/instantiation gate (no per-instruction obligation exists)",
        reason: "an ACTIVE data segment is not an instruction at all: the host copies its bytes \
                 into linear memory during INSTANTIATION, before any code runs, so there is no \
                 emitted opcode for a per-instruction obligation to decode. Its correctness is a \
                 module-level property (segment offset in bounds, bytes placed little-endian at \
                 the declared offset, no overlap with the shadow stack) belonging to a \
                 module/instantiation gate that does not exist yet. The PASSIVE form is driven by \
                 the bulk-memory opcodes memory.init (0xfc 8) and data.drop (0xfc 9), which the \
                 backend does not emit; those would need their own obligations if it ever does",
    },
];

/// The named deferral for a P3 opcode byte, if that byte is deferred.
pub fn value_domain_deferral(byte: u8) -> Option<&'static WasmValueDomainDeferral> {
    WASM_VALUE_DOMAIN_DEFERRALS
        .iter()
        .find(|d| d.opcode_byte == Some(byte))
}

// ===========================================================================
// Linear-memory obligations (loads + stores), reconstructed from the real byte
// ===========================================================================

fn reconstructed_obligation(
    name: String,
    trust_ir_expr: SmtExpr,
    machine_expr: SmtExpr,
    inputs: Vec<(String, u32)>,
    from_opcode: String,
    arity: u8,
) -> ProofObligation {
    ProofObligation {
        name,
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed { from_opcode, arity },
    }
}

/// The little-endian narrowing of `v` to `bits`, without an identity `extract`
/// when `bits` already IS the value's width.
fn low_bits(v: &SmtExpr, bits: u32) -> SmtExpr {
    if bits >= v.bv_width() {
        v.clone()
    } else {
        v.clone().extract(bits - 1, 0)
    }
}

/// LOAD obligation #1 — the EXTENSION and the access WIDTH.
///
/// `intended_byte` names the load the lowering meant to emit; `emitted_byte` is
/// the byte actually in the module. The machine side DECODES `emitted_byte` and
/// rebuilds `extend(read_le(mem, p, access_bytes))`; the source side is built
/// INDEPENDENTLY from the INTENDED access width and extension. Memory is
/// pre-filled by a full-width little-endian store of a symbolic `v` at `p`, so
/// the two sides agree IFF the emitted byte has the intended width AND the
/// intended extension — `i32.load8_s` (0x2c) for `i32.load8_u` (0x2d) diverges
/// for every `v` with bit 7 set.
///
/// Returns `None` (fail closed, therefore no credit) when `emitted_byte` is not
/// a load, or when its result width differs from the intended one — a
/// cross-width slip is a type error, not a value the obligation can compare.
pub fn mem_load_value_obligation(intended_byte: u8, emitted_byte: u8) -> Option<ProofObligation> {
    let intended = w::decode_mem_op(intended_byte)?;
    let emitted = w::decode_mem_op(emitted_byte)?;
    if !intended.is_load() || !emitted.is_load() {
        return None;
    }
    if emitted.value_bits != intended.value_bits {
        return None;
    }

    let value_bits = intended.value_bits;
    let p = SmtExpr::var("recon_p", ADDR_BITS);
    let v = SmtExpr::var("recon_v", value_bits);

    // Memory holding `v` at `p`, written little-endian at the FULL value width —
    // independent of the emitted byte, so the read is what is under test.
    let mem = w::encode_store_n(w::zero_memory(), p.clone(), v.clone(), value_bits / 8);
    let machine_expr = w::encode_mem_load(mem, p, emitted)?;

    // Source: the INTENDED narrow value, extended independently of the byte model.
    let narrow = low_bits(&v, intended.access_bits);
    let extra = value_bits - intended.access_bits;
    let trust_ir_expr = match intended.extend()? {
        w::WasmLoadExtend::None => narrow,
        w::WasmLoadExtend::Zero => narrow.zero_ext(extra),
        w::WasmLoadExtend::Sign => narrow.sign_ext(extra),
    };

    Some(reconstructed_obligation(
        format!(
            "RECONSTRUCTED wasm {} (0x{:02x}) -> extension+width of a linear-memory read",
            intended.mnemonic, emitted.byte
        ),
        trust_ir_expr,
        machine_expr,
        vec![
            ("recon_p".to_string(), ADDR_BITS),
            ("recon_v".to_string(), value_bits),
        ],
        format!("{} (0x{:02x})", emitted.mnemonic, emitted.byte),
        1,
    ))
}

/// LOAD obligation #2 — the loaded carrier respects its NARROW WIDTH INVARIANT.
///
/// A `..._u` load must yield a carrier with all bits above the access width
/// CLEAR (`x == zext_n(x[n-1:0])`); a `..._s` load must yield one whose upper
/// bits REPLICATE bit `n-1` (`x == sext_n(x[n-1:0])`). This is the property the
/// narrow-arithmetic family assumes of its inputs, so it is stated here rather
/// than assumed. It is refutable in the direction that matters: an `_s` byte
/// emitted where `_u` was intended fails the unsigned invariant for every
/// negative byte.
///
/// `None` for a full-width load (the invariant is trivially the whole carrier)
/// and for a store.
pub fn mem_load_invariant_obligation(
    intended_byte: u8,
    emitted_byte: u8,
) -> Option<ProofObligation> {
    let intended = w::decode_mem_op(intended_byte)?;
    let emitted = w::decode_mem_op(emitted_byte)?;
    if !intended.is_load() || !emitted.is_load() {
        return None;
    }
    if emitted.value_bits != intended.value_bits {
        return None;
    }
    if intended.access_bits == intended.value_bits {
        return None; // full-width load: no narrow carrier, no invariant to state
    }

    let value_bits = intended.value_bits;
    let p = SmtExpr::var("recon_p", ADDR_BITS);
    let v = SmtExpr::var("recon_v", value_bits);
    let mem = w::encode_store_n(w::zero_memory(), p.clone(), v.clone(), value_bits / 8);
    let loaded = w::encode_mem_load(mem, p, emitted)?;

    let n = intended.access_bits;
    let machine_expr = match intended.extend()? {
        w::WasmLoadExtend::Zero => w::narrow_invariant_u(loaded, n),
        w::WasmLoadExtend::Sign => w::narrow_invariant_s(loaded, n),
        w::WasmLoadExtend::None => return None,
    };

    Some(reconstructed_obligation(
        format!(
            "RECONSTRUCTED wasm {} (0x{:02x}) -> loaded carrier respects its {n}-bit width \
             invariant",
            intended.mnemonic, emitted.byte
        ),
        SmtExpr::bool_const(true),
        machine_expr,
        vec![
            ("recon_p".to_string(), ADDR_BITS),
            ("recon_v".to_string(), value_bits),
        ],
        format!("{} (0x{:02x})", emitted.mnemonic, emitted.byte),
        1,
    ))
}

/// STORE obligation #1 — the value written is the operand TRUNCATED to the
/// access width.
///
/// The machine side stores through the DECODED emitted byte, then reads back
/// exactly the INTENDED access width; the source side is the intended truncation
/// `v[n-1:0]`. A NARROWER emitted store leaves the upper intended bytes at their
/// pre-store value and diverges.
pub fn mem_store_value_obligation(intended_byte: u8, emitted_byte: u8) -> Option<ProofObligation> {
    let intended = w::decode_mem_op(intended_byte)?;
    let emitted = w::decode_mem_op(emitted_byte)?;
    if intended.is_load() || emitted.is_load() {
        return None;
    }
    // A byte that pops a DIFFERENT stack type (an i64 store where an i32 store
    // was intended) is a TYPE error caught by module validation, not a value
    // difference this obligation could ever see — both write the same low bytes.
    // Fail closed rather than credit a comparison that cannot refute it.
    if emitted.value_bits != intended.value_bits {
        return None;
    }
    let value_bits = intended.value_bits;
    // Fail closed rather than build an out-of-range extract on the value operand.
    if emitted.access_bits > value_bits {
        return None;
    }

    let p = SmtExpr::var("recon_p", ADDR_BITS);
    let v = SmtExpr::var("recon_v", value_bits);
    let mem = w::encode_mem_store(w::zero_memory(), p.clone(), v.clone(), emitted)?;
    let machine_expr = w::encode_load_n(mem, p, intended.access_bytes());
    let trust_ir_expr = low_bits(&v, intended.access_bits);

    Some(reconstructed_obligation(
        format!(
            "RECONSTRUCTED wasm {} (0x{:02x}) -> stored value is the operand truncated to {} bits",
            intended.mnemonic, emitted.byte, intended.access_bits
        ),
        trust_ir_expr,
        machine_expr,
        vec![
            ("recon_p".to_string(), ADDR_BITS),
            ("recon_v".to_string(), value_bits),
        ],
        format!("{} (0x{:02x})", emitted.mnemonic, emitted.byte),
        2,
    ))
}

/// STORE obligation #2 — the store touches NO byte past its access width.
///
/// The byte at `p + intended_access_bytes` must still hold its pre-store value
/// (zero, from the zero-initialized model memory). This is the obligation a
/// `i32.store16` (0x3b) emitted where `i32.store8` (0x3a) was intended REFUTES —
/// the value obligation alone cannot see a too-WIDE store, because the low bytes
/// still match. Together the pair pins the access width exactly.
pub fn mem_store_width_obligation(intended_byte: u8, emitted_byte: u8) -> Option<ProofObligation> {
    let intended = w::decode_mem_op(intended_byte)?;
    let emitted = w::decode_mem_op(emitted_byte)?;
    if intended.is_load() || emitted.is_load() {
        return None;
    }
    // Same TYPE-slip fail-closed rule as the value obligation above.
    if emitted.value_bits != intended.value_bits {
        return None;
    }
    let value_bits = intended.value_bits;
    if emitted.access_bits > value_bits {
        return None;
    }

    let p = SmtExpr::var("recon_p", ADDR_BITS);
    let v = SmtExpr::var("recon_v", value_bits);
    let mem = w::encode_mem_store(w::zero_memory(), p.clone(), v.clone(), emitted)?;
    // The guard byte offset comes from the INTENDED width — it is a property of
    // the lowering's intent, not of whatever byte landed in the module.
    let guard_addr = p.bvadd(SmtExpr::bv_const(
        u64::from(intended.access_bytes()),
        ADDR_BITS,
    ));
    let machine_expr = w::encode_load_n(mem, guard_addr, 1);

    Some(reconstructed_obligation(
        format!(
            "RECONSTRUCTED wasm {} (0x{:02x}) -> writes no byte past its {}-bit access",
            intended.mnemonic, emitted.byte, intended.access_bits
        ),
        SmtExpr::bv_const(0, 8),
        machine_expr,
        vec![
            ("recon_p".to_string(), ADDR_BITS),
            ("recon_v".to_string(), value_bits),
        ],
        format!("{} (0x{:02x})", emitted.mnemonic, emitted.byte),
        2,
    ))
}

// ===========================================================================
// The memarg static offset
// ===========================================================================

/// The no-trap precondition and the trust-ir address of an access at
/// `(recon_p, recon_off)`: `recon_p + recon_off` as trust-ir computes a byte
/// GEP on wasm32. Under the precondition the sum does not wrap, which is also
/// the only case trust-ir defines (a GEP past `2^32 - 1`, or an access past the
/// address space, is UB there), so the obligation covers every defined access.
fn offset_access(n_bytes: u32) -> (SmtExpr, SmtExpr, SmtExpr, SmtExpr) {
    let p = SmtExpr::var("recon_p", ADDR_BITS);
    let off = SmtExpr::var("recon_off", ADDR_BITS);
    let pre = w::encode_access_does_not_trap(p.clone(), off.clone(), n_bytes);
    let q = p.clone().bvadd(off.clone());
    (p, off, pre, q)
}

/// The emitted offset: the intended symbolic offset plus `skew` (mod 2^32).
/// `skew == 0` is the honest lowering; a nonzero skew is a negative control.
fn skewed(off: &SmtExpr, skew: u32) -> SmtExpr {
    if skew == 0 {
        off.clone()
    } else {
        off.clone()
            .bvadd(SmtExpr::bv_const(u64::from(skew), ADDR_BITS))
    }
}

/// LOAD OFFSET obligation — the access at `(base, offset)` reads the value
/// trust-ir stored at `base + offset`.
///
/// Memory holds a symbolic `v` at the trust-ir address `q = p + off` (full
/// value width, little-endian); the machine side DECODES `emitted_byte` and
/// loads with the memarg offset `off + skew` through the spec's no-wrap
/// effective address; the source side is the intended narrow value extended
/// independently, exactly as in [`mem_load_value_obligation`]. The offset is
/// SYMBOLIC, so the statement covers every offset the lowering can emit, under
/// the precondition that the access does not trap. A shifted offset (`skew !=
/// 0`) reads other bytes and REFUTES.
pub fn mem_load_offset_obligation(
    intended_byte: u8,
    emitted_byte: u8,
    skew: u32,
) -> Option<ProofObligation> {
    let intended = w::decode_mem_op(intended_byte)?;
    let emitted = w::decode_mem_op(emitted_byte)?;
    if !intended.is_load() || !emitted.is_load() || emitted.value_bits != intended.value_bits {
        return None;
    }
    let value_bits = intended.value_bits;
    let (p, off, pre, q) = offset_access(value_bits / 8);
    let v = SmtExpr::var("recon_v", value_bits);
    let mem = w::encode_store_n(w::zero_memory(), q, v.clone(), value_bits / 8);
    let machine_expr = w::encode_mem_load_at(mem, p, skewed(&off, skew), emitted)?;

    let narrow = low_bits(&v, intended.access_bits);
    let extra = value_bits - intended.access_bits;
    let trust_ir_expr = match intended.extend()? {
        w::WasmLoadExtend::None => narrow,
        w::WasmLoadExtend::Zero => narrow.zero_ext(extra),
        w::WasmLoadExtend::Sign => narrow.sign_ext(extra),
    };
    let mut ob = reconstructed_obligation(
        format!(
            "RECONSTRUCTED wasm {} (0x{:02x}) at memarg offset off{} -> reads the value at \
             trust-ir address base + off",
            intended.mnemonic,
            emitted.byte,
            if skew == 0 {
                String::new()
            } else {
                format!(" + {skew}")
            }
        ),
        trust_ir_expr,
        machine_expr,
        vec![
            ("recon_p".to_string(), ADDR_BITS),
            ("recon_off".to_string(), ADDR_BITS),
            ("recon_v".to_string(), value_bits),
        ],
        format!("{} (0x{:02x})", emitted.mnemonic, emitted.byte),
        1,
    );
    ob.preconditions = vec![pre];
    Some(ob)
}

/// STORE OFFSET obligation — the access at `(base, offset)` writes the bytes
/// trust-ir addresses at `base + offset`.
///
/// The machine side stores a symbolic `v` through the DECODED `emitted_byte`
/// with memarg offset `off + skew` (spec no-wrap effective address) into zeroed
/// memory; the source side reads the INTENDED access width back at the trust-ir
/// address `p + off` and demands the truncated operand. A shifted offset
/// leaves those bytes zero and REFUTES.
pub fn mem_store_offset_obligation(
    intended_byte: u8,
    emitted_byte: u8,
    skew: u32,
) -> Option<ProofObligation> {
    let intended = w::decode_mem_op(intended_byte)?;
    let emitted = w::decode_mem_op(emitted_byte)?;
    if intended.is_load() || emitted.is_load() || emitted.value_bits != intended.value_bits {
        return None;
    }
    let value_bits = intended.value_bits;
    if emitted.access_bits > value_bits {
        return None;
    }
    let (p, off, pre, q) = offset_access(intended.access_bytes());
    let v = SmtExpr::var("recon_v", value_bits);
    let mem = w::encode_mem_store_at(w::zero_memory(), p, skewed(&off, skew), v.clone(), emitted)?;
    let machine_expr = w::encode_load_n(mem, q, intended.access_bytes());
    let trust_ir_expr = low_bits(&v, intended.access_bits);
    let mut ob = reconstructed_obligation(
        format!(
            "RECONSTRUCTED wasm {} (0x{:02x}) at memarg offset off{} -> writes the bytes at \
             trust-ir address base + off",
            intended.mnemonic,
            emitted.byte,
            if skew == 0 {
                String::new()
            } else {
                format!(" + {skew}")
            }
        ),
        trust_ir_expr,
        machine_expr,
        vec![
            ("recon_p".to_string(), ADDR_BITS),
            ("recon_off".to_string(), ADDR_BITS),
            ("recon_v".to_string(), value_bits),
        ],
        format!("{} (0x{:02x})", emitted.mnemonic, emitted.byte),
        2,
    );
    ob.preconditions = vec![pre];
    Some(ob)
}

// ===========================================================================
// Sign-extension operator obligations (0xc0..=0xc4)
// ===========================================================================

/// SIGN-EXTEND obligation #1 — the operator sign-extends from the width its
/// opcode byte names.
///
/// Source: the trust-ir `Sextend { from: iN, to: iW }` of the carrier's low `N`
/// bits, at the INTENDED `N`. Machine: the extension rebuilt at the width
/// DECODED from the emitted byte. `i32.extend16_s` (0xc1) emitted for
/// `i32.extend8_s` (0xc0) keeps bits 8..15 instead of overwriting them and
/// diverges for every carrier whose byte 1 is not the sign fill.
///
/// Credited by PROVENANCE, exactly like the other reconstructions: a CORRECT
/// emission reconstructs to the same expression on both sides, and the
/// non-vacuity comes from the machine side being built from the REAL byte.
pub fn sign_extend_value_obligation(
    intended_byte: u8,
    emitted_byte: u8,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_sextend;

    let intended = w::decode_sign_extend(intended_byte)?;
    let emitted = w::decode_sign_extend(emitted_byte)?;
    if emitted.value_bits != intended.value_bits {
        return None;
    }

    let width = intended.value_bits;
    let x = SmtExpr::var("recon_a", width);
    let machine_expr = w::encode_sign_extend_in_place(x.clone(), emitted.from_bits);
    let trust_ir_expr = encode_trust_ir_sextend(
        intended.from_bits,
        width,
        x.clone().extract(intended.from_bits - 1, 0),
    );

    Some(reconstructed_obligation(
        format!(
            "RECONSTRUCTED wasm {} (0x{:02x}) -> trust-ir Sextend i{}->i{width}",
            intended.mnemonic, emitted.byte, intended.from_bits
        ),
        trust_ir_expr,
        machine_expr,
        vec![("recon_a".to_string(), width)],
        format!("{} (0x{:02x})", emitted.mnemonic, emitted.byte),
        1,
    ))
}

/// SIGN-EXTEND obligation #2 — the single-opcode operator agrees with the
/// SHIFT-PAIR expansion a backend emits when it does not use the 0xc0 block.
///
/// Source: `(x << (W - N)) >>s (W - N)` built from the FAITHFUL amount-masked
/// wasm shift encoders. Machine: the operator at the DECODED width. The two
/// sides are structurally distinct expression trees, so this is a genuinely
/// non-degenerate identity — and it is the exact equivalence a lowering relies
/// on when it chooses between the two sequences.
pub fn sign_extend_shift_pair_obligation(
    intended_byte: u8,
    emitted_byte: u8,
) -> Option<ProofObligation> {
    let intended = w::decode_sign_extend(intended_byte)?;
    let emitted = w::decode_sign_extend(emitted_byte)?;
    if emitted.value_bits != intended.value_bits {
        return None;
    }

    let width = intended.value_bits;
    let x = SmtExpr::var("recon_a", width);
    let machine_expr = w::encode_sign_extend_in_place(x.clone(), emitted.from_bits);
    let trust_ir_expr = w::encode_narrow_shift_sext(x, intended.from_bits);

    Some(reconstructed_obligation(
        format!(
            "RECONSTRUCTED wasm {} (0x{:02x}) -> equals the shl/shr_s narrowing expansion",
            intended.mnemonic, emitted.byte
        ),
        trust_ir_expr,
        machine_expr,
        vec![("recon_a".to_string(), width)],
        format!("{} (0x{:02x})", emitted.mnemonic, emitted.byte),
        1,
    ))
}

/// SIGN-EXTEND obligation #3 — the operator's RESULT respects the signed narrow
/// width invariant `x == sext_n(x[n-1:0])`, i.e. it re-establishes the carrier
/// representation the narrow-arithmetic family assumes.
pub fn sign_extend_invariant_obligation(
    intended_byte: u8,
    emitted_byte: u8,
) -> Option<ProofObligation> {
    let intended = w::decode_sign_extend(intended_byte)?;
    let emitted = w::decode_sign_extend(emitted_byte)?;
    if emitted.value_bits != intended.value_bits {
        return None;
    }

    let width = intended.value_bits;
    let x = SmtExpr::var("recon_a", width);
    let extended = w::encode_sign_extend_in_place(x, emitted.from_bits);
    let machine_expr = w::narrow_invariant_s(extended, intended.from_bits);

    Some(reconstructed_obligation(
        format!(
            "RECONSTRUCTED wasm {} (0x{:02x}) -> result respects the {}-bit signed width \
             invariant",
            intended.mnemonic, emitted.byte, intended.from_bits
        ),
        SmtExpr::bool_const(true),
        machine_expr,
        vec![("recon_a".to_string(), width)],
        format!("{} (0x{:02x})", emitted.mnemonic, emitted.byte),
        1,
    ))
}

// ===========================================================================
// Per-byte obligation set + the coverage-gate credit hook
// ===========================================================================

/// Every obligation the P3 inventory holds for one opcode byte, reconstructed
/// from THAT byte (intended == emitted, the honest lowering).
///
/// Empty for a byte outside the P3 surface — the caller must treat an empty set
/// as NO CREDIT, never as trivially satisfied.
pub fn obligations_for_byte(byte: u8) -> Vec<ProofObligation> {
    let mut out = Vec::new();
    if let Some(op) = w::decode_mem_op(byte) {
        if op.is_load() {
            out.extend(mem_load_value_obligation(byte, byte));
            out.extend(mem_load_invariant_obligation(byte, byte));
            out.extend(mem_load_offset_obligation(byte, byte, 0));
        } else {
            out.extend(mem_store_value_obligation(byte, byte));
            out.extend(mem_store_width_obligation(byte, byte));
            out.extend(mem_store_offset_obligation(byte, byte, 0));
        }
    } else if w::decode_sign_extend(byte).is_some() {
        out.extend(sign_extend_value_obligation(byte, byte));
        out.extend(sign_extend_shift_pair_obligation(byte, byte));
        out.extend(sign_extend_invariant_obligation(byte, byte));
    }
    out
}

/// Every P3 per-opcode obligation, in spec-byte order.
pub fn all_value_domain_obligations() -> Vec<ProofObligation> {
    all_wasm_value_domain_bytes()
        .into_iter()
        .flat_map(obligations_for_byte)
        .collect()
}

/// The coverage-gate credit hook: does the FULL obligation set for `byte`
/// discharge `Valid` — and, for a load or store byte the lowerer selects, is
/// its emitted memarg offset bound to the trust-ir layout offset?
///
/// Fails closed — `false` for a byte with no obligations, for any obligation
/// that is not tagged [`MachineSideProvenance::Reconstructed`], and for any that
/// does not discharge `Valid`. Mirrors
/// `wasm_function_verifier::reconstruction_discharges_valid` exactly, except that
/// a P3 byte must clear EVERY one of its obligations, not just one: the store
/// pair only pins the access width when both halves hold. A selected load or
/// store byte must also pass
/// [`crate::wasm_memarg_offset_proofs::memarg_offset_discharges_valid`]: the
/// offset obligation instantiated from DECODED emitted offsets of captured
/// field accesses, with its shifted- and dropped-offset controls refuting. A
/// never-selected byte has no emitted access to bind, so its set alone is
/// checked (it is excluded from the credited denominator either way).
///
/// This is [`value_domain_discharges_valid_over`] over the captured corpus
/// [`crate::wasm_memarg_offset_proofs::MEMARG_FIELDS_TIR`] /
/// [`crate::wasm_memarg_offset_proofs::MEMARG_FIELDS_WASM`].
pub fn value_domain_discharges_valid(byte: u8, config: &VerificationConfig) -> bool {
    value_domain_discharges_valid_over(
        byte,
        config,
        crate::wasm_memarg_offset_proofs::MEMARG_FIELDS_TIR,
        crate::wasm_memarg_offset_proofs::MEMARG_FIELDS_WASM,
    )
}

/// [`value_domain_discharges_valid`] with the memarg-offset binding of a
/// selected load or store byte taken over the corpus `(tir, wasm)` through
/// [`crate::wasm_memarg_offset_proofs::memarg_offset_credit_failures`], so a
/// corpus whose emitted offsets do not match the trust-ir layout withdraws the
/// credit of every byte it touches.
pub fn value_domain_discharges_valid_over(
    byte: u8,
    config: &VerificationConfig,
    tir: &str,
    wasm: &[u8],
) -> bool {
    let obligations = obligations_for_byte(byte);
    if obligations.is_empty() {
        return false;
    }
    let set_holds = obligations.iter().all(|ob| {
        ob.is_reconstructed()
            && matches!(
                verify_by_evaluation_with_config(ob, config),
                VerificationResult::Valid
            )
    });
    let selected_access =
        w::decode_mem_op(byte).is_some() && value_domain_unselected(byte).is_none();
    set_holds
        && (!selected_access
            || crate::wasm_memarg_offset_proofs::memarg_offset_credit_failures(
                byte, tir, wasm, config,
            )
            .is_empty())
}

// ===========================================================================
// Narrow-width arithmetic: the i32-carried u8/u16/i8/i16 representation
// ===========================================================================

/// The narrow integer domains the wasm backend carries in an `i32`: `(bits,
/// signed, tag)`.
const NARROW_DOMAINS: &[(u32, bool, &str)] = &[
    (8, false, "u8"),
    (8, true, "i8"),
    (16, false, "u16"),
    (16, true, "i16"),
];

/// Build the `i32` carrier of a narrow `n`-bit value, per the domain's
/// representation: zero-filled above bit `n-1` for an unsigned domain,
/// sign-filled for a signed one.
fn carrier(narrow: SmtExpr, n: u32, signed: bool) -> SmtExpr {
    if signed {
        narrow.sign_ext(32 - n)
    } else {
        narrow.zero_ext(32 - n)
    }
}

/// Re-normalize an `i32` carrier back into the domain's representation — the
/// sequence the backend MUST emit after a wrapping narrow op.
fn renormalize(x: SmtExpr, n: u32, signed: bool) -> SmtExpr {
    if signed {
        w::encode_narrow_shift_sext(x, n)
    } else {
        w::encode_narrow_mask_u(x, n)
    }
}

/// The narrow domain's width invariant on an `i32` carrier, as a Bool.
fn invariant(x: SmtExpr, n: u32, signed: bool) -> SmtExpr {
    if signed {
        w::narrow_invariant_s(x, n)
    } else {
        w::narrow_invariant_u(x, n)
    }
}

/// The binary narrow ops whose `i32`-carried lowering must re-normalize:
/// `(tag, at-narrow-width builder, i32 wasm builder)`.
type NarrowBinOp = (
    &'static str,
    fn(SmtExpr, SmtExpr) -> SmtExpr,
    fn(SmtExpr, SmtExpr) -> SmtExpr,
);

fn narrow_bin_ops() -> Vec<NarrowBinOp> {
    vec![
        ("add", |a, b| a.bvadd(b), w::encode_add as fn(_, _) -> _),
        ("sub", |a, b| a.bvsub(b), w::encode_sub),
        ("mul", |a, b| a.bvmul(b), w::encode_mul),
        ("and", |a, b| a.bvand(b), w::encode_and),
        ("or", |a, b| a.bvor(b), w::encode_or),
        ("xor", |a, b| a.bvxor(b), w::encode_xor),
    ]
}

fn narrow_obligation(
    name: String,
    trust_ir_expr: SmtExpr,
    machine_expr: SmtExpr,
    inputs: Vec<(String, u32)>,
) -> ProofObligation {
    ProofObligation {
        machine_side_provenance: MachineSideProvenance::StaticDb,
        name,
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
    }
}

/// The NARROW-WIDTH obligations: an `i32`-carried `u8`/`i8`/`u16`/`i16` value
/// respects its width invariant across the backend's wrapping arithmetic.
///
/// # The obligation shape
///
/// For each narrow domain and each wrapping op, over inputs CONSTRUCTED to
/// satisfy the invariant (fresh `n`-bit leaves lifted into the carrier — NOT a
/// precondition, which 32-bit random sampling would satisfy for ~none of its
/// samples and pass vacuously):
///
/// ```text
///   source  = carrier_n( op_n( a_n, b_n ) )         -- the op at the NARROW width
///   machine = renormalize_n( wasm_i32_op(carrier_n(a_n), carrier_n(b_n)) )
/// ```
///
/// The two sides are structurally distinct trees, and the obligation is exactly
/// what a wrong renormalization refutes: masking with `0xff` where an `i8`
/// domain needs `shl 24; shr_s 24` diverges for every negative `a_n`.
///
/// A SHIFT variant is included for the same domains, with the shift amount bound
/// as a `log2(n)`-bit leaf so it is in range by construction. The
/// `shr_u`/`shr_s` narrow pair is deliberately NOT here: its correctness depends
/// on which carrier representation the source operand arrives in, which is a
/// property of the SELECTION rule rather than of the op, and modeling it as a
/// per-op identity would state something weaker than the real obligation.
///
/// At `n = 8` both operands are 8-bit leaves, so the native evaluator verifies
/// these EXHAUSTIVELY (all 2^16 pairs) rather than by sampling.
pub fn narrow_width_proofs() -> Vec<ProofObligation> {
    let mut out = Vec::new();

    for &(n, signed, tag) in NARROW_DOMAINS {
        // --- binary wrapping / bitwise ops ---
        for (op_tag, narrow_op, wasm_op) in narrow_bin_ops() {
            let a_n = SmtExpr::var("narrow_a", n);
            let b_n = SmtExpr::var("narrow_b", n);
            let source = carrier(narrow_op(a_n.clone(), b_n.clone()), n, signed);
            let machine = renormalize(
                wasm_op(carrier(a_n, n, signed), carrier(b_n, n, signed)),
                n,
                signed,
            );
            out.push(narrow_obligation(
                format!(
                    "narrow {tag} {op_tag} -> i32-carried wasm {op_tag} + renormalize (width \
                     invariant)"
                ),
                source,
                machine,
                vec![("narrow_a".to_string(), n), ("narrow_b".to_string(), n)],
            ));
        }

        // --- left shift by an in-range amount ---
        let amount_bits = n.trailing_zeros(); // 3 for n=8, 4 for n=16
        let a_n = SmtExpr::var("narrow_a", n);
        let sh = SmtExpr::var("narrow_sh", amount_bits);
        let sh_n = sh.clone().zero_ext(n - amount_bits);
        let source = carrier(a_n.clone().bvshl(sh_n), n, signed);
        let machine = renormalize(
            w::encode_shl(carrier(a_n, n, signed), sh.zero_ext(32 - amount_bits), 32),
            n,
            signed,
        );
        out.push(narrow_obligation(
            format!("narrow {tag} shl -> i32-carried wasm i32.shl + renormalize (width invariant)"),
            source,
            machine,
            vec![
                ("narrow_a".to_string(), n),
                ("narrow_sh".to_string(), amount_bits),
            ],
        ));

        // --- renormalization ESTABLISHES the invariant for an arbitrary carrier ---
        let x = SmtExpr::var("narrow_x", 32);
        out.push(narrow_obligation(
            format!(
                "narrow {tag} renormalization establishes the {n}-bit width invariant on any i32"
            ),
            SmtExpr::bool_const(true),
            invariant(renormalize(x, n, signed), n, signed),
            vec![("narrow_x".to_string(), 32)],
        ));
    }

    out
}

// ===========================================================================
// Anti-tautology guards — the wrong byte / wrong renormalization must REFUTE
// ===========================================================================

/// Anti-tautology: `i32.load8_s` (0x2c) emitted where `i32.load8_u` (0x2d) was
/// intended. The one-bit opcode slip the load obligations exist to catch.
pub fn proof_wrong_load8_u_is_load8_s() -> ProofObligation {
    let mut ob = mem_load_value_obligation(0x2d, 0x2c)
        .expect("0x2d/0x2c are both i32 sub-word loads by construction");
    ob.name = "WRONG: i32.load8_u lowered as i32.load8_s 0x2c (must be refuted)".to_string();
    ob
}

/// Anti-tautology: `i32.load16_u` (0x2f) emitted where `i32.load8_u` (0x2d) was
/// intended — a wrong ACCESS WIDTH at the same extension.
pub fn proof_wrong_load8_u_is_load16_u() -> ProofObligation {
    let mut ob = mem_load_value_obligation(0x2d, 0x2f)
        .expect("0x2d/0x2f are both i32 unsigned loads by construction");
    ob.name = "WRONG: i32.load8_u lowered as i32.load16_u 0x2f (must be refuted)".to_string();
    ob
}

/// Anti-tautology: `i32.store16` (0x3b) emitted where `i32.store8` (0x3a) was
/// intended. The VALUE obligation cannot see this (the low byte still matches);
/// the WIDTH obligation must.
pub fn proof_wrong_store8_is_store16() -> ProofObligation {
    let mut ob = mem_store_width_obligation(0x3a, 0x3b)
        .expect("0x3a/0x3b are both i32 narrowing stores by construction");
    ob.name = "WRONG: i32.store8 lowered as i32.store16 0x3b (must be refuted)".to_string();
    ob
}

/// Anti-tautology: `i32.store8` (0x3a) emitted where `i32.store16` (0x3b) was
/// intended — a too-NARROW store, which the VALUE obligation catches.
pub fn proof_wrong_store16_is_store8() -> ProofObligation {
    let mut ob = mem_store_value_obligation(0x3b, 0x3a)
        .expect("0x3b/0x3a are both i32 narrowing stores by construction");
    ob.name = "WRONG: i32.store16 lowered as i32.store8 0x3a (must be refuted)".to_string();
    ob
}

/// Anti-tautology: `i32.extend16_s` (0xc1) emitted where `i32.extend8_s` (0xc0)
/// was intended.
pub fn proof_wrong_extend8_s_is_extend16_s() -> ProofObligation {
    let mut ob = sign_extend_value_obligation(0xc0, 0xc1)
        .expect("0xc0/0xc1 are both i32 sign-extension operators by construction");
    ob.name = "WRONG: i32.extend8_s lowered as i32.extend16_s 0xc1 (must be refuted)".to_string();
    ob
}

/// Anti-tautology: an `i8` narrow op renormalized with the UNSIGNED mask
/// (`and 0xff`) instead of the signed `shl 24; shr_s 24`. Diverges for every
/// negative result, so it must be refuted.
pub fn proof_wrong_signed_narrow_uses_unsigned_mask() -> ProofObligation {
    let n = 8;
    let a_n = SmtExpr::var("narrow_a", n);
    let b_n = SmtExpr::var("narrow_b", n);
    let source = carrier(a_n.clone().bvadd(b_n.clone()), n, true);
    let machine = w::encode_narrow_mask_u(
        w::encode_add(carrier(a_n, n, true), carrier(b_n, n, true)),
        n,
    );
    narrow_obligation(
        "WRONG: i8 add renormalized with the UNSIGNED mask (must be refuted)".to_string(),
        source,
        machine,
        vec![("narrow_a".to_string(), n), ("narrow_b".to_string(), n)],
    )
}

/// Anti-tautology: a narrow op that is NOT renormalized at all — the i32
/// wrapping result is handed on as the carrier. Diverges as soon as the wrap
/// escapes the narrow width, so it must be refuted.
pub fn proof_wrong_narrow_skips_renormalization() -> ProofObligation {
    let n = 8;
    let a_n = SmtExpr::var("narrow_a", n);
    let b_n = SmtExpr::var("narrow_b", n);
    let source = carrier(a_n.clone().bvadd(b_n.clone()), n, false);
    let machine = w::encode_add(carrier(a_n, n, false), carrier(b_n, n, false));
    narrow_obligation(
        "WRONG: u8 add with NO renormalization (must be refuted)".to_string(),
        source,
        machine,
        vec![("narrow_a".to_string(), n), ("narrow_b".to_string(), n)],
    )
}

/// Every P3 anti-tautology guard. Each must be REFUTED; a guard that passes
/// means the corresponding obligation family has gone vacuous.
pub fn all_value_domain_anti_tautologies() -> Vec<ProofObligation> {
    vec![
        proof_wrong_load8_u_is_load8_s(),
        proof_wrong_load8_u_is_load16_u(),
        proof_wrong_store8_is_store16(),
        proof_wrong_store16_is_store8(),
        proof_wrong_extend8_s_is_extend16_s(),
        proof_wrong_signed_narrow_uses_unsigned_mask(),
        proof_wrong_narrow_skips_renormalization(),
    ]
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn cfg() -> VerificationConfig {
        VerificationConfig::default()
    }

    /// The P3 surface is exactly the spec's memory block plus the sign-extension
    /// operators, with no duplicates and no byte doing double duty.
    #[test]
    fn p3_surface_matches_the_spec_opcode_table() {
        let bytes = all_wasm_value_domain_bytes();
        assert_eq!(bytes.len(), 28, "14 loads + 9 stores + 5 sign-extensions");
        let unique: std::collections::HashSet<_> = bytes.iter().copied().collect();
        assert_eq!(unique.len(), bytes.len(), "a byte is listed twice");
        // The spec memory block is contiguous 0x28..=0x3e; 0x3f/0x40 are the
        // memory-META instructions and must NOT decode as accesses.
        for b in 0x28u8..=0x3e {
            assert!(
                w::decode_mem_op(b).is_some(),
                "0x{b:02x} must decode as a linear-memory access"
            );
        }
        for b in [0x3fu8, 0x40] {
            assert!(w::decode_mem_op(b).is_none(), "0x{b:02x} is memory-meta");
            assert!(w::decode_memory_meta(b).is_some());
        }
        for b in 0xc0u8..=0xc4 {
            assert!(w::decode_sign_extend(b).is_some());
        }
        // Bytes just outside each block fail closed.
        for b in [0x27u8, 0x41, 0xbf, 0xc5] {
            assert!(w::decode_mem_op(b).is_none() && w::decode_sign_extend(b).is_none());
        }
    }

    /// Every P3 byte carries a non-empty obligation set, and every obligation is
    /// tagged `Reconstructed` (the credit rule's provenance discriminator).
    #[test]
    fn every_p3_byte_has_reconstructed_obligations() {
        for byte in all_wasm_value_domain_bytes() {
            let obs = obligations_for_byte(byte);
            assert!(
                !obs.is_empty(),
                "0x{byte:02x} ({:?}) has NO obligation — uncredited debt",
                value_domain_mnemonic(byte)
            );
            for ob in &obs {
                assert!(
                    ob.is_reconstructed(),
                    "obligation '{}' is not reconstruction-provenanced",
                    ob.name
                );
            }
        }
    }

    /// Sub-word loads/stores carry BOTH of their obligations; full-width loads
    /// carry only the value one (there is no narrow carrier to constrain).
    /// Every load and store also carries its memarg-offset obligation.
    #[test]
    fn obligation_counts_are_width_aware() {
        // Full-width loads: value + offset.
        for byte in [0x28u8, 0x29, 0x2a, 0x2b] {
            assert_eq!(obligations_for_byte(byte).len(), 2, "0x{byte:02x}");
        }
        // Sub-word loads: value + invariant + offset.
        for byte in [0x2cu8, 0x2d, 0x2e, 0x2f, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35] {
            assert_eq!(obligations_for_byte(byte).len(), 3, "0x{byte:02x}");
        }
        // All stores: value + width + offset.
        for byte in WASM_STORE_BYTES {
            assert_eq!(obligations_for_byte(*byte).len(), 3, "0x{byte:02x}");
        }
        // Sign-extension operators: value + shift-pair + invariant.
        for byte in WASM_SIGN_EXTEND_BYTES {
            assert_eq!(obligations_for_byte(*byte).len(), 3, "0x{byte:02x}");
        }
        assert_eq!(all_value_domain_obligations().len(), 57 + 23);
    }

    /// The memarg-offset obligations hold at the honest offset, carry the
    /// no-trap precondition, and REFUTE for a shifted offset in either
    /// direction, for every load and store byte.
    #[test]
    fn a_shifted_memarg_offset_refutes_for_every_access() {
        let cfg = cfg();
        let refutes = |ob: &ProofObligation| {
            matches!(
                verify_by_evaluation_with_config(ob, &cfg),
                VerificationResult::Invalid { .. }
            )
        };
        for &byte in WASM_LOAD_BYTES.iter().chain(WASM_STORE_BYTES) {
            let (honest, skews): (ProofObligation, Vec<ProofObligation>) =
                if w::decode_mem_op(byte).expect("mem op").is_load() {
                    (
                        mem_load_offset_obligation(byte, byte, 0).expect("builds"),
                        [4u32, 1, u32::MAX - 3]
                            .iter()
                            .map(|&k| mem_load_offset_obligation(byte, byte, k).expect("builds"))
                            .collect(),
                    )
                } else {
                    (
                        mem_store_offset_obligation(byte, byte, 0).expect("builds"),
                        [4u32, 1, u32::MAX - 3]
                            .iter()
                            .map(|&k| mem_store_offset_obligation(byte, byte, k).expect("builds"))
                            .collect(),
                    )
                };
            assert_eq!(honest.preconditions.len(), 1, "0x{byte:02x} states no-trap");
            assert!(
                matches!(
                    verify_by_evaluation_with_config(&honest, &cfg),
                    VerificationResult::Valid
                ),
                "0x{byte:02x}: the honest offset must hold"
            );
            for ob in &skews {
                assert!(refutes(ob), "{} must REFUTE", ob.name);
            }
        }
    }

    /// The effective address does not wrap: `ea + N <= 2^32` is the no-trap
    /// condition, so an access at `(0xffff_fffc, 4)` of 4 bytes traps while
    /// `(0xffff_fff8, 4)` does not, and a wrapping 32-bit sum would name
    /// address 0 for the first.
    #[test]
    fn the_effective_address_is_unbounded_and_traps_past_the_address_space() {
        use crate::smt::SmtExpr as E;
        let at = |base: u64, off: u64, n: u32| {
            w::encode_access_does_not_trap(E::bv_const(base, 32), E::bv_const(off, 32), n)
        };
        let eval = |e: SmtExpr| match e.try_eval(&crate::smt::EvalEnv::default()) {
            Ok(crate::smt::EvalResult::Bool(b)) => b,
            other => panic!("closed Bool expression, got {other:?}"),
        };
        assert!(eval(at(0xffff_fff8, 4, 4)));
        assert!(!eval(at(0xffff_fffc, 4, 4)));
        assert!(!eval(at(0xffff_ffff, 0xffff_ffff, 1)));
        assert!(eval(at(0, 0xffff_fffc, 4)));
    }

    /// Every P3 byte's FULL obligation set discharges `Valid` under the native
    /// evaluator — the coverage-gate credit basis.
    #[test]
    fn every_p3_byte_discharges_valid() {
        let cfg = cfg();
        for byte in all_wasm_value_domain_bytes() {
            assert!(
                value_domain_discharges_valid(byte, &cfg),
                "0x{byte:02x} ({:?}) did not discharge Valid",
                value_domain_mnemonic(byte)
            );
        }
    }

    /// A byte OUTSIDE the P3 surface earns no credit (fail closed).
    #[test]
    fn non_p3_bytes_earn_no_credit() {
        let cfg = cfg();
        for byte in [0x00u8, 0x0e, 0x3f, 0x40, 0x6a, 0xc5, 0xff] {
            assert!(obligations_for_byte(byte).is_empty(), "0x{byte:02x}");
            assert!(!value_domain_discharges_valid(byte, &cfg), "0x{byte:02x}");
        }
    }

    /// THE TEETH: every anti-tautology guard is REFUTED by the evaluator. If any
    /// passes, the matching obligation family proves nothing.
    #[test]
    fn anti_tautologies_are_refuted() {
        let cfg = cfg();
        for ob in all_value_domain_anti_tautologies() {
            let result = verify_by_evaluation_with_config(&ob, &cfg);
            assert!(
                !matches!(result, VerificationResult::Valid),
                "'{}' was NOT refuted (result {result:?}) — the obligation is vacuous",
                ob.name
            );
        }
    }

    /// Cross-CARRIER-width and load/store slips fail CLOSED — no obligation is
    /// built, so no credit is earned.
    ///
    /// These are TYPE errors, not value errors: `i64.store8` and `i32.store8`
    /// write the same low byte, so no value obligation could ever separate them;
    /// module validation does, by rejecting the wrong stack type. Returning
    /// `None` says that out loud instead of manufacturing a comparison that
    /// would pass and read as coverage.
    #[test]
    fn cross_width_slips_fail_closed() {
        assert!(mem_load_value_obligation(0x2d, 0x31).is_none()); // i32.load8_u vs i64.load8_u
        assert!(mem_store_value_obligation(0x3a, 0x3c).is_none()); // i32.store8 vs i64.store8
        assert!(sign_extend_value_obligation(0xc0, 0xc2).is_none()); // i32 vs i64 extend8_s
        // A load byte where a store was intended, and vice versa.
        assert!(mem_load_value_obligation(0x2d, 0x3a).is_none());
        assert!(mem_store_value_obligation(0x3a, 0x2d).is_none());
    }

    /// The narrow-width family: every obligation discharges `Valid`, and none is
    /// a degenerate `X == X`.
    #[test]
    fn narrow_width_proofs_discharge_valid() {
        let cfg = cfg();
        let proofs = narrow_width_proofs();
        assert_eq!(
            proofs.len(),
            32,
            "4 domains x (6 binary + 1 shl + 1 renormalization-establishes-invariant) = 32"
        );
        for ob in &proofs {
            assert!(
                ob.is_genuinely_proven(),
                "narrow proof '{}' is degenerate (X==X)",
                ob.name
            );
            assert!(
                matches!(
                    verify_by_evaluation_with_config(ob, &cfg),
                    VerificationResult::Valid
                ),
                "narrow proof '{}' did not discharge Valid",
                ob.name
            );
        }
    }

    /// The four named deferrals are present, distinct, and each states a family
    /// and a substantive reason. A deferral with an empty reason is debt hidden
    /// behind a label.
    #[test]
    fn deferrals_are_named_and_substantive() {
        assert_eq!(WASM_VALUE_DOMAIN_DEFERRALS.len(), 4);
        let names: std::collections::HashSet<_> =
            WASM_VALUE_DOMAIN_DEFERRALS.iter().map(|d| d.name).collect();
        assert_eq!(names.len(), 4, "deferral names must be distinct");
        for d in WASM_VALUE_DOMAIN_DEFERRALS {
            assert!(!d.family.is_empty(), "{} has no family", d.name);
            assert!(
                d.reason.len() > 80,
                "{} has a token reason, not an auditable one",
                d.name
            );
        }
        // The three opcode-bearing deferrals are exactly br_table / memory.size /
        // memory.grow, and none of them is also in the credited surface.
        let deferred_bytes: Vec<u8> = WASM_VALUE_DOMAIN_DEFERRALS
            .iter()
            .filter_map(|d| d.opcode_byte)
            .collect();
        assert_eq!(deferred_bytes, vec![0x0e, 0x3f, 0x40]);
        for b in &deferred_bytes {
            assert!(
                !all_wasm_value_domain_bytes().contains(b),
                "0x{b:02x} is both credited and deferred"
            );
            assert!(value_domain_deferral(*b).is_some());
        }
    }

    // -----------------------------------------------------------------------
    // FORMAL discharge (ay) — the same guarded shape the rest of the wasm suite
    // uses. `z3_available()` is FALSE unless a CAPABLE independent Alethe
    // checker is installed, so these skip loudly rather than pretending.
    // -----------------------------------------------------------------------

    fn proof_authority_available() -> bool {
        crate::ay_bridge::z3_available()
    }

    /// FORMAL: every P3 per-opcode obligation is proven `unsat` by ay — correct
    /// for ALL addresses and values, not sampled.
    #[test]
    fn p3_obligations_proven_formally() {
        if !proof_authority_available() {
            crate::formal_gap::skip_test(
                "p3_obligations_proven_formally",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }
        for ob in all_value_domain_obligations() {
            crate::wasm_formal::prove_or_certification_gap_skip(&ob);
        }
    }

    /// FORMAL: every narrow-width obligation is proven `unsat` by ay.
    #[test]
    fn narrow_width_proofs_proven_formally() {
        if !proof_authority_available() {
            crate::formal_gap::skip_test(
                "narrow_width_proofs_proven_formally",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }
        for ob in narrow_width_proofs() {
            crate::wasm_formal::prove_or_certification_gap_skip(&ob);
        }
    }

    /// FORMAL anti-tautology guards: every deliberately-wrong P3 byte and every
    /// wrong renormalization is REFUTED (`sat`) by ay. Unguarded on purpose —
    /// a refutation needs a solver verdict, not the certification chain — so
    /// this exercises the solver even where UNSAT cannot be promoted.
    #[test]
    fn p3_anti_tautologies_refuted_formally() {
        for ob in all_value_domain_anti_tautologies() {
            crate::wasm_formal::refute(&ob);
        }
    }

    /// Aggregate FORMAL report over the whole P3 slice, printing the REAL
    /// proven / certification-gapped split rather than a bare headline count.
    /// Every obligation must be PROVEN or the exact confirmed certification gap;
    /// a refutation, a timeout, or an unrecognized diagnostic still fails.
    #[test]
    fn p3_formal_discharge_summary() {
        if !proof_authority_available() {
            eprintln!(
                "p3_formal_discharge_summary: SKIPPED — no capable independent proof authority \
                 (ay UNSAT cannot be promoted without a Clean/Carcara checker built with \
                 `carcara-verify`); 0 proven, 0 gapped, {} obligations not discharged formally",
                all_value_domain_obligations().len() + narrow_width_proofs().len()
            );
            return;
        }
        let mut all = all_value_domain_obligations();
        all.extend(narrow_width_proofs());
        let total = all.len();
        let mut proven = 0usize;
        let mut gapped = 0usize;
        for ob in all {
            let verdict = crate::wasm_formal::discharge(&ob);
            if verdict == crate::wasm_formal::Formal::Proven {
                proven += 1;
            } else if let Some(reason) = crate::wasm_formal::certification_gap_reason(&verdict) {
                crate::formal_gap::print_gap_skip(
                    &format!("p3_formal_discharge_summary `{}`", ob.name),
                    &reason,
                );
                gapped += 1;
            } else {
                panic!(
                    "obligation `{}` neither proven nor certification-gapped: {verdict:?}",
                    ob.name
                );
            }
        }
        eprintln!(
            "p3_formal_discharge_summary: {proven}/{total} P3 obligations proven (unsat) via ay \
             ({gapped} certification-gap skipped)"
        );
        assert_eq!(
            proven + gapped,
            total,
            "every P3 obligation must be formally proven or the exact confirmed certification gap"
        );
    }

    /// f32/f64 accesses are bit-identical to the same-width integer accesses, so
    /// the int/FP pair is NOT value-refutable. Asserted so the limitation is a
    /// pinned, visible fact rather than a silent hole.
    #[test]
    fn fp_and_int_accesses_are_deliberately_indistinguishable() {
        // f32.load (0x2a) reconstructed from i32.load (0x28) still discharges
        // Valid: at the value level they ARE the same function.
        let ob = mem_load_value_obligation(0x2a, 0x28).expect("both are 32-bit full-width loads");
        assert!(matches!(
            verify_by_evaluation_with_config(&ob, &cfg()),
            VerificationResult::Valid
        ));
        // The decode still distinguishes them, so the audit row can say which is
        // which even though the value obligation cannot.
        assert!(w::decode_mem_op(0x2a).expect("f32.load").is_fp);
        assert!(!w::decode_mem_op(0x28).expect("i32.load").is_fp);
    }
}
