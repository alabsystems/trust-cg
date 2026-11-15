// trust-cg-verify/tests/x86_addressing_gate.rs - the x86-64 memory-MOV ADDRESS obligation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The gate for [`trust_cg_verify::x86_addressing_proofs`].
//!
//! The obligation it defends: for every integer memory MOV the backend emits,
//! the address ENCODED IN THE BYTES denotes the address the addressing operand
//! asked for. The machine side is decoded from the real emitted bytes by an
//! SDM-derived decoder that shares no code with the encoder, and is built as
//! `base + (index << shift) + sext(disp_field)` — structurally distinct from
//! the intent's `base + index*scale + disp`, so a passing comparison is an
//! agreement between two readings rather than a tree compared with itself.
//!
//! This is the obligation `x86_reconstruct_effective_address` was CLAIMED to
//! carry and does not: that helper builds BOTH halves from the same operand
//! with identical encoders, so no address error of any kind can refute — see
//! the audit `report_which_credited_opcodes_have_no_address_teeth`.
//!
//! STATUS, stated exactly: this lane CARRIES the address facet of every row
//! `coverage_gate::x86_opcode_has_address_credit` names. The coverage gate
//! consults it BEFORE the reconstruction (e2275815a for the memory access
//! forms, f74b4561c for Lea/LeaSib, 88de9e199 for the sixteen volatile forms).
//! That the lane discharges and that losing it costs exactly those rows is
//! `x86_address_credit_is_live_counted_and_has_teeth` in `coverage_gate_tests`;
//! that every credited memory opcode without address teeth in the shared
//! reconstruction is routed here and has captured encodings is the in-crate
//! teeth audit. What this lane does not establish is that instruction
//! SELECTION chose the right address: it runs post-isel with no trust_ir input.

#[path = "support/x86_addressing_live_encode.rs"]
mod live;

use trust_cg_verify::x86_addressing_proofs as addr;

/// Floor on corpus size. An encoder that stops emitting a form shrinks the
/// corpus; this makes that shrink a FAILURE rather than a quieter green.
const MIN_CORPUS: usize = 60;

#[test]
fn the_address_obligation_holds_on_every_live_encoding() {
    let corpus = live::live_mem_mov_corpus();
    assert!(
        corpus.len() >= MIN_CORPUS,
        "the live memory-MOV corpus shrank to {} (floor {MIN_CORPUS}) — the encoder stopped \
         emitting forms this lane credits",
        corpus.len()
    );
    // A total-count floor cannot see the loss of a whole OPCODE: with slack in
    // the total, an encoder that stopped emitting (say) the byte SIB forms
    // would drop twelve cases and still clear the floor, taking that family
    // out of the lane silently. Require every opcode to contribute.
    for &(opcode, _, _, is_sib, _) in live::MEM_MOV_OPCODES {
        let want = if is_sib {
            live::SIB_SHAPES.len()
        } else {
            live::PLAIN_SHAPES.len()
        };
        let got = corpus
            .iter()
            .filter(|c| c.label.starts_with(&format!("{opcode:?} ")))
            .count();
        assert_eq!(
            got, want,
            "{opcode:?} contributed {got} of {want} shapes — the encoder refused some form this \
             lane is supposed to cover, and a total-count floor would have hidden it"
        );
    }
    // The compare-exchange forms take their own shape tables; every shape must
    // contribute there too.
    let compare_exchange = live::COMPARE_EXCHANGE_OPCODES
        .iter()
        .map(|&(opcode, _)| (opcode, live::COMPARE_EXCHANGE_SHAPES.len()))
        .chain(std::iter::once((
            trust_cg_ir::X86Opcode::AtomicLoadCmpxchg16b,
            live::ATOMIC_LOAD_CMPXCHG16B_BASES.len(),
        )));
    for (opcode, want) in compare_exchange {
        let got = corpus
            .iter()
            .filter(|c| c.label.starts_with(&format!("{opcode:?} ")))
            .count();
        assert_eq!(
            got, want,
            "{opcode:?} contributed {got} of {want} shapes — the encoder refused a \
             compare-exchange form this lane is supposed to cover"
        );
    }
    for case in &corpus {
        match addr::address_encoding_holds(&case.bytes, &case.intent) {
            Ok(outcome) => assert_eq!(
                outcome.rows,
                addr::WITNESS_ROWS,
                "{}: not every witness row was compared",
                case.label
            ),
            Err(e) => panic!(
                "{}: the address obligation must hold on bytes the encoder really emits \
                 ({:02x?}): {e}",
                case.label, case.bytes
            ),
        }
    }
}

/// The witness environment must actually exercise high addresses, or agreement
/// could be an artifact of a narrow, all-small register set.
#[test]
fn the_witness_rows_exercise_both_high_and_low_addresses() {
    let corpus = live::live_mem_mov_corpus();
    let mut saw_high = 0usize;
    for case in &corpus {
        let outcome = addr::address_encoding_holds(&case.bytes, &case.intent)
            .unwrap_or_else(|e| panic!("{}: {e}", case.label));
        if outcome.high_rows > 0 && outcome.high_rows < outcome.rows {
            saw_high += 1;
        }
    }
    assert_eq!(
        saw_high,
        corpus.len(),
        "every case must see BOTH high and low addresses; {saw_high} of {} did",
        corpus.len()
    );
    // And the witness generator itself must not collide two distinct register
    // roots in any row — a collision would let a wrong-register control
    // evaluate equal and silently fail to refute, which is the one way this
    // lane could look strict while proving less than it claims.
    for row in 0..addr::WITNESS_ROWS {
        let mut seen = std::collections::BTreeMap::new();
        for root in 0u8..16 {
            let v = addr::witness_reg_value(row, root);
            if let Some(other) = seen.insert(v, root) {
                panic!(
                    "row {row}: roots {other} and {root} share the witness value {v:#018x}, so a \
                     wrong-register control between them cannot refute"
                );
            }
        }
    }
}

/// EVERY address error refutes — the whole point of the lane.
///
/// Each control perturbs the INTENT away from what the bytes encode, one facet
/// at a time, and must be refuted FOR ITS OWN REASON. A control refuted for a
/// different reason withholds the credit exactly as a surviving one does: it
/// would mean the lane is not testing the facet it claims.
#[test]
fn every_address_error_refutes_for_its_own_reason() {
    let corpus = live::live_mem_mov_corpus();
    let mut checked = 0usize;
    let mut neutral_swaps = 0usize;
    let mut survivors: Vec<String> = Vec::new();
    let mut misattributed: Vec<String> = Vec::new();

    for case in &corpus {
        let i = &case.intent;
        // (label, perturbed intent, the refutation class it must produce)
        let mut controls: Vec<(&str, addr::MemAccessIntent, &str)> = vec![
            (
                "C1 wrong base register",
                addr::MemAccessIntent {
                    base_root: i.base_root ^ 1,
                    ..i.clone()
                },
                "address",
            ),
            (
                "C2 displacement off by 16",
                addr::MemAccessIntent {
                    disp: i.disp.wrapping_add(16),
                    ..i.clone()
                },
                "address",
            ),
            (
                "C3 wrong register operand",
                addr::MemAccessIntent {
                    reg_root: i.reg_root ^ 1,
                    ..i.clone()
                },
                "register",
            ),
            (
                "C4 wrong access width",
                addr::MemAccessIntent {
                    access_bits: if i.access_bits == 64 { 32 } else { 64 },
                    ..i.clone()
                },
                "width",
            ),
            (
                "C5 wrong direction",
                addr::MemAccessIntent {
                    is_store: !i.is_store,
                    ..i.clone()
                },
                "direction",
            ),
        ];
        // C9: a GPR load names its destination rule. A zero-extending intent
        // against merging bytes, or the reverse, is an EXTENSION error.
        if !i.is_store && i.reg_file == addr::RegFile::Gpr {
            controls.push((
                "C9 zero extension flipped",
                addr::MemAccessIntent {
                    zero_extending_load: !i.zero_extending_load,
                    ..i.clone()
                },
                "extension",
            ));
        }
        if let Some(index) = i.index_root {
            // C6 is conditional, and the condition is a FACT about x86
            // addressing rather than a convenience: at scale 1 the address is
            // `base + index*1 + disp`, so swapping base and index denotes the
            // SAME address. The swap changes the SIB byte, but this lane proves
            // the ADDRESS, and the address is genuinely unchanged. Asserting a
            // refutation there would be asserting that a correct address is
            // wrong. The neutrality is PINNED below rather than skipped, so it
            // cannot quietly become a hole if the denotation changes.
            if i.scale != 1 {
                controls.push((
                    "C6 base/index SWAPPED",
                    addr::MemAccessIntent {
                        base_root: index,
                        index_root: Some(i.base_root),
                        ..i.clone()
                    },
                    "address",
                ));
            } else {
                let swapped = addr::MemAccessIntent {
                    base_root: index,
                    index_root: Some(i.base_root),
                    ..i.clone()
                };
                assert!(
                    addr::address_encoding_holds(&case.bytes, &swapped).is_ok(),
                    "{}: at scale 1 a base/index swap denotes the SAME address, so it must \
                     NOT be refuted — if this now refutes, the address denotation changed",
                    case.label
                );
                neutral_swaps += 1;
            }
            controls.push((
                "C7 wrong index register",
                addr::MemAccessIntent {
                    index_root: Some(index ^ 1),
                    ..i.clone()
                },
                "address",
            ));
            controls.push((
                "C8 wrong scale factor",
                addr::MemAccessIntent {
                    scale: if i.scale == 8 { 4 } else { 8 },
                    ..i.clone()
                },
                "address",
            ));
        }

        for (label, perturbed, expected_class) in controls {
            // A control that does not actually change anything is not a
            // control; skip rather than score it.
            if perturbed == *i {
                continue;
            }
            checked += 1;
            match addr::address_encoding_holds(&case.bytes, &perturbed) {
                Ok(_) => survivors.push(format!("{} :: {label}", case.label)),
                Err(e) => {
                    let actual = match e {
                        addr::AddressRefutation::Address { .. } => "address",
                        addr::AddressRefutation::RegisterOperand { .. } => "register",
                        addr::AddressRefutation::AccessWidth { .. } => "width",
                        addr::AddressRefutation::Direction { .. } => "direction",
                        addr::AddressRefutation::Extension { .. } => "extension",
                        addr::AddressRefutation::Degenerate => "DEGENERATE",
                        other => {
                            misattributed
                                .push(format!("{} :: {label} => unexpected {other}", case.label));
                            continue;
                        }
                    };
                    if actual != expected_class {
                        misattributed.push(format!(
                            "{} :: {label} => refuted as {actual}, expected {expected_class}",
                            case.label
                        ));
                    }
                }
            }
        }
    }

    assert!(
        survivors.is_empty(),
        "{} address error(s) SURVIVED: {survivors:#?}",
        survivors.len()
    );
    assert!(
        misattributed.is_empty(),
        "{} control(s) refuted for the WRONG reason: {misattributed:#?}",
        misattributed.len()
    );
    assert!(
        checked >= 300,
        "only {checked} controls ran; the battery is not covering the corpus"
    );
    assert!(
        neutral_swaps > 0,
        "no scale-1 shape was exercised, so the semantically neutral swap is unpinned"
    );
    println!(
        "x86 addressing gate: {checked} address controls all refuted as stated; \
         {neutral_swaps} scale-1 base/index swaps pinned as semantically neutral"
    );
}

/// The anti-vacuity guard itself must work: a machine side stated EXACTLY as
/// the source side is refused rather than scored.
#[test]
fn a_machine_side_equal_to_the_source_side_is_refused() {
    use trust_cg_verify::smt::SmtExpr;
    let intent = addr::MemAccessIntent {
        reg_root: 0,
        reg_file: addr::RegFile::Gpr,
        base_root: 3,
        index_root: Some(1),
        scale: 8,
        disp: 16,
        access_bits: 64,
        is_store: false,
        zero_extending_load: false,
    };
    let source = addr::intent_address_denotation(&intent);
    // The degenerate pairing the old reconstruction produced.
    assert!(
        matches!(
            addr::compare_addresses_for_test(&source, &source),
            Err(addr::AddressRefutation::Degenerate)
        ),
        "a source-equals-machine pairing must be refused as Degenerate"
    );
    // And a genuinely distinct pairing is not refused for that reason.
    let distinct = source.clone().bvadd(SmtExpr::bv_const(0, addr::ADDR_BITS));
    assert!(
        !matches!(
            addr::compare_addresses_for_test(&source, &distinct),
            Err(addr::AddressRefutation::Degenerate)
        ),
        "a structurally distinct pairing must not be called Degenerate"
    );
}

/// Locate the structural byte positions of an encoding: the REX byte (if any),
/// the opcode, the ModR/M byte, the SIB byte (if any) and the displacement.
///
/// Written here, in the TEST, from the same SDM layout the decoder implements,
/// so a control can reach into a real encoding and corrupt one specific field.
struct ByteLayout {
    rex: Option<usize>,
    opcode: usize,
    modrm: usize,
    sib: Option<usize>,
    disp: Option<usize>,
}

fn layout_of(bytes: &[u8]) -> ByteLayout {
    let mut i = 0;
    // Mandatory (F2/F3), operand-size (66) and — on the compare-exchange forms —
    // LOCK (F0) prefixes precede REX, and the opcode may be a two-byte 0x0F
    // escape. Getting this wrong makes a control corrupt the REX byte while
    // believing it corrupted ModR/M.
    while matches!(bytes[i], 0x66 | 0xF2 | 0xF3 | 0xF0) {
        i += 1;
    }
    let rex = if bytes[i] & 0xF0 == 0x40 {
        let r = i;
        i += 1;
        Some(r)
    } else {
        None
    };
    let opcode = i;
    i += if bytes[i] == 0x0F { 2 } else { 1 };
    let modrm = i;
    i += 1;
    let mod_field = bytes[modrm] >> 6;
    let rm = bytes[modrm] & 0b111;
    let sib = if rm == 0b100 {
        let s = i;
        i += 1;
        Some(s)
    } else {
        None
    };
    // A displacement is present under either of two independent ModRM rules:
    // mod=01/10 carries disp8/disp32 directly, and mod=00 with a SIB whose
    // base field is 101 is the no-base form, which carries a disp32. Both
    // place it at the same offset.
    let has_disp = mod_field == 0b01
        || mod_field == 0b10
        || (mod_field == 0b00 && sib.is_some() && (bytes[sib.unwrap()] & 0b111) == 0b101);
    let disp = has_disp.then_some(i);
    ByteLayout {
        rex,
        opcode,
        modrm,
        sib,
        disp,
    }
}

/// EVERY corruption of the emitted BYTES refutes, unless it is provably
/// semantically neutral — and each neutral case is pinned by name.
///
/// The intent-side battery above tests whether the COMPARISON is sensitive.
/// This one tests the DECODER, which is the only thing standing between this
/// lane and the `X == X` shape it replaces. Without it the lane's independence
/// would be asserted rather than measured: a bug mirrored in both the decoder
/// and the encoder (the decoder masking the SIB scale field to one bit while
/// the encoder emits one bit) agrees on every corpus row and moves no
/// intent-side control at all.
#[test]
fn every_corruption_of_the_emitted_bytes_refutes_or_is_a_named_neutral() {
    let corpus = live::live_mem_mov_corpus();
    let mut checked = 0usize;
    let mut survivors: Vec<String> = Vec::new();
    let mut neutral: Vec<String> = Vec::new();

    for case in &corpus {
        let l = layout_of(&case.bytes);
        let mut mutants: Vec<(String, Vec<u8>)> = Vec::new();
        let push = |label: &str, at: usize, xor: u8, out: &mut Vec<(String, Vec<u8>)>| {
            let mut b = case.bytes.clone();
            b[at] ^= xor;
            out.push((label.to_string(), b));
        };

        if let Some(rex) = l.rex {
            push(
                "B1 REX.B toggled (base register)",
                rex,
                0b0001,
                &mut mutants,
            );
            push(
                "B2 REX.X toggled (index register)",
                rex,
                0b0010,
                &mut mutants,
            );
            push(
                "B3 REX.R toggled (register operand)",
                rex,
                0b0100,
                &mut mutants,
            );
            if case.bytes[rex] & 0b1000 != 0 {
                push("B4 REX.W cleared (access width)", rex, 0b1000, &mut mutants);
            }
        }
        push(
            "B5 opcode direction bit",
            l.opcode,
            0b0000_0010,
            &mut mutants,
        );
        push(
            "B6 ModR/M.reg rewritten",
            l.modrm,
            0b0000_1000,
            &mut mutants,
        );
        if let Some(sib) = l.sib {
            push("B7 SIB scale field rotated", sib, 0b0100_0000, &mut mutants);
            push(
                "B8 SIB index field rewritten",
                sib,
                0b0000_1000,
                &mut mutants,
            );
            push(
                "B9 SIB base field rewritten",
                sib,
                0b0000_0001,
                &mut mutants,
            );
        }
        if let Some(disp) = l.disp {
            push("B10 displacement byte flipped", disp, 0x40, &mut mutants);
        }
        // Length corruptions.
        let mut truncated = case.bytes.clone();
        truncated.pop();
        mutants.push(("B11 last byte dropped".to_string(), truncated));
        let mut appended = case.bytes.clone();
        appended.push(0x90);
        mutants.push(("B12 byte appended".to_string(), appended));

        for (label, bytes) in mutants {
            if bytes == case.bytes {
                continue;
            }
            checked += 1;
            match addr::address_encoding_holds(&bytes, &case.intent) {
                Err(_) => {}
                Ok(_) => {
                    // A corruption that survives is either a real hole or a
                    // provably neutral one. Decide which, HERE, rather than
                    // letting it pass unremarked.
                    let decoded = addr::sdm_decode_memory_mov(&bytes);
                    let original = addr::sdm_decode_memory_mov(&case.bytes);
                    let same_address = match (&decoded, &original) {
                        (Ok(d), Ok(o)) => {
                            addr::decoded_address_denotation(&d.address)
                                == addr::decoded_address_denotation(&o.address)
                                && d.access_bits == o.access_bits
                                && d.reg_root == o.reg_root
                                && d.mnemonic.is_store() == o.mnemonic.is_store()
                        }
                        _ => false,
                    };
                    if same_address {
                        // A surviving corruption is only acceptable if it is
                        // ARCHITECTURALLY inert, and that is checked here from
                        // the encoding's structure — not taken on trust from
                        // the label. Exactly two corruptions can be inert:
                        //
                        //   * REX.X on a form with NO SIB byte. REX.X extends
                        //     only the SIB index field, so with no SIB byte it
                        //     extends nothing (SDM Vol 2A Table 2-4).
                        //   * the SIB scale field when there is NO INDEX. With
                        //     index = 100b and REX.X clear there is no index
                        //     term, and the scale field is ignored (Table 2-3).
                        //
                        // Anything else that survives is a HOLE, whatever it
                        // is called.
                        let l2 = layout_of(&case.bytes);
                        let inert_rex_x = label.starts_with("B2") && l2.sib.is_none();
                        let inert_scale = label.starts_with("B7")
                            && matches!(
                                addr::sdm_decode_memory_mov(&case.bytes).map(|d| d.address),
                                Ok(addr::DecodedAddress::Sib {
                                    index_root: None,
                                    ..
                                })
                            );
                        assert!(
                            inert_rex_x || inert_scale,
                            "{} :: {label} survived and is NOT one of the two architecturally \
                             inert corruptions (REX.X with no SIB byte; scale field with no \
                             index). Bytes {:02x?}",
                            case.label,
                            bytes
                        );
                        neutral.push(format!("{} :: {label}", case.label));
                    } else {
                        survivors.push(format!(
                            "{} :: {label} :: bytes {:02x?} decoded {:?}",
                            case.label, bytes, decoded
                        ));
                    }
                }
            }
        }
    }

    assert!(
        survivors.is_empty(),
        "{} byte corruption(s) changed the instruction and were NOT refuted: {survivors:#?}",
        survivors.len()
    );
    assert!(
        checked >= 500,
        "only {checked} byte controls ran; the battery is not covering the corpus"
    );
    // Name the neutral set rather than only counting it: a bare count is where
    // a real hole would hide.
    let mut kinds: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    for n in &neutral {
        let kind = n.split(":: ").nth(1).unwrap_or(n).to_string();
        *kinds.entry(kind).or_default() += 1;
    }
    println!(
        "x86 addressing gate: {checked} BYTE corruptions, {} refuted, {} pinned as \
         denotationally neutral",
        checked - neutral.len(),
        neutral.len()
    );
    for (kind, n) in &kinds {
        println!("    neutral: {n:3} x {kind}");
    }
    for n in neutral.iter().take(4) {
        println!("    example: {n}");
    }
}

/// The corpus must actually reach every addressing MODE the decoder models.
///
/// A total-count floor cannot see the loss of a whole family or a whole mode,
/// which is exactly the failure it is written to catch. This asserts coverage
/// per mode instead.
#[test]
fn the_corpus_reaches_every_addressing_mode_the_decoder_models() {
    let corpus = live::live_mem_mov_corpus();
    let (mut mod00, mut disp8, mut disp32, mut sib_rows, mut rex_x_index, mut no_index) =
        (0, 0, 0, 0, 0, 0);
    let mut widths = std::collections::BTreeSet::new();
    let mut stores = 0usize;

    for case in &corpus {
        let d = addr::sdm_decode_memory_mov(&case.bytes)
            .unwrap_or_else(|e| panic!("{}: {e}", case.label));
        widths.insert(d.access_bits);
        if d.mnemonic.is_store() {
            stores += 1;
        }
        let disp = match &d.address {
            addr::DecodedAddress::BaseDisp { disp, .. } => Some(disp.encoded_bits),
            addr::DecodedAddress::Sib {
                disp,
                index_root,
                base_root,
                ..
            } => {
                sib_rows += 1;
                if index_root.is_none() {
                    no_index += 1;
                }
                if index_root.map(|i| i >= 8).unwrap_or(false) {
                    rex_x_index += 1;
                }
                let _ = base_root;
                Some(disp.encoded_bits)
            }
            _ => None,
        };
        match disp {
            Some(0) => mod00 += 1,
            Some(8) => disp8 += 1,
            Some(32) => disp32 += 1,
            _ => {}
        }
    }

    assert!(mod00 > 0, "no case decodes mod=00 (no displacement field)");
    assert!(disp8 > 0, "no case decodes a disp8");
    assert!(disp32 > 0, "no case decodes a disp32");
    assert!(sib_rows > 0, "no case decodes a SIB form");
    assert!(no_index > 0, "no case decodes the no-index sentinel");
    assert!(
        rex_x_index > 0,
        "no case decodes a REX.X-extended index register"
    );
    assert!(stores > 0, "no case is a STORE");
    assert_eq!(
        widths,
        [8u32, 16, 32, 64, 128].into_iter().collect(),
        "the corpus must reach every access width the family encodes"
    );
    println!(
        "x86 addressing gate modes: mod00={mod00} disp8={disp8} disp32={disp32} sib={sib_rows} \
         no_index={no_index} rex_x_index={rex_x_index} stores={stores} widths={widths:?}"
    );
}

/// The CREDIT HOOK discharges, and reports a lane that actually covers the
/// family.
#[test]
fn the_credit_hook_discharges_over_the_captured_corpus() {
    let credit = addr::mem_mov_address_credit()
        .unwrap_or_else(|e| panic!("the memory-MOV address credit must discharge: {e}"));
    assert_eq!(
        credit.entries,
        addr::EMITTED_X86_MEM_MOV.len(),
        "every captured entry must be checked"
    );
    assert_eq!(
        credit.modes, 3,
        "mod=00, disp8 and disp32 must all be reached"
    );
    assert_eq!(credit.widths, 5, "8/16/32/64/128 must all be reached");
    // Floors, not targets: they exist so a lane that quietly shrinks fails
    // instead of passing with less evidence.
    assert!(
        credit.intent_controls_refuted >= 1400,
        "intent controls fell to {}",
        credit.intent_controls_refuted
    );
    assert!(
        credit.byte_controls_refuted >= 1800,
        "byte controls fell to {}",
        credit.byte_controls_refuted
    );
    println!(
        "ADDR-x86 credit: {} entries, {} modes, {} widths, {} intent controls, {} byte controls",
        credit.entries,
        credit.modes,
        credit.widths,
        credit.intent_controls_refuted,
        credit.byte_controls_refuted
    );
}

/// The captured corpus is what the LIVE encoder emits today.
///
/// A capture can rot. If the encoder changes, the credit hook would keep
/// decoding FROZEN bytes and stay green while the backend emitted something
/// else entirely — the exact failure the MovRI and SSE lanes each hit.
#[test]
fn the_captured_corpus_is_what_the_live_encoder_emits() {
    let live_corpus = live::live_mem_mov_corpus();
    assert_eq!(
        live_corpus.len(),
        addr::EMITTED_X86_MEM_MOV.len(),
        "the live corpus and the capture have diverged in SIZE"
    );
    for (live_case, captured) in live_corpus.iter().zip(addr::EMITTED_X86_MEM_MOV) {
        assert_eq!(
            live_case.label, captured.label,
            "capture order diverged from the live corpus"
        );
        assert_eq!(
            live_case.bytes.as_slice(),
            captured.bytes,
            "{}: the live encoder now emits {:02x?}, but the capture says {:02x?}",
            captured.label,
            live_case.bytes,
            captured.bytes
        );
        assert_eq!(
            live_case.intent,
            captured.intent(),
            "{}: the intent diverged from the capture",
            captured.label
        );
    }
}

/// THE CREDIT HAS TEETH: a lane that stops refuting must WITHHOLD the credit.
///
/// A control battery that lives outside the hook cannot withhold anything when
/// it stops working. This proves the hook itself refuses, by handing it a
/// corpus entry whose bytes encode a DIFFERENT address than its intent — the
/// shape a real encoder bug would produce.
#[test]
fn the_credit_is_withheld_when_an_encoding_does_not_match_its_intent() {
    let good = addr::EMITTED_X86_MEM_MOV
        .iter()
        .find(|e| e.index_root.is_some())
        .expect("a SIB entry");
    // Same bytes, an intent naming a different base: the credit must refuse.
    let wrong = addr::MemAccessIntent {
        base_root: good.base_root ^ 1,
        ..good.intent()
    };
    assert!(
        addr::address_encoding_holds(good.bytes, &wrong).is_err(),
        "an intent that does not match the bytes must be refused"
    );
    // And a corrupted encoding must be refused against its own intent.
    let mut corrupted = good.bytes.to_vec();
    let modrm = corrupted.len() - 3;
    corrupted[modrm] ^= 0b0000_1000;
    assert!(
        addr::address_encoding_holds(&corrupted, &good.intent()).is_err(),
        "a corrupted encoding must be refused against its own intent"
    );
}

/// THE DEFECT THIS LANE REPLACES, pinned from a gate target.
///
/// The same partition the in-crate audit computes, re-exercised here so the
/// meta-gate has a target it actually runs. NO memory opcode the coverage gate
/// credits can refute an address error through its reconstruction:
/// `x86_reconstruct_effective_address` builds both halves from the same
/// operand, so an obligation rebuilt at a wrong base, index, scale or
/// displacement is exactly as Valid as the original. That is measured
/// SEMANTICALLY (the rebuilt obligation must evaluate `Invalid` to count); a
/// structural version of this test credited the compare-exchange rows
/// (`Cmpxchg8`/`Cmpxchg16`, and then `AtomicLoadCmpxchg16b`) with teeth
/// because their halves are different trees at every operand. That is why this
/// lane exists and now carries those three too, and if the partition ever
/// changes the claim has to be restated.
#[test]
fn the_shared_reconstruction_still_has_no_address_teeth() {
    use trust_cg_verify::coverage_gate::{ALL_X86_OPCODES, OpcodeClass, classify_x86};
    use trust_cg_verify::x86_64_function_verifier::x86_reconstruction_teeth;

    let mut with_teeth: Vec<String> = Vec::new();
    let mut toothless = 0usize;
    for &opcode in ALL_X86_OPCODES {
        if !matches!(classify_x86(opcode), OpcodeClass::EmittableNeedsProof) {
            continue;
        }
        let Some(teeth) = x86_reconstruction_teeth(opcode) else {
            continue;
        };
        if teeth.operand_perturbation_can_refute {
            with_teeth.push(format!("{opcode:?}"));
        } else {
            toothless += 1;
        }
    }
    with_teeth.sort();
    assert!(
        with_teeth.is_empty(),
        "an opcode's reconstruction now refutes a perturbed address ({with_teeth:?}); the \
         classification comments that cite the partition must be restated"
    );
    // The three compare-exchange rows, which the structural test used to credit
    // with teeth, are carried by this lane now.
    for opcode in [
        trust_cg_ir::X86Opcode::Cmpxchg8,
        trust_cg_ir::X86Opcode::Cmpxchg16,
        trust_cg_ir::X86Opcode::AtomicLoadCmpxchg16b,
    ] {
        assert!(
            trust_cg_verify::coverage_gate::x86_opcode_has_address_credit(opcode),
            "{opcode:?} must be routed to the byte-level address lane"
        );
        let prefix = format!("{opcode:?} ");
        assert!(
            addr::EMITTED_X86_MEM_MOV
                .iter()
                .any(|entry| entry.label.starts_with(&prefix)),
            "{opcode:?} needs captured encodings in the lane's corpus"
        );
    }
    // The precise claim, rather than a loose floor: EVERY opcode this lane
    // credits is address-toothless through the shared reconstruction. That is
    // exactly why the lane exists, and a loose `toothless >= N` would pass
    // trivially on the ~138 non-memory opcodes that also have no address to
    // perturb.
    let mut credited_but_has_teeth: Vec<String> = Vec::new();
    let mut not_reconstructed: Vec<String> = Vec::new();
    for &opcode in ALL_X86_OPCODES {
        if !trust_cg_verify::coverage_gate::x86_opcode_has_address_credit(opcode) {
            continue;
        }
        // An opcode with NO reconstruction would fall outside this claim:
        // there is no shared reconstruction for it to be toothless THROUGH.
        // No credited opcode is in that position. Every one, the sixteen
        // volatile forms included, has a representative instance in its ISel
        // register class that reconstructs, so the claim covers the whole lane.
        let Some(teeth) = x86_reconstruction_teeth(opcode) else {
            not_reconstructed.push(format!("{opcode:?}"));
            continue;
        };
        if teeth.operand_perturbation_can_refute {
            credited_but_has_teeth.push(format!("{opcode:?}"));
        }
    }
    assert!(
        credited_but_has_teeth.is_empty(),
        "the shared reconstruction now refutes an address error for {credited_but_has_teeth:?}. \
         If that is a real repair, the byte-level ADDRESS credit may be re-stated or retired \
         for those opcodes; until then it is the only thing carrying their address facet"
    );
    // Before the volatile representatives took their plain siblings' register
    // classes, VolatileMovRM and VolatileMovsdRM had a Gpr32 destination for a
    // 64-bit load, the reconstruction refused it, and this list held those two.
    // A non-empty list narrows the claim above without failing it, so it is
    // asserted empty rather than counted.
    assert!(
        not_reconstructed.is_empty(),
        "credited opcodes with NO reconstruction at all, so outside the no-address-teeth claim: \
         {not_reconstructed:?}"
    );
    println!(
        "shared reconstruction: {toothless} opcodes with NO address teeth ({} of them credited \
         by this lane), {} with teeth",
        ALL_X86_OPCODES
            .iter()
            .filter(|&&o| trust_cg_verify::coverage_gate::x86_opcode_has_address_credit(o))
            .count(),
        with_teeth.len()
    );
}

// ---------------------------------------------------------------------------
// The ZERO-EXTENDING loads (`movzx r32, m8/m16`): the destination facet
// ---------------------------------------------------------------------------

/// Every zero-extending load in the LIVE corpus holds its DESTINATION facet:
/// the register the decoded bytes leave is the access value zero-extended to 64
/// bits, over dirty old registers and set top bits; and every WRONG destination
/// model (the merging MOV, a sign extension to 32 or 64 bits, the other access
/// width) refutes as a destination error through the same comparison.
#[test]
fn every_zero_extending_live_encoding_holds_its_destination_facet() {
    let corpus = live::live_mem_mov_corpus();
    let mut held = 0usize;
    let mut models_refuted = 0usize;
    let mut opcodes = std::collections::BTreeSet::new();
    for case in corpus.iter().filter(|c| c.intent.zero_extending_load) {
        let outcome = addr::destination_write_holds(&case.bytes, &case.intent)
            .unwrap_or_else(|e| panic!("{}: destination does not hold: {e}", case.label));
        assert!(
            outcome.dirty_rows > 0 && outcome.signed_rows > 0,
            "{}",
            case.label
        );
        held += 1;
        opcodes.insert(case.label.split(' ').next().unwrap_or_default().to_string());
        let source = addr::intent_destination_denotation(case.intent.access_bits);
        for (label, model) in addr::destination_model_controls(case.intent.access_bits) {
            let machine = addr::machine_destination_denotation(model);
            assert!(
                matches!(
                    addr::compare_destinations(&source, &machine, case.intent.access_bits),
                    Err(addr::AddressRefutation::DestinationWrite { .. })
                ),
                "{} :: destination model `{label}` did not refute as a destination error",
                case.label
            );
            models_refuted += 1;
        }
    }
    let expected: std::collections::BTreeSet<String> = [
        "MovzxRM8",
        "MovzxRM16",
        "MovzxRM8Sib",
        "VolatileMovzxRM8",
        "VolatileMovzxRM16",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    assert_eq!(
        opcodes, expected,
        "every zero-extending opcode must be in the corpus"
    );
    assert!(
        held >= 30,
        "only {held} zero-extending encodings were checked"
    );
    println!(
        "zero-extending loads: {held} live encodings hold their destination facet; \
         {models_refuted} wrong destination models refuted"
    );
}

/// The WHOLE register product through the LIVE encoder: every destination x
/// every base (RSP and R12 force a SIB byte, RBP and R13 force a displacement)
/// x a displacement set crossing both disp8 boundaries, for both widths and
/// both the plain and volatile forms; and every destination x base x index
/// (RSP is not an index) x scale for the byte SIB form. Each encoding must hold
/// its address AND its destination facet. The captured corpus is the credit;
/// this is what keeps its independence from resting on the table being wide.
#[test]
fn the_zero_extending_loads_hold_over_the_whole_register_product() {
    const R64: [&str; 16] = [
        "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12",
        "r13", "r14", "r15",
    ];
    let mut checked = 0usize;
    for (op, bits) in [
        (trust_cg_ir::X86Opcode::MovzxRM8, 8),
        (trust_cg_ir::X86Opcode::MovzxRM16, 16),
        (trust_cg_ir::X86Opcode::VolatileMovzxRM8, 8),
        (trust_cg_ir::X86Opcode::VolatileMovzxRM16, 16),
    ] {
        for dst in R64 {
            for base in R64 {
                for disp in [0i64, 1, -1, 127, 128, -128, -129, 4096, -0x8000_0000] {
                    let bytes = live::live_encode_plain(op, dst, base, disp)
                        .unwrap_or_else(|| panic!("{op:?} {dst},[{base}{disp:+}] must encode"));
                    let intent = addr::MemAccessIntent {
                        reg_root: live::root_of(dst),
                        reg_file: addr::RegFile::Gpr,
                        base_root: live::root_of(base),
                        index_root: None,
                        scale: 1,
                        disp,
                        access_bits: bits,
                        is_store: false,
                        zero_extending_load: true,
                    };
                    addr::address_encoding_holds(&bytes, &intent).unwrap_or_else(|e| {
                        panic!("{op:?} {dst},[{base}{disp:+}] = {bytes:02x?}: {e}")
                    });
                    addr::destination_write_holds(&bytes, &intent).unwrap_or_else(|e| {
                        panic!("{op:?} {dst},[{base}{disp:+}] = {bytes:02x?} destination: {e}")
                    });
                    checked += 1;
                }
            }
        }
    }
    for dst in R64 {
        for base in R64 {
            for index in R64.iter().copied().filter(|&r| r != "rsp") {
                for scale in [1u8, 2, 4, 8] {
                    for disp in [0i64, -8, 4096] {
                        let bytes = live::live_encode_sib(
                            trust_cg_ir::X86Opcode::MovzxRM8Sib,
                            dst,
                            base,
                            index,
                            scale,
                            disp,
                        )
                        .unwrap_or_else(|| {
                            panic!("MovzxRM8Sib {dst},[{base}+{index}*{scale}{disp:+}] must encode")
                        });
                        let intent = addr::MemAccessIntent {
                            reg_root: live::root_of(dst),
                            reg_file: addr::RegFile::Gpr,
                            base_root: live::root_of(base),
                            index_root: Some(live::root_of(index)),
                            scale: u32::from(scale),
                            disp,
                            access_bits: 8,
                            is_store: false,
                            zero_extending_load: true,
                        };
                        addr::address_encoding_holds(&bytes, &intent).unwrap_or_else(|e| {
                            panic!(
                                "MovzxRM8Sib {dst},[{base}+{index}*{scale}{disp:+}] = \
                                 {bytes:02x?}: {e}"
                            )
                        });
                        addr::destination_write_holds(&bytes, &intent).unwrap_or_else(|e| {
                            panic!(
                                "MovzxRM8Sib {dst},[{base}+{index}*{scale}{disp:+}] destination: \
                                 {e}"
                            )
                        });
                        checked += 1;
                    }
                }
            }
        }
    }
    assert_eq!(checked, 4 * 16 * 16 * 9 + 16 * 16 * 15 * 4 * 3);
    println!("zero-extending loads: {checked} live encodings hold address and destination");
}

/// THE SILICON DIFFERENTIAL for the destination rule. The decoder, the SDM
/// transcription and the intent were written from the same manual, so a shared
/// MISREADING of what `movzx r32, m8` and `mov r8, m8` leave in the register
/// would be invisible to them. This runs both instructions on this CPU over the
/// destination witness family (dirty old registers, every memory pattern) and
/// requires the SDM model the lane uses to predict the hardware exactly. One
/// CPU and a witness grid: it defeats a shared misreading; it is not a proof.
#[cfg(target_arch = "x86_64")]
#[test]
fn the_destination_models_match_this_cpu() {
    use addr::{DestinationWrite, machine_destination_denotation};
    use trust_cg_verify::smt::EvalEnv;

    let model = |write: DestinationWrite, old: u64, mem: u64| -> u64 {
        let mut env = EvalEnv::default();
        env.insert("dst_old".to_string(), old);
        env.insert("mem_qword".to_string(), mem);
        machine_destination_denotation(write)
            .try_eval(&env)
            .expect("the destination model evaluates")
            .as_u64()
    };
    let mut compared = 0usize;
    for old in addr::DESTINATION_OLD_VALUES {
        for mem in addr::DESTINATION_MEMORY_VALUES {
            let cell = mem.to_le_bytes();
            let p = cell.as_ptr();
            let (zx8, zx16, mov8, mov16): (u64, u64, u64, u64);
            // SAFETY: each block reads 1 or 2 bytes of the 8-byte `cell` that
            // `p` points to and writes only its named output register.
            unsafe {
                core::arch::asm!(
                    "mov {r}, {old}",
                    "movzx {r:e}, byte ptr [{p}]",
                    r = out(reg) zx8,
                    old = in(reg) old,
                    p = in(reg) p,
                    options(nostack, readonly, preserves_flags)
                );
                core::arch::asm!(
                    "mov {r}, {old}",
                    "movzx {r:e}, word ptr [{p}]",
                    r = out(reg) zx16,
                    old = in(reg) old,
                    p = in(reg) p,
                    options(nostack, readonly, preserves_flags)
                );
                core::arch::asm!(
                    "mov {r}, {old}",
                    "mov {r:l}, byte ptr [{p}]",
                    r = out(reg_abcd) mov8,
                    old = in(reg) old,
                    p = in(reg) p,
                    options(nostack, readonly, preserves_flags)
                );
                core::arch::asm!(
                    "mov {r}, {old}",
                    "mov {r:x}, word ptr [{p}]",
                    r = out(reg) mov16,
                    old = in(reg) old,
                    p = in(reg) p,
                    options(nostack, readonly, preserves_flags)
                );
            }
            assert_eq!(
                zx8,
                model(DestinationWrite::ZeroExtend { from_bits: 8 }, old, mem)
            );
            assert_eq!(
                zx16,
                model(DestinationWrite::ZeroExtend { from_bits: 16 }, old, mem)
            );
            assert_eq!(
                mov8,
                model(DestinationWrite::MergeLow { bits: 8 }, old, mem)
            );
            assert_eq!(
                mov16,
                model(DestinationWrite::MergeLow { bits: 16 }, old, mem)
            );
            // And the intent agrees with the zero-extending hardware.
            let mut env = EvalEnv::default();
            env.insert("mem_qword".to_string(), mem);
            assert_eq!(
                zx8,
                addr::intent_destination_denotation(8)
                    .try_eval(&env)
                    .expect("the intent evaluates")
                    .as_u64()
            );
            compared += 4;
        }
    }
    assert!(compared >= 4 * 4 * 12);
    println!("destination models: {compared} hardware results predicted exactly");
}
