// trust-cg-regalloc/tests/abi_clobber_weld.rs - ABI call-clobber completeness weld
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Differential WELD between the REAL AArch64 call-clobber accessors
//! (`aarch64_caller_saved_regs` / `aarch64_callee_saved_regs` in
//! `call_clobber.rs`) and the machine-checked AAPCS64 partition proven in
//! `proofs/abi_clobber_spec.lean`.
//!
//! The Clean spec proves, over the architectural register file (GPR X0..X30,
//! FPR V0..V31), that caller-saved and callee-saved are DISJOINT and TILE the
//! whole bank (every register is exactly one). This test pins the real Rust
//! `BTreeSet<PReg>` accessors to EXACTLY that partition, so a regression in
//! either direction is caught:
//!
//!   * NO volatile (caller-saved) register may be MISSING from the clobber
//!     set — that would let a value live across a call survive in a register
//!     the callee freely overwrites (a silent miscompile).
//!   * NO callee-saved (preserved) register may be WRONGLY included in the
//!     clobber set — that would force needless save/restore and could treat a
//!     preserved register as clobbered.
//!
//! GROUND-TRUTH ORACLE (mirror of abi_clobber_spec.lean):
//!   GPR callee-saved = X19..X28 ; everything else in X0..X30 is caller-saved.
//!   FPR callee-saved = V8..V15  ; everything else in V0..V31 is caller-saved.
//! These two lines are the SAME convention the Clean `gprClass` / `fprClass`
//! classifiers encode; the spec proves disjointness + tiling of this partition,
//! and this test welds the real accessors to it.
//!
//! WIDTH ALIASES. The `PReg` model encodes width-aliased views of the SAME
//! architectural register at distinct encodings (X/W for GPR; V/D/S/H for FPR).
//! The convention is a property of the underlying architectural register, so we
//! decode each encoding back to (bank, arch index) and check the alias lands in
//! the class the spec assigns that register. The B0..B31 8-bit aliases, SP/ZR,
//! and the FPCR/FPSR/NZCV system encodings are NOT allocatable and appear in
//! neither accessor; the decoder rejects them so a stray inclusion is caught.
//!
//! RESERVED EXCEPTION. X29 (FP, frame pointer) and its W29 alias are reserved
//! and non-allocatable, so the real accessors omit them from BOTH sets. The
//! spec models X29 as caller-saved (it is volatile per AAPCS64), but regalloc
//! never hands it out; we document and assert this single carve-out explicitly
//! so completeness is checked HONESTLY rather than by quietly skipping it.

use std::collections::BTreeSet;
use trust_cg_regalloc::call_clobber::{aarch64_callee_saved_regs, aarch64_caller_saved_regs};
use trust_cg_regalloc::machine_types::PReg;

/// A register bank.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Bank {
    Gpr,
    Fpr,
}

/// The two partition classes the spec proves tile each bank.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SavedClass {
    Caller,
    Callee,
}

/// Decode a `PReg` encoding into (bank, architectural index, is-allocatable-alias).
///
/// Returns `None` for any encoding that is NOT a width-alias of an allocatable
/// register the accessors partition: SP(31)/WSP(63), XZR/WZR/NZCV/FPCR/FPSR
/// (160..164), and the B0..B31 8-bit aliases (197..228). Encodings the
/// accessors should never contain therefore fail decoding loudly.
fn decode(enc: u16) -> Option<(Bank, u16)> {
    match enc {
        0..=30 => Some((Bank::Gpr, enc)),          // X0..X30
        32..=62 => Some((Bank::Gpr, enc - 32)),    // W0..W30
        64..=95 => Some((Bank::Fpr, enc - 64)),    // V0..V31
        96..=127 => Some((Bank::Fpr, enc - 96)),   // D0..D31
        128..=159 => Some((Bank::Fpr, enc - 128)), // S0..S31
        165..=196 => Some((Bank::Fpr, enc - 165)), // H0..H31
        _ => None,                                 // SP/ZR/system/B-aliases: not partitioned
    }
}

/// The GROUND-TRUTH AAPCS64 class of an architectural register, mirroring the
/// Clean `gprClass` / `fprClass` proven in abi_clobber_spec.lean.
fn spec_class(bank: Bank, idx: u16) -> SavedClass {
    match bank {
        // GPR callee-saved = X19..X28; everything else (X0..X18, X29, X30) caller-saved.
        Bank::Gpr => {
            if (19..=28).contains(&idx) {
                SavedClass::Callee
            } else {
                SavedClass::Caller
            }
        }
        // FPR callee-saved = V8..V15; everything else caller-saved.
        Bank::Fpr => {
            if (8..=15).contains(&idx) {
                SavedClass::Callee
            } else {
                SavedClass::Caller
            }
        }
    }
}

/// All width-alias encodings of an allocatable GPR architectural register.
fn gpr_aliases(idx: u16) -> Vec<u16> {
    vec![idx, idx + 32] // X, W
}

/// All width-alias encodings of an allocatable FPR architectural register.
fn fpr_aliases(idx: u16) -> Vec<u16> {
    vec![idx + 64, idx + 96, idx + 128, idx + 165] // V, D, S, H
}

/// X29 / W29 (the reserved frame pointer and its 32-bit alias).
const X29_ALIASES: [u16; 2] = [29, 29 + 32];

// =====================================================================
// (1) Every encoding in each real set decodes to a real allocatable
//     register alias, and the spec agrees with which set it is in.
// =====================================================================

#[test]
fn real_caller_set_matches_spec_caller_class() {
    let caller = aarch64_caller_saved_regs();
    for &preg in &caller {
        let enc = preg.encoding();
        let (bank, idx) = decode(enc).unwrap_or_else(|| {
            panic!("caller-saved set contains non-allocatable encoding {enc} (SP/ZR/system/B?)")
        });
        assert_eq!(
            spec_class(bank, idx),
            SavedClass::Caller,
            "enc {enc} = {bank:?} reg {idx} is in the REAL caller-saved set, \
             but the spec classifies it as callee-saved (wrongly-clobbered preserved reg)"
        );
    }
}

#[test]
fn real_callee_set_matches_spec_callee_class() {
    let callee = aarch64_callee_saved_regs();
    for &preg in &callee {
        let enc = preg.encoding();
        let (bank, idx) = decode(enc).unwrap_or_else(|| {
            panic!("callee-saved set contains non-allocatable encoding {enc} (SP/ZR/system/B?)")
        });
        assert_eq!(
            spec_class(bank, idx),
            SavedClass::Callee,
            "enc {enc} = {bank:?} reg {idx} is in the REAL callee-saved set, \
             but the spec classifies it as caller-saved"
        );
    }
}

// =====================================================================
// (2) DISJOINTNESS — no encoding is in both sets (mirrors gpr_disjoint /
//     fpr_disjoint in the spec). The accessors already have an in-module
//     disjointness test; this re-pins it at the weld boundary.
// =====================================================================

#[test]
fn real_sets_are_disjoint() {
    let caller = aarch64_caller_saved_regs();
    let callee = aarch64_callee_saved_regs();
    for r in &caller {
        assert!(
            !callee.contains(r),
            "enc {} is in BOTH caller- and callee-saved (partition overlap)",
            r.encoding()
        );
    }
}

// =====================================================================
// (3) COMPLETENESS / TILING — every allocatable architectural register's
//     EVERY width alias appears in EXACTLY ONE real set, on the side the
//     spec dictates. This is the "no volatile reg missing from the clobber
//     set, no callee-saved reg wrongly included" guarantee, checked
//     exhaustively over the modeled bank (mirrors gpr_cover / fpr_cover).
//     X29/W29 are the documented reserved carve-out: in NEITHER set.
// =====================================================================

#[test]
fn every_allocatable_alias_is_tiled_exactly_once() {
    let caller = aarch64_caller_saved_regs();
    let callee = aarch64_callee_saved_regs();

    let reserved: BTreeSet<u16> = X29_ALIASES.iter().copied().collect();

    // GPR X0..X30 (31 architectural registers).
    for idx in 0u16..=30 {
        for enc in gpr_aliases(idx) {
            check_alias(Bank::Gpr, idx, enc, &caller, &callee, &reserved);
        }
    }
    // FPR V0..V31 (32 architectural registers).
    for idx in 0u16..=31 {
        for enc in fpr_aliases(idx) {
            check_alias(Bank::Fpr, idx, enc, &caller, &callee, &reserved);
        }
    }
}

fn check_alias(
    bank: Bank,
    idx: u16,
    enc: u16,
    caller: &BTreeSet<PReg>,
    callee: &BTreeSet<PReg>,
    reserved: &BTreeSet<u16>,
) {
    let preg = PReg::new(enc);
    let in_caller = caller.contains(&preg);
    let in_callee = callee.contains(&preg);

    if reserved.contains(&enc) {
        // X29/W29: reserved frame pointer — must be in NEITHER set.
        assert!(
            !in_caller && !in_callee,
            "reserved {bank:?} reg {idx} (enc {enc}) must be in NEITHER accessor set"
        );
        return;
    }

    // Exactly one of the two sets contains this alias.
    assert!(
        in_caller ^ in_callee,
        "{bank:?} reg {idx} (enc {enc}) must be in EXACTLY ONE set \
         (caller={in_caller}, callee={in_callee}) — a missing volatile reg or \
         a wrongly-included preserved reg"
    );

    let actual = if in_caller {
        SavedClass::Caller
    } else {
        SavedClass::Callee
    };
    assert_eq!(
        actual,
        spec_class(bank, idx),
        "{bank:?} reg {idx} (enc {enc}) lands in {actual:?} but the spec proves {:?}",
        spec_class(bank, idx)
    );
}

// =====================================================================
// (4) NO STRAY ENCODINGS — every encoding in either real set is an
//     allocatable alias of a register in the modeled bank (i.e. decode
//     succeeds AND, for GPR, the index is not the reserved X29 unless via
//     the reserved carve-out — but X29 is in neither set, so any X29 alias
//     present here is a bug). This catches a B-alias / SP / system reg
//     accidentally leaking into the clobber set.
// =====================================================================

#[test]
fn real_sets_contain_only_modeled_allocatable_aliases() {
    let mut all: BTreeSet<u16> = BTreeSet::new();
    for r in aarch64_caller_saved_regs() {
        all.insert(r.encoding());
    }
    for r in aarch64_callee_saved_regs() {
        all.insert(r.encoding());
    }
    for enc in all {
        let (bank, idx) =
            decode(enc).unwrap_or_else(|| panic!("set contains non-allocatable encoding {enc}"));
        let max = match bank {
            Bank::Gpr => 30,
            Bank::Fpr => 31,
        };
        assert!(
            idx <= max,
            "{bank:?} index {idx} (enc {enc}) out of modeled range"
        );
        assert_ne!(
            (bank, idx),
            (Bank::Gpr, 29),
            "X29 (FP) alias enc {enc} must not appear in any accessor set"
        );
    }
}
