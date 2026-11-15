// Copyright 2026 Andrew Yates | Apache-2.0
//! Live silicon differential of the CRC32/CRC32C decoded-word models (ledger
//! `L04-P1`).
//!
//! The eight CRC32 opcode rows are credited by the coverage gate on an
//! in-process decision (`aarch64_crc32_proofs`): the Arm ARM pseudocode of the
//! decoded word equals the reflected-CRC intent for every register value.
//! Both sides are transcriptions written for this repository. This target
//! checks them against THIS CPU: for every form and seven register
//! assignments (distinct registers, the destination aliasing either source,
//! both sources equal, the zero register as accumulator, as data and as the
//! destination),
//!
//! 1. the live encoder (`trust_cg_codegen::aarch64::encode::encode_instruction`)
//!    must produce exactly the word the verify-side encoder re-derives, ENC-5
//!    (`A64DecodeCheck`, which includes the CRC32 binding) must accept it, and
//!    every single-bit flip of it must be rejected;
//! 2. the word runs on this CPU inside a small JIT stub (`x9`, `x10`, `x11`
//!    loaded from memory, the word, all three stored back), over an
//!    edge-value grid and deterministic pseudo-random register values whose
//!    upper bits are garbage the instruction must ignore;
//! 3. all three registers after the word are compared with the machine-side
//!    model (the decoded word's pseudocode) and with the intent, both
//!    evaluated by the memoized concrete evaluator, and with a host bitwise
//!    reference; the registers the word does not write must be unchanged;
//! 4. the neighbouring models (the other polynomial, the next data width, the
//!    MSB-first register) must DISAGREE with the CPU on some input.
//!
//! Single-threaded, one CPU, finitely many inputs: testing evidence about the
//! models, not a proof, and it credits nothing.
#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]

use std::collections::HashMap;

use trust_cg_codegen::aarch64::decode_check::A64DecodeCheck;
use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_codegen::decode_check::{DecodeCheck, DecodeCheckOutcome};
use trust_cg_verify::aarch64_crc32_proofs::{
    Crc32Form, Crc32IntentMutation, REFLECTED_CASTAGNOLI, REFLECTED_IEEE, crc32_intent, crc32_word,
    decode_crc32_word, denote_crc32, mutated_intent, representative_instruction,
};
use trust_cg_verify::gf2_affine_decide::{Concrete, eval_concrete};
use trust_cg_verify::smt::SmtExpr;

// ===========================================================================
// Executable stubs
// ===========================================================================

/// `ldr x9,[x0]; ldr x10,[x0,#8]; ldr x11,[x0,#16]` (llvm-mc).
const PROLOGUE: [u32; 3] = [0xf940_0009, 0xf940_040a, 0xf940_080b];
/// `str x9,[x1]; str x10,[x1,#8]; str x11,[x1,#16]; ret` (llvm-mc).
const EPILOGUE: [u32; 4] = [0xf900_0029, 0xf900_042a, 0xf900_082b, 0xd65f_03c0];
/// Bytes per stub.
const STUB_BYTES: usize = 32;

mod exec {
    use super::{EPILOGUE, PROLOGUE, STUB_BYTES};

    type Stub = unsafe extern "C" fn(*const u64, *mut u64);

    #[cfg(target_os = "macos")]
    unsafe extern "C" {
        fn pthread_jit_write_protect_np(enabled: libc::c_int);
        fn sys_icache_invalidate(start: *mut libc::c_void, len: libc::size_t);
    }

    /// An executable mapping holding one stub per word.
    pub struct Page {
        base: *mut u8,
        len: usize,
        stubs: usize,
    }

    impl Page {
        pub fn new(words: &[u32]) -> Page {
            let mut code = Vec::with_capacity(words.len() * STUB_BYTES);
            for &word in words {
                let start = code.len();
                for w in PROLOGUE.iter().chain([word].iter()).chain(EPILOGUE.iter()) {
                    code.extend_from_slice(&w.to_le_bytes());
                }
                assert_eq!(code.len() - start, STUB_BYTES);
            }
            let page = 16 * 1024;
            let len = code.len().div_ceil(page).max(1) * page;
            // SAFETY: an anonymous private mapping; every pointer below stays
            // inside it.
            unsafe {
                let base = map(len);
                write(base, &code);
                Page {
                    base,
                    len,
                    stubs: words.len(),
                }
            }
        }

        /// Run stub `index` with `x9`, `x10`, `x11` set; returns the three
        /// registers after the word.
        pub fn run(&self, index: usize, regs: [u64; 3]) -> [u64; 3] {
            assert!(index < self.stubs);
            let mut out = [0u64; 3];
            // SAFETY: the stub reads 24 bytes of `regs`, writes 24 bytes of
            // `out`, and clobbers only the caller-saved x9-x11.
            unsafe {
                let stub: Stub = std::mem::transmute(self.base.add(index * STUB_BYTES));
                stub(regs.as_ptr(), out.as_mut_ptr());
            }
            out
        }
    }

    impl Drop for Page {
        fn drop(&mut self) {
            // SAFETY: `base`/`len` are exactly the mapping `new` created.
            unsafe {
                libc::munmap(self.base.cast(), self.len);
            }
        }
    }

    #[cfg(target_os = "macos")]
    unsafe fn map(len: usize) -> *mut u8 {
        let base = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                len,
                libc::PROT_READ | libc::PROT_WRITE | libc::PROT_EXEC,
                libc::MAP_PRIVATE | libc::MAP_ANON | libc::MAP_JIT,
                -1,
                0,
            )
        };
        assert_ne!(base, libc::MAP_FAILED, "MAP_JIT mapping failed");
        base.cast()
    }

    #[cfg(target_os = "macos")]
    unsafe fn write(base: *mut u8, code: &[u8]) {
        unsafe {
            pthread_jit_write_protect_np(0);
            std::ptr::copy_nonoverlapping(code.as_ptr(), base, code.len());
            pthread_jit_write_protect_np(1);
            sys_icache_invalidate(base.cast(), code.len());
        }
    }

    #[cfg(target_os = "linux")]
    unsafe fn map(len: usize) -> *mut u8 {
        let base = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                len,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                -1,
                0,
            )
        };
        assert_ne!(base, libc::MAP_FAILED, "mapping failed");
        base.cast()
    }

    #[cfg(target_os = "linux")]
    unsafe fn write(base: *mut u8, code: &[u8]) {
        unsafe {
            std::ptr::copy_nonoverlapping(code.as_ptr(), base, code.len());
            let len = code.len().div_ceil(16 * 1024) * 16 * 1024;
            assert_eq!(
                libc::mprotect(base.cast(), len, libc::PROT_READ | libc::PROT_EXEC),
                0
            );
            // Arm ARM B2.4.4: clean the data lines to the point of
            // unification, invalidate the instruction lines, synchronize.
            let ctr: u64;
            std::arch::asm!("mrs {}, ctr_el0", out(reg) ctr);
            let dline = 4usize << ((ctr >> 16) & 0xf);
            let iline = 4usize << (ctr & 0xf);
            let start = base as usize;
            let end = start + code.len();
            let mut at = start & !(dline - 1);
            while at < end {
                std::arch::asm!("dc cvau, {}", in(reg) at);
                at += dline;
            }
            std::arch::asm!("dsb ish");
            let mut at = start & !(iline - 1);
            while at < end {
                std::arch::asm!("ic ivau, {}", in(reg) at);
                at += iline;
            }
            std::arch::asm!("dsb ish", "isb");
        }
    }
}

// ===========================================================================
// Inputs and references
// ===========================================================================

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // SplitMix64.
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

const EDGES: [u64; 12] = [
    0,
    1,
    0x80,
    0xFF,
    0x8000,
    0xFFFF,
    0x8000_0000,
    0xFFFF_FFFF,
    0x1_0000_0000,
    0x8000_0000_0000_0000,
    0xDEAD_BEEF_CAFE_F00D,
    u64::MAX,
];

/// Register triples `(x9, x10, x11)`: every edge pair for the two sources
/// with a random third, then pseudo-random triples.
fn inputs(seed: u64) -> Vec<[u64; 3]> {
    let mut rng = Rng(seed);
    let mut out = Vec::new();
    for &a in &EDGES {
        for &b in &EDGES {
            out.push([a, b, rng.next()]);
        }
    }
    for _ in 0..400 {
        out.push([rng.next(), rng.next(), rng.next()]);
    }
    out
}

/// The bitwise reflected CRC on host integers.
fn host_crc(mut crc: u32, data: u64, bytes: u32, reflected_poly: u32) -> u32 {
    for byte in 0..bytes {
        crc ^= ((data >> (8 * byte)) & 0xff) as u32;
        for _ in 0..8 {
            crc = if crc & 1 == 1 {
                (crc >> 1) ^ reflected_poly
            } else {
                crc >> 1
            };
        }
    }
    crc
}

fn eval(term: &SmtExpr, regs: [u64; 3]) -> u64 {
    let values: HashMap<String, u128> = [9u32, 10, 11]
        .iter()
        .zip(regs)
        .map(|(n, value)| (format!("x{n}"), u128::from(value)))
        .collect();
    match eval_concrete(term, &values).expect("the model evaluates") {
        Concrete::Bv(value, 64) => value as u64,
        other => panic!("not a 64-bit register value: {other:?}"),
    }
}

/// `(rd, rn, rm)` over x9..x11 and the zero register.
const ASSIGNMENTS: [(u32, u32, u32); 7] = [
    (11, 9, 10),
    (9, 9, 10),
    (10, 9, 10),
    (11, 10, 10),
    (11, 31, 10),
    (11, 9, 31),
    (31, 9, 10),
];

fn reg(regs: [u64; 3], n: u32) -> u64 {
    match n {
        9..=11 => regs[n as usize - 9],
        31 => 0,
        _ => unreachable!(),
    }
}

// ===========================================================================
// The differential
// ===========================================================================

#[test]
fn crc32_models_agree_with_this_cpu_and_neighbouring_models_do_not() {
    if !std::arch::is_aarch64_feature_detected!("crc") {
        eprintln!("this CPU does not implement FEAT_CRC32; nothing to compare");
        return;
    }
    let mut words = Vec::new();
    let mut cases = Vec::new();
    for form in Crc32Form::ALL {
        for (rd, rn, rm) in ASSIGNMENTS {
            let inst = representative_instruction(form, rd, rn, rm);
            let word = crc32_word(form, rd, rn, rm);
            // 1. live encoder, ENC-5, single-bit flips.
            assert_eq!(
                encode_instruction(&inst).expect("the live encoder accepts the form"),
                word,
                "{} {rd}/{rn}/{rm}",
                form.mnemonic()
            );
            assert!(
                matches!(
                    A64DecodeCheck.check_one(&inst, &word.to_le_bytes(), None),
                    DecodeCheckOutcome::Match
                ),
                "ENC-5 must accept {} {word:#010x}",
                form.mnemonic()
            );
            for bit in 0..32 {
                let flipped = word ^ (1 << bit);
                assert!(
                    !matches!(
                        A64DecodeCheck.check_one(&inst, &flipped.to_le_bytes(), None),
                        DecodeCheckOutcome::Match
                    ),
                    "ENC-5 accepted {} with bit {bit} flipped",
                    form.mnemonic()
                );
            }
            let machine = denote_crc32(&decode_crc32_word(word).expect("decodes"));
            let intent = crc32_intent(&inst).expect("in the model");
            assert_eq!(machine.dest, intent.dest);
            words.push(word);
            cases.push((form, (rd, rn, rm), machine, intent));
        }
    }
    let page = exec::Page::new(&words);
    let mut executions = 0usize;
    for (index, (form, (rd, rn, rm), machine, intent)) in cases.iter().enumerate() {
        let reflected = if form.castagnoli {
            REFLECTED_CASTAGNOLI
        } else {
            REFLECTED_IEEE
        };
        for regs in inputs(0xC0FF_EE00 ^ index as u64) {
            let after = page.run(index, regs);
            executions += 1;
            let data = reg(regs, *rm);
            let masked = if form.sz == 3 {
                data
            } else {
                data & ((1u64 << form.data_bits()) - 1)
            };
            let host = u64::from(host_crc(
                reg(regs, *rn) as u32,
                masked,
                1 << form.sz,
                reflected,
            ));
            for (slot, n) in [9u32, 10, 11].into_iter().enumerate() {
                let want = if n == *rd {
                    let by_machine = eval(&machine.value, regs);
                    let by_intent = eval(&intent.value, regs);
                    assert_eq!(by_machine, host, "{} machine model", form.mnemonic());
                    assert_eq!(by_intent, host, "{} intent", form.mnemonic());
                    by_machine
                } else {
                    regs[slot]
                };
                assert_eq!(
                    after[slot],
                    want,
                    "{} {rd}/{rn}/{rm} x{n} on {regs:#x?}",
                    form.mnemonic()
                );
            }
        }
    }
    eprintln!(
        "CRC32 silicon differential: {} words, {executions} executions, every register \
         equal to the machine model, the intent and the host reference",
        words.len()
    );
    assert_eq!(words.len(), 8 * ASSIGNMENTS.len());
}

#[test]
fn neighbouring_models_disagree_with_this_cpu() {
    if !std::arch::is_aarch64_feature_detected!("crc") {
        eprintln!("this CPU does not implement FEAT_CRC32; nothing to compare");
        return;
    }
    let forms = Crc32Form::ALL;
    let words: Vec<u32> = forms
        .iter()
        .map(|&form| crc32_word(form, 11, 9, 10))
        .collect();
    let page = exec::Page::new(&words);
    let mut refuted = 0usize;
    for (index, &form) in forms.iter().enumerate() {
        let inst = representative_instruction(form, 11, 9, 10);
        let mut neighbours: Vec<(String, SmtExpr)> = Vec::new();
        let other_poly = Crc32Form {
            castagnoli: !form.castagnoli,
            ..form
        };
        let wider = Crc32Form {
            sz: (form.sz + 1) % 4,
            ..form
        };
        for other in [other_poly, wider] {
            let word = crc32_word(other, 11, 9, 10);
            neighbours.push((
                format!("{} model", other.mnemonic()),
                denote_crc32(&decode_crc32_word(word).unwrap()).value,
            ));
        }
        for mutation in [
            Crc32IntentMutation::MsbFirst,
            Crc32IntentMutation::UnreflectedConstant,
            Crc32IntentMutation::Complemented,
        ] {
            let mutated = mutated_intent(&inst, mutation).unwrap().unwrap();
            neighbours.push((format!("{mutation:?} intent"), mutated.value));
        }
        let samples = inputs(0x0BAD_5EED ^ index as u64);
        for (label, model) in neighbours {
            let disagrees = samples.iter().any(|&regs| {
                let after = page.run(index, regs);
                eval(&model, regs) != after[2]
            });
            assert!(
                disagrees,
                "the {label} agrees with this CPU's {} on every sample",
                form.mnemonic()
            );
            refuted += 1;
        }
    }
    assert_eq!(refuted, 8 * 5);
}
