// Copyright 2026 Andrew Yates | Apache-2.0
//! Live silicon differential of the `SUBS #imm` decoded-word models (ledger
//! `L04-P1`).
//!
//! The `SubsRI` row is credited by the coverage gate on an in-process
//! decision (`aarch64_subs_imm_proofs`): the destination value and N, Z, C, V
//! of the decoded word equal the operands' difference and comparison flags.
//! Both sides are transcriptions written for this repository. This target
//! checks them against THIS CPU, for both widths, six immediates (0, 1, 16,
//! 2048, 4095 and the probe's 1) and five register assignments (the probe's
//! `rd == rn`, distinct registers both ways, and the `CMP` alias writing the
//! zero register):
//!
//! 1. the live encoder must produce exactly the word the verify-side encoder
//!    re-derives, ENC-5 must accept it and reject every single-bit flip;
//! 2. the word runs on this CPU inside a JIT stub (`x9`, `x10` loaded, the
//!    word, `mrs x11, nzcv`, all three stored back) over an edge grid and
//!    pseudo-random register values;
//! 3. the written register, the untouched register and NZCV are compared with
//!    the machine-side model, the intent and a host reference;
//! 4. neighbouring models (ADDS, a borrow carry, a signed carry, no
//!    overflow, the minuend's sign) must disagree with the CPU.
//!
//! The stack pointer as a source is not exercised here (the stub cannot
//! choose SP's value); the models' SP read is the same variable on both
//! sides. Single-threaded, one CPU, finitely many inputs: testing evidence
//! about the models, not a proof, and it credits nothing.
#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]

use trust_cg_codegen::aarch64::decode_check::A64DecodeCheck;
use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_codegen::decode_check::{DecodeCheck, DecodeCheckOutcome};
use trust_cg_verify::aarch64_subs_imm_proofs::{
    Dest, Nzcv, SubsImmForm, SubsImmIntentMutation, decode_add_sub_imm_word, denote_add_sub_imm,
    mutated_intent, representative_instruction, subs_imm_intent, subs_imm_word,
};
use trust_cg_verify::smt::{EvalEnv, EvalResult, SmtExpr};

/// `ldr x9,[x0]; ldr x10,[x0,#8]` (llvm-mc).
const PROLOGUE: [u32; 2] = [0xf940_0009, 0xf940_040a];
/// `mrs x11, nzcv; str x9,[x1]; str x10,[x1,#8]; str x11,[x1,#16]; ret`.
const EPILOGUE: [u32; 5] = [
    0xd53b_420b,
    0xf900_0029,
    0xf900_042a,
    0xf900_082b,
    0xd65f_03c0,
];
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

        /// Run stub `index` with `x9`, `x10` set; returns `x9`, `x10` and
        /// NZCV (as `mrs` reads it) after the word.
        pub fn run(&self, index: usize, regs: [u64; 2]) -> [u64; 3] {
            assert!(index < self.stubs);
            let mut out = [0u64; 3];
            // SAFETY: the stub reads 16 bytes of `regs`, writes 24 bytes of
            // `out`, and clobbers only the caller-saved x9-x11 and NZCV.
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

/// Edge values around every immediate and every sign/carry boundary, plus
/// pseudo-random ones, for both registers.
fn inputs(seed: u64) -> Vec<[u64; 2]> {
    let mut edges = vec![
        0u64,
        u64::MAX,
        0x7FFF_FFFF,
        0x8000_0000,
        0x8000_0001,
        0xFFFF_FFFF,
        0x1_0000_0000,
        0x7FFF_FFFF_FFFF_FFFF,
        0x8000_0000_0000_0000,
        0x8000_0000_0000_0001,
    ];
    for imm in [0u64, 1, 16, 2048, 4095] {
        edges.extend([imm.wrapping_sub(1), imm, imm + 1, (1 << 32) | imm]);
    }
    let mut rng = Rng(seed);
    let mut out = Vec::new();
    for &a in &edges {
        out.push([a, rng.next()]);
        out.push([rng.next(), a]);
    }
    for _ in 0..200 {
        out.push([rng.next(), rng.next()]);
    }
    out
}

fn env(regs: [u64; 2]) -> EvalEnv {
    let mut env = EvalEnv::default();
    env.insert("x9".into(), regs[0]);
    env.insert("x10".into(), regs[1]);
    env
}

fn eval_bv(term: &SmtExpr, env: &EvalEnv) -> u64 {
    match term.eval(env) {
        EvalResult::Bv(v) => v,
        other => panic!("not a bit-vector: {other:?}"),
    }
}

fn eval_flags(flags: &Nzcv, env: &EvalEnv) -> u64 {
    let bit = |term: &SmtExpr| match term.eval(env) {
        EvalResult::Bool(b) => u64::from(b),
        other => panic!("not a Boolean: {other:?}"),
    };
    (bit(&flags.n) << 31) | (bit(&flags.z) << 30) | (bit(&flags.c) << 29) | (bit(&flags.v) << 28)
}

/// Host `SUBS` at `width`: the zero-extended difference and NZCV as `mrs`
/// reads it.
fn host(a: u64, imm: u64, width: u32) -> (u64, u64) {
    let mask = if width == 64 {
        u64::MAX
    } else {
        (1 << width) - 1
    };
    let a = a & mask;
    let result = a.wrapping_sub(imm) & mask;
    let sign = |x: u64| (x >> (width - 1)) & 1;
    let n = sign(result);
    let z = u64::from(result == 0);
    let c = u64::from(a >= imm);
    let v = u64::from(sign(a) != sign(imm) && sign(result) != sign(a));
    (result, (n << 31) | (z << 30) | (c << 29) | (v << 28))
}

const IMMEDIATES: [u32; 5] = [0, 1, 16, 2048, 4095];
const ASSIGNMENTS: [(u32, u32); 5] = [(9, 9), (10, 10), (9, 10), (10, 9), (31, 9)];

fn reg(regs: [u64; 2], n: u32) -> u64 {
    regs[n as usize - 9]
}

#[test]
fn subs_imm_models_agree_with_this_cpu() {
    let mut words = Vec::new();
    let mut cases = Vec::new();
    for form in SubsImmForm::ALL {
        for imm in IMMEDIATES {
            for (rd, rn) in ASSIGNMENTS {
                let inst = representative_instruction(form, rd, rn, imm);
                let word = subs_imm_word(form, rd, rn, imm);
                assert_eq!(
                    encode_instruction(&inst).expect("the live encoder accepts SUBS #imm"),
                    word,
                    "{form:?} {rd}/{rn}/#{imm}"
                );
                assert!(
                    matches!(
                        A64DecodeCheck.check_one(&inst, &word.to_le_bytes(), None),
                        DecodeCheckOutcome::Match
                    ),
                    "ENC-5 must accept {word:#010x}"
                );
                for bit in 0..32 {
                    let flipped = word ^ (1 << bit);
                    assert!(
                        !matches!(
                            A64DecodeCheck.check_one(&inst, &flipped.to_le_bytes(), None),
                            DecodeCheckOutcome::Match
                        ),
                        "ENC-5 accepted {word:#010x} with bit {bit} flipped"
                    );
                }
                let machine = denote_add_sub_imm(&decode_add_sub_imm_word(word).unwrap());
                let intent = subs_imm_intent(&inst).unwrap();
                assert_eq!(machine.dest, intent.dest);
                words.push(word);
                cases.push((form, imm, rd, rn, machine, intent));
            }
        }
    }
    let page = exec::Page::new(&words);
    let mut executions = 0usize;
    for (index, (form, imm, rd, rn, machine, intent)) in cases.iter().enumerate() {
        let machine_flags = machine.flags.as_ref().expect("SUBS sets flags");
        for regs in inputs(0x5AB5 ^ index as u64) {
            let after = page.run(index, regs);
            executions += 1;
            let env = env(regs);
            let (difference, nzcv) = host(reg(regs, *rn), u64::from(*imm), form.width());
            assert_eq!(eval_flags(machine_flags, &env), nzcv, "machine flags");
            assert_eq!(eval_flags(&intent.flags, &env), nzcv, "intent flags");
            assert_eq!(
                after[2] & 0xF000_0000,
                nzcv,
                "{form:?} #{imm} NZCV on {regs:#x?}"
            );
            for (slot, n) in [9u32, 10].into_iter().enumerate() {
                let want = if machine.dest == Dest::Gpr(n as u8) {
                    assert_eq!(eval_bv(&machine.value, &env), difference);
                    assert_eq!(eval_bv(&intent.value, &env), difference);
                    difference
                } else {
                    regs[slot]
                };
                assert_eq!(
                    after[slot], want,
                    "{form:?} {rd}/{rn}/#{imm} x{n} on {regs:#x?}"
                );
            }
        }
    }
    eprintln!(
        "SUBS #imm silicon differential: {} words, {executions} executions, destination and \
         NZCV equal to the machine model, the intent and the host reference",
        words.len()
    );
    assert_eq!(words.len(), 2 * IMMEDIATES.len() * ASSIGNMENTS.len());
}

#[test]
fn neighbouring_models_disagree_with_this_cpu() {
    let mut refuted = 0;
    for form in SubsImmForm::ALL {
        let word = subs_imm_word(form, 9, 9, 1);
        let page = exec::Page::new(&[word]);
        let intent = subs_imm_intent(&representative_instruction(form, 9, 9, 1)).unwrap();
        let samples = inputs(0xD1FF ^ form.width() as u64);
        let observed: Vec<([u64; 2], [u64; 3])> = samples
            .iter()
            .map(|&regs| (regs, page.run(0, regs)))
            .collect();
        // The ADDS word's model.
        let adds = denote_add_sub_imm(&decode_add_sub_imm_word(word & !(1 << 30)).unwrap());
        let disagrees = |value: &SmtExpr, flags: &Nzcv| {
            observed.iter().any(|(regs, after)| {
                let env = env(*regs);
                eval_bv(value, &env) != after[0]
                    || eval_flags(flags, &env) != after[2] & 0xF000_0000
            })
        };
        assert!(
            disagrees(&adds.value, adds.flags.as_ref().unwrap()),
            "ADDS model"
        );
        refuted += 1;
        for mutation in [
            SubsImmIntentMutation::BorrowCarry,
            SubsImmIntentMutation::SignedCarry,
            SubsImmIntentMutation::NoOverflow,
            SubsImmIntentMutation::MinuendSign,
            SubsImmIntentMutation::Sum,
        ] {
            let mutated = mutated_intent(&intent, mutation);
            assert!(
                disagrees(&mutated.value, &mutated.flags),
                "{form:?} {mutation:?} agrees with this CPU on every sample"
            );
            refuted += 1;
        }
    }
    assert_eq!(refuted, 12);
}
