// Copyright 2026 Andrew Yates | Apache-2.0
//! Live silicon differential of the NEON `LD1`/`ST1` post-index FORM theorems
//! (ledger `L04-P1`).
//!
//! The `NeonLd1Post`/`NeonSt1Post` rows are credited per instruction only by
//! a replayed certificate of their form theorem
//! (`aarch64_neon_structure_forms`). Both sides of every theorem are
//! transcriptions written for this repository. This target checks them
//! against THIS CPU, for each of the fourteen forms (`LD1`/`ST1` x `8B`, `16B`,
//! `4H`, `8H`, `2S`, `4S`, `2D`):
//!
//! 1. the live encoder must produce exactly the word the memory-effect lane
//!    re-derives (which ENC-5 requires the emitted word to be), ENC-5 must
//!    accept it and refuse every single-bit flip, and the word must decode to
//!    the form the binder attributes;
//! 2. the word runs on this CPU inside a JIT stub (`x9` = an address inside a
//!    48-byte buffer, `q3` loaded with a garbage pattern, the word, `q3` and
//!    `x9` stored back) over deterministic pseudo-random buffers and
//!    registers;
//! 3. both sides of the form theorem are evaluated at the CPU's own
//!    observations: for a load, at every register byte `j` with the
//!    single-point memory placed on the byte the CPU loaded there; for a
//!    store, at every buffer byte around the transfer; and the written-back
//!    base;
//! 4. every machine defect of the theorem (`NeonStructureMutation`) must
//!    disagree with the CPU on some sample.
//!
//! Single-threaded, one CPU, finitely many inputs: testing evidence about the
//! models, not a proof, and it credits nothing.
#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]

use trust_cg_codegen::aarch64::decode_check::A64DecodeCheck;
use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_codegen::decode_check::{DecodeCheck, DecodeCheckOutcome};
use trust_cg_verify::aarch64_neon_structure_forms::{
    NEON_STRUCTURE_FORMS, NeonStructureForm, NeonStructureMutation, NeonStructureTransfer,
    bind_neon_structure_instruction, decode_neon_structure_word, proof_neon_structure_form,
    proof_neon_structure_form_with_mutation, representative_neon_instruction,
};
use trust_cg_verify::lowering_proof::ProofObligation;
use trust_cg_verify::smt::{EvalEnv, EvalResult};

/// `ldr x9,[x0]; ldr q3,[x0,#16]` (assembled by clang).
const PROLOGUE: [u32; 2] = [0xf940_0009, 0x3dc0_0403];
/// `str q3,[x1]; str x9,[x1,#16]; ret; nop; nop` (assembled by clang; the
/// NOPs only pad the stub to eight words and never execute).
const EPILOGUE: [u32; 5] = [
    0x3d80_0023,
    0xf900_0829,
    0xd65f_03c0,
    0xd503_201f,
    0xd503_201f,
];
const STUB_BYTES: usize = 32;
/// Buffer bytes; the transfer starts at `OFFSET`.
const BUFFER: usize = 48;
const OFFSET: usize = 16;

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

        /// Run stub `index` with `x9 = address` and `q3 = (lo, hi)`; returns
        /// `q3` (low, high) and `x9` after the word.
        pub fn run(&self, index: usize, address: *mut u8, q3: [u64; 2]) -> [u64; 3] {
            assert!(index < self.stubs);
            let block: [u64; 4] = [address as u64, 0, q3[0], q3[1]];
            let mut out = [0u64; 3];
            // SAFETY: the stub reads 32 bytes of `block`, writes 24 bytes of
            // `out`, clobbers only the caller-saved x9 and v3, and its one
            // transfer is the 8 or 16 bytes at `address`, inside the caller's
            // buffer.
            unsafe {
                let stub: Stub = std::mem::transmute(self.base.add(index * STUB_BYTES));
                stub(block.as_ptr(), out.as_mut_ptr());
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

/// One execution of a form: the buffer before and after, `q3` before and
/// after, and the base before and after.
struct Run {
    address: u64,
    before: [u8; BUFFER],
    after: [u8; BUFFER],
    q3_before: [u64; 2],
    q3_after: [u64; 2],
    base_after: u64,
}

fn execute(page: &exec::Page, index: usize, rng: &mut Rng) -> Run {
    let mut buffer = [0u8; BUFFER];
    for chunk in buffer.chunks_mut(8) {
        chunk.copy_from_slice(&rng.next().to_le_bytes()[..chunk.len()]);
    }
    let before = buffer;
    let q3_before = [rng.next(), rng.next()];
    let address = buffer.as_mut_ptr().wrapping_add(OFFSET);
    let out = page.run(index, address, q3_before);
    Run {
        address: address as u64,
        before,
        after: buffer,
        q3_before,
        q3_after: [out[0], out[1]],
        base_after: out[2],
    }
}

fn eval(expr: &trust_cg_verify::smt::SmtExpr, env: &EvalEnv) -> u64 {
    match expr.try_eval(env).expect("the theorem evaluates") {
        EvalResult::Bv(v) => v,
        other => panic!("not a bit-vector: {other:?}"),
    }
}

/// The disagreements of both sides of `ob` with one CPU run (empty when the
/// theorem's sides both match the CPU everywhere they are evaluated).
fn disagreements(ob: &ProofObligation, form: &NeonStructureForm, run: &Run) -> Vec<String> {
    let mut out = Vec::new();
    let mut check = |env: &EvalEnv, want: u64, what: String| {
        for (side, expr) in [("intent", &ob.trust_ir_expr), ("machine", &ob.aarch64_expr)] {
            let got = eval(expr, env);
            if got != want {
                out.push(format!("{side} {what}: {got:#x} != CPU {want:#x}"));
            }
        }
    };
    let mut base_env = EvalEnv::default();
    base_env.insert("neon_base".into(), run.address);
    base_env.insert("neon_sel".into(), 1);
    for name in ["neon_p", "neon_c", "neon_d", "neon_j", "neon_q", "neon_m"] {
        base_env.insert(name.into(), 0);
    }
    base_env.insert("neon_v_lo".into(), run.q3_before[0]);
    base_env.insert("neon_v_hi".into(), run.q3_before[1]);
    check(&base_env, run.base_after, "written-back base".into());
    match form.transfer {
        NeonStructureTransfer::Load => {
            let register: Vec<u8> = run.q3_after[0]
                .to_le_bytes()
                .into_iter()
                .chain(run.q3_after[1].to_le_bytes())
                .collect();
            for (j, &cpu_byte) in register.iter().enumerate() {
                // The single-point memory sits on the byte the CPU loaded at
                // j (or, above the transfer, anywhere: both sides must be 0).
                let at = OFFSET + j.min(BUFFER - OFFSET - 1);
                let c = run.before[at];
                let mut env = EvalEnv::default();
                env.insert("neon_base".into(), run.address);
                env.insert("neon_sel".into(), 0);
                env.insert("neon_p".into(), run.address + j as u64);
                env.insert("neon_c".into(), u64::from(c));
                env.insert("neon_d".into(), u64::from(!c));
                env.insert("neon_j".into(), j as u64);
                check(&env, u64::from(cpu_byte), format!("register byte {j}"));
            }
        }
        NeonStructureTransfer::Store => {
            for (index, &cpu_byte) in run.after.iter().enumerate() {
                let q = (run.address - OFFSET as u64) + index as u64;
                let mut env = EvalEnv::default();
                env.insert("neon_base".into(), run.address);
                env.insert("neon_sel".into(), 0);
                env.insert("neon_q".into(), q);
                env.insert("neon_m".into(), u64::from(run.before[index]));
                env.insert("neon_v_lo".into(), run.q3_before[0]);
                env.insert("neon_v_hi".into(), run.q3_before[1]);
                check(&env, u64::from(cpu_byte), format!("memory byte {index}"));
            }
        }
    }
    out
}

fn forms() -> Vec<NeonStructureForm> {
    NEON_STRUCTURE_FORMS.iter().map(|(form, _)| *form).collect()
}

/// The stubs: every form with `Vt = v3` (`d3` for a 64-bit arrangement) and
/// `Xn = x9`, after checking the encoder, ENC-5 and the decoder.
fn words() -> Vec<u32> {
    forms()
        .iter()
        .map(|form| {
            let inst = representative_neon_instruction(form, false);
            let word = trust_cg_verify::aarch64_memory_effect::memory_effect_word(&inst)
                .expect("the memory-effect lane admits the representative");
            assert_eq!(
                encode_instruction(&inst).expect("the live encoder accepts the form"),
                word,
                "{form:?}"
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
            assert_eq!(
                decode_neon_structure_word(word),
                Some(bind_neon_structure_instruction(&inst).unwrap())
            );
            word
        })
        .collect()
}

#[test]
fn both_sides_of_every_form_theorem_agree_with_this_cpu() {
    let words = words();
    let page = exec::Page::new(&words);
    let mut rng = Rng(0x1D1D_0001);
    let mut executions = 0usize;
    let mut evaluations = 0usize;
    for (index, form) in forms().iter().enumerate() {
        let theorem = proof_neon_structure_form(form).unwrap();
        for _ in 0..64 {
            let run = execute(&page, index, &mut rng);
            executions += 1;
            let wrong = disagreements(&theorem, form, &run);
            assert!(wrong.is_empty(), "{}: {wrong:?}", theorem.name);
            evaluations += match form.transfer {
                NeonStructureTransfer::Load => 2 * 17,
                NeonStructureTransfer::Store => 2 * (BUFFER + 1),
            };
        }
    }
    eprintln!(
        "NEON LD1/ST1 form silicon differential: {} words, {executions} executions, \
         {evaluations} theorem-side evaluations equal to the CPU",
        words.len()
    );
    assert_eq!(words.len(), 14);
}

#[test]
fn every_machine_defect_disagrees_with_this_cpu() {
    let words = words();
    let page = exec::Page::new(&words);
    let mut rng = Rng(0x1D1D_0002);
    let mut refuted = 0usize;
    for (index, form) in forms().iter().enumerate() {
        let runs: Vec<Run> = (0..8).map(|_| execute(&page, index, &mut rng)).collect();
        for mutation in NeonStructureMutation::DEFECTS {
            let Some(wrong) = proof_neon_structure_form_with_mutation(form, mutation) else {
                continue;
            };
            // Only the machine side carries the defect: some run must show it.
            let refutes = runs.iter().any(|run| {
                disagreements(&wrong, form, run)
                    .iter()
                    .any(|d| d.starts_with("machine"))
            });
            assert!(
                refutes,
                "{form:?}: the {mutation:?} model agrees with this CPU"
            );
            refuted += 1;
        }
    }
    assert_eq!(refuted, 14 * 7 - 4 - 11 - 7);
}
