// Copyright 2026 Andrew Yates | Apache-2.0
//! Live silicon differential of the single-instruction atomic models (ledger
//! `X-OPCODES-P2`, `L04-P1`).
//!
//! The 46 atomic opcode rows (`LDAR{,B,H}`, `STLR{,B,H}`, `CAS*`, `SWP*`,
//! `LD<op>*`) are credited per instruction only by a replayed certificate of
//! their form theorem (`aarch64_atomic_forms`), and judged in process by the
//! word-bound decomposition (`aarch64_atomic_effect`). Both are transcriptions
//! of the Arm pseudocode written for this repository. This target checks both
//! against THIS CPU: for every atomic opcode at every width the selector can
//! emit, and two register assignments,
//!
//! 1. the live encoder (`trust_cg_codegen::aarch64::encode::encode_instruction`)
//!    must produce exactly the word the verify-side encoder re-derives, and
//!    ENC-5 (`A64DecodeCheck`, which now includes the atomic binding) must
//!    decode it to its intent;
//! 2. the word runs on this CPU inside a small JIT stub (`x9` = address of an
//!    aligned 8-byte window inside a 24-byte buffer, `x10` = `Rs`, `x11` =
//!    `Rt`), over an edge-value grid and deterministic pseudo-random values of
//!    the window and both registers, CAS successes and failures included;
//! 3. the destination register, the untouched register, every byte of the
//!    window and the bytes around it are compared with the decomposition's
//!    machine terms evaluated over the same inputs and, for the first
//!    register assignment, with BOTH sides of the form theorem at every
//!    register byte and every buffer byte.
//!
//! Single-threaded, one CPU, finitely many inputs: testing evidence about the
//! models, not a proof, and it credits nothing. Ordering is not observable
//! here (the memory-order litmus targets cover it).
#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]

use trust_cg_codegen::aarch64::decode_check::A64DecodeCheck;
use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_codegen::decode_check::{DecodeCheck, DecodeCheckOutcome};
use trust_cg_ir::MachInst;
use trust_cg_verify::aarch64_atomic_effect::{
    AtomicEffectPart, AtomicEffectVerdict, REG_S, REG_T, WINDOW, atomic_effect,
    atomic_effect_for_word, judge,
};
use trust_cg_verify::aarch64_atomic_forms::{
    self as forms, ATOMIC_MEMORY_OPCODES, AtomicOp, atomic_opcode_forms, atomic_opcode_shape,
    proof_atomic_form, representative_instruction,
};
use trust_cg_verify::smt::EvalEnv;

// ===========================================================================
// Executable stubs
// ===========================================================================

/// `ldr x9,[x0]; ldr x10,[x0,#8]; ldr x11,[x0,#16]` (llvm-mc).
const PROLOGUE: [u32; 3] = [0xf940_0009, 0xf940_040a, 0xf940_080b];
/// `str x10,[x1]; str x11,[x1,#8]; ret` (llvm-mc).
const EPILOGUE: [u32; 3] = [0xf900_002a, 0xf900_042b, 0xd65f_03c0];
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
                code.resize(start + STUB_BYTES, 0);
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

        /// Run stub `index` with `x9 = address`, `x10 = rs`, `x11 = rt`;
        /// returns `(x10, x11)` after the word.
        pub fn run(&self, index: usize, address: *mut u8, rs: u64, rt: u64) -> (u64, u64) {
            assert!(index < self.stubs);
            let block: [u64; 3] = [address as u64, rs, rt];
            let mut out = [0u64; 2];
            // SAFETY: the stub reads 24 bytes of `block`, writes 16 bytes of
            // `out`, clobbers only caller-saved x9-x11, and its one atomic
            // access is to the aligned window `address` points at.
            unsafe {
                let stub: Stub = std::mem::transmute(self.base.add(index * STUB_BYTES));
                stub(block.as_ptr(), out.as_mut_ptr());
            }
            (out[0], out[1])
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
// Inputs
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

/// Edge values at every width plus pseudo-random ones.
fn values(seed: u64) -> Vec<u64> {
    let mut out = vec![
        0,
        1,
        u64::MAX,
        0x80,
        0x7F,
        0xFF,
        0x8000,
        0x7FFF,
        0xFFFF,
        0x8000_0000,
        0x7FFF_FFFF,
        0xFFFF_FFFF,
        0x8000_0000_0000_0000,
        0x7FFF_FFFF_FFFF_FFFF,
    ];
    let mut rng = Rng(seed);
    for _ in 0..6 {
        out.push(rng.next());
    }
    out
}

/// One word under test.
struct Case {
    inst: MachInst,
    word: u32,
    op: AtomicOp,
    bytes: u32,
    /// Whether this case is also checked against the form theorem.
    theorem: bool,
}

fn cases() -> Vec<Case> {
    let mut out = Vec::new();
    for opcode in ATOMIC_MEMORY_OPCODES {
        let shape = atomic_opcode_shape(opcode).unwrap();
        for form in atomic_opcode_forms(opcode).unwrap() {
            // Rs = x10, Rt = x11, Rn = x9; and Rs == Rt for the LSE forms.
            let assignments: &[(u16, u16)] = match shape.op {
                AtomicOp::LoadAcquire | AtomicOp::StoreRelease | AtomicOp::Cas => &[(10, 11)],
                _ => &[(10, 11), (10, 10)],
            };
            for (index, &(rs, rt)) in assignments.iter().enumerate() {
                let inst = representative_instruction(opcode, form.bytes, rs, rt, 9).unwrap();
                let word = encode_instruction(&inst)
                    .unwrap_or_else(|e| panic!("{inst:?}: the live encoder refuses: {e:?}"));
                out.push(Case {
                    inst,
                    word,
                    op: shape.op,
                    bytes: form.bytes,
                    theorem: index == 0,
                });
            }
        }
    }
    out
}

// ===========================================================================
// The differential
// ===========================================================================

#[test]
fn live_encoder_words_are_the_verified_words_and_decode() {
    let cases = cases();
    for case in &cases {
        let decomposition = atomic_effect(&case.inst)
            .unwrap_or_else(|| panic!("{:?}: the atomic lane must admit it", case.inst));
        assert_eq!(
            decomposition.word, case.word,
            "{:?}: the live encoder's word differs from the verify-side word",
            case.inst
        );
        assert_eq!(
            judge(&decomposition),
            AtomicEffectVerdict::Holds,
            "{:?}",
            case.inst
        );
        let outcome = A64DecodeCheck.check_one(&case.inst, &case.word.to_le_bytes(), None);
        assert!(
            matches!(outcome, DecodeCheckOutcome::Match),
            "{:?}: ENC-5 does not decode {:#010x}: {outcome:?}",
            case.inst,
            case.word
        );
        // ENC-5 refuses every single-bit flip of the word for this intent.
        for bit in 0..32 {
            let flipped = case.word ^ (1 << bit);
            let outcome = A64DecodeCheck.check_one(&case.inst, &flipped.to_le_bytes(), None);
            assert!(
                !matches!(outcome, DecodeCheckOutcome::Match),
                "{:?}: ENC-5 accepts the flipped word {flipped:#010x} (bit {bit})",
                case.inst
            );
        }
    }
    eprintln!("ATOMIC_ENCODER_WORDS cases={}", cases.len());
}

fn eval(expr: &trust_cg_verify::smt::SmtExpr, env: &EvalEnv) -> u64 {
    expr.try_eval(env)
        .unwrap_or_else(|e| panic!("evaluation failed: {e:?}"))
        .as_u64()
}

#[test]
fn every_atomic_word_matches_its_models_on_this_cpu() {
    let cases = cases();
    let page = exec::Page::new(&cases.iter().map(|case| case.word).collect::<Vec<_>>());
    // A 24-byte buffer, 16-byte aligned; the window is bytes 8..16.
    #[repr(C, align(16))]
    struct Buffer([u8; 32]);
    let mut buffer = Buffer([0; 32]);
    let fill = 0xA5u8;
    let mut runs = 0usize;
    let mut theorem_checks = 0usize;
    for (index, case) in cases.iter().enumerate() {
        let decomposition = atomic_effect(&case.inst).unwrap();
        let part = |which: AtomicEffectPart| {
            decomposition
                .parts
                .iter()
                .find(|part| part.part == which)
                .map(|part| part.obligation.aarch64_expr.clone())
        };
        let value_model = part(AtomicEffectPart::Value);
        let memory_model = part(AtomicEffectPart::Memory).expect("every form has a memory part");
        // Teeth: the machine terms of a neighbouring word (another operation:
        // the low `opc` bit for LD<op>, `o3` for SWP, the class bits for
        // CAS/LDAR/STLR; and another width) must disagree with this CPU
        // somewhere on the same inputs.
        let neighbours: Vec<u32> = {
            let operation_bit = match case.op {
                AtomicOp::Swp => 15,
                AtomicOp::Cas => 21,
                AtomicOp::LoadAcquire | AtomicOp::StoreRelease => 22,
                _ => 12,
            };
            vec![case.word ^ (1 << operation_bit), case.word ^ (1 << 30)]
        };
        let neighbour_models: Vec<_> = neighbours
            .iter()
            .map(|&word| {
                let decomposition = atomic_effect_for_word(&case.inst, word).unwrap();
                let pick = |which| {
                    decomposition
                        .parts
                        .iter()
                        .find(|part| part.part == which)
                        .map(|part| part.obligation.aarch64_expr.clone())
                };
                (
                    pick(AtomicEffectPart::Value),
                    pick(AtomicEffectPart::Memory).unwrap(),
                )
            })
            .collect();
        let mut neighbour_disagreements = vec![0usize; neighbours.len()];
        let theorem = proof_atomic_form(&forms::AtomicForm {
            op: case.op,
            bytes: case.bytes,
        })
        .unwrap();
        let windows = values(0x5EED ^ index as u64);
        let registers = values(0xC0FFEE ^ (index as u64) << 8);
        for (wi, &window) in windows.iter().enumerate() {
            for (si, &s) in registers.iter().enumerate() {
                // CAS: also compare-equal values (success) with garbage above
                // the access width.
                let s = if case.op == AtomicOp::Cas && si % 3 == 0 {
                    let mask = if case.bytes == 8 {
                        u64::MAX
                    } else {
                        (1u64 << (8 * case.bytes)) - 1
                    };
                    (window & mask) | (s & !mask)
                } else {
                    s
                };
                let t = registers[(si + wi) % registers.len()].rotate_left(17);
                // Same register for Rs and Rt: both read the one value.
                let same = matches!(case.inst.operands.as_slice(), [a, b, ..] if a == b)
                    && !matches!(case.op, AtomicOp::LoadAcquire | AtomicOp::StoreRelease);
                let t = if same { s } else { t };

                buffer.0 = [fill; 32];
                buffer.0[8..16].copy_from_slice(&window.to_le_bytes());
                let before = buffer.0;
                let (x10, x11) = page.run(index, buffer.0.as_mut_ptr().wrapping_add(8), s, t);
                runs += 1;

                // The decomposition's machine terms.
                let mut env = EvalEnv::default();
                env.insert(WINDOW.to_string(), window);
                env.insert(REG_S.to_string(), s);
                env.insert(REG_T.to_string(), t);
                let after = eval(&memory_model, &env);
                let label = format!(
                    "{:?} {:#010x} window={window:#x} s={s:#x} t={t:#x}",
                    case.inst, case.word
                );
                assert_eq!(
                    u64::from_le_bytes(buffer.0[8..16].try_into().unwrap()),
                    after,
                    "{label}: memory window"
                );
                assert!(
                    buffer.0[..8]
                        .iter()
                        .chain(&buffer.0[16..])
                        .all(|&b| b == fill),
                    "{label}: bytes outside the window changed"
                );
                let (written, untouched, untouched_input) = match case.op {
                    AtomicOp::StoreRelease => (None, (x10, x11), (s, t)),
                    AtomicOp::Cas => (Some(x10), (x11, x11), (t, t)),
                    // Rs == Rt == x10: the old value lands in x10.
                    _ if same => (Some(x10), (x11, x11), (t, t)),
                    _ => (Some(x11), (x10, x10), (s, s)),
                };
                if let (Some(written), Some(model)) = (written, &value_model) {
                    assert_eq!(written, eval(model, &env), "{label}: destination register");
                }
                assert_eq!(
                    untouched, untouched_input,
                    "{label}: a register it must not write"
                );
                let silicon_window = u64::from_le_bytes(buffer.0[8..16].try_into().unwrap());
                for (slot, (value, memory)) in neighbour_models.iter().enumerate() {
                    let value_differs = match (written, value) {
                        (Some(written), Some(model)) => written != eval(model, &env),
                        _ => false,
                    };
                    if value_differs || silicon_window != eval(memory, &env) {
                        neighbour_disagreements[slot] += 1;
                    }
                }

                // Both sides of the form theorem, at every register byte and
                // every window byte (first register assignment, every eighth
                // input).
                if case.theorem && (wi * registers.len() + si).is_multiple_of(8) {
                    let base = buffer.0.as_ptr() as u64 + 8;
                    let mut env = EvalEnv::default();
                    env.insert(forms::BASE.to_string(), base);
                    for k in 0..case.bytes {
                        env.insert(forms::window_byte(k), (window >> (8 * k)) & 0xFF);
                    }
                    env.insert(forms::RS.to_string(), s);
                    env.insert(forms::RT.to_string(), t);
                    let destination = match case.op {
                        AtomicOp::Cas => x10,
                        _ if same => x10,
                        _ => x11,
                    };
                    for sel in [0u64, 1] {
                        for k in 0..16u64 {
                            env.insert(forms::SEL.to_string(), sel);
                            env.insert(forms::J.to_string(), k % 8);
                            let q = buffer.0.as_ptr() as u64 + 4 + k;
                            env.insert(forms::Q.to_string(), q);
                            // The byte outside the theorem's window is the
                            // buffer's byte at `q` before the access.
                            env.insert(forms::M.to_string(), u64::from(before[4 + k as usize]));
                            let silicon = if sel == 0 && case.op != AtomicOp::StoreRelease {
                                (destination >> (8 * (k % 8))) & 0xFF
                            } else {
                                u64::from(buffer.0[4 + k as usize])
                            };
                            // STLR has no selector: its theorem observes memory.
                            if sel == 0 && case.op == AtomicOp::StoreRelease {
                                continue;
                            }
                            for (side, expr) in [
                                ("machine", &theorem.aarch64_expr),
                                ("intent", &theorem.trust_ir_expr),
                            ] {
                                assert_eq!(
                                    eval(expr, &env) & 0xFF,
                                    silicon,
                                    "{label}: form theorem {side} side, sel={sel} k={k}"
                                );
                            }
                            theorem_checks += 1;
                        }
                    }
                }
            }
        }
        for (word, disagreements) in neighbours.iter().zip(&neighbour_disagreements) {
            assert!(
                *disagreements > 0,
                "{:?}: the models of the neighbouring word {word:#010x} never disagree with this \
                 CPU, so the differential has no teeth there",
                case.inst
            );
        }
    }
    eprintln!(
        "ATOMIC_SILICON words={} runs={runs} theorem_checks={theorem_checks}",
        cases.len()
    );
    assert!(runs > 0 && theorem_checks > 0);
}
