// Copyright 2026 Andrew Yates | Apache-2.0
//! Live silicon differential of the word-bound scalar memory-effect models
//! (ledger `L04-P1`, `X-OPCODES-P1`).
//!
//! `aarch64_memory_effect` now decomposes every attributable scalar load and
//! store form, not only the general-purpose zero-extending immediates: the
//! `H`/`S`/`D`/`Q` transfers (whose decomposition is the in-process clause-2
//! check of the Formal-only rule for those rows), the sign-extending
//! `LDRSB`/`LDRSH`, W/X pre- and post-index writeback, and register offset in
//! every packed mode. Each part's machine side is a transcription of the Arm
//! pseudocode over the instruction word written for this repository. This
//! target checks those terms against THIS CPU: for every scalar opcode and
//! every legal form, over offsets that land in each form's field and, for
//! register offset, every mode with W/X indices (garbage in the upper half of
//! a W index, negative `SXTW`/`SXTX` indices),
//!
//! 1. the live encoder (`encode_instruction`) must produce the word the
//!    decomposition carries, and ENC-5 must accept it;
//! 2. the word runs on this CPU inside a JIT stub (`x9` = base pointer into a
//!    256-byte buffer, `x10` = index, `x11` = the GPR transfer, `q0` = the
//!    SIMD&FP transfer), over pseudo-random buffer contents and transfer
//!    values;
//! 3. the base register after, the loaded register (both halves of `V0`), and
//!    every byte of the buffer are compared with the decomposition's machine
//!    terms (address, writeback, load and store parts) evaluated over the same
//!    inputs; bytes no store part names must be unchanged, and a model of the
//!    neighbouring form (another width or extension) must disagree somewhere.
//!
//! Testing evidence about the models on one CPU over finitely many inputs; it
//! is not a proof and credits nothing.
#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]

use trust_cg_codegen::aarch64::decode_check::A64DecodeCheck;
use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_codegen::decode_check::{DecodeCheck, DecodeCheckOutcome};
use trust_cg_ir::{AArch64Opcode as Op, MachInst, MachOperand as Arg, PReg};
use trust_cg_verify::aarch64_memory_effect::{
    BASE_INPUT, INDEX_INPUT, MemoryEffectDecomposition, MemoryEffectPart, memory_effect,
    memory_effect_for_word,
};
use trust_cg_verify::aarch64_scalar_memory_proofs::{
    ScalarAddressing, ScalarBank, ScalarExtension, ScalarMemoryForm, ScalarTransfer,
    bind_scalar_memory_instruction, scalar_opcode_forms,
};
use trust_cg_verify::smt::EvalEnv;

// ===========================================================================
// Executable stubs
// ===========================================================================

/// `ldr x9,[x0]; ldr x10,[x0,#8]; ldr x11,[x0,#16]; ldr q0,[x0,#32]` (llvm-mc).
const PROLOGUE: [u32; 4] = [0xf940_0009, 0xf940_040a, 0xf940_080b, 0x3dc0_0800];
/// `str x9,[x1]; str x10,[x1,#8]; str x11,[x1,#16]; str q0,[x1,#32]; ret`.
const EPILOGUE: [u32; 5] = [
    0xf900_0029,
    0xf900_042a,
    0xf900_082b,
    0x3d80_0820,
    0xd65f_03c0,
];
const STUB_BYTES: usize = 64;

mod exec {
    use super::{EPILOGUE, PROLOGUE, STUB_BYTES};

    type Stub = unsafe extern "C" fn(*const u64, *mut u64);

    #[cfg(target_os = "macos")]
    unsafe extern "C" {
        fn pthread_jit_write_protect_np(enabled: libc::c_int);
        fn sys_icache_invalidate(start: *mut libc::c_void, len: libc::size_t);
    }

    pub struct Page {
        base: *mut u8,
        len: usize,
        stubs: usize,
    }

    /// The registers a stub reads and writes.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Regs {
        pub x9: u64,
        pub x10: u64,
        pub x11: u64,
        pub q0: u128,
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

        /// Run stub `index` from `regs`; the word's one access stays inside
        /// the caller's buffer.
        pub fn run(&self, index: usize, regs: Regs) -> Regs {
            assert!(index < self.stubs);
            let block: [u64; 6] = [
                regs.x9,
                regs.x10,
                regs.x11,
                0,
                regs.q0 as u64,
                (regs.q0 >> 64) as u64,
            ];
            let mut out = [0u64; 6];
            // SAFETY: the stub reads 48 bytes of `block`, writes 48 bytes of
            // `out`, clobbers only caller-saved x9-x11 and v0, and its access
            // is inside the buffer x9 points into.
            unsafe {
                let stub: Stub = std::mem::transmute(self.base.add(index * STUB_BYTES));
                stub(block.as_ptr(), out.as_mut_ptr());
            }
            Regs {
                x9: out[0],
                x10: out[1],
                x11: out[2],
                q0: u128::from(out[4]) | (u128::from(out[5]) << 64),
            }
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
// Cases
// ===========================================================================

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

fn preg(n: u16) -> Arg {
    Arg::PReg(PReg::new(n))
}

/// The transfer register of a form: x11/w11, or h0/s0/d0/q0.
fn transfer(form: &ScalarMemoryForm) -> Arg {
    match (form.bank, form.access_bytes, form.extension) {
        (ScalarBank::Fpr, 2, _) => preg(165),
        (ScalarBank::Fpr, 4, _) => preg(128),
        (ScalarBank::Fpr, 8, _) => preg(96),
        (ScalarBank::Fpr, _, _) => preg(64),
        (ScalarBank::Gpr, 8, _) | (ScalarBank::Gpr, _, ScalarExtension::SignTo64) => preg(11),
        (ScalarBank::Gpr, _, _) => preg(32 + 11),
    }
}

/// One instruction and the index register values its mode admits.
struct Case {
    inst: MachInst,
    word: u32,
    form: ScalarMemoryForm,
    indices: Vec<u64>,
}

const SCALAR_OPCODES: [Op; 18] = [
    Op::LdrRI,
    Op::StrRI,
    Op::LdrbRI,
    Op::LdrhRI,
    Op::LdrsbRI,
    Op::LdrshRI,
    Op::StrbRI,
    Op::StrhRI,
    Op::LdrPreIndex,
    Op::LdrPostIndex,
    Op::StrPreIndex,
    Op::StrPostIndex,
    Op::LdrRO,
    Op::StrRO,
    Op::LdrbRO,
    Op::LdrhRO,
    Op::StrbRO,
    Op::StrhRO,
];

fn cases() -> Vec<Case> {
    let mut out = Vec::new();
    for opcode in SCALAR_OPCODES {
        for form in scalar_opcode_forms(opcode).unwrap() {
            let w = i64::from(form.access_bytes);
            let t = transfer(&form);
            let x9 = preg(9);
            let shapes: Vec<(Vec<Arg>, Vec<u64>)> = match form.addressing {
                ScalarAddressing::UnsignedOffset => [0, w, 2 * w, 3 * w]
                    .into_iter()
                    .map(|offset| (vec![t.clone(), x9.clone(), Arg::Imm(offset)], vec![0]))
                    .collect(),
                ScalarAddressing::Unscaled => [-64, -9, -1, 1, 7, 63]
                    .into_iter()
                    .map(|offset| (vec![t.clone(), x9.clone(), Arg::Imm(offset)], vec![0]))
                    .collect(),
                ScalarAddressing::PreIndex | ScalarAddressing::PostIndex => {
                    [-64, -16, -1, 0, 8, 63]
                        .into_iter()
                        .map(|offset| (vec![t.clone(), x9.clone(), Arg::Imm(offset)], vec![0]))
                        .collect()
                }
                ScalarAddressing::RegisterOffset => {
                    let mut shapes = Vec::new();
                    for mode in [4i64, 5, 6, 7, 12, 13, 14, 15] {
                        // UXTW/SXTW read a W index (garbage above bit 31);
                        // LSL/SXTX an X index.
                        let (index, values): (Arg, Vec<u64>) = match mode {
                            4 | 5 => (preg(32 + 10), vec![0, 1, 3, 0xDEAD_BEEF_0000_0002]),
                            12 | 13 => (
                                preg(32 + 10),
                                vec![1, 3, 0x1234_5678_FFFF_FFFE, 0xFFFF_FFFF],
                            ),
                            _ => (preg(10), vec![0, 2, u64::MAX - 1, u64::MAX]),
                        };
                        shapes.push((vec![t.clone(), x9.clone(), index, Arg::Imm(mode)], values));
                    }
                    shapes
                }
                ScalarAddressing::Literal => Vec::new(),
            };
            for (operands, indices) in shapes {
                let inst = MachInst::new(opcode, operands);
                // Only the shapes the binder attributes to THIS form.
                let Ok(binding) = bind_scalar_memory_instruction(&inst) else {
                    continue;
                };
                if binding.form != form {
                    continue;
                }
                let word = encode_instruction(&inst)
                    .unwrap_or_else(|e| panic!("{inst:?}: the live encoder refuses: {e:?}"));
                out.push(Case {
                    inst,
                    word,
                    form,
                    indices,
                });
            }
        }
    }
    out
}

fn part_expr(
    decomposition: &MemoryEffectDecomposition,
    which: MemoryEffectPart,
) -> Option<&trust_cg_verify::smt::SmtExpr> {
    decomposition
        .parts
        .iter()
        .find(|part| part.part == which)
        .map(|part| &part.obligation.aarch64_expr)
}

fn eval(expr: &trust_cg_verify::smt::SmtExpr, env: &EvalEnv) -> u64 {
    expr.try_eval(env)
        .unwrap_or_else(|e| panic!("evaluation failed: {e:?}"))
        .as_u64()
}

/// What the decomposition's machine terms predict for one run.
struct Prediction {
    base_after: u64,
    /// The loaded register: (low, high) halves.
    loaded: Option<(u64, u64)>,
    /// Stored windows: (offset into the buffer, 8 bytes).
    stored: Vec<(usize, u64)>,
}

fn predict(
    decomposition: &MemoryEffectDecomposition,
    buffer: &[u8; 256],
    buffer_addr: u64,
    regs: &exec::Regs,
    simd: bool,
) -> Option<Prediction> {
    let mut env = EvalEnv::default();
    env.insert(BASE_INPUT.to_string(), regs.x9);
    env.insert(INDEX_INPUT.to_string(), regs.x10);
    let address = eval(
        part_expr(decomposition, MemoryEffectPart::Address { lane: 0 })?,
        &env,
    );
    let offset = usize::try_from(address.wrapping_sub(buffer_addr)).ok()?;
    if offset + 16 > buffer.len() {
        return None;
    }
    let window = |at: usize| u64::from_le_bytes(buffer[at..at + 8].try_into().unwrap());
    for (name, value) in [
        ("w0", window(offset)),
        ("w0h0", window(offset)),
        ("w0h1", window(offset + 8)),
    ] {
        env.insert(name.to_string(), value);
    }
    let (data_lo, data_hi) = if simd {
        (regs.q0 as u64, (regs.q0 >> 64) as u64)
    } else {
        (regs.x11, 0)
    };
    for (name, value) in [("d0", data_lo), ("d0h0", data_lo), ("d0h1", data_hi)] {
        env.insert(name.to_string(), value);
    }
    let base_after = part_expr(decomposition, MemoryEffectPart::Writeback)
        .map_or(regs.x9, |expr| eval(expr, &env));
    let load = |half: u8| {
        part_expr(decomposition, MemoryEffectPart::Load { lane: 0, half }).map(|e| eval(e, &env))
    };
    let store = |half: u8| {
        part_expr(decomposition, MemoryEffectPart::Store { lane: 0, half }).map(|e| eval(e, &env))
    };
    let loaded = load(0).map(|low| (low, load(1).unwrap_or(0)));
    let mut stored = Vec::new();
    if let Some(low) = store(0) {
        stored.push((offset, low));
    }
    if let Some(high) = store(1) {
        stored.push((offset + 8, high));
    }
    Some(Prediction {
        base_after,
        loaded,
        stored,
    })
}

#[test]
fn every_scalar_form_word_matches_its_memory_effect_model_on_this_cpu() {
    let cases = cases();
    assert!(cases.len() > 300, "{}", cases.len());
    for case in &cases {
        let decomposition = memory_effect(&case.inst)
            .unwrap_or_else(|| panic!("{:?}: the decomposition must admit it", case.inst));
        assert_eq!(decomposition.word, case.word, "{:?}", case.inst);
        let outcome = A64DecodeCheck.check_one(&case.inst, &case.word.to_le_bytes(), None);
        assert!(
            matches!(outcome, DecodeCheckOutcome::Match),
            "{:?} {:#010x}: {outcome:?}",
            case.inst,
            case.word
        );
    }
    let page = exec::Page::new(&cases.iter().map(|case| case.word).collect::<Vec<_>>());
    #[repr(C, align(16))]
    struct Buffer([u8; 256]);
    let mut buffer = Buffer([0; 256]);
    let mut rng = Rng(0x5CA1_AB1E);
    let (mut runs, mut teeth) = (0usize, 0usize);
    for (index, case) in cases.iter().enumerate() {
        let decomposition = memory_effect(&case.inst).unwrap();
        let simd = case.form.bank == ScalarBank::Fpr;
        let load = case.form.transfer == ScalarTransfer::Load;
        // A neighbouring word: another width (size bit 30) or, for a
        // sign-extending load, another extension (opc bit 22).
        let neighbour_bits: &[u32] = if case.form.extension == ScalarExtension::Zero {
            &[30]
        } else {
            &[30, 22]
        };
        let neighbours: Vec<MemoryEffectDecomposition> = neighbour_bits
            .iter()
            .filter_map(|bit| memory_effect_for_word(&case.inst, case.word ^ (1 << bit)))
            .collect();
        let mut disagreed = vec![false; neighbours.len()];
        for &index_value in &case.indices {
            for _ in 0..12 {
                for byte in buffer.0.iter_mut() {
                    *byte = rng.next() as u8;
                }
                let before = buffer.0;
                let buffer_addr = buffer.0.as_ptr() as u64;
                let regs = exec::Regs {
                    x9: buffer_addr + 128,
                    x10: index_value,
                    x11: rng.next(),
                    q0: u128::from(rng.next()) | (u128::from(rng.next()) << 64),
                };
                let Some(expected) = predict(&decomposition, &before, buffer_addr, &regs, simd)
                else {
                    panic!("{:?}: the modelled address leaves the buffer", case.inst);
                };
                let after = page.run(index, regs);
                runs += 1;
                let label = format!(
                    "{:?} {:#010x} index={index_value:#x} regs={regs:x?}",
                    case.inst, case.word
                );
                assert_eq!(after.x9, expected.base_after, "{label}: base after");
                assert_eq!(after.x10, regs.x10, "{label}: the index register changed");
                match (load, simd, expected.loaded) {
                    (true, false, Some((low, _))) => {
                        assert_eq!(after.x11, low, "{label}: loaded X");
                        assert_eq!(after.q0, regs.q0, "{label}: V0 changed");
                    }
                    (true, true, Some((low, high))) => {
                        assert_eq!(
                            after.q0,
                            u128::from(low) | (u128::from(high) << 64),
                            "{label}: loaded V"
                        );
                        assert_eq!(after.x11, regs.x11, "{label}: X11 changed");
                    }
                    (false, _, None) => {
                        assert_eq!(after.x11, regs.x11, "{label}: X11 changed");
                        assert_eq!(after.q0, regs.q0, "{label}: V0 changed");
                    }
                    other => panic!("{label}: unexpected prediction shape {other:?}"),
                }
                let mut predicted = before;
                for (at, window) in &expected.stored {
                    predicted[*at..*at + 8].copy_from_slice(&window.to_le_bytes());
                }
                assert_eq!(buffer.0, predicted, "{label}: memory");
                for (slot, neighbour) in neighbours.iter().enumerate() {
                    let Some(other) = predict(neighbour, &before, buffer_addr, &regs, simd) else {
                        disagreed[slot] = true;
                        continue;
                    };
                    let mut other_memory = before;
                    for (at, window) in &other.stored {
                        other_memory[*at..*at + 8].copy_from_slice(&window.to_le_bytes());
                    }
                    let other_reg = other.loaded.map(|(low, high)| {
                        if simd {
                            u128::from(low) | (u128::from(high) << 64)
                        } else {
                            u128::from(low)
                        }
                    });
                    let silicon_reg = if simd {
                        after.q0
                    } else {
                        u128::from(after.x11)
                    };
                    if other_memory != buffer.0
                        || other.base_after != after.x9
                        || other_reg.is_some_and(|reg| reg != silicon_reg)
                    {
                        disagreed[slot] = true;
                    }
                }
            }
        }
        for (slot, &bit) in neighbour_bits.iter().enumerate().take(neighbours.len()) {
            assert!(
                disagreed[slot],
                "{:?}: the model of the word with bit {bit} flipped never disagrees with this \
                 CPU, so the differential has no teeth there",
                case.inst
            );
            teeth += 1;
        }
    }
    eprintln!(
        "SCALAR_MEMORY_SILICON words={} runs={runs} neighbour_controls={teeth}",
        cases.len()
    );
}
