//! TRUST-SELF ROUND 16 (thread R16, TRUST BATCH 6): verifying trust-cg's
//! x86-64 MACHINE-CODE ENCODER CORE — the REX prefix, ModR/M, SIB, and
//! condition-code field builders, plus the x86-64 register-file predicates
//! that feed them — through the full pipeline Rust -> MIR -> trust-ir (stage1
//! `trust_ir_mir --mir-emit-closure`) -> trust-cg JIT -> machine code,
//! asserting native Rust == JIT over swept real inputs, with the LINKED
//! PRODUCTION functions (`trust_cg_codegen::x86_64::{RexPrefix,ModRM,Sib}`,
//! `trust_cg_ir::X86CondCode`, `trust_cg_ir::x86_64_regs::*`) as a SECOND
//! oracle (the round-7 dual-oracle discipline).
//!
//! WHY THIS IS NEW: the aarch64 encoders were rounds 1/7 and the aarch64
//! register file was round 5. The x86-64 encoder was UNTOUCHED until this
//! round — the same exhaustive-sweep tractability, a different ISA.
//!
//! WHY SOUNDNESS-CRITICAL: these builders assemble the exact bytes x86-64
//! machine code is made of. `RexPrefix::encode` sets REX.W (operand size)
//! and the R/X/B high-register bits; `ModRM`/`Sib` pack the register and
//! addressing fields; `X86CondCode::encoding` is the 4-bit `tttn` OR'd into
//! every Jcc/SETcc/CMOVcc; the register predicates decide which physical
//! register (and REX extension) each field names. A single wrong bit is a
//! silent miscompile of EVERY x86-64 program the backend emits.
//!
//! New verified functions in this file — the x86-64 encoder core (16
//! headline: 12 field builders + 4 condition-code predicates; Trust-itself
//! inventory 66 -> 82). The register-file props root additionally verifies
//! 10 x86-64 register predicates (by round-5's whole-swept-set convention
//! that reaches ~66 -> 92):
//!   * encoder field builders (trust-cg-codegen/src/x86_64/encode.rs):
//!     `RexPrefix::is_needed`, `RexPrefix::encode`,
//!     `ModRM::{reg_reg,ext_reg,indirect,indirect_disp8,indirect_disp32}`,
//!     `ModRM::encode`, `Sib::{base_only,scaled}`, `Sib::encode`,
//!     `require_disp32`                                          (12)
//!   * condition codes (trust-cg-ir/src/x86_64_ops.rs):
//!     `X86CondCode::{encoding,invert,is_signed,is_unsigned}`    (4)
//!   * register-file inputs (trust-cg-ir/src/x86_64_regs.rs):
//!     `x86_hw_encoding`, `X86PReg::needs_rex`, `x86_regs_overlap` (the 3
//!     most directly tied to encoding) + `x86_preg_class`,
//!     `x86_is_callee_saved`, `x86_is_caller_saved`, `x86_reg_number`,
//!     `X86RegClass::{size_bits,size_bytes}`, `X86PReg::{is_gpr,is_xmm}`
//!     — all swept + ground-truthed in the props root                 (10)
//!
//! Slices (verbatim transcriptions, modeled boundaries documented inline
//! there and summarized at each fixture below):
//!   tests/slices/trust_x86_encoder_slice.rs   (trust-cg-codegen @ 58dac2f)
//!   tests/slices/trust_x86_condcode_slice.rs  (trust-cg-ir @ 58dac2f)
//!   tests/slices/trust_x86_regfile_slice.rs   (trust-cg-ir @ 58dac2f)
//! Transcribed from THIS repo's working tree; the production fns are linked
//! into this very test binary, so transcription drift is caught by the dual
//! oracle.
//!
//! REGEN (per module; trust-ir frontend @ 5fbd88d):
//!   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//!   cd $HOME/trust-ir/frontend && env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//!     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//!     $S/bin/cargo run --bin trust_ir_mir -- <slice.rs> \
//!     --crate-type=lib -C overflow-checks=off -C debug-assertions=off \
//!     --mir-emit-closure <root> <out.tir>
//!   Every module: validate_module = 0 errors, re-parse OK, EXTERN-FREE
//!   (no host shims anywhere in this file), deterministic re-emit proven
//!   byte-identical. No-drift whnf gate re-checked green (115661) — no
//!   frontend changes this round.
//!
//! MODELED BOUNDARIES (summary; full text in the slices):
//!   encoder [B1] `require_disp32` returns `bool` in place of
//!     `Result<(),X86EncodeError>` (the Err message is diagnostic-only) —
//!     `disp < i32::MIN as i64 || disp > i32::MAX as i64` is VERBATIM;
//!     [B2] roots pass the struct fields as u32 and dispatch the ctor family
//!     by a `form` selector (the round-5 enum<->tag plumbing).
//!   condcode [B2] `invert` written as the 16-arm match RESULT-IDENTICAL to
//!     production's `transmute((self as u8) ^ 1)` (the enum has a variant at
//!     every 0x0..=0xF, so the transmute is exactly the bit-0 flip; asserted
//!     against the linked production `invert` for all 16 codes); [B3]
//!     enum<->tag plumbing at the root.
//!   regfile [B1] `x86_preg_name`/Debug/Display out of scope (diagnostic
//!     &'static str); [B2] enum->u32 tag + Option<u8>->(present,value) at
//!     the root, mirrored 1:1 in the oracles.
//!
//! COVERAGE NOTE: gated to aarch64 (the JIT target); on any other host this
//! file compiles to ZERO tests. Run tests ONE AT A TIME
//! (`-- --exact <name> --test-threads=1`): the JIT engine is not
//! thread-safe at suite scale (jit-parallel-race-2026-06-29.md). Every JIT
//! execution runs inside a WATCHDOG worker thread.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::mpsc;
use std::time::Duration;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

use trust_cg_codegen::x86_64::{ModRM as ProdModRM, RexPrefix as ProdRex, Sib as ProdSib};
use trust_cg_ir::X86CondCode as ProdCc;
use trust_cg_ir::x86_64_regs as prod_x86;

// ── shared harness (round-5 pattern) ─────────────────────────────────────────

/// Parse + JIT one embedded module; return the buffer (keep it alive while
/// calling fn pointers bound from it). All round-16 modules are EXTERN-FREE.
fn jit_module(text: &str, what: &str) -> trust_cg_codegen::jit::ExecutableBuffer {
    let module = trust_ir::parser::parse_module(text)
        .unwrap_or_else(|e| panic!("MIR-emitted `{what}` trust-ir text must parse: {e:?}"));
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(&module, &HashMap::new())
        .unwrap_or_else(|e| panic!("trust-cg JIT compile of MIR-emitted `{what}` failed: {e:?}"))
        .buffer
}

fn bind(buffer: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buffer
        .get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("JIT symbol `{sym}` not found"))
        .as_ptr()
}

const WATCHDOG_SECS: u64 = 120;

/// Run `worker` (which JITs a module and streams `expected` rows) under the
/// watchdog: the JIT buffer lives entirely inside the worker thread; the
/// main thread bounds every wait.
fn run_watchdogged<T: Send + 'static>(
    what: &'static str,
    expected: usize,
    worker: impl FnOnce(mpsc::Sender<T>) + Send + 'static,
) -> Vec<T> {
    let (tx, rx) = mpsc::channel::<T>();
    std::thread::spawn(move || worker(tx));
    let mut rows = Vec::with_capacity(expected);
    for i in 0..expected {
        match rx.recv_timeout(Duration::from_secs(WATCHDOG_SECS)) {
            Ok(row) => rows.push(row),
            Err(_) => panic!(
                "JIT `{what}` HUNG (watchdog {WATCHDOG_SECS}s): no progress at row {i} of {expected}"
            ),
        }
    }
    rows
}

// ── oracle plumbing (mirrored 1:1 from the slices) ───────────────────────────

/// Build a production X86CondCode from its 4-bit tag (there is no from_u8;
/// this mirrors the slice's total `cc_from_tag`).
fn prod_cc_from_tag(tag: u8) -> ProdCc {
    match tag {
        0x0 => ProdCc::O,
        0x1 => ProdCc::NO,
        0x2 => ProdCc::B,
        0x3 => ProdCc::AE,
        0x4 => ProdCc::E,
        0x5 => ProdCc::NE,
        0x6 => ProdCc::BE,
        0x7 => ProdCc::A,
        0x8 => ProdCc::S,
        0x9 => ProdCc::NS,
        0xA => ProdCc::P,
        0xB => ProdCc::NP,
        0xC => ProdCc::L,
        0xD => ProdCc::GE,
        0xE => ProdCc::LE,
        _ => ProdCc::G,
    }
}

/// The PRODUCTION condition-code property row (oracle for the condcode test).
fn native_cc_row(tag: u8) -> [u32; 4] {
    let cc = prod_cc_from_tag(tag);
    [
        cc.encoding() as u32,
        cc.invert().encoding() as u32,
        cc.is_signed() as u32,
        cc.is_unsigned() as u32,
    ]
}

/// The PRODUCTION REX (is_needed, encode) for a (w,r,x,b) flag-set.
fn native_rex_row(w: bool, r: bool, x: bool, b: bool) -> (u32, u32) {
    let rex = ProdRex { w, r, x, b };
    (rex.is_needed() as u32, rex.encode() as u32)
}

/// The PRODUCTION ModRM dispatch, mirroring the slice root's `form` decoder.
fn native_modrm(form: u32, x0: u32, x1: u32, x2: u32) -> u32 {
    let m = match form {
        0 => ProdModRM::reg_reg(x0 as u8, x1 as u8),
        1 => ProdModRM::ext_reg(x0 as u8, x1 as u8),
        2 => ProdModRM::indirect(x0 as u8, x1 as u8),
        3 => ProdModRM::indirect_disp8(x0 as u8, x1 as u8),
        4 => ProdModRM::indirect_disp32(x0 as u8, x1 as u8),
        5 => ProdModRM {
            mode: x0 as u8,
            reg: x1 as u8,
            rm: x2 as u8,
        },
        _ => ProdModRM::reg_reg(x0 as u8, x1 as u8),
    };
    m.encode() as u32
}

/// The PRODUCTION SIB dispatch, mirroring the slice root's `form` decoder.
fn native_sib(form: u32, x0: u32, x1: u32, x2: u32) -> u32 {
    let s = match form {
        0 => ProdSib::base_only(x0 as u8),
        2 => ProdSib {
            scale: x0 as u8,
            index: x1 as u8,
            base: x2 as u8,
        },
        _ => ProdSib::scaled(x0 as u8, x1 as u8, x2 as u8),
    };
    s.encode() as u32
}

/// Naive semantic reference for require_disp32 (the fn is private; no linked
/// oracle — verified by verbatim transcription + this in-range reference).
fn naive_fits_disp32(disp: i64) -> u32 {
    (disp >= i32::MIN as i64 && disp <= i32::MAX as i64) as u32
}

/// The x86 RegClass -> u32 tag map, mirrored 1:1 from the slice.
fn x86_class_tag(c: prod_x86::X86RegClass) -> u32 {
    use prod_x86::X86RegClass::*;
    match c {
        Gpr64 => 0,
        Gpr32 => 1,
        Gpr16 => 2,
        Gpr8 => 3,
        Xmm128 => 4,
        System => 5,
    }
}

/// The x86 register-file property POD (mirror of the slice `X86RegProps`).
#[repr(C)]
#[derive(Clone, Copy)]
struct X86RegPropsC {
    class_tag: u32,
    hw_enc: u32,
    needs_rex: u32,
    callee_saved: u32,
    caller_saved: u32,
    is_gpr: u32,
    is_xmm: u32,
    num_present: u32,
    num: u32,
    size_bits: u32,
    size_bytes: u32,
}

impl X86RegPropsC {
    fn poisoned() -> Self {
        X86RegPropsC {
            class_tag: 0xDEAD,
            hw_enc: 0xDEAD,
            needs_rex: 0xDEAD,
            callee_saved: 0xDEAD,
            caller_saved: 0xDEAD,
            is_gpr: 0xDEAD,
            is_xmm: 0xDEAD,
            num_present: 0xDEAD,
            num: 0xDEAD,
            size_bits: 0xDEAD,
            size_bytes: 0xDEAD,
        }
    }
    fn as_row(&self) -> [u32; 11] {
        [
            self.class_tag,
            self.hw_enc,
            self.needs_rex,
            self.callee_saved,
            self.caller_saved,
            self.is_gpr,
            self.is_xmm,
            self.num_present,
            self.num,
            self.size_bits,
            self.size_bytes,
        ]
    }
}

/// The PRODUCTION x86 register-file property row (oracle for the regprops test).
fn native_x86_regprops_row(e: u16) -> [u32; 11] {
    let r = prod_x86::X86PReg::new(e);
    let c = prod_x86::x86_preg_class(r);
    let (num_present, num) = match prod_x86::x86_reg_number(r) {
        Some(n) => (1u32, n as u32),
        None => (0, 0),
    };
    [
        x86_class_tag(c),
        prod_x86::x86_hw_encoding(r) as u32,
        r.needs_rex() as u32,
        prod_x86::x86_is_callee_saved(r) as u32,
        prod_x86::x86_is_caller_saved(r) as u32,
        r.is_gpr() as u32,
        r.is_xmm() as u32,
        num_present,
        num,
        c.size_bits(),
        c.size_bytes(),
    ]
}

// ── the tests ────────────────────────────────────────────────────────────────

/// `X86CondCode::{encoding,invert,is_signed,is_unsigned}` — EXHAUSTIVE over
/// all 16 condition codes, JIT vs the LINKED PRODUCTION `X86CondCode`.
#[test]
fn trust_x86_condcode_all16_production_eq_jit() {
    let expected = 16usize;
    let rows = run_watchdogged::<(u32, [u32; 4])>("x86_condcode", expected, move |tx| {
        let buffer = jit_module(X86_CONDCODE_IR, "x86_condcode");
        // SAFETY: machine code for functy.0 = (u32, ptr) -> ().
        let f: unsafe extern "C" fn(u32, *mut [u32; 4]) =
            unsafe { std::mem::transmute(bind(&buffer, "x86_condcode_root")) };
        for tag in 0u32..16 {
            let mut out = [0xDEADu32; 4];
            unsafe { f(tag, &mut out) };
            if tx.send((tag, out)).is_err() {
                return;
            }
        }
    });
    for &(tag, row) in &rows {
        let expect = native_cc_row(tag as u8);
        assert_eq!(
            row, expect,
            "condcode(tag={tag}): JIT {row:?} != production {expect:?}"
        );
    }
    let get = |t: u32| rows[t as usize].1;
    // Ground truth against the x86 SDM tttn table.
    assert_eq!(get(0x4)[0], 0x4, "E encodes 0x4 (JE = 0x74)");
    assert_eq!(get(0x4)[1], 0x5, "invert(E) = NE (bit0 flip)");
    assert_eq!(get(0x5)[1], 0x4, "invert(NE) = E");
    assert_eq!(get(0xC)[2], 1, "L (0xC) is a signed condition");
    assert_eq!(get(0xC)[3], 0, "L is NOT unsigned");
    assert_eq!(get(0x2)[3], 1, "B (0x2) is an unsigned condition");
    assert_eq!(get(0x2)[2], 0, "B is NOT signed");
    assert_eq!(get(0x0)[2], 0, "O is neither signed nor unsigned");
    assert_eq!(get(0x0)[3], 0, "O is neither signed nor unsigned");
    // invert is an involution over the whole space.
    for t in 0u32..16 {
        let inv = get(t)[1];
        assert_eq!(get(inv)[1], t, "invert(invert({t})) == {t}");
        assert_eq!(inv, t ^ 1, "invert flips exactly bit 0 (tag {t})");
    }

    // NEGATIVE CONTROL (armed): an oracle that inverts by ^2 (a plausible
    // wrong flip) must DISAGREE on E.
    let wrong = |t: u32| t ^ 2;
    assert_ne!(
        wrong(0x4),
        get(0x4)[1],
        "negative control must FAIL: ^2 inversion"
    );
}

/// `RexPrefix::{is_needed,encode}` — EXHAUSTIVE over all 16 (w,r,x,b) flag
/// combinations, JIT vs the LINKED PRODUCTION `RexPrefix`.
#[test]
fn trust_x86_rex_exhaustive_production_eq_jit() {
    let expected = 16usize;
    let rows = run_watchdogged::<(u32, u32, u32)>("x86_rex", expected, move |tx| {
        let buffer = jit_module(X86_REX_IR, "x86_rex");
        // SAFETY: machine code for functy.0 = (u32,u32,u32,u32,ptr) -> ().
        let f: unsafe extern "C" fn(u32, u32, u32, u32, *mut [u32; 2]) =
            unsafe { std::mem::transmute(bind(&buffer, "x86_rex_root")) };
        for combo in 0u32..16 {
            let (w, r, x, b) = (
                combo & 1,
                (combo >> 1) & 1,
                (combo >> 2) & 1,
                (combo >> 3) & 1,
            );
            let mut out = [0xDEADu32; 2];
            unsafe { f(w, r, x, b, &mut out) };
            if tx.send((combo, out[0], out[1])).is_err() {
                return;
            }
        }
    });
    for &(combo, is_needed, encode) in &rows {
        let (w, r, x, b) = (
            combo & 1 != 0,
            (combo >> 1) & 1 != 0,
            (combo >> 2) & 1 != 0,
            (combo >> 3) & 1 != 0,
        );
        let (en, ee) = native_rex_row(w, r, x, b);
        assert_eq!(
            (is_needed, encode),
            (en, ee),
            "rex(combo={combo:04b}): JIT != production"
        );
    }
    let at = |combo: u32| (rows[combo as usize].1, rows[combo as usize].2);
    // Ground truth against the REX byte layout 0100_WRXB.
    assert_eq!(at(0b0000), (0, 0x40), "no bits: not needed, base 0x40");
    // combo bit0 = w, bit1 = r, bit2 = x, bit3 = b:
    assert_eq!(at(0b0001), (1, 0x48), "w=1 -> needed, 0x48 (REX.W)");
    assert_eq!(at(0b0001).1, 0x48, "w=1 -> 0x48 (REX.W)");
    assert_eq!(at(0b0010).1, 0x44, "r=1 -> 0x44 (REX.R)");
    assert_eq!(at(0b0100).1, 0x42, "x=1 -> 0x42 (REX.X)");
    assert_eq!(at(0b1000).1, 0x41, "b=1 -> 0x41 (REX.B)");
    assert_eq!(at(0b1111).1, 0x4F, "all bits -> 0x4F");
    assert_eq!(at(0b1111).0, 1, "all bits: needed");

    // NEGATIVE CONTROL: a base-0x00 oracle (forgot the 0x40 REX base) must
    // disagree everywhere a REX is emitted.
    let blind = |combo: u32| (rows[combo as usize].2) & 0x0F;
    assert_ne!(
        blind(0b0001),
        at(0b0001).1,
        "negative control must FAIL: missing 0x40 base"
    );
}

/// The ModR/M family — the 5 ctors (each masking `& 0x7` and stamping its
/// `mode`) + the raw `encode()` pack — swept over the register-field product,
/// JIT vs the LINKED PRODUCTION `ModRM`.
#[test]
fn trust_x86_modrm_family_production_eq_jit() {
    // ctor forms 0..=4 and wildcards 6,7 over (x0,x1) in 0..16^2;
    // form 5 (raw encode) over (mode,reg,rm) in 0..4 x 0..16 x 0..16.
    let mut inputs: Vec<(u32, u32, u32, u32)> = Vec::new();
    for &form in &[0u32, 1, 2, 3, 4, 6, 7] {
        for x0 in 0u32..16 {
            for x1 in 0u32..16 {
                inputs.push((form, x0, x1, 0));
            }
        }
    }
    for mode in 0u32..4 {
        for reg in 0u32..16 {
            for rm in 0u32..16 {
                inputs.push((5, mode, reg, rm));
            }
        }
    }
    let expected = inputs.len();
    let inp = inputs.clone();
    let rows = run_watchdogged::<(u32, u32, u32, u32, u32)>("x86_modrm", expected, move |tx| {
        let buffer = jit_module(X86_MODRM_IR, "x86_modrm");
        // SAFETY: machine code for functy.0 = (u32,u32,u32,u32) -> (u32).
        let f: unsafe extern "C" fn(u32, u32, u32, u32) -> u32 =
            unsafe { std::mem::transmute(bind(&buffer, "x86_modrm_root")) };
        for &(form, x0, x1, x2) in &inp {
            let r = unsafe { f(form, x0, x1, x2) };
            if tx.send((form, x0, x1, x2, r)).is_err() {
                return;
            }
        }
    });
    for &(form, x0, x1, x2, r) in &rows {
        let native = native_modrm(form, x0, x1, x2);
        assert_eq!(
            r, native,
            "modrm(form={form}, {x0},{x1},{x2}): JIT {r} != production {native}"
        );
    }
    let find = |form: u32, x0: u32, x1: u32, x2: u32| {
        rows.iter()
            .find(|q| q.0 == form && q.1 == x0 && q.2 == x1 && q.3 == x2)
            .unwrap()
            .4
    };
    // Ground truth against the ModR/M byte layout [mod:2][reg:3][rm:3].
    assert_eq!(find(0, 0, 0, 0), 0xC0, "reg_reg(0,0) = mod=11 -> 0xC0");
    assert_eq!(find(0, 1, 2, 0), 0xCA, "reg_reg(1,2) = 11_001_010 = 0xCA");
    assert_eq!(
        find(0, 8, 8, 0),
        0xC0,
        "reg_reg masks &0x7: 8&7=0,8&7=0 -> 0xC0"
    );
    assert_eq!(find(2, 0, 0, 0), 0x00, "indirect(0,0) = mod=00 -> 0x00");
    assert_eq!(
        find(3, 0, 5, 0),
        0x45,
        "indirect_disp8(reg=0,base=5)=01_000_101=0x45"
    );
    assert_eq!(
        find(4, 2, 3, 0),
        0x93,
        "indirect_disp32(reg=2,base=3)=10_010_011=0x93"
    );
    assert_eq!(find(1, 4, 1, 0), 0xE1, "ext_reg(/4, rm=1)=11_100_001=0xE1");
    assert_eq!(
        find(5, 3, 7, 7),
        0xFF,
        "raw encode(mode=3,reg=7,rm=7)=11_111_111=0xFF"
    );
    assert_eq!(
        find(5, 1, 0, 5),
        0x45,
        "raw encode(mode=1,reg=0,rm=5)=01_000_101=0x45"
    );

    // NEGATIVE CONTROL: a builder that forgets the mode<<6 shift must disagree.
    let blind = |x0: u32, x1: u32| ((x0 & 7) << 3) | (x1 & 7);
    assert_ne!(
        blind(0, 0),
        find(0, 0, 0, 0),
        "negative control must FAIL: dropped mode field"
    );
}

/// The SIB family — `base_only` (RSP-no-index encoding), `scaled` (the
/// {1,2,4,8}->{0,1,2,3} scale decode + fallback), and the raw `encode()`
/// pack — swept over the scale/index/base product, JIT vs LINKED PRODUCTION.
#[test]
fn trust_x86_sib_family_production_eq_jit() {
    let mut inputs: Vec<(u32, u32, u32, u32)> = Vec::new();
    // form 0: base_only(x0) over base 0..16.
    for base in 0u32..16 {
        inputs.push((0, base, 0, 0));
    }
    // form 1: scaled(base, index, scale_factor) — every base/index x the
    // scale-factor menu (valid 1/2/4/8 + invalid 0/3/5/16/255 -> fallback 0).
    let scale_menu = [0u32, 1, 2, 3, 4, 5, 8, 16, 255];
    for base in 0u32..16 {
        for index in 0u32..16 {
            for &sf in &scale_menu {
                inputs.push((1, base, index, sf));
            }
        }
    }
    // form 2: raw encode(scale, index, base) over scale 0..4 x index,base 0..16.
    for scale in 0u32..4 {
        for index in 0u32..16 {
            for base in 0u32..16 {
                inputs.push((2, scale, index, base));
            }
        }
    }
    let expected = inputs.len();
    let inp = inputs.clone();
    let rows = run_watchdogged::<(u32, u32, u32, u32, u32)>("x86_sib", expected, move |tx| {
        let buffer = jit_module(X86_SIB_IR, "x86_sib");
        let f: unsafe extern "C" fn(u32, u32, u32, u32) -> u32 =
            unsafe { std::mem::transmute(bind(&buffer, "x86_sib_root")) };
        for &(form, x0, x1, x2) in &inp {
            let r = unsafe { f(form, x0, x1, x2) };
            if tx.send((form, x0, x1, x2, r)).is_err() {
                return;
            }
        }
    });
    for &(form, x0, x1, x2, r) in &rows {
        let native = native_sib(form, x0, x1, x2);
        assert_eq!(
            r, native,
            "sib(form={form}, {x0},{x1},{x2}): JIT {r} != production {native}"
        );
    }
    let find = |form: u32, x0: u32, x1: u32, x2: u32| {
        rows.iter()
            .find(|q| q.0 == form && q.1 == x0 && q.2 == x1 && q.3 == x2)
            .unwrap()
            .4
    };
    // Ground truth against SIB layout [scale:2][index:3][base:3].
    // base_only(base): scale=0, index=0b100 (no index), base -> 00_100_base.
    assert_eq!(find(0, 5, 0, 0), 0x25, "base_only(5)=00_100_101=0x25");
    assert_eq!(find(0, 4, 0, 0), 0x24, "base_only(4/RSP)=00_100_100=0x24");
    // scaled(base=0,index=6,scale=8): scale_bits=3 -> 11_110_000 = 0xF0.
    assert_eq!(find(1, 0, 6, 8), 0xF0, "scaled(b0,i6,x8)=11_110_000=0xF0");
    assert_eq!(find(1, 0, 6, 4), 0xB0, "scaled(b0,i6,x4)=10_110_000=0xB0");
    assert_eq!(find(1, 0, 6, 2), 0x70, "scaled(b0,i6,x2)=01_110_000=0x70");
    assert_eq!(find(1, 0, 6, 1), 0x30, "scaled(b0,i6,x1)=00_110_000=0x30");
    assert_eq!(
        find(1, 0, 6, 3),
        0x30,
        "scaled fallback: sf=3 (invalid) -> scale=0"
    );
    assert_eq!(
        find(1, 0, 6, 255),
        0x30,
        "scaled fallback: sf=255 -> scale=0"
    );
    assert_eq!(
        find(2, 3, 7, 7),
        0xFF,
        "raw encode(scale=3,index=7,base=7)=11_111_111=0xFF"
    );

    // NEGATIVE CONTROL: a decode that treats the scale FACTOR as the scale
    // BITS (skipping the {1,2,4,8}->{0..3} map) must disagree for factor 8.
    let blind = |base: u32, index: u32, sf: u32| ((sf & 3) << 6) | ((index & 7) << 3) | (base & 7);
    assert_ne!(
        blind(0, 6, 8),
        find(1, 0, 6, 8),
        "negative control must FAIL: raw scale factor"
    );
}

/// `require_disp32` — the disp32 range gate — over the i32 boundary edges
/// and beyond, JIT vs the naive in-range reference ([B1] bool form).
#[test]
fn trust_x86_require_disp32_edges_naive_eq_jit() {
    let inputs: Vec<i64> = vec![
        i64::MIN,
        i32::MIN as i64 - 1,
        i32::MIN as i64,
        i32::MIN as i64 + 1,
        -70000,
        -1,
        0,
        1,
        70000,
        i32::MAX as i64 - 1,
        i32::MAX as i64,
        i32::MAX as i64 + 1,
        i32::MAX as i64 + 1000,
        1i64 << 40,
        i64::MAX,
    ];
    let expected = inputs.len();
    let inp = inputs.clone();
    let rows = run_watchdogged::<(i64, u32)>("x86_disp32", expected, move |tx| {
        let buffer = jit_module(X86_DISP32_IR, "x86_disp32");
        // SAFETY: machine code for functy.0 = (i64) -> (u32).
        let f: unsafe extern "C" fn(i64) -> u32 =
            unsafe { std::mem::transmute(bind(&buffer, "x86_require_disp32_root")) };
        for &d in &inp {
            let r = unsafe { f(d) };
            if tx.send((d, r)).is_err() {
                return;
            }
        }
    });
    for &(d, r) in &rows {
        assert_eq!(
            r,
            naive_fits_disp32(d),
            "require_disp32({d}): JIT {r} != naive"
        );
    }
    let at = |d: i64| rows.iter().find(|q| q.0 == d).unwrap().1;
    // Ground truth: the exact i32 boundary.
    assert_eq!(at(i32::MIN as i64), 1, "i32::MIN fits");
    assert_eq!(at(i32::MIN as i64 - 1), 0, "i32::MIN - 1 does NOT fit");
    assert_eq!(at(i32::MAX as i64), 1, "i32::MAX fits");
    assert_eq!(at(i32::MAX as i64 + 1), 0, "i32::MAX + 1 does NOT fit");
    assert_eq!(at(0), 1, "0 fits");
    assert_eq!(at(i64::MIN), 0, "i64::MIN does not fit");
    assert_eq!(at(i64::MAX), 0, "i64::MAX does not fit");

    // NEGATIVE CONTROL: an unsigned-bound oracle (ignoring the negative side)
    // must disagree on i32::MIN.
    let blind = |d: i64| (d >= 0 && d <= i32::MAX as i64) as u32;
    assert_ne!(
        blind(i32::MIN as i64),
        at(i32::MIN as i64),
        "negative control must FAIL: unsigned bound"
    );
}

/// The x86-64 scalar register-file property vector — `x86_preg_class`,
/// `x86_hw_encoding`, `X86PReg::needs_rex`, `x86_is_callee_saved`,
/// `x86_is_caller_saved`, `X86PReg::{is_gpr,is_xmm}`, `x86_reg_number`,
/// `X86RegClass::{size_bits,size_bytes}` — over encodings 0..=127 (every
/// defined register 0..=81 + the whole undefined tail), JIT vs LINKED
/// PRODUCTION `trust_cg_ir::x86_64_regs`.
#[test]
fn trust_x86_regprops_exhaustive_production_eq_jit() {
    let expected = 128usize;
    let rows = run_watchdogged::<(u32, [u32; 11])>("x86_regprops", expected, move |tx| {
        let buffer = jit_module(X86_REGPROPS_IR, "x86_regprops");
        // SAFETY: machine code for functy.0 = (u16, ptr) -> ().
        let f: unsafe extern "C" fn(u16, *mut X86RegPropsC) =
            unsafe { std::mem::transmute(bind(&buffer, "x86_regprops_root")) };
        for e in 0u32..128 {
            let mut out = X86RegPropsC::poisoned();
            unsafe { f(e as u16, &mut out) };
            if tx.send((e, out.as_row())).is_err() {
                return;
            }
        }
    });
    for &(e, row) in &rows {
        let expect = native_x86_regprops_row(e as u16);
        assert_eq!(
            row, expect,
            "x86 regprops({e}): JIT {row:?} != production {expect:?}"
        );
    }
    let get = |e: u32| rows[e as usize].1;
    // Ground truth against the x86-64 encoding scheme + System V ABI.
    assert_eq!(get(0)[0], 0, "RAX classifies Gpr64");
    assert_eq!(get(0)[1], 0, "RAX hw_enc = 0");
    assert_eq!(
        get(8)[1],
        8,
        "R8 hw_enc = 8 (the full 4-bit value; ModRM takes &0x7) ..."
    );
    assert_eq!(
        get(8)[2],
        1,
        "... and R8 needs_rex (REX.B, since hw_enc >= 8)"
    );
    assert_eq!(get(0)[2], 0, "RAX does not need REX");
    assert_eq!(get(52)[2], 1, "SPL (52) needs a bare REX to avoid AH");
    assert_eq!(get(48)[2], 0, "AL (48) does not need REX");
    assert_eq!(get(3)[3], 1, "RBX is callee-saved (System V)");
    assert_eq!(get(0)[4], 1, "RAX is caller-saved");
    assert_eq!(get(0)[3], 0, "RAX is not callee-saved");
    assert_eq!(get(16)[0], 1, "EAX classifies Gpr32");
    assert_eq!(get(16)[9], 32, "EAX size_bits = 32");
    assert_eq!(get(64)[0], 4, "XMM0 classifies Xmm128");
    assert_eq!(get(64)[6], 1, "XMM0 is_xmm");
    assert_eq!(get(64)[9], 128, "XMM0 size_bits = 128");
    assert_eq!(get(64)[10], 16, "XMM0 size_bytes = 16");
    assert_eq!(
        get(64)[4],
        1,
        "XMM0 caller-saved (all XMM caller-saved in SysV)"
    );
    assert_eq!(get(80)[0], 5, "RFLAGS classifies System");
    assert_eq!(get(80)[7], 0, "RFLAGS has NO reg_number");
    assert_eq!(get(15)[7], 1, "R15 has a reg_number ...");
    assert_eq!(get(15)[8], 15, "... = 15");
    assert_eq!(get(100)[0], 5, "undefined encoding 100 falls to System");

    // NEGATIVE CONTROL: a needs_rex oracle shifted by one encoding must
    // disagree at the R8/RDI boundary (7 needs no rex, 8 does).
    let corrupt = |e: u16| prod_x86::X86PReg::new(e.wrapping_add(1)).needs_rex() as u32;
    assert_ne!(
        corrupt(7),
        get(7)[2],
        "negative control must FAIL: shifted needs_rex at e=7"
    );
}

/// `x86_regs_overlap` — THE x86-64 interference-aliasing predicate — over all
/// pairs (a,b) in 0..=90 (8281 rows: the entire defined register file
/// RAX..RIP + the undefined tail), JIT vs LINKED PRODUCTION + symmetry.
#[test]
fn trust_x86_regoverlap_exhaustive_production_eq_jit() {
    const N: u32 = 91; // 0..=90
    let expected = (N * N) as usize;
    let rows = run_watchdogged::<(u32, u32, u32)>("x86_regoverlap", expected, move |tx| {
        let buffer = jit_module(X86_REGOVERLAP_IR, "x86_regoverlap");
        // SAFETY: machine code for functy.0 = (u16, u16) -> (u32).
        let f: unsafe extern "C" fn(u16, u16) -> u32 =
            unsafe { std::mem::transmute(bind(&buffer, "x86_regoverlap_root")) };
        for a in 0..N {
            for b in 0..N {
                let r = unsafe { f(a as u16, b as u16) };
                if tx.send((a, b, r)).is_err() {
                    return;
                }
            }
        }
    });
    for &(a, b, r) in &rows {
        let native = prod_x86::x86_regs_overlap(
            prod_x86::X86PReg::new(a as u16),
            prod_x86::X86PReg::new(b as u16),
        );
        assert_eq!(
            native as u32, r,
            "x86_regs_overlap({a},{b}): production={native} jit={r}"
        );
    }
    let at = |a: u32, b: u32| rows[(a * N + b) as usize].2;
    // Symmetry over the exhaustive square.
    for a in 0..N {
        for b in 0..N {
            assert_eq!(at(a, b), at(b, a), "overlap must be symmetric at ({a},{b})");
        }
    }
    // Ground truth: the RAX/EAX/AX/AL alias chain (same root 0, GPR group).
    assert_eq!(at(0, 16), 1, "RAX overlaps EAX");
    assert_eq!(at(0, 32), 1, "RAX overlaps AX");
    assert_eq!(at(0, 48), 1, "RAX overlaps AL");
    assert_eq!(at(16, 48), 1, "EAX overlaps AL");
    assert_eq!(at(0, 1), 0, "RAX does not overlap RCX");
    assert_eq!(at(0, 17), 0, "RAX does not overlap ECX (root 1)");
    // XMM chain (group 1).
    assert_eq!(at(64, 64), 1, "XMM0 == XMM0 (equality fast path)");
    assert_eq!(at(64, 65), 0, "XMM0 does not overlap XMM1");
    assert_eq!(
        at(0, 64),
        0,
        "RAX (GPR group 0) does not overlap XMM0 (group 1)"
    );
    assert_eq!(at(3, 19), 1, "RBX overlaps EBX (root 3)");
    // R8/R8D/R8W/R8B chain (root 8).
    assert_eq!(at(8, 24), 1, "R8 overlaps R8D");
    assert_eq!(at(8, 56), 1, "R8 overlaps R8B");
    // System regs have no root -> only self-equal.
    assert_eq!(at(80, 80), 1, "RFLAGS == RFLAGS");
    assert_eq!(at(80, 81), 0, "RFLAGS vs RIP: no roots, no overlap");
    assert_eq!(
        at(82, 82),
        1,
        "undefined encoding equals itself (PartialEq fast path)"
    );
    assert_eq!(at(82, 83), 0, "distinct undefined encodings never overlap");

    // NEGATIVE CONTROL: an alias-blind oracle (pure equality) must disagree
    // on the RAX/EAX row.
    let blind = |a: u32, b: u32| (a == b) as u32;
    assert_ne!(
        blind(0, 16),
        at(0, 16),
        "negative control must FAIL: alias-blind oracle"
    );
}

/// THE ARMED CONTROL for this file (corrupt -> loud failure -> restore
/// byte-identical -> re-pass): patch the SINGLE `const u8 8` in the embedded
/// REX module (RexPrefix::encode's `byte |= 0x08` REX.W bit) to `const u8 16`
/// (0x10 — a bit that does not exist in the REX byte), JIT the corrupted
/// text, and prove the differential CATCHES the miscompiled operand-size bit
/// on EXACTLY the w=1 combinations while the pristine module re-passes.
#[test]
fn trust_x86_encoder_armed_control_corrupted_rexw_caught_then_restored() {
    let anchor = "    %11 = const u8 8\n";
    assert_eq!(
        X86_REX_IR.matches(anchor).count(),
        1,
        "armed-control anchor must be unique in the fixture"
    );
    let corrupted = X86_REX_IR.replace(anchor, "    %11 = const u8 16\n");
    assert_ne!(corrupted, X86_REX_IR);

    // Corrupted run: sweep all 16 combos.
    let rows = run_watchdogged::<(u32, u32)>("x86_rex CORRUPTED", 16, move |tx| {
        let buffer = jit_module(&corrupted, "x86_rex CORRUPTED");
        let f: unsafe extern "C" fn(u32, u32, u32, u32, *mut [u32; 2]) =
            unsafe { std::mem::transmute(bind(&buffer, "x86_rex_root")) };
        for combo in 0u32..16 {
            let (w, r, x, b) = (
                combo & 1,
                (combo >> 1) & 1,
                (combo >> 2) & 1,
                (combo >> 3) & 1,
            );
            let mut out = [0xDEADu32; 2];
            unsafe { f(w, r, x, b, &mut out) };
            if tx.send((combo, out[1])).is_err() {
                return;
            }
        }
    });
    let mut diverged = Vec::new();
    for &(combo, encode) in &rows {
        let (w, r, x, b) = (
            combo & 1 != 0,
            (combo >> 1) & 1 != 0,
            (combo >> 2) & 1 != 0,
            (combo >> 3) & 1 != 0,
        );
        let (_n, ee) = native_rex_row(w, r, x, b);
        if encode != ee {
            diverged.push(combo);
        }
    }
    // w is bit0 of combo; exactly the 8 combos with bit0 set must diverge.
    let expect_diverge: Vec<u32> = (0u32..16).filter(|c| c & 1 == 1).collect();
    assert_eq!(
        diverged, expect_diverge,
        "ARMED: the corrupted REX.W bit must be caught on exactly the w=1 combos"
    );
    // The specific corruption: w=1 alone should be 0x48, corrupted to 0x50.
    let bad = rows.iter().find(|q| q.0 == 0b0001).unwrap().1;
    assert_eq!(
        bad, 0x50,
        "ARMED: corrupted encode sets 0x10 not 0x08 -> 0x50"
    );
    assert_eq!(
        native_rex_row(true, false, false, false).1,
        0x48,
        "production REX.W = 0x48 — the divergence is LOUD"
    );

    // Restore: the pristine const (byte-identical embedded text) re-passes.
    let rows = run_watchdogged::<(u32, u32)>("x86_rex RESTORED", 16, move |tx| {
        let buffer = jit_module(X86_REX_IR, "x86_rex RESTORED");
        let f: unsafe extern "C" fn(u32, u32, u32, u32, *mut [u32; 2]) =
            unsafe { std::mem::transmute(bind(&buffer, "x86_rex_root")) };
        for combo in 0u32..16 {
            let (w, r, x, b) = (
                combo & 1,
                (combo >> 1) & 1,
                (combo >> 2) & 1,
                (combo >> 3) & 1,
            );
            let mut out = [0xDEADu32; 2];
            unsafe { f(w, r, x, b, &mut out) };
            if tx.send((combo, out[1])).is_err() {
                return;
            }
        }
    });
    for &(combo, encode) in &rows {
        let (w, r, x, b) = (
            combo & 1 != 0,
            (combo >> 1) & 1 != 0,
            (combo >> 2) & 1 != 0,
            (combo >> 3) & 1 != 0,
        );
        assert_eq!(
            encode,
            native_rex_row(w, r, x, b).1,
            "RESTORED module must re-pass at combo={combo:04b}"
        );
    }
}

// ── embedded fixtures (VERBATIM MIR-closure emits; regen per header) ─────────

/// VERBATIM MIR-closure emit of `x86_condcode_root`. X86CondCode::{encoding,invert,is_signed,is_unsigned}; slice trust_x86_condcode_slice.rs.
/// Emit: 4914 bytes; 6 member(s); validate_module = 0 error(s); re-parse OK; EXTERN-FREE.
const X86_CONDCODE_IR: &str = r#"; TrustIr text format v1
module "mir::closure::x86_condcode_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_x86_condcode_slice.rs"

functy.0 = (u32, ptr) -> ()

functy.1 = (ptr, u8) -> ()

functy.2 = (u8) -> (u8)

functy.3 = (ptr, u8) -> ()

functy.4 = (u8) -> (bool)

functy.5 = (u8) -> (bool)

fn @x86_condcode_root(functy.0) {
bb0(%0: u32, %1: ptr):
    %12 = alloca i8, align 1
    %13 = alloca i8, align 1
    %14 = trunc u32 %0 to u8
    call @func.1(%12, %14)
    br bb1(%1)
bb1(%2: ptr):
    %15 = load u8, ptr %12
    %16 = call @func.2(%15)
    br bb2(%2, %16)
bb2(%3: ptr, %4: u8):
    %17 = zext u8 %4 to u32
    store u32 %17, ptr %3
    %18 = load u8, ptr %12
    call @func.3(%13, %18)
    br bb3(%3)
bb3(%5: ptr):
    %19 = load u8, ptr %13
    %20 = call @func.2(%19)
    br bb4(%5, %20)
bb4(%6: ptr, %7: u8):
    %21 = zext u8 %7 to u32
    %22 = const i64 4
    %23 = gep i8, ptr %6, %22
    store u32 %21, ptr %23
    %24 = load u8, ptr %12
    %25 = call @func.4(%24)
    br bb5(%6, %25)
bb5(%8: ptr, %9: bool):
    %26 = const u32 1
    %27 = const u32 0
    %28 = select u32 %9, %26, %27
    %29 = const i64 8
    %30 = gep i8, ptr %8, %29
    store u32 %28, ptr %30
    %31 = load u8, ptr %12
    %32 = call @func.5(%31)
    br bb6(%8, %32)
bb6(%10: ptr, %11: bool):
    %33 = const u32 1
    %34 = const u32 0
    %35 = select u32 %11, %33, %34
    %36 = const i64 12
    %37 = gep i8, ptr %10, %36
    store u32 %35, ptr %37
    ret
}

fn @cc_from_tag(functy.1) {
bb0(%0: ptr, %1: u8):
    switch %1 [ 0: bb16 1: bb15 2: bb14 3: bb13 4: bb12 5: bb11 6: bb10 7: bb9 8: bb8 9: bb7 10: bb6 11: bb5 12: bb4 13: bb3 14: bb2 default: bb1 ]
bb1:
    %2 = const i8 15
    store i8 %2, ptr %0
    br bb17
bb2:
    %3 = const i8 14
    store i8 %3, ptr %0
    br bb17
bb3:
    %4 = const i8 13
    store i8 %4, ptr %0
    br bb17
bb4:
    %5 = const i8 12
    store i8 %5, ptr %0
    br bb17
bb5:
    %6 = const i8 11
    store i8 %6, ptr %0
    br bb17
bb6:
    %7 = const i8 10
    store i8 %7, ptr %0
    br bb17
bb7:
    %8 = const i8 9
    store i8 %8, ptr %0
    br bb17
bb8:
    %9 = const i8 8
    store i8 %9, ptr %0
    br bb17
bb9:
    %10 = const i8 7
    store i8 %10, ptr %0
    br bb17
bb10:
    %11 = const i8 6
    store i8 %11, ptr %0
    br bb17
bb11:
    %12 = const i8 5
    store i8 %12, ptr %0
    br bb17
bb12:
    %13 = const i8 4
    store i8 %13, ptr %0
    br bb17
bb13:
    %14 = const i8 3
    store i8 %14, ptr %0
    br bb17
bb14:
    %15 = const i8 2
    store i8 %15, ptr %0
    br bb17
bb15:
    %16 = const i8 1
    store i8 %16, ptr %0
    br bb17
bb16:
    %17 = const i8 0
    store i8 %17, ptr %0
    br bb17
bb17:
    ret
}

fn @X86CondCode__encoding(functy.2) {
bb0(%0: u8):
    %1 = alloca i8, align 1
    store u8 %0, ptr %1
    %2 = load i8, ptr %1
    %3 = bitcast i8 %2 to u8
    ret %3
}

fn @X86CondCode__invert(functy.3) {
bb0(%0: ptr, %1: u8):
    %2 = alloca i8, align 1
    store u8 %1, ptr %2
    %3 = load i8, ptr %2
    %4 = bitcast i8 %3 to u8
    switch %4 [ 0: bb17 1: bb16 2: bb15 3: bb14 4: bb13 5: bb12 6: bb11 7: bb10 8: bb9 9: bb8 10: bb7 11: bb6 12: bb5 13: bb4 14: bb3 15: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %5 = const i8 14
    store i8 %5, ptr %0
    br bb18
bb3:
    %6 = const i8 15
    store i8 %6, ptr %0
    br bb18
bb4:
    %7 = const i8 12
    store i8 %7, ptr %0
    br bb18
bb5:
    %8 = const i8 13
    store i8 %8, ptr %0
    br bb18
bb6:
    %9 = const i8 10
    store i8 %9, ptr %0
    br bb18
bb7:
    %10 = const i8 11
    store i8 %10, ptr %0
    br bb18
bb8:
    %11 = const i8 8
    store i8 %11, ptr %0
    br bb18
bb9:
    %12 = const i8 9
    store i8 %12, ptr %0
    br bb18
bb10:
    %13 = const i8 6
    store i8 %13, ptr %0
    br bb18
bb11:
    %14 = const i8 7
    store i8 %14, ptr %0
    br bb18
bb12:
    %15 = const i8 4
    store i8 %15, ptr %0
    br bb18
bb13:
    %16 = const i8 5
    store i8 %16, ptr %0
    br bb18
bb14:
    %17 = const i8 2
    store i8 %17, ptr %0
    br bb18
bb15:
    %18 = const i8 3
    store i8 %18, ptr %0
    br bb18
bb16:
    %19 = const i8 0
    store i8 %19, ptr %0
    br bb18
bb17:
    %20 = const i8 1
    store i8 %20, ptr %0
    br bb18
bb18:
    ret
}

fn @X86CondCode__is_signed(functy.4) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = bitcast i8 %3 to u8
    switch %4 [ 12: bb2 13: bb2 14: bb2 15: bb2 default: bb1 ]
bb1:
    %5 = const bool false
    br bb3(%5)
bb2:
    %6 = const bool true
    br bb3(%6)
bb3(%1: bool):
    ret %1
}

fn @X86CondCode__is_unsigned(functy.5) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = bitcast i8 %3 to u8
    switch %4 [ 2: bb2 3: bb2 6: bb2 7: bb2 default: bb1 ]
bb1:
    %5 = const bool false
    br bb3(%5)
bb2:
    %6 = const bool true
    br bb3(%6)
bb3(%1: bool):
    ret %1
}
"#;

/// VERBATIM MIR-closure emit of `x86_rex_root`. RexPrefix::{is_needed,encode}; slice trust_x86_encoder_slice.rs.
/// Emit: 2514 bytes; 3 member(s); validate_module = 0 error(s); re-parse OK; EXTERN-FREE.
const X86_REX_IR: &str = r#"; TrustIr text format v1
module "mir::closure::x86_rex_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_x86_encoder_slice.rs"

functy.0 = (u32, u32, u32, u32, ptr) -> ()

functy.1 = (ptr) -> (bool)

functy.2 = (ptr) -> (u8)

fn @x86_rex_root(functy.0) {
bb0(%0: u32, %1: u32, %2: u32, %3: u32, %4: ptr):
    %9 = alloca (i8, i8, i8, i8), align 1
    %10 = const u32 0
    %11 = icmp ne u32 %0, %10
    %12 = const u32 0
    %13 = icmp ne u32 %1, %12
    %14 = const u32 0
    %15 = icmp ne u32 %2, %14
    %16 = const u32 0
    %17 = icmp ne u32 %3, %16
    store bool %11, ptr %9
    %18 = const i64 1
    %19 = gep i8, ptr %9, %18
    store bool %13, ptr %19
    %20 = const i64 2
    %21 = gep i8, ptr %9, %20
    store bool %15, ptr %21
    %22 = const i64 3
    %23 = gep i8, ptr %9, %22
    store bool %17, ptr %23
    %24 = call @func.1(%9)
    br bb1(%4, %24)
bb1(%5: ptr, %6: bool):
    %25 = const u32 1
    %26 = const u32 0
    %27 = select u32 %6, %25, %26
    store u32 %27, ptr %5
    %28 = call @func.2(%9)
    br bb2(%5, %28)
bb2(%7: ptr, %8: u8):
    %29 = zext u8 %8 to u32
    %30 = const i64 4
    %31 = gep i8, ptr %7, %30
    store u32 %29, ptr %31
    ret
}

fn @RexPrefix__is_needed(functy.1) {
bb0(%0: ptr):
    %2 = load bool, ptr %0
    condbr %2, bb3, bb1
bb1:
    %3 = const i64 1
    %4 = gep i8, ptr %0, %3
    %5 = load bool, ptr %4
    condbr %5, bb3, bb2
bb2:
    %6 = const i64 2
    %7 = gep i8, ptr %0, %6
    %8 = load bool, ptr %7
    condbr %8, bb3, bb4
bb3:
    %9 = const bool true
    br bb5(%9)
bb4:
    %10 = const i64 3
    %11 = gep i8, ptr %0, %10
    %12 = load bool, ptr %11
    br bb5(%12)
bb5(%1: bool):
    ret %1
}

fn @RexPrefix__encode(functy.2) {
bb0(%0: ptr):
    %9 = const u8 64
    %10 = load bool, ptr %0
    condbr %10, bb1(%9), bb2(%9)
bb1(%1: u8):
    %11 = const u8 8
    %12 = or u8 %1, %11
    br bb2(%12)
bb2(%2: u8):
    %13 = const i64 1
    %14 = gep i8, ptr %0, %13
    %15 = load bool, ptr %14
    condbr %15, bb3(%2), bb4(%2)
bb3(%3: u8):
    %16 = const u8 4
    %17 = or u8 %3, %16
    br bb4(%17)
bb4(%4: u8):
    %18 = const i64 2
    %19 = gep i8, ptr %0, %18
    %20 = load bool, ptr %19
    condbr %20, bb5(%4), bb6(%4)
bb5(%5: u8):
    %21 = const u8 2
    %22 = or u8 %5, %21
    br bb6(%22)
bb6(%6: u8):
    %23 = const i64 3
    %24 = gep i8, ptr %0, %23
    %25 = load bool, ptr %24
    condbr %25, bb7(%6), bb8(%6)
bb7(%7: u8):
    %26 = const u8 1
    %27 = or u8 %7, %26
    br bb8(%27)
bb8(%8: u8):
    ret %8
}
"#;

/// VERBATIM MIR-closure emit of `x86_modrm_root`. ModRM 5-ctor family + encode; slice trust_x86_encoder_slice.rs.
/// Emit: 4410 bytes; 7 member(s); validate_module = 0 error(s); re-parse OK; EXTERN-FREE.
const X86_MODRM_IR: &str = r#"; TrustIr text format v1
module "mir::closure::x86_modrm_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_x86_encoder_slice.rs"

functy.0 = (u32, u32, u32, u32) -> (u32)

functy.1 = (ptr, u8, u8) -> ()

functy.2 = (ptr, u8, u8) -> ()

functy.3 = (ptr, u8, u8) -> ()

functy.4 = (ptr, u8, u8) -> ()

functy.5 = (ptr, u8, u8) -> ()

functy.6 = (ptr) -> (u8)

fn @x86_modrm_root(functy.0) {
bb0(%0: u32, %1: u32, %2: u32, %3: u32):
    %20 = alloca (i8, i8, i8), align 1
    %21 = alloca (i8, i8, i8), align 1
    switch %0 [ 0: bb7(%1, %2) 1: bb6(%1, %2) 2: bb5(%1, %2) 3: bb4(%1, %2) 4: bb3(%1, %2) 5: bb2(%1, %2, %3) default: bb1(%1, %2) ]
bb1(%4: u32, %5: u32):
    %22 = trunc u32 %4 to u8
    %23 = trunc u32 %5 to u8
    call @func.1(%20, %22, %23)
    br bb8
bb2(%6: u32, %7: u32, %8: u32):
    %24 = trunc u32 %6 to u8
    %25 = trunc u32 %7 to u8
    %26 = trunc u32 %8 to u8
    store u8 %24, ptr %20
    %27 = const i64 1
    %28 = gep i8, ptr %20, %27
    store u8 %25, ptr %28
    %29 = const i64 2
    %30 = gep i8, ptr %20, %29
    store u8 %26, ptr %30
    br bb8
bb3(%9: u32, %10: u32):
    %31 = trunc u32 %9 to u8
    %32 = trunc u32 %10 to u8
    call @func.2(%20, %31, %32)
    br bb8
bb4(%11: u32, %12: u32):
    %33 = trunc u32 %11 to u8
    %34 = trunc u32 %12 to u8
    call @func.3(%20, %33, %34)
    br bb8
bb5(%13: u32, %14: u32):
    %35 = trunc u32 %13 to u8
    %36 = trunc u32 %14 to u8
    call @func.4(%20, %35, %36)
    br bb8
bb6(%15: u32, %16: u32):
    %37 = trunc u32 %15 to u8
    %38 = trunc u32 %16 to u8
    call @func.5(%20, %37, %38)
    br bb8
bb7(%17: u32, %18: u32):
    %39 = trunc u32 %17 to u8
    %40 = trunc u32 %18 to u8
    call @func.1(%20, %39, %40)
    br bb8
bb8:
    %41 = load i8, ptr %20
    store i8 %41, ptr %21
    %42 = const i64 1
    %43 = gep i8, ptr %20, %42
    %44 = const i64 1
    %45 = gep i8, ptr %21, %44
    %46 = load i8, ptr %43
    store i8 %46, ptr %45
    %47 = const i64 2
    %48 = gep i8, ptr %20, %47
    %49 = const i64 2
    %50 = gep i8, ptr %21, %49
    %51 = load i8, ptr %48
    store i8 %51, ptr %50
    %52 = call @func.6(%21)
    br bb9(%52)
bb9(%19: u8):
    %53 = zext u8 %19 to u32
    ret %53
}

fn @ModRM__reg_reg(functy.1) {
bb0(%0: ptr, %1: u8, %2: u8):
    %3 = const u8 7
    %4 = and u8 %1, %3
    %5 = const u8 7
    %6 = and u8 %2, %5
    %7 = const u8 3
    store u8 %7, ptr %0
    %8 = const i64 1
    %9 = gep i8, ptr %0, %8
    store u8 %4, ptr %9
    %10 = const i64 2
    %11 = gep i8, ptr %0, %10
    store u8 %6, ptr %11
    ret
}

fn @ModRM__indirect_disp32(functy.2) {
bb0(%0: ptr, %1: u8, %2: u8):
    %3 = const u8 7
    %4 = and u8 %1, %3
    %5 = const u8 7
    %6 = and u8 %2, %5
    %7 = const u8 2
    store u8 %7, ptr %0
    %8 = const i64 1
    %9 = gep i8, ptr %0, %8
    store u8 %4, ptr %9
    %10 = const i64 2
    %11 = gep i8, ptr %0, %10
    store u8 %6, ptr %11
    ret
}

fn @ModRM__indirect_disp8(functy.3) {
bb0(%0: ptr, %1: u8, %2: u8):
    %3 = const u8 7
    %4 = and u8 %1, %3
    %5 = const u8 7
    %6 = and u8 %2, %5
    %7 = const u8 1
    store u8 %7, ptr %0
    %8 = const i64 1
    %9 = gep i8, ptr %0, %8
    store u8 %4, ptr %9
    %10 = const i64 2
    %11 = gep i8, ptr %0, %10
    store u8 %6, ptr %11
    ret
}

fn @ModRM__indirect(functy.4) {
bb0(%0: ptr, %1: u8, %2: u8):
    %3 = const u8 7
    %4 = and u8 %1, %3
    %5 = const u8 7
    %6 = and u8 %2, %5
    %7 = const u8 0
    store u8 %7, ptr %0
    %8 = const i64 1
    %9 = gep i8, ptr %0, %8
    store u8 %4, ptr %9
    %10 = const i64 2
    %11 = gep i8, ptr %0, %10
    store u8 %6, ptr %11
    ret
}

fn @ModRM__ext_reg(functy.5) {
bb0(%0: ptr, %1: u8, %2: u8):
    %3 = const u8 7
    %4 = and u8 %1, %3
    %5 = const u8 7
    %6 = and u8 %2, %5
    %7 = const u8 3
    store u8 %7, ptr %0
    %8 = const i64 1
    %9 = gep i8, ptr %0, %8
    store u8 %4, ptr %9
    %10 = const i64 2
    %11 = gep i8, ptr %0, %10
    store u8 %6, ptr %11
    ret
}

fn @ModRM__encode(functy.6) {
bb0(%0: ptr):
    %1 = load u8, ptr %0
    %2 = const i32 6
    %3 = trunc i32 %2 to u8
    %4 = shl u8 %1, %3
    %5 = const i64 1
    %6 = gep i8, ptr %0, %5
    %7 = load u8, ptr %6
    %8 = const i32 3
    %9 = trunc i32 %8 to u8
    %10 = shl u8 %7, %9
    %11 = or u8 %4, %10
    %12 = const i64 2
    %13 = gep i8, ptr %0, %12
    %14 = load u8, ptr %13
    %15 = or u8 %11, %14
    ret %15
}
"#;

/// VERBATIM MIR-closure emit of `x86_sib_root`. Sib base_only/scaled + encode; slice trust_x86_encoder_slice.rs.
/// Emit: 3192 bytes; 4 member(s); validate_module = 0 error(s); re-parse OK; EXTERN-FREE.
const X86_SIB_IR: &str = r#"; TrustIr text format v1
module "mir::closure::x86_sib_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_x86_encoder_slice.rs"

functy.0 = (u32, u32, u32, u32) -> (u32)

functy.1 = (ptr, u8, u8, u8) -> ()

functy.2 = (ptr, u8) -> ()

functy.3 = (ptr) -> (u8)

fn @x86_sib_root(functy.0) {
bb0(%0: u32, %1: u32, %2: u32, %3: u32):
    %12 = alloca (i8, i8, i8), align 1
    %13 = alloca (i8, i8, i8), align 1
    switch %0 [ 0: bb3(%1) 2: bb2(%1, %2, %3) default: bb1(%1, %2, %3) ]
bb1(%4: u32, %5: u32, %6: u32):
    %14 = trunc u32 %4 to u8
    %15 = trunc u32 %5 to u8
    %16 = trunc u32 %6 to u8
    call @func.1(%12, %14, %15, %16)
    br bb4
bb2(%7: u32, %8: u32, %9: u32):
    %17 = trunc u32 %7 to u8
    %18 = trunc u32 %8 to u8
    %19 = trunc u32 %9 to u8
    store u8 %17, ptr %12
    %20 = const i64 1
    %21 = gep i8, ptr %12, %20
    store u8 %18, ptr %21
    %22 = const i64 2
    %23 = gep i8, ptr %12, %22
    store u8 %19, ptr %23
    br bb4
bb3(%10: u32):
    %24 = trunc u32 %10 to u8
    call @func.2(%12, %24)
    br bb4
bb4:
    %25 = load i8, ptr %12
    store i8 %25, ptr %13
    %26 = const i64 1
    %27 = gep i8, ptr %12, %26
    %28 = const i64 1
    %29 = gep i8, ptr %13, %28
    %30 = load i8, ptr %27
    store i8 %30, ptr %29
    %31 = const i64 2
    %32 = gep i8, ptr %12, %31
    %33 = const i64 2
    %34 = gep i8, ptr %13, %33
    %35 = load i8, ptr %32
    store i8 %35, ptr %34
    %36 = call @func.3(%13)
    br bb5(%36)
bb5(%11: u8):
    %37 = zext u8 %11 to u32
    ret %37
}

fn @Sib__scaled(functy.1) {
bb0(%0: ptr, %1: u8, %2: u8, %3: u8):
    switch %3 [ 1: bb5(%1, %2) 2: bb4(%1, %2) 4: bb3(%1, %2) 8: bb2(%1, %2) default: bb1(%1, %2) ]
bb1(%4: u8, %5: u8):
    %17 = const u8 0
    br bb6(%4, %5, %17)
bb2(%6: u8, %7: u8):
    %18 = const u8 3
    br bb6(%6, %7, %18)
bb3(%8: u8, %9: u8):
    %19 = const u8 2
    br bb6(%8, %9, %19)
bb4(%10: u8, %11: u8):
    %20 = const u8 1
    br bb6(%10, %11, %20)
bb5(%12: u8, %13: u8):
    %21 = const u8 0
    br bb6(%12, %13, %21)
bb6(%14: u8, %15: u8, %16: u8):
    %22 = const u8 7
    %23 = and u8 %15, %22
    %24 = const u8 7
    %25 = and u8 %14, %24
    store u8 %16, ptr %0
    %26 = const i64 1
    %27 = gep i8, ptr %0, %26
    store u8 %23, ptr %27
    %28 = const i64 2
    %29 = gep i8, ptr %0, %28
    store u8 %25, ptr %29
    ret
}

fn @Sib__base_only(functy.2) {
bb0(%0: ptr, %1: u8):
    %2 = const u8 7
    %3 = and u8 %1, %2
    %4 = const u8 0
    store u8 %4, ptr %0
    %5 = const u8 4
    %6 = const i64 1
    %7 = gep i8, ptr %0, %6
    store u8 %5, ptr %7
    %8 = const i64 2
    %9 = gep i8, ptr %0, %8
    store u8 %3, ptr %9
    ret
}

fn @Sib__encode(functy.3) {
bb0(%0: ptr):
    %1 = load u8, ptr %0
    %2 = const i32 6
    %3 = trunc i32 %2 to u8
    %4 = shl u8 %1, %3
    %5 = const i64 1
    %6 = gep i8, ptr %0, %5
    %7 = load u8, ptr %6
    %8 = const u8 7
    %9 = and u8 %7, %8
    %10 = const i32 3
    %11 = trunc i32 %10 to u8
    %12 = shl u8 %9, %11
    %13 = or u8 %4, %12
    %14 = const i64 2
    %15 = gep i8, ptr %0, %14
    %16 = load u8, ptr %15
    %17 = const u8 7
    %18 = and u8 %16, %17
    %19 = or u8 %13, %18
    ret %19
}
"#;

/// VERBATIM MIR-closure emit of `x86_require_disp32_root`. require_disp32 range gate ([B1] bool); slice trust_x86_encoder_slice.rs.
/// Emit: 807 bytes; 2 member(s); validate_module = 0 error(s); re-parse OK; EXTERN-FREE.
const X86_DISP32_IR: &str = r#"; TrustIr text format v1
module "mir::closure::x86_require_disp32_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_x86_encoder_slice.rs"

functy.0 = (i64) -> (u32)

functy.1 = (i64) -> (bool)

fn @x86_require_disp32_root(functy.0) {
bb0(%0: i64):
    %2 = call @func.1(%0)
    br bb1(%2)
bb1(%1: bool):
    %3 = const u32 1
    %4 = const u32 0
    %5 = select u32 %1, %3, %4
    ret %5
}

fn @require_disp32(functy.1) {
bb0(%0: i64):
    %3 = const i32 -2147483648
    %4 = sext i32 %3 to i64
    %5 = icmp slt i64 %0, %4
    condbr %5, bb2, bb1(%0)
bb1(%1: i64):
    %6 = const i32 2147483647
    %7 = sext i32 %6 to i64
    %8 = icmp sgt i64 %1, %7
    condbr %8, bb2, bb3
bb2:
    %9 = const bool false
    br bb4(%9)
bb3:
    %10 = const bool true
    br bb4(%10)
bb4(%2: bool):
    ret %2
}
"#;

/// VERBATIM MIR-closure emit of `x86_regprops_root`. x86 register-file scalar props; slice trust_x86_regfile_slice.rs.
/// Emit: 17099 bytes; 14 member(s); validate_module = 0 error(s); re-parse OK; EXTERN-FREE.
const X86_REGPROPS_IR: &str = r#"; TrustIr text format v1
module "mir::closure::x86_regprops_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_x86_regfile_slice.rs"

functy.0 = (u16, ptr) -> ()

functy.1 = (ptr, u16) -> ()

functy.2 = (ptr, u16) -> ()

functy.3 = (u8) -> (u32)

functy.4 = (u16) -> (u8)

functy.5 = (u16) -> (bool)

functy.6 = (u16) -> (bool)

functy.7 = (u16) -> (bool)

functy.8 = (u16) -> (bool)

functy.9 = (u16) -> (bool)

functy.10 = (ptr, u16) -> ()

functy.11 = (u8) -> (u32)

functy.12 = (u8) -> (u32)

functy.13 = (u16) -> (u16)

fn @x86_regprops_root(functy.0) {
bb0(%0: u16, %1: ptr):
    %26 = alloca i16, align 2
    %27 = alloca i8, align 1
    %28 = alloca (i8, i8), align 1
    call @func.1(%26, %0)
    br bb1(%1)
bb1(%2: ptr):
    %29 = load u16, ptr %26
    call @func.2(%27, %29)
    br bb2(%2)
bb2(%3: ptr):
    %30 = load u8, ptr %27
    %31 = call @func.3(%30)
    br bb3(%3, %31)
bb3(%4: ptr, %5: u32):
    store u32 %5, ptr %4
    %32 = load u16, ptr %26
    %33 = call @func.4(%32)
    br bb4(%4, %33)
bb4(%6: ptr, %7: u8):
    %34 = zext u8 %7 to u32
    %35 = const i64 4
    %36 = gep i8, ptr %6, %35
    store u32 %34, ptr %36
    %37 = load u16, ptr %26
    %38 = call @func.5(%37)
    br bb5(%6, %38)
bb5(%8: ptr, %9: bool):
    %39 = const u32 1
    %40 = const u32 0
    %41 = select u32 %9, %39, %40
    %42 = const i64 8
    %43 = gep i8, ptr %8, %42
    store u32 %41, ptr %43
    %44 = load u16, ptr %26
    %45 = call @func.6(%44)
    br bb6(%8, %45)
bb6(%10: ptr, %11: bool):
    %46 = const u32 1
    %47 = const u32 0
    %48 = select u32 %11, %46, %47
    %49 = const i64 12
    %50 = gep i8, ptr %10, %49
    store u32 %48, ptr %50
    %51 = load u16, ptr %26
    %52 = call @func.7(%51)
    br bb7(%10, %52)
bb7(%12: ptr, %13: bool):
    %53 = const u32 1
    %54 = const u32 0
    %55 = select u32 %13, %53, %54
    %56 = const i64 16
    %57 = gep i8, ptr %12, %56
    store u32 %55, ptr %57
    %58 = load u16, ptr %26
    %59 = call @func.8(%58)
    br bb8(%12, %59)
bb8(%14: ptr, %15: bool):
    %60 = const u32 1
    %61 = const u32 0
    %62 = select u32 %15, %60, %61
    %63 = const i64 20
    %64 = gep i8, ptr %14, %63
    store u32 %62, ptr %64
    %65 = load u16, ptr %26
    %66 = call @func.9(%65)
    br bb9(%14, %66)
bb9(%16: ptr, %17: bool):
    %67 = const u32 1
    %68 = const u32 0
    %69 = select u32 %17, %67, %68
    %70 = const i64 24
    %71 = gep i8, ptr %16, %70
    store u32 %69, ptr %71
    %72 = load u16, ptr %26
    call @func.10(%28, %72)
    br bb10(%16)
bb10(%18: ptr):
    %73 = load i8, ptr %28
    %74 = sext i8 %73 to i64
    switch %74 [ 0: bb12(%18) 1: bb13(%18) default: bb11 ]
bb11:
    unreachable
bb12(%19: ptr):
    %75 = const u32 0
    %76 = const i64 28
    %77 = gep i8, ptr %19, %76
    store u32 %75, ptr %77
    %78 = const u32 0
    %79 = const i64 32
    %80 = gep i8, ptr %19, %79
    store u32 %78, ptr %80
    br bb14(%19)
bb13(%20: ptr):
    %81 = const i64 1
    %82 = gep i8, ptr %28, %81
    %83 = load u8, ptr %82
    %84 = const u32 1
    %85 = const i64 28
    %86 = gep i8, ptr %20, %85
    store u32 %84, ptr %86
    %87 = zext u8 %83 to u32
    %88 = const i64 32
    %89 = gep i8, ptr %20, %88
    store u32 %87, ptr %89
    br bb14(%20)
bb14(%21: ptr):
    %90 = load u8, ptr %27
    %91 = call @func.11(%90)
    br bb15(%21, %91)
bb15(%22: ptr, %23: u32):
    %92 = const i64 36
    %93 = gep i8, ptr %22, %92
    store u32 %23, ptr %93
    %94 = load u8, ptr %27
    %95 = call @func.12(%94)
    br bb16(%22, %95)
bb16(%24: ptr, %25: u32):
    %96 = const i64 40
    %97 = gep i8, ptr %24, %96
    store u32 %25, ptr %97
    ret
}

fn @X86PReg__new(functy.1) {
bb0(%0: ptr, %1: u16):
    store u16 %1, ptr %0
    ret
}

fn @x86_preg_class(functy.2) {
bb0(%0: ptr, %1: u16):
    %14 = alloca i16, align 2
    store u16 %1, ptr %14
    %15 = load u16, ptr %14
    %16 = call @func.13(%15)
    br bb1(%16)
bb1(%2: u16):
    %17 = const u16 0
    %18 = icmp ule u16 %17, %2
    condbr %18, bb19(%2), bb4(%2)
bb2:
    %19 = const i8 5
    store i8 %19, ptr %0
    br bb20
bb3:
    %20 = const i8 0
    store i8 %20, ptr %0
    br bb20
bb4(%3: u16):
    %21 = const u16 16
    %22 = icmp ule u16 %21, %3
    condbr %22, bb18(%3), bb6(%3)
bb5:
    %23 = const i8 1
    store i8 %23, ptr %0
    br bb20
bb6(%4: u16):
    %24 = const u16 32
    %25 = icmp ule u16 %24, %4
    condbr %25, bb17(%4), bb8(%4)
bb7:
    %26 = const i8 2
    store i8 %26, ptr %0
    br bb20
bb8(%5: u16):
    %27 = const u16 48
    %28 = icmp ule u16 %27, %5
    condbr %28, bb16(%5), bb10(%5)
bb9:
    %29 = const i8 3
    store i8 %29, ptr %0
    br bb20
bb10(%6: u16):
    %30 = const u16 64
    %31 = icmp ule u16 %30, %6
    condbr %31, bb15(%6), bb12(%6)
bb11:
    %32 = const i8 4
    store i8 %32, ptr %0
    br bb20
bb12(%7: u16):
    %33 = const u16 80
    %34 = icmp ule u16 %33, %7
    condbr %34, bb14(%7), bb2
bb13:
    %35 = const i8 5
    store i8 %35, ptr %0
    br bb20
bb14(%8: u16):
    %36 = const u16 81
    %37 = icmp ule u16 %8, %36
    condbr %37, bb13, bb2
bb15(%9: u16):
    %38 = const u16 79
    %39 = icmp ule u16 %9, %38
    condbr %39, bb11, bb12(%9)
bb16(%10: u16):
    %40 = const u16 63
    %41 = icmp ule u16 %10, %40
    condbr %41, bb9, bb10(%10)
bb17(%11: u16):
    %42 = const u16 47
    %43 = icmp ule u16 %11, %42
    condbr %43, bb7, bb8(%11)
bb18(%12: u16):
    %44 = const u16 31
    %45 = icmp ule u16 %12, %44
    condbr %45, bb5, bb6(%12)
bb19(%13: u16):
    %46 = const u16 15
    %47 = icmp ule u16 %13, %46
    condbr %47, bb3, bb4(%13)
bb20:
    ret
}

fn @class_tag(functy.3) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 0: bb7 1: bb6 2: bb5 3: bb4 4: bb3 5: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %5 = const u32 5
    br bb8(%5)
bb3:
    %6 = const u32 4
    br bb8(%6)
bb4:
    %7 = const u32 3
    br bb8(%7)
bb5:
    %8 = const u32 2
    br bb8(%8)
bb6:
    %9 = const u32 1
    br bb8(%9)
bb7:
    %10 = const u32 0
    br bb8(%10)
bb8(%1: u32):
    ret %1
}

fn @x86_hw_encoding(functy.4) {
bb0(%0: u16):
    %17 = alloca i16, align 2
    store u16 %0, ptr %17
    %18 = load u16, ptr %17
    %19 = call @func.13(%18)
    br bb1(%19)
bb1(%1: u16):
    %20 = const u16 0
    %21 = icmp ule u16 %20, %1
    condbr %21, bb16(%1), bb4(%1)
bb2:
    %22 = const u8 0
    br bb17(%22)
bb3(%2: u16):
    %23 = trunc u16 %2 to u8
    br bb17(%23)
bb4(%3: u16):
    %24 = const u16 16
    %25 = icmp ule u16 %24, %3
    condbr %25, bb15(%3), bb6(%3)
bb5(%4: u16):
    %26 = const u16 16
    %27 = sub u16 %4, %26
    %28 = trunc u16 %27 to u8
    br bb17(%28)
bb6(%5: u16):
    %29 = const u16 32
    %30 = icmp ule u16 %29, %5
    condbr %30, bb14(%5), bb8(%5)
bb7(%6: u16):
    %31 = const u16 32
    %32 = sub u16 %6, %31
    %33 = trunc u16 %32 to u8
    br bb17(%33)
bb8(%7: u16):
    %34 = const u16 48
    %35 = icmp ule u16 %34, %7
    condbr %35, bb13(%7), bb10(%7)
bb9(%8: u16):
    %36 = const u16 48
    %37 = sub u16 %8, %36
    %38 = trunc u16 %37 to u8
    br bb17(%38)
bb10(%9: u16):
    %39 = const u16 64
    %40 = icmp ule u16 %39, %9
    condbr %40, bb12(%9), bb2
bb11(%10: u16):
    %41 = const u16 64
    %42 = sub u16 %10, %41
    %43 = trunc u16 %42 to u8
    br bb17(%43)
bb12(%11: u16):
    %44 = const u16 79
    %45 = icmp ule u16 %11, %44
    condbr %45, bb11(%11), bb2
bb13(%12: u16):
    %46 = const u16 63
    %47 = icmp ule u16 %12, %46
    condbr %47, bb9(%12), bb10(%12)
bb14(%13: u16):
    %48 = const u16 47
    %49 = icmp ule u16 %13, %48
    condbr %49, bb7(%13), bb8(%13)
bb15(%14: u16):
    %50 = const u16 31
    %51 = icmp ule u16 %14, %50
    condbr %51, bb5(%14), bb6(%14)
bb16(%15: u16):
    %52 = const u16 15
    %53 = icmp ule u16 %15, %52
    condbr %53, bb3(%15), bb4(%15)
bb17(%16: u8):
    ret %16
}

fn @X86PReg__needs_rex(functy.5) {
bb0(%0: u16):
    %11 = alloca i16, align 2
    store u16 %0, ptr %11
    %12 = load u16, ptr %11
    %13 = const u16 8
    %14 = icmp ule u16 %13, %12
    condbr %14, bb15(%12), bb3(%12)
bb1:
    %15 = const bool false
    br bb16(%15)
bb2:
    %16 = const bool true
    br bb16(%16)
bb3(%1: u16):
    %17 = const u16 24
    %18 = icmp ule u16 %17, %1
    condbr %18, bb14(%1), bb5(%1)
bb4:
    %19 = const bool true
    br bb16(%19)
bb5(%2: u16):
    %20 = const u16 40
    %21 = icmp ule u16 %20, %2
    condbr %21, bb13(%2), bb7(%2)
bb6:
    %22 = const bool true
    br bb16(%22)
bb7(%3: u16):
    %23 = const u16 52
    %24 = icmp ule u16 %23, %3
    condbr %24, bb12(%3), bb9(%3)
bb8:
    %25 = const bool true
    br bb16(%25)
bb9(%4: u16):
    %26 = const u16 72
    %27 = icmp ule u16 %26, %4
    condbr %27, bb11(%4), bb1
bb10:
    %28 = const bool true
    br bb16(%28)
bb11(%5: u16):
    %29 = const u16 79
    %30 = icmp ule u16 %5, %29
    condbr %30, bb10, bb1
bb12(%6: u16):
    %31 = const u16 63
    %32 = icmp ule u16 %6, %31
    condbr %32, bb8, bb9(%6)
bb13(%7: u16):
    %33 = const u16 47
    %34 = icmp ule u16 %7, %33
    condbr %34, bb6, bb7(%7)
bb14(%8: u16):
    %35 = const u16 31
    %36 = icmp ule u16 %8, %35
    condbr %36, bb4, bb5(%8)
bb15(%9: u16):
    %37 = const u16 15
    %38 = icmp ule u16 %9, %37
    condbr %38, bb2, bb3(%9)
bb16(%10: bool):
    ret %10
}

fn @x86_is_callee_saved(functy.6) {
bb0(%0: u16):
    %11 = alloca i16, align 2
    store u16 %0, ptr %11
    %12 = load u16, ptr %11
    %13 = call @func.13(%12)
    br bb1(%13)
bb1(%1: u16):
    switch %1 [ 3: bb14 5: bb14 19: bb13 21: bb13 35: bb12 37: bb12 51: bb11 53: bb11 default: bb3(%1) ]
bb2:
    %14 = const bool false
    br bb15(%14)
bb3(%2: u16):
    %15 = const u16 12
    %16 = icmp ule u16 %15, %2
    condbr %16, bb10(%2), bb4(%2)
bb4(%3: u16):
    %17 = const u16 28
    %18 = icmp ule u16 %17, %3
    condbr %18, bb9(%3), bb5(%3)
bb5(%4: u16):
    %19 = const u16 44
    %20 = icmp ule u16 %19, %4
    condbr %20, bb8(%4), bb6(%4)
bb6(%5: u16):
    %21 = const u16 60
    %22 = icmp ule u16 %21, %5
    condbr %22, bb7(%5), bb2
bb7(%6: u16):
    %23 = const u16 63
    %24 = icmp ule u16 %6, %23
    condbr %24, bb11, bb2
bb8(%7: u16):
    %25 = const u16 47
    %26 = icmp ule u16 %7, %25
    condbr %26, bb12, bb6(%7)
bb9(%8: u16):
    %27 = const u16 31
    %28 = icmp ule u16 %8, %27
    condbr %28, bb13, bb5(%8)
bb10(%9: u16):
    %29 = const u16 15
    %30 = icmp ule u16 %9, %29
    condbr %30, bb14, bb4(%9)
bb11:
    %31 = const bool true
    br bb15(%31)
bb12:
    %32 = const bool true
    br bb15(%32)
bb13:
    %33 = const bool true
    br bb15(%33)
bb14:
    %34 = const bool true
    br bb15(%34)
bb15(%10: bool):
    ret %10
}

fn @x86_is_caller_saved(functy.7) {
bb0(%0: u16):
    %20 = alloca i16, align 2
    store u16 %0, ptr %20
    %21 = load u16, ptr %20
    %22 = call @func.13(%21)
    br bb1(%22)
bb1(%1: u16):
    %23 = const u16 0
    %24 = icmp ule u16 %23, %1
    condbr %24, bb20(%1), bb3(%1)
bb2:
    %25 = const bool false
    br bb25(%25)
bb3(%2: u16):
    %26 = const u16 6
    %27 = icmp ule u16 %26, %2
    condbr %27, bb19(%2), bb4(%2)
bb4(%3: u16):
    %28 = const u16 16
    %29 = icmp ule u16 %28, %3
    condbr %29, bb18(%3), bb5(%3)
bb5(%4: u16):
    %30 = const u16 22
    %31 = icmp ule u16 %30, %4
    condbr %31, bb17(%4), bb6(%4)
bb6(%5: u16):
    %32 = const u16 32
    %33 = icmp ule u16 %32, %5
    condbr %33, bb16(%5), bb7(%5)
bb7(%6: u16):
    %34 = const u16 38
    %35 = icmp ule u16 %34, %6
    condbr %35, bb15(%6), bb8(%6)
bb8(%7: u16):
    %36 = const u16 48
    %37 = icmp ule u16 %36, %7
    condbr %37, bb14(%7), bb9(%7)
bb9(%8: u16):
    %38 = const u16 54
    %39 = icmp ule u16 %38, %8
    condbr %39, bb13(%8), bb10(%8)
bb10(%9: u16):
    %40 = const u16 64
    %41 = icmp ule u16 %40, %9
    condbr %41, bb12(%9), bb2
bb11:
    %42 = const bool true
    br bb25(%42)
bb12(%10: u16):
    %43 = const u16 79
    %44 = icmp ule u16 %10, %43
    condbr %44, bb11, bb2
bb13(%11: u16):
    %45 = const u16 59
    %46 = icmp ule u16 %11, %45
    condbr %46, bb21, bb10(%11)
bb14(%12: u16):
    %47 = const u16 50
    %48 = icmp ule u16 %12, %47
    condbr %48, bb21, bb9(%12)
bb15(%13: u16):
    %49 = const u16 43
    %50 = icmp ule u16 %13, %49
    condbr %50, bb22, bb8(%13)
bb16(%14: u16):
    %51 = const u16 34
    %52 = icmp ule u16 %14, %51
    condbr %52, bb22, bb7(%14)
bb17(%15: u16):
    %53 = const u16 27
    %54 = icmp ule u16 %15, %53
    condbr %54, bb23, bb6(%15)
bb18(%16: u16):
    %55 = const u16 18
    %56 = icmp ule u16 %16, %55
    condbr %56, bb23, bb5(%16)
bb19(%17: u16):
    %57 = const u16 11
    %58 = icmp ule u16 %17, %57
    condbr %58, bb24, bb4(%17)
bb20(%18: u16):
    %59 = const u16 2
    %60 = icmp ule u16 %18, %59
    condbr %60, bb24, bb3(%18)
bb21:
    %61 = const bool true
    br bb25(%61)
bb22:
    %62 = const bool true
    br bb25(%62)
bb23:
    %63 = const bool true
    br bb25(%63)
bb24:
    %64 = const bool true
    br bb25(%64)
bb25(%19: bool):
    ret %19
}

fn @X86PReg__is_gpr(functy.8) {
bb0(%0: u16):
    %1 = alloca i16, align 2
    store u16 %0, ptr %1
    %2 = load u16, ptr %1
    %3 = const u16 63
    %4 = icmp ule u16 %2, %3
    ret %4
}

fn @X86PReg__is_xmm(functy.9) {
bb0(%0: u16):
    %2 = alloca i16, align 2
    store u16 %0, ptr %2
    %3 = load u16, ptr %2
    %4 = const u16 64
    %5 = icmp uge u16 %3, %4
    condbr %5, bb1, bb2
bb1:
    %6 = load u16, ptr %2
    %7 = const u16 79
    %8 = icmp ule u16 %6, %7
    br bb3(%8)
bb2:
    %9 = const bool false
    br bb3(%9)
bb3(%1: bool):
    ret %1
}

fn @x86_reg_number(functy.10) {
bb0(%0: ptr, %1: u16):
    %17 = alloca i16, align 2
    store u16 %1, ptr %17
    %18 = load u16, ptr %17
    %19 = call @func.13(%18)
    br bb1(%19)
bb1(%2: u16):
    %20 = const u16 0
    %21 = icmp ule u16 %20, %2
    condbr %21, bb16(%2), bb4(%2)
bb2:
    %22 = const i8 0
    store i8 %22, ptr %0
    br bb17
bb3(%3: u16):
    %23 = trunc u16 %3 to u8
    %24 = const i64 1
    %25 = gep i8, ptr %0, %24
    store u8 %23, ptr %25
    %26 = const i8 1
    store i8 %26, ptr %0
    br bb17
bb4(%4: u16):
    %27 = const u16 16
    %28 = icmp ule u16 %27, %4
    condbr %28, bb15(%4), bb6(%4)
bb5(%5: u16):
    %29 = const u16 16
    %30 = sub u16 %5, %29
    %31 = trunc u16 %30 to u8
    %32 = const i64 1
    %33 = gep i8, ptr %0, %32
    store u8 %31, ptr %33
    %34 = const i8 1
    store i8 %34, ptr %0
    br bb17
bb6(%6: u16):
    %35 = const u16 32
    %36 = icmp ule u16 %35, %6
    condbr %36, bb14(%6), bb8(%6)
bb7(%7: u16):
    %37 = const u16 32
    %38 = sub u16 %7, %37
    %39 = trunc u16 %38 to u8
    %40 = const i64 1
    %41 = gep i8, ptr %0, %40
    store u8 %39, ptr %41
    %42 = const i8 1
    store i8 %42, ptr %0
    br bb17
bb8(%8: u16):
    %43 = const u16 48
    %44 = icmp ule u16 %43, %8
    condbr %44, bb13(%8), bb10(%8)
bb9(%9: u16):
    %45 = const u16 48
    %46 = sub u16 %9, %45
    %47 = trunc u16 %46 to u8
    %48 = const i64 1
    %49 = gep i8, ptr %0, %48
    store u8 %47, ptr %49
    %50 = const i8 1
    store i8 %50, ptr %0
    br bb17
bb10(%10: u16):
    %51 = const u16 64
    %52 = icmp ule u16 %51, %10
    condbr %52, bb12(%10), bb2
bb11(%11: u16):
    %53 = const u16 64
    %54 = sub u16 %11, %53
    %55 = trunc u16 %54 to u8
    %56 = const i64 1
    %57 = gep i8, ptr %0, %56
    store u8 %55, ptr %57
    %58 = const i8 1
    store i8 %58, ptr %0
    br bb17
bb12(%12: u16):
    %59 = const u16 79
    %60 = icmp ule u16 %12, %59
    condbr %60, bb11(%12), bb2
bb13(%13: u16):
    %61 = const u16 63
    %62 = icmp ule u16 %13, %61
    condbr %62, bb9(%13), bb10(%13)
bb14(%14: u16):
    %63 = const u16 47
    %64 = icmp ule u16 %14, %63
    condbr %64, bb7(%14), bb8(%14)
bb15(%15: u16):
    %65 = const u16 31
    %66 = icmp ule u16 %15, %65
    condbr %66, bb5(%15), bb6(%15)
bb16(%16: u16):
    %67 = const u16 15
    %68 = icmp ule u16 %16, %67
    condbr %68, bb3(%16), bb4(%16)
bb17:
    ret
}

fn @X86RegClass__size_bits(functy.11) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 0: bb7 1: bb6 2: bb5 3: bb4 4: bb3 5: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %5 = const u32 64
    br bb8(%5)
bb3:
    %6 = const u32 128
    br bb8(%6)
bb4:
    %7 = const u32 8
    br bb8(%7)
bb5:
    %8 = const u32 16
    br bb8(%8)
bb6:
    %9 = const u32 32
    br bb8(%9)
bb7:
    %10 = const u32 64
    br bb8(%10)
bb8(%1: u32):
    ret %1
}

fn @X86RegClass__size_bytes(functy.12) {
bb0(%0: u8):
    %3 = alloca i8, align 1
    store u8 %0, ptr %3
    %4 = load u8, ptr %3
    %5 = call @func.11(%4)
    br bb1(%5)
bb1(%1: u32):
    %6 = const u32 8
    %7 = const u32 0
    %8 = icmp eq u32 %6, %7
    %9 = const bool false
    %10 = icmp eq bool %8, %9
    condbr %10, bb2(%1), bb3
bb2(%2: u32):
    %11 = const u32 8
    %12 = udiv u32 %2, %11
    ret %12
bb3:
    unreachable
}

fn @X86PReg__encoding(functy.13) {
bb0(%0: u16):
    %1 = alloca i16, align 2
    store u16 %0, ptr %1
    %2 = load u16, ptr %1
    ret %2
}
"#;

/// VERBATIM MIR-closure emit of `x86_regoverlap_root`. x86_regs_overlap; slice trust_x86_regfile_slice.rs.
/// Emit: 7539 bytes; 6 member(s); validate_module = 0 error(s); re-parse OK; EXTERN-FREE.
const X86_REGOVERLAP_IR: &str = r#"; TrustIr text format v1
module "mir::closure::x86_regoverlap_root"
target "aarch64-apple-darwin" 8 little
file 0 "trust_x86_regfile_slice.rs"

functy.0 = (u16, u16) -> (u32)

functy.1 = (ptr, u16) -> ()

functy.2 = (u16, u16) -> (bool)

functy.3 = (ptr, ptr) -> (bool)

functy.4 = (ptr, u16) -> ()

functy.5 = (u16) -> (u16)

fn @x86_regoverlap_root(functy.0) {
bb0(%0: u16, %1: u16):
    %4 = alloca i16, align 2
    %5 = alloca i16, align 2
    call @func.1(%4, %0)
    br bb1(%1)
bb1(%2: u16):
    call @func.1(%5, %2)
    br bb2
bb2:
    %6 = load u16, ptr %4
    %7 = load u16, ptr %5
    %8 = call @func.2(%6, %7)
    br bb3(%8)
bb3(%3: bool):
    %9 = const u32 1
    %10 = const u32 0
    %11 = select u32 %3, %9, %10
    ret %11
}

fn @X86PReg__new(functy.1) {
bb0(%0: ptr, %1: u16):
    store u16 %1, ptr %0
    ret
}

fn @x86_regs_overlap(functy.2) {
bb0(%0: u16, %1: u16):
    %6 = alloca i16, align 2
    %7 = alloca i16, align 2
    %8 = alloca (i8, i8, i8), align 1
    %9 = alloca (i8, i8, i8), align 1
    %10 = alloca (i8, i8, i8, i8, i8, i8), align 1
    store u16 %0, ptr %6
    store u16 %1, ptr %7
    %11 = call @func.3(%6, %7)
    br bb1(%11)
bb1(%2: bool):
    condbr %2, bb2, bb3
bb2:
    %12 = const bool true
    br bb11(%12)
bb3:
    %13 = load u16, ptr %6
    call @func.4(%8, %13)
    br bb4
bb4:
    %14 = load u16, ptr %7
    call @func.4(%9, %14)
    br bb5
bb5:
    %15 = load i8, ptr %8
    store i8 %15, ptr %10
    %16 = const i64 1
    %17 = gep i8, ptr %8, %16
    %18 = const i64 1
    %19 = gep i8, ptr %10, %18
    %20 = load i8, ptr %17
    store i8 %20, ptr %19
    %21 = const i64 2
    %22 = gep i8, ptr %8, %21
    %23 = const i64 2
    %24 = gep i8, ptr %10, %23
    %25 = load i8, ptr %22
    store i8 %25, ptr %24
    %26 = const i64 3
    %27 = gep i8, ptr %10, %26
    %28 = load i8, ptr %9
    store i8 %28, ptr %27
    %29 = const i64 1
    %30 = gep i8, ptr %9, %29
    %31 = const i64 1
    %32 = gep i8, ptr %27, %31
    %33 = load i8, ptr %30
    store i8 %33, ptr %32
    %34 = const i64 2
    %35 = gep i8, ptr %9, %34
    %36 = const i64 2
    %37 = gep i8, ptr %27, %36
    %38 = load i8, ptr %35
    store i8 %38, ptr %37
    %39 = load i8, ptr %10
    %40 = sext i8 %39 to i64
    switch %40 [ 1: bb7 0: bb6 default: bb12 ]
bb6:
    %41 = const bool false
    br bb11(%41)
bb7:
    %42 = const i64 3
    %43 = gep i8, ptr %10, %42
    %44 = load i8, ptr %43
    %45 = sext i8 %44 to i64
    switch %45 [ 1: bb8 0: bb6 default: bb12 ]
bb8:
    %46 = const i64 1
    %47 = gep i8, ptr %10, %46
    %48 = load u8, ptr %47
    %49 = const i64 2
    %50 = gep i8, ptr %10, %49
    %51 = load u8, ptr %50
    %52 = const i64 4
    %53 = gep i8, ptr %10, %52
    %54 = load u8, ptr %53
    %55 = const i64 5
    %56 = gep i8, ptr %10, %55
    %57 = load u8, ptr %56
    %58 = icmp eq u8 %48, %54
    condbr %58, bb9(%51, %57), bb10
bb9(%3: u8, %4: u8):
    %59 = icmp eq u8 %3, %4
    br bb11(%59)
bb10:
    %60 = const bool false
    br bb11(%60)
bb11(%5: bool):
    ret %5
bb12:
    unreachable
}

fn @_X86PReg_as_std__cmp__PartialEq___eq(functy.3) {
bb0(%0: ptr, %1: ptr):
    %2 = load u16, ptr %0
    %3 = load u16, ptr %1
    %4 = icmp eq u16 %2, %3
    ret %4
}

fn @x86_reg_root(functy.4) {
bb0(%0: ptr, %1: u16):
    %17 = alloca i16, align 2
    %18 = alloca (i8, i8), align 1
    %19 = alloca (i8, i8), align 1
    %20 = alloca (i8, i8), align 1
    %21 = alloca (i8, i8), align 1
    %22 = alloca (i8, i8), align 1
    store u16 %1, ptr %17
    %23 = load u16, ptr %17
    %24 = call @func.5(%23)
    br bb1(%24)
bb1(%2: u16):
    %25 = const u16 0
    %26 = icmp ule u16 %25, %2
    condbr %26, bb16(%2), bb4(%2)
bb2:
    %27 = const i8 0
    store i8 %27, ptr %0
    br bb17
bb3(%3: u16):
    %28 = trunc u16 %3 to u8
    store u8 %28, ptr %18
    %29 = const u8 0
    %30 = const i64 1
    %31 = gep i8, ptr %18, %30
    store u8 %29, ptr %31
    %32 = const i64 1
    %33 = gep i8, ptr %0, %32
    %34 = load i8, ptr %18
    store i8 %34, ptr %33
    %35 = const i64 1
    %36 = gep i8, ptr %18, %35
    %37 = const i64 1
    %38 = gep i8, ptr %33, %37
    %39 = load i8, ptr %36
    store i8 %39, ptr %38
    %40 = const i8 1
    store i8 %40, ptr %0
    br bb17
bb4(%4: u16):
    %41 = const u16 16
    %42 = icmp ule u16 %41, %4
    condbr %42, bb15(%4), bb6(%4)
bb5(%5: u16):
    %43 = const u16 16
    %44 = sub u16 %5, %43
    %45 = trunc u16 %44 to u8
    store u8 %45, ptr %19
    %46 = const u8 0
    %47 = const i64 1
    %48 = gep i8, ptr %19, %47
    store u8 %46, ptr %48
    %49 = const i64 1
    %50 = gep i8, ptr %0, %49
    %51 = load i8, ptr %19
    store i8 %51, ptr %50
    %52 = const i64 1
    %53 = gep i8, ptr %19, %52
    %54 = const i64 1
    %55 = gep i8, ptr %50, %54
    %56 = load i8, ptr %53
    store i8 %56, ptr %55
    %57 = const i8 1
    store i8 %57, ptr %0
    br bb17
bb6(%6: u16):
    %58 = const u16 32
    %59 = icmp ule u16 %58, %6
    condbr %59, bb14(%6), bb8(%6)
bb7(%7: u16):
    %60 = const u16 32
    %61 = sub u16 %7, %60
    %62 = trunc u16 %61 to u8
    store u8 %62, ptr %20
    %63 = const u8 0
    %64 = const i64 1
    %65 = gep i8, ptr %20, %64
    store u8 %63, ptr %65
    %66 = const i64 1
    %67 = gep i8, ptr %0, %66
    %68 = load i8, ptr %20
    store i8 %68, ptr %67
    %69 = const i64 1
    %70 = gep i8, ptr %20, %69
    %71 = const i64 1
    %72 = gep i8, ptr %67, %71
    %73 = load i8, ptr %70
    store i8 %73, ptr %72
    %74 = const i8 1
    store i8 %74, ptr %0
    br bb17
bb8(%8: u16):
    %75 = const u16 48
    %76 = icmp ule u16 %75, %8
    condbr %76, bb13(%8), bb10(%8)
bb9(%9: u16):
    %77 = const u16 48
    %78 = sub u16 %9, %77
    %79 = trunc u16 %78 to u8
    store u8 %79, ptr %21
    %80 = const u8 0
    %81 = const i64 1
    %82 = gep i8, ptr %21, %81
    store u8 %80, ptr %82
    %83 = const i64 1
    %84 = gep i8, ptr %0, %83
    %85 = load i8, ptr %21
    store i8 %85, ptr %84
    %86 = const i64 1
    %87 = gep i8, ptr %21, %86
    %88 = const i64 1
    %89 = gep i8, ptr %84, %88
    %90 = load i8, ptr %87
    store i8 %90, ptr %89
    %91 = const i8 1
    store i8 %91, ptr %0
    br bb17
bb10(%10: u16):
    %92 = const u16 64
    %93 = icmp ule u16 %92, %10
    condbr %93, bb12(%10), bb2
bb11(%11: u16):
    %94 = const u16 64
    %95 = sub u16 %11, %94
    %96 = trunc u16 %95 to u8
    store u8 %96, ptr %22
    %97 = const u8 1
    %98 = const i64 1
    %99 = gep i8, ptr %22, %98
    store u8 %97, ptr %99
    %100 = const i64 1
    %101 = gep i8, ptr %0, %100
    %102 = load i8, ptr %22
    store i8 %102, ptr %101
    %103 = const i64 1
    %104 = gep i8, ptr %22, %103
    %105 = const i64 1
    %106 = gep i8, ptr %101, %105
    %107 = load i8, ptr %104
    store i8 %107, ptr %106
    %108 = const i8 1
    store i8 %108, ptr %0
    br bb17
bb12(%12: u16):
    %109 = const u16 79
    %110 = icmp ule u16 %12, %109
    condbr %110, bb11(%12), bb2
bb13(%13: u16):
    %111 = const u16 63
    %112 = icmp ule u16 %13, %111
    condbr %112, bb9(%13), bb10(%13)
bb14(%14: u16):
    %113 = const u16 47
    %114 = icmp ule u16 %14, %113
    condbr %114, bb7(%14), bb8(%14)
bb15(%15: u16):
    %115 = const u16 31
    %116 = icmp ule u16 %15, %115
    condbr %116, bb5(%15), bb6(%15)
bb16(%16: u16):
    %117 = const u16 15
    %118 = icmp ule u16 %16, %117
    condbr %118, bb3(%16), bb4(%16)
bb17:
    ret
}

fn @X86PReg__encoding(functy.5) {
bb0(%0: u16):
    %1 = alloca i16, align 2
    store u16 %0, ptr %1
    %2 = load u16, ptr %1
    ret %2
}
"#;
