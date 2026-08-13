// Trust-toolchain slice — the AArch64 FIXUP BYTE-PATCH layer, transcribed
// VERBATIM from trust-cg/crates/trust-cg-codegen/src/macho/fixup.rs
//   apply_branch26  (fixup.rs:431-452)  — imm26 branch-displacement patch
//   apply_page21    (fixup.rs:469-484)  — ADRP immhi/immlo page-offset split
//   apply_pageoff12 (fixup.rs:498-526)  — pageoff12 shift-scaled 12-bit patch
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 24, TRUST BATCH
// 11 — the machine-code EMITTER / RELOCATION / FIXUP layer, the MOST
// soundness-critical codegen surface: where the final instruction-word BYTES
// are produced. A single wrong bit in a branch displacement or ADRP page split
// IS a miscompile — the branch jumps to the wrong address, the load reads the
// wrong page. These three functions patch a 32-bit instruction word with a
// PC-relative displacement after final layout.
//
// EMIT: stage1 `trust_ir_mir --mir-emit-closure fixup_patch_root` per the
// README recipe; `-C overflow-checks=off -C debug-assertions=off` (EXTERN-FREE;
// re-emits byte-identical).
//
// MODELED BOUNDARIES (the ARITHMETIC + the range/alignment DECISIONS are
// VERBATIM; only the error CARRIER + a few const spellings differ):
//   [B-errcode] production returns `Result<(), FixupError>` and mutates the
//        `&mut [u8;4]` in place on Ok only; the Err carriers use `format!`
//        (F4 gap-4: `format_args!` does not lower). Transcribed to write the
//        patched WORD + an error CODE via `&mut out`, overwriting the word only
//        on the Ok path (mirroring "instruction bytes untouched on error").
//        err: 0=ok, 1=misaligned/unaligned-assert, 2=out-of-range/<4096-assert,
//        3=scaled-field-assert. The native dual-oracle drives the REAL
//        `apply_*` (catching the pageoff12 panics) and cross-checks Ok-path
//        bytes byte-for-byte + the Ok/Err decision at every boundary.
//   [F2/contains] production writes `!(-(1<<25)..(1<<25)).contains(&word_offset)`
//        and `!(-(1<<20)..(1<<20)).contains(&page_offset)`; `Range::contains`
//        lowers to an empty library leaf (owner-#6 / F2). Transcribed to the
//        result-identical explicit comparison `x < LO || x >= HI` (a pure
//        rewrite; the native oracle runs the REAL `.contains()` form inside the
//        linked `apply_*`).
//   [F3/const-shift] the trust-ir validator requires lhs_ty == rhs_ty on binops
//        (F3: 32-bit shift consts are not type-normalized). The constant
//        boundaries `1<<25`, `1<<20`, `1<<12` are spelled as their explicit
//        typed literal values (33_554_432i64, 1_048_576i64, 4096u32) and every
//        mask/literal carries its operand's type. The single runtime shift
//        `1u32 << shift` / `page_offset >> shift` is u32<<u32 (matching); the
//        i64 `byte_offset >> 2` is the 64-bit-normalized form. Value-identical
//        to production.
//   [B-shiftu32] production `apply_pageoff12` takes `shift: u8`; transcribed as
//        `shift: u32` (the root passes it; values 0/2/3). The scale arithmetic
//        `1u32 << shift` and `page_offset >> shift` is verbatim.

// ── POD out-vector ────────────────────────────────────────────────────────────
#[repr(C)]
pub struct FixupPatchOut {
    pub patched: u32, // resulting instruction word (unchanged input on error)
    pub err: u32,     // 0=ok 1=misalign 2=range 3=scaled-overflow
}

// ── apply_branch26 (fixup.rs:431-452, VERBATIM arithmetic) ────────────────────
// Branch26 value = signed 26-bit word offset (byte_offset >> 2), bits [25:0].
fn apply_branch26_core(insn: u32, byte_offset: i64, out: &mut FixupPatchOut) {
    if byte_offset & 3i64 != 0i64 {
        // production: RelocationOverflow "Branch26 offset must be 4-byte aligned"
        out.patched = insn;
        out.err = 1u32;
        return;
    }
    let word_offset = byte_offset >> 2; // i64 ashr (64-bit normalized)
    // production: !(-(1 << 25)..(1 << 25)).contains(&word_offset)  [F2/contains]
    if word_offset < -33_554_432i64 || word_offset >= 33_554_432i64 {
        out.patched = insn;
        out.err = 2u32;
        return;
    }
    let imm26 = (word_offset as u32) & 0x03FF_FFFFu32;
    out.patched = (insn & 0xFC00_0000u32) | imm26;
    out.err = 0u32;
}

// ── apply_page21 (fixup.rs:469-484, VERBATIM arithmetic) ──────────────────────
// ADRP: immhi = bits[23:5] (19b), immlo = bits[30:29] (2b);
//        value = (immhi << 2) | immlo, sign-extended from 21 bits.
fn apply_page21_core(insn: u32, page_offset: i64, out: &mut FixupPatchOut) {
    // production: !(-(1 << 20)..(1 << 20)).contains(&page_offset)  [F2/contains]
    if page_offset < -1_048_576i64 || page_offset >= 1_048_576i64 {
        out.patched = insn;
        out.err = 2u32;
        return;
    }
    let imm21 = (page_offset as u32) & 0x001F_FFFFu32;
    let immlo = imm21 & 0x3u32;
    let immhi = (imm21 >> 2u32) & 0x0007_FFFFu32;
    out.patched = (insn & 0x9F00_001Fu32) | (immlo << 29u32) | (immhi << 5u32);
    out.err = 0u32;
}

// ── apply_pageoff12 (fixup.rs:498-526, VERBATIM arithmetic) ───────────────────
// 12-bit page offset in bits [21:10], optionally scaled by 2^shift (LDR).
fn apply_pageoff12_core(insn: u32, page_offset: u32, shift: u32, out: &mut FixupPatchOut) {
    // production: assert!(page_offset < 4096, ...)
    if page_offset >= 4096u32 {
        out.patched = insn;
        out.err = 2u32;
        return;
    }
    let scaled_offset = if shift > 0u32 {
        // production: assert!(page_offset & ((1 << shift) - 1) == 0, ...)
        if page_offset & ((1u32 << shift) - 1u32) != 0u32 {
            out.patched = insn;
            out.err = 1u32;
            return;
        }
        page_offset >> shift
    } else {
        page_offset
    };
    // production: assert!(scaled_offset < (1 << 12), ...)
    if scaled_offset >= 4096u32 {
        out.patched = insn;
        out.err = 3u32;
        return;
    }
    out.patched = (insn & 0xFFC0_03FFu32) | ((scaled_offset & 0x0FFFu32) << 10u32);
    out.err = 0u32;
}

// ── #[no_mangle] mono ROOT ────────────────────────────────────────────────────
/// ROOT: one call patches ONE instruction word.
///   which=0 -> apply_branch26_core(insn, off)
///   which=1 -> apply_page21_core(insn, off)
///   which=2 -> apply_pageoff12_core(insn, off as u32, shift)
#[no_mangle]
pub fn fixup_patch_root(insn: u32, off: i64, shift: u32, which: u32, out: &mut FixupPatchOut) {
    if which == 0u32 {
        apply_branch26_core(insn, off, out);
    } else if which == 1u32 {
        apply_page21_core(insn, off, out);
    } else {
        apply_pageoff12_core(insn, off as u32, shift, out);
    }
}
