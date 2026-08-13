// Trust-toolchain slice — the LIVENESS / INTERFERENCE predicates and the
// spill-cost & slot-size helpers of trust-cg's register allocator,
// transcribed from trust-cg/crates/trust-cg-regalloc/src/liveness.rs and
// src/spill.rs (trust-cg rev 00ae28c, re-checked against the working tree
// on 2026-07-03).
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 5:
// regalloc predicates batch, part 2 of 2).
//
// WHY SOUNDNESS-CRITICAL: these predicates DECIDE register allocation.
//   * `LiveRange::overlaps` / `LiveInterval::overlaps` are the interference
//     tests behind coalescing (coalesce.rs:132/217/491) and the greedy
//     allocator's assignment audit (greedy.rs:3281) — a false "no overlap"
//     merges two live values into one register: silent data corruption in
//     ALL code Trust compiles;
//   * `LiveInterval::is_live_at` gates call-clobber handling
//     (call_clobber.rs:143) and eviction (greedy.rs:629) — a false "dead at
//     call" lets a call clobber a live caller-saved value;
//   * `merge_vreg_class` (liveness.rs:552) collapses the register class of
//     a vreg used at several widths — a wrong merge allocates a 128-bit
//     value into a 64-bit register file;
//   * `reg_class_size` (spill.rs:129) sizes spill slots — too small and a
//     spilled Q-register store tramples the neighbouring slot;
//   * `compute_spill_weight` (liveness.rs:576) orders evictions — pure
//     performance EXCEPT that the allocators also use weight==f64::INFINITY
//     conventions upstream; we verify the arithmetic bit-exactly.
//
// TRANSCRIBED FROM:
//   * `LiveRange` struct + `contains` + `overlaps`     (liveness.rs:23-46)
//   * `LiveInterval::is_live_at`                        (liveness.rs:92-105)
//   * `LiveInterval::overlaps`                          (liveness.rs:108-133)
//   * `LiveInterval::{start,end}` (inside spill weight) (liveness.rs:82-89)
//   * `merge_vreg_class`                                (liveness.rs:552-567)
//   * `compute_spill_weight`                            (liveness.rs:576-597)
//   * `reg_class_size`                                  (spill.rs:129-139)
//   * `RegClass` (re-exported trust_cg_ir enum, VERBATIM variant order —
//     same transcription as trust_regfile_slice.rs)
//
// EMIT: stage1 `trust_ir_mir --mir-emit-closure <root>` per the README
// recipe; `-C overflow-checks=off -C debug-assertions=off` (parity with the
// other Trust-self slices; `LiveRange::new`'s debug_assert is not
// transcribed — roots construct range PODs directly from swept scalars).
//
// MODELED BOUNDARIES (each also marked at the exact line):
//   [B1] Vec<LiveRange> -> (&[LiveRange; N], len) plumbing: production
//        methods live on `LiveInterval` whose `ranges: Vec<LiveRange>`;
//        Vec construction does not lower (known frontend gap). The slice
//        fns take a FIXED-CAPACITY array reference + logical length and
//        spell `self.ranges.len()` as `len`, `self.ranges[i]` as
//        `a[i as usize]` (the static bounds check against N lowers and is
//        in-domain dead: len <= N is a harness invariant). `.first()` /
//        `.last()` become the definitional `len == 0` guard + `a[0]` /
//        `a[len-1]`. The RANGE ARITHMETIC AND SCAN STRUCTURE are verbatim.
//   [B2] `is_live_at`'s `ranges.binary_search_by(|r| ...).is_ok()` -> an
//        explicit lo/hi binary-search while-loop whose three-way compare is
//        the production closure VERBATIM (r.end <= idx -> Less/right,
//        r.start > idx -> Greater/left, else found). Result-equivalent on
//        every sorted non-overlapping list (the LiveInterval invariant,
//        liveness.rs:56); additionally cross-checked in the test against
//        the linked PRODUCTION `LiveInterval::is_live_at` as a second
//        oracle over the full sweep.
//   [B3] compute_spill_weight rewrites (each definitional, each swept):
//        - `&mut LiveInterval` field write -> return value;
//        - `use_positions.iter().chain(def_positions.iter())` -> two
//          consecutive while-loops in the SAME order (uses then defs:
//          identical f64 accumulation order => bit-identical sums);
//        - `10.0_f64.powi(loop_depth as i32)` -> a multiply loop
//          (`w *= 10.0`, loop_depth times). Exact for loop_depth <= 22
//          (10^22 is the largest exactly-representable power of ten in
//          f64; both forms then compute the exact value). The harness
//          sweeps loop_depth 0..=22 and ALSO asserts loop == powi natively
//          per row, so any divergence is loud;
//        - `inst_loop_depths.get(*pos as usize).copied().unwrap_or(0)` ->
//          the definitional explicit bounds test `if pos < depths_len`;
//        - `interval.end().saturating_sub(interval.start()).max(1)` ->
//          explicit compares (end >= start always holds for sorted
//          non-empty range lists; the explicit form is total anyway).
//   [B4] enum <-> u32 tag decoders at the roots (established convention);
//        the decoders are total (`_ =>` arm) and mirrored in the oracles.
//
// PRODUCTION LINK NOTE: `LiveRange::{contains,overlaps}`,
// `LiveInterval::{is_live_at,overlaps}` are pub and cross-checked against
// the linked trust-cg-regalloc crate in the test (dual oracle);
// `merge_vreg_class`, `compute_spill_weight`, `reg_class_size` are private
// fns — transcription fidelity is by line-cited verbatim text only.

#![allow(dead_code)]
#![allow(clippy::all)]

// ── RegClass (trust_cg_ir enum re-exported by machine_types; VERBATIM
//    variant set + order — same transcription as trust_regfile_slice.rs) ────

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum RegClass {
    Gpr64,
    Gpr32,
    Fpr128,
    Fpr64,
    Fpr32,
    Fpr16,
    Fpr8,
    System,
}

// ── LiveRange (liveness.rs:23-46) ───────────────────────────────────────────

/// liveness.rs:23-29, VERBATIM fields (derives minus Debug — diagnostic-only).
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct LiveRange {
    /// Instruction index where the live range starts (inclusive).
    pub start: u32,
    /// Instruction index where the live range ends (exclusive).
    pub end: u32,
}

impl LiveRange {
    /// liveness.rs:38-40, VERBATIM.
    pub fn contains(&self, idx: u32) -> bool {
        self.start <= idx && idx < self.end
    }

    /// liveness.rs:43-45, VERBATIM.
    pub fn overlaps(&self, other: &LiveRange) -> bool {
        self.start < other.end && other.start < self.end
    }
}

// ── LiveInterval predicates in (&[LiveRange; N], len) form [B1] ────────────

/// Fixed capacity for range lists crossing the JIT boundary ([B1]).
pub const CAP: usize = 4;

/// liveness.rs:92-105 — `LiveInterval::is_live_at`. [B1] slice plumbing;
/// [B2] binary_search_by -> explicit lo/hi loop, three-way compare VERBATIM.
pub fn interval_is_live_at(ranges: &[LiveRange; CAP], len: u32, idx: u32) -> bool {
    // `ranges` is sorted and non-overlapping, so binary search suffices.
    let mut lo: u32 = 0;
    let mut hi: u32 = len;
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        let r = &ranges[mid as usize];
        if r.end <= idx {
            // production closure: std::cmp::Ordering::Less
            lo = mid + 1;
        } else if r.start > idx {
            // production closure: std::cmp::Ordering::Greater
            hi = mid;
        } else {
            // production closure: std::cmp::Ordering::Equal -> is_ok()
            return true;
        }
    }
    false
}

/// liveness.rs:108-133 — `LiveInterval::overlaps`. [B1] slice plumbing
/// (`.first()`/`.last()` -> len-guard + a[0]/a[len-1]; `.len()` -> len);
/// the bounds fast-reject and the merge-style scan are VERBATIM.
pub fn interval_overlaps(
    a: &[LiveRange; CAP],
    a_len: u32,
    b: &[LiveRange; CAP],
    b_len: u32,
) -> bool {
    // Fast whole-interval bounds reject: most pairs don't even come close.
    // [B1] production: let (Some(a_first), Some(a_last)) = (ranges.first(), ranges.last()) else { return false };
    if a_len == 0 || b_len == 0 {
        return false;
    }
    let a_first = &a[0];
    let a_last = &a[(a_len - 1) as usize];
    let b_first = &b[0];
    let b_last = &b[(b_len - 1) as usize];
    if a_last.end <= b_first.start || b_last.end <= a_first.start {
        return false;
    }
    // Merge-style scan over the sorted, non-overlapping range lists.
    let (mut i, mut j) = (0u32, 0u32);
    while i < a_len && j < b_len {
        let (x, y) = (&a[i as usize], &b[j as usize]);
        if x.overlaps(y) {
            return true;
        }
        if x.end <= y.start {
            i += 1;
        } else {
            j += 1;
        }
    }
    false
}

// ── merge_vreg_class (liveness.rs:552-567), VERBATIM ───────────────────────

fn merge_vreg_class(lhs: RegClass, rhs: RegClass) -> RegClass {
    if lhs == rhs {
        return lhs;
    }

    use RegClass::*;
    match (lhs, rhs) {
        (Gpr64, Gpr32 | System) | (Gpr32 | System, Gpr64) => Gpr64,
        (Gpr32, System) | (System, Gpr32) => Gpr32,
        (Fpr128, Fpr64 | Fpr32 | Fpr16 | Fpr8) | (Fpr64 | Fpr32 | Fpr16 | Fpr8, Fpr128) => Fpr128,
        (Fpr64, Fpr32 | Fpr16 | Fpr8) | (Fpr32 | Fpr16 | Fpr8, Fpr64) => Fpr64,
        (Fpr32, Fpr16 | Fpr8) | (Fpr16 | Fpr8, Fpr32) => Fpr32,
        (Fpr16, Fpr8) | (Fpr8, Fpr16) => Fpr16,
        _ => lhs,
    }
}

// ── reg_class_size (spill.rs:129-139), VERBATIM ────────────────────────────

/// Returns the size in bytes for a register class.
fn reg_class_size(class: RegClass) -> u32 {
    match class {
        RegClass::Gpr32 | RegClass::Fpr32 => 4,
        RegClass::Gpr64 | RegClass::Fpr64 => 8,
        RegClass::Fpr128 => 16,
        // Smaller FPR classes: use their natural size
        RegClass::Fpr16 => 2,
        RegClass::Fpr8 => 1,
        RegClass::System => 4,
    }
}

// ── compute_spill_weight (liveness.rs:576-597) in [B1]/[B3] form ───────────

/// Capacity for the position/depth arrays crossing the boundary ([B1]).
pub const PCAP: usize = 8;
pub const DCAP: usize = 16;

/// liveness.rs:576-597. Structure VERBATIM under the [B3] rewrites
/// (documented in the header): interval fields -> explicit params, chain ->
/// two same-order loops, powi -> multiply loop, slice get -> bounds test,
/// saturating_sub/max -> explicit compares, &mut write -> return.
pub fn compute_spill_weight(
    ranges: &[LiveRange; CAP],
    ranges_len: u32,
    use_positions: &[u32; PCAP],
    uses_len: u32,
    def_positions: &[u32; PCAP],
    defs_len: u32,
    inst_loop_depths: &[u32; DCAP],
    depths_len: u32,
) -> f64 {
    if ranges_len == 0 {
        // production: interval.ranges.is_empty() -> spill_weight = 0.0
        return 0.0;
    }

    let mut weight = 0.0;

    // Accumulate weight from each use/def position.
    // [B3] production: for pos in use_positions.iter().chain(def_positions.iter())
    //      — same order (uses then defs), so the f64 sum is bit-identical.
    let mut k: u32 = 0;
    while k < uses_len {
        let pos = use_positions[k as usize];
        // [B3] production: inst_loop_depths.get(*pos as usize).copied().unwrap_or(0)
        let loop_depth = if pos < depths_len {
            inst_loop_depths[pos as usize]
        } else {
            0
        };
        // [B3] production: weight += 10.0_f64.powi(loop_depth as i32)
        let mut w = 1.0_f64;
        let mut d: u32 = 0;
        while d < loop_depth {
            w *= 10.0_f64;
            d += 1;
        }
        weight += w;
        k += 1;
    }
    let mut k: u32 = 0;
    while k < defs_len {
        let pos = def_positions[k as usize];
        let loop_depth = if pos < depths_len {
            inst_loop_depths[pos as usize]
        } else {
            0
        };
        let mut w = 1.0_f64;
        let mut d: u32 = 0;
        while d < loop_depth {
            w *= 10.0_f64;
            d += 1;
        }
        weight += w;
        k += 1;
    }

    // Normalize by interval length.
    // production: interval.end() = ranges.last().end, interval.start() =
    // ranges.first().start (non-empty here) [B1]; then
    // `end.saturating_sub(start).max(1) as f64` [B3].
    let start = ranges[0].start;
    let end = ranges[(ranges_len - 1) as usize].end;
    let diff = if end >= start { end - start } else { 0 };
    let length = (if diff < 1 { 1 } else { diff }) as f64;
    weight / length
}

// ── [B4] tag decoder (mirrored 1:1 in the test oracles) ────────────────────

fn class_from_u32(tag: u32) -> RegClass {
    match tag {
        0 => RegClass::Gpr64,
        1 => RegClass::Gpr32,
        2 => RegClass::Fpr128,
        3 => RegClass::Fpr64,
        4 => RegClass::Fpr32,
        5 => RegClass::Fpr16,
        6 => RegClass::Fpr8,
        _ => RegClass::System,
    }
}

fn class_tag(c: RegClass) -> u32 {
    match c {
        RegClass::Gpr64 => 0,
        RegClass::Gpr32 => 1,
        RegClass::Fpr128 => 2,
        RegClass::Fpr64 => 3,
        RegClass::Fpr32 => 4,
        RegClass::Fpr16 => 5,
        RegClass::Fpr8 => 6,
        RegClass::System => 7,
    }
}

// ── #[no_mangle] mono ROOTS ─────────────────────────────────────────────────
//
// Range lists cross the boundary as FLAT u32 buffers (layout-independent —
// the round-6 Num-decode lesson) and are rebuilt into LiveRange PODs
// in-module: flat[2*i] = start_i, flat[2*i+1] = end_i.

fn unflatten(flat: &[u32; 2 * CAP], out: &mut [LiveRange; CAP]) {
    let mut i: usize = 0;
    while i < CAP {
        out[i] = LiveRange {
            start: flat[2 * i],
            end: flat[2 * i + 1],
        };
        i += 1;
    }
}

/// ROOT 1: LiveRange::contains — (start, end, idx) -> bool.
#[no_mangle]
pub fn ra_lr_contains_root(start: u32, end: u32, idx: u32) -> u32 {
    let r = LiveRange { start, end };
    r.contains(idx) as u32
}

/// ROOT 2: LiveRange::overlaps — two ranges -> bool.
#[no_mangle]
pub fn ra_lr_overlaps_root(s1: u32, e1: u32, s2: u32, e2: u32) -> u32 {
    let a = LiveRange { start: s1, end: e1 };
    let b = LiveRange { start: s2, end: e2 };
    a.overlaps(&b) as u32
}

/// ROOT 3: LiveInterval::is_live_at over a flat range buffer.
#[no_mangle]
pub fn ra_iv_live_at_root(flat: &[u32; 2 * CAP], len: u32, idx: u32) -> u32 {
    let mut ranges = [LiveRange { start: 0, end: 0 }; CAP];
    unflatten(flat, &mut ranges);
    interval_is_live_at(&ranges, len, idx) as u32
}

/// ROOT 4: LiveInterval::overlaps over two flat range buffers.
#[no_mangle]
pub fn ra_iv_overlaps_root(
    a_flat: &[u32; 2 * CAP],
    a_len: u32,
    b_flat: &[u32; 2 * CAP],
    b_len: u32,
) -> u32 {
    let mut a = [LiveRange { start: 0, end: 0 }; CAP];
    let mut b = [LiveRange { start: 0, end: 0 }; CAP];
    unflatten(a_flat, &mut a);
    unflatten(b_flat, &mut b);
    interval_overlaps(&a, a_len, &b, b_len) as u32
}

/// ROOT 5: merge_vreg_class over [B4] tags.
#[no_mangle]
pub fn ra_merge_class_root(l_tag: u32, r_tag: u32) -> u32 {
    class_tag(merge_vreg_class(class_from_u32(l_tag), class_from_u32(r_tag)))
}

/// ROOT 6: reg_class_size over a [B4] tag.
#[no_mangle]
pub fn ra_slot_size_root(tag: u32) -> u32 {
    reg_class_size(class_from_u32(tag))
}

/// ROOT 7: compute_spill_weight; the f64 crosses back via out-pointer.
#[no_mangle]
pub fn ra_spill_weight_root(
    ranges_flat: &[u32; 2 * CAP],
    uses: &[u32; PCAP],
    defs: &[u32; PCAP],
    depths: &[u32; DCAP],
    lens: &[u32; 4], // [ranges_len, uses_len, defs_len, depths_len]
    out: &mut f64,
) {
    let mut ranges = [LiveRange { start: 0, end: 0 }; CAP];
    unflatten(ranges_flat, &mut ranges);
    *out = compute_spill_weight(
        &ranges, lens[0], uses, lens[1], defs, lens[2], depths, lens[3],
    );
}

fn main() {}
