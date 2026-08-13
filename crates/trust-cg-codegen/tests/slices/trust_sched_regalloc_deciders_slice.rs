// Trust-toolchain slice — the SCHEDULER MAY-ALIAS + REGALLOC SCALAR DECIDER
// layer, transcribed VERBATIM from three crates:
//   * trust-cg/crates/trust-cg-opt/src/scheduler.rs
//       `byte_ranges_overlap`  (403-421)  — the static may-alias / memory-
//                                            disjointness decider used to drop
//                                            store->load ordering edges;
//       `port_capacity`        (1740-1749)— per-port execution-unit count;
//       `ExecutionPort`        (76-90)    — the port enum.
//   * trust-cg/crates/trust-cg-regalloc/src/liveness.rs
//       `LiveRange`            (23-46)    — { start, end } + overlaps/contains;
//       `merge_vreg_class`     (552-567)  — the reg-class-compatibility join.
//   * trust-cg/crates/trust-cg-regalloc/src/spill.rs
//       `reg_class_size`       (128-139)  — class -> spill-slot byte size.
//   * trust-cg/crates/trust-cg-ir/src/aarch64_regs.rs
//       `RegClass`             (96-115)   — the 8-variant class enum;
//       `RegClass::size_bits/size_bytes` (117-137).
// working tree @ (see report).
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 22, TRUST
// BATCH 9, part 1 of 2 — the REGALLOC + SCHEDULER decider surface, a NEW area:
// rounds 1/7/16 did encoders, 5/16 the register FILES (regs_overlap), 20/21
// the opt/analysis category+addr-mode predicates. The scheduler's may-alias
// decider and the regalloc interference/class-join deciders were UNTOUCHED).
//
// WHY SOUNDNESS-CRITICAL: these deciders gate correctness-affecting choices:
//   * `byte_ranges_overlap` decides whether two static memory byte-ranges are
//     PROVABLY disjoint; a false "disjoint" (returns false when they DO
//     overlap) lets the scheduler drop the store->load ordering edge and
//     REORDER a store past a load that reads the same bytes — an UNSOUND
//     memory-ordering miscompile. It is deliberately CONSERVATIVE: any
//     unknown/overflow/degenerate case returns `true` (= "assume overlap").
//   * `LiveRange::overlaps` is the live-range INTERFERENCE primitive; a false
//     "no overlap" for two ranges that DO overlap lets two simultaneously-live
//     vregs share one physical register — a clobber miscompile. Endpoints are
//     where it hides: adjacent ranges [a,b)+[b,c) must NOT overlap (half-open).
//   * `merge_vreg_class` is the class-compatibility JOIN used when coalescing
//     merges two vregs' classes; a wrong join assigns a value to a register
//     class that cannot hold it.
//   * `reg_class_size` sizes the spill slot; too-small a slot corrupts the
//     spilled value's neighbours.
//
// EMIT: stage1 `trust_ir_mir --mir-emit-closure deciders_root` per the README
// recipe; `-C overflow-checks=off -C debug-assertions=off`.
//
// MODELED BOUNDARIES:
//   [B1] `RegClass` / `ExecutionPort` are fed to the root as u32 tags and
//        reconstructed by the total `reg_class_from_tag` / `port_from_tag`
//        (declaration-order enum<->tag plumbing, round-5/7/16 pattern); the
//        transcribed predicates themselves are UNMODIFIED. Merged class and
//        port are returned as u32 tags.
//   [B2] `LiveRange` is constructed via the struct literal `LiveRange{start,
//        end}` (NOT `LiveRange::new`) so the sweep can drive degenerate/empty
//        ranges (start>=end) that `new`'s `debug_assert!(start<end)` would
//        reject; `overlaps`/`contains` never call `new`, so this is faithful
//        to the deciders under test. The dual oracle links the production
//        `LiveRange` (also via struct literal).
//   [B3] The private fns (`byte_ranges_overlap`, `merge_vreg_class`,
//        `reg_class_size`) have no linked oracle; they are cross-checked
//        against a verbatim NATIVE transcription in the harness. The PUBLIC
//        fns (`LiveRange::overlaps`/`contains`, `port_capacity`,
//        `size_bits`/`size_bytes`) are LINKED (true dual oracle). `reg_class_size`
//        is additionally cross-checked to equal production `RegClass::size_bytes`.
//   [B4] FRONTEND FINDING (F4 / owner-#6 class, NEW instance): production
//        `byte_ranges_overlap` uses `i64::checked_add`, but `--mir-emit-closure`
//        lowers `core::num::<i64>::checked_add` to an EMPTY-BODIED extern leaf
//        (it is a core-library method, not crate-local, so its body is not
//        pulled) -> `Jit(UnresolvedSymbol)`. Transcribed here as the
//        RESULT-IDENTICAL pure-i64 high-side overflow check: after the
//        `left_size<=0 || right_size<=0` guard both sizes are strictly
//        positive, so `x + size` can only overflow on the HIGH side, i.e.
//        `checked_add(x,size) == None  <=>  x > i64::MAX - size`. The native
//        oracle in the harness runs the REAL `checked_add` form VERBATIM, so
//        native==JIT proves the rewrite equivalent across the overflow
//        endpoints. REPORTED as a frontend finding.

// ── ExecutionPort (scheduler.rs:76-90, VERBATIM) ─────────────────────────────
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ExecutionPort {
    IntAlu,
    IntMul,
    IntDiv,
    LoadStore,
    Branch,
    FpAlu,
}

// ── RegClass (aarch64_regs.rs:96-138, VERBATIM) ──────────────────────────────
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

impl RegClass {
    /// aarch64_regs.rs:119-131, VERBATIM
    #[inline]
    pub const fn size_bits(self) -> u32 {
        match self {
            Self::Gpr64 => 64,
            Self::Gpr32 => 32,
            Self::Fpr128 => 128,
            Self::Fpr64 => 64,
            Self::Fpr32 => 32,
            Self::Fpr16 => 16,
            Self::Fpr8 => 8,
            Self::System => 32,
        }
    }

    /// aarch64_regs.rs:134-137, VERBATIM
    #[inline]
    pub const fn size_bytes(self) -> u32 {
        self.size_bits() / 8
    }
}

// ── LiveRange (liveness.rs:23-46, VERBATIM) ──────────────────────────────────
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiveRange {
    pub start: u32,
    pub end: u32,
}

impl LiveRange {
    /// liveness.rs:37-40, VERBATIM
    pub fn contains(&self, idx: u32) -> bool {
        self.start <= idx && idx < self.end
    }

    /// liveness.rs:42-45, VERBATIM
    pub fn overlaps(&self, other: &LiveRange) -> bool {
        self.start < other.end && other.start < self.end
    }
}

// ── byte_ranges_overlap (scheduler.rs:403-421; [B4] checked_add rewrite) ──────
fn byte_ranges_overlap(
    left_offset: i64,
    left_size: i64,
    right_offset: i64,
    right_size: i64,
) -> bool {
    if left_size <= 0 || right_size <= 0 {
        return true;
    }

    // [B4] `left_offset.checked_add(left_size)` == None  <=>  high overflow
    // (left_size>0 here), i.e. left_offset > i64::MAX - left_size.
    if left_offset > i64::MAX - left_size {
        return true;
    }
    if right_offset > i64::MAX - right_size {
        return true;
    }
    let left_end = left_offset + left_size;
    let right_end = right_offset + right_size;

    left_offset < right_end && right_offset < left_end
}

// ── merge_vreg_class (liveness.rs:552-567, VERBATIM) ─────────────────────────
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

// ── reg_class_size (spill.rs:128-139, VERBATIM) ──────────────────────────────
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

// ── port_capacity (scheduler.rs:1740-1749, VERBATIM) ─────────────────────────
fn port_capacity(port: ExecutionPort) -> u32 {
    match port {
        ExecutionPort::IntAlu => 6,
        ExecutionPort::IntMul => 2,
        ExecutionPort::IntDiv => 1,
        ExecutionPort::LoadStore => 2,
        ExecutionPort::Branch => 1,
        ExecutionPort::FpAlu => 4,
    }
}

// ── [B1] tag plumbing ────────────────────────────────────────────────────────

fn reg_class_from_tag(tag: u32) -> RegClass {
    use RegClass::*;
    match tag {
        0 => Gpr64,
        1 => Gpr32,
        2 => Fpr128,
        3 => Fpr64,
        4 => Fpr32,
        5 => Fpr16,
        6 => Fpr8,
        _ => System,
    }
}

fn reg_class_tag(rc: RegClass) -> u32 {
    match rc {
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

fn port_from_tag(tag: u32) -> ExecutionPort {
    use ExecutionPort::*;
    match tag {
        0 => IntAlu,
        1 => IntMul,
        2 => IntDiv,
        3 => LoadStore,
        4 => Branch,
        _ => FpAlu,
    }
}

// ── out-POD + #[no_mangle] mono ROOT ─────────────────────────────────────────

/// POD decider vector for one input tuple.
#[repr(C)]
pub struct DecidersOut {
    pub byte_overlap: u32,
    pub lr_overlap: u32,
    pub lr_contains: u32,
    pub merged_class_tag: u32,
    pub reg_class_size: u32,
    pub size_bits: u32,
    pub size_bytes: u32,
    pub port_capacity: u32,
}

/// ROOT: the scheduler-may-alias + regalloc-scalar decider vector.
///
/// Input mapping (one call exercises every decider):
///   byte_ranges_overlap(a, b, c, d)   [i64]
///   LiveRange{a,b}.overlaps(&{c,d})   [u32]   (a=start,b=end,c=o.start,d=o.end)
///   LiveRange{a,b}.contains(c)        [u32]   (a=start,b=end,c=idx)
///   merge_vreg_class(rc1, rc2)
///   reg_class_size(rc1) / rc1.size_bits() / rc1.size_bytes()
///   port_capacity(port)
#[no_mangle]
pub fn deciders_root(a: i64, b: i64, c: i64, d: i64, rc1: u32, rc2: u32, port: u32, out: &mut DecidersOut) {
    out.byte_overlap = byte_ranges_overlap(a, b, c, d) as u32;

    let ua = a as u32;
    let ub = b as u32;
    let uc = c as u32;
    let ud = d as u32;
    out.lr_overlap = (LiveRange { start: ua, end: ub }).overlaps(&LiveRange { start: uc, end: ud }) as u32;
    out.lr_contains = (LiveRange { start: ua, end: ub }).contains(uc) as u32;

    let r1 = reg_class_from_tag(rc1);
    let r2 = reg_class_from_tag(rc2);
    out.merged_class_tag = reg_class_tag(merge_vreg_class(r1, r2));
    out.reg_class_size = reg_class_size(r1);
    out.size_bits = r1.size_bits();
    out.size_bytes = r1.size_bytes();

    out.port_capacity = port_capacity(port_from_tag(port));
}
