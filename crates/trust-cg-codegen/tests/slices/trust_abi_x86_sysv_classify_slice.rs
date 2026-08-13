// Trust-toolchain slice — the x86-64 SYSTEM V AMD64 psABI aggregate
// CLASSIFICATION deciders, transcribed VERBATIM from
//   trust-cg/crates/trust-cg-lower/src/x86_64_isel.rs
//   trust-cg/crates/trust-cg-lower/src/types.rs (`Type::bytes`)
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 23, TRUST
// BATCH 10, part 2 of 2 — the x86-64 SysV ABI classification surface, companion
// to part 1 (AArch64). These are the psABI §3.2.3 deciders that assign a
// by-value aggregate to INTEGER/SSE eightbyte classes and decide
// register-vs-MEMORY / sret passing.
//
// WHY SOUNDNESS-CRITICAL: a wrong SysV classification is a WRONG CALL — a field
// placed in the wrong register class (GPR vs XMM) or a struct passed in
// registers when the psABI requires MEMORY (stack / sret):
//   * `sysv_scalar_leaf_class` — integer/bool -> INTEGER, float -> SSE.
//   * `merge_sysv_eightbyte_class` — INTEGER wins; SSE only if all-SSE.
//   * `sysv_eightbyte_lane_type` — width-correct GPR/XMM lane access; only
//     power-of-two 1/2/4/8 widths (3/5/6/7-byte tails fail closed).
//   * the sret / MEMORY size deciders — THE "exact size at which a struct goes
//     to memory": SysV >16 -> MEMORY/sret; WindowsX64 return >8.
//   * `eightbyte_count` — how many eightbytes a size occupies (the 2-eightbyte
//     register limit).
//
// EMIT: stage1 `trust_ir_mir --mir-emit-closure abi_x86_root` per the README
// recipe (NO extra flags; EXTERN-FREE; re-emits byte-identical).
//
// SCOPE — the size deciders are SCALAR-DRIVEN (Vec<Type> recursion blocker):
//   The full aggregate walk (`classify_sysv_register_aggregate`,
//   `collect_sysv_aggregate_leaves`) and `ty.bytes()` on Struct/Array recurse
//   over `Vec<Type>`/`Box<Type>`, whose library methods lower to empty-bodied
//   leaves the in-process JIT cannot resolve (F4 / owner-#6; see the AArch64
//   slice header). So the SIZE-based sret/MEMORY deciders are transcribed
//   taking the scalar `size` (production computes it via `ty.bytes()`) and the
//   `is_aggregate` gate as a bool [B-aggsize] — the THRESHOLD COMPARISONS
//   (`> 16`, `> 8`) + the SysV-only gate are VERBATIM the production bodies.
//   The native oracle computes size + is_aggregate from REAL aggregate `Type`s
//   via the LINKED production `Type::bytes`, so native==JIT proves the JIT's
//   threshold decisions correct at the exact 8 / 16 / 17 / 24 byte boundaries.
//   The leaf-class / merge / lane / eightbyte-count deciders operate on scalars
//   and are transcribed FULLY VERBATIM.
//
// MODELED BOUNDARIES:
//   [B3] these classifiers are PRIVATE `fn` in x86_64_isel.rs (not linkable);
//        transcribed VERBATIM and cross-checked against a verbatim native
//        transcription + independent hand-computed boundary values. Class/type
//        enums decode to scalar tags: LaneClass Integer=0 Sse=1 None=9; lane
//        Type tag I8=0 I16=1 I32=2 I64=3 F32=6 F64=7 None=99. `Type::bytes` +
//        `X86CallAbi` (both public) ARE linked as a partial second oracle.
//   [F1] production `is_sysv_memory_byval_aggregate` writes `abi ==
//        X86CallAbi::SystemV`; the fieldless-enum `==` does not lower
//        ("constant value not a single scalar", F1/owner-#6). Transcribed as
//        `matches!(abi, X86CallAbi::SystemV)` (result-identical); the native
//        oracle runs the REAL `==` form.
//   [B-scalaronly] the sliced `Type` (for leaf-class) carries only scalar
//        variants; leaf_class's `_ => None` arm covers the aggregate + I128 +
//        V128 shapes exactly as production does for those inputs.

// ── Type (types.rs scalar variants; aggregate variants elided [B-scalaronly]) ──
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Type {
    I8,
    I16,
    I32,
    I64,
    I128,
    F16,
    F32,
    F64,
    B1,
    V128,
}
impl Type {
    pub fn bytes(&self) -> u32 {
        match self {
            Type::B1 | Type::I8 => 1,
            Type::I16 | Type::F16 => 2,
            Type::I32 | Type::F32 => 4,
            Type::I64 | Type::F64 => 8,
            Type::I128 | Type::V128 => 16,
        }
    }
}

// ── X86CallAbi (x86_64_isel.rs:607-612, VERBATIM) ─────────────────────────────
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum X86CallAbi {
    SystemV,
    WindowsX64,
}

// ── X86SysVAggregateLaneClass (x86_64_isel.rs:250-254, VERBATIM) ──────────────
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum X86SysVAggregateLaneClass {
    Integer,
    Sse,
}

// ── sysv_scalar_leaf_class (x86_64_isel.rs:297-305, VERBATIM scalar arms) ──────
fn sysv_scalar_leaf_class(ty: &Type) -> Option<X86SysVAggregateLaneClass> {
    match ty {
        Type::B1 | Type::I8 | Type::I16 | Type::I32 | Type::I64 => {
            Some(X86SysVAggregateLaneClass::Integer)
        }
        Type::F16 | Type::F32 | Type::F64 => Some(X86SysVAggregateLaneClass::Sse),
        _ => None,
    }
}

// ── merge_sysv_eightbyte_class (x86_64_isel.rs:310-323, VERBATIM) ──────────────
fn merge_sysv_eightbyte_class(
    acc: &mut Option<X86SysVAggregateLaneClass>,
    leaf: X86SysVAggregateLaneClass,
) {
    *acc = Some(match (*acc, leaf) {
        (None, c) => c,
        (Some(X86SysVAggregateLaneClass::Integer), _) | (_, X86SysVAggregateLaneClass::Integer) => {
            X86SysVAggregateLaneClass::Integer
        }
        (Some(X86SysVAggregateLaneClass::Sse), X86SysVAggregateLaneClass::Sse) => {
            X86SysVAggregateLaneClass::Sse
        }
    });
}

// ── sysv_eightbyte_lane_type (x86_64_isel.rs:417-427, VERBATIM) ────────────────
fn sysv_eightbyte_lane_type(class: X86SysVAggregateLaneClass, valid_bytes: u32) -> Option<Type> {
    match (class, valid_bytes) {
        (X86SysVAggregateLaneClass::Integer, 8) => Some(Type::I64),
        (X86SysVAggregateLaneClass::Integer, 4) => Some(Type::I32),
        (X86SysVAggregateLaneClass::Integer, 2) => Some(Type::I16),
        (X86SysVAggregateLaneClass::Integer, 1) => Some(Type::I8),
        (X86SysVAggregateLaneClass::Sse, 8) => Some(Type::F64),
        (X86SysVAggregateLaneClass::Sse, 4) => Some(Type::F32),
        _ => None,
    }
}

// ── eightbyte_count (x86_64_isel.rs:270-272; [B-from] i64::from -> `as i64`) ───
// production returns `i64::from((self.size + 7) / 8)`; `i64::from(u32)` lowers to
// an empty `From::from` library leaf the JIT cannot resolve, so the widening is
// transcribed as the result-identical `as i64` (u32 -> i64 is always exact).
fn eightbyte_count(size: u32) -> i64 {
    ((size + 7) / 8) as i64
}

// ── size deciders (x86_64_isel.rs:200-230; scalar size + is_agg gate [B-aggsize]) ─
// The THRESHOLD comparisons + SysV-only gate are VERBATIM; `ty.bytes()` and the
// `matches!(ty, Struct|Array|Enum)` aggregate gate are supplied by the caller.
fn is_large_x86_sret_by_size(is_aggregate: bool, size: u32) -> bool {
    is_aggregate && size > 16
}
fn is_sysv_memory_byval_by_size(is_aggregate: bool, abi: X86CallAbi, size: u32) -> bool {
    matches!(abi, X86CallAbi::SystemV) && is_aggregate && size > 16
}
fn is_x86_sret_return_by_size(is_aggregate: bool, abi: X86CallAbi, size: u32) -> bool {
    match abi {
        X86CallAbi::SystemV => is_large_x86_sret_by_size(is_aggregate, size),
        X86CallAbi::WindowsX64 => is_aggregate && size > 8,
    }
}

// ── plumbing ──────────────────────────────────────────────────────────────────
fn build_type(tag: u32) -> Type {
    match tag {
        0 => Type::I8,
        1 => Type::I16,
        2 => Type::I32,
        3 => Type::I64,
        4 => Type::I128,
        5 => Type::F16,
        6 => Type::F32,
        7 => Type::F64,
        8 => Type::B1,
        _ => Type::V128,
    }
}
fn lc_tag(o: Option<X86SysVAggregateLaneClass>) -> u32 {
    match o {
        None => 9,
        Some(X86SysVAggregateLaneClass::Integer) => 0,
        Some(X86SysVAggregateLaneClass::Sse) => 1,
    }
}
fn lane_ty_tag(o: Option<Type>) -> u32 {
    match o {
        None => 99,
        Some(t) => match t {
            Type::I8 => 0,
            Type::I16 => 1,
            Type::I32 => 2,
            Type::I64 => 3,
            Type::F32 => 6,
            Type::F64 => 7,
            _ => 100,
        },
    }
}

// ── POD out-vector + #[no_mangle] mono ROOT ───────────────────────────────────
#[repr(C)]
pub struct AbiX86Out {
    pub leaf: u32,
    pub merged: u32,
    pub lane: u32,
    pub ebc: u32,        // eightbyte_count(size) as u32
    pub sret_large: u32, // is_large_x86_sret_by_size(is_agg, size)
    pub mem_byval: u32,  // is_sysv_memory_byval_by_size(is_agg, abi, size)
    pub sret_ret: u32,   // is_x86_sret_return_by_size(is_agg, abi, size)
}

/// ROOT: one call exercises every x86-64 SysV scalar-shaped decider.
///   leaf_tag       -> sysv_scalar_leaf_class(build_type(leaf_tag))
///   acc_tag/mleaf  -> merge_sysv_eightbyte_class
///   class_tag/valid-> sysv_eightbyte_lane_type
///   size           -> eightbyte_count + the three size deciders
///   is_agg         -> aggregate gate (0/1)
///   abi_tag        -> 0=SystemV 1=WindowsX64
#[no_mangle]
pub fn abi_x86_root(
    leaf_tag: u32,
    acc_tag: u32,
    merge_leaf_tag: u32,
    class_tag: u32,
    valid: u32,
    size: u32,
    is_agg: u32,
    abi_tag: u32,
    out: &mut AbiX86Out,
) {
    let leaf_ty = build_type(leaf_tag);
    let abi = if abi_tag == 0 {
        X86CallAbi::SystemV
    } else {
        X86CallAbi::WindowsX64
    };
    let is_aggregate = is_agg != 0;

    out.leaf = lc_tag(sysv_scalar_leaf_class(&leaf_ty));

    let mut acc: Option<X86SysVAggregateLaneClass> = match acc_tag {
        0 => Some(X86SysVAggregateLaneClass::Integer),
        1 => Some(X86SysVAggregateLaneClass::Sse),
        _ => None,
    };
    let ml = if merge_leaf_tag == 0 {
        X86SysVAggregateLaneClass::Integer
    } else {
        X86SysVAggregateLaneClass::Sse
    };
    merge_sysv_eightbyte_class(&mut acc, ml);
    out.merged = lc_tag(acc);

    let cls = if class_tag == 0 {
        X86SysVAggregateLaneClass::Integer
    } else {
        X86SysVAggregateLaneClass::Sse
    };
    out.lane = lane_ty_tag(sysv_eightbyte_lane_type(cls, valid));

    out.ebc = eightbyte_count(size) as u32;
    out.sret_large = is_large_x86_sret_by_size(is_aggregate, size) as u32;
    out.mem_byval = is_sysv_memory_byval_by_size(is_aggregate, abi, size) as u32;
    out.sret_ret = is_x86_sret_return_by_size(is_aggregate, abi, size) as u32;
}
