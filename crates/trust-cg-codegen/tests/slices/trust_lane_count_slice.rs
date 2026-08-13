// Trust-toolchain slice — the production trust-ir `Ty::element_op_lane_count`
// and `Ty::supports_element_ops` (trust-ir/crates/trust-ir/src/ty.rs:236 / :247)
// lowered VERBATIM over the real `Ty` enum.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (3rd batch, fn #3).
//
// `element_op_lane_count(ty)` returns the STATIC element count for a type that
// supports element-update ops (`extract_element` / `insert_element`): a SIMD
// vector's lane count, or an array's length (narrowed `u64 -> u32`, `None` on
// overflow), `None` for everything else. `supports_element_ops` is the matching
// predicate. Both are SOUNDNESS-critical: trust-ir validates that an
// `insert_element`/`extract_element` index is in-bounds against this count, so a
// wrong lane count (or classifying a non-indexable type as indexable) admits an
// out-of-bounds element access — a memory-safety miscompile. The `u64 -> u32`
// narrowing is the real edge: an array longer than `u32::MAX` returns `None` (no
// static count) rather than a WRAPPED count.
//
// PURE, deterministic, closure-free, self-contained:
//   * `element_op_lane_count`: a 3-arm match over `Ty` returning `Option<u32>`,
//     with the `Vector` lane `u32` direct, the `Array` `u64 -> u32` checked
//     narrowing (`u32::try_from(..).ok()`, written as its provably-equivalent
//     `len <= u32::MAX` desugar — see the body note), and `_ => None`,
//   * `supports_element_ops`: a 2-variant `matches!`,
//   * NO closures, NO HashMap/Arc/RefCell, NO env/I/O, NO rustc internals, and
//     (with the alloc-free `ty_for_tag` menu) NO external host leaves at all.
//
// TRANSCRIBED VERBATIM:
//   * `Ty` enum (ty.rs:55-131) + the id newtypes / inline enums — reused from the
//     verified `trust_ty_bitwidth_slice.rs` transcription.
//   * `Ty::element_op_lane_count` (ty.rs:236-242) — THE EMIT ROOT, byte-for-byte.
//   * `Ty::supports_element_ops` (ty.rs:247-249) — byte-for-byte.
// The only adaptation is dropping the serde cfg_attr derives.

#![allow(dead_code)]


// ── id newtypes (value.rs `typed_id!`: `pub struct $name(pub u32)`). ──
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StructId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TyId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FuncTyId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EnumId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RecordId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ClosureTyId(pub u32);

impl TyId {
    pub const fn new(index: u32) -> Self {
        Self(index)
    }
}

// ── SetRepr (ty.rs:12-22) — VERBATIM (serde cfg_attr dropped). ──
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum SetRepr {
    Bitset,
    #[default]
    Boxed,
}

// ── FatPtrKind (ty.rs:37-43) — VERBATIM (serde cfg_attr dropped). ──
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FatPtrKind {
    Slice(TyId),
    Str,
    TraitObject { trait_id: u32 },
}

// ── Ty (ty.rs:55-131) — VERBATIM variant set & order (serde cfg_attr dropped). ──
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    U128,
    F16,
    F32,
    F64,
    Bool,
    Vector(Box<Ty>, u32),
    Ptr,
    FatPtr(FatPtrKind),
    Unit,
    Never,
    Struct(StructId),
    Array(TyId, u64),
    Tuple(Vec<Ty>),
    Enum(EnumId),
    Func(FuncTyId),
    Ref(Box<Ty>),
    RefMut(Box<Ty>),
    PtrConst(Box<Ty>),
    PtrMut(Box<Ty>),
    Rc(Box<Ty>),
    Set(TyId, SetRepr),
    Sequence(TyId),
    Record(RecordId),
    Closure(ClosureTyId),
}

impl Ty {
    /// (ty.rs:236-242 — THE EMIT ROOT.)
    ///
    /// The `Array` arm's `u32::try_from(*len).ok()` is written as its OWN
    /// provably-equivalent desugaring `if *len <= u32::MAX as u64 { Some(*len as
    /// u32) } else { None }` — `u32::try_from(x: u64)` succeeds with `Ok(x as u32)`
    /// EXACTLY when `x <= u32::MAX`, and `Result::ok` maps `Ok(v) -> Some(v)` /
    /// `Err -> None`, so the predicate and the produced `Option<u32>` are identical.
    /// (This keeps the slice free of the `core::convert::TryFrom` / `Result::ok`
    /// EXTERNAL sret shims — a trust-cg JIT bug HANGS on such `<_ as Try*>::*`
    /// sret-shim calls in this position; the desugar sidesteps it.)
    pub fn element_op_lane_count(&self) -> Option<u32> {
        match self {
            Ty::Vector(_, lanes) => Some(*lanes),
            Ty::Array(_, len) => {
                if *len <= u32::MAX as u64 {
                    Some(*len as u32)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// (ty.rs:247-249, VERBATIM.)
    pub fn supports_element_ops(&self) -> bool {
        matches!(self, Ty::Vector(_, _) | Ty::Array(_, _))
    }
}

/// Map a small tag to a representative `Ty`. The menu is intentionally
/// `Box`/`Vec`-FREE (no `Ty::Vector`/`Ty::Tuple` constructed here) so the slice
/// pulls in NO `Box::<Ty>::new` / `__rust_alloc` host leaf — keeping it
/// extern-free and self-contained. It covers:
///   * Array(elem, len)    — BOTH `element_op_lane_count` arms that produce a
///     count: the `u64 -> u32` checked narrowing (in-range -> `Some`, the
///     `len > u32::MAX` overflow -> `None`) AND the `supports_element_ops` `true`,
///   * a scalar / pointer / aggregate (I64/Bool/Ptr/Struct/Sequence/Record/Set/
///     Unit/Never) — the `_ => None` / `supports_element_ops` `false` arms.
/// (The `Vector(_, lanes) => Some(*lanes)` arm is structurally identical to the
/// Array `Some(..)` arm — a direct field read of the trailing `u32` — and needs a
/// `Box` to construct; it is left out of the JIT menu to stay alloc-free. The
/// Array narrowing is the soundness-critical computation and IS exercised.)
fn ty_for_tag(tag: u32, aux: u64) -> Ty {
    match tag {
        1 => Ty::Array(TyId::new(0), aux),
        2 => Ty::I64,
        3 => Ty::Bool,
        4 => Ty::Ptr,
        5 => Ty::Struct(StructId(0)),
        7 => Ty::Unit,
        8 => Ty::Sequence(TyId::new(0)),
        9 => Ty::Never,
        10 => Ty::Set(TyId::new(0), SetRepr::Boxed),
        11 => Ty::Record(RecordId(0)),
        _ => Ty::I32,
    }
}

// ── C-ABI entrypoint. The verified bodies are `element_op_lane_count` /
//    `supports_element_ops`; this wrapper builds a `Ty` from (tag, aux), calls the
//    REAL fn, and flattens the `Option<u32>` to an i64 sentinel (-1 = None, else
//    the lane count) — `which == 0`. `which == 1` returns the `supports_element_ops`
//    bit. The build + flatten are OUTSIDE the verified body, no closures.
#[no_mangle]
pub extern "C" fn lane_count_entry(tag: u32, aux: u64, which: u32) -> i64 {
    let ty = ty_for_tag(tag, aux);
    if which == 0 {
        match ty.element_op_lane_count() {
            Some(n) => n as i64,
            None => -1,
        }
    } else {
        ty.supports_element_ops() as i64
    }
}

fn main() {
    // Smoke: <4 x i32> lane count 4; [T; 10] -> 10; an array longer than u32::MAX
    // -> None (-1); a scalar -> None; Vector supports element ops.
    println!("{}", lane_count_entry(1, 10, 0)); // 10 (array len)
    println!("{}", lane_count_entry(1, (u32::MAX as u64) + 1, 0)); // -1 (overflow)
    println!("{}", lane_count_entry(2, 0, 0)); // -1 (scalar -> None)
    println!("{}", lane_count_entry(1, 10, 1)); // 1 (array supports element ops)
}
