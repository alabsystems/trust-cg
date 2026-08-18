// trust-cg-llvm-import / native_vector.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// NATIVE 128-bit VECTOR LOWERING (the contracted shapes only).
//
// [`crate::vector`] scalarizes EVERY vector instruction into lanes. That is
// correct for every width and it is what bought `-O2`/`-O3` import breadth,
// but it multiplies the dynamic instruction count and destroys the loop
// shapes trust-cg's own NEON vectorizers key on.
//
// This module decides, per function, which vector SSA values can instead be
// carried as ONE `trust_ir` value of type `Ty::Vector(elem, lanes)` — a single
// machine V128 register — and leaves everything else to the scalarizer.
//
// # What "native" means here, exactly
//
// `trust-cg-lower` already models a CONTRACTED set of 128-bit shapes end to
// end (adapter -> LIR opcode -> AArch64 ISel -> encoder), and this module is
// deliberately a strict SUBSET of what that pipeline has already proven. It
// introduces NO new machine opcode, NO new lowering, and NO new proof
// obligation: every instruction it emits is one the backend already accepts
// from `rustc_codegen_trust_cg`'s `std::simd` path.
//
// Admitted shapes ([`NATIVE_SHAPES`]):
//
//   `<16 x i8>`  `<8 x i16>`  `<4 x i32>`  `<2 x i64>`
//   `<4 x float>`  `<2 x double>`
//
// The two packed floating-point shapes USED to be excluded here, because their
// LIR opcodes (`V4F32Fadd` …) were wired only in the x86-64 ISel and FAILED
// CLOSED in the AArch64 ISel. That hole is now closed: `isel.rs` dispatches
// them to `NeonFaddV`/`NeonFsubV`/`NeonFmulV`/`NeonFdivV`, machine opcodes the
// backend already encoded, already emitted from its own FP vectorizers, and
// already discharged lane obligations for at BOTH `.4S` and `.2D`. So packed
// FP is admitted on exactly the same terms as the integer shapes.
//
// Admitted operations, on those shapes only:
//
//   * `load` / `store`                       -> `LDR Q` / `STR Q`
//   * `add` `sub` `mul` `and` `or` `xor`     -> `ADD/SUB/MUL .16b/.8h/.4s/.2d`,
//     (INTEGER elements only)                   `AND/ORR/EOR .16b`
//   * `fadd` `fsub` `fmul` `fdiv`            -> `FADD/FSUB/FMUL/FDIV .4s/.2d`
//     (FLOAT elements only)
//   * `phi`                                  -> a V128 block parameter
//   * `extractelement` / `insertelement`     -> `UMOV` / `INS` (constant lane);
//                                               FP lanes go via the adapter's
//                                               proven stack round-trip
//   * `shufflevector` with an ALL-ZERO mask  -> `DUP` (lane-0 broadcast)
//
// The integer and FP arithmetic sets are DISJOINT and enforced as such: an
// integer opcode on an FP shape (or the reverse) scalarizes rather than
// picking some other lane operation.
//
// Packing FP lanes is BIT-EXACT, not an approximation. Each admitted FP
// opcode is defined lane-wise as the IEEE-754 binary operation under
// round-to-nearest-even, which is exactly what the NEON vector form computes;
// no reassociation, contraction, or horizontal reduction is introduced. This
// is why packed FP needs no fast-math licence, and equally why FP opcodes that
// WOULD need one (any reduction) are still absent.
//
// Every other opcode, every other mask, and every other shape returns
// "scalarize" and is handled by [`crate::vector`] exactly as before.
//
// # Mixed representation, and why it is sound
//
// A function may legitimately mix: puzzle's `-O2` loop carries a `<4 x i64>`
// induction vector (256-bit, NOT a machine register) that feeds `<4 x i32>`
// arithmetic through a `trunc`. So a vector SSA value is in exactly one of two
// states, decided ONCE per value by [`plan_function`]:
//
//   NATIVE      — one `ValueId` of type `Ty::Vector(elem, lanes)`.
//   SCALARIZED  — `lanes` scalar `ValueId`s named `%v#v0 … %v#v{n-1}`.
//
// Both forms may be materialized for the same value; the boundary conversions
// are emitted AT THE DEFINITION SITE, never at a use site, so the converted
// value dominates every use exactly as the original did:
//
//   NATIVE -> lanes   `extractelement` per lane, right after the producer.
//   lanes -> NATIVE   `vector.pack_lanes`, right after the last lane is defined.
//
// Both directions are pure re-materializations of the SAME bit pattern: LLVM
// fixes lane `i` at byte offset `i * sizeof(elem)` (little-endian lane order),
// which is exactly the lane numbering `trust_ir`'s `ExtractElement` /
// `InsertElement` / `vector.pack_lanes` use, and exactly the numbering the
// AArch64 encoder emits for `INS`/`UMOV`/`DUP`. Nothing is reordered.
//
// # Fail-closed discipline
//
// [`plan_function`] is purely SUBTRACTIVE: it starts from the instructions it
// can prove native and removes any whose operands it cannot prove native. A
// value that never makes it into the plan simply scalarizes, which is already
// correct. There is no path on which an unrecognized opcode, mask, shape or
// operand spelling is lowered natively "by default".
//
// `TCG_NO_NATIVE_VECTOR_LOWER=1` empties every plan, restoring pure
// scalarization byte for byte.

use std::collections::{BTreeMap, BTreeSet};

use trust_ir::Ty;

/// The contracted 128-bit vector shapes this module lowers natively, spelled
/// as `(llvm_element_token, lanes)`.
///
/// Membership is NOT "what fits in 128 bits": it is "what `trust-cg-lower`'s
/// AArch64 ISel already lowers for EVERY operation in [`native_capable`]".
/// `<4 x double>` and `<8 x float>` fit that first description and are still
/// absent, because they are two registers, not one.
const NATIVE_SHAPES: &[(&str, u32)] = &[
    ("i8", 16),
    ("i16", 8),
    ("i32", 4),
    ("i64", 2),
    ("float", 4),
    ("double", 2),
];

/// A native vector shape: the trust_ir element type and the lane count.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Shape {
    pub elem: NativeElem,
    pub lanes: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NativeElem {
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
}

impl NativeElem {
    pub fn ty(self) -> Ty {
        match self {
            NativeElem::I8 => Ty::I8,
            NativeElem::I16 => Ty::I16,
            NativeElem::I32 => Ty::I32,
            NativeElem::I64 => Ty::I64,
            NativeElem::F32 => Ty::F32,
            NativeElem::F64 => Ty::F64,
        }
    }

    /// The LLVM textual spelling of this element type.
    pub fn token(self) -> &'static str {
        match self {
            NativeElem::I8 => "i8",
            NativeElem::I16 => "i16",
            NativeElem::I32 => "i32",
            NativeElem::I64 => "i64",
            NativeElem::F32 => "float",
            NativeElem::F64 => "double",
        }
    }

    /// Whether this element is a floating-point type.
    ///
    /// The integer and FP lane opcodes are mutually exclusive: only the FP
    /// elements may carry `fadd`/`fsub`/`fmul`/`fdiv`, and only the integer
    /// elements may carry `add`/`sub`/`mul`/`and`/`or`/`xor`.
    pub fn is_float(self) -> bool {
        matches!(self, NativeElem::F32 | NativeElem::F64)
    }

    fn from_token(t: &str) -> Option<Self> {
        match t {
            "i8" => Some(NativeElem::I8),
            "i16" => Some(NativeElem::I16),
            "i32" => Some(NativeElem::I32),
            "i64" => Some(NativeElem::I64),
            "float" => Some(NativeElem::F32),
            "double" => Some(NativeElem::F64),
            _ => None,
        }
    }
}

impl Shape {
    pub fn vector_ty(self) -> Ty {
        Ty::Vector(Box::new(self.elem.ty()), self.lanes)
    }
}

/// Parse `<N x T>` and return the shape iff it is one of [`NATIVE_SHAPES`].
///
/// Returns `None` both for non-vector types and for vector types outside the
/// contracted set — the caller treats both as "not ours", and the second case
/// is what keeps `<4 x double>`, `<8 x float>`, `<4 x i64>`, `<12 x i32>` and
/// the rest of the census on the scalarizing path.
pub(crate) fn native_shape(ty: &str) -> Option<Shape> {
    let (elem_tok, lanes) = match crate::vector::vector_shape(ty) {
        Ok(Some(pair)) => pair,
        _ => return None,
    };
    if !NATIVE_SHAPES
        .iter()
        .any(|(e, l)| *e == elem_tok && *l == lanes)
    {
        return None;
    }
    Some(Shape {
        elem: NativeElem::from_token(&elem_tok)?,
        lanes,
    })
}

/// `TCG_NO_NATIVE_VECTOR_LOWER=1` restores pure lane scalarization.
pub(crate) fn native_lower_disabled() -> bool {
    std::env::var_os("TCG_NO_NATIVE_VECTOR_LOWER").is_some_and(|v| v != "0")
}

/// How one instruction wants a native vector built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum NativeForm {
    /// `load <S>, ptr %p`
    Load,
    /// `store <S> %v, ptr %p`
    Store,
    /// A lane-wise `trust_ir` `BinOp` over the whole vector.
    BinOp,
    /// `phi <S> [...]` — a V128 block parameter.
    Phi,
    /// `extractelement <S> %v, <ity> K` (constant lane).
    ExtractElement,
    /// `insertelement <S> %v, <T> %x, <ity> K` (constant lane).
    InsertElement,
    /// `shufflevector <S> %a, <S> _, <N x i32> zeroinitializer` where `%a` is
    /// the canonical `insertelement <S> poison, T %x, i64 0` — i.e. clang's
    /// two-instruction spelling of "broadcast the scalar `%x`", which is one
    /// NEON `DUP`.
    ///
    /// `splat_token` is that scalar. The pair is recognised TOGETHER and no
    /// other shuffle is admitted: a broadcast whose source is an arbitrary
    /// vector would need a lane-0 read followed by a pack, and that path has no
    /// witness coverage, so it fails closed to scalarization instead of being
    /// carried as unproven code.
    SplatLane0 { splat_token: String },
}

/// One vector-carrying instruction, as the planner sees it.
#[derive(Clone, Debug)]
struct Desc {
    /// SSA result name without `%`, when the instruction has one.
    result: Option<String>,
    /// The result's native vector shape, when the RESULT is a native vector.
    result_shape: Option<Shape>,
    /// `%name` operands that are vector-typed, with their shape when native.
    /// A vector operand whose shape is NOT native makes `form` `None`.
    vec_operands: Vec<String>,
    /// The native lowering this instruction would use, if it is eligible.
    form: Option<NativeForm>,
    /// `false` for `phi`: a block parameter's incoming values are bound in the
    /// PREDECESSOR's terminator, where a `vector.pack_lanes` cannot be placed
    /// at the definition site. A native phi therefore requires every incoming
    /// vector value to be native already.
    allows_pack: bool,
    /// For a `shufflevector`: the SSA name of its FIRST operand, which is the
    /// only operand a lane-0 broadcast reads.
    ///
    /// This is recorded explicitly rather than taken from `vec_operands[0]`
    /// because the first operand may be a CONSTANT vector, in which case
    /// `vec_operands[0]` would be the SECOND operand — and resolving the splat
    /// idiom against the wrong operand would broadcast the wrong scalar.
    shuffle_src: Option<String>,
}

/// The per-function decision.
#[derive(Clone, Debug, Default)]
pub(crate) struct NativePlan {
    /// SSA names carried as ONE native vector value.
    native: BTreeSet<String>,
    /// Native names that ALSO need per-lane values materialized (some use of
    /// them is scalarized).
    needs_lanes: BTreeMap<String, Shape>,
    /// Scalarized names that ALSO need a packed native value materialized
    /// (some use of them is native).
    needs_pack: BTreeMap<String, Shape>,
    /// How each native RESULT-PRODUCING instruction is lowered, keyed by its
    /// SSA result name. A `store` has no result and is decided at emission
    /// time by the same rule the planner used: native exactly when its stored
    /// value is native (or a constant) and its type is a contracted shape.
    forms: BTreeMap<String, NativeForm>,
}

impl NativePlan {
    pub fn is_empty(&self) -> bool {
        self.native.is_empty() && self.forms.is_empty()
    }

    pub fn is_native(&self, name: &str) -> bool {
        self.native.contains(name)
    }

    pub fn lanes_needed(&self, name: &str) -> Option<Shape> {
        self.needs_lanes.get(name).copied()
    }

    pub fn pack_needed(&self, name: &str) -> Option<Shape> {
        self.needs_pack.get(name).copied()
    }

    /// The native form for the instruction whose result is `name`, or `None`
    /// when that instruction scalarizes.
    pub fn form(&self, name: &str) -> Option<&NativeForm> {
        self.forms.get(name)
    }
}

/// Strip the opcode's leading flag tokens (`nsw`, `nuw`, `fast`, …) the same
/// way [`crate::vector`] does, so the planner sees the same operand text the
/// emitter will.
fn peel_flags(s: &str) -> &str {
    let mut rest = s.trim_start();
    loop {
        let next = rest.split_whitespace().next().unwrap_or("");
        let is_flag = matches!(
            next,
            "nsw"
                | "nuw"
                | "exact"
                | "disjoint"
                | "samesign"
                | "nneg"
                | "fast"
                | "nnan"
                | "ninf"
                | "nsz"
                | "arcp"
                | "contract"
                | "afn"
                | "reassoc"
        );
        if next.is_empty() || !is_flag {
            return rest;
        }
        rest = rest[next.len()..].trim_start();
    }
}

fn split_ty_val(s: &str) -> Option<(String, String)> {
    crate::parser::split_leading_type(s).map(|(t, v)| (t.to_string(), v.to_string()))
}

/// True for the constant spellings a vector operand may take. These carry no
/// SSA dependency, so an instruction whose only vector operand is one of them
/// can be native regardless of what else the function does.
fn is_vector_constant_token(tok: &str) -> bool {
    let tok = tok.trim();
    tok == "zeroinitializer"
        || tok == "undef"
        || tok == "poison"
        || tok.starts_with("splat (")
        || (tok.starts_with('<') && tok.ends_with('>'))
}

/// Classify ONE vector operand clause `<ty> <val>`.
///
/// * `Ok(None)`  — not vector-typed; irrelevant to the plan.
/// * `Ok(Some(None))` — a native-shaped vector CONSTANT (no SSA dependency).
/// * `Ok(Some(Some(name)))` — a native-shaped vector SSA operand.
/// * `Err(())` — vector-typed but NOT a native shape, or a spelling this
///   module does not model. The instruction is not eligible.
#[allow(clippy::type_complexity)]
fn classify_operand(clause: &str) -> Result<Option<Option<String>>, ()> {
    let Some((ty, val)) = split_ty_val(clause) else {
        return Err(());
    };
    if crate::vector::vector_shape(&ty).ok().flatten().is_none() {
        // Not a vector operand at all (or an unparsable vector type, which
        // `vector_shape` reports as `Err` and we treat as ineligible).
        return match crate::vector::vector_shape(&ty) {
            Ok(None) => Ok(None),
            _ => Err(()),
        };
    }
    if native_shape(&ty).is_none() {
        return Err(());
    }
    let val = val.trim();
    if let Some(name) = val.strip_prefix('%') {
        return Ok(Some(Some(name.to_string())));
    }
    if is_vector_constant_token(val) {
        return Ok(Some(None));
    }
    Err(())
}

/// Read a non-negative constant lane index out of an operand clause.
fn const_lane_index(clause: &str) -> Option<u32> {
    let (_, val) = split_ty_val(clause)?;
    let v = crate::parser::parse_int_literal(&val)?;
    u32::try_from(v).ok()
}

/// True when the mask operand of a `shufflevector` selects lane 0 of the FIRST
/// operand for every result lane — the only mask this module lowers.
///
/// Accepted spellings: `zeroinitializer`, and an explicit all-`0` element list.
/// `undef`/`poison` mask lanes are REFUSED here (rather than refined to 0)
/// because the whole point of this gate is that the emitted `DUP` is provably
/// the requested permutation, not a legal-but-different one.
fn is_lane0_broadcast_mask(clause: &str, out_lanes: u32) -> bool {
    let Some((mask_ty, mask_val)) = split_ty_val(clause) else {
        return false;
    };
    let Ok(Some((_, mask_lanes))) = crate::vector::vector_shape(&mask_ty) else {
        return false;
    };
    if mask_lanes != out_lanes {
        return false;
    }
    let v = mask_val.trim();
    if v == "zeroinitializer" {
        return true;
    }
    let Some(inner) = v.strip_prefix('<').and_then(|s| s.strip_suffix('>')) else {
        return false;
    };
    let elems = crate::parser::split_aggregate_elems(inner);
    if elems.len() != out_lanes as usize {
        return false;
    }
    elems.iter().all(|e| {
        split_ty_val(e).is_some_and(|(_, val)| crate::parser::parse_int_literal(&val) == Some(0))
    })
}

/// The native FORMS admitted for a floating-point element shape.
///
/// Packed FP is a strict SUBSET of what the integer shapes get, and the cut is
/// drawn where the downstream path stops existing rather than where it stops
/// being useful:
///
///   * `Splat` — `trust_ir::dialect::vector::pack_lanes_repeated` gates on its
///     own supported-shape list (`<16 x i8>`, `<8 x i16>`, `<4 x i32>`,
///     `<2 x i64>`, `<8 x i8>`) and REFUSES an FP vector type. trust-ir is a
///     pinned external dependency, so the splat form scalarizes for FP until
///     that gate admits it.
///   * `ExtractElement` / `InsertElement` — the adapter does lower these for
///     FP, but only through a stack round-trip (`translate_fp_vector_extract_
///     element` -> `translate_vector_extract_lane_stack`). Admitting them would
///     build a value in a vector register whose lane access immediately spills
///     it, which is exactly the cost floor the planner's rule (2) exists to
///     avoid. They stay scalarized until a register-form FP lane access exists.
///
/// `Load`/`Store`/`BinOp`/`Phi` are admitted: those are `LDR Q`/`STR Q`, the
/// four `NeonF*V` arithmetic forms, and a V128 block parameter — all
/// register-form, all already proven.
///
/// This is a POLICY function, deliberately separate from the per-opcode
/// recognizers, so that "what packed FP is allowed to do" is stated in exactly
/// one place and can be widened by editing one list.
fn fp_form_admitted(form: &NativeForm) -> bool {
    matches!(
        form,
        NativeForm::Load | NativeForm::Store | NativeForm::BinOp | NativeForm::Phi
    )
}

/// Describe one instruction line for the planner. `None` means the line has no
/// vector type at all and is irrelevant.
///
/// This wrapper applies the packed-FP form restriction to whatever
/// [`describe_forms`] recognized; see [`fp_form_admitted`].
fn describe(result: Option<&str>, rest: &str) -> Option<Desc> {
    let mut desc = describe_forms(result, rest)?;
    let shape_is_fp = desc.result_shape.is_some_and(|s| s.elem.is_float());
    // A `store` carries no result shape — its shape lives on the operand — so
    // ask the text directly rather than inferring from `result_shape`.
    let operand_is_fp = desc.form.as_ref().is_some_and(|f| *f == NativeForm::Store)
        && stored_value_shape(rest).is_some_and(|s| s.elem.is_float());
    if (shape_is_fp || operand_is_fp) && desc.form.as_ref().is_some_and(|f| !fp_form_admitted(f)) {
        desc.form = None;
    }
    // Packed FP never participates in the lanes -> NATIVE boundary, because
    // that boundary emits `vector.pack_lanes`, whose strict trust-ir decode
    // gate does not admit an FP vector type. Clearing `allows_pack` makes the
    // planner demand that every vector operand of a native FP instruction be
    // native ALREADY -- strictly stronger than the integer rule, and the
    // fail-closed direction.
    if shape_is_fp || operand_is_fp {
        desc.allows_pack = false;
    }
    Some(desc)
}

/// The native shape of a `store`'s VALUE operand, or `None`.
fn stored_value_shape(rest: &str) -> Option<Shape> {
    let opcode = rest.split_whitespace().next().unwrap_or("");
    if opcode != "store" {
        return None;
    }
    let tail = peel_flags(rest[opcode.len()..].trim_start());
    let (val_part, _) = crate::parser::split_comma(&tail)?;
    let (ty, _) = split_ty_val(&val_part)?;
    native_shape(&ty)
}

/// Recognize one instruction line's native FORM, before the packed-FP policy
/// filter in [`describe`] is applied.
fn describe_forms(result: Option<&str>, rest: &str) -> Option<Desc> {
    if !crate::vector::mentions_vector_type(rest) {
        return None;
    }
    let opcode = rest.split_whitespace().next().unwrap_or("");
    let tail = peel_flags(rest[opcode.len()..].trim_start());

    // Default: vector-typed but not eligible. Recording it with `form: None`
    // still matters — the planner reads `vec_operands` to learn which native
    // values a SCALARIZED instruction consumes, which is what drives
    // `needs_lanes`.
    let mut desc = Desc {
        result: result.map(str::to_string),
        result_shape: None,
        vec_operands: Vec::new(),
        form: None,
        allows_pack: true,
        shuffle_src: None,
    };

    // Collect every vector-typed SSA operand, whatever the opcode. An operand
    // whose shape is NOT native leaves `vec_operands` empty for that clause
    // and marks the instruction ineligible (`eligible_operands == false`),
    // but the instruction still scalarizes correctly.
    let mut eligible_operands = true;
    let mut push = |desc: &mut Desc, clause: &str| match classify_operand(clause) {
        Ok(Some(Some(name))) => desc.vec_operands.push(name),
        Ok(Some(None)) | Ok(None) => {}
        Err(()) => eligible_operands = false,
    };

    match opcode {
        "load" => {
            // `load [volatile|atomic] <ty>, ptr %p[, align N]`
            if tail.starts_with("volatile ") || tail.starts_with("atomic ") {
                return Some(desc);
            }
            let (ty, _) = crate::parser::split_comma(tail)?;
            desc.result_shape = native_shape(&ty);
            if desc.result_shape.is_some() && result.is_some() {
                desc.form = Some(NativeForm::Load);
            }
            return Some(desc);
        }
        "store" => {
            if tail.starts_with("volatile ") || tail.starts_with("atomic ") {
                return Some(desc);
            }
            let (val_part, _) = crate::parser::split_comma(tail)?;
            let (ty, _) = split_ty_val(&val_part)?;
            if native_shape(&ty).is_some() {
                push(&mut desc, &val_part);
                if eligible_operands {
                    // A `store` has no SSA result: it never enters `native` and
                    // is decided at emission time from its operand.
                    desc.form = Some(NativeForm::Store);
                }
            } else if crate::vector::vector_shape(&ty).ok().flatten().is_some() {
                // A non-native vector store: the stored value scalarizes.
                push(&mut desc, &val_part);
            }
            return Some(desc);
        }
        "add" | "sub" | "mul" | "and" | "or" | "xor" | "fadd" | "fsub" | "fmul" | "fdiv" => {
            let (ty, operands) = split_ty_val(tail)?;
            desc.result_shape = native_shape(&ty);
            let (lhs, rhs) = crate::parser::split_comma(&operands)?;
            push(&mut desc, &format!("{ty} {lhs}"));
            push(&mut desc, &format!("{ty} {rhs}"));
            // The integer opcodes and the FP opcodes address DISJOINT element
            // domains, and the machine instructions they lower to are entirely
            // different (`ADD .4s` vs `FADD .4s`). LLVM's own verifier already
            // rejects `fadd <4 x i32>` and `and <2 x double>`, so this can only
            // fire on malformed input — but "the frontend would have caught it"
            // is not a reason for a backend to pick an arbitrary lane op.
            // Refuse the cross product explicitly; a refusal here scalarizes,
            // which is always correct.
            let elem_is_fp = desc.result_shape.is_some_and(|s| s.elem.is_float());
            let op_is_fp = matches!(opcode, "fadd" | "fsub" | "fmul" | "fdiv");
            if elem_is_fp != op_is_fp {
                desc.result_shape = None;
            }
            if desc.result_shape.is_some() && eligible_operands && result.is_some() {
                desc.form = Some(NativeForm::BinOp);
            }
            return Some(desc);
        }
        "phi" => {
            let (ty, incoming) = split_ty_val(tail)?;
            desc.result_shape = native_shape(&ty);
            desc.allows_pack = false;
            for clause in crate::parser::split_aggregate_elems(&incoming) {
                let body = clause
                    .trim()
                    .strip_prefix('[')
                    .and_then(|s| s.trim().strip_suffix(']'))?;
                let (val, _) = crate::parser::split_comma(body)?;
                push(&mut desc, &format!("{ty} {val}"));
            }
            if desc.result_shape.is_some() && eligible_operands && result.is_some() {
                desc.form = Some(NativeForm::Phi);
            }
            return Some(desc);
        }
        "extractelement" => {
            let parts = crate::parser::split_aggregate_elems(tail);
            if parts.len() != 2 {
                return Some(desc);
            }
            let (vec_ty, _) = split_ty_val(&parts[0])?;
            let Some(shape) = native_shape(&vec_ty) else {
                push(&mut desc, &parts[0]);
                return Some(desc);
            };
            push(&mut desc, &parts[0]);
            let idx = const_lane_index(&parts[1]);
            if eligible_operands
                && result.is_some()
                && idx.is_some_and(|i| i < shape.lanes)
                // A constant-vector source has no SSA operand to be native, so
                // there is nothing to extract FROM natively; let it scalarize
                // (the scalarizer turns it into a literal, which is strictly
                // better than materializing a register).
                && !desc.vec_operands.is_empty()
            {
                desc.form = Some(NativeForm::ExtractElement);
            }
            return Some(desc);
        }
        "insertelement" => {
            let parts = crate::parser::split_aggregate_elems(tail);
            if parts.len() != 3 {
                return Some(desc);
            }
            let (vec_ty, _) = split_ty_val(&parts[0])?;
            desc.result_shape = native_shape(&vec_ty);
            push(&mut desc, &parts[0]);
            let Some(shape) = desc.result_shape else {
                return Some(desc);
            };
            // The inserted element must be the vector's own element type.
            let (ins_ty, _) = split_ty_val(&parts[1])?;
            let idx = const_lane_index(&parts[2]);
            if eligible_operands
                && result.is_some()
                && ins_ty == shape.elem.token()
                && idx.is_some_and(|i| i < shape.lanes)
            {
                desc.form = Some(NativeForm::InsertElement);
            }
            return Some(desc);
        }
        "shufflevector" => {
            let parts = crate::parser::split_aggregate_elems(tail);
            if parts.len() != 3 {
                return Some(desc);
            }
            let (a_ty, _) = split_ty_val(&parts[0])?;
            let (b_ty, _) = split_ty_val(&parts[1])?;
            // The first operand, recorded BEFORE the generic operand scan so
            // the splat resolver can never bind to the second one.
            if let Ok(Some(Some(name))) = classify_operand(&parts[0]) {
                desc.shuffle_src = Some(name);
            }
            push(&mut desc, &parts[0]);
            push(&mut desc, &parts[1]);
            let Some(shape) = native_shape(&a_ty) else {
                return Some(desc);
            };
            if a_ty != b_ty {
                return Some(desc);
            }
            desc.result_shape = Some(shape);
            if eligible_operands
                && result.is_some()
                && desc.shuffle_src.is_some()
                && is_lane0_broadcast_mask(&parts[2], shape.lanes)
            {
                // Placeholder: `plan_function` fills in the broadcast scalar
                // once it can look at the source's producer, and DROPS the form
                // if the source is not the canonical insert-at-lane-0 idiom.
                desc.form = Some(NativeForm::SplatLane0 {
                    splat_token: String::new(),
                });
            }
            return Some(desc);
        }
        _ => {}
    }

    // Every other opcode. This instruction will SCALARIZE, so the planner only
    // needs two things from it: the native shape of its result (so a native
    // consumer can pack the lanes back up) and which native values it reads (so
    // they get exploded into lanes at their definition).
    //
    // Both scans are conservative in the SAFE direction. Missing an operand or
    // a result shape here cannot miscompile: the scalarized text would then
    // reference `%v#vi` (or the native emitter would reference `%v`) with no
    // definition, and `check_all_named_values_defined` turns that into a clean
    // `Unsupported` before any code is emitted.
    desc.result_shape = native_result_shape(rest);
    scan_vector_operands(tail, &mut desc.vec_operands);
    Some(desc)
}

/// The native vector shape of an instruction's RESULT, read from its text.
///
/// A cast prints its destination type after a top-level ` to `; every other
/// result-producing form prints the result type first. Returns `None` for a
/// scalar or non-contracted result.
fn native_result_shape(rest: &str) -> Option<Shape> {
    let opcode = rest.split_whitespace().next().unwrap_or("");
    let tail = peel_flags(rest[opcode.len()..].trim_start());
    if let Some(dst) = split_top_level_to(tail) {
        return native_shape(dst);
    }
    let (ty, _) = split_ty_val(tail)?;
    native_shape(&ty)
}

/// Split at the first top-level ` to ` (a cast's type separator), returning the
/// destination-type text. Bracket-aware so `<4 x i32>` is never cut apart.
fn split_top_level_to(s: &str) -> Option<&str> {
    let bytes = s.as_bytes();
    let mut depth = 0i32;
    for (i, b) in bytes.iter().enumerate() {
        match b {
            b'[' | b'(' | b'{' | b'<' => depth += 1,
            b']' | b')' | b'}' | b'>' => depth -= 1,
            b' ' if depth == 0 && s[i..].starts_with(" to ") => {
                return Some(s[i + 4..].trim());
            }
            _ => {}
        }
    }
    None
}

/// Collect every `%name` that appears in `text` immediately after a CONTRACTED
/// vector type, plus the further `%name`s in the same comma list (LLVM prints
/// `add <4 x i32> %a, %b` — one type, two operands).
///
/// Only contracted shapes are collected: a `<4 x i64>` operand can never be
/// native, so it needs no boundary conversion.
fn scan_vector_operands(text: &str, out: &mut Vec<String>) {
    let bytes = text.as_bytes();
    for i in 0..bytes.len() {
        if bytes[i] != b'<' {
            continue;
        }
        let Some((ty, rest)) = crate::parser::split_leading_type(&text[i..]) else {
            continue;
        };
        if native_shape(ty).is_none() {
            continue;
        }
        // `rest` starts at the operand list for this type. Take names until a
        // token that is not an operand (a new type, a label, a closing paren).
        for tok in rest.split(',') {
            let tok = tok.trim();
            let tok = tok.split_whitespace().next().unwrap_or("");
            let tok = tok.trim_end_matches([')', ']', '}']);
            let Some(name) = tok.strip_prefix('%') else {
                break;
            };
            if name.is_empty() {
                break;
            }
            if !out.iter().any(|n| n == name) {
                out.push(name.to_string());
            }
        }
    }
}

/// The `insertelement <S> poison/undef, T %x, i64 0` idiom, returning the
/// broadcast token `%x`. Used to collapse clang's canonical two-instruction
/// splat into a single `DUP`.
fn insert_lane0_into_undef(rest: &str) -> Option<String> {
    let opcode = rest.split_whitespace().next().unwrap_or("");
    if opcode != "insertelement" {
        return None;
    }
    let parts = crate::parser::split_aggregate_elems(rest[opcode.len()..].trim_start());
    if parts.len() != 3 {
        return None;
    }
    let (vec_ty, vec_val) = split_ty_val(&parts[0])?;
    native_shape(&vec_ty)?;
    let vec_val = vec_val.trim();
    if vec_val != "undef" && vec_val != "poison" {
        return None;
    }
    if const_lane_index(&parts[2])? != 0 {
        return None;
    }
    let (_, ins_val) = split_ty_val(&parts[1])?;
    Some(ins_val.trim().to_string())
}

/// Decide, for one function body, which vector values are carried natively.
///
/// `body` is the function's instruction lines in source order; each entry is
/// `(result_name_without_percent, instruction_text)` exactly as the parser
/// sees it after the tail-call marker has been stripped. Non-instruction lines
/// (labels, braces) must be passed as `None`/`""` so line indices line up with
/// the caller's own numbering.
///
/// `enabled` is the kill switch, passed in so the caller reads the environment
/// exactly once per module and the planner stays a pure function of its input.
pub(crate) fn plan_function(body: &[(Option<String>, String)], enabled: bool) -> NativePlan {
    if !enabled {
        return NativePlan::default();
    }

    let mut descs: Vec<Desc> = Vec::new();
    // result name -> index into `descs`
    let mut producer: BTreeMap<String, usize> = BTreeMap::new();
    // instruction text keyed by result name, for the splat peephole.
    let mut text_of: BTreeMap<String, String> = BTreeMap::new();

    for (result, rest) in body.iter() {
        if rest.is_empty() {
            continue;
        }
        if let Some(name) = result {
            text_of.insert(name.clone(), rest.clone());
        }
        let Some(desc) = describe(result.as_deref(), rest) else {
            continue;
        };
        if let Some(name) = &desc.result {
            producer.insert(name.clone(), descs.len());
        }
        descs.push(desc);
    }

    // Resolve the lane-0 broadcast idiom now that every producer is known.
    // A broadcast shuffle is admitted ONLY when its source is clang's
    // `insertelement <S> undef/poison, T %x, i64 0`; anything else loses its
    // form here and scalarizes. Resolving it also DROPS the dependency on the
    // insertelement's result: the emitted `DUP` reads the scalar `%x` directly,
    // so the source vector is judged purely on its other uses (typically none,
    // in which case it costs nothing).
    for i in 0..descs.len() {
        if !matches!(descs[i].form, Some(NativeForm::SplatLane0 { .. })) {
            continue;
        }
        let token = descs[i]
            .shuffle_src
            .as_ref()
            .and_then(|src| text_of.get(src))
            .and_then(|text| insert_lane0_into_undef(text));
        match token {
            Some(splat_token) => {
                descs[i].form = Some(NativeForm::SplatLane0 { splat_token });
                descs[i].vec_operands.clear();
            }
            None => descs[i].form = None,
        }
    }

    // Seed: every instruction with a native form and a native vector result.
    let mut native: BTreeSet<String> = descs
        .iter()
        .filter(|d| d.form.is_some() && d.result_shape.is_some())
        .filter_map(|d| d.result.clone())
        .collect();

    // A native instruction is one that will actually be emitted natively.
    // For a value-producing instruction that is "its result is native"; for a
    // `store` it is "every vector operand is native or constant".
    let inst_is_native = |d: &Desc, native: &BTreeSet<String>| -> bool {
        if d.form.is_none() {
            return false;
        }
        match d.result_shape {
            Some(_) => d.result.as_ref().is_some_and(|r| native.contains(r)),
            // Result-less (`store`) or scalar-result (`extractelement`):
            // native exactly when its vector sources are native.
            None => d.vec_operands.iter().all(|o| native.contains(o)),
        }
    };

    // GREATEST FIXPOINT. Start optimistic, then remove any value that cannot
    // be justified. Removal is monotone, so this terminates in at most
    // `native.len()` rounds.
    loop {
        let mut victim: Option<String> = None;
        for name in &native {
            let Some(&di) = producer.get(name) else {
                victim = Some(name.clone());
                break;
            };
            let d = &descs[di];
            // (1) A phi cannot pack its incoming values (they are bound in the
            //     predecessor's terminator), so every incoming must be native.
            if !d.allows_pack && d.vec_operands.iter().any(|o| !native.contains(o)) {
                victim = Some(name.clone());
                break;
            }
            // (1b) A NON-NATIVE vector operand of a native instruction is
            //      materialised by the `needs_pack` boundary below, and that
            //      boundary can only emit a pack when it knows the operand's
            //      SHAPE -- it reads `descs[producer[operand]].result_shape`
            //      and silently skips the operand when either the producer is
            //      absent from this function or its shape was never derived.
            //      Staying native on such an operand therefore emits a USE of
            //      a value that nothing ever defines, and the importer stops
            //      with "SSA value `%N` is used but never defined".
            //
            //      Found by gcc-c-torture pr37573 / 20090113-1 at -O2, where
            //      the operand is a vector `select` (a form this planner does
            //      not recognise, so `result_shape` is None) feeding a `xor`
            //      that WAS planned native.  Both programs import at HEAD and
            //      regressed to IMPORT_FAIL.
            //
            //      Fail closed, which is this subsystem's whole contract: an
            //      unpackable operand demotes its consumer and the chain
            //      scalarizes exactly as it did before native lowering existed.
            if d.allows_pack
                && d.vec_operands.iter().any(|o| {
                    !native.contains(o)
                        && !producer
                            .get(o)
                            .is_some_and(|&pi| descs[pi].result_shape.is_some())
                })
            {
                victim = Some(name.clone());
                break;
            }
            // (2) Cost floor: a native value with NO native consumer would be
            //     built in a vector register only to be taken apart again. That
            //     is never a win, so demote it and let the whole chain
            //     scalarize. (A `store` counts as a native consumer: one
            //     `STR Q` always beats `lanes` scalar stores.)
            let has_native_use = descs
                .iter()
                .any(|d| d.vec_operands.iter().any(|o| o == name) && inst_is_native(d, &native));
            if !has_native_use {
                victim = Some(name.clone());
                break;
            }
            // (3) PACKED-FP COST FLOOR: a float-element value must be native
            //     for its WHOLE lifetime, or not at all.
            //
            //     Rule (2) asks only whether SOME consumer is native. For the
            //     integer shapes that is the right bar, because the NATIVE ->
            //     lanes boundary is a register-form `UMOV` per lane. For the
            //     FP shapes it is NOT: the adapter materializes an FP lane
            //     through `translate_vector_extract_lane_stack`, which stores
            //     the whole 16-byte vector to a FRESH stack slot and reloads
            //     the lane narrow. One mixed-use value therefore pays
            //     `sub`+`str q`+`ldr d` PER LANE PER USE SITE, each to a
            //     DIFFERENT address.
            //
            //     MEASURED, on BenchmarkGame/n-body at -O3 IR (the largest
            //     packed-FP SLP site in the corpus). Admitting mixed-use FP
            //     values bought TWO packed instructions in `advance` --
            //     `fsub.2d` and `fmul.2d` -- and paid for them with four
            //     16-byte spills of the same register to four distinct stack
            //     addresses plus four narrow reloads:
            //
            //         fsub.2d v1, v18, v0
            //         sub x0, x29, #0x50 ; str q1, [x0] ; ldr d9, [x0]
            //         sub x0, x29, #0x60 ; str q1, [x0] ; ldr d7, [x0, #8]
            //         fmul.2d v0, v1, v1
            //         sub x0, x29, #0x70 ; str q0, [x0] ; ldr d2, [x0, #8]
            //         sub x0, x29, #0x80 ; str q1, [x0] ; ldr d0, [x0]
            //
            //     Net: retired instructions 1.372 -> 1.579 and cycles
            //     1.033 -> 1.343 against the same oracle. Distinct-address
            //     store-port pressure is one of the few things that genuinely
            //     costs on this core, and this is a textbook case of it.
            //
            //     So: demote any FP value with a non-native consumer. What
            //     survives is the shape that actually pays -- vector in,
            //     vector arithmetic, vector out, lanes never separated.
            //
            //     This floor can be RAISED (i.e. this rule deleted) the moment
            //     FP lane access has a register form. `NeonDupScalarD` (`MOV
            //     Dd, Vn.D[lane]`) is already encoded and already carries a
            //     discharged lane obligation; it is not reachable from
            //     `trust_ir` lowering yet. That, not a wider shape table, is
            //     the next thing packed FP needs.
            if descs[di].result_shape.is_some_and(|s| s.elem.is_float()) {
                let has_scalar_use = descs.iter().any(|d| {
                    d.vec_operands.iter().any(|o| o == name) && !inst_is_native(d, &native)
                });
                if has_scalar_use {
                    victim = Some(name.clone());
                    break;
                }
            }
        }
        match victim {
            Some(v) => {
                native.remove(&v);
            }
            None => break,
        }
    }

    // Materialization requirements at the boundaries.
    let mut needs_lanes: BTreeMap<String, Shape> = BTreeMap::new();
    let mut needs_pack: BTreeMap<String, Shape> = BTreeMap::new();
    for d in &descs {
        let d_native = inst_is_native(d, &native);
        for operand in &d.vec_operands {
            let Some(&pi) = producer.get(operand) else {
                continue;
            };
            let Some(shape) = descs[pi].result_shape else {
                continue;
            };
            if native.contains(operand) {
                if !d_native {
                    needs_lanes.insert(operand.clone(), shape);
                }
            } else if d_native {
                needs_pack.insert(operand.clone(), shape);
            }
        }
    }

    // Record the emission form for every instruction that survived.
    let mut forms: BTreeMap<String, NativeForm> = BTreeMap::new();
    for d in &descs {
        if !inst_is_native(d, &native) {
            continue;
        }
        let (Some(name), Some(form)) = (d.result.clone(), d.form.clone()) else {
            continue;
        };
        forms.insert(name, form);
    }

    let plan = NativePlan {
        native,
        needs_lanes,
        needs_pack,
        forms,
    };
    if std::env::var_os("TCG_NATIVE_VECTOR_DEBUG").is_some() {
        eprintln!(
            "native-vector: {} vector-carrying insts, {} native, {} explode, {} pack",
            descs.len(),
            plan.native.len(),
            plan.needs_lanes.len(),
            plan.needs_pack.len()
        );
        for d in &descs {
            eprintln!(
                "  {:>10} form={:?} shape={:?} ops={:?} native={}",
                d.result.as_deref().unwrap_or("-"),
                d.form.as_ref().map(std::mem::discriminant),
                d.result_shape.map(|s| s.lanes),
                d.vec_operands,
                d.result.as_ref().is_some_and(|r| plan.native.contains(r))
            );
        }
    }
    plan
}

// What still scalarizes, deliberately (each one is a proven-lowering gap, not
// an oversight):
//
//   * EVERY wider or odd shape (`<4 x double>`, `<8 x float>`, `<4 x i64>`,
//     `<16 x i32>`, `<12 x i32>`, …) — those are not machine registers.
//     (`<4 x float>` / `<2 x double>` USED to be on this list; they are now
//     admitted, see the header.)
//   * `sdiv` `udiv` `srem` `urem` `shl` `lshr` `ashr` — no packed integer
//     divide exists; the packed shifts lower only for a uniform CONSTANT count
//     and are not worth a special case yet.
//   * `frem` and packed `fmin`/`fmax` — the adapter lowers these lane-wise
//     through a stack round-trip (a per-lane `fmod` CALL for `frem`), so
//     admitting them natively here would buy a register-form vector value
//     whose only consumer immediately spills it again.
//   * `icmp` / `fcmp` / `select` — the adapter accepts a vector `select` only
//     when its condition is provably a compare mask of the SAME shape, a
//     provenance rule this planner does not model.
//   * every vector CAST (`trunc`, `zext`, `sext`, `bitcast`, `fptosi`, …) —
//     `validate_cast_shape` admits only scalar source/destination types.
//   * `llvm.fmuladd.v*` / `llvm.fma.v*` — `vector.fma` has no adapter arm.
//   * `llvm.vector.reduce.*` — no adapter arm; the scalarizer's left-to-right
//     fold is already the exact ordered-reduction semantics.
//   * every `shufflevector` mask other than the lane-0 broadcast, including
//     `rev`/`zip`/`uzp`/`trn`/`ext`-shaped masks: their NEON opcodes exist in
//     the encoder but are reachable only from `trust-cg-opt`'s vectorizers,
//     not from `trust_ir` instruction lowering, so emitting them here would
//     need a new LIR opcode and a new proof.
//   * `volatile` / `atomic` vector memory, and `<N x i1>` in memory.

#[cfg(test)]
mod tests {
    use super::*;

    fn plan(lines: &[(Option<&str>, &str)]) -> NativePlan {
        plan_enabled(lines, true)
    }

    fn plan_enabled(lines: &[(Option<&str>, &str)], enabled: bool) -> NativePlan {
        let body: Vec<(Option<String>, String)> = lines
            .iter()
            .map(|(r, t)| (r.map(str::to_string), t.to_string()))
            .collect();
        plan_function(&body, enabled)
    }

    #[test]
    fn contracted_shapes_are_recognized_and_the_rest_are_not() {
        assert!(native_shape("<16 x i8>").is_some());
        assert!(native_shape("<8 x i16>").is_some());
        assert!(native_shape("<4 x i32>").is_some());
        assert!(native_shape("<2 x i64>").is_some());
        // Packed FP is admitted now that the AArch64 ISel lowers it.
        assert!(native_shape("<4 x float>").is_some());
        assert!(native_shape("<2 x double>").is_some());
        // Wider than a machine register.
        assert!(native_shape("<4 x i64>").is_none());
        assert!(native_shape("<8 x i32>").is_none());
        assert!(native_shape("<12 x i32>").is_none());
        // Not a vector.
        assert!(native_shape("i32").is_none());
        assert!(native_shape("<{ i32, i8 }>").is_none());
    }

    #[test]
    fn load_binop_store_chain_is_native() {
        let p = plan(&[
            (Some("a"), "load <4 x i32>, ptr %p, align 4"),
            (Some("b"), "load <4 x i32>, ptr %q, align 4"),
            (Some("c"), "add nsw <4 x i32> %a, %b"),
            (None, "store <4 x i32> %c, ptr %p, align 4"),
        ]);
        assert!(p.is_native("a"));
        assert!(p.is_native("b"));
        assert!(p.is_native("c"));
        assert!(p.lanes_needed("c").is_none());
        assert_eq!(p.form("c"), Some(&NativeForm::BinOp));
    }

    #[test]
    fn a_value_with_no_native_consumer_is_demoted() {
        // The load's only consumer is a `trunc`, which has no native lowering.
        // Building a vector register just to take it apart is never a win.
        let p = plan(&[
            (Some("a"), "load <4 x i32>, ptr %p, align 4"),
            (Some("t"), "trunc <4 x i32> %a to <4 x i8>"),
        ]);
        assert!(!p.is_native("a"));
        assert!(p.lanes_needed("a").is_none());
    }

    #[test]
    fn a_scalarized_operand_of_a_native_op_is_packed() {
        // `trunc` scalarizes; the `add` that consumes it stays native, so the
        // truncated lanes are packed back into one register at the boundary.
        let p = plan(&[
            (Some("w"), "load <4 x i64>, ptr %q, align 8"),
            (Some("t"), "trunc <4 x i64> %w to <4 x i32>"),
            (Some("s"), "add <4 x i32> %t, %u"),
            (Some("u"), "load <4 x i32>, ptr %p, align 4"),
            (None, "store <4 x i32> %s, ptr %p, align 4"),
        ]);
        assert!(p.is_native("s"));
        assert!(p.is_native("u"));
        assert!(!p.is_native("t"));
        assert_eq!(p.pack_needed("t").map(|s| s.lanes), Some(4));
        // The <4 x i64> value never becomes native: it is not a register shape.
        assert!(!p.is_native("w"));
    }

    #[test]
    fn a_native_value_read_by_a_scalarized_op_is_exploded() {
        let p = plan(&[
            (Some("a"), "load <4 x i32>, ptr %p, align 4"),
            (Some("b"), "load <4 x i32>, ptr %q, align 4"),
            (Some("c"), "xor <4 x i32> %a, %b"),
            (None, "store <4 x i32> %c, ptr %p, align 4"),
            (
                Some("r"),
                "call i32 @llvm.vector.reduce.xor.v4i32(<4 x i32> %c)",
            ),
        ]);
        assert!(p.is_native("c"));
        assert_eq!(p.lanes_needed("c").map(|s| s.lanes), Some(4));
    }

    #[test]
    fn phi_requires_native_incomings_and_cannot_pack() {
        // `%t` scalarizes (a cast), so the phi that takes it cannot be native:
        // a pack cannot be placed on the predecessor's edge.
        let p = plan(&[
            (Some("w"), "load <4 x i64>, ptr %q, align 8"),
            (Some("t"), "trunc <4 x i64> %w to <4 x i32>"),
            (
                Some("h"),
                "phi <4 x i32> [ zeroinitializer, %e ], [ %t, %l ]",
            ),
            (None, "store <4 x i32> %h, ptr %p, align 4"),
        ]);
        assert!(!p.is_native("h"));
    }

    #[test]
    fn phi_of_native_values_is_native() {
        let p = plan(&[
            (
                Some("h"),
                "phi <4 x i32> [ zeroinitializer, %e ], [ %n, %l ]",
            ),
            (Some("v"), "load <4 x i32>, ptr %p, align 4"),
            (Some("n"), "xor <4 x i32> %h, %v"),
            (None, "store <4 x i32> %n, ptr %p, align 4"),
        ]);
        assert!(p.is_native("h"));
        assert!(p.is_native("n"));
        assert_eq!(p.form("h"), Some(&NativeForm::Phi));
    }

    #[test]
    fn lane0_broadcast_shuffle_is_native_and_fuses_the_insert() {
        let p = plan(&[
            (Some("i"), "insertelement <4 x i32> poison, i32 %x, i64 0"),
            (
                Some("s"),
                "shufflevector <4 x i32> %i, <4 x i32> poison, <4 x i32> zeroinitializer",
            ),
            (Some("v"), "load <4 x i32>, ptr %p, align 4"),
            (Some("m"), "mul <4 x i32> %s, %v"),
            (None, "store <4 x i32> %m, ptr %p, align 4"),
        ]);
        assert!(p.is_native("s"));
        assert_eq!(
            p.form("s"),
            Some(&NativeForm::SplatLane0 {
                splat_token: "%x".to_string()
            })
        );
    }

    #[test]
    fn a_broadcast_whose_source_is_not_the_insert_idiom_fails_closed() {
        // The shuffle mask IS a lane-0 broadcast, but the source is an
        // ordinary loaded vector rather than `insertelement <S> poison, x, 0`.
        // Reading lane 0 out and packing it back has no witness coverage, so
        // the whole shuffle scalarizes instead.
        let p = plan(&[
            (Some("a"), "load <4 x i32>, ptr %p, align 4"),
            (
                Some("s"),
                "shufflevector <4 x i32> %a, <4 x i32> poison, <4 x i32> zeroinitializer",
            ),
            (None, "store <4 x i32> %s, ptr %p, align 4"),
        ]);
        assert!(!p.is_native("s"));
        // ... and an insert at a lane OTHER than 0 is not the idiom either.
        let p = plan(&[
            (Some("i"), "insertelement <4 x i32> poison, i32 %x, i64 1"),
            (
                Some("s"),
                "shufflevector <4 x i32> %i, <4 x i32> poison, <4 x i32> zeroinitializer",
            ),
            (None, "store <4 x i32> %s, ptr %p, align 4"),
        ]);
        assert!(!p.is_native("s"));
    }

    #[test]
    fn a_constant_first_operand_never_resolves_the_splat_to_the_second() {
        // The broadcast reads lane 0 of the FIRST operand, which here is a
        // CONSTANT vector. `%i` is the second operand and happens to be the
        // insert-into-poison idiom; binding the splat to it would broadcast
        // `%x` instead of the constant's lane 0 — a miscompile. The shuffle
        // must scalarize.
        let p = plan(&[
            (Some("i"), "insertelement <4 x i32> poison, i32 %x, i64 0"),
            (
                Some("s"),
                "shufflevector <4 x i32> <i32 7, i32 8, i32 9, i32 10>, \
                 <4 x i32> %i, <4 x i32> zeroinitializer",
            ),
            (None, "store <4 x i32> %s, ptr %p, align 4"),
        ]);
        assert!(!p.is_native("s"));
        assert!(p.form("s").is_none());
    }

    #[test]
    fn non_broadcast_masks_fail_closed_to_scalarization() {
        for mask in [
            "<4 x i32> <i32 3, i32 2, i32 1, i32 0>",     // rev
            "<4 x i32> <i32 0, i32 4, i32 1, i32 5>",     // zip1
            "<4 x i32> <i32 1, i32 2, i32 3, i32 4>",     // ext
            "<4 x i32> <i32 0, i32 undef, i32 0, i32 0>", // undef lane
            "<4 x i32> <i32 0, i32 0, i32 0, i32 1>",     // near-miss broadcast
        ] {
            let p = plan(&[
                (Some("a"), "load <4 x i32>, ptr %p, align 4"),
                (
                    Some("s"),
                    &format!("shufflevector <4 x i32> %a, <4 x i32> %a, {mask}"),
                ),
                (None, "store <4 x i32> %s, ptr %p, align 4"),
            ]);
            assert!(!p.is_native("s"), "mask {mask} must not lower natively");
        }
    }

    #[test]
    fn dynamic_lane_index_fails_closed() {
        let p = plan(&[
            (Some("a"), "load <4 x i32>, ptr %p, align 4"),
            (Some("e"), "extractelement <4 x i32> %a, i64 %i"),
            (Some("f"), "insertelement <4 x i32> %a, i32 %x, i64 %i"),
            (None, "store <4 x i32> %f, ptr %p, align 4"),
        ]);
        assert!(!p.is_native("f"));
        assert!(p.form("e").is_none());
    }

    #[test]
    fn out_of_range_lane_index_fails_closed() {
        let p = plan(&[
            (Some("a"), "load <4 x i32>, ptr %p, align 4"),
            (Some("f"), "insertelement <4 x i32> %a, i32 %x, i64 4"),
            (None, "store <4 x i32> %f, ptr %p, align 4"),
        ]);
        assert!(!p.is_native("f"));
    }

    #[test]
    fn volatile_and_atomic_vector_memory_never_go_native() {
        let p = plan(&[
            (Some("a"), "load volatile <4 x i32>, ptr %p, align 4"),
            (None, "store volatile <4 x i32> %a, ptr %p, align 4"),
        ]);
        assert!(!p.is_native("a"));
    }

    /// Packed FP now goes native at BOTH shapes and all four arithmetic ops
    /// (the AArch64 ISel dispatches them to `NeonF{add,sub,mul,div}V`).
    #[test]
    fn packed_fp_goes_native_at_both_shapes() {
        for (ty, op) in [
            ("<4 x float>", "fadd"),
            ("<4 x float>", "fsub"),
            ("<4 x float>", "fmul"),
            ("<4 x float>", "fdiv"),
            ("<2 x double>", "fadd"),
            ("<2 x double>", "fsub"),
            ("<2 x double>", "fmul"),
            ("<2 x double>", "fdiv"),
        ] {
            let p = plan(&[
                (Some("a"), &format!("load {ty}, ptr %p, align 4")),
                (Some("b"), &format!("load {ty}, ptr %q, align 4")),
                (Some("c"), &format!("{op} {ty} %a, %b")),
                (None, &format!("store {ty} %c, ptr %p, align 4")),
            ]);
            assert!(p.is_native("a"), "{ty} {op}: load a should be native");
            assert!(p.is_native("b"), "{ty} {op}: load b should be native");
            assert!(p.is_native("c"), "{ty} {op}: {op} should be native");
        }
    }

    /// The integer and FP arithmetic sets are DISJOINT. LLVM's verifier already
    /// rejects these spellings, so this pins the backend's own refusal rather
    /// than relying on the frontend to have filtered them out.
    #[test]
    fn integer_and_fp_lane_opcodes_do_not_cross() {
        // FP opcode on an integer shape.
        for op in ["fadd", "fsub", "fmul", "fdiv"] {
            let p = plan(&[
                (Some("a"), "load <4 x i32>, ptr %p, align 4"),
                (Some("b"), "load <4 x i32>, ptr %q, align 4"),
                (Some("c"), &format!("{op} <4 x i32> %a, %b")),
            ]);
            assert!(!p.is_native("c"), "{op} <4 x i32> must not go native");
        }
        // Integer opcode on an FP shape.
        for op in ["add", "sub", "mul", "and", "or", "xor"] {
            let p = plan(&[
                (Some("a"), "load <2 x double>, ptr %p, align 8"),
                (Some("b"), "load <2 x double>, ptr %q, align 8"),
                (Some("c"), &format!("{op} <2 x double> %a, %b")),
            ]);
            assert!(!p.is_native("c"), "{op} <2 x double> must not go native");
        }
    }

    /// Wider-than-a-register FP shapes stay scalarized.
    #[test]
    fn wide_fp_shapes_are_still_refused() {
        assert!(native_shape("<4 x double>").is_none());
        assert!(native_shape("<8 x float>").is_none());
        assert!(native_shape("<2 x float>").is_none());
        assert!(native_shape("<1 x double>").is_none());
    }

    #[test]
    fn kill_switch_empties_the_plan() {
        let lines: &[(Option<&str>, &str)] = &[
            (Some("a"), "load <4 x i32>, ptr %p, align 4"),
            (Some("b"), "load <4 x i32>, ptr %q, align 4"),
            (Some("c"), "add <4 x i32> %a, %b"),
            (None, "store <4 x i32> %c, ptr %p, align 4"),
        ];
        assert!(!plan_enabled(lines, true).is_empty());
        assert!(plan_enabled(lines, false).is_empty());
    }
}
