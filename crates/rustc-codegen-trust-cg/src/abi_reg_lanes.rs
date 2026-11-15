// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

//! THE REGISTER-LEVEL ABI PLACEMENT MODEL: which registers, of which CLASS and
//! how many, carry a by-value aggregate across a call edge.
//!
//! # Why this exists
//!
//! `822fdc69` closed the INDIRECT (sret) return end to end and left a hole it
//! named in its own commit message: its `ReturnPlacement` had exactly two
//! variants — `Registers` and `CallerBuffer` — so it could only compare WHERE
//! (registers vs a caller buffer), never WHICH. rustc's `PassMode::Pair` and
//! `PassMode::Cast` both map to "the return registers", so the gate agreed with
//! rustc while the register CLASS or COUNT differed. Measured on this host
//! (aarch64-apple-darwin, trustc 8b50cbcc5b, 2026-09-11), callee in a separately
//! compiled rlib, `#[inline(never)]`, at `-Copt-level=0` AND `=2`:
//!
//! ```text
//! struct P { a: f64, b: f64 }   -> P     LLVM: fmul d0 / fmul d1 / ret   (d0,d1)
//!                                        tcg : ldr x0,[x2] ; ldr x1,[x2,#8]
//!                                        llvm x tcg = 0, tcg x llvm = 0, want 42
//!
//! struct Q { a: i32, b: i32 }   -> Q     LLVM: ldr w0 / ldur w1 / ret    (w0,w1)
//!                                        tcg : ldr x0,[x1]               (ONE reg)
//!                                        llvm x tcg = 188/28, tcg x llvm = 20, want 42
//! ```
//!
//! Both are SILENT WRONG VALUES at a real ABI boundary, invisible to every
//! whole-program differential in this repo because both sides of such a test are
//! built by the same backend. The same hole exists on the ARGUMENT side and was
//! measured the same way (`benchmarks/regclass-xback`).
//!
//! # The model
//!
//! An ABI placement is a LIST OF LANES. Each lane is one register's worth: its
//! CLASS (integer / floating / vector), the number of value BYTES it carries,
//! and the value-relative byte OFFSET those bytes come from. Two classifiers
//! agree exactly when their lane lists agree lane by lane — same length, same
//! class, same offset, and the carrier's lane at least as wide as the lane the
//! ABI requires (a register's bits above the value's width are unspecified by
//! both AAPCS64 §5.4 and the AMD64 psABI, so a WIDER carrier is conformant and a
//! narrower one is not).
//!
//! Every fact on the rustc side comes from `FnAbi`/`PassMode`/`CastTarget`/`Reg`
//! and the layout's `BackendRepr` — never from a type name, a size heuristic or
//! a re-derived ABI rule. Every fact on the trust-cg side comes from the
//! backend's own classifier for the type the bridge is ABOUT TO DECLARE: on
//! aarch64 that is literally `AppleAArch64ABI::classify_returns` /
//! `classify_params`, the same function the instruction selector calls.

use rustc_abi::{BackendRepr, CanonAbi, HasDataLayout, Primitive, RegKind, Scalar, X86Call};
use rustc_target::callconv::PassMode;
use trust_cg_lower::x86_64_isel::{
    X86CallAbi, x86_scalar_return_result_regs, x86_sysv_returns_exceed_c_return_file,
};
use trust_cg_lower::{
    AArch64AbiVariant, AppleAArch64ABI, ArgLocation, PReg, Type as LowerType,
    translate_type_with_tables,
};
use trust_ir::Ty as TrustIrTy;

/// The broad class of register a lane occupies. Named for the MACHINE's
/// partition of its register file, which is what an ABI disagreement is about:
/// a value in `x0` and the same value in `d0` are different places, and no
/// amount of agreement about size makes them the same one.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum AbiRegClass {
    /// A general-purpose register (`x`/`w` on AArch64, `RAX`/`RDX`/… on x86-64).
    Integer,
    /// A scalar floating-point register (`d`/`s`/`h`/`b` on AArch64, an `XMM`
    /// used as a scalar on x86-64).
    Float,
    /// A full SIMD vector register (`v`/`q` on AArch64, a packed `XMM`).
    Vector,
}

impl AbiRegClass {
    fn describe(self) -> &'static str {
        self.describe_for(None)
    }

    /// The class named in `target`'s own terms: a wasm32 lane is a typed wasm
    /// value (a parameter or result), not a machine register.
    fn describe_for(self, target: Option<TrustCgAbiTarget>) -> &'static str {
        match (target, self) {
            (Some(TrustCgAbiTarget::Wasm32), AbiRegClass::Integer) => {
                "an INTEGER wasm value (i32/i64)"
            }
            (Some(TrustCgAbiTarget::Wasm32), AbiRegClass::Float) => {
                "a FLOATING-POINT wasm value (f32/f64)"
            }
            (Some(TrustCgAbiTarget::Wasm32), AbiRegClass::Vector) => "a VECTOR wasm value (v128)",
            (_, AbiRegClass::Integer) => "an INTEGER register (x/w, RAX/RDX)",
            (_, AbiRegClass::Float) => "a FLOATING-POINT register (d/s, XMM)",
            (_, AbiRegClass::Vector) => "a VECTOR register (v/q, packed XMM)",
        }
    }
}

/// What one lane of a placement is on `target`: a machine register natively,
/// a typed wasm value (parameter or result) on wasm32.
fn lane_noun(target: Option<TrustCgAbiTarget>) -> &'static str {
    match target {
        Some(TrustCgAbiTarget::Wasm32) => "wasm value",
        _ => "register",
    }
}

/// What a lane disagreement does at a real call edge on `target`: natively the
/// callee reads a value out of the wrong register file; on wasm32 each lane is a
/// typed wasm parameter or result, so the value is read as the wrong wasm value
/// type (or the two sides' signatures differ).
pub(super) fn boundary_misread(target: Option<TrustCgAbiTarget>) -> &'static str {
    match target {
        Some(TrustCgAbiTarget::Wasm32) => {
            "a value read as the wrong wasm value type or through a mismatched signature"
        }
        _ => "a value read out of the wrong register file",
    }
}

/// The escapes named by the `[TCG-ARG-ABI]` lane-disagreement refusal, in the
/// target's own terms. `pair` is rustc's `PassMode::Pair`, whose cause and
/// escapes differ from every other lane disagreement.
pub(super) fn arg_abi_options(target: TrustCgAbiTarget, pair: bool) -> &'static str {
    let wasm32 = target == TrustCgAbiTarget::Wasm32;
    if wasm32 && pair {
        "WHY: rustc's wasm32 Rust ABI passes a `BackendRepr::ScalarPair` value BY ITS TWO \
         SCALARS, each its own wasm parameter, while trust-cg declares this by-value aggregate \
         parameter differently. Options: (1) pass the value by reference (`fn f(v: &T)`), \
         which crosses no by-value argument convention; (2) for two scalars of EQUAL width \
         totalling at most 4 bytes, pass an array (`[u16; 2]` instead of `(u16, u16)`) — \
         rustc casts it to one `i32`, which trust-cg matches; (3) box it (`Box<T>`), which \
         passes one `i32` pointer; (4) teach trust-cg's ABI to place THIS lane shape."
    } else if wasm32 {
        "Options: (1) pass the value by reference (`fn f(v: &T)`), which crosses no by-value \
         argument convention; (2) give the type a shape whose wasm32 placement trust-cg \
         already matches — one scalar, at most 4 bytes of memory (rustc casts it to one \
         `i32`), or a larger memory aggregate (a caller-made copy passed by its `i32` \
         address); (3) box it (`Box<T>`), which passes one `i32` pointer; (4) teach \
         trust-cg's ABI to place THIS lane shape."
    } else if pair {
        "WHY: rustc passes a `BackendRepr::ScalarPair` value BY ITS TWO SCALARS, each in its \
         own register lane(s) (a 128-bit scalar takes two), whatever the pair's total size \
         and whatever its `#[repr]`, while a whole-slot declaration uses ONE value, \
         and no single carrier type has a pair's lanes. Options: \
         (1) pass the value by reference (`fn f(v: &T)`), which crosses no by-value argument \
         convention; (2) for two scalars of EQUAL width, pass an array (`[i16; 2]` instead \
         of `(i16, i16)`) — an array is never a ScalarPair, and up to 8 bytes rustc passes it \
         as one integer register, which trust-cg matches; (3) box it (`Box<T>`), which \
         passes one pointer-sized scalar; (4) teach trust-cg's ABI to place THIS lane \
         shape. The two-value `PassMode::Pair` lane (`scalar_pair_param_plan`) already \
         places admitted scalar carriers (including I128 arguments on AArch64 and \
         x86-64 integer pairs) and engages wherever it can; unsupported shapes include a \
         128-bit scalar lane beside a float or pointer or on an unadmitted target, a \
         lane with no carrier at all \
         (`f16`/`f128`), a pair whose scalars rustc marks `signext` (the lane's \
         zero-extending typed loads would not deliver it), or a closure BODY parameter \
         outside the shared AArch64/wasm32 argument plan (other targets, closure shims, \
         coroutine closures and unsupported wide-pointer construction retain their \
         existing routes; pass the pair by reference instead)."
    } else {
        "Options: (1) pass the value by reference (`fn f(v: &T)`), which crosses no \
         by-value argument convention; (2) give the type a shape whose register \
         placement trust-cg already matches — all-integer fields totalling 9-16 bytes \
         (an x0/x1 pair), one to four `f32` fields or one to four `f64` fields (an HFA \
         in s0-s3 / d0-d3), or anything over 16 bytes (a caller-allocated copy passed \
         by pointer); (3) box it (`Box<T>`), which passes one pointer-sized scalar; \
         (4) teach trust-cg's ABI to place THIS lane shape — a `PassMode::Pair` \
         argument already rides the two-value lane (`scalar_pair_param_plan`); this \
         one is a different mode."
    }
}

/// The escapes named by the `[TCG-RET-ABI]` lane-disagreement refusal, in the
/// target's own terms (`None`: the native register conventions).
pub(super) fn ret_abi_options(target: Option<TrustCgAbiTarget>) -> &'static str {
    if target == Some(TrustCgAbiTarget::Wasm32) {
        "Options: (1) return the value through an explicit out-parameter \
         (`fn f(out: &mut T)`), which crosses no return convention; (2) give the returned type \
         a shape whose wasm32 placement trust-cg already matches — one scalar, at most 4 bytes \
         of memory (rustc casts it to one `i32` result), or a value rustc returns through the \
         caller-allocated `sret` buffer (a larger memory aggregate); (3) box the value \
         (`-> Box<T>`), which returns one `i32` pointer; (4) teach trust-cg's ABI to place THIS \
         lane shape and this gate then passes on its own."
    } else {
        "Options: (1) return the value through an explicit out-parameter \
         (`fn f(out: &mut T)`), which crosses no return convention; (2) give the returned type \
         a shape whose register placement trust-cg already matches — all-integer fields \
         totalling 9-16 bytes (an x0/x1 pair), one to four `f32` fields or one to four `f64` \
         fields (an HFA in s0-s3 / d0-d3), a two-scalar pair on AArch64 (two registers of the \
         scalars' own classes), or anything over 16 bytes (the x8 buffer); (3) box the value \
         (`-> Box<T>`), which returns one pointer-sized scalar; (4) teach trust-cg's ABI to \
         place THIS lane shape and this gate then passes on its own."
    }
}

/// ONE register's worth of an ABI placement.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) struct AbiRegLane {
    pub(super) class: AbiRegClass,
    /// How many bytes OF THE VALUE this lane carries. For a carrier this is the
    /// register's own width; for a requirement it is the width the ABI says must
    /// be live, which may be narrower than the register (`w1` inside `x1`).
    pub(super) bytes: u64,
    /// Byte offset, within the value, of the bytes this lane carries.
    pub(super) offset: u64,
}

impl AbiRegLane {
    fn describe_for(&self, target: Option<TrustCgAbiTarget>) -> String {
        format!(
            "{} carrying {} byte(s) from offset {}",
            self.class.describe_for(target),
            self.bytes,
            self.offset
        )
    }
}

/// WHERE a value is placed at a call edge. Named for what the machine does, not
/// for one ABI's spelling of it, because the whole point of this type is to
/// compare TWO classifiers.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(super) enum ReturnPlacement {
    /// In registers — now with the CLASS, COUNT and per-lane extent, which is
    /// exactly what the two-variant predecessor could not state.
    Registers(Vec<AbiRegLane>),
    /// Written through a caller-allocated buffer whose address arrives in a
    /// hidden argument register (`x8` on AAPCS64, `RDI` on System V) — LLVM's
    /// `sret`, rustc's `PassMode::Indirect { on_stack: false }`.
    CallerBuffer,
    /// Copied BY VALUE onto the outgoing argument area (LLVM's `byval`, rustc's
    /// `PassMode::Indirect { on_stack: true }`). ARGUMENT-ONLY: no target rustc
    /// supports returns a value this way, and the return gate refuses the mode
    /// outright rather than mapping it onto a placement.
    StackByValue,
}

impl ReturnPlacement {
    pub(super) fn describe(&self) -> String {
        self.describe_for(None)
    }

    /// The placement named in `target`'s own terms (see
    /// [`AbiRegClass::describe_for`]); `None` names the native register files.
    pub(super) fn describe_for(&self, target: Option<TrustCgAbiTarget>) -> String {
        let wasm32 = target == Some(TrustCgAbiTarget::Wasm32);
        match self {
            ReturnPlacement::Registers(lanes) if lanes.is_empty() => {
                format!("no {}s at all", lane_noun(target))
            }
            ReturnPlacement::Registers(lanes) => format!(
                "{} {} lane(s): {}",
                lanes.len(),
                lane_noun(target),
                lanes
                    .iter()
                    .map(|lane| lane.describe_for(target))
                    .collect::<Vec<_>>()
                    .join("; ")
            ),
            ReturnPlacement::CallerBuffer if wasm32 => {
                "a caller-allocated RETURN BUFFER whose address is a hidden leading `i32` \
                 parameter (the wasm32 `sret` convention)"
                    .to_owned()
            }
            ReturnPlacement::CallerBuffer => {
                "a caller-allocated RETURN BUFFER whose address is a hidden argument (x8, RDI)"
                    .to_owned()
            }
            ReturnPlacement::StackByValue if wasm32 => {
                "memory: a caller-made copy whose address is passed as one `i32` parameter, so \
                 no wasm value carries any of the value's bytes"
                    .to_owned()
            }
            ReturnPlacement::StackByValue => {
                "a BY-VALUE COPY in the outgoing argument area (LLVM `byval`)".to_owned()
            }
        }
    }

    /// True when this placement is the hidden caller-allocated buffer. Kept as a
    /// predicate (rather than a `==` against a unit variant) so callers read the
    /// same way they did before `Registers` grew a payload.
    pub(super) fn is_caller_buffer(&self) -> bool {
        matches!(self, ReturnPlacement::CallerBuffer)
    }
}

/// The register class and byte width of an AArch64 physical register, read from
/// the backend's OWN assembly name for it.
///
/// The name is the backend's public statement of which register file entry it
/// selected (`preg_name`), and it is cross-checked against `PReg::is_gpr` /
/// `PReg::is_fpr` so a name/class disagreement refuses instead of resolving one
/// way. There is no wildcard admit: an unrecognised name is an error.
fn aarch64_preg_lane_shape(reg: PReg) -> Result<(AbiRegClass, u64), String> {
    let name = format!("{reg}");
    let (class, bytes) = match name.as_bytes().first() {
        Some(b'x') => (AbiRegClass::Integer, 8),
        Some(b'w') => (AbiRegClass::Integer, 4),
        // `v`/`q` name the full 128-bit SIMD register; `d`/`s`/`h`/`b` name the
        // 64/32/16/8-bit scalar views AAPCS64 §6.4.2 uses for HFA lanes.
        Some(b'v') | Some(b'q') => (AbiRegClass::Vector, 16),
        Some(b'd') => (AbiRegClass::Float, 8),
        Some(b's') if name != "sp" => (AbiRegClass::Float, 4),
        Some(b'h') => (AbiRegClass::Float, 2),
        Some(b'b') => (AbiRegClass::Float, 1),
        _ => {
            return Err(format!(
                "trust-cg's AArch64 ABI classifier placed a value in register `{name}`, which is \
                 not an argument/return register this gate can classify. Failing closed rather \
                 than guessing its register class."
            ));
        }
    };
    // Cross-check the name against the backend's own register-file predicate.
    // `PReg::is_gpr` answers "is a 64-bit X register", so a 32-bit `w` view is
    // NOT a `is_gpr` — the check that means "this is in the general-purpose file"
    // is therefore `!is_fpr`, which both `x` and `w` satisfy and no FP view does.
    // (Measured 2026-09-11: testing `is_gpr` here rejected a genuine `w0` return
    // lane the two-value scalar-pair lane had just emitted.)
    let consistent = match class {
        AbiRegClass::Integer => !reg.is_fpr(),
        AbiRegClass::Float | AbiRegClass::Vector => reg.is_fpr(),
    };
    if !consistent {
        return Err(format!(
            "trust-cg register `{name}` names {} but the backend's own is_fpr predicate \
             disagrees; refusing rather than picking one of the two answers.",
            class.describe()
        ));
    }
    Ok((class, bytes))
}

/// The lane list trust-cg's AArch64 classifier produces for ONE classified
/// location.
///
/// The offsets are the ones `isel::select_aggregate_return` /
/// `lower_formal_arguments` actually use:
///
/// * `Reg` — the whole value in one register, from offset 0.
/// * `RegPair` — AAPCS64's 9-16 byte composite: low eightbyte at 0, high at 8.
/// * `RegSequence` — an HFA/HVA (AAPCS64 §6.4.2): member `i` at `i * width`.
fn aarch64_location_lanes(loc: &ArgLocation) -> Result<ReturnPlacement, String> {
    Ok(match loc {
        ArgLocation::Ignore => ReturnPlacement::Registers(Vec::new()),
        ArgLocation::Reg(reg) => {
            let (class, bytes) = aarch64_preg_lane_shape(*reg)?;
            ReturnPlacement::Registers(vec![AbiRegLane {
                class,
                bytes,
                offset: 0,
            }])
        }
        ArgLocation::RegPair(lo, hi) => {
            let (lo_class, lo_bytes) = aarch64_preg_lane_shape(*lo)?;
            let (hi_class, hi_bytes) = aarch64_preg_lane_shape(*hi)?;
            ReturnPlacement::Registers(vec![
                AbiRegLane {
                    class: lo_class,
                    bytes: lo_bytes,
                    offset: 0,
                },
                AbiRegLane {
                    class: hi_class,
                    bytes: hi_bytes,
                    offset: 8,
                },
            ])
        }
        ArgLocation::RegSequence(regs) => {
            let mut lanes = Vec::with_capacity(regs.len());
            let mut offset = 0u64;
            for reg in regs {
                let (class, bytes) = aarch64_preg_lane_shape(*reg)?;
                lanes.push(AbiRegLane {
                    class,
                    bytes,
                    offset,
                });
                offset += bytes;
            }
            ReturnPlacement::Registers(lanes)
        }
        ArgLocation::Indirect { .. } => ReturnPlacement::CallerBuffer,
        ArgLocation::Stack { .. } => ReturnPlacement::StackByValue,
    })
}

/// System V AMD64 eightbyte class of one lane: `true` = SSE (all-float),
/// `false` = INTEGER. `None` = not yet seen.
type SysvEightbytes = [Option<bool>; 2];

/// Merge a leaf's class into its eightbyte, applying the psABI §3.2.3 rule that
/// INTEGER wins over SSE whenever both appear in the same eightbyte.
fn merge_eightbyte(slot: &mut Option<bool>, is_sse: bool) {
    *slot = Some(match *slot {
        None => is_sse,
        Some(prev) => prev && is_sse,
    });
}

/// Walk a LIR type's leaves, assigning each to its System V eightbyte.
///
/// `None` means the shape is one this model does NOT state exactly (a leaf
/// straddling an eightbyte boundary, an `Enum` whose payload overlaps, a
/// `V128` mixed with other fields, a zero-width leaf) — the caller then fails
/// closed rather than comparing against a guess. This mirrors
/// `trust_cg_lower::x86_64_isel::collect_sysv_aggregate_leaves`, whose
/// classification the x86-64 selector actually performs.
fn collect_sysv_leaves(ty: &LowerType, base: u64, out: &mut SysvEightbytes) -> Option<()> {
    match ty {
        LowerType::Struct(fields) => {
            for (index, field) in fields.iter().enumerate() {
                let offset = u64::from(ty.offset_of(index)?);
                collect_sysv_leaves(field, base + offset, out)?;
            }
            Some(())
        }
        LowerType::Array(elem, count) => {
            let stride = u64::from(elem.checked_bytes()? as u32);
            for index in 0..u64::from(*count) {
                collect_sysv_leaves(elem, base + index * stride, out)?;
            }
            Some(())
        }
        // A 128-bit integer leaf is TWO consecutive INTEGER eightbytes (psABI
        // §3.2.3: `RAX:RDX` / two GPR argument slots) — byte-for-byte the rule
        // the selector's `collect_sysv_aggregate_leaves` applies
        // (`x86_64_isel.rs`), so this gate never states a placement the selector
        // does not implement. `Array(I128, 1)` is the memory-slot spelling of a
        // 16-byte / 16-aligned niche scalar (`Option<NonZero<u128>>`, six
        // `library/core` roots), whose rustc placement is the same two lanes
        // (`rustc_placement` splits a 128-bit `Scalar` the same way). Measured
        // 2026-09-22: without this arm the scalar fall-through refused it as
        // "leaves do not tile the System V eightbytes exactly".
        LowerType::I128 => {
            let end = base.checked_add(16)?;
            if base % 8 != 0 || end > 16 {
                return None;
            }
            let lo = (base / 8) as usize;
            merge_eightbyte(&mut out[lo], false);
            merge_eightbyte(&mut out[lo + 1], false);
            Some(())
        }
        // An overlapping (tagged) payload has no single leaf class; a `V128`
        // mixed into a walk is the dedicated carrier shape, not a leaf.
        LowerType::Enum { .. } | LowerType::V128 => None,
        scalar => {
            let bytes = u64::from(scalar.bytes());
            if bytes == 0 {
                return None;
            }
            let end = base.checked_add(bytes)?;
            if end > 16 || base / 8 != (end - 1) / 8 {
                return None;
            }
            let is_sse = matches!(
                scalar,
                LowerType::F16 | LowerType::F32 | LowerType::F64 | LowerType::V64
            );
            merge_eightbyte(&mut out[(base / 8) as usize], is_sse);
            Some(())
        }
    }
}

/// The lane list the System V AMD64 RETURN classifier produces for one LIR
/// type, by the psABI §3.2.3 eightbyte rule the x86-64 selector implements.
///
/// A `>16`-byte aggregate is MEMORY class (a caller buffer); a shape the
/// eightbyte walk cannot state exactly is refused, never approximated.
///
/// RETURNS ONLY. This is still a mirror of the selector's return
/// classification (the selector exposes no return-placement function yet);
/// arguments read the selector's own placement (`x86_64_param_lanes`).
fn x86_64_type_lanes(ty: &LowerType) -> Result<ReturnPlacement, String> {
    let refuse = |why: &str| {
        Err(format!(
            "trust-cg's System V x86-64 classifier placement for `{ty:?}` is not stated exactly \
             by this gate ({why}); failing closed rather than comparing against a guess."
        ))
    };
    // A bare scalar keeps its own register; this mirrors `is_xmm_abi_value_type`
    // and the integer/`i128` return paths in `x86_64_isel`.
    let scalar_lane = |class: AbiRegClass, bytes: u64| {
        Ok(ReturnPlacement::Registers(vec![AbiRegLane {
            class,
            bytes,
            offset: 0,
        }]))
    };
    match ty {
        LowerType::B1 | LowerType::I8 => return scalar_lane(AbiRegClass::Integer, 1),
        LowerType::I16 => return scalar_lane(AbiRegClass::Integer, 2),
        LowerType::I32 => return scalar_lane(AbiRegClass::Integer, 4),
        LowerType::I64 => return scalar_lane(AbiRegClass::Integer, 8),
        // psABI §3.2.3: a 128-bit integer is TWO INTEGER eightbytes (RAX:RDX).
        LowerType::I128 => {
            return Ok(ReturnPlacement::Registers(vec![
                AbiRegLane {
                    class: AbiRegClass::Integer,
                    bytes: 8,
                    offset: 0,
                },
                AbiRegLane {
                    class: AbiRegClass::Integer,
                    bytes: 8,
                    offset: 8,
                },
            ]));
        }
        LowerType::F16 => return scalar_lane(AbiRegClass::Float, 2),
        LowerType::F32 => return scalar_lane(AbiRegClass::Float, 4),
        LowerType::F64 => return scalar_lane(AbiRegClass::Float, 8),
        LowerType::V64 => return scalar_lane(AbiRegClass::Float, 8),
        LowerType::V128 => return scalar_lane(AbiRegClass::Vector, 16),
        LowerType::Struct(_) | LowerType::Array(_, _) | LowerType::Enum { .. } => {}
    }
    let Some(size) = ty.checked_bytes() else {
        return refuse("its natural extent does not fit the LIR carrier");
    };
    if size == 0 {
        return refuse("it is zero-sized");
    }
    if size > 16 {
        // MEMORY class: a return goes through the caller's buffer.
        return Ok(ReturnPlacement::CallerBuffer);
    }
    let mut eightbytes: SysvEightbytes = [None, None];
    if collect_sysv_leaves(ty, 0, &mut eightbytes).is_none() {
        return refuse("its leaves do not tile the System V eightbytes exactly");
    }
    let count = size.div_ceil(8) as usize;
    let mut lanes = Vec::with_capacity(count);
    for index in 0..count {
        let Some(is_sse) = eightbytes[index] else {
            return refuse("one of its eightbytes holds no classified leaf");
        };
        lanes.push(AbiRegLane {
            class: if is_sse {
                AbiRegClass::Float
            } else {
                AbiRegClass::Integer
            },
            bytes: (size - (index as u64) * 8).min(8),
            offset: (index as u64) * 8,
        });
    }
    Ok(ReturnPlacement::Registers(lanes))
}

/// The targets whose trust-cg register placement this gate states exactly.
///
/// Any other architecture is REFUSED rather than compared against a guess: the
/// whole purpose of the gate is that a placement it reports as agreeing really
/// does agree, and it cannot say that about a classifier it does not model.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum TrustCgAbiTarget {
    /// `AppleAArch64ABI` — the backend's own classifier is called directly, so
    /// this side is not a mirror at all.
    AArch64,
    /// System V AMD64, modelled by the eightbyte rule above.
    X86_64,
    /// WebAssembly (wasm32), through trust-cg's wasm object lane. A wasm call
    /// has no registers: every scalar lane is one typed wasm PARAMETER (`i32`
    /// carries every integer up to 32 bits and pointers, `i64`/`f32`/`f64`
    /// their own), and LLVM's wasm32 ABI returns anything wider than one lane
    /// through a hidden `sret` buffer. `wasm_type_lanes` states the lanes
    /// trust-cg's wasm ABI (`trust_cg_codegen::wasm`, `lower/abi.rs`) gives a
    /// declared type; `rustc_placement_for_target` rewrites rustc's side into
    /// the same terms.
    Wasm32,
}

/// Architecture-only classifier selection, NOT calling-convention admission.
/// Production aggregate boundaries must first call `aggregate_abi_scope`.
pub(super) fn trust_cg_abi_target(arch_desc: &str) -> Option<TrustCgAbiTarget> {
    match arch_desc {
        "aarch64" | "arm64" => Some(TrustCgAbiTarget::AArch64),
        "x86_64" => Some(TrustCgAbiTarget::X86_64),
        "wasm32" => Some(TrustCgAbiTarget::Wasm32),
        _ => None,
    }
}

/// The wasm-parameter lanes trust-cg's wasm ABI (`trust_cg_codegen::wasm`,
/// `lower/abi.rs`) gives ONE declared trust-ir value: a scalar is one parameter
/// whose width is its WASM carrier (`i32` for every integer up to 32 bits and
/// every pointer, `i64`/`f32`/`f64` for their own), a 128-bit integer two
/// `i64`s, and a single-scalar aggregate its one scalar. Anything else is passed
/// by ADDRESS (an argument) or returned through `sret` (a return) — never as
/// its lanes. Read from the trust-ir type, not the LIR one, because LIR widens
/// a pointer to 64 bits and wasm does not.
fn wasm_trust_ir_lanes(
    ty: &TrustIrTy,
    is_return: bool,
    lane_types: &[TrustIrTy],
) -> Result<ReturnPlacement, String> {
    let lane = |class, bytes| {
        ReturnPlacement::Registers(vec![AbiRegLane {
            class,
            bytes,
            offset: 0,
        }])
    };
    let by_memory = if is_return {
        ReturnPlacement::CallerBuffer
    } else {
        ReturnPlacement::StackByValue
    };
    Ok(match ty {
        TrustIrTy::Bool
        | TrustIrTy::I8
        | TrustIrTy::U8
        | TrustIrTy::I16
        | TrustIrTy::U16
        | TrustIrTy::I32
        | TrustIrTy::U32
        | TrustIrTy::Isize
        | TrustIrTy::Usize
        | TrustIrTy::Char
        | TrustIrTy::Ptr
        | TrustIrTy::PtrConst(_)
        | TrustIrTy::PtrMut(_)
        | TrustIrTy::Ref(_)
        | TrustIrTy::RefMut(_)
        | TrustIrTy::Rc(_)
        | TrustIrTy::Func(_) => lane(AbiRegClass::Integer, 4),
        TrustIrTy::I64 | TrustIrTy::U64 => lane(AbiRegClass::Integer, 8),
        TrustIrTy::F32 => lane(AbiRegClass::Float, 4),
        TrustIrTy::F64 => lane(AbiRegClass::Float, 8),
        TrustIrTy::I128 | TrustIrTy::U128 if is_return => ReturnPlacement::CallerBuffer,
        TrustIrTy::I128 | TrustIrTy::U128 => ReturnPlacement::Registers(vec![
            AbiRegLane {
                class: AbiRegClass::Integer,
                bytes: 8,
                offset: 0,
            },
            AbiRegLane {
                class: AbiRegClass::Integer,
                bytes: 8,
                offset: 8,
            },
        ]),
        // A lane tuple: a singleton only with exactly one element (every lane
        // of a bridge slot tuple is non-empty), and then that element.
        TrustIrTy::Tuple(elems) if elems.len() == 1 => {
            wasm_trust_ir_lanes(&elems[0], is_return, lane_types)?
        }
        TrustIrTy::Array(elem, 1) => match lane_types.get(elem.0 as usize) {
            Some(elem) => wasm_trust_ir_lanes(elem, is_return, lane_types)?,
            None => by_memory,
        },
        _ => by_memory,
    })
}

/// Lane agreement on wasm32 is EXACT: a lane's width is the wasm parameter's
/// TYPE (`i32` vs `i64`), so a wider carrier is not conformant there — it is a
/// different function signature, which `wasm-ld` would bind to a trapping stub.
/// `lanes_disagreement` checks class, count and offset and allows a wider
/// carrier; this adds the exact-width rule on top for the wasm target.
pub(super) fn lanes_disagreement_for(
    target: TrustCgAbiTarget,
    required: &[AbiRegLane],
    carried: &[AbiRegLane],
) -> Option<String> {
    if let Some(detail) = lanes_disagreement_in(Some(target), required, carried) {
        return Some(detail);
    }
    if target == TrustCgAbiTarget::Wasm32 {
        for (index, (want, got)) in required.iter().zip(carried).enumerate() {
            if want.bytes != got.bytes {
                return Some(format!(
                    "lane {index}: rustc's wasm parameter carries {} byte(s) and trust-cg's \
                     carries {} — a different wasm value type",
                    want.bytes, got.bytes
                ));
            }
        }
    }
    None
}

/// rustc's placement restated in what LLVM's wasm32 lowering makes of it: an
/// INTEGER lane wider than 8 bytes (a `PassMode::Cast` of a one-field `i128`
/// aggregate to one 16-byte integer register) is legalized as `i64` halves,
/// low half first, exactly as a 128-bit scalar is; a RETURN that then needs
/// more than one lane (a `PassMode::Pair`, a 128-bit integer, a
/// multi-register cast) comes back through a hidden `sret` buffer, because
/// the wasm32 C ABI returns at most one value. Arguments keep their lanes —
/// each becomes its own wasm parameter.
pub(super) fn rustc_placement_for_target(
    target: TrustCgAbiTarget,
    placement: Option<ReturnPlacement>,
    is_return: bool,
) -> Option<ReturnPlacement> {
    match (target, placement) {
        (TrustCgAbiTarget::Wasm32, Some(ReturnPlacement::Registers(lanes))) => {
            let lanes: Vec<AbiRegLane> = lanes
                .into_iter()
                .flat_map(|lane| {
                    let halves = if lane.class == AbiRegClass::Integer && lane.bytes > 8 {
                        lane.bytes.div_ceil(8)
                    } else {
                        1
                    };
                    (0..halves).map(move |half| AbiRegLane {
                        bytes: if halves == 1 {
                            lane.bytes
                        } else {
                            (lane.bytes - half * 8).min(8)
                        },
                        offset: lane.offset + half * 8,
                        ..lane
                    })
                })
                .collect();
            if is_return && lanes.len() > 1 {
                return Some(ReturnPlacement::CallerBuffer);
            }
            // Each lane becomes a wasm parameter of its carrier type: an integer
            // of up to 4 bytes (or a pointer) an `i32`, of 5-8 bytes an `i64`.
            Some(ReturnPlacement::Registers(
                lanes
                    .into_iter()
                    .map(|lane| AbiRegLane {
                        bytes: match lane.class {
                            AbiRegClass::Integer if lane.bytes <= 4 => 4,
                            AbiRegClass::Integer => 8,
                            _ => lane.bytes,
                        },
                        ..lane
                    })
                    .collect(),
            ))
        }
        (_, placement) => placement,
    }
}

/// Facts captured from the actual rustc target/FnAbi and the compiled host.
/// Keeping this input concrete permits testing the policy without a TyCtxt;
/// it is not a substitute compiler or an alternate source of ABI authority.
#[derive(Clone, Copy, Debug)]
pub(super) struct AggregateAbiScope<'a> {
    pub(super) arch: &'a str,
    pub(super) target_os: &'a str,
    pub(super) is_like_windows: bool,
    pub(super) is_like_darwin: bool,
    pub(super) host_os: &'a str,
    pub(super) pointer_bytes: u64,
    pub(super) conv: CanonAbi,
    pub(super) c_variadic: bool,
}

/// Admit only the native ABI families this bridge currently emits for the new
/// aggregate/carrier/sret routes. `Compiler::new` selects its OS family from
/// the compiled host, not rustc's requested triple; cross-family compilation
/// therefore cannot be admitted by target architecture or equal lane lists.
///
/// C and ordinary Rust use the platform C register convention. RustCold,
/// RustPreserveNone and RustTail do NOT, despite all being "rustic". Explicit
/// SysV64 agrees only on x86-64/System V; Win64/Vectorcall cannot inherit that
/// agreement. CallerBuffer equality likewise says nothing about X8/RDI/RCX.
/// This is a refusal boundary, not a claim of general platform qualification.
pub(super) fn aggregate_abi_scope(
    scope: AggregateAbiScope<'_>,
) -> Result<TrustCgAbiTarget, String> {
    let refuse = |reason: &str| {
        format!(
            "[TCG-AGGREGATE-ABI-SCOPE] {reason}; aggregate/carrier/hidden-return-buffer \
             ABI is not admitted for target {}/{} (windows={}, darwin={}, pointer_bytes={}), \
             host {}, convention {:?}, variadic={}. Compiler::new currently selects the \
             host OS family. Refusing this ABI, not asserting that the whole platform is \
             unsupported; scalar-only paths are unchanged.",
            scope.arch,
            scope.target_os,
            scope.is_like_windows,
            scope.is_like_darwin,
            scope.pointer_bytes,
            scope.host_os,
            scope.conv,
            scope.c_variadic,
        )
    };
    let target = trust_cg_abi_target(scope.arch)
        .ok_or_else(|| refuse("the architecture has no aggregate lane model"))?;
    if target == TrustCgAbiTarget::Wasm32 {
        // The wasm object lane's ABI is the target's, not the host's: nothing
        // here depends on the OS family `Compiler::new` selects.
        if scope.pointer_bytes != 4 {
            return Err(refuse("the wasm aggregate lanes require 32-bit pointers"));
        }
        if scope.c_variadic {
            return Err(refuse(
                "variadic aggregate calling conventions are outside this scope",
            ));
        }
        return match scope.conv {
            CanonAbi::C | CanonAbi::Rust => Ok(target),
            _ => Err(refuse(
                "the canonical calling convention is not the emitted wasm convention",
            )),
        };
    }
    if scope.is_like_windows {
        return Err(refuse(
            "Windows aggregate calling conventions are not modeled by this gate",
        ));
    }
    let native_family = match scope.host_os {
        "linux" => scope.target_os == "linux" && !scope.is_like_darwin,
        "macos" => scope.is_like_darwin,
        _ => false,
    };
    if !native_family {
        return Err(refuse(
            "the requested target does not match a modeled native OS/ABI family",
        ));
    }
    if scope.pointer_bytes != 8 {
        return Err(refuse("the aggregate carriers require 64-bit pointers"));
    }
    if scope.c_variadic {
        return Err(refuse(
            "variadic aggregate calling conventions are outside this scope",
        ));
    }
    match scope.conv {
        CanonAbi::C | CanonAbi::Rust => Ok(target),
        CanonAbi::X86(X86Call::SysV64) if target == TrustCgAbiTarget::X86_64 => Ok(target),
        _ => Err(refuse(
            "the canonical calling convention is not the emitted native convention",
        )),
    }
}

/// Translate one declared trust-ir ABI type into the LIR type the backend will
/// classify. A type the adapter cannot translate is refused here rather than
/// silently skipping the comparison.
/// `lane_types` is the module's `types` table. A memory-slot ABI type spells a
/// uniform lane tuple as `Ty::Array(TyId, n)` (an O(1) spelling of the same
/// type — see `memory_slot_lane_ty`), and that `TyId` indexes this table, so the
/// gate cannot resolve the declared type without it.
fn lower_ty(ty: &TrustIrTy, lane_types: &[TrustIrTy]) -> Result<LowerType, String> {
    translate_type_with_tables(ty, &[], lane_types).map_err(|err| {
        format!(
            "the declared trust-ir ABI type `{ty:?}` does not translate to a backend type \
             ({err:?}), so the register placement it would receive cannot be stated. Failing \
             closed."
        )
    })
}

/// Where trust-cg will place the value returned by a function whose DECLARED
/// trust-ir return list is `returns`.
///
/// An EMPTY return list means the value does not come back as a return value at
/// all: the bridge has already lowered it into the hidden caller-allocated
/// buffer parameter (`sret_return_plan_for_abi`), so the placement is the
/// buffer. (A genuinely valueless function never reaches this gate — it engages
/// only for a non-zero-sized by-value aggregate.)
pub(super) fn trust_cg_return_placement(
    target: TrustCgAbiTarget,
    returns: &[TrustIrTy],
    value_offsets: &[u64],
    lane_types: &[TrustIrTy],
) -> Result<ReturnPlacement, String> {
    if returns.is_empty() {
        return Ok(ReturnPlacement::CallerBuffer);
    }
    // Each declared return VALUE carries bytes from a stated offset in the
    // returned value. A single value always starts at 0; a MULTI-value return
    // (the two-register `PassMode::Pair` lane) states its own lane offsets,
    // because `classify_returns` allocates registers and knows nothing about
    // which bytes of the aggregate each value came from. Synthesising them from
    // the carriers' widths is what this gate did first, and it reported
    // `Option<u8>`'s second lane at offset 4 (the width of the `w1` carrier)
    // instead of 1 — a false refusal on 168 `core` roots, measured 2026-09-11.
    if value_offsets.len() != returns.len() {
        return Err(format!(
            "{} declared return value(s) but {} stated value offset(s); the gate will not \
             synthesise the missing ones.",
            returns.len(),
            value_offsets.len()
        ));
    }
    let lir: Vec<LowerType> = returns
        .iter()
        .map(|ty| lower_ty(ty, lane_types))
        .collect::<Result<_, _>>()?;
    match target {
        TrustCgAbiTarget::AArch64 => {
            // THE BACKEND'S OWN CLASSIFIER, not a mirror of it: this is the
            // function `isel::select_return` calls to decide the registers.
            let locs = AppleAArch64ABI::classify_returns(&lir);
            if locs.len() != lir.len() {
                return Err(format!(
                    "trust-cg's AArch64 return classifier produced {} location(s) for {} \
                     declared return value(s); failing closed.",
                    locs.len(),
                    lir.len()
                ));
            }
            let mut lanes = Vec::new();
            for (loc, base) in locs.iter().zip(value_offsets) {
                match aarch64_location_lanes(loc)? {
                    ReturnPlacement::Registers(mut l) => {
                        // Each value's own lanes are relative to that value;
                        // shift them by the value's STATED offset in the
                        // returned aggregate.
                        for lane in &mut l {
                            lane.offset += *base;
                        }
                        lanes.append(&mut l);
                    }
                    other => {
                        if locs.len() == 1 {
                            return Ok(other);
                        }
                        return Err(format!(
                            "trust-cg's AArch64 return classifier placed one value of a \
                             multi-value return in {}; this gate models only register lanes \
                             for that shape. Failing closed.",
                            other.describe()
                        ));
                    }
                }
            }
            Ok(ReturnPlacement::Registers(lanes))
        }
        TrustCgAbiTarget::X86_64 => {
            if lir.len() == 1 {
                return x86_64_type_lanes(&lir[0]);
            }
            x86_64_scalar_return_lanes(&lir, value_offsets)
        }
        TrustCgAbiTarget::Wasm32 => {
            // Several declared values travel through the sret buffer.
            if returns.len() == 1 {
                return wasm_trust_ir_lanes(&returns[0], true, lane_types);
            }
            Ok(ReturnPlacement::CallerBuffer)
        }
    }
}

/// Where trust-cg's System V x86-64 selector places a MULTI-value scalar
/// return (the two-register `PassMode::Pair` lane): THE BACKEND'S OWN
/// CLASSIFIER, `x86_scalar_return_result_regs` — the function `lower_return`
/// and the call-site result metadata share — never a mirror of it. Integer
/// results take RAX then RDX and SSE results XMM0 then XMM1, each class from
/// its own sequence. A register's defined width is the lane's byte count and
/// the value's STATED offset is the lane's offset, exactly as the AArch64 arm
/// shifts its classifier's lanes.
///
/// A 128-bit value takes the RAX:RDX pair, i.e. two registers for one value;
/// the scalar-pair return plan declines `I128`, and this gate refuses the
/// shape rather than guess which half rustc's offset describes.
fn x86_64_scalar_return_lanes(
    lir: &[LowerType],
    value_offsets: &[u64],
) -> Result<ReturnPlacement, String> {
    // The selector's file now runs past RAX:RDX / XMM0:XMM1 (5e06c59a0: RCX, RSI,
    // ... and XMM2-XMM7), but that extension is TrustCG's INTERNAL multi-result
    // convention, admitted only for `Fast`/`Cold` edges; `[TCG-X86-MULTI-RESULT]`
    // refuses it for `C` and `Rust`. This gate describes a rustc boundary, whose
    // Rust ABI returns at most RAX:RDX, so a return that exhausts System V's C
    // return file has no placement here and is refused rather than reported in
    // registers no rustc-side caller or callee reads.
    if x86_sysv_returns_exceed_c_return_file(lir) {
        return Err(format!(
            "this {}-value return ({lir:?}) exhausts System V's C return file (RAX,RDX / \
             XMM0,XMM1); the registers past it are TrustCG's internal multi-result \
             convention, which a rustc boundary never uses. Failing closed.",
            lir.len()
        ));
    }
    let regs = x86_scalar_return_result_regs(lir, X86CallAbi::SystemV).ok_or_else(|| {
        format!(
            "trust-cg's System V x86-64 scalar-return classifier refuses this {}-value return \
             ({lir:?}); failing closed.",
            lir.len()
        )
    })?;
    if regs.len() != lir.len() {
        return Err(format!(
            "trust-cg's System V x86-64 scalar-return classifier produced {} register(s) for \
             {} declared return value(s) (a 128-bit value takes two); this gate models one \
             register per value. Failing closed.",
            regs.len(),
            lir.len()
        ));
    }
    let mut lanes = Vec::with_capacity(regs.len());
    for (reg, offset) in regs.iter().zip(value_offsets) {
        let class = if reg.is_sse() {
            if reg.defined_bits == 128 {
                AbiRegClass::Vector
            } else {
                AbiRegClass::Float
            }
        } else {
            AbiRegClass::Integer
        };
        if reg.defined_bits % 8 != 0 || reg.defined_bits == 0 {
            return Err(format!(
                "trust-cg's System V x86-64 scalar-return classifier reports {} defined bit(s) \
                 for a return register; this gate models whole bytes only. Failing closed.",
                reg.defined_bits
            ));
        }
        lanes.push(AbiRegLane {
            class,
            bytes: u64::from(reg.defined_bits) / 8,
            offset: *offset,
        });
    }
    Ok(ReturnPlacement::Registers(lanes))
}

/// Where trust-cg will place ONE declared by-value parameter.
///
/// The parameter is classified IN ISOLATION — as if it were the first argument:
/// the class of a single aggregate does not depend on what precedes it, while
/// the register NUMBERS do. This per-argument gate therefore decides the
/// argument's class and lanes (its MODE), and claims nothing about NUMBERING,
/// exhaustion or stack offsets — those are the whole-signature placement
/// check's (`signature_byte_homes` / `signature_placement_disagreement`, run on
/// every declaration by `lib.rs` `check_signature_placement`), which places the
/// whole value list at once.
pub(super) fn trust_cg_param_placement(
    target: TrustCgAbiTarget,
    params: &[TrustIrTy],
    value_offsets: &[u64],
    lane_types: &[TrustIrTy],
) -> Result<ReturnPlacement, String> {
    if params.is_empty() || params.len() != value_offsets.len() {
        return Err(format!(
            "{} declared parameter value(s) but {} stated value offset(s); the gate will not \
             synthesise the missing ones.",
            params.len(),
            value_offsets.len()
        ));
    }
    let lir: Vec<LowerType> = params
        .iter()
        .map(|ty| lower_ty(ty, lane_types))
        .collect::<Result<_, _>>()?;
    match target {
        TrustCgAbiTarget::AArch64 => {
            // One classification over ALL the values this argument declares, so
            // a two-value `PassMode::Pair` argument sees the same allocation the
            // backend performs (each value takes the next register of its class).
            let locs = AppleAArch64ABI::classify_params(&lir);
            if locs.len() != lir.len() {
                return Err(format!(
                    "trust-cg's AArch64 parameter classifier produced {} location(s) for {} \
                     declared parameter value(s); failing closed.",
                    locs.len(),
                    lir.len()
                ));
            }
            let mut lanes = Vec::new();
            for (loc, base) in locs.iter().zip(value_offsets) {
                match aarch64_location_lanes(loc)? {
                    ReturnPlacement::Registers(mut l) => {
                        for lane in &mut l {
                            lane.offset += *base;
                        }
                        lanes.append(&mut l);
                    }
                    other => {
                        if locs.len() == 1 {
                            return Ok(other);
                        }
                        return Err(format!(
                            "trust-cg's AArch64 parameter classifier placed one value of a \
                             multi-value argument in {}; this gate models only register lanes \
                             for that shape. Failing closed.",
                            other.describe()
                        ));
                    }
                }
            }
            Ok(ReturnPlacement::Registers(lanes))
        }
        TrustCgAbiTarget::X86_64 => x86_64_param_lanes(&lir, value_offsets),
        TrustCgAbiTarget::Wasm32 => {
            if params.len() == 1 {
                return wasm_trust_ir_lanes(&params[0], false, lane_types);
            }
            let mut lanes = Vec::new();
            for (ty, base) in params.iter().zip(value_offsets) {
                match wasm_trust_ir_lanes(ty, false, lane_types)? {
                    ReturnPlacement::Registers(mut l) => {
                        for lane in &mut l {
                            lane.offset += *base;
                        }
                        lanes.append(&mut l);
                    }
                    other => {
                        return Err(format!(
                            "trust-cg's wasm ABI passes one value of a multi-value argument \
                             in {}; this gate models only parameter lanes for that shape. \
                             Failing closed.",
                            other.describe()
                        ));
                    }
                }
            }
            Ok(ReturnPlacement::Registers(lanes))
        }
    }
}

/// The lanes the x86-64 SELECTOR gives the values of ONE argument, read from
/// its own System V placement (`trust_cg_lower::x86_sysv_param_locations`,
/// the function `lower_call` and `lower_formal_arguments` both call) with the
/// values first in the argument list, so a register location is the class /
/// extent / offset question this per-argument gate asks. A lone value the
/// selector passes on the stack from position 0 is a MEMORY-class aggregate
/// (`byval`); a value of a MULTI-value argument that would go to the stack is
/// refused, because this gate models only register lanes for that shape.
fn x86_64_param_lanes(lir: &[LowerType], value_offsets: &[u64]) -> Result<ReturnPlacement, String> {
    use trust_cg_lower::X86ParamLocation as Loc;
    let locations = trust_cg_lower::x86_sysv_param_locations(lir, false).map_err(|err| {
        format!(
            "trust-cg's System V x86-64 argument placement refuses {lir:?}: {err}; failing \
             closed."
        )
    })?;
    if locations.len() != lir.len() {
        return Err(format!(
            "trust-cg's System V x86-64 argument placement produced {} location(s) for {} \
             declared parameter value(s); failing closed.",
            locations.len(),
            lir.len()
        ));
    }
    if let [Loc::Stack { .. }] = locations.as_slice() {
        return Ok(ReturnPlacement::StackByValue);
    }
    let mut lanes = Vec::new();
    for ((location, ty), base) in locations.iter().zip(lir).zip(value_offsets) {
        let base = *base;
        match location {
            Loc::Gpr(_) => lanes.push(AbiRegLane {
                class: AbiRegClass::Integer,
                bytes: u64::from(ty.bytes()),
                offset: base,
            }),
            Loc::GprPair { .. } => {
                for half in 0..2 {
                    lanes.push(AbiRegLane {
                        class: AbiRegClass::Integer,
                        bytes: 8,
                        offset: base + half * 8,
                    });
                }
            }
            Loc::Xmm(_) => lanes.push(AbiRegLane {
                class: if *ty == LowerType::V128 {
                    AbiRegClass::Vector
                } else {
                    AbiRegClass::Float
                },
                bytes: u64::from(ty.bytes()),
                offset: base,
            }),
            Loc::Lanes(eightbytes) => {
                for lane in eightbytes {
                    lanes.push(AbiRegLane {
                        class: match (lane.sse, lane.valid_bytes) {
                            (false, _) => AbiRegClass::Integer,
                            (true, 16) => AbiRegClass::Vector,
                            (true, _) => AbiRegClass::Float,
                        },
                        bytes: u64::from(lane.valid_bytes),
                        offset: base + u64::from(lane.offset),
                    });
                }
            }
            Loc::Stack { .. } => {
                return Err(format!(
                    "trust-cg's System V x86-64 placement puts one value of a multi-value \
                     argument ({ty:?}) on the stack; this gate models only register lanes for \
                     that shape. Failing closed."
                ));
            }
        }
    }
    Ok(ReturnPlacement::Registers(lanes))
}

/// The lanes rustc's own `FnAbi` requires for one argument or return.
///
/// `Ok(None)` means rustc passes NOTHING (`PassMode::Ignore`: a ZST or
/// uninhabited slot), which is not a placement and is compared separately.
///
/// Every number here is read from rustc: the `Reg`s of a `CastTarget` (each with
/// its own `RegKind` and `Size`), the `Scalar`s of a `ScalarPair` layout, and
/// the `BackendRepr` of a `Direct`. Nothing is re-derived from the Rust type,
/// its name or its size.
pub(super) fn rustc_placement<'a, C: HasDataLayout>(
    cx: &C,
    mode: &PassMode,
    layout_repr: BackendRepr,
    layout_size: u64,
    tag: &'a str,
    what: &'a str,
) -> Result<Option<ReturnPlacement>, String> {
    let refuse = |why: String| -> Result<Option<ReturnPlacement>, String> {
        Err(format!(
            "{tag} rustc's FnAbi places this {what} with a convention this gate does not state \
             exactly: {why}. Failing closed rather than comparing against a guess. Options: \
             (1) pass or return the value through an explicit out-parameter \
             (`fn f(out: &mut T)`), which crosses no register convention; (2) give the type a \
             scalar or scalar-pair shape; (3) teach `abi_reg_lanes::rustc_placement` this \
             `PassMode` and give trust-cg's classifier the matching lanes."
        ))
    };
    // ONE scalar can still need TWO registers: AAPCS64 §5.4 and the AMD64 psABI
    // §3.2.3 both split a 128-bit INTEGER across two general-purpose registers
    // (`x0`/`x1`, `RAX`/`RDX`), which is also what LLVM emits for an `i128`
    // return — and exactly what trust-cg's own classifier reports for its
    // `I128` type (`ArgLocation::RegPair`). Reporting one 16-byte lane here
    // would have made `Option<NonZero<u128>>` — a `PassMode::Direct` over a
    // 128-bit `BackendRepr::Scalar` — look like a disagreement when the two
    // sides in fact place it identically. Measured in the `core` census.
    let scalar_lanes = |scalar: Scalar, offset: u64| -> Result<Vec<AbiRegLane>, String> {
        let class = match scalar.primitive() {
            Primitive::Int(..) | Primitive::Pointer(..) => AbiRegClass::Integer,
            Primitive::Float(float) => {
                crate::abi_primitive::ieee_bits(float)
                    .map_err(|why| format!("{tag} rustc's FnAbi {what} uses {why}"))?;
                AbiRegClass::Float
            }
        };
        let bytes = scalar.size(cx).bytes();
        if class == AbiRegClass::Integer && bytes > 8 && bytes % 8 == 0 {
            return Ok((0..bytes / 8)
                .map(|index| AbiRegLane {
                    class,
                    bytes: 8,
                    offset: offset + index * 8,
                })
                .collect());
        }
        Ok(vec![AbiRegLane {
            class,
            bytes,
            offset,
        }])
    };
    let indirect = || {
        let view = match crate::indirect_abi::checked(mode) {
            Ok(Some(view)) => view,
            Ok(None) => {
                return refuse("an indirect descriptor whose payload could not be read".to_owned());
            }
            Err(reason) => return refuse(reason),
        };
        Ok(Some(if view.kind == crate::indirect_abi::Kind::OnStack {
            ReturnPlacement::StackByValue
        } else {
            ReturnPlacement::CallerBuffer
        }))
    };
    Ok(match mode {
        PassMode::Ignore => None,
        PassMode::Direct(_) => match layout_repr {
            BackendRepr::Scalar(scalar) => {
                Some(ReturnPlacement::Registers(scalar_lanes(scalar, 0)?))
            }
            // A SIMD vector goes in one vector register of the value's own width.
            BackendRepr::SimdVector { .. } => Some(ReturnPlacement::Registers(vec![AbiRegLane {
                class: AbiRegClass::Vector,
                bytes: layout_size,
                offset: 0,
            }])),
            // `PassMode::Direct` on an aggregate is the documented wasm leak of
            // LLVM implementation details (rust-lang/rust#115666). Refuse.
            other => {
                return refuse(format!(
                    "`PassMode::Direct` over a non-scalar layout ({other:?})"
                ));
            }
        },
        PassMode::Pair(..) => {
            let Some(pair) = crate::scalar_pair::view(layout_repr) else {
                return refuse(format!(
                    "`PassMode::Pair` over a non-`ScalarPair` layout ({layout_repr:?})"
                ));
            };
            // ABI memory order and offset, including niche-encoded enums.
            let b_offset = pair.second_offset(cx).bytes();
            let mut lanes = scalar_lanes(pair.a, 0)?;
            lanes.extend(scalar_lanes(pair.b, b_offset)?);
            Some(ReturnPlacement::Registers(lanes))
        }
        PassMode::Cast { .. } => {
            let Some(view) = crate::cast_abi::view(mode) else {
                return refuse("`PassMode::Cast` payload could not be read".to_owned());
            };
            if let Some(reason) = view.padding_refusal() {
                // Leading dummy arguments consume additional ABI positions;
                // the bridge emits none of them, regardless of the count.
                return refuse(reason);
            }
            let cast = view.target;
            let mut lanes = Vec::new();
            let mut offset = 0u64;
            for reg in cast.prefix.iter() {
                lanes.push(AbiRegLane {
                    class: reg_kind_class(reg.kind)
                        .map_err(|why| format!("{tag} rustc's FnAbi {what} uses {why}"))?,
                    bytes: reg.size.bytes(),
                    offset,
                });
                offset += reg.size.bytes();
            }
            if let Some(rest_offset) = cast.rest_offset {
                if rest_offset.bytes() < offset {
                    return refuse(
                        "`CastTarget::rest_offset` overlaps the prefix registers".to_owned(),
                    );
                }
                offset = rest_offset.bytes();
            }
            let unit = cast.rest.unit.size.bytes();
            if unit == 0 {
                return refuse("`CastTarget::rest` has a zero-sized unit register".to_owned());
            }
            let total = cast.rest.total.bytes();
            let units = total.div_ceil(unit);
            for index in 0..units {
                // The doc on `Uniform::total`: only the LAST element may be
                // shorter, and only for an INTEGER unit. Its live extent is what
                // the ABI requires; the register it rides in is `unit` wide.
                let live = (total - index * unit).min(unit);
                lanes.push(AbiRegLane {
                    class: reg_kind_class(cast.rest.unit.kind)
                        .map_err(|why| format!("{tag} rustc's FnAbi {what} uses {why}"))?,
                    bytes: live,
                    offset: offset + index * unit,
                });
            }
            if lanes.is_empty() {
                return refuse("`PassMode::Cast` with no registers at all".to_owned());
            }
            Some(ReturnPlacement::Registers(lanes))
        }
        PassMode::Indirect { .. } => return indirect(),
        #[cfg(rustc_indirect_modes)]
        PassMode::IndirectUnsized { .. } => return indirect(),
    })
}

fn reg_kind_class(kind: RegKind) -> Result<AbiRegClass, &'static str> {
    use crate::abi_primitive::{RegisterFile, register_file};
    Ok(match register_file(kind)? {
        RegisterFile::Integer => AbiRegClass::Integer,
        RegisterFile::Float => AbiRegClass::Float,
        RegisterFile::Vector => AbiRegClass::Vector,
    })
}

/// The lane an argument rustc passes `PassMode::Indirect { on_stack: false }`
/// occupies at the call edge. That mode does not place the value's bytes at all:
/// it passes ONE POINTER to a copy the caller made (`rustc_codegen_llvm` lowers
/// it to a single `ptr` IR argument), which the target places like any other
/// pointer — one INTEGER lane of pointer width. The indirect argument lane
/// (`indirect_arg_param_plan`) declares exactly one `Ptr` for it, and the
/// argument gate compares that declaration against this lane.
pub(super) fn indirect_argument_pointer_lanes(pointer_bytes: u64) -> Vec<AbiRegLane> {
    vec![AbiRegLane {
        class: AbiRegClass::Integer,
        bytes: pointer_bytes,
        offset: 0,
    }]
}

/// Why the argument-ABI gate refuses a by-value argument on rustc's placement
/// MODE alone, before any lane is compared. Each arm is a placement the module's
/// `StructPassingPolicy::NativeC` stamp would otherwise claim with nothing having
/// checked it, which is why none of them is a silent accept any more.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum ArgPlacementRefusal {
    /// rustc passes NOTHING for the argument (`PassMode::Ignore`, a zero-sized
    /// value) while the bridge declared an ABI value for it: the two signatures
    /// would not even have the same number of values.
    IgnoredButDeclared,
    /// rustc passes a POINTER to a caller-made copy (`PassMode::Indirect {
    /// on_stack: false }`) on a target without the indirect argument lane
    /// (`rust_abi_indirect_lane_target`), so nothing declares that pointer.
    /// Unreachable while `check_aggregate_abi_scope` admits only lane targets;
    /// it is refused so that the two scopes cannot drift apart silently.
    CallerBufferOffLane,
    /// rustc copies the argument BY VALUE into the outgoing argument area
    /// (`PassMode::Indirect { on_stack: true }`, LLVM `byval`) on a target that
    /// is not x86-64 System V, where no rule states that trust-cg places it the
    /// same way.
    StackByValueOffSysV,
}

impl ArgPlacementRefusal {
    pub(super) fn describe(self) -> &'static str {
        match self {
            ArgPlacementRefusal::IgnoredButDeclared => {
                "rustc's FnAbi passes no value for it (`PassMode::Ignore`), but the bridge \
                 declared an ABI value, so the two signatures would disagree in arity"
            }
            ArgPlacementRefusal::CallerBufferOffLane => {
                "rustc's FnAbi passes it as a POINTER to a caller-made copy \
                 (`PassMode::Indirect { on_stack: false }`), and this target has no indirect \
                 argument lane (`rust_abi_indirect_lane_target`) to declare that pointer"
            }
            ArgPlacementRefusal::StackByValueOffSysV => {
                "rustc's FnAbi copies it by value into the outgoing argument area \
                 (`PassMode::Indirect { on_stack: true }`, LLVM `byval`), which only the \
                 x86-64 System V rule admits, and this target is not x86-64 System V"
            }
        }
    }
}

/// What the argument-ABI gate does with one by-value argument, decided from
/// rustc's placement MODE alone. See [`arg_memory_placement_verdict`].
#[derive(Clone, PartialEq, Eq, Debug)]
pub(super) enum ArgPlacementVerdict {
    /// rustc places the argument in these register lanes: compare trust-cg's
    /// classifier placement of the declared values against them, lane for lane.
    CompareRegisters(Vec<AbiRegLane>),
    /// rustc passes a POINTER to a caller-made copy and the bridge declares
    /// exactly that one pointer — the indirect argument lane
    /// (`indirect_arg_param_plan`), trust-ir §17's pre-lowered crossing: compare
    /// the pointer's one integer lane (`indirect_argument_pointer_lanes`).
    ComparePointerLane,
    /// rustc passes a POINTER to a caller-made copy and the bridge declares the
    /// value itself: admitted only where trust-cg's OWN classifier also passes
    /// the declared composite as a caller-made copy whose address travels as an
    /// ordinary pointer argument (AAPCS64 §6.8.2 B.4, a C-ABI composite over 16
    /// bytes), refused otherwise.
    CompareCallerBufferWithClassifier,
    /// x86-64 System V `byval` (rustc `Indirect { on_stack: true }`), which only
    /// C-ABI arguments reach: a MEMORY-class aggregate, or one that no longer
    /// fits the remaining registers. The MODE is admitted here (trust-cg's
    /// x86-64 classifier also puts both on the stack as a copy); WHERE the copy
    /// lands is compared per byte by the whole-signature placement check, which
    /// places rustc's byval image in memory whatever its class
    /// (`rustc_backend_values`, `x86_sysv_param_locations_with_byval`).
    CompareSysVByvalInSignature,
    /// Refused on the mode alone.
    Refuse(ArgPlacementRefusal),
}

/// THE ONE TABLE of what the argument-ABI gate does with a by-value argument
/// before comparing lanes. It replaced two silent accepts: an off-lane
/// caller-made copy returned `Ok`, and every other non-register mode fell
/// through a `_ => Ok(())`. Pure, so every cell is a unit test
/// (`arg_memory_placement_verdict_table`).
///
/// * `target` — the classifier model for the target architecture
///   (`trust_cg_abi_target`).
/// * `lane_target` — whether the target serves the indirect argument lane
///   (`rust_abi_indirect_lane_target`: x86-64 or AArch64, not Windows).
/// * `rustc` — rustc's own placement of the argument (`rustc_placement`;
///   `None` is `PassMode::Ignore`).
/// * `declared_is_single_ptr` — the bridge declared exactly one `Ptr` at
///   offset 0 for the argument.
///
/// A `CompareRegisters` verdict compares each argument IN ISOLATION: class,
/// count, per-lane extent and value offset. Register numbering, exhaustion and
/// stack offsets — every argument's actual home — are the whole-signature
/// placement check's; the two together are the argument half of the module's
/// `NativeC` claim, at the test rung.
pub(super) fn arg_memory_placement_verdict(
    target: Option<TrustCgAbiTarget>,
    lane_target: bool,
    rustc: Option<ReturnPlacement>,
    declared_is_single_ptr: bool,
) -> ArgPlacementVerdict {
    match rustc {
        Some(ReturnPlacement::Registers(lanes)) => ArgPlacementVerdict::CompareRegisters(lanes),
        Some(ReturnPlacement::CallerBuffer) if !lane_target => {
            ArgPlacementVerdict::Refuse(ArgPlacementRefusal::CallerBufferOffLane)
        }
        Some(ReturnPlacement::CallerBuffer) if declared_is_single_ptr => {
            ArgPlacementVerdict::ComparePointerLane
        }
        Some(ReturnPlacement::CallerBuffer) => {
            ArgPlacementVerdict::CompareCallerBufferWithClassifier
        }
        Some(ReturnPlacement::StackByValue)
            if lane_target && target == Some(TrustCgAbiTarget::X86_64) =>
        {
            ArgPlacementVerdict::CompareSysVByvalInSignature
        }
        Some(ReturnPlacement::StackByValue) => {
            ArgPlacementVerdict::Refuse(ArgPlacementRefusal::StackByValueOffSysV)
        }
        None => ArgPlacementVerdict::Refuse(ArgPlacementRefusal::IgnoredButDeclared),
    }
}

/// Compare the lanes rustc REQUIRES against the lanes trust-cg will CARRY.
///
/// `Ok(())` only when they agree lane for lane. The carrier may be WIDER than
/// the requirement in the same class — AAPCS64 §5.4 and the AMD64 psABI both
/// leave a register's bits above the value's width unspecified, so a `w1`
/// requirement is satisfied by an `x1` carrier — but never narrower, never a
/// different class, never a different offset, and never a different count.
/// Lanes carry no extension attribute: an argument rustc EXTENDS (a `bool` is
/// `zeroext`) has a callee that reads the bits above the value, so whoever
/// builds a wider carrier for it must clean those bits itself (the pair lane's
/// `narrow_carrier` / `lane_ext`; a `rust-call` element is its own argument
/// since round 10's untupling, `rust_call_spread`).
pub(super) fn lanes_disagreement(
    required: &[AbiRegLane],
    carried: &[AbiRegLane],
) -> Option<String> {
    lanes_disagreement_in(None, required, carried)
}

/// [`lanes_disagreement`], naming the lanes in `target`'s own terms.
fn lanes_disagreement_in(
    target: Option<TrustCgAbiTarget>,
    required: &[AbiRegLane],
    carried: &[AbiRegLane],
) -> Option<String> {
    if required.len() != carried.len() {
        return Some(format!(
            "rustc requires {} {} lane(s) and trust-cg would emit {}",
            required.len(),
            lane_noun(target),
            carried.len()
        ));
    }
    for (index, (want, got)) in required.iter().zip(carried).enumerate() {
        if want.class != got.class {
            return Some(format!(
                "lane {index}: rustc requires {} and trust-cg would use {}",
                want.class.describe_for(target),
                got.class.describe_for(target)
            ));
        }
        if want.offset != got.offset {
            return Some(format!(
                "lane {index}: rustc takes its bytes from value offset {} and trust-cg would \
                 take them from offset {}",
                want.offset, got.offset
            ));
        }
        if got.bytes < want.bytes {
            return Some(format!(
                "lane {index}: rustc requires {} live byte(s) and trust-cg's carrier holds \
                 only {}",
                want.bytes, got.bytes
            ));
        }
    }
    None
}

// ---------------------------------------------------------------------------
// THE WHOLE-SIGNATURE PLACEMENT CHECK (the pure half; `lib.rs`
// `check_signature_placement` supplies rustc's `FnAbi` and the declaration).
// ---------------------------------------------------------------------------

/// One ABI VALUE of one argument: its backend type, the argument-relative byte
/// offset its first byte carries, and how many of its bytes are the
/// argument's (`live`; a carrier wider than its lane has dead bytes above).
#[derive(Clone, Debug, PartialEq)]
pub(super) struct AbiValue {
    pub(super) ty: LowerType,
    pub(super) offset: u64,
    pub(super) live: u64,
    /// LLVM `byval`: passed by value in memory whatever its class.
    pub(super) byval: bool,
}

impl AbiValue {
    pub(super) fn new(ty: LowerType, offset: u64, live: u64) -> Self {
        Self {
            ty,
            offset,
            live,
            byval: false,
        }
    }
}

/// Where ONE BYTE of an argument lives at the call edge: byte `byte` of an
/// argument register, or the outgoing argument area at `offset`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, PartialOrd, Ord, Hash)]
pub(super) enum ByteHome {
    Gpr { reg: u8, byte: u8 },
    Fpr { reg: u8, byte: u8 },
    Stack { offset: i64 },
}

fn int_lower_type(bytes: u64) -> Option<LowerType> {
    Some(match bytes {
        1 => LowerType::I8,
        2 => LowerType::I16,
        3 | 4 => LowerType::I32,
        5..=8 => LowerType::I64,
        16 => LowerType::I128,
        _ => return None,
    })
}

fn reg_lower_type(kind: RegKind, bytes: u64) -> Option<LowerType> {
    use crate::abi_primitive::{RegisterFile, register_file};
    match register_file(kind).ok()? {
        RegisterFile::Integer => int_lower_type(bytes),
        RegisterFile::Float => match bytes {
            2 => Some(LowerType::F16),
            4 => Some(LowerType::F32),
            8 => Some(LowerType::F64),
            _ => None,
        },
        RegisterFile::Vector => match bytes {
            8 => Some(LowerType::V64),
            16 => Some(LowerType::V128),
            _ => None,
        },
    }
}

fn scalar_lower_type<C: HasDataLayout>(cx: &C, scalar: Scalar) -> Option<LowerType> {
    let bytes = scalar.size(cx).bytes();
    match scalar.primitive() {
        Primitive::Int(..) | Primitive::Pointer(..) => int_lower_type(bytes),
        Primitive::Float(float) => reg_lower_type(
            RegKind::Float,
            crate::abi_primitive::ieee_bits(float).ok()? / 8,
        ),
    }
}

/// An in-memory image of `size` bytes aligned to `align`, for LLVM `byval`.
fn memory_image(size: u64, align: u64) -> Option<LowerType> {
    let elem = match align {
        1 => LowerType::I8,
        2 => LowerType::I16,
        4 => LowerType::I32,
        8 => LowerType::I64,
        16 => LowerType::I128,
        _ => return None,
    };
    if size == 0 || size % align != 0 {
        return None;
    }
    Some(LowerType::Array(
        Box::new(elem),
        u32::try_from(size / align).ok()?,
    ))
}

/// rustc's BACKEND value list for one argument: the values `rustc_codegen_llvm`
/// passes for its `PassMode`, as the calling convention legalizes them.
///
/// * `Direct` over a scalar: that scalar (an `i128` is one value the target
///   places in two registers); over a SIMD vector: one vector value.
/// * `Pair`: its two scalars, the second at rustc's own offset (`b_offset`).
/// * `Cast`: each prefix register as its own value, then the rest — one value
///   of the unit's legalized type (`i24` -> `I32`), or a consecutive BLOCK
///   `[unit x n]` (an HFA / `[i64 x 2]`); a `pad_i32` register is refused.
/// * `Indirect { on_stack: false }`: ONE pointer (and one metadata word).
/// * `Indirect { on_stack: true }` (LLVM `byval`): the value's bytes in memory,
///   of its size AND alignment, whatever its class.
/// * `Ignore`: nothing.
///
/// This is a model of `rustc_codegen_llvm`'s lowering, shared by nothing on the
/// bridge side; its evidence is the cross-backend family matrix
/// (`tests/signature_placement_families_xback.rs`), test rung.
pub(super) fn rustc_backend_values<C: HasDataLayout>(
    cx: &C,
    mode: &PassMode,
    layout_repr: BackendRepr,
    layout_size: u64,
    layout_align: u64,
) -> Result<Vec<AbiValue>, String> {
    let scalar = |s: Scalar, offset: u64| -> Result<AbiValue, String> {
        let ty =
            scalar_lower_type(cx, s).ok_or_else(|| format!("scalar {s:?} has no backend type"))?;
        Ok(AbiValue::new(ty, offset, s.size(cx).bytes()))
    };
    let indirect = || -> Result<Vec<AbiValue>, String> {
        let view = crate::indirect_abi::checked(mode)?
            .ok_or_else(|| "an indirect descriptor whose payload could not be read".to_owned())?;
        if view.kind == crate::indirect_abi::Kind::OnStack {
            let ty = memory_image(layout_size, layout_align).ok_or_else(|| {
                format!("a {layout_size}-byte, {layout_align}-aligned byval image")
            })?;
            Ok(vec![AbiValue {
                ty,
                offset: 0,
                live: layout_size,
                byval: true,
            }])
        } else {
            let mut values = vec![AbiValue::new(LowerType::I64, 0, 8)];
            if view.meta_attrs.is_some() {
                values.push(AbiValue::new(LowerType::I64, 8, 8));
            }
            Ok(values)
        }
    };
    Ok(match mode {
        PassMode::Ignore => Vec::new(),
        PassMode::Direct(_) => match layout_repr {
            BackendRepr::Scalar(s) => vec![scalar(s, 0)?],
            BackendRepr::SimdVector { .. } => {
                let ty = match layout_size {
                    8 => LowerType::V64,
                    16 => LowerType::V128,
                    _ => return Err(format!("a {layout_size}-byte SIMD vector")),
                };
                vec![AbiValue::new(ty, 0, layout_size)]
            }
            other => return Err(format!("`PassMode::Direct` over {other:?}")),
        },
        PassMode::Pair(..) => {
            let Some(pair) = crate::scalar_pair::view(layout_repr) else {
                return Err(format!("`PassMode::Pair` over {layout_repr:?}"));
            };
            let b_offset = pair.second_offset(cx).bytes();
            vec![scalar(pair.a, 0)?, scalar(pair.b, b_offset)?]
        }
        PassMode::Cast { .. } => {
            let Some(view) = crate::cast_abi::view(mode) else {
                return Err("`PassMode::Cast` payload could not be read".to_owned());
            };
            if let Some(reason) = view.padding_refusal() {
                return Err(reason);
            }
            let cast = view.target;
            let mut values = Vec::new();
            let mut offset = 0u64;
            for reg in cast.prefix.iter() {
                let bytes = reg.size.bytes();
                let ty = reg_lower_type(reg.kind, bytes)
                    .ok_or_else(|| format!("a {bytes}-byte {:?} prefix register", reg.kind))?;
                values.push(AbiValue::new(ty, offset, bytes));
                offset += bytes;
            }
            if let Some(rest_offset) = cast.rest_offset {
                offset = rest_offset.bytes();
            }
            let unit = cast.rest.unit.size.bytes();
            let total = cast.rest.total.bytes();
            if unit == 0 || total == 0 {
                return Err("`PassMode::Cast` with an empty rest".to_owned());
            }
            let count = total.div_ceil(unit);
            if count == 1 {
                let ty = reg_lower_type(cast.rest.unit.kind, unit)
                    .ok_or_else(|| format!("a {unit}-byte {:?} cast unit", cast.rest.unit.kind))?;
                values.push(AbiValue::new(ty, offset, total));
            } else {
                let unit_ty = reg_lower_type(cast.rest.unit.kind, unit)
                    .ok_or_else(|| format!("a {unit}-byte {:?} cast unit", cast.rest.unit.kind))?;
                let count = u32::try_from(count).map_err(|_| "cast unit count".to_owned())?;
                values.push(AbiValue::new(
                    LowerType::Array(Box::new(unit_ty), count),
                    offset,
                    total,
                ));
            }
            values
        }
        PassMode::Indirect { .. } => return indirect(),
        #[cfg(rustc_indirect_modes)]
        PassMode::IndirectUnsized { .. } => return indirect(),
    })
}

fn preg_bytes(reg: PReg, lo: u64, hi: u64, base: u64, out: &mut Vec<(u64, ByteHome)>) {
    let n = reg.hw_enc();
    for b in lo..hi {
        let byte = (b - lo) as u8;
        out.push((
            base + b,
            if reg.is_fpr() {
                ByteHome::Fpr { reg: n, byte }
            } else {
                ByteHome::Gpr { reg: n, byte }
            },
        ));
    }
}

/// Every LIVE byte home of one value the AArch64 classifier placed at `loc`.
fn aarch64_value_homes(
    loc: &ArgLocation,
    value: &AbiValue,
    out: &mut Vec<(u64, ByteHome)>,
) -> Result<(), String> {
    // Only the value's live bytes have a home: a carrier wider than its lane
    // (a zero-extended 32-bit carrier for an 8-bit lane) is conformant.
    let size = u64::from(value.ty.bytes()).min(value.live);
    match loc {
        ArgLocation::Ignore => {
            if size != 0 || value.ty.bytes() != 0 {
                return Err("an ignored aggregate argument has live bytes".into());
            }
        }
        ArgLocation::Reg(r) => preg_bytes(*r, 0, size, value.offset, out),
        ArgLocation::RegPair(lo, hi) => {
            preg_bytes(*lo, 0, size.min(8), value.offset, out);
            if size > 8 {
                preg_bytes(*hi, 0, size - 8, value.offset + 8, out);
            }
        }
        ArgLocation::RegSequence(regs) => {
            let n = regs.len() as u64;
            let full = u64::from(value.ty.bytes());
            if n == 0 || full % n != 0 {
                return Err(format!("an HFA of {full} bytes in {n} registers"));
            }
            let w = full / n;
            for (i, r) in regs.iter().enumerate() {
                let lo = i as u64 * w;
                if lo >= size {
                    break;
                }
                preg_bytes(*r, 0, w.min(size - lo), value.offset + lo, out);
            }
        }
        ArgLocation::Stack { offset, .. } => {
            for b in 0..size {
                out.push((
                    value.offset + b,
                    ByteHome::Stack {
                        offset: offset + b as i64,
                    },
                ));
            }
        }
        // The classifier passes the declared composite as a POINTER to a copy:
        // the pointer's 8 bytes are the argument's crossing (rustc's
        // `Indirect` pointer is the same 8 bytes at argument offset 0).
        ArgLocation::Indirect { ptr_reg } => preg_bytes(*ptr_reg, 0, 8, 0, out),
    }
    Ok(())
}

/// Every LIVE byte home of one value the x86-64 selector placed at `loc`.
fn x86_value_homes(
    loc: &trust_cg_lower::X86ParamLocation,
    value: &AbiValue,
    out: &mut Vec<(u64, ByteHome)>,
) {
    use trust_cg_lower::X86ParamLocation as L;
    let size = u64::from(value.ty.bytes()).min(value.live);
    let push = |b: u64, home: ByteHome, out: &mut Vec<(u64, ByteHome)>| {
        out.push((value.offset + b, home));
    };
    match loc {
        L::Gpr(r) => {
            for b in 0..size.min(8) {
                push(
                    b,
                    ByteHome::Gpr {
                        reg: *r,
                        byte: b as u8,
                    },
                    out,
                );
            }
        }
        L::GprPair { lo, hi } => {
            for b in 0..size.min(16) {
                let reg = if b < 8 { *lo } else { *hi };
                push(
                    b,
                    ByteHome::Gpr {
                        reg,
                        byte: (b % 8) as u8,
                    },
                    out,
                );
            }
        }
        L::Xmm(r) => {
            for b in 0..size.min(16) {
                push(
                    b,
                    ByteHome::Fpr {
                        reg: *r,
                        byte: b as u8,
                    },
                    out,
                );
            }
        }
        L::Lanes(lanes) => {
            for lane in lanes {
                for b in 0..u64::from(lane.valid_bytes) {
                    let arg_b = u64::from(lane.offset) + b;
                    if arg_b >= size {
                        continue;
                    }
                    let home = if lane.sse {
                        ByteHome::Fpr {
                            reg: lane.index,
                            byte: b as u8,
                        }
                    } else {
                        ByteHome::Gpr {
                            reg: lane.index,
                            byte: b as u8,
                        }
                    };
                    push(arg_b, home, out);
                }
            }
        }
        L::Stack { offset, .. } => {
            for b in 0..size {
                push(
                    b,
                    ByteHome::Stack {
                        offset: offset + b as i64,
                    },
                    out,
                );
            }
        }
    }
}

/// Per argument, every live byte's home: `values` is one flat ABI value list
/// (the whole signature, in order, WITHOUT a hidden return buffer), `spans` the
/// value index range of each argument, `has_sret` whether a hidden return
/// buffer takes an argument register (RDI on System V; AAPCS64's X8 is not an
/// argument register). The placement is trust-cg's OWN classifier for the
/// target: `AppleAArch64ABI::classify_params_with` with the target's variant,
/// or `x86_sysv_param_locations_with_byval` — the functions the selectors
/// themselves call.
pub(super) fn signature_byte_homes(
    target: TrustCgAbiTarget,
    variant: AArch64AbiVariant,
    values: &[AbiValue],
    spans: &[std::ops::Range<usize>],
    has_sret: bool,
) -> Result<Vec<Vec<(u64, ByteHome)>>, String> {
    let types: Vec<LowerType> = values.iter().map(|v| v.ty.clone()).collect();
    let mut per_value: Vec<Vec<(u64, ByteHome)>> = vec![Vec::new(); values.len()];
    match target {
        TrustCgAbiTarget::AArch64 => {
            if values.iter().any(|v| v.byval) {
                return Err("AArch64 has no `byval` argument".to_owned());
            }
            let locs = AppleAArch64ABI::classify_params_with(variant, &types);
            if locs.len() != values.len() {
                return Err(format!(
                    "the AArch64 classifier placed {} of {} values",
                    locs.len(),
                    values.len()
                ));
            }
            for (i, (loc, value)) in locs.iter().zip(values).enumerate() {
                aarch64_value_homes(loc, value, &mut per_value[i])?;
            }
        }
        TrustCgAbiTarget::X86_64 => {
            let byval: Vec<bool> = values.iter().map(|v| v.byval).collect();
            let locs =
                trust_cg_lower::x86_sysv_param_locations_with_byval(&types, &byval, has_sret)
                    .map_err(|err| format!("the System V placement refuses the values: {err}"))?;
            if locs.len() != values.len() {
                return Err(format!(
                    "the System V placement placed {} of {} values",
                    locs.len(),
                    values.len()
                ));
            }
            for (i, (loc, value)) in locs.iter().zip(values).enumerate() {
                x86_value_homes(loc, value, &mut per_value[i]);
            }
        }
        // A wasm call has no registers and no argument area: every declared
        // value is its own typed, positional wasm parameter, which the
        // per-argument gate compares lane by lane (`wasm_type_lanes`). There is
        // no byte home to compare, so asking is a caller error, not a pass.
        TrustCgAbiTarget::Wasm32 => {
            return Err("wasm32 parameters have no register or stack byte homes".to_owned());
        }
    }
    let mut per_arg = Vec::with_capacity(spans.len());
    for span in spans {
        let mut homes = Vec::new();
        for i in span.clone() {
            homes.extend(
                per_value
                    .get(i)
                    .cloned()
                    .ok_or("a span past the value list")?,
            );
        }
        per_arg.push(homes);
    }
    Ok(per_arg)
}

/// A disagreement between two placements of one signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct PlacementDisagreement {
    /// The argument (index into the compared argument list) whose byte moves.
    pub(super) arg: usize,
    /// Its argument-relative byte.
    pub(super) byte: u64,
    pub(super) rustc: Option<ByteHome>,
    pub(super) declared: Option<ByteHome>,
}

/// THE RULE: every byte rustc's `FnAbi` passes for an argument must have the
/// same home under the bridge's declaration. `live` is, per argument, the
/// argument-relative bytes rustc passes (each value's `[offset, offset +
/// live)`); `rustc` / `declared` are the two placements from
/// [`signature_byte_homes`]. The first byte (argument order, then byte order)
/// whose homes differ is returned. A declared byte rustc does not pass (a
/// carrier wider than its lane) is not compared.
pub(super) fn signature_placement_disagreement(
    live: &[Vec<u64>],
    rustc: &[Vec<(u64, ByteHome)>],
    declared: &[Vec<(u64, ByteHome)>],
) -> Option<PlacementDisagreement> {
    for (arg, bytes) in live.iter().enumerate() {
        for &byte in bytes {
            let find = |homes: &[Vec<(u64, ByteHome)>]| {
                homes
                    .get(arg)
                    .and_then(|h| h.iter().find(|(b, _)| *b == byte).map(|(_, home)| *home))
            };
            let (r, d) = (find(rustc), find(declared));
            if r != d || r.is_none() {
                return Some(PlacementDisagreement {
                    arg,
                    byte,
                    rustc: r,
                    declared: d,
                });
            }
        }
    }
    None
}

/// Per argument, the argument-relative bytes rustc passes.
pub(super) fn live_bytes(values: &[AbiValue], spans: &[std::ops::Range<usize>]) -> Vec<Vec<u64>> {
    spans
        .iter()
        .map(|span| {
            let mut bytes: Vec<u64> = values[span.clone()]
                .iter()
                .flat_map(|v| v.offset..v.offset + v.live)
                .collect();
            bytes.sort_unstable();
            bytes.dedup();
            bytes
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_abi::{Reg, Size};
    use rustc_target::callconv::{ArgAttributes, CastTarget, Uniform};

    /// A minimal `HasDataLayout` for the lane arithmetic: only scalar sizes and
    /// alignments are read, and those come from the `Scalar`s themselves.
    struct Dl(rustc_abi::TargetDataLayout);
    impl HasDataLayout for Dl {
        fn data_layout(&self) -> &rustc_abi::TargetDataLayout {
            &self.0
        }
    }
    fn dl() -> Dl {
        Dl(rustc_abi::TargetDataLayout::default())
    }

    fn int_scalar(bytes: u64) -> Scalar {
        Scalar::Initialized {
            value: Primitive::Int(
                match bytes {
                    1 => rustc_abi::Integer::I8,
                    2 => rustc_abi::Integer::I16,
                    4 => rustc_abi::Integer::I32,
                    _ => rustc_abi::Integer::I64,
                },
                true,
            ),
            valid_range: rustc_abi::WrappingRange::full(Size::from_bytes(bytes)),
        }
    }

    fn float_scalar(bytes: u64) -> Scalar {
        Scalar::Initialized {
            value: Primitive::Float(if bytes == 4 {
                rustc_abi::Float::F32
            } else {
                rustc_abi::Float::F64
            }),
            valid_range: rustc_abi::WrappingRange::full(Size::from_bytes(bytes)),
        }
    }

    /// Native register names and conventions that must not appear in a wasm32
    /// ABI refusal: a wasm32 lane is a typed wasm value, not a register.
    const NATIVE_REGISTER_WORDS: &[&str] = &[
        "register", "x/w", "RAX", "RDX", "RDI", "x8", "XMM", "d/s", "v/q", "AAPCS", "System V",
        "s0-s3", "x0/x1",
    ];

    fn assert_wasm32_wording(what: &str, text: &str) {
        for word in NATIVE_REGISTER_WORDS {
            assert!(
                !text.contains(word),
                "{what} names the native `{word}` on wasm32: {text}"
            );
        }
    }

    fn lane(class: AbiRegClass, bytes: u64, offset: u64) -> AbiRegLane {
        AbiRegLane {
            class,
            bytes,
            offset,
        }
    }

    #[test]
    fn wasm32_abi_refusal_text_names_wasm_values_not_native_registers() {
        let wasm = Some(TrustCgAbiTarget::Wasm32);
        let lanes = vec![
            lane(AbiRegClass::Integer, 4, 0),
            lane(AbiRegClass::Float, 8, 8),
            lane(AbiRegClass::Vector, 16, 16),
        ];
        let registers = ReturnPlacement::Registers(lanes.clone()).describe_for(wasm);
        assert!(registers.contains("3 wasm value lane(s)"), "{registers}");
        for fragment in ["(i32/i64)", "(f32/f64)", "(v128)"] {
            assert!(registers.contains(fragment), "{registers}");
        }
        let empty = ReturnPlacement::Registers(Vec::new()).describe_for(wasm);
        assert_eq!(empty, "no wasm values at all");
        let sret = ReturnPlacement::CallerBuffer.describe_for(wasm);
        assert!(sret.contains("hidden leading `i32` parameter"), "{sret}");
        let byval = ReturnPlacement::StackByValue.describe_for(wasm);
        assert!(byval.contains("one `i32` parameter"), "{byval}");

        let int4 = [lane(AbiRegClass::Integer, 4, 0)];
        let disagreements = [
            // Count, class, offset, a narrower carrier, and the wasm exact-width rule.
            lanes_disagreement_for(TrustCgAbiTarget::Wasm32, &lanes, &int4),
            lanes_disagreement_for(
                TrustCgAbiTarget::Wasm32,
                &int4,
                &[lane(AbiRegClass::Float, 4, 0)],
            ),
            lanes_disagreement_for(
                TrustCgAbiTarget::Wasm32,
                &int4,
                &[lane(AbiRegClass::Integer, 4, 4)],
            ),
            lanes_disagreement_for(
                TrustCgAbiTarget::Wasm32,
                &[lane(AbiRegClass::Integer, 8, 0)],
                &int4,
            ),
            lanes_disagreement_for(
                TrustCgAbiTarget::Wasm32,
                &int4,
                &[lane(AbiRegClass::Integer, 8, 0)],
            ),
        ];
        assert!(
            disagreements[0]
                .as_deref()
                .is_some_and(|d| d.contains("wasm value lane(s)"))
        );
        assert!(
            disagreements[1]
                .as_deref()
                .is_some_and(|d| d.contains("wasm value (f32/f64)"))
        );
        assert!(
            disagreements[4]
                .as_deref()
                .is_some_and(|d| d.contains("a different wasm value type"))
        );

        let mut texts = vec![
            ("Registers", registers),
            ("empty Registers", empty),
            ("CallerBuffer", sret),
            ("StackByValue", byval),
            ("boundary", boundary_misread(wasm).to_owned()),
            ("RET options", ret_abi_options(wasm).to_owned()),
            (
                "ARG options",
                arg_abi_options(TrustCgAbiTarget::Wasm32, false).to_owned(),
            ),
            (
                "ARG Pair options",
                arg_abi_options(TrustCgAbiTarget::Wasm32, true).to_owned(),
            ),
        ];
        for (index, detail) in disagreements.into_iter().enumerate() {
            let detail = detail.unwrap_or_else(|| panic!("disagreement {index} must refuse"));
            texts.push(("lane disagreement", detail));
        }
        for (what, text) in &texts {
            assert_wasm32_wording(what, text);
        }
        assert!(boundary_misread(wasm).contains("wasm value type"));

        // Native wording is unchanged: it still names the native registers.
        assert!(
            ReturnPlacement::Registers(int4.to_vec())
                .describe_for(None)
                .contains("x/w, RAX/RDX")
        );
        assert!(
            ReturnPlacement::CallerBuffer
                .describe_for(None)
                .contains("(x8, RDI)")
        );
        assert_eq!(
            boundary_misread(Some(TrustCgAbiTarget::AArch64)),
            "a value read out of the wrong register file"
        );
        assert!(ret_abi_options(None).contains("x0/x1 pair"));
        assert!(arg_abi_options(TrustCgAbiTarget::X86_64, false).contains("x0/x1 pair"));
    }

    #[test]
    fn float_scalar_pair_requires_two_float_lanes() {
        let a = float_scalar(8);
        let placement = rustc_placement(
            &dl(),
            &PassMode::Pair(ArgAttributes::new(), ArgAttributes::new()),
            crate::scalar_pair::canonical(a, a, &dl()),
            16,
            "[TCG-RET-ABI]",
            "return",
        )
        .unwrap()
        .unwrap();
        assert_eq!(
            placement,
            ReturnPlacement::Registers(vec![
                AbiRegLane {
                    class: AbiRegClass::Float,
                    bytes: 8,
                    offset: 0
                },
                AbiRegLane {
                    class: AbiRegClass::Float,
                    bytes: 8,
                    offset: 8
                },
            ])
        );
    }

    #[test]
    fn int32_pair_requires_two_lanes_but_the_uniform_slot_carries_one() {
        let s = int_scalar(4);
        let required = rustc_placement(
            &dl(),
            &PassMode::Pair(ArgAttributes::new(), ArgAttributes::new()),
            crate::scalar_pair::canonical(s, s, &dl()),
            8,
            "[TCG-RET-ABI]",
            "return",
        )
        .unwrap()
        .unwrap();
        let carried = trust_cg_return_placement(
            TrustCgAbiTarget::AArch64,
            &[TrustIrTy::Tuple(vec![TrustIrTy::I32, TrustIrTy::I32])],
            &[0],
            &[],
        )
        .unwrap();
        let (ReturnPlacement::Registers(want), ReturnPlacement::Registers(got)) =
            (&required, &carried)
        else {
            panic!("both placements must be register lanes: {required:?} {carried:?}");
        };
        assert_eq!(want.len(), 2, "rustc's ScalarPair is two registers");
        assert_eq!(got.len(), 1, "trust-cg packs the 8-byte slot into ONE GPR");
        assert!(lanes_disagreement(want, got).is_some());
    }

    #[test]
    fn float_lane_tuple_is_carried_in_the_fp_registers_on_aarch64() {
        let carried = trust_cg_return_placement(
            TrustCgAbiTarget::AArch64,
            &[TrustIrTy::Tuple(vec![TrustIrTy::F64, TrustIrTy::F64])],
            &[0],
            &[],
        )
        .unwrap();
        assert_eq!(
            carried,
            ReturnPlacement::Registers(vec![
                AbiRegLane {
                    class: AbiRegClass::Float,
                    bytes: 8,
                    offset: 0
                },
                AbiRegLane {
                    class: AbiRegClass::Float,
                    bytes: 8,
                    offset: 8
                },
            ]),
            "AAPCS64 §6.4.2: a two-double HFA returns in d0/d1"
        );
    }

    #[test]
    fn integer_lane_tuple_is_carried_in_the_gpr_pair_on_aarch64() {
        let carried = trust_cg_return_placement(
            TrustCgAbiTarget::AArch64,
            &[TrustIrTy::Tuple(vec![TrustIrTy::I64, TrustIrTy::I64])],
            &[0],
            &[],
        )
        .unwrap();
        assert_eq!(
            carried,
            ReturnPlacement::Registers(vec![
                AbiRegLane {
                    class: AbiRegClass::Integer,
                    bytes: 8,
                    offset: 0
                },
                AbiRegLane {
                    class: AbiRegClass::Integer,
                    bytes: 8,
                    offset: 8
                },
            ])
        );
    }

    #[test]
    fn float_lane_tuple_is_two_sse_eightbytes_on_x86_64() {
        let carried = trust_cg_return_placement(
            TrustCgAbiTarget::X86_64,
            &[TrustIrTy::Tuple(vec![TrustIrTy::F64, TrustIrTy::F64])],
            &[0],
            &[],
        )
        .unwrap();
        assert_eq!(
            carried,
            ReturnPlacement::Registers(vec![
                AbiRegLane {
                    class: AbiRegClass::Float,
                    bytes: 8,
                    offset: 0
                },
                AbiRegLane {
                    class: AbiRegClass::Float,
                    bytes: 8,
                    offset: 8
                },
            ])
        );
    }

    #[test]
    fn mixed_eightbyte_is_integer_class_on_x86_64() {
        // psABI §3.2.3: INTEGER wins over SSE inside one eightbyte, so
        // `{ f32, i32 }` is a single GPR — the case `sysv_c_abi_aggregate_lane_ty`
        // deliberately leaves on the integer path.
        let carried = trust_cg_return_placement(
            TrustCgAbiTarget::X86_64,
            &[TrustIrTy::Tuple(vec![TrustIrTy::F32, TrustIrTy::I32])],
            &[0],
            &[],
        )
        .unwrap();
        assert_eq!(
            carried,
            ReturnPlacement::Registers(vec![AbiRegLane {
                class: AbiRegClass::Integer,
                bytes: 8,
                offset: 0
            }])
        );
    }

    #[test]
    fn over_sixteen_bytes_is_the_caller_buffer_on_both_targets() {
        let big = TrustIrTy::Tuple(vec![TrustIrTy::I64, TrustIrTy::I64, TrustIrTy::I64]);
        for target in [TrustCgAbiTarget::AArch64, TrustCgAbiTarget::X86_64] {
            assert_eq!(
                trust_cg_return_placement(target, std::slice::from_ref(&big), &[0], &[]).unwrap(),
                ReturnPlacement::CallerBuffer,
                "{target:?}"
            );
        }
    }

    #[test]
    fn empty_return_list_is_the_hidden_buffer() {
        assert_eq!(
            trust_cg_return_placement(TrustCgAbiTarget::AArch64, &[], &[], &[]).unwrap(),
            ReturnPlacement::CallerBuffer
        );
    }

    #[test]
    fn a_wider_carrier_lane_satisfies_a_narrower_requirement_but_not_the_reverse() {
        let want = vec![AbiRegLane {
            class: AbiRegClass::Integer,
            bytes: 4,
            offset: 8,
        }];
        let wide = vec![AbiRegLane {
            class: AbiRegClass::Integer,
            bytes: 8,
            offset: 8,
        }];
        let narrow = vec![AbiRegLane {
            class: AbiRegClass::Integer,
            bytes: 2,
            offset: 8,
        }];
        assert!(lanes_disagreement(&want, &wide).is_none());
        assert!(lanes_disagreement(&want, &narrow).is_some());
    }

    #[test]
    fn a_different_class_or_offset_never_agrees() {
        let want = vec![AbiRegLane {
            class: AbiRegClass::Float,
            bytes: 8,
            offset: 0,
        }];
        for got in [
            AbiRegLane {
                class: AbiRegClass::Integer,
                bytes: 8,
                offset: 0,
            },
            AbiRegLane {
                class: AbiRegClass::Float,
                bytes: 8,
                offset: 8,
            },
        ] {
            assert!(lanes_disagreement(&want, std::slice::from_ref(&got)).is_some());
        }
    }

    /// rustc's wasm32 C ABI casts a `#[repr(C)]` struct around one `i128` to ONE
    /// 16-byte integer register; LLVM legalizes it as two `i64` halves for an
    /// argument and returns it through the caller buffer, exactly as the lane
    /// places an `i128` scalar, so the two placements agree.
    #[test]
    fn a_wasm32_sixteen_byte_integer_cast_is_two_i64_halves() {
        use rustc_abi::RegKind;
        let mode = crate::cast_abi::fixture(
            CastTarget::from(Reg {
                kind: RegKind::Integer,
                size: Size::from_bytes(16),
            }),
            false,
        );
        let rustc = || {
            rustc_placement(
                &dl(),
                &mode,
                BackendRepr::Memory { sized: true },
                16,
                "[TCG-ARG-ABI]",
                "argument",
            )
            .unwrap()
        };
        let lanes = |placement: Option<ReturnPlacement>| match placement {
            Some(ReturnPlacement::Registers(lanes)) => lanes,
            other => panic!("expected wasm value lanes, got {other:?}"),
        };
        let arg = lanes(rustc_placement_for_target(
            TrustCgAbiTarget::Wasm32,
            rustc(),
            false,
        ));
        assert_eq!(
            arg,
            vec![
                lane(AbiRegClass::Integer, 8, 0),
                lane(AbiRegClass::Integer, 8, 8)
            ]
        );
        let bridge = lanes(Some(
            wasm_trust_ir_lanes(&TrustIrTy::I128, false, &[]).unwrap(),
        ));
        assert_eq!(
            lanes_disagreement_for(TrustCgAbiTarget::Wasm32, &arg, &bridge),
            None
        );
        assert_eq!(
            rustc_placement_for_target(TrustCgAbiTarget::Wasm32, rustc(), true),
            Some(ReturnPlacement::CallerBuffer)
        );
        // A native target keeps rustc's one register.
        assert_eq!(
            rustc_placement_for_target(TrustCgAbiTarget::AArch64, rustc(), false),
            rustc()
        );
    }

    #[test]
    fn a_float_cast_is_one_lane_per_unit_register() {
        let mode = crate::cast_abi::fixture(
            CastTarget::from(Uniform::consecutive(Reg::f64(), Size::from_bytes(24))),
            false,
        );
        let placement = rustc_placement(
            &dl(),
            &mode,
            BackendRepr::Memory { sized: true },
            24,
            "[TCG-RET-ABI]",
            "return",
        )
        .unwrap()
        .unwrap();
        assert_eq!(
            placement,
            ReturnPlacement::Registers(vec![
                AbiRegLane {
                    class: AbiRegClass::Float,
                    bytes: 8,
                    offset: 0
                },
                AbiRegLane {
                    class: AbiRegClass::Float,
                    bytes: 8,
                    offset: 8
                },
                AbiRegLane {
                    class: AbiRegClass::Float,
                    bytes: 8,
                    offset: 16
                },
            ])
        );
    }

    #[test]
    fn an_integer_cast_with_a_short_tail_states_the_live_bytes() {
        let mode = crate::cast_abi::fixture(
            CastTarget::from(Uniform::new(Reg::i64(), Size::from_bytes(12))),
            false,
        );
        let placement = rustc_placement(
            &dl(),
            &mode,
            BackendRepr::Memory { sized: true },
            12,
            "[TCG-RET-ABI]",
            "return",
        )
        .unwrap()
        .unwrap();
        assert_eq!(
            placement,
            ReturnPlacement::Registers(vec![
                AbiRegLane {
                    class: AbiRegClass::Integer,
                    bytes: 8,
                    offset: 0
                },
                AbiRegLane {
                    class: AbiRegClass::Integer,
                    bytes: 4,
                    offset: 8
                },
            ])
        );
        // trust-cg's 12-byte AArch64 return is x0 + x1 (the high lane an exact
        // 4-byte load), which CARRIES the 4 live bytes rustc requires.
        let carried = trust_cg_return_placement(
            TrustCgAbiTarget::AArch64,
            &[TrustIrTy::Tuple(vec![
                TrustIrTy::I32,
                TrustIrTy::I32,
                TrustIrTy::I32,
            ])],
            &[0],
            &[],
        )
        .unwrap();
        let (ReturnPlacement::Registers(want), ReturnPlacement::Registers(got)) =
            (&placement, &carried)
        else {
            panic!("register lanes expected");
        };
        assert_eq!(lanes_disagreement(want, got), None);
    }

    #[test]
    fn pad_i32_and_zero_unit_casts_are_refused_not_approximated() {
        let padded = crate::cast_abi::fixture(CastTarget::from(Reg::i64()), true);
        assert!(
            rustc_placement(
                &dl(),
                &padded,
                BackendRepr::Memory { sized: true },
                8,
                "[TCG-RET-ABI]",
                "return"
            )
            .is_err()
        );
    }

    #[test]
    fn indirect_modes_map_to_their_own_placements() {
        let buffer = crate::indirect_abi::fixture(ArgAttributes::new(), None, false);
        let stack = crate::indirect_abi::fixture(ArgAttributes::new(), None, true);
        for (mode, expect) in [
            (buffer, ReturnPlacement::CallerBuffer),
            (stack, ReturnPlacement::StackByValue),
        ] {
            assert_eq!(
                rustc_placement(
                    &dl(),
                    &mode,
                    BackendRepr::Memory { sized: true },
                    32,
                    "[TCG-RET-ABI]",
                    "return"
                )
                .unwrap()
                .unwrap(),
                expect
            );
        }
    }

    /// rustc's `Indirect { on_stack: false }` argument is ONE pointer. trust-cg
    /// places a declared `Ptr` in exactly that lane on both targets, while the
    /// whole-slot lane tuple of the same 12-byte `{u32, u32, u32}` — what the
    /// bridge declared before the indirect argument lane — does not match it.
    #[test]
    fn an_indirect_argument_is_one_pointer_lane_on_both_targets() {
        let want = indirect_argument_pointer_lanes(8);
        let t12 = TrustIrTy::Tuple(vec![TrustIrTy::I32, TrustIrTy::I32, TrustIrTy::I32]);
        for target in [TrustCgAbiTarget::X86_64, TrustCgAbiTarget::AArch64] {
            let carried = trust_cg_param_placement(target, &[TrustIrTy::Ptr], &[0], &[]).unwrap();
            let ReturnPlacement::Registers(got) = &carried else {
                panic!("{target:?}: a pointer must ride a register lane: {carried:?}");
            };
            assert_eq!(lanes_disagreement(&want, got), None, "{target:?}");
            let whole = trust_cg_param_placement(target, &[t12.clone()], &[0], &[]).unwrap();
            let ReturnPlacement::Registers(lanes) = &whole else {
                panic!("{target:?}: a 12-byte lane tuple rides registers: {whole:?}");
            };
            assert!(lanes_disagreement(&want, lanes).is_some(), "{target:?}");
        }
    }

    #[test]
    fn ignore_is_not_a_placement() {
        assert!(
            rustc_placement(
                &dl(),
                &PassMode::Ignore,
                BackendRepr::Memory { sized: true },
                0,
                "[TCG-RET-ABI]",
                "return"
            )
            .unwrap()
            .is_none()
        );
    }

    #[test]
    fn an_unmodelled_architecture_has_no_target() {
        for arch in ["riscv64", "wasm64", "powerpc64"] {
            assert!(trust_cg_abi_target(arch).is_none(), "{arch}");
        }
        // wasm32 is modelled: the wasm object lane's BasicCABI lanes.
        assert_eq!(
            trust_cg_abi_target("wasm32"),
            Some(TrustCgAbiTarget::Wasm32)
        );
    }

    #[test]
    fn two_integer_values_are_rax_then_rdx_on_x86_64() {
        // `Option<u8>` as rustc's `PassMode::Pair`: two 1-byte INTEGER lanes at
        // offsets 0 and 1. On x86-64 the bridge widens a `Zext` lane to an I32
        // carrier; the classifier still names RAX then RDX, and the carrier is
        // at least as wide as the lane rustc requires.
        let required = rustc_placement(
            &dl(),
            &PassMode::Pair(ArgAttributes::new(), ArgAttributes::new()),
            crate::scalar_pair::canonical(int_scalar(1), int_scalar(1), &dl()),
            2,
            "[TCG-RET-ABI]",
            "return",
        )
        .unwrap()
        .unwrap();
        let carried = trust_cg_return_placement(
            TrustCgAbiTarget::X86_64,
            &[TrustIrTy::I32, TrustIrTy::I8],
            &[0, 1],
            &[],
        )
        .unwrap();
        assert_eq!(
            carried,
            ReturnPlacement::Registers(vec![
                AbiRegLane {
                    class: AbiRegClass::Integer,
                    bytes: 4,
                    offset: 0
                },
                AbiRegLane {
                    class: AbiRegClass::Integer,
                    bytes: 1,
                    offset: 1
                },
            ])
        );
        let (ReturnPlacement::Registers(want), ReturnPlacement::Registers(got)) =
            (&required, &carried)
        else {
            panic!("register lanes expected");
        };
        assert_eq!(lanes_disagreement(want, got), None);
    }

    #[test]
    fn two_float_values_are_xmm0_then_xmm1_on_x86_64() {
        let carried = trust_cg_return_placement(
            TrustCgAbiTarget::X86_64,
            &[TrustIrTy::F64, TrustIrTy::F64],
            &[0, 8],
            &[],
        )
        .unwrap();
        assert_eq!(
            carried,
            ReturnPlacement::Registers(vec![
                AbiRegLane {
                    class: AbiRegClass::Float,
                    bytes: 8,
                    offset: 0
                },
                AbiRegLane {
                    class: AbiRegClass::Float,
                    bytes: 8,
                    offset: 8
                },
            ])
        );
    }

    #[test]
    fn a_mixed_pair_takes_one_register_of_each_class_on_x86_64() {
        // `(u64, f64)`: RAX carries the integer lane and XMM0 the float lane;
        // the two sequences are independent, so neither lane moves to RDX/XMM1.
        let carried = trust_cg_return_placement(
            TrustCgAbiTarget::X86_64,
            &[TrustIrTy::I64, TrustIrTy::F64],
            &[0, 8],
            &[],
        )
        .unwrap();
        assert_eq!(
            carried,
            ReturnPlacement::Registers(vec![
                AbiRegLane {
                    class: AbiRegClass::Integer,
                    bytes: 8,
                    offset: 0
                },
                AbiRegLane {
                    class: AbiRegClass::Float,
                    bytes: 8,
                    offset: 8
                },
            ])
        );
    }

    #[test]
    fn a_pointer_and_length_pair_is_two_integer_registers_on_x86_64() {
        let carried = trust_cg_return_placement(
            TrustCgAbiTarget::X86_64,
            &[TrustIrTy::Ptr, TrustIrTy::I64],
            &[0, 8],
            &[],
        )
        .unwrap();
        assert_eq!(
            carried,
            ReturnPlacement::Registers(vec![
                AbiRegLane {
                    class: AbiRegClass::Integer,
                    bytes: 8,
                    offset: 0
                },
                AbiRegLane {
                    class: AbiRegClass::Integer,
                    bytes: 8,
                    offset: 8
                },
            ])
        );
    }

    #[test]
    fn a_narrow_x86_64_carrier_does_not_satisfy_a_wider_rustc_lane() {
        // rustc's lane is 4 live bytes; an I8 carrier holds one. The gate must
        // refuse, not round up.
        let required = rustc_placement(
            &dl(),
            &PassMode::Pair(ArgAttributes::new(), ArgAttributes::new()),
            crate::scalar_pair::canonical(int_scalar(4), int_scalar(4), &dl()),
            8,
            "[TCG-RET-ABI]",
            "return",
        )
        .unwrap()
        .unwrap();
        let carried = trust_cg_return_placement(
            TrustCgAbiTarget::X86_64,
            &[TrustIrTy::I8, TrustIrTy::I32],
            &[0, 4],
            &[],
        )
        .unwrap();
        let (ReturnPlacement::Registers(want), ReturnPlacement::Registers(got)) =
            (&required, &carried)
        else {
            panic!("register lanes expected");
        };
        assert!(lanes_disagreement(want, got).is_some());
    }

    #[test]
    fn a_three_value_x86_64_return_exhausts_the_integer_file() {
        // System V has exactly RAX and RDX; a third integer result has no
        // stated placement and the gate refuses rather than invent one.
        assert!(
            trust_cg_return_placement(
                TrustCgAbiTarget::X86_64,
                &[TrustIrTy::I64, TrustIrTy::I64, TrustIrTy::I64],
                &[0, 8, 16],
                &[],
            )
            .is_err()
        );
    }

    fn native_scope<'a>(arch: &'a str, host_os: &'static str) -> AggregateAbiScope<'a> {
        AggregateAbiScope {
            arch,
            target_os: host_os,
            is_like_windows: false,
            is_like_darwin: host_os == "macos",
            host_os,
            pointer_bytes: 8,
            conv: CanonAbi::C,
            c_variadic: false,
        }
    }

    #[test]
    fn aggregate_scope_checks_each_canonical_convention_not_rustic_membership() {
        use rustc_abi::{ArmCall, InterruptKind};
        // All 23 concrete variants at the inspected Trust revision. These are
        // independent expected policy rows, not a call to is_rustic_abi or to
        // the classifier under test to reconstruct the expected answer.
        let rows = [
            (CanonAbi::C, true, true),
            (CanonAbi::Rust, true, true),
            (CanonAbi::RustCold, false, false),
            (CanonAbi::RustPreserveNone, false, false),
            (CanonAbi::RustTail, false, false),
            (CanonAbi::Custom, false, false),
            (CanonAbi::Swift, false, false),
            (CanonAbi::Arm(ArmCall::Aapcs), false, false),
            (CanonAbi::Arm(ArmCall::CCmseNonSecureCall), false, false),
            (CanonAbi::Arm(ArmCall::CCmseNonSecureEntry), false, false),
            (CanonAbi::GpuKernel, false, false),
            (CanonAbi::Interrupt(InterruptKind::Avr), false, false),
            (
                CanonAbi::Interrupt(InterruptKind::AvrNonBlocking),
                false,
                false,
            ),
            (CanonAbi::Interrupt(InterruptKind::Msp430), false, false),
            (
                CanonAbi::Interrupt(InterruptKind::RiscvMachine),
                false,
                false,
            ),
            (
                CanonAbi::Interrupt(InterruptKind::RiscvSupervisor),
                false,
                false,
            ),
            (CanonAbi::Interrupt(InterruptKind::X86), false, false),
            (CanonAbi::X86(X86Call::Fastcall), false, false),
            (CanonAbi::X86(X86Call::Stdcall), false, false),
            (CanonAbi::X86(X86Call::SysV64), false, true),
            (CanonAbi::X86(X86Call::Thiscall), false, false),
            (CanonAbi::X86(X86Call::Vectorcall), false, false),
            (CanonAbi::X86(X86Call::Win64), false, false),
        ];
        let mut attempts = 0;
        for host in ["linux", "macos"] {
            for (arch, target, x86) in [
                ("aarch64", TrustCgAbiTarget::AArch64, false),
                ("arm64", TrustCgAbiTarget::AArch64, false),
                ("x86_64", TrustCgAbiTarget::X86_64, true),
            ] {
                for (conv, a64_ok, x86_ok) in rows {
                    let result = aggregate_abi_scope(AggregateAbiScope {
                        conv,
                        ..native_scope(arch, host)
                    });
                    if if x86 { x86_ok } else { a64_ok } {
                        assert_eq!(result.unwrap(), target, "{host}/{arch}/{conv:?}");
                    } else {
                        let error = result.unwrap_err();
                        assert!(error.starts_with("[TCG-AGGREGATE-ABI-SCOPE]"), "{error}");
                    }
                    attempts += 1;
                }
            }
        }
        assert_eq!(attempts, 138);
    }

    #[test]
    fn aggregate_scope_binds_target_host_pointer_width_and_nonvariadic_policy() {
        // The optional host is the sole admitted family for this authored row.
        // In particular a Windows-like target cannot disguise itself as Linux.
        let target_rows = [
            ("linux", false, false, Some("linux")),
            ("macos", false, true, Some("macos")),
            ("ios", false, true, Some("macos")),
            ("windows", true, false, None),
            ("linux", true, false, None),
            ("freebsd", false, false, None),
            ("unknown", false, false, None),
        ];
        let mut pairs = 0;
        let mut refusals = 0;
        for arch in ["aarch64", "arm64", "x86_64"] {
            for host in ["linux", "macos", "windows", "freebsd", "android", "unknown"] {
                for (target_os, is_like_windows, is_like_darwin, accepted_host) in target_rows {
                    let scope = AggregateAbiScope {
                        target_os,
                        is_like_windows,
                        is_like_darwin,
                        ..native_scope(arch, host)
                    };
                    assert_eq!(
                        aggregate_abi_scope(scope).is_ok(),
                        accepted_host == Some(host),
                        "{scope:?}",
                    );
                    pairs += 1;
                }
            }
            for host in ["linux", "macos"] {
                for pointer_bytes in [0, 1, 2, 4, 16] {
                    assert!(
                        aggregate_abi_scope(AggregateAbiScope {
                            pointer_bytes,
                            ..native_scope(arch, host)
                        })
                        .is_err()
                    );
                    refusals += 1;
                }
                assert!(
                    aggregate_abi_scope(AggregateAbiScope {
                        c_variadic: true,
                        ..native_scope(arch, host)
                    })
                    .is_err()
                );
                refusals += 1;
            }
        }
        for arch in [
            "riscv64",
            "wasm32",
            "powerpc64",
            "arm64ec",
            "x86",
            "unknown",
        ] {
            for host in ["linux", "macos"] {
                assert!(aggregate_abi_scope(native_scope(arch, host)).is_err());
                refusals += 1;
            }
        }
        assert_eq!(pairs, 126);
        assert_eq!(refusals, 48);
    }

    #[test]
    fn caller_buffer_or_float_lane_equality_is_not_convention_authority() {
        let float = float_scalar(8);
        let float_requirement = rustc_placement(
            &dl(),
            &PassMode::Pair(ArgAttributes::new(), ArgAttributes::new()),
            crate::scalar_pair::canonical(float, float, &dl()),
            16,
            "[TEST]",
            "return",
        )
        .unwrap()
        .unwrap();
        let big = TrustIrTy::Tuple(vec![TrustIrTy::I64, TrustIrTy::I64, TrustIrTy::I64]);
        let float_pair = TrustIrTy::Tuple(vec![TrustIrTy::F64, TrustIrTy::F64]);
        let mut equal_but_refused = 0;
        for (arch, target) in [
            ("aarch64", TrustCgAbiTarget::AArch64),
            ("x86_64", TrustCgAbiTarget::X86_64),
        ] {
            // These equalities demonstrate why a placement-only gate is
            // insufficient. The independent scope gate must still reject.
            assert_eq!(
                trust_cg_return_placement(target, &[big.clone()], &[0], &[]).unwrap(),
                ReturnPlacement::CallerBuffer,
            );
            assert_eq!(
                trust_cg_return_placement(target, &[float_pair.clone()], &[0], &[]).unwrap(),
                float_requirement,
            );
            for conv in [
                CanonAbi::RustCold,
                CanonAbi::RustPreserveNone,
                CanonAbi::RustTail,
                CanonAbi::X86(X86Call::Win64),
                CanonAbi::X86(X86Call::Vectorcall),
            ] {
                assert!(
                    aggregate_abi_scope(AggregateAbiScope {
                        conv,
                        ..native_scope(arch, "linux")
                    })
                    .is_err()
                );
                equal_but_refused += 1;
            }
        }
        assert_eq!(equal_but_refused, 10);
    }
    /// The x86-64 twin of the AArch64 multi-value argument model: two declared
    /// values are two INTEGER lanes at rustc's own offsets, and they satisfy
    /// the `PassMode::Pair` requirement the whole-slot value could not.
    #[test]
    fn two_i32_values_are_two_integer_lanes_at_their_offsets_on_x86_64() {
        let carried = trust_cg_param_placement(
            TrustCgAbiTarget::X86_64,
            &[TrustIrTy::I32, TrustIrTy::I32],
            &[0, 4],
            &[],
        )
        .unwrap();
        assert_eq!(
            carried,
            ReturnPlacement::Registers(vec![
                AbiRegLane {
                    class: AbiRegClass::Integer,
                    bytes: 4,
                    offset: 0
                },
                AbiRegLane {
                    class: AbiRegClass::Integer,
                    bytes: 4,
                    offset: 4
                },
            ])
        );
        let s = int_scalar(4);
        let required = rustc_placement(
            &dl(),
            &PassMode::Pair(ArgAttributes::new(), ArgAttributes::new()),
            crate::scalar_pair::canonical(s, s, &dl()),
            8,
            "[TCG-ARG-ABI]",
            "argument",
        )
        .unwrap()
        .unwrap();
        let (ReturnPlacement::Registers(want), ReturnPlacement::Registers(got)) =
            (&required, &carried)
        else {
            panic!("both placements must be register lanes: {required:?} {carried:?}");
        };
        assert_eq!(lanes_disagreement(want, got), None);
        // The whole-slot value still disagrees, exactly as before the arm.
        let whole = trust_cg_param_placement(
            TrustCgAbiTarget::X86_64,
            &[TrustIrTy::Tuple(vec![TrustIrTy::I32, TrustIrTy::I32])],
            &[0],
            &[],
        )
        .unwrap();
        let ReturnPlacement::Registers(one) = &whole else {
            panic!("{whole:?}");
        };
        assert!(lanes_disagreement(want, one).is_some());
    }

    /// `Option<u8>`: rustc's lanes are `1 byte @0` (a `zeroext` tag) and
    /// `1 byte @1`. The 32-bit carrier the lane declares for the extended tag
    /// satisfies the 1-byte lane (a wider carrier of the same class at the same
    /// offset), while a carrier NARROWER than the lane never does.
    #[test]
    fn a_wider_carrier_satisfies_a_narrow_lane_but_never_the_reverse_on_x86_64() {
        let s = int_scalar(1);
        let required = rustc_placement(
            &dl(),
            &PassMode::Pair(ArgAttributes::new(), ArgAttributes::new()),
            crate::scalar_pair::canonical(s, s, &dl()),
            2,
            "[TCG-ARG-ABI]",
            "argument",
        )
        .unwrap()
        .unwrap();
        let carried = trust_cg_param_placement(
            TrustCgAbiTarget::X86_64,
            &[TrustIrTy::I32, TrustIrTy::I8],
            &[0, 1],
            &[],
        )
        .unwrap();
        let (ReturnPlacement::Registers(want), ReturnPlacement::Registers(got)) =
            (&required, &carried)
        else {
            panic!("{required:?} {carried:?}");
        };
        assert_eq!(lanes_disagreement(want, got), None);

        let s4 = int_scalar(4);
        let required = rustc_placement(
            &dl(),
            &PassMode::Pair(ArgAttributes::new(), ArgAttributes::new()),
            crate::scalar_pair::canonical(s4, s4, &dl()),
            8,
            "[TCG-ARG-ABI]",
            "argument",
        )
        .unwrap()
        .unwrap();
        let narrow = trust_cg_param_placement(
            TrustCgAbiTarget::X86_64,
            &[TrustIrTy::I8, TrustIrTy::I32],
            &[0, 4],
            &[],
        )
        .unwrap();
        let (ReturnPlacement::Registers(want), ReturnPlacement::Registers(got)) =
            (&required, &narrow)
        else {
            panic!("{required:?} {narrow:?}");
        };
        assert!(lanes_disagreement(want, got).is_some_and(|d| d.contains("carrier holds only")));
    }

    /// A value that would not ride registers inside a multi-value argument (a
    /// MEMORY-class aggregate) is refused by name, never modelled as a lane.
    #[test]
    fn a_memory_class_value_inside_a_multi_value_argument_is_refused_on_x86_64() {
        let err = trust_cg_param_placement(
            TrustCgAbiTarget::X86_64,
            &[
                TrustIrTy::I64,
                TrustIrTy::Tuple(vec![TrustIrTy::I64, TrustIrTy::I64, TrustIrTy::I64]),
            ],
            &[0, 8],
            &[],
        )
        .unwrap_err();
        assert!(err.contains("multi-value argument"), "{err}");
    }
    /// `Option<NonZero<u128>>`: a 16-byte / 16-aligned niche scalar whose
    /// memory-slot spelling is a one-element I128 aggregate. rustc returns it
    /// as a 128-bit `BackendRepr::Scalar` in RAX:RDX; the gate's leaf collector
    /// now mirrors the selector's I128 arm — two consecutive INTEGER eightbytes
    /// — so the two placements agree, in both directions.
    #[test]
    fn an_i128_leaf_inside_an_aggregate_is_two_integer_eightbytes_on_x86_64() {
        let two_lanes = ReturnPlacement::Registers(vec![
            AbiRegLane {
                class: AbiRegClass::Integer,
                bytes: 8,
                offset: 0,
            },
            AbiRegLane {
                class: AbiRegClass::Integer,
                bytes: 8,
                offset: 8,
            },
        ]);
        let returned = trust_cg_return_placement(
            TrustCgAbiTarget::X86_64,
            &[TrustIrTy::Tuple(vec![TrustIrTy::I128])],
            &[0],
            &[],
        )
        .unwrap();
        assert_eq!(returned, two_lanes);
        let passed = trust_cg_param_placement(
            TrustCgAbiTarget::X86_64,
            &[TrustIrTy::Tuple(vec![TrustIrTy::I128])],
            &[0],
            &[],
        )
        .unwrap();
        assert_eq!(passed, two_lanes);
        let s = Scalar::Initialized {
            value: Primitive::Int(rustc_abi::Integer::I128, false),
            valid_range: rustc_abi::WrappingRange::full(Size::from_bytes(16)),
        };
        let required = rustc_placement(
            &dl(),
            &PassMode::Direct(ArgAttributes::new()),
            BackendRepr::Scalar(s),
            16,
            "[TCG-RET-ABI]",
            "return",
        )
        .unwrap()
        .unwrap();
        let (ReturnPlacement::Registers(want), ReturnPlacement::Registers(got)) =
            (&required, &returned)
        else {
            panic!("{required:?} {returned:?}");
        };
        assert_eq!(lanes_disagreement(want, got), None);
        // A 24-byte aggregate holding an I128 is MEMORY class: the caller's buffer
        // for a return, a by-value stack copy for an argument — never a lane.
        assert_eq!(
            trust_cg_return_placement(
                TrustCgAbiTarget::X86_64,
                &[TrustIrTy::Tuple(vec![TrustIrTy::I128, TrustIrTy::I64])],
                &[0],
                &[],
            )
            .unwrap(),
            ReturnPlacement::CallerBuffer
        );
    }
    /// EVERY cell of the argument-placement verdict table
    /// (`arg_memory_placement_verdict`): target model x lane target x rustc's
    /// placement mode x "declared exactly one `Ptr`". The rows are the decision,
    /// written out; a mutant of the table (admitting an off-lane caller-made
    /// copy, admitting `byval` on AArch64, refusing a declared-`Ptr` caller-made
    /// copy) fails exactly the rows it changes, and the failure lists them.
    #[test]
    fn arg_memory_placement_verdict_table() {
        #[derive(Clone, Copy, Debug)]
        enum P {
            Ignore,
            Regs,
            Buffer,
            Byval,
        }
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        enum Expect {
            Regs,
            Ptr,
            Classifier,
            Byval,
            NoLane,
            NotSysV,
            Ignored,
        }
        const A64: Option<TrustCgAbiTarget> = Some(TrustCgAbiTarget::AArch64);
        const X64: Option<TrustCgAbiTarget> = Some(TrustCgAbiTarget::X86_64);
        let lane = AbiRegLane {
            class: AbiRegClass::Integer,
            bytes: 8,
            offset: 0,
        };
        let rows: &[(Option<TrustCgAbiTarget>, bool, P, bool, Expect)] = &[
            (None, false, P::Ignore, false, Expect::Ignored),
            (None, false, P::Ignore, true, Expect::Ignored),
            (None, false, P::Regs, false, Expect::Regs),
            (None, false, P::Regs, true, Expect::Regs),
            (None, false, P::Buffer, false, Expect::NoLane),
            (None, false, P::Buffer, true, Expect::NoLane),
            (None, false, P::Byval, false, Expect::NotSysV),
            (None, false, P::Byval, true, Expect::NotSysV),
            (None, true, P::Ignore, false, Expect::Ignored),
            (None, true, P::Ignore, true, Expect::Ignored),
            (None, true, P::Regs, false, Expect::Regs),
            (None, true, P::Regs, true, Expect::Regs),
            (None, true, P::Buffer, false, Expect::Classifier),
            (None, true, P::Buffer, true, Expect::Ptr),
            (None, true, P::Byval, false, Expect::NotSysV),
            (None, true, P::Byval, true, Expect::NotSysV),
            (A64, false, P::Ignore, false, Expect::Ignored),
            (A64, false, P::Ignore, true, Expect::Ignored),
            (A64, false, P::Regs, false, Expect::Regs),
            (A64, false, P::Regs, true, Expect::Regs),
            (A64, false, P::Buffer, false, Expect::NoLane),
            (A64, false, P::Buffer, true, Expect::NoLane),
            (A64, false, P::Byval, false, Expect::NotSysV),
            (A64, false, P::Byval, true, Expect::NotSysV),
            (A64, true, P::Ignore, false, Expect::Ignored),
            (A64, true, P::Ignore, true, Expect::Ignored),
            (A64, true, P::Regs, false, Expect::Regs),
            (A64, true, P::Regs, true, Expect::Regs),
            (A64, true, P::Buffer, false, Expect::Classifier),
            (A64, true, P::Buffer, true, Expect::Ptr),
            (A64, true, P::Byval, false, Expect::NotSysV),
            (A64, true, P::Byval, true, Expect::NotSysV),
            (X64, false, P::Ignore, false, Expect::Ignored),
            (X64, false, P::Ignore, true, Expect::Ignored),
            (X64, false, P::Regs, false, Expect::Regs),
            (X64, false, P::Regs, true, Expect::Regs),
            (X64, false, P::Buffer, false, Expect::NoLane),
            (X64, false, P::Buffer, true, Expect::NoLane),
            (X64, false, P::Byval, false, Expect::NotSysV),
            (X64, false, P::Byval, true, Expect::NotSysV),
            (X64, true, P::Ignore, false, Expect::Ignored),
            (X64, true, P::Ignore, true, Expect::Ignored),
            (X64, true, P::Regs, false, Expect::Regs),
            (X64, true, P::Regs, true, Expect::Regs),
            (X64, true, P::Buffer, false, Expect::Classifier),
            (X64, true, P::Buffer, true, Expect::Ptr),
            (X64, true, P::Byval, false, Expect::Byval),
            (X64, true, P::Byval, true, Expect::Byval),
        ];
        // Every key is drawn from 3 target models x 2 x 4 modes x 2, so as many
        // DISTINCT keys as that product is every cell exactly once.
        let keys: std::collections::BTreeSet<String> = rows
            .iter()
            .map(|(t, l, p, s, _)| format!("{t:?}/{l}/{p:?}/{s}"))
            .collect();
        assert_eq!(keys.len(), rows.len(), "a cell is listed twice");
        assert_eq!(keys.len(), 3 * 2 * 4 * 2, "a cell is missing");
        let mut wrong = Vec::new();
        for &(target, lane_target, placement, single_ptr, want) in rows {
            let rustc = match placement {
                P::Ignore => None,
                P::Regs => Some(ReturnPlacement::Registers(vec![lane])),
                P::Buffer => Some(ReturnPlacement::CallerBuffer),
                P::Byval => Some(ReturnPlacement::StackByValue),
            };
            let got = match arg_memory_placement_verdict(target, lane_target, rustc, single_ptr) {
                ArgPlacementVerdict::CompareRegisters(lanes) => {
                    assert_eq!(lanes, vec![lane], "rustc's lanes are compared unchanged");
                    Expect::Regs
                }
                ArgPlacementVerdict::ComparePointerLane => Expect::Ptr,
                ArgPlacementVerdict::CompareCallerBufferWithClassifier => Expect::Classifier,
                ArgPlacementVerdict::CompareSysVByvalInSignature => Expect::Byval,
                ArgPlacementVerdict::Refuse(ArgPlacementRefusal::CallerBufferOffLane) => {
                    Expect::NoLane
                }
                ArgPlacementVerdict::Refuse(ArgPlacementRefusal::StackByValueOffSysV) => {
                    Expect::NotSysV
                }
                ArgPlacementVerdict::Refuse(ArgPlacementRefusal::IgnoredButDeclared) => {
                    Expect::Ignored
                }
            };
            if got != want {
                wrong.push(format!(
                    "({target:?}, lane_target={lane_target}, {placement:?}, \
                     single_ptr={single_ptr}): want {want:?}, got {got:?}"
                ));
            }
        }
        assert!(
            wrong.is_empty(),
            "{} cell(s) wrong:\n  {}",
            wrong.len(),
            wrong.join("\n  ")
        );
    }

    // ---- the whole-signature placement check ----

    fn int_reg(bytes: u64) -> Reg {
        Reg {
            kind: RegKind::Integer,
            size: Size::from_bytes(bytes),
        }
    }

    fn cast(reg: Reg, total: u64) -> PassMode {
        crate::cast_abi::fixture(
            CastTarget::from(Uniform::consecutive(reg, Size::from_bytes(total))),
            false,
        )
    }

    fn values_of(mode: &PassMode, repr: BackendRepr, size: u64, align: u64) -> Vec<AbiValue> {
        rustc_backend_values(&dl(), mode, repr, size, align).unwrap()
    }

    /// rustc's backend values per `PassMode`, the model of
    /// `rustc_codegen_llvm`'s lowering the check compares against.
    #[test]
    fn rustc_backend_values_table() {
        let mem = BackendRepr::Memory { sized: true };
        // Direct scalar, and a 128-bit scalar as ONE value.
        assert_eq!(
            values_of(
                &PassMode::Direct(ArgAttributes::new()),
                BackendRepr::Scalar(int_scalar(4)),
                4,
                4
            ),
            vec![AbiValue::new(LowerType::I32, 0, 4)]
        );
        // Pair `(u8, u32)`: the second scalar at rustc's `b_offset` (the first
        // scalar's size rounded up to the second's alignment), 4 — never 1.
        assert_eq!(
            values_of(
                &PassMode::Pair(ArgAttributes::new(), ArgAttributes::new()),
                crate::scalar_pair::canonical(int_scalar(1), int_scalar(4), &dl()),
                8,
                4
            ),
            vec![
                AbiValue::new(LowerType::I8, 0, 1),
                AbiValue::new(LowerType::I32, 4, 4)
            ]
        );
        // A single-unit integer Cast of 1..=8 bytes is the integer LLVM
        // legalizes `iN` to: never the 8-byte slot below 5 bytes.
        for (size, ty) in [
            (1, LowerType::I8),
            (2, LowerType::I16),
            (3, LowerType::I32),
            (4, LowerType::I32),
            (5, LowerType::I64),
            (6, LowerType::I64),
            (7, LowerType::I64),
            (8, LowerType::I64),
        ] {
            assert_eq!(
                values_of(&cast(int_reg(size), size), mem, size, 1),
                vec![AbiValue::new(ty, 0, size)],
                "a {size}-byte narrow cast"
            );
        }
        // A multi-unit Cast is one consecutive block.
        assert_eq!(
            values_of(&cast(Reg::i64(), 16), mem, 16, 8),
            vec![AbiValue::new(
                LowerType::Array(Box::new(LowerType::I64), 2),
                0,
                16
            )]
        );
        // Indirect: one pointer, plus the metadata word of an unsized value.
        let indirect = |meta: bool| {
            crate::indirect_abi::fixture(ArgAttributes::new(), meta.then(ArgAttributes::new), false)
        };
        assert_eq!(
            values_of(&indirect(false), mem, 24, 8),
            vec![AbiValue::new(LowerType::I64, 0, 8)]
        );
        assert_eq!(
            values_of(&indirect(true), mem, 24, 8),
            vec![
                AbiValue::new(LowerType::I64, 0, 8),
                AbiValue::new(LowerType::I64, 8, 8)
            ]
        );
        // byval: the value's bytes of its size AND alignment — a 32-byte,
        // 16-aligned struct is a 16-aligned image, never a 1-aligned one.
        let byval = crate::indirect_abi::fixture(ArgAttributes::new(), None, true);
        let v = values_of(&byval, mem, 32, 16);
        assert_eq!(v.len(), 1);
        assert!(v[0].byval);
        assert_eq!(v[0].ty.bytes(), 32);
        assert_eq!(v[0].ty.align(), 16);
        // Ignore: nothing. A pad_i32 Cast: refused by name.
        assert!(values_of(&PassMode::Ignore, mem, 0, 1).is_empty());
        let padded = crate::cast_abi::fixture(CastTarget::from(int_reg(4)), true);
        assert!(rustc_backend_values(&dl(), &padded, mem, 4, 4).is_err());
    }

    #[test]
    fn unsupported_indirect_descriptors_refuse_both_consumers() {
        #[cfg(not(rustc_indirect_modes))]
        let cases = vec![(
            PassMode::Indirect {
                attrs: ArgAttributes::new(),
                meta_attrs: Some(ArgAttributes::new()),
                on_stack: true,
            },
            "metadata",
        )];
        #[cfg(rustc_indirect_modes)]
        let cases = {
            use rustc_abi::AddressSpace;
            use rustc_target::callconv::IndirectMode;
            vec![
                (
                    PassMode::Indirect {
                        attrs: ArgAttributes::new(),
                        address_space: Some(AddressSpace(1)),
                        mode: IndirectMode::Pointer,
                    },
                    "address space",
                ),
                (
                    PassMode::Indirect {
                        attrs: ArgAttributes::new(),
                        address_space: None,
                        mode: IndirectMode::AmdgpuKernelArg,
                    },
                    "AmdgpuKernelArg",
                ),
            ]
        };
        for (mode, marker) in cases {
            let placement = rustc_placement(
                &dl(),
                &mode,
                BackendRepr::Memory { sized: true },
                32,
                "[TCG-ARG-ABI]",
                "argument",
            )
            .unwrap_err();
            assert!(placement.contains(marker), "{placement}");
            let values =
                rustc_backend_values(&dl(), &mode, BackendRepr::Memory { sized: true }, 32, 16)
                    .unwrap_err();
            assert!(values.contains(marker), "{values}");
        }
    }

    /// `n` pointer-width integers, then `tail`.
    fn after_u64s(n: usize, tail: Vec<AbiValue>) -> (Vec<AbiValue>, Vec<std::ops::Range<usize>>) {
        let mut values: Vec<AbiValue> = (0..n)
            .map(|_| AbiValue::new(LowerType::I64, 0, 8))
            .collect();
        let mut spans: Vec<std::ops::Range<usize>> = (0..n).map(|i| i..i + 1).collect();
        values.extend(tail.clone());
        // Each tail value is its own argument unless it carries a non-zero
        // offset, which marks it as the second value of the previous one.
        for (i, v) in tail.iter().enumerate() {
            let at = n + i;
            if v.offset != 0 {
                spans.last_mut().unwrap().end = at + 1;
            } else {
                spans.push(at..at + 1);
            }
        }
        (values, spans)
    }

    fn disagreement(
        target: TrustCgAbiTarget,
        variant: AArch64AbiVariant,
        rustc: (Vec<AbiValue>, Vec<std::ops::Range<usize>>),
        declared: (Vec<AbiValue>, Vec<std::ops::Range<usize>>),
    ) -> Option<PlacementDisagreement> {
        let r = signature_byte_homes(target, variant, &rustc.0, &rustc.1, false).unwrap();
        let d = signature_byte_homes(target, variant, &declared.0, &declared.1, false).unwrap();
        signature_placement_disagreement(&live_bytes(&rustc.0, &rustc.1), &r, &d)
    }

    /// THE RULE, per family, on each target's own classifier. Each row states
    /// what rustc passes and what a declaration passes; the verdict is the
    /// first argument byte whose home differs.
    #[test]
    fn signature_placement_disagreement_table() {
        use AArch64AbiVariant::{Aapcs64, Darwin};
        use TrustCgAbiTarget::{AArch64, X86_64};
        let bytes4 = || AbiValue::new(LowerType::Array(Box::new(LowerType::I8), 4), 0, 4);
        let i32v = || AbiValue::new(LowerType::I32, 0, 4);
        let narrow_rustc = || after_u64s(8, vec![i32v(), i32v()]);
        let narrow_decl = || after_u64s(8, vec![bytes4(), i32v()]);
        // Darwin: a 4-byte cast after eight integers. The composite takes an
        // 8-byte slot where rustc's i32 takes 4, so the NEXT argument moves:
        // [sp+4] against [sp+8].
        let d = disagreement(AArch64, Darwin, narrow_rustc(), narrow_decl()).expect("disagrees");
        assert_eq!(d.arg, 9);
        assert_eq!(d.rustc, Some(ByteHome::Stack { offset: 4 }));
        assert_eq!(d.declared, Some(ByteHome::Stack { offset: 8 }));
        // The same with registers to spare agrees.
        assert_eq!(
            disagreement(
                AArch64,
                Darwin,
                after_u64s(2, vec![i32v(), i32v()]),
                after_u64s(2, vec![bytes4(), i32v()])
            ),
            None
        );
        // Base AAPCS64 gives every stack argument an 8-byte slot: agrees.
        assert_eq!(
            disagreement(AArch64, Aapcs64, narrow_rustc(), narrow_decl()),
            None
        );
        // System V gives every stack argument an eightbyte: agrees.
        assert_eq!(
            disagreement(X86_64, Darwin, narrow_rustc(), narrow_decl()),
            None
        );

        // A Pair at the last integer register: rustc's lane 0 in x7, the
        // whole-slot composite wholly on the stack.
        let pair_rustc = |n| {
            after_u64s(
                n,
                vec![
                    AbiValue::new(LowerType::I64, 0, 8),
                    AbiValue::new(LowerType::I64, 8, 8),
                ],
            )
        };
        let slot = |n| {
            after_u64s(
                n,
                vec![AbiValue::new(
                    LowerType::Array(Box::new(LowerType::I64), 2),
                    0,
                    16,
                )],
            )
        };
        let d = disagreement(AArch64, Darwin, pair_rustc(7), slot(7)).expect("disagrees");
        assert_eq!((d.arg, d.byte), (7, 0));
        assert_eq!(d.rustc, Some(ByteHome::Gpr { reg: 7, byte: 0 }));
        // x86-64: R9 is the last integer register after five.
        let d = disagreement(X86_64, Darwin, pair_rustc(5), slot(5)).expect("disagrees");
        assert_eq!((d.arg, d.byte), (5, 0));
        // Two independent values — the pair lane — agree on both.
        assert_eq!(
            disagreement(AArch64, Darwin, pair_rustc(7), pair_rustc(7)),
            None
        );
        assert_eq!(
            disagreement(X86_64, Darwin, pair_rustc(5), pair_rustc(5)),
            None
        );

        // A float pair at the last FP register: rustc's two doubles against a
        // declared two-double HFA.
        let f64s = |n: usize, tail: Vec<AbiValue>| {
            let mut v: Vec<AbiValue> = (0..n)
                .map(|_| AbiValue::new(LowerType::F64, 0, 8))
                .collect();
            let mut s: Vec<std::ops::Range<usize>> = (0..n).map(|i| i..i + 1).collect();
            let at = v.len();
            v.extend(tail.clone());
            s.push(at..at + tail.len());
            (v, s)
        };
        let hfa = f64s(
            7,
            vec![AbiValue::new(
                LowerType::Struct(vec![LowerType::F64, LowerType::F64]),
                0,
                16,
            )],
        );
        let two = f64s(
            7,
            vec![
                AbiValue::new(LowerType::F64, 0, 8),
                AbiValue::new(LowerType::F64, 8, 8),
            ],
        );
        assert!(disagreement(AArch64, Darwin, two.clone(), hfa).is_some());
        assert_eq!(disagreement(AArch64, Darwin, two.clone(), two), None);

        // A carrier WIDER than its lane is conformant: a 32-bit carrier for a
        // 1-byte lane homes only that byte.
        let narrow_lane = after_u64s(1, vec![AbiValue::new(LowerType::I8, 0, 1)]);
        let wide_carrier = after_u64s(1, vec![AbiValue::new(LowerType::I32, 0, 1)]);
        assert_eq!(
            disagreement(X86_64, Darwin, narrow_lane.clone(), wide_carrier.clone()),
            None
        );
        assert_eq!(
            disagreement(AArch64, Darwin, narrow_lane, wide_carrier),
            None
        );

        // A byval image is on the stack even with registers free, while a
        // declared 16-byte composite would ride two GPRs: disagrees.
        let byval = |n| {
            after_u64s(
                n,
                vec![AbiValue {
                    ty: LowerType::Array(Box::new(LowerType::I64), 2),
                    offset: 0,
                    live: 16,
                    byval: true,
                }],
            )
        };
        assert!(disagreement(X86_64, Darwin, byval(1), slot(1)).is_some());
        // At exhaustion both are on the stack at one offset: agrees.
        assert_eq!(disagreement(X86_64, Darwin, byval(6), slot(6)), None);
    }
}
