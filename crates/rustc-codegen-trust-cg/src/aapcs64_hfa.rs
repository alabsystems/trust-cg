// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

//! A deliberately narrow carrier for rustc's Linux AAPCS64 HFA Cast decision.
//! This consumes an ABI decision; it is neither a replacement ABI classifier
//! nor a proof of rustc/MIR/TrustIR equivalence. Other PassModes are untouched.

use rustc_abi::{BackendRepr, HasDataLayout, Primitive, RegKind};
use rustc_target::callconv::{ArgAttribute, ArgExtension, PassMode};
use trust_ir::Ty;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct HfaCarrierPlan {
    pub(super) lane_ty: Ty,
    pub(super) integer_lane_ty: Ty,
    pub(super) lanes: usize,
    pub(super) lane_bytes: u64,
    pub(super) scalarized: bool,
}

impl HfaCarrierPlan {
    pub(super) fn carrier_ty(&self) -> Ty {
        if self.scalarized {
            self.lane_ty.clone()
        } else {
            Ty::Tuple(vec![self.lane_ty.clone(); self.lanes])
        }
    }

    pub(super) fn scalar_projection_layout_matches(
        &self,
        field_count: usize,
        field_index: usize,
        offset: u64,
        size: u64,
        align: u64,
    ) -> bool {
        self.scalarized
            && self.lanes == 1
            && field_count == 1
            && field_index == 0
            && offset == 0
            && size == self.lane_bytes
            && align == self.lane_bytes
    }
}

pub(super) fn is_float_cast(mode: &PassMode) -> bool {
    // `CastTarget::prefix` is an `ArrayVec<Reg, 8>` on this compiler (it was an
    // `[Option<Reg>; 8]` on the stock nightly the crate used to pin), so the
    // occupied prefix registers are exactly the elements — nothing to flatten.
    crate::cast_abi::view(mode).is_some_and(|view| {
        view.target.rest.unit.kind == RegKind::Float
            || view
                .target
                .prefix
                .iter()
                .any(|reg| reg.kind == RegKind::Float)
    })
}

/// `None` means no float Cast was requested, NOT an unrepresentable HFA.
/// Any float-bearing Cast that cannot be represented exactly is an error.
/// `slot` describes the bridge's existing byte storage, not a new ABI layout.
/// Without a slot, only an existing exact single floating scalar is admitted.
pub(super) fn plan_from_pass_mode(
    mode: &PassMode,
    rust_size: u64,
    rust_align: u64,
    slot: Option<(u64, u64, bool)>,
    scalar_ty: Option<&Ty>,
) -> Result<Option<HfaCarrierPlan>, String> {
    let Some(view) = crate::cast_abi::view(mode) else {
        return Ok(None);
    };
    let cast = view.target;
    if !is_float_cast(mode) {
        return Ok(None);
    }
    let reject = |why: &str| {
        Err(format!(
            "[TCG-AAPCS64-HFA] rustc float Cast cannot preserve the bridge byte carrier: {why}"
        ))
    };
    if view.has_padding() || !cast.prefix.is_empty() || cast.rest_offset.is_some() {
        return reject("padding, prefix, or displaced rest is unsupported");
    }
    if cast.rest.unit.kind != RegKind::Float || !cast.rest.is_consecutive {
        return reject("expected consecutive homogeneous float registers");
    }
    if cast.attrs.contains(ArgAttribute::InReg) || cast.attrs.arg_ext != ArgExtension::None {
        return reject("extra register/extension ABI attributes are unsupported");
    }
    let (lane_ty, integer_lane_ty, lane_bytes) = match cast.rest.unit.size.bits() {
        32 => (Ty::F32, Ty::I32, 4),
        64 => (Ty::F64, Ty::I64, 8),
        _ => return reject("only f32/f64 HFA lanes are implemented"),
    };
    let total = cast.rest.total.bytes();
    if total != rust_size || total % lane_bytes != 0 || !(1..=4).contains(&(total / lane_bytes)) {
        return reject(
            "Cast extent must equal the Rust layout and contain one to four whole lanes",
        );
    }
    let scalarized = match slot {
        Some((slot_size, slot_align, has_tag)) => {
            if has_tag || slot_size != total || slot_align != lane_bytes || rust_align != slot_align
            {
                return reject(
                    "tag, extent, or alignment differs from the existing uniform lane storage",
                );
            }
            false
        }
        // The existing bridge represents single-field float newtypes as bare
        // scalars. One exactly-sized/aligned HFA lane has the same register and
        // stack placement. Do not manufacture a memory slot or numeric cast.
        None if total == lane_bytes && rust_align == lane_bytes && scalar_ty == Some(&lane_ty) => {
            true
        }
        None => {
            return reject("no supported aggregate memory slot or exact one-lane scalar carrier");
        }
    };
    Ok(Some(HfaCarrierPlan {
        lane_ty,
        integer_lane_ty,
        lanes: (total / lane_bytes) as usize,
        lane_bytes,
        scalarized,
    }))
}

/// Whether this `PassMode` is the FLOAT SCALAR PAIR the carrier below handles —
/// a `PassMode::Pair` whose layout is a `ScalarPair` of two floats of the SAME
/// width. Its name is deliberately parallel to [`is_float_cast`]: both answer
/// "does rustc want this value in the floating-point register file", from
/// rustc's own decision, for two different spellings of that decision.
pub(super) fn is_float_scalar_pair<C: HasDataLayout>(
    cx: &C,
    mode: &PassMode,
    repr: BackendRepr,
) -> bool {
    float_scalar_pair_shape(cx, mode, repr).is_some()
}

/// `(format, lane bytes, offset of the second scalar)` for a float `ScalarPair`.
fn float_scalar_pair_shape<C: HasDataLayout>(
    cx: &C,
    mode: &PassMode,
    repr: BackendRepr,
) -> Option<(rustc_abi::Float, u64, u64)> {
    if !matches!(mode, PassMode::Pair(..)) {
        return None;
    }
    let pair = crate::scalar_pair::view(repr)?;
    let (a, b) = (pair.a, pair.b);
    let (Primitive::Float(fa), Primitive::Float(fb)) = (a.primitive(), b.primitive()) else {
        return None;
    };
    if fa != fb {
        return None;
    }
    // Preserve the declared ABI offset; derive it only on the legacy API.
    let second = pair.second_offset(cx).bytes();
    Some((fa, a.size(cx).bytes(), second))
}

/// THE FLOAT SCALAR-PAIR CARRIER: a `#[repr(Rust)]` `{ f64, f64 }` / `{ f32, f32 }`
/// returned or passed BY VALUE.
///
/// # Why this exists, and why it reuses `HfaCarrierPlan`
///
/// rustc classifies such an aggregate `PassMode::Pair`, which means two ABI
/// values of the scalars' own classes — `d0`/`d1` (AAPCS64 §6.4.2 assigns each
/// returned value the next SIMD&FP register; LLVM's `RetCC_AArch64_AAPCS` does
/// exactly this for a `{double,double}` first-class aggregate) and `xmm0`/`xmm1`
/// on System V. The bridge's uniform-integer lane slot erases that: it declares
/// `Tuple([I64, I64])`, which trust-cg's classifier places in the GPR PAIR.
/// MEASURED 2026-09-11 across a real codegen boundary, `-Copt-level=0` and `=2`:
/// LLVM's callee is `fmul d0 / fmul d1 / ret` and trust-cg's is
/// `ldr x0,[x2] ; ldr x1,[x2,#8] ; ret`; both mixed-link directions returned 0
/// where the oracle returns 42.
///
/// The FIX is not new machinery — it is the carrier the Linux AAPCS64 HFA `Cast`
/// lane already uses. A `HfaCarrierPlan` states "this ABI value is `lanes`
/// floating lanes of `lane_bytes`", and every consumer of that plan already
/// exists and is exercised: `carrier_ty()` declares `Tuple([F64; n])`,
/// `store_incoming_aggregate_param` unpacks the incoming floating lanes into the
/// unchanged integer storage slot through `extract_hfa_storage_lane`, and
/// `copy_memory_aggregate_call_result` relocates a call result the same way.
/// This function therefore CONSUMES a second rustc spelling of the same decision
/// rather than adding a second lowering of it.
///
/// The bytes do not move: the lane type only changes which register file the
/// lane rides in and which mov opcode carries it. A `Bitcast` (not a numeric
/// conversion) preserves the bit pattern into the integer storage lane.
///
/// `None` means rustc did not ask for this (not a Pair, not two equal floats).
/// A float pair whose byte carrier cannot be preserved EXACTLY is an error, not
/// a silent fall-through to the integer lanes — the whole point is that the
/// fall-through was the bug.
pub(super) fn float_scalar_pair_carrier<C: HasDataLayout>(
    cx: &C,
    mode: &PassMode,
    repr: BackendRepr,
    rust_size: u64,
    rust_align: u64,
    slot: Option<(u64, u64, bool)>,
) -> Result<Option<HfaCarrierPlan>, String> {
    let Some((float, lane_bytes, second_offset)) = float_scalar_pair_shape(cx, mode, repr) else {
        return Ok(None);
    };
    let reject = |why: &str| {
        Err(format!(
            "[TCG-AAPCS64-HFA] rustc float ScalarPair cannot preserve the bridge byte carrier: \
             {why}"
        ))
    };
    // Recognition retains unsupported floating pairs so they cannot fall
    // through to integer aggregate lanes. Validate the actual format first.
    if let Err(why) = crate::abi_primitive::ieee_bits(float) {
        return reject(why);
    }
    let (lane_ty, integer_lane_ty) = match lane_bytes {
        4 => (Ty::F32, Ty::I32),
        8 => (Ty::F64, Ty::I64),
        _ => return reject("only f32/f64 scalar-pair lanes are implemented"),
    };
    // The two lanes must TILE the value: second scalar exactly one lane in, and
    // the whole aggregate exactly two lanes wide at the lane's own alignment.
    // Anything else (padding between the scalars, a wider aggregate alignment)
    // would make the uniform lane storage disagree with the ABI value.
    if second_offset != lane_bytes {
        return reject("the second scalar does not start exactly one lane in");
    }
    if rust_size != lane_bytes * 2 || rust_align != lane_bytes {
        return reject("the Rust layout is not exactly two lanes at the lane alignment");
    }
    match slot {
        Some((slot_size, slot_align, has_tag)) => {
            if has_tag || slot_size != rust_size || slot_align != lane_bytes {
                return reject(
                    "tag, extent, or alignment differs from the existing uniform lane storage",
                );
            }
        }
        // Unlike the one-lane `Cast` carrier, there is no scalarized form of a
        // two-lane pair: without a memory slot there is nothing to unpack the
        // two lanes into. Refuse rather than invent one.
        None => return reject("no supported aggregate memory slot for a two-lane float pair"),
    }
    Ok(Some(HfaCarrierPlan {
        lane_ty,
        integer_lane_ty,
        lanes: 2,
        lane_bytes,
        scalarized: false,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_abi::{Reg, Size};
    use rustc_target::callconv::{ArgAttributes, CastTarget, Uniform};

    fn cast(unit: Reg, lanes: u64) -> PassMode {
        crate::cast_abi::fixture(
            CastTarget::from(Uniform::consecutive(
                unit,
                Size::from_bytes(unit.size.bytes() * lanes),
            )),
            false,
        )
    }

    #[test]
    fn accepts_exact_f32_f64_hfa_one_through_four_lanes() {
        for (reg, lane_ty) in [(Reg::f32(), Ty::F32), (Reg::f64(), Ty::F64)] {
            for lanes in 1..=4 {
                let size = reg.size.bytes() * lanes;
                let align = reg.size.bytes();
                let plan = plan_from_pass_mode(
                    &cast(reg, lanes),
                    size,
                    align,
                    Some((size, align, false)),
                    None,
                )
                .unwrap()
                .unwrap();
                assert_eq!(
                    plan.carrier_ty(),
                    Ty::Tuple(vec![lane_ty.clone(); lanes as usize])
                );
                assert_eq!(plan.lane_bytes, align);
            }
        }
    }

    #[test]
    fn non_float_modes_are_not_reclassified() {
        for mode in [
            PassMode::Ignore,
            PassMode::Direct(ArgAttributes::new()),
            PassMode::Pair(ArgAttributes::new(), ArgAttributes::new()),
            cast(Reg::i64(), 2),
        ] {
            assert!(
                plan_from_pass_mode(&mode, 16, 8, None, None)
                    .unwrap()
                    .is_none()
            );
        }
    }

    #[test]
    fn malformed_float_casts_never_fall_back() {
        let base = cast(Reg::f64(), 3);
        let reject = |mode: &PassMode, size, align, slot| {
            let err = plan_from_pass_mode(mode, size, align, slot, None).unwrap_err();
            assert!(err.starts_with("[TCG-AAPCS64-HFA]"), "{err}");
        };
        for mutation in 0..9 {
            let mut mode = base.clone();
            if mutation == 0 {
                crate::cast_abi::fixture_padding(&mut mode, true);
            }
            let PassMode::Cast { cast, .. } = &mut mode else {
                unreachable!()
            };
            match mutation {
                0 => (),
                // `CastTarget::prefix` is an `ArrayVec<Reg, 8>` on this
                // compiler and starts EMPTY, so "has a prefix register" is a
                // push, not an index assignment.
                1 => cast.prefix.push(Reg::i64()),
                2 => cast.rest_offset = Some(Size::from_bytes(8)),
                3 => cast.rest.is_consecutive = false,
                4 => cast.attrs.arg_ext = ArgExtension::Zext,
                5 => {
                    cast.attrs.set(ArgAttribute::InReg);
                }
                6 => cast.rest.unit.size = Size::from_bytes(2),
                7 => cast.rest.total = Size::from_bytes(40),
                8 => cast.rest.total = Size::from_bytes(23),
                _ => unreachable!(),
            }
            reject(&mode, 24, 8, Some((24, 8, false)));
        }
        for (size, align, slot) in [
            (16, 8, Some((24, 8, false))),
            (24, 8, None),
            (24, 8, Some((24, 8, true))),
            (24, 8, Some((16, 8, false))),
            (24, 8, Some((24, 4, false))),
            (24, 16, Some((24, 8, false))),
        ] {
            reject(&base, size, align, slot);
        }
        let mut prefix_float = cast(Reg::i64(), 3);
        let PassMode::Cast { cast: target, .. } = &mut prefix_float else {
            unreachable!()
        };
        target.prefix.push(Reg::f64());
        reject(&prefix_float, 24, 8, Some((24, 8, false)));
        for lanes in [0, 5] {
            reject(
                &cast(Reg::f64(), lanes),
                lanes * 8,
                8,
                Some((lanes * 8, 8, false)),
            );
        }
    }

    // ---------------------------------------------------------------------
    // The float SCALAR-PAIR carrier (`PassMode::Pair`, not `PassMode::Cast`).
    // ---------------------------------------------------------------------

    /// A minimal `HasDataLayout` — only scalar sizes and alignments are read,
    /// and those come from the `Scalar`s themselves.
    struct Dl(rustc_abi::TargetDataLayout);
    impl HasDataLayout for Dl {
        fn data_layout(&self) -> &rustc_abi::TargetDataLayout {
            &self.0
        }
    }
    fn dl() -> Dl {
        Dl(rustc_abi::TargetDataLayout::default())
    }

    fn float(bytes: u64) -> rustc_abi::Scalar {
        rustc_abi::Scalar::Initialized {
            value: Primitive::Float(if bytes == 4 {
                rustc_abi::Float::F32
            } else {
                rustc_abi::Float::F64
            }),
            valid_range: rustc_abi::WrappingRange::full(rustc_abi::Size::from_bytes(bytes)),
        }
    }

    fn int(bytes: u64) -> rustc_abi::Scalar {
        rustc_abi::Scalar::Initialized {
            value: Primitive::Int(
                if bytes == 4 {
                    rustc_abi::Integer::I32
                } else {
                    rustc_abi::Integer::I64
                },
                true,
            ),
            valid_range: rustc_abi::WrappingRange::full(rustc_abi::Size::from_bytes(bytes)),
        }
    }

    fn pair_mode() -> PassMode {
        PassMode::Pair(ArgAttributes::new(), ArgAttributes::new())
    }

    #[test]
    fn accepts_an_exact_f32_and_f64_scalar_pair() {
        for (bytes, lane_ty, int_ty) in [(4u64, Ty::F32, Ty::I32), (8, Ty::F64, Ty::I64)] {
            let plan = float_scalar_pair_carrier(
                &dl(),
                &pair_mode(),
                crate::scalar_pair::canonical(float(bytes), float(bytes), &dl()),
                bytes * 2,
                bytes,
                Some((bytes * 2, bytes, false)),
            )
            .unwrap()
            .unwrap();
            assert_eq!(plan.lanes, 2);
            assert_eq!(plan.lane_bytes, bytes);
            assert_eq!(plan.lane_ty, lane_ty);
            assert_eq!(plan.integer_lane_ty, int_ty);
            assert!(!plan.scalarized);
            assert_eq!(plan.carrier_ty(), Ty::Tuple(vec![lane_ty.clone(); 2]));
        }
    }

    #[test]
    fn a_non_pair_or_non_float_pair_is_not_reclassified() {
        // Not a `Pair` at all.
        for mode in [
            PassMode::Ignore,
            PassMode::Direct(ArgAttributes::new()),
            cast(rustc_abi::Reg::f64(), 2),
        ] {
            assert!(
                float_scalar_pair_carrier(
                    &dl(),
                    &mode,
                    crate::scalar_pair::canonical(float(8), float(8), &dl()),
                    16,
                    8,
                    Some((16, 8, false)),
                )
                .unwrap()
                .is_none()
            );
        }
        // A `Pair` whose scalars are not both the same float: an integer pair,
        // a mixed pair, and two floats of different widths. Each stays on the
        // uniform integer lane storage, where `[TCG-RET-ABI]` decides it.
        for repr in [
            crate::scalar_pair::canonical(int(8), int(8), &dl()),
            crate::scalar_pair::canonical(int(8), float(8), &dl()),
            crate::scalar_pair::canonical(float(8), int(8), &dl()),
            crate::scalar_pair::canonical(float(4), float(8), &dl()),
        ] {
            assert!(
                float_scalar_pair_carrier(&dl(), &pair_mode(), repr, 16, 8, Some((16, 8, false)))
                    .unwrap()
                    .is_none(),
                "{repr:?}"
            );
        }
        // Not a `ScalarPair` layout at all.
        assert!(
            float_scalar_pair_carrier(
                &dl(),
                &pair_mode(),
                BackendRepr::Memory { sized: true },
                16,
                8,
                Some((16, 8, false)),
            )
            .unwrap()
            .is_none()
        );
    }

    #[test]
    fn a_float_pair_whose_carrier_cannot_be_preserved_is_an_error_not_a_fallback() {
        let repr = crate::scalar_pair::canonical(float(8), float(8), &dl());
        let reject = |size, align, slot| {
            let err = float_scalar_pair_carrier(&dl(), &pair_mode(), repr, size, align, slot)
                .unwrap_err();
            assert!(err.starts_with("[TCG-AAPCS64-HFA]"), "{err}");
        };
        // The Rust layout is not exactly two lanes at the lane alignment.
        reject(24, 8, Some((24, 8, false)));
        reject(16, 16, Some((16, 8, false)));
        // No memory slot at all: there is no scalarized form of a two-lane pair.
        reject(16, 8, None);
        // The slot disagrees with the ABI value's extent, alignment, or carries
        // a Direct enum tag.
        reject(16, 8, Some((24, 8, false)));
        reject(16, 8, Some((16, 4, false)));
        reject(16, 8, Some((16, 8, true)));
    }

    #[test]
    fn is_float_scalar_pair_agrees_with_the_carrier_builder() {
        assert!(is_float_scalar_pair(
            &dl(),
            &pair_mode(),
            crate::scalar_pair::canonical(float(8), float(8), &dl())
        ));
        assert!(!is_float_scalar_pair(
            &dl(),
            &pair_mode(),
            crate::scalar_pair::canonical(int(8), int(8), &dl())
        ));
        assert!(!is_float_scalar_pair(
            &dl(),
            &PassMode::Direct(ArgAttributes::new()),
            crate::scalar_pair::canonical(float(8), float(8), &dl())
        ));
    }

    #[test]
    fn single_lane_newtype_requires_the_exact_existing_float_scalar() {
        for (reg, lane_ty) in [(Reg::f32(), Ty::F32), (Reg::f64(), Ty::F64)] {
            let bytes = reg.size.bytes();
            let plan = plan_from_pass_mode(&cast(reg, 1), bytes, bytes, None, Some(&lane_ty))
                .unwrap()
                .unwrap();
            assert!(plan.scalarized);
            assert_eq!(plan.carrier_ty(), lane_ty);
            assert!(plan.scalar_projection_layout_matches(1, 0, 0, bytes, bytes));
            for (count, index, offset, size, align) in [
                (2, 0, 0, bytes, bytes),
                (1, 1, 0, bytes, bytes),
                (1, 0, bytes, bytes, bytes),
                (1, 0, 0, bytes * 2, bytes),
                (1, 0, 0, bytes, bytes * 2),
            ] {
                assert!(!plan.scalar_projection_layout_matches(count, index, offset, size, align));
            }
            for wrong_ty in [
                Ty::I32,
                Ty::I64,
                Ty::Ptr,
                if lane_ty == Ty::F32 { Ty::F64 } else { Ty::F32 },
                Ty::Tuple(vec![lane_ty.clone()]),
            ] {
                assert!(
                    plan_from_pass_mode(&cast(reg, 1), bytes, bytes, None, Some(&wrong_ty))
                        .is_err()
                );
            }
            assert!(
                plan_from_pass_mode(&cast(reg, 2), bytes * 2, bytes, None, Some(&lane_ty)).is_err()
            );
            assert!(
                plan_from_pass_mode(&cast(reg, 1), bytes, bytes * 2, None, Some(&lane_ty)).is_err()
            );
        }
    }
}
