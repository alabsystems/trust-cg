// rustc_codegen_trust_cg/box_deref_facts.rs - Box deref casts and their carried facts
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

//! What the bridge does with a `CastKind::BoxDerefTransmute` cast.
//!
//! Rust defines the cast as undefined behaviour unless its operand is valid as
//! a `Box`. This backend has no model that establishes that, so a body holding
//! the cast is refused with `[TCG-BOX-DEREF]`. The one exception is a compiler
//! that exports Box-deref validity facts (build capability
//! `rustc_box_deref_facts`, probed in `build.rs`): there a cast whose site the
//! COMPILER's own acceptance check admits under its fail-closed admission is
//! emitted as trust-ir `Inst::BoxDeref`, carrying the compiler's fact
//! translated to trust-ir's `BoxValidityFact`.
//!
//! Three build configurations, one refusal text:
//!
//! - no `rustc_session_split`: the compiler has no such cast kind;
//! - `rustc_session_split` without `rustc_box_deref_facts` (Trust 0.13): every
//!   body holding the cast is refused, as before this module existed;
//! - `rustc_box_deref_facts`: [`plan`] asks the compiler per site and refuses
//!   the WHOLE body when any cast of it is not admitted.
//!
//! Evidence boundary. An emitted `Inst::BoxDeref` is not a proof of anything
//! and this module adds no evidence to it. The fact is a NAMED ASSUMPTION of
//! the producing compiler; the translation copies its root, its standing
//! assumptions and its session and can only refuse, never strengthen. What
//! trust-ir has no spelling for (a root outside its five, zero-size evidence,
//! a wide or instance-dependent pointee) is refused here. Emission is not
//! admission: the trust-cg license decides afterwards, and its default floor
//! refuses every `Inst::BoxDeref` (`trust_cg_lower::admit_box_derefs`).
//!
//! What the compiler's fail-closed admission has already decided, and trust-ir
//! therefore does not carry: the judged body has no failed or unknown verifier
//! row, the verifier's own engine stopped charging the cast, the walk's census
//! took no `vec![..]` exemption, the root is one of the four the engine has,
//! and a local callee the root rests on was verified by a session that stops
//! on a failed row. This module never states another admission.

use rustc_middle::mir;
use trust_ir::box_validity as ir;

/// The refusal every unadmitted Box deref gets. A reason is appended after
/// `": "` when the compiler gave one; the prefix never changes.
pub(crate) const REFUSAL: &str =
    "[TCG-BOX-DEREF] BoxDerefTransmute requires an unmodeled Box validity obligation";

fn refuse(why: impl std::fmt::Display) -> String {
    format!("{REFUSAL}: {why}")
}

/// One admitted cast site of the body being lowered.
struct PlanRow {
    fact: ir::BoxValidityFact,
    /// How many casts of the lowered body carry the site.
    expected: u32,
}

/// The admitted Box deref casts of one lowering attempt: empty for a body that
/// holds no such cast. A body with an unadmitted cast has no plan ([`plan`]
/// refuses it).
#[derive(Default)]
pub(crate) struct BoxDerefPlan {
    rows: Vec<PlanRow>,
}

impl BoxDerefPlan {
    /// Whether the lowered body holds no admitted cast.
    pub(crate) fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    /// The conservation check of one lowering attempt: `module` holds exactly
    /// one `Inst::BoxDeref` per admitted cast of the lowered body, each with
    /// the planned fact, and no other. A lowering route that consumed a cast
    /// as a plain copy (dropping the fact), skipped it, duplicated it or
    /// invented one is refused here.
    pub(crate) fn check_emitted(&self, module: &trust_ir::Module) -> Result<(), String> {
        let mut found = vec![0u32; self.rows.len()];
        for func in &module.functions {
            for node in func.blocks.iter().flat_map(|block| &block.body) {
                let trust_ir::Inst::BoxDeref { fact, .. } = &node.inst else {
                    continue;
                };
                let Some(row) = self.rows.iter().position(|row| row.fact == **fact) else {
                    return Err(refuse(format!(
                        "function `{}` holds a BoxDeref no admitted cast of the lowered body \
                         accounts for (site ordinal {})",
                        func.name, fact.site.ordinal
                    )));
                };
                found[row] += 1;
            }
        }
        for (row, found) in self.rows.iter().zip(found) {
            if found != row.expected {
                return Err(refuse(format!(
                    "the lowering emitted {found} BoxDeref instruction(s) for site ordinal {} \
                     and the lowered body holds {} cast(s) of it: a lowering route consumed the \
                     cast without its fact, or did not lower it",
                    row.fact.site.ordinal, row.expected
                )));
            }
        }
        Ok(())
    }
}

/// What rustc's layout says about the pointee of one Box deref cast.
#[derive(Clone, Copy, Debug)]
pub(crate) struct PointeeLayout {
    pub(crate) sized: bool,
    pub(crate) zero_sized: bool,
    pub(crate) uninhabited: bool,
    /// Size in bytes.
    pub(crate) size: u64,
    /// ABI alignment in bytes.
    pub(crate) align: u64,
}

/// The pointee type an emitted `Inst::BoxDeref` states. Only
/// [`admit_emission`] constructs one, so no emission route can skip its
/// gates.
#[derive(Debug)]
pub(crate) struct AdmittedPointee(trust_ir::Ty);

impl AdmittedPointee {
    pub(crate) fn into_ty(self) -> trust_ir::Ty {
        self.0
    }
}

/// Whether trust-ir lays `candidate` out with exactly `size` bytes and
/// `align` bytes of alignment, and has a value of it. Equality, not a bound:
/// the instruction's `Aligned` and `Dereferenceable` conjuncts are stated
/// over this type.
pub(crate) fn states_layout(
    module: &trust_ir::Module,
    candidate: &trust_ir::Ty,
    size: u64,
    align: u64,
) -> bool {
    let layouts = module.layout_table();
    !layouts.ty_is_uninhabited(candidate)
        && layouts.ty_layout(candidate).is_ok_and(|shape| {
            size.checked_mul(8) == Some(shape.size_bits)
                && align
                    .checked_mul(8)
                    .is_some_and(|bits| shape.align_bits == Some(bits))
        })
}

/// The integer lane and lane count whose array has `size` bytes and `align`
/// bytes of alignment: the unsigned integer of `align` bytes, `size / align`
/// times. `None` for an alignment with no such integer and for a size that is
/// not a whole number of lanes.
pub(crate) fn lane_array(size: u64, align: u64) -> Option<(trust_ir::Ty, u64)> {
    let lane = match align {
        1 => trust_ir::Ty::U8,
        2 => trust_ir::Ty::U16,
        4 => trust_ir::Ty::U32,
        8 => trust_ir::Ty::U64,
        _ => return None,
    };
    if size % align != 0 {
        return None;
    }
    Some((lane, size / align))
}

/// Every emission gate of one admitted Box deref cast, in one place.
///
/// Refuses (with [`REFUSAL`]) unless the cast is thin pointer to thin pointer
/// in trust-ir, its operand and result are distinct values, the pointee is
/// sized, of positive size and inhabited in rustc's layout, and a trust-ir
/// type with exactly rustc's size and ABI alignment exists: `natural` (the
/// pointee's own trust-ir type) when it has that layout, else the
/// [`lane_array`]. `name` is the pointee as the refusal prints it.
#[allow(clippy::too_many_arguments)]
pub(crate) fn admit_emission(
    module: &mut trust_ir::Module,
    src_ty: &trust_ir::Ty,
    dst_ty: &trust_ir::Ty,
    operand: trust_ir::ValueId,
    result: trust_ir::ValueId,
    name: &dyn std::fmt::Display,
    layout: PointeeLayout,
    natural: Option<trust_ir::Ty>,
) -> Result<AdmittedPointee, String> {
    if !crate::runtime_pointer_value::is_thin_pointer(src_ty)
        || !crate::runtime_pointer_value::is_thin_pointer(dst_ty)
    {
        return Err(refuse(format!(
            "the cast is not thin pointer to thin pointer in trust-ir ({src_ty:?} -> {dst_ty:?})"
        )));
    }
    if operand == result {
        return Err(refuse(
            "the cast's operand and result share one value, so no instruction can carry the fact",
        ));
    }
    if !layout.sized {
        return Err(refuse(format!(
            "the pointee {name} is unsized, which trust-ir's BoxDeref does not state"
        )));
    }
    if layout.zero_sized {
        return Err(refuse(format!(
            "the pointee {name} is zero-sized, which trust-ir's BoxDeref does not state"
        )));
    }
    if layout.uninhabited {
        return Err(refuse(format!(
            "the pointee {name} is uninhabited, which trust-ir's BoxDeref does not state"
        )));
    }
    let PointeeLayout { size, align, .. } = layout;
    let natural = natural.filter(|candidate| states_layout(module, candidate, size, align));
    let pointee = match natural {
        Some(natural) => Some(natural),
        None => lane_array(size, align)
            .and_then(|(lane, count)| {
                let id = match module.types.iter().position(|ty| *ty == lane) {
                    Some(index) => trust_ir::TyId::new(u32::try_from(index).ok()?),
                    None => module.add_type(lane).ok()?,
                };
                Some(trust_ir::Ty::Array(id, count))
            })
            .filter(|candidate| states_layout(module, candidate, size, align)),
    };
    pointee.map(AdmittedPointee).ok_or_else(|| {
        refuse(format!(
            "no trust-ir pointee type states the layout of {name} (size {size}, align {align})"
        ))
    })
}

#[cfg(test)]
mod emission_tests {
    use super::{PointeeLayout, REFUSAL, admit_emission, lane_array, states_layout};
    use trust_ir::{Module, Ty, ValueId};

    const WORD: PointeeLayout = PointeeLayout {
        sized: true,
        zero_sized: false,
        uninhabited: false,
        size: 8,
        align: 8,
    };

    fn admit(
        src: &Ty,
        dst: &Ty,
        operand: u32,
        result: u32,
        layout: PointeeLayout,
        natural: Option<Ty>,
    ) -> Result<Ty, String> {
        let mut module = Module::new("m");
        admit_emission(
            &mut module,
            src,
            dst,
            ValueId::new(operand),
            ValueId::new(result),
            &"T",
            layout,
            natural,
        )
        .map(super::AdmittedPointee::into_ty)
    }

    fn refusal(result: Result<Ty, String>, why: &str) {
        let error = result.expect_err("the emission gate admitted");
        assert!(error.starts_with(REFUSAL), "{error}");
        assert!(error.contains(why), "expected `{why}` in `{error}`");
    }

    /// The control every refusal below is one mutation away from.
    #[test]
    fn a_thin_sized_inhabited_pointee_with_its_own_layout_is_admitted() {
        assert_eq!(
            admit(&Ty::Ptr, &Ty::Ptr, 0, 1, WORD, Some(Ty::U64)),
            Ok(Ty::U64)
        );
        let typed = Ty::PtrConst(Box::new(Ty::U64));
        assert_eq!(
            admit(&typed, &typed, 0, 1, WORD, Some(Ty::U64)),
            Ok(Ty::U64)
        );
    }

    #[test]
    fn each_cast_shape_gate_refuses_with_its_own_reason() {
        let wide = Ty::FatPtr(trust_ir::FatPtrKind::Str);
        for (src, dst) in [
            (&Ty::U64, &Ty::Ptr),
            (&Ty::Ptr, &Ty::U64),
            (&wide, &Ty::Ptr),
            (&Ty::Ptr, &wide),
        ] {
            refusal(
                admit(src, dst, 0, 1, WORD, Some(Ty::U64)),
                "not thin pointer to thin pointer",
            );
        }
        refusal(
            admit(&Ty::Ptr, &Ty::Ptr, 3, 3, WORD, Some(Ty::U64)),
            "share one value",
        );
    }

    #[test]
    fn each_pointee_layout_gate_refuses_with_its_own_reason() {
        refusal(
            admit(
                &Ty::Ptr,
                &Ty::Ptr,
                0,
                1,
                PointeeLayout {
                    sized: false,
                    ..WORD
                },
                Some(Ty::U64),
            ),
            "is unsized",
        );
        // A zero-sized instance of a generic body: the compiler's fact is
        // instance-independent, so this gate is the only one that sees it.
        refusal(
            admit(
                &Ty::Ptr,
                &Ty::Ptr,
                0,
                1,
                PointeeLayout {
                    zero_sized: true,
                    size: 0,
                    align: 1,
                    ..WORD
                },
                Some(Ty::Unit),
            ),
            "is zero-sized",
        );
        // Positive size and uninhabited, as `(u64, Void)` is in rustc.
        refusal(
            admit(
                &Ty::Ptr,
                &Ty::Ptr,
                0,
                1,
                PointeeLayout {
                    uninhabited: true,
                    ..WORD
                },
                Some(Ty::U64),
            ),
            "is uninhabited",
        );
    }

    #[test]
    fn the_stated_layout_is_exactly_rustcs_or_the_site_is_refused() {
        let module = Module::new("m");
        assert!(states_layout(&module, &Ty::U64, 8, 8));
        // Size and alignment are each an equality.
        assert!(!states_layout(&module, &Ty::U64, 16, 8));
        assert!(!states_layout(&module, &Ty::U64, 4, 8));
        assert!(!states_layout(&module, &Ty::U64, 8, 4));
        assert!(!states_layout(&module, &Ty::U64, 8, 16));
        // A type with no value states nothing. This does not isolate the
        // inhabitedness clause: trust-ir gives no aligned layout to `Never`,
        // none to a tuple and an incoherent one to a struct with a `Never`
        // field, so the layout clause refuses these too. The clause is a
        // second refusal behind rustc's own `uninhabited` bit, which
        // `each_pointee_layout_gate_refuses_with_its_own_reason` pins.
        assert!(module.layout_table().ty_is_uninhabited(&Ty::Never));
        assert!(!states_layout(&module, &Ty::Never, 0, 1));

        // A natural type with another layout is not used: the lane array is.
        let stated = |layout: PointeeLayout, natural: Option<Ty>| {
            let mut module = Module::new("m");
            let pointee = admit_emission(
                &mut module,
                &Ty::Ptr,
                &Ty::Ptr,
                ValueId::new(0),
                ValueId::new(1),
                &"T",
                layout,
                natural,
            )
            .expect("admitted")
            .into_ty();
            assert!(states_layout(&module, &pointee, layout.size, layout.align));
            pointee
        };
        assert!(matches!(stated(WORD, Some(Ty::U32)), Ty::Array(_, 1)));
        assert!(matches!(stated(WORD, None), Ty::Array(_, 1)));
        let pair = PointeeLayout {
            size: 8,
            align: 4,
            ..WORD
        };
        assert!(matches!(stated(pair, Some(Ty::U64)), Ty::Array(_, 2)));

        // No lane: an alignment above eight bytes, and a size that is not a
        // whole number of lanes.
        for (size, align) in [(16, 16), (32, 32), (12, 8), (3, 2), (8, 0), (8, 3)] {
            if align != 0 {
                assert_eq!(lane_array(size, align), None, "{size}/{align}");
            }
            refusal(
                admit(
                    &Ty::Ptr,
                    &Ty::Ptr,
                    0,
                    1,
                    PointeeLayout {
                        size,
                        align,
                        ..WORD
                    },
                    None,
                ),
                "no trust-ir pointee type states the layout",
            );
        }
        assert_eq!(lane_array(8, 4), Some((Ty::U32, 2)));
        assert_eq!(lane_array(3, 1), Some((Ty::U8, 3)));
        assert_eq!(lane_array(6, 2), Some((Ty::U16, 3)));
        assert_eq!(lane_array(24, 8), Some((Ty::U64, 3)));
    }
}

/// Whether `kind` is the Box deref cast.
#[cfg(not(rustc_session_split))]
pub(crate) fn is_box_deref_cast(_kind: &mir::CastKind) -> bool {
    false
}

#[cfg(all(rustc_session_split, not(rustc_box_deref_facts)))]
pub(crate) fn is_box_deref_cast(kind: &mir::CastKind) -> bool {
    matches!(kind, mir::CastKind::BoxDerefTransmute)
}

#[cfg(rustc_box_deref_facts)]
pub(crate) fn is_box_deref_cast(kind: &mir::CastKind) -> bool {
    matches!(kind, mir::CastKind::BoxDerefTransmute(_))
}

#[cfg(not(rustc_box_deref_facts))]
mod refused {
    use rustc_middle::mir::{self, Body};
    use rustc_middle::ty::{Instance, TyCtxt};
    use trust_ir::box_validity as ir;

    use super::{BoxDerefPlan, REFUSAL, is_box_deref_cast};

    /// Whether `body` holds a Box deref cast anywhere.
    fn holds_box_deref_cast(body: &Body<'_>) -> bool {
        use rustc_middle::mir::visit::Visitor;
        use rustc_middle::mir::{Location, Rvalue};
        struct Scan(bool);
        impl<'tcx> Visitor<'tcx> for Scan {
            fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
                if let Rvalue::Cast(kind, ..) = rvalue {
                    self.0 |= is_box_deref_cast(kind);
                }
                self.super_rvalue(rvalue, location);
            }
        }
        let mut scan = Scan(false);
        scan.visit_body(body);
        scan.0
    }

    /// A compiler without Box-deref facts: a body holding the cast is
    /// refused, whatever else is true of it.
    pub(crate) fn plan<'tcx>(
        _tcx: TyCtxt<'tcx>,
        _instance: Instance<'tcx>,
        body: &Body<'tcx>,
    ) -> Result<BoxDerefPlan, String> {
        if holds_box_deref_cast(body) {
            return Err(REFUSAL.to_owned());
        }
        Ok(BoxDerefPlan::default())
    }

    impl BoxDerefPlan {
        /// No fact exists in this build.
        pub(crate) fn fact_for(
            &self,
            _tcx: TyCtxt<'_>,
            _kind: &mir::CastKind,
        ) -> Result<ir::BoxValidityFact, String> {
            Err(REFUSAL.to_owned())
        }

        /// One line per admitted site, for the disclosure. Always empty here.
        pub(crate) fn admitted_lines(&self) -> Vec<String> {
            Vec::new()
        }
    }
}

#[cfg(not(rustc_box_deref_facts))]
pub(crate) use refused::plan;

#[cfg(rustc_box_deref_facts)]
mod carried {
    use rustc_middle::mir::trust_box_deref as facts;
    use rustc_middle::mir::visit::Visitor;
    use rustc_middle::mir::{
        self, Body, BoxDerefSite, Location, Operand, Place, Rvalue, Statement, StatementKind,
    };
    use rustc_middle::ty::{self, Instance, TyCtxt};
    use trust_ir::box_validity as ir;

    use super::{BoxDerefPlan, PlanRow, refuse};

    /// The parts of a cast a site is bound to in the judged MIR. A later MIR
    /// may delete that cast, but it may not move the site onto another source,
    /// result place or target type: then the carried fact would describe a
    /// different operation from the one the producer judged.
    #[derive(Clone, Debug, PartialEq)]
    struct CastBinding<'tcx> {
        destination: Place<'tcx>,
        operand: Operand<'tcx>,
        target: ty::Ty<'tcx>,
    }

    /// Every Box deref cast of `body`, in visit order, one entry per cast,
    /// together with the exact operation its site names.
    fn cast_bindings<'tcx>(body: &Body<'tcx>) -> Vec<(BoxDerefSite, CastBinding<'tcx>)> {
        struct Scan<'tcx>(Vec<(BoxDerefSite, CastBinding<'tcx>)>);
        impl<'tcx> Visitor<'tcx> for Scan<'tcx> {
            fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
                if let StatementKind::Assign(assignment) = &statement.kind {
                    let (destination, rvalue) = &**assignment;
                    if let Rvalue::Cast(mir::CastKind::BoxDerefTransmute(site), operand, target) =
                        rvalue
                    {
                        self.0.push((
                            *site,
                            CastBinding {
                                destination: *destination,
                                operand: operand.clone(),
                                target: *target,
                            },
                        ));
                    }
                }
                self.super_statement(statement, location);
            }
        }
        let mut scan = Scan(Vec::new());
        scan.visit_body(body);
        scan.0
    }

    fn count<'tcx>(casts: &[(BoxDerefSite, CastBinding<'tcx>)], site: BoxDerefSite) -> usize {
        casts.iter().filter(|(other, _)| *other == site).count()
    }

    /// Prove that the rewritten body's sited casts are a multiset subset of
    /// the judged body's exact sited operations. The site-only count catches a
    /// duplicated known site; the exact binding comparison catches a site
    /// rebound to another operand/result/target even when the counts agree.
    fn check_rewritten_casts<S, B>(lowered: &[(S, B)], judged: &[(S, B)]) -> Result<(), String>
    where
        S: Copy + Eq + std::fmt::Debug,
        B: PartialEq + std::fmt::Debug,
    {
        let mut sites = Vec::new();
        for (site, _) in lowered {
            if sites.contains(site) {
                continue;
            }
            sites.push(*site);
            let lowered_count = lowered.iter().filter(|(other, _)| other == site).count();
            let judged_count = judged.iter().filter(|(other, _)| other == site).count();
            if lowered_count > judged_count {
                return Err(format!(
                    "rewritten body holds {lowered_count} cast(s) of known site {site:?}, but the \
                     judged body holds only {judged_count}: the site multiset is not a subset"
                ));
            }
        }

        let mut consumed = vec![false; judged.len()];
        for (site, binding) in lowered {
            let Some(index) =
                judged
                    .iter()
                    .enumerate()
                    .position(|(index, (judged_site, judged_binding))| {
                        !consumed[index] && judged_site == site && judged_binding == binding
                    })
            else {
                return Err(format!(
                    "rewritten cast site {site:?} is rebound from its judged \
                     operand/result/target: rewritten {binding:?}"
                ));
            };
            consumed[index] = true;
        }
        Ok(())
    }

    /// The trust-ir identity of a compiler site: the owner's 128-bit stable
    /// path hash, little-endian, and the ordinal.
    fn ir_site(tcx: TyCtxt<'_>, site: BoxDerefSite) -> ir::BoxDerefSite {
        ir::BoxDerefSite {
            item: tcx.def_path_hash(site.owner).0.to_le_bytes(),
            ordinal: site.ordinal,
        }
    }

    /// The trust-ir root with the SAME name as the compiler's, or a refusal.
    /// trust-ir derives a premise's tier from its root, so a same-name map
    /// cannot raise one. Exhaustive on purpose: a root a later compiler adds
    /// fails this build until it is given a row here.
    fn root(root: facts::BoxValidityRoot) -> Result<ir::PremiseRoot, String> {
        match root {
            facts::BoxValidityRoot::ParamByValue => Ok(ir::PremiseRoot::ParamByValue),
            facts::BoxValidityRoot::AllocPostcondition => Ok(ir::PremiseRoot::AllocPostcondition),
            facts::BoxValidityRoot::ReturnedBoxAssumed => Ok(ir::PremiseRoot::ReturnedBoxAssumed),
            facts::BoxValidityRoot::ReferenceArgBoxValid => {
                Ok(ir::PremiseRoot::ReferenceArgBoxValid)
            }
            // The consumer format names this root, but this compiler does not
            // yet establish the required local-callee certificate chain. A
            // table spelling it is therefore not producer-authentic.
            facts::BoxValidityRoot::ReturnedBoxDischarged => Err(
                "root ReturnedBoxDischarged is representable in trust-ir, but this compiler \
                     exports no admitted producer for it; refusing until that producer exists"
                    .to_owned(),
            ),
            facts::BoxValidityRoot::ReferenceReturnedAssumed
            | facts::BoxValidityRoot::LentSlotAssumed(_) => Err(format!(
                "root {root:?} has no trust-ir spelling (wire v68 names five roots)"
            )),
        }
    }

    fn conjunct(conjunct: facts::BoxValidityConjunct) -> ir::ValidityConjunct {
        match conjunct {
            facts::BoxValidityConjunct::NonNull => ir::ValidityConjunct::NonNull,
            facts::BoxValidityConjunct::Aligned => ir::ValidityConjunct::Aligned,
            facts::BoxValidityConjunct::Dereferenceable => ir::ValidityConjunct::Dereferenceable,
            facts::BoxValidityConjunct::MetadataValid => ir::ValidityConjunct::MetadataValid,
        }
    }

    fn standing(assumption: facts::BoxStandingAssumption) -> ir::StandingAssumption {
        match assumption {
            facts::BoxStandingAssumption::SafeBody => ir::StandingAssumption::SafeBody,
            facts::BoxStandingAssumption::SoundCallees => ir::StandingAssumption::SoundCallees,
            facts::BoxStandingAssumption::BoxUnique => ir::StandingAssumption::BoxUnique,
        }
    }

    /// The compiler's fact as a trust-ir fact for the site `site`, or why it
    /// has no trust-ir spelling.
    ///
    /// Total and fail-closed: every enum of the compiler's fact is matched
    /// exhaustively, and each value trust-ir cannot state is a refusal. Copied
    /// faithfully: the conjunct list in the compiler's order, per conjunct the
    /// root and the standing assumptions the compiler listed, and the session.
    /// The standing set is the compiler's own (trust-ir's validator then
    /// requires it to be the pinned three), and a session other than the
    /// unoptimized proof-session pipeline is refused. Two fields are constants
    /// this function supplies, neither a strengthening: the session, which is
    /// the proof snapshot because every premise was just required to be one,
    /// and the non-claim list, which is trust-ir's pinned one.
    pub(super) fn translate(
        fact: &facts::BoxValidityFact,
        site: ir::BoxDerefSite,
    ) -> Result<ir::BoxValidityFact, String> {
        if !fact.is_well_formed() {
            return Err("the compiler's fact is not well formed".to_owned());
        }
        match fact.pointee {
            facts::BoxPointeeShape::Thin => {}
            facts::BoxPointeeShape::Slice
            | facts::BoxPointeeShape::Str
            | facts::BoxPointeeShape::Dyn
            | facts::BoxPointeeShape::UnsizedTail
            | facts::BoxPointeeShape::InstanceDependent => {
                return Err(format!(
                    "pointee shape {:?} has no trust-ir spelling (wire v68 carries thin, sized \
                     pointees only)",
                    fact.pointee
                ));
            }
        }
        match fact.instance_scope {
            facts::BoxFactInstanceScope::ConcreteBody
            | facts::BoxFactInstanceScope::InstanceIndependent => {}
            facts::BoxFactInstanceScope::InstanceDependent => {
                return Err(
                    "the fact was judged on the polymorphic body only and this is an instance"
                        .to_owned(),
                );
            }
        }
        let mut evidence = Vec::with_capacity(fact.evidence.len());
        for (which, entry) in &fact.evidence {
            let premise = match entry {
                facts::BoxValidityEvidence::Premise(premise) => premise,
                facts::BoxValidityEvidence::ZeroSized => {
                    return Err(format!(
                        "conjunct {which:?} rests on zero-size evidence, which has no trust-ir \
                         spelling"
                    ));
                }
            };
            match premise.session {
                facts::BoxFactSession::UnoptimizedMir => {}
                facts::BoxFactSession::OptimizedMir => {
                    return Err(format!(
                        "conjunct {which:?} was judged outside the proof-session MIR pipeline"
                    ));
                }
            }
            evidence.push(ir::ConjunctEvidence {
                conjunct: conjunct(*which),
                evidence: ir::ValidityEvidence::Premise {
                    root: root(premise.root)?,
                    standing: premise.standing.assumptions().map(standing).collect(),
                },
            });
        }
        Ok(ir::BoxValidityFact {
            site,
            // Every premise above was judged in the proof-session pipeline,
            // on the body the verifier ran over (its last MIR pass).
            session: ir::BoxFactSession::PROOF_SNAPSHOT,
            evidence,
            not_claimed: ir::BoxValidityNonClaim::PINNED.to_vec(),
        })
    }

    /// Asks the compiler about every Box deref cast of `body`, the body about
    /// to be lowered for `instance`. `Ok` with an empty plan when it holds
    /// none; otherwise every cast is admitted by the compiler's fail-closed
    /// acceptance check and translated, or the body is refused.
    pub(crate) fn plan<'tcx>(
        tcx: TyCtxt<'tcx>,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
    ) -> Result<BoxDerefPlan, String> {
        let lowered = cast_bindings(body);
        if lowered.is_empty() {
            return Ok(BoxDerefPlan::default());
        }
        let ty::InstanceKind::Item(def_id) = instance.def else {
            return Err(refuse(format!(
                "no fact: the body is not an item body ({:?})",
                instance.def
            )));
        };
        let Some(table) = tcx.trust_box_deref_facts(def_id) else {
            return Err(refuse(format!(
                "no fact table for `{}` (carrier of its crate: {:?})",
                tcx.def_path_str(def_id),
                tcx.trust_box_deref_fact_carrier(def_id.krate).status
            )));
        };
        if !table.is_servable_for(tcx.def_path_hash(def_id)) {
            return Err(refuse(format!(
                "the fact table of `{}` is not servable for it",
                tcx.def_path_str(def_id)
            )));
        }
        // The judged body is the one `instance_mir` returns; `body` may be a
        // rewrite of it that dropped blocks, never one that gained a cast.
        let judged = cast_bindings(tcx.instance_mir(instance.def));
        if u32::try_from(judged.len()).ok() != Some(table.cast_count) {
            return Err(refuse(format!(
                "the body of `{}` holds {} Box deref cast(s) and its fact table was judged on {}",
                tcx.def_path_str(def_id),
                judged.len(),
                table.cast_count
            )));
        }
        check_rewritten_casts(&lowered, &judged).map_err(refuse)?;
        let mut plan = BoxDerefPlan::default();
        let mut seen: Vec<BoxDerefSite> = Vec::new();
        for (site, _) in &lowered {
            if seen.contains(site) {
                continue;
            }
            seen.push(*site);
            let fact = table
                .admit(*site, facts::BoxFactAdmission::FAIL_CLOSED)
                .map_err(|refusal| {
                    refuse(format!(
                        "site {site:?}: the compiler's fail-closed admission refused: \
                         {refusal:?} (body verdict {:?}, policy {:?})",
                        table.verdict, table.policy
                    ))
                })?;
            if u32::try_from(count(&judged, *site)).ok() != Some(fact.occurrences) {
                return Err(refuse(format!(
                    "site {site:?}: the judged body holds {} cast(s) of it and the fact was \
                     recorded for {}",
                    count(&judged, *site),
                    fact.occurrences
                )));
            }
            let translated = translate(fact, ir_site(tcx, *site))
                .map_err(|why| refuse(format!("site {site:?}: {why}")))?;
            plan.rows.push(PlanRow {
                fact: translated,
                expected: u32::try_from(count(&lowered, *site))
                    .map_err(|_| refuse("too many casts of one site"))?,
            });
        }
        Ok(plan)
    }

    impl BoxDerefPlan {
        /// The translated fact of the cast `kind`, which must be an admitted
        /// cast of the planned body. A cast from any other body (one a
        /// lowering route pulled in) has no row and is refused.
        pub(crate) fn fact_for(
            &self,
            tcx: TyCtxt<'_>,
            kind: &mir::CastKind,
        ) -> Result<ir::BoxValidityFact, String> {
            let mir::CastKind::BoxDerefTransmute(site) = kind else {
                return Err(refuse("not a Box deref cast"));
            };
            let wanted = ir_site(tcx, *site);
            self.rows
                .iter()
                .find(|row| row.fact.site == wanted)
                .map(|row| row.fact.clone())
                .ok_or_else(|| {
                    refuse(format!(
                        "site {site:?} is not an admitted cast of the body being lowered"
                    ))
                })
        }

        /// One line per admitted site, for the disclosure.
        pub(crate) fn admitted_lines(&self) -> Vec<String> {
            self.rows
                .iter()
                .map(|row| {
                    format!(
                        "site ordinal {} x{}: root {}, admitted by the compiler's fail-closed \
                         check",
                        row.fact.site.ordinal,
                        row.expected,
                        row.fact
                            .premise_root()
                            .map_or("<none>", ir::PremiseRoot::name),
                    )
                })
                .collect()
        }
    }

    #[cfg(test)]
    mod tests {
        use rustc_span::def_id::{CRATE_DEF_INDEX, DefId, LOCAL_CRATE};

        use super::*;

        const SITE: ir::BoxDerefSite = ir::BoxDerefSite {
            item: [7; 16],
            ordinal: 3,
        };

        fn premise(root: facts::BoxValidityRoot) -> facts::BoxValidityEvidence {
            facts::BoxValidityEvidence::Premise(facts::BoxValidityPremise {
                root,
                standing: facts::BoxStandingSet::ALL,
                session: facts::BoxFactSession::UnoptimizedMir,
            })
        }

        fn fact(root: facts::BoxValidityRoot) -> facts::BoxValidityFact {
            let evidence = premise(root);
            facts::BoxValidityFact {
                site: BoxDerefSite::new(
                    DefId {
                        krate: LOCAL_CRATE,
                        index: CRATE_DEF_INDEX,
                    },
                    3,
                ),
                evidence: vec![
                    (facts::BoxValidityConjunct::NonNull, evidence),
                    (facts::BoxValidityConjunct::Aligned, evidence),
                    (facts::BoxValidityConjunct::Dereferenceable, evidence),
                ],
                pointee: facts::BoxPointeeShape::Thin,
                instance_scope: facts::BoxFactInstanceScope::ConcreteBody,
                occurrences: 1,
                engine_credit: facts::BoxEngineCredit::NotCredited,
                callee: if root.rests_on_a_certified_call() {
                    facts::BoxRootCallee::OtherCrate
                } else {
                    facts::BoxRootCallee::NoCallee
                },
            }
        }

        /// Each root trust-ir names translates to the root of the same name,
        /// so the tier trust-ir derives is the root's own: the two assumed
        /// roots stay below `named_premise`.
        #[test]
        fn a_translated_fact_keeps_its_root_and_never_gains_a_tier() {
            for (root, name, tier) in [
                (
                    facts::BoxValidityRoot::ParamByValue,
                    "param_by_value",
                    ir::BoxValidityTier::NamedPremise,
                ),
                (
                    facts::BoxValidityRoot::AllocPostcondition,
                    "alloc_postcondition",
                    ir::BoxValidityTier::NamedPremise,
                ),
                (
                    facts::BoxValidityRoot::ReturnedBoxAssumed,
                    "returned_box_assumed",
                    ir::BoxValidityTier::AssumedRootPremise,
                ),
                (
                    facts::BoxValidityRoot::ReferenceArgBoxValid,
                    "reference_arg_box_valid",
                    ir::BoxValidityTier::AssumedRootPremise,
                ),
            ] {
                let translated = translate(&fact(root), SITE).expect("a root trust-ir names");
                assert_eq!(
                    translated,
                    ir::BoxValidityFact::premise(
                        SITE,
                        ir::BoxFactSession::PROOF_SNAPSHOT,
                        ir::PremiseRoot::from_name(name).unwrap()
                    ),
                    "{root:?}"
                );
                for entry in &translated.evidence {
                    assert_eq!(entry.evidence.tier(), tier, "{root:?}");
                }
            }
        }

        /// A root trust-ir does not name is refused, not mapped to a
        /// neighbour: the walk-only roots.
        #[test]
        fn a_root_without_a_trust_ir_spelling_is_refused() {
            for root in [
                facts::BoxValidityRoot::ReferenceReturnedAssumed,
                facts::BoxValidityRoot::LentSlotAssumed(facts::BoxLentSlotOrigin::ParamByValue),
                facts::BoxValidityRoot::LentSlotAssumed(
                    facts::BoxLentSlotOrigin::AllocPostcondition,
                ),
                facts::BoxValidityRoot::LentSlotAssumed(
                    facts::BoxLentSlotOrigin::ReturnedBoxAssumed,
                ),
            ] {
                let refused = translate(&fact(root), SITE);
                assert!(refused.is_err(), "{root:?}: {refused:?}");
            }
        }

        #[test]
        fn returned_box_discharged_is_refused_until_the_compiler_has_a_producer() {
            let error = translate(&fact(facts::BoxValidityRoot::ReturnedBoxDischarged), SITE)
                .expect_err("the format root alone is not producer authority");
            assert!(error.contains("representable in trust-ir"), "{error}");
            assert!(error.contains("no admitted producer"), "{error}");
            assert!(error.contains("until that producer exists"), "{error}");
        }

        #[test]
        fn rewritten_casts_are_a_multiset_subset_and_cannot_rebind_a_known_site() {
            let judged = [(7u32, "operand0->result0:ptr")];
            assert!(check_rewritten_casts(&judged, &judged).is_ok());
            assert!(check_rewritten_casts(&judged[..0], &judged).is_ok());

            let duplicate = [judged[0], judged[0]];
            let error = check_rewritten_casts(&duplicate, &judged)
                .expect_err("duplicating a known site must not duplicate its fact authority");
            assert!(error.contains("site multiset is not a subset"), "{error}");

            let rebound = [(7u32, "operand1->result0:ptr")];
            let error = check_rewritten_casts(&rebound, &judged)
                .expect_err("a known site cannot be rebound to a different cast");
            assert!(error.contains("is rebound"), "{error}");
        }

        /// Zero-size evidence, a wide or instance-dependent pointee, an
        /// instance-dependent verdict, another session and a malformed fact
        /// are each refused.
        #[test]
        fn evidence_and_shapes_without_a_trust_ir_spelling_are_refused() {
            let good = fact(facts::BoxValidityRoot::ParamByValue);
            assert!(translate(&good, SITE).is_ok());

            let mut zero_sized = good.clone();
            zero_sized.evidence[2].1 = facts::BoxValidityEvidence::ZeroSized;
            assert!(zero_sized.is_well_formed());
            assert!(
                translate(&zero_sized, SITE)
                    .unwrap_err()
                    .contains("zero-size")
            );

            for shape in [
                facts::BoxPointeeShape::Slice,
                facts::BoxPointeeShape::Str,
                facts::BoxPointeeShape::Dyn,
                facts::BoxPointeeShape::UnsizedTail,
                facts::BoxPointeeShape::InstanceDependent,
            ] {
                let mut wide = good.clone();
                wide.pointee = shape;
                if shape.is_wide() == Some(true) {
                    wide.evidence.push((
                        facts::BoxValidityConjunct::MetadataValid,
                        premise(facts::BoxValidityRoot::ParamByValue),
                    ));
                }
                // A wide shape is refused by this module's own shape match. An
                // instance-dependent shape never reaches it: the compiler's
                // well-formedness refuses a fact that does not know whether
                // its pointee is wide, and that check is the pinned gate.
                let error = translate(&wide, SITE).unwrap_err();
                let expected = if shape.is_wide() == Some(true) {
                    assert!(wide.is_well_formed(), "{shape:?}");
                    "has no trust-ir spelling"
                } else {
                    assert!(!wide.is_well_formed(), "{shape:?}");
                    "not well formed"
                };
                assert!(error.contains(expected), "{shape:?}: {error}");
            }

            let mut instance = good.clone();
            instance.instance_scope = facts::BoxFactInstanceScope::InstanceDependent;
            assert!(instance.is_well_formed());
            assert!(translate(&instance, SITE).unwrap_err().contains("instance"));

            let mut optimized = good.clone();
            for (_, evidence) in &mut optimized.evidence {
                *evidence = facts::BoxValidityEvidence::Premise(facts::BoxValidityPremise {
                    root: facts::BoxValidityRoot::ParamByValue,
                    standing: facts::BoxStandingSet::ALL,
                    session: facts::BoxFactSession::OptimizedMir,
                });
            }
            // The compiler's well-formedness already refuses a premise judged
            // on optimized MIR; that check is the pinned gate. The session
            // match in `translate` is a second refusal behind it, reachable
            // only if the compiler's rule is relaxed.
            assert!(!optimized.is_well_formed());
            assert!(
                translate(&optimized, SITE)
                    .unwrap_err()
                    .contains("well formed")
            );

            let mut malformed = good.clone();
            malformed.occurrences = 0;
            assert!(
                translate(&malformed, SITE)
                    .unwrap_err()
                    .contains("well formed")
            );
        }

        /// The conservation check: one instruction per planned cast with the
        /// planned fact, and nothing else.
        #[test]
        fn the_plan_refuses_a_module_that_dropped_or_invented_a_box_deref() {
            use trust_ir::{BlockId, FuncId, Function, Inst, InstrNode, Module, Ty, ValueId};
            let planned =
                translate(&fact(facts::BoxValidityRoot::ParamByValue), SITE).expect("translates");
            let plan = BoxDerefPlan {
                rows: vec![PlanRow {
                    fact: planned.clone(),
                    expected: 1,
                }],
            };
            let module_with = |facts: &[ir::BoxValidityFact]| {
                let mut module = Module::new("m");
                let mut func = Function::new(
                    FuncId::new(0),
                    "f",
                    trust_ir::FuncTyId::new(0),
                    BlockId::new(0),
                );
                let mut block = trust_ir::Block::new(BlockId::new(0));
                for (index, fact) in facts.iter().enumerate() {
                    block.body.push(
                        InstrNode::new(Inst::BoxDeref {
                            ptr_ty: Ty::Ptr,
                            pointee: ir::BoxPointee::Sized { ty: Ty::U64 },
                            operand: ValueId::new(0),
                            fact: Box::new(fact.clone()),
                        })
                        .with_result(ValueId::new(u32::try_from(index).unwrap() + 1)),
                    );
                }
                func.blocks.push(block);
                module.functions.push(func);
                module
            };
            assert!(plan.check_emitted(&module_with(&[planned.clone()])).is_ok());
            // Dropped: the cast was lowered some other way.
            assert!(plan.check_emitted(&module_with(&[])).is_err());
            // Duplicated.
            assert!(
                plan.check_emitted(&module_with(&[planned.clone(), planned.clone()]))
                    .is_err()
            );
            // Invented: a fact no planned cast has.
            let mut other = planned.clone();
            other.site.ordinal += 1;
            assert!(plan.check_emitted(&module_with(&[planned, other])).is_err());
            // An empty plan admits no instruction at all.
            let stray = translate(&fact(facts::BoxValidityRoot::ParamByValue), SITE).unwrap();
            assert!(
                BoxDerefPlan::default()
                    .check_emitted(&module_with(&[stray]))
                    .is_err()
            );
        }
    }
}

#[cfg(rustc_box_deref_facts)]
pub(crate) use carried::plan;
