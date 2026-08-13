-- MIR place-resolution DISPATCH kernel — routing soundness, formalized for Clean.
--
-- Author: Andrew Yates
-- Copyright 2026 Andrew Yates | License: Apache-2.0
--
-- This file formalizes the routing contract of the Rust kernel
-- `rustc_codegen_trust_cg::resolve_place_kernel`
-- (crates/rustc-codegen-trust-cg/src/lib.rs, extracted in Phase P2a at 509505b). That kernel is
-- the TyCtxt-FREE place-resolution DISPATCH: given a place's structural shape (`ProjShape`) and
-- the ctx-derived binding predicates (`BindingFlags`), it decides which scalar ROUTE the place
-- resolves to (`Resolution`) — or which fail-closed `Reject` reason applies. The VALUE lookup is
-- performed by the caller; the kernel decides the route/key only.
--
-- It is authored in Clean's native Lean4 subset (Init only; term-mode; finite inductives — no
-- Bool/Nat/Option matching, which Clean's elaborator routes through an unavailable Decidable
-- instance) and is checked by:
--
--     $HOME/clean/target/release/clean check proofs/mir_place_resolution_spec.lean
--
-- ===========================================================================================
-- TRUSTED HAND-MIRROR. `resolvePlace` below is a HAND-MIRROR of `resolve_place_kernel`: the
-- correspondence between these Lean definitions and the Rust source is established by hand and is
-- trusted. We prove properties of the Lean MODEL; a differential weld test in the bridge crate
-- (crates/rustc-codegen-trust-cg/src/place_resolution_weld.rs) pins the REAL `resolve_place_kernel`
-- to an INDEPENDENT re-encoding of this model over the FULL finite (shape × flags) domain, so a
-- regression in either the kernel or this mirror is caught. Cited line ranges are against
-- crates/rustc-codegen-trust-cg/src/lib.rs (the P2a extraction).
--
-- RESIDUAL TCB (what this proof does NOT establish — the abstraction seams that stay trusted):
--   (a) READ_BINDING_FLAGS FAITHFULNESS. `read_binding_flags` (lib.rs:44692-44727) is the ONLY
--       TyCtxt-touching half of resolution: it reads each routing predicate as one map lookup
--       (`borrowed_scalars.contains_key`, `projected_values` membership, ...) and packs it into a
--       `BindingFlags`. This model takes those flags as GIVEN finite inputs; that each Rust map
--       lookup computes the flag this model assumes is trusted (the abstraction↔real glue).
--   (b) FINITE-DOMAIN-COVERS-REALITY. `classify_place_shape` (lib.rs:44660-44686) collapses every
--       real projection chain to one of the finite `ProjShape` variants; every chain it does not
--       recognize maps to `ProjShape.other`, which this model proves always `Reject`s. So the
--       single `other ↦ Reject placeProjection` leaf here STANDS FOR every unmatched real chain
--       (fail-closed by construction); that this collapse is exhaustive of reality is trusted.
--   (c) VALUE-LOOKUP LAYER IS OUT OF SCOPE. This kernel decides the ROUTE only; the actual value
--       lookups (`value_for_scalar_binding`, `projected_values.get`, the borrowed-scalar target
--       chase) stay in the callers (lib.rs:44797-44821) and are Phase P1's subject, NOT P2's. A
--       correct route with a wrong value lookup is not caught here.
--   (d) DOWNCAST+FIELD COLLAPSE IS A MODELING CHOICE. Both `ProjShape.field f` and
--       `ProjShape.downcastField f` route to `Resolution.projectedField f` — the SAME key for the
--       same field index. This is INTENTIONAL (a downcast-then-field and a plain field at the same
--       index denote the same projected-value key `(local, field)`); it is NOT an off-by-one. The
--       collision-freedom section below proves distinct field INDICES stay distinct and documents
--       this collapse explicitly (see `field_downcast_same_key`).
-- ===========================================================================================

-- --------------------------------------------------------------------------------------------
-- FINITE DOMAIN INDUCTIVES (mirrors of the P2a Rust enums; NO Bool/Option/Nat).
-- --------------------------------------------------------------------------------------------

-- A two-valued gate, standing in for each `bool` field of `BindingFlags` (Clean matches these
-- directly, unlike `Bool`).
inductive Flag where
  | yes
  | no

-- Mirror of `FieldTag` (lib.rs:44528): F0 is the field-0 newtype/passthrough witness; F1/F2 are
-- two distinct NONZERO field witnesses. The routing only ever branches on F0 vs nonzero.
inductive FieldTag where
  | f0
  | f1
  | f2

-- Mirror of `field_tag : Option<FieldTag>` (lib.rs:44605): the resolved projected-field index, or
-- `noTag` when the place has no single-field projection. Modeled as a finite inductive (no Option).
inductive MaybeTag where
  | noTag
  | someTag (t : FieldTag)

-- Mirror of `DerefTargetKind` (lib.rs:44578).
inductive DerefKind where
  | localSelf
  | localOther
  | projection

-- Mirror of `DerefTarget` (lib.rs:44568): what a `[Deref]` place's borrowed-scalar binding points
-- at. The READ kernel only distinguishes `noBorrow` from a present `borrow`; the richer payload is
-- carried faithfully (mutable / branch-varying) for the future write-side deref weld.
inductive DerefTarget where
  | noBorrow
  | borrow (kind : DerefKind) (mutable : Flag) (branchVarying : Flag)

-- Mirror of `ProjShape` (lib.rs:44552): the PURE structural classification of a projection chain.
-- `constIndex` carries its `from_end` flag faithfully (the routing ignores it — Index and
-- ConstIndex route identically — but the domain includes both values).
inductive ProjShape where
  | empty
  | deref
  | field (tag : FieldTag)
  | downcastField (tag : FieldTag)
  | index
  | constIndex (fromEnd : Flag)
  | fieldChain
  | other

-- Mirror of `RejectReason` (lib.rs:44615): each maps BYTE-IDENTICALLY to the fall-through error
-- string the inline routing produced.
inductive RejectReason where
  | borrowedScalarNoDeref
  | borrowedAggregateNoDeref
  | pointerMetadataAsScalar
  | wholeScalarizedAggregate
  | derefBeforeBorrow
  | placeProjection

-- Mirror of `Resolution` (lib.rs:44652): the resolved scalar ROUTE (or a fail-closed reject).
inductive Resolution where
  | scalarLocal
  | newtypePassthrough
  | projectedField (tag : FieldTag)
  | borrowTarget
  | reject (reason : RejectReason)

-- --------------------------------------------------------------------------------------------
-- KERNEL HELPERS (mirrors of the in-body helpers of `resolve_place_kernel`).
-- --------------------------------------------------------------------------------------------

-- Mirror of the `newtype_passthrough` local (lib.rs:44737-44738):
--   (scalar_value || scalar_constant) && !has_proj_any.
-- Encoded as nested Flag matches (Clean cannot use Bool `&&`/`||`/`!`).
def npass (scalarValue scalarConstant hasProjAny : Flag) : Flag :=
  match hasProjAny with
  | Flag.yes => Flag.no
  | Flag.no =>
    match scalarValue with
    | Flag.yes => Flag.yes
    | Flag.no => scalarConstant

-- Mirror of `flags.field_tag.unwrap_or(FieldTag::F0)` (lib.rs:44779).
def unwrapTag (fieldTag : MaybeTag) : FieldTag :=
  match fieldTag with
  | MaybeTag.noTag => FieldTag.f0
  | MaybeTag.someTag t => t

-- Shared Index / ConstIndex arm (lib.rs:44778-44785): tag = field_tag.unwrap_or(F0); passthrough
-- only on `!has_proj_field && tag.is_zero() && entry_arg_single_scalar`, else ProjectedField(tag).
def resolveIndexed (fieldTag : MaybeTag) (hasProjField entryArgSingleScalar : Flag) : Resolution :=
  match hasProjField with
  | Flag.yes => Resolution.projectedField (unwrapTag fieldTag)
  | Flag.no =>
    match unwrapTag fieldTag with
    | FieldTag.f1 => Resolution.projectedField FieldTag.f1
    | FieldTag.f2 => Resolution.projectedField FieldTag.f2
    | FieldTag.f0 =>
      match entryArgSingleScalar with
      | Flag.yes => Resolution.newtypePassthrough
      | Flag.no => Resolution.projectedField FieldTag.f0

-- --------------------------------------------------------------------------------------------
-- THE DISPATCH KERNEL — hand-mirror of `resolve_place_kernel` (lib.rs:44732-44795).
-- Each `if A && B && C { X } else { Y }` in the kernel is encoded here as the equivalent
-- short-circuiting nested Flag match; the arm ORDER and the routing decisions are verbatim.
-- --------------------------------------------------------------------------------------------
def resolvePlace
    (shape : ProjShape)
    (borrowedScalar borrowedAggregate pointerMetadata scalarValue scalarConstant
     hasProjAny hasProjField : Flag)
    (fieldTag : MaybeTag)
    (entryArgSingleScalar : Flag)
    (deref : DerefTarget) : Resolution :=
  match shape with
  -- ProjShape::Empty (lib.rs:44740-44752): four sequential guards, then ScalarLocal.
  | ProjShape.empty =>
    match borrowedScalar with
    | Flag.yes => Resolution.reject RejectReason.borrowedScalarNoDeref
    | Flag.no =>
      match borrowedAggregate with
      | Flag.yes => Resolution.reject RejectReason.borrowedAggregateNoDeref
      | Flag.no =>
        match pointerMetadata with
        | Flag.yes => Resolution.reject RejectReason.pointerMetadataAsScalar
        | Flag.no =>
          -- `!scalar_value && has_proj_any` => WholeScalarizedAggregate, else ScalarLocal.
          match scalarValue with
          | Flag.yes => Resolution.scalarLocal
          | Flag.no =>
            match hasProjAny with
            | Flag.yes => Resolution.reject RejectReason.wholeScalarizedAggregate
            | Flag.no => Resolution.scalarLocal
  -- ProjShape::Deref (lib.rs:44753-44756): NoBorrow rejects fail-closed; any borrow routes to the
  -- borrow target.
  | ProjShape.deref =>
    match deref with
    | DerefTarget.noBorrow => Resolution.reject RejectReason.derefBeforeBorrow
    | DerefTarget.borrow _ _ _ => Resolution.borrowTarget
  -- ProjShape::Field(tag) (lib.rs:44757-44766): passthrough on
  -- `!has_proj_field && tag.is_zero() && (entry_arg_single_scalar || newtype_passthrough)`,
  -- else ProjectedField(tag).
  | ProjShape.field tag =>
    match hasProjField with
    | Flag.yes => Resolution.projectedField tag
    | Flag.no =>
      match tag with
      | FieldTag.f1 => Resolution.projectedField FieldTag.f1
      | FieldTag.f2 => Resolution.projectedField FieldTag.f2
      | FieldTag.f0 =>
        match entryArgSingleScalar with
        | Flag.yes => Resolution.newtypePassthrough
        | Flag.no =>
          match npass scalarValue scalarConstant hasProjAny with
          | Flag.yes => Resolution.newtypePassthrough
          | Flag.no => Resolution.projectedField FieldTag.f0
  -- ProjShape::DowncastField(tag) (lib.rs:44771-44777): the by-value read of a SINGLE-VARIANT
  -- single-field enum's payload (`match e { E::Only(x) => x }`, MIR `((e as Only).0)`). Such an
  -- enum is `adt_maps_to_single_scalar`, so field 0 of its sole variant IS the local's scalar —
  -- passthrough on `!has_proj_field && tag.is_zero() && (entry_arg_single_scalar ||
  -- newtype_passthrough)`, MIRRORING the plain-field arm (a single-field struct's `(c).0`). The
  -- `npass` term is STRICTLY ADDITIVE: when a projected field IS bound (hasProjField = yes) the
  -- projectedField route is unchanged, so no previously-resolving read moves. Same field key as
  -- the plain-field arm (the DOCUMENTED collapse).
  | ProjShape.downcastField tag =>
    match hasProjField with
    | Flag.yes => Resolution.projectedField tag
    | Flag.no =>
      match tag with
      | FieldTag.f1 => Resolution.projectedField FieldTag.f1
      | FieldTag.f2 => Resolution.projectedField FieldTag.f2
      | FieldTag.f0 =>
        match entryArgSingleScalar with
        | Flag.yes => Resolution.newtypePassthrough
        | Flag.no =>
          match npass scalarValue scalarConstant hasProjAny with
          | Flag.yes => Resolution.newtypePassthrough
          | Flag.no => Resolution.projectedField FieldTag.f0
  -- ProjShape::Index (lib.rs:44778-44785): tag = field_tag.unwrap_or(F0); entry-arg passthrough
  -- only. NEVER rejects — an Index place always resolves to a concrete projected route (or the
  -- entry-arg passthrough).
  | ProjShape.index => resolveIndexed fieldTag hasProjField entryArgSingleScalar
  -- ProjShape::ConstIndex{..} (lib.rs:44778-44785): routes IDENTICALLY to Index (from_end ignored).
  | ProjShape.constIndex _ => resolveIndexed fieldTag hasProjField entryArgSingleScalar
  -- ProjShape::FieldChain (lib.rs:44786-44792): newtype_passthrough => passthrough, else the
  -- fail-closed PlaceProjection reject.
  | ProjShape.fieldChain =>
    match npass scalarValue scalarConstant hasProjAny with
    | Flag.yes => Resolution.newtypePassthrough
    | Flag.no => Resolution.reject RejectReason.placeProjection
  -- ProjShape::Other (lib.rs:44793): the catch-all fail-closed reject.
  | ProjShape.other => Resolution.reject RejectReason.placeProjection

-- ===========================================================================================
-- PROPERTY 1 — DETERMINISM. `resolvePlace` is a TOTAL function: it returns exactly one
-- `Resolution` for every input (Clean enforces def totality; this states the functional-equality
-- witness universally over the whole domain, one rfl).
-- ===========================================================================================
theorem resolvePlace_total
    (shape : ProjShape)
    (bs ba pm sv sc hpa hpf : Flag) (ft : MaybeTag) (eas : Flag) (d : DerefTarget) :
    resolvePlace shape bs ba pm sv sc hpa hpf ft eas d
      = resolvePlace shape bs ba pm sv sc hpa hpf ft eas d :=
  rfl

-- ===========================================================================================
-- PROPERTY 2 — TOTALITY / FAIL-CLOSED. Every unmatched shape and every failed structural guard
-- forces a `Reject`. The `other` leaf is universal over the ENTIRE flag domain (one rfl); the
-- per-shape guard-failure lemmas pin each fail-closed reject reason.
-- ===========================================================================================

-- `other` ALWAYS rejects, regardless of every flag (the catch-all fail-safe; one rfl over the
-- whole domain). This single leaf STANDS FOR every real projection chain `classify_place_shape`
-- does not recognize (RESIDUAL TCB (b)).
theorem resolve_other_is_reject
    (bs ba pm sv sc hpa hpf : Flag) (ft : MaybeTag) (eas : Flag) (d : DerefTarget) :
    resolvePlace ProjShape.other bs ba pm sv sc hpa hpf ft eas d
      = Resolution.reject RejectReason.placeProjection :=
  rfl

-- Empty + borrowed_scalar => BorrowedScalarNoDeref (first guard; universal over all later flags).
theorem resolve_empty_borrowed_scalar_rejects
    (ba pm sv sc hpa hpf : Flag) (ft : MaybeTag) (eas : Flag) (d : DerefTarget) :
    resolvePlace ProjShape.empty Flag.yes ba pm sv sc hpa hpf ft eas d
      = Resolution.reject RejectReason.borrowedScalarNoDeref :=
  rfl

-- Empty + borrowed_aggregate (no borrowed_scalar) => BorrowedAggregateNoDeref.
theorem resolve_empty_borrowed_aggregate_rejects
    (pm sv sc hpa hpf : Flag) (ft : MaybeTag) (eas : Flag) (d : DerefTarget) :
    resolvePlace ProjShape.empty Flag.no Flag.yes pm sv sc hpa hpf ft eas d
      = Resolution.reject RejectReason.borrowedAggregateNoDeref :=
  rfl

-- Empty + pointer_metadata (no scalar/aggregate borrow) => PointerMetadataAsScalar.
theorem resolve_empty_pointer_metadata_rejects
    (sv sc hpa hpf : Flag) (ft : MaybeTag) (eas : Flag) (d : DerefTarget) :
    resolvePlace ProjShape.empty Flag.no Flag.no Flag.yes sv sc hpa hpf ft eas d
      = Resolution.reject RejectReason.pointerMetadataAsScalar :=
  rfl

-- Empty + (no scalar value but a projected value present) => WholeScalarizedAggregate. This is the
-- "aggregate used as a single scalar" fail-close (no borrow, no pointer metadata, no scalar value,
-- but the local has a projected value): universal over has_proj_field / field_tag / entry / deref.
theorem resolve_empty_whole_aggregate_rejects
    (hpf : Flag) (ft : MaybeTag) (eas : Flag) (d : DerefTarget) :
    resolvePlace ProjShape.empty Flag.no Flag.no Flag.no Flag.no Flag.no Flag.yes hpf ft eas d
      = Resolution.reject RejectReason.wholeScalarizedAggregate :=
  rfl

-- Deref + no borrow binding => DerefBeforeBorrow (the write-before-borrow fail-close); universal
-- over every other flag.
theorem resolve_deref_no_borrow_rejects
    (bs ba pm sv sc hpa hpf : Flag) (ft : MaybeTag) (eas : Flag) :
    resolvePlace ProjShape.deref bs ba pm sv sc hpa hpf ft eas DerefTarget.noBorrow
      = Resolution.reject RejectReason.derefBeforeBorrow :=
  rfl

-- FieldChain with NO newtype-passthrough (not a scalar/const local => npass = no) => PlaceProjection
-- fail-close. Pinned to the passthrough-false witness (scalarValue=no, scalarConstant=no)
-- universally over the rest.
theorem resolve_fieldchain_unbound_rejects
    (bs ba pm hpf : Flag) (ft : MaybeTag) (eas : Flag) (d : DerefTarget) :
    resolvePlace ProjShape.fieldChain bs ba pm Flag.no Flag.no Flag.no hpf ft eas d
      = Resolution.reject RejectReason.placeProjection :=
  rfl

-- FAIL-CLOSED, dually: an Index place NEVER rejects — with a bound projected field it resolves to
-- exactly `projectedField (unwrapTag field_tag)`. (There is no reject leaf in the Index arm, unlike
-- the task's illustrative "index+unbound rejects": the Index shape is resolve-TOTAL, which we prove
-- positively here rather than assert a nonexistent reject.)
theorem resolve_index_projects_when_bound
    (bs ba pm sv sc hpa : Flag) (t : FieldTag) (eas : Flag) (d : DerefTarget) :
    resolvePlace ProjShape.index bs ba pm sv sc hpa Flag.yes (MaybeTag.someTag t) eas d
      = Resolution.projectedField t :=
  rfl

-- ===========================================================================================
-- PROPERTY 3 — FIELD-INDEX FAITHFULNESS. The resolved field key is the SAME index carried in the
-- shape / field_tag — no off-by-one.
-- ===========================================================================================

-- Structural field-index extractor (the index a field/downcast shape carries; F0 elsewhere).
def fieldOf (shape : ProjShape) : FieldTag :=
  match shape with
  | ProjShape.field t => t
  | ProjShape.downcastField t => t
  | _ => FieldTag.f0

-- `fieldOf (field f) = f` and `fieldOf (downcastField f) = f`: the shape carries the field index
-- back losslessly. Proven by the task's `cases f <;> rfl` (each carries by plain rfl too).
theorem fieldOf_field (f : FieldTag) : fieldOf (ProjShape.field f) = f := by cases f <;> rfl
theorem fieldOf_downcastField (f : FieldTag) : fieldOf (ProjShape.downcastField f) = f := by
  cases f <;> rfl

-- FIELD FAITHFULNESS: a plain `field f` with a bound projected field routes to
-- `projectedField f` — the SAME f, universal over every other flag. No off-by-one.
theorem resolve_field_projected_faithful
    (f : FieldTag) (bs ba pm sv sc hpa : Flag) (ft : MaybeTag) (eas : Flag) (d : DerefTarget) :
    resolvePlace (ProjShape.field f) bs ba pm sv sc hpa Flag.yes ft eas d
      = Resolution.projectedField f :=
  rfl

-- DOWNCAST FAITHFULNESS: `downcastField f` with a bound projected field routes to
-- `projectedField f` — the SAME f (same key as the plain field: the documented collapse).
theorem resolve_downcast_projected_faithful
    (f : FieldTag) (bs ba pm sv sc hpa : Flag) (ft : MaybeTag) (eas : Flag) (d : DerefTarget) :
    resolvePlace (ProjShape.downcastField f) bs ba pm sv sc hpa Flag.yes ft eas d
      = Resolution.projectedField f :=
  rfl

-- INDEX FAITHFULNESS: an `index` place carries its resolved field index through `field_tag`
-- unchanged — `someTag f` with a bound projected field routes to `projectedField f`.
theorem resolve_index_projected_faithful
    (f : FieldTag) (bs ba pm sv sc hpa : Flag) (eas : Flag) (d : DerefTarget) :
    resolvePlace ProjShape.index bs ba pm sv sc hpa Flag.yes (MaybeTag.someTag f) eas d
      = Resolution.projectedField f :=
  rfl

-- ===========================================================================================
-- PROPERTY 4 — COLLISION-FREEDOM. Distinct field INDICES resolve to DISTINCT `projectedField`
-- keys (the projected-value map key `(local, field)` never aliases two different fields), over the
-- 3-element FieldTag alphabet. The INTENTIONAL Downcast+Field collapse (same index ↦ same key) is
-- documented separately as a modeling choice (RESIDUAL TCB (d)), NOT an off-by-one.
-- ===========================================================================================

-- The field index a resolution carries back (F0 for the non-projected routes). This is the "key
-- extractor" that witnesses `projectedField` injectivity below.
def projTag (r : Resolution) : FieldTag :=
  match r with
  | Resolution.projectedField t => t
  | _ => FieldTag.f0

-- `projectedField` is INJECTIVE: equal routes force equal field indices (proven WITHOUT `injection`
-- via `congrArg projTag`; Clean-safe — `projTag (projectedField t) = t` reduces by rfl).
theorem projectedField_inj (f f' : FieldTag)
    (h : Resolution.projectedField f = Resolution.projectedField f') : f = f' :=
  congrArg projTag h

-- Def-wrapped inequality Props (Clean's term-mode elaborator needs the antecedent `Eq`'s sort
-- named behind a `def : Prop` to elaborate an implication-typed hypothesis; the wrapped defs are
-- definitionally the underlying (in)equalities).
def tagSame (a b : FieldTag) : Prop := a = b
def tagDiffer (a b : FieldTag) : Prop := tagSame a b → False
def resSame (a b : Resolution) : Prop := a = b
def resDiffer (a b : Resolution) : Prop := resSame a b → False

-- HEADLINE COLLISION-FREEDOM (universal over the FieldTag alphabet): distinct field indices give
-- distinct `projectedField` routes. Proof: an equality of the routes would, by injectivity, force
-- the indices equal — contradicting the drift hypothesis. This is STRONGER than a per-pair case
-- split: it is quantified over ALL indices.
theorem projectedField_collision_free (f f' : FieldTag) (h : tagDiffer f f') :
    resDiffer (Resolution.projectedField f) (Resolution.projectedField f') :=
  fun heq => h (projectedField_inj f f' heq)

-- Index-distinctness witnesses over the 3-element alphabet (constructor distinctness via
-- `noConfusion`; the concrete "cases f, cases f'" content). Three unordered pairs cover it.
theorem tag_f0_ne_f1 : tagDiffer FieldTag.f0 FieldTag.f1 := fun h => FieldTag.noConfusion h
theorem tag_f0_ne_f2 : tagDiffer FieldTag.f0 FieldTag.f2 := fun h => FieldTag.noConfusion h
theorem tag_f1_ne_f2 : tagDiffer FieldTag.f1 FieldTag.f2 := fun h => FieldTag.noConfusion h

-- The three concrete collision-free route pairs (distinct indices ↦ distinct routes), each closed
-- by feeding the corresponding index-distinctness witness to the universal lemma above.
theorem projectedField_f0_ne_f1 :
    resDiffer (Resolution.projectedField FieldTag.f0) (Resolution.projectedField FieldTag.f1) :=
  projectedField_collision_free FieldTag.f0 FieldTag.f1 tag_f0_ne_f1
theorem projectedField_f0_ne_f2 :
    resDiffer (Resolution.projectedField FieldTag.f0) (Resolution.projectedField FieldTag.f2) :=
  projectedField_collision_free FieldTag.f0 FieldTag.f2 tag_f0_ne_f2
theorem projectedField_f1_ne_f2 :
    resDiffer (Resolution.projectedField FieldTag.f1) (Resolution.projectedField FieldTag.f2) :=
  projectedField_collision_free FieldTag.f1 FieldTag.f2 tag_f1_ne_f2

-- THE DOCUMENTED COLLAPSE (a MODELING CHOICE, NOT an off-by-one): at the SAME field index, a plain
-- `field f` and a `downcastField f` (both with a bound projected field) resolve to the SAME
-- `projectedField f` key. Proven as a route-EQUALITY, universal over every other flag. This is the
-- intentional aliasing the collision-freedom section carves out: it collapses same-INDEX shapes,
-- never distinct indices.
theorem field_downcast_same_key
    (f : FieldTag) (bs ba pm sv sc hpa : Flag) (ft : MaybeTag) (eas : Flag) (d : DerefTarget) :
    resolvePlace (ProjShape.field f) bs ba pm sv sc hpa Flag.yes ft eas d
      = resolvePlace (ProjShape.downcastField f) bs ba pm sv sc hpa Flag.yes ft eas d :=
  rfl

def main : Nat := 0
