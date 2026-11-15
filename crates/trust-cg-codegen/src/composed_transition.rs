// trust-cg-codegen/composed_transition.rs - pipeline wiring of the composed transition record
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Pipeline wiring of the composed transition record
//! ([`trust_cg_verify::composed_transition`], ledger L09-P3).
//!
//! A [`Session`] follows one function through
//! `Pipeline::prepare_function_*` and records one link per checked
//! transition:
//!
//! 1. **legalization** (TrustIR → LIR) and **selection** (LIR → raw MachIR),
//!    both from the one affine check
//!    ([`trust_cg_verify::aarch64_affine_lowering::check_aarch64_trust_ir_affine_lowering`])
//!    run on the raw selection, before any pass;
//! 2. one **pass run** per optimizer, CEGIS or scheduler run that changed
//!    the function's interface, from the optimizer's transitions
//!    (`trust_cg_opt::pass_validation`), each mapped by [`pass_run_link`]:
//!    every pass-manager and scheduler run is validated for the record by
//!    its dedicated validator or the generic region check; CEGIS and the
//!    extended loop rotation have no validator, so such a run is uncovered;
//!    an uncovered, refuted (including silent) or unproved run becomes a
//!    link that is not established;
//! 3. the **post-allocation** comparison
//!    ([`trust_cg_verify::post_ra_value_flow`]) of the function entering
//!    register allocation with the final resolved stream (two links when
//!    the comparison is split);
//! 4. **encoding**: the final function encoded under the proof-grade policy
//!    (ENC-5 enforced with undecoded words refused, the CFG-bound
//!    final-layout cross-check, the switch binding), relocation-free.
//!
//! The record lands in `PreparationMetrics::composed_transition`. Routes
//! that require compositions ([`ComposedTransitionPolicy::Require`]: the
//! sealed Core, the verifying JIT and `--emit-proofs` objects) then refuse
//! a function a TrustIR-bound legalization check covers unless its record
//! composes at [`EvidenceStrength::ExactlyDecided`] or stronger
//! ([`require_composition`], which the JIT and object routes apply right
//! after preparation, before any certificate is generated or promoted) and
//! the bytes they publish for it are exactly the chain's terminal
//! ([`require_published`] for the sealed code, the JIT's installed range,
//! [`require_object_publication`] for the object's symbol extent). A function the
//! legalization check does not cover (no TrustIR source, or a source outside
//! its affine domain) keeps a record that says so and is published on the
//! route's other gates alone: no TrustIR-to-bytes claim is made for it.

use trust_cg_ir::MachFunction;
use trust_cg_opt::{FunctionInterfaceDigest, PassTransition, ValidationVerdict};
use trust_cg_verify::composed_transition::{
    self as ct, ComposedTransition, CompositionRefusal, EvidenceStrength, Interface, LinkStage,
    LinkVerdict, TransitionLink, TransitionRecord, relations as rel,
};

/// What a pipeline does with composed transition records.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum ComposedTransitionPolicy {
    /// No record.
    #[default]
    Off,
    /// Build a record for every prepared function; never refuse.
    /// Measurement and diagnostics (`TRUST_CG_COMPOSED_TRANSITION=record`).
    Record,
    /// Build a record for every prepared function; the routes that publish
    /// proof-grade code refuse a function a TrustIR-bound legalization check
    /// covers unless its record composes and reaches the published bytes.
    /// Proof-grade publication and the sealed Core select it; it cannot be
    /// lowered there.
    Require,
}

impl ComposedTransitionPolicy {
    /// Stable spelling.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::Record => "record",
            Self::Require => "require",
        }
    }

    /// Parse [`Self::as_str`]'s spelling.
    pub fn parse(text: &str) -> Option<Self> {
        match text.trim() {
            "off" => Some(Self::Off),
            "record" => Some(Self::Record),
            "require" => Some(Self::Require),
            _ => None,
        }
    }

    /// The stronger of two policies.
    pub fn strongest(self, other: Self) -> Self {
        fn rank(policy: ComposedTransitionPolicy) -> u8 {
            match policy {
                ComposedTransitionPolicy::Off => 0,
                ComposedTransitionPolicy::Record => 1,
                ComposedTransitionPolicy::Require => 2,
            }
        }
        if rank(other) > rank(self) {
            other
        } else {
            self
        }
    }

    /// The policy `TRUST_CG_COMPOSED_TRANSITION` asks for, if any.
    pub(crate) fn from_environment() -> Option<Self> {
        crate::env_lock::var("TRUST_CG_COMPOSED_TRANSITION")
            .ok()
            .and_then(|text| Self::parse(&text))
    }
}

/// How the legalization stage's affine check ended.
pub(crate) enum Legalization<'a> {
    /// The module-owned TrustIR function at `ordinal` was checked against
    /// the LIR and the raw selection.
    Checked {
        module: &'a trust_ir::Module,
        ordinal: usize,
    },
    /// No TrustIR-bound legalization check covers the function.
    NotCovered(String),
    /// The check covers the source and refused the lowering.
    Rejected {
        module: &'a trust_ir::Module,
        ordinal: usize,
        reason: String,
    },
}

/// One function's record in progress.
pub(crate) struct Session {
    policy: ComposedTransitionPolicy,
    record: Option<TransitionRecord>,
    /// Interface of the function entering register allocation.
    pre_allocation: Option<Interface>,
}

fn established() -> LinkVerdict {
    LinkVerdict::Established
}

/// The pass-run link of one optimizer, CEGIS or scheduler run that changed
/// the function's interface: established only when the run's validator
/// validated it. An uncovered run (no validator: CEGIS, the extended loop
/// rotation, any step outside a validated pass manager), a refuted run
/// (including a run that reported no change but altered the interface) and
/// an unproved one each become a link that is not established, carrying the
/// validator's own outcome and reason, so the chain refuses by the run's
/// name. The pipeline maps every recorded transition through this function.
pub fn pass_run_link(transition: PassTransition) -> TransitionLink {
    let verdict = match &transition.verdict {
        ValidationVerdict::Validated => established(),
        ValidationVerdict::Uncovered => {
            not_established("uncovered", "no validator covers this run")
        }
        other => not_established(other.as_str(), other.reason().unwrap_or_default()),
    };
    TransitionLink {
        stage: LinkStage::PassRun,
        name: transition.pass_name,
        relation: rel::PASS_RUN_RELATION.to_string(),
        check: transition
            .validator
            .map_or("none", |validator| validator.as_str())
            .to_string(),
        model: rel::PASS_RUN_MODEL.to_string(),
        from: Interface {
            representation: ct::Representation::MachIr,
            digest: transition.before,
        },
        to: Interface {
            representation: ct::Representation::MachIr,
            digest: transition.after,
        },
        to_len: None,
        strength: EvidenceStrength::ExactlyDecided,
        verdict,
    }
}

fn not_established(outcome: &str, reason: impl Into<String>) -> LinkVerdict {
    LinkVerdict::NotEstablished {
        outcome: outcome.to_string(),
        reason: reason.into(),
    }
}

impl Session {
    /// Start `function`'s record under `policy`.
    pub(crate) fn begin(policy: ComposedTransitionPolicy, function: &str) -> Self {
        Self {
            policy,
            record: (policy != ComposedTransitionPolicy::Off)
                .then(|| TransitionRecord::new(function)),
            pre_allocation: None,
        }
    }

    /// The policy this session runs under.
    pub(crate) fn policy(&self) -> ComposedTransitionPolicy {
        self.policy
    }

    /// Whether the chain is still being extended: a record exists, it is
    /// in the legalization domain and every link so far was established.
    /// Only then do the later stages pay for their links.
    pub(crate) fn recording(&self) -> bool {
        self.record
            .as_ref()
            .is_some_and(|record| record.is_open() && !record.links.is_empty())
    }

    /// The interface digest the optimizer records transitions with, while
    /// recording.
    pub(crate) fn transition_digest(&self) -> Option<FunctionInterfaceDigest> {
        self.recording()
            .then_some(ct::mach_function_interface_digest as FunctionInterfaceDigest)
    }

    fn record_mut(&mut self) -> Option<&mut TransitionRecord> {
        self.record.as_mut()
    }

    /// Record the legalization stage's outcome for `lir` and its raw
    /// selection `raw`.
    pub(crate) fn legalization(
        &mut self,
        outcome: Legalization<'_>,
        lir: &trust_cg_lower::Function,
        raw: &MachFunction,
    ) {
        let Some(record) = self.record_mut() else {
            return;
        };
        let (module, ordinal, verdict) = match outcome {
            Legalization::NotCovered(reason) => {
                record.mark_not_composed(LinkStage::Legalization, reason);
                return;
            }
            Legalization::Checked { module, ordinal } => (module, ordinal, None),
            Legalization::Rejected {
                module,
                ordinal,
                reason,
            } => (module, ordinal, Some(reason)),
        };
        let lir_interface = ct::lir_function_interface(lir);
        let Some(origin) = ct::trust_ir_function_interface(module, ordinal) else {
            // The check ran on (or refused) this source, so the function is
            // in the domain: a missing source interface refuses the chain
            // instead of taking the function out of the requirement.
            record.push(TransitionLink {
                stage: LinkStage::Legalization,
                name: rel::LEGALIZATION_NAME.to_string(),
                relation: rel::LEGALIZATION_RELATION.to_string(),
                check: rel::AFFINE_CHECK.to_string(),
                model: rel::LEGALIZATION_MODEL.to_string(),
                from: Interface {
                    representation: ct::Representation::TrustIr,
                    digest: [0; 32],
                },
                to: lir_interface,
                to_len: None,
                strength: EvidenceStrength::ExactlyDecided,
                verdict: not_established(
                    "no-source-interface",
                    format!(
                        "module function ordinal {ordinal} has no TrustIR interface (outside the \
                         module, or its signature is not the module's)"
                    ),
                ),
            });
            return;
        };
        let legalization = |verdict| TransitionLink {
            stage: LinkStage::Legalization,
            name: rel::LEGALIZATION_NAME.to_string(),
            relation: rel::LEGALIZATION_RELATION.to_string(),
            check: rel::AFFINE_CHECK.to_string(),
            model: rel::LEGALIZATION_MODEL.to_string(),
            from: origin,
            to: lir_interface,
            to_len: None,
            strength: EvidenceStrength::ExactlyDecided,
            verdict,
        };
        if let Some(reason) = verdict {
            // The check decides both relations together, so a refusal
            // establishes neither.
            record.push(legalization(not_established(
                "rejected",
                format!(
                    "{reason} (the affine check decides TrustIR/LIR and LIR/raw MachIR together)"
                ),
            )));
            return;
        }
        record.push(legalization(established()));
        record.push(TransitionLink {
            stage: LinkStage::Selection,
            name: rel::SELECTION_NAME.to_string(),
            relation: rel::SELECTION_RELATION.to_string(),
            check: rel::AFFINE_CHECK.to_string(),
            model: rel::SELECTION_MODEL.to_string(),
            from: lir_interface,
            to: ct::mach_function_interface(raw),
            to_len: None,
            strength: EvidenceStrength::ExactlyDecided,
            verdict: established(),
        });
    }

    /// Record the optimizer's interface-changing runs, each through
    /// [`pass_run_link`].
    pub(crate) fn pass_runs(&mut self, transitions: Vec<PassTransition>) {
        if !self.recording() {
            return;
        }
        let Some(record) = self.record_mut() else {
            return;
        };
        for transition in transitions {
            record.push(pass_run_link(transition));
        }
    }

    /// Capture the interface of `func`, the function entering register
    /// allocation.
    pub(crate) fn pre_allocation(&mut self, func: &MachFunction) {
        if self.recording() {
            self.pre_allocation = Some(ct::mach_function_interface(func));
        }
    }

    /// Record one post-allocation comparison window ending at `func`:
    /// `stage` names it, `verdict` is its recorded verdict (`None` when the
    /// comparison did not run).
    pub(crate) fn post_allocation(
        &mut self,
        stage: &str,
        func: &MachFunction,
        verdict: Option<&ValidationVerdict>,
    ) {
        if !self.recording() {
            return;
        }
        let from = self
            .record
            .as_ref()
            .and_then(|record| {
                record
                    .links
                    .last()
                    .filter(|link| link.stage == LinkStage::PostAllocation)
                    .map(|link| link.to)
            })
            .or(self.pre_allocation);
        let Some(from) = from else {
            if let Some(record) = self.record_mut() {
                record.mark_not_composed(
                    LinkStage::PostAllocation,
                    "the function entering register allocation was not captured",
                );
            }
            return;
        };
        let verdict = match verdict {
            Some(ValidationVerdict::Validated) => established(),
            Some(other) => not_established(other.as_str(), other.reason().unwrap_or_default()),
            None => not_established(
                "not-run",
                "the post-allocation comparison did not run under this pass-validation scope",
            ),
        };
        let to = ct::mach_function_interface(func);
        if let Some(record) = self.record_mut() {
            record.push(TransitionLink {
                stage: LinkStage::PostAllocation,
                name: stage.to_string(),
                relation: rel::POST_ALLOCATION_RELATION.to_string(),
                check: rel::POST_ALLOCATION_CHECK.to_string(),
                model: rel::POST_ALLOCATION_MODEL.to_string(),
                from,
                to,
                to_len: None,
                strength: EvidenceStrength::ExactlyDecided,
                verdict,
            });
        }
    }

    /// Record the encoding of the final function `func`: `encoded` is the
    /// proof-grade encoder's result (bytes and symbolic fixup count) or its
    /// refusal.
    pub(crate) fn encoding(
        &mut self,
        func: &MachFunction,
        encoded: Result<(&[u8], usize), String>,
    ) {
        if !self.recording() {
            return;
        }
        let from = ct::mach_function_interface(func);
        let (to, to_len, verdict) = match encoded {
            Ok((code, 0)) => (
                ct::bytes_interface(code),
                Some(code.len() as u64),
                established(),
            ),
            Ok((code, fixups)) => (
                ct::bytes_interface(code),
                Some(code.len() as u64),
                not_established(
                    "fixups",
                    format!(
                        "the encoded function carries {fixups} symbolic fixup(s); a relocation \
                         applied after the check could rewrite a checked word"
                    ),
                ),
            ),
            Err(reason) => (
                ct::bytes_interface(&[]),
                None,
                not_established("rejected", reason),
            ),
        };
        if let Some(record) = self.record_mut() {
            record.push(TransitionLink {
                stage: LinkStage::Encoding,
                name: rel::ENCODING_NAME.to_string(),
                relation: rel::ENCODING_RELATION.to_string(),
                check: rel::ENCODING_CHECK.to_string(),
                model: rel::ENCODING_MODEL.to_string(),
                from,
                to,
                to_len,
                strength: EvidenceStrength::ExactlyDecided,
                verdict,
            });
        }
    }

    /// The finished record.
    pub(crate) fn finish(self) -> Option<TransitionRecord> {
        self.record
    }
}

/// The composition a route that requires compositions publishes
/// `function` under, checked against nothing yet: `Ok(None)` when no
/// TrustIR-bound legalization check covers it, the composition when its
/// record composes at [`EvidenceStrength::ExactlyDecided`] or stronger,
/// and the refusal otherwise. A missing record refuses: such a route always
/// builds one.
pub fn require_composition(
    function: &str,
    record: Option<&TransitionRecord>,
) -> Result<Option<ComposedTransition>, CompositionRefusal> {
    let Some(record) = record else {
        return Err(CompositionRefusal::NotComposed {
            function: function.to_string(),
            stage: LinkStage::Legalization,
            reason: "no composed transition record was built for this function".to_string(),
        });
    };
    if !record.in_legalization_domain() {
        return Ok(None);
    }
    record
        .compose_at_least(EvidenceStrength::ExactlyDecided)
        .map(Some)
}

/// [`require_composition`], then refuse unless `published` (the bytes the
/// route publishes for the function, before any relocation) are the chain's
/// terminal and carry no symbolic fixup (`published_fixups`) a later
/// relocation could apply.
pub fn require_published(
    function: &str,
    record: Option<&TransitionRecord>,
    published: &[u8],
    published_fixups: usize,
) -> Result<Option<ComposedTransition>, CompositionRefusal> {
    let composed = require_composition(function, record)?;
    if let Some(composed) = &composed {
        if published_fixups != 0 {
            return Err(CompositionRefusal::NotComposed {
                function: function.to_string(),
                stage: LinkStage::Encoding,
                reason: format!(
                    "the published function carries {published_fixups} symbolic fixup(s) the \
                     composed bytes do not"
                ),
            });
        }
        composed.check_published(published)?;
    }
    Ok(composed)
}

/// The AArch64 `NOP` word the module emitters pad between functions with
/// (little-endian).
const AARCH64_NOP: [u8; 4] = 0xd503_201f_u32.to_le_bytes();

/// The bytes the object `object` (AArch64 Mach-O or ELF, relocatable)
/// carries for the function `name` (its IR name), `len` bytes from its
/// defining symbol, read independently of the writer, refused unless they
/// are exactly the symbol's extent and no relocation patches them:
///
/// * ELF: the symbol's `st_size` is `len`;
/// * Mach-O (no symbol sizes): no other symbol is defined inside the `len`
///   bytes, and every byte from their end to the next symbol defined in the
///   section (or the section's end) belongs to `NOP` padding words;
/// * both: no relocation record of the section patches a byte inside them,
///   so the linker cannot rewrite a word the chain checked.
pub fn object_function_bytes(object: &[u8], name: &str, len: u64) -> Result<Vec<u8>, String> {
    let len_usize = usize::try_from(len).map_err(|_| format!("length {len} does not fit"))?;
    let slice = |data: &[u8], offset: u64| -> Result<Vec<u8>, String> {
        let start = usize::try_from(offset).map_err(|_| "offset does not fit".to_string())?;
        data.get(start..start.saturating_add(len_usize))
            .filter(|bytes| bytes.len() == len_usize)
            .map(<[u8]>::to_vec)
            .ok_or_else(|| {
                format!("`{name}`: {len} bytes at section offset {start} leave its section")
            })
    };
    let inside = |at: u64, offset: u64| at >= offset && at - offset < len;
    if object.starts_with(b"\x7fELF") {
        let records = crate::elf::reparse::read_object_records(object)
            .map_err(|error| format!("the object does not parse as ELF: {error}"))?;
        let symbol = records
            .symbols
            .iter()
            .find(|symbol| symbol.name == name && symbol.defining_section().is_some())
            .ok_or_else(|| format!("`{name}` has no defining symbol"))?;
        let index = symbol
            .defining_section()
            .ok_or_else(|| format!("`{name}` names no section"))?;
        let section = records
            .sections
            .get(index)
            .ok_or_else(|| format!("`{name}`'s section is not in the object"))?;
        if symbol.size != len {
            return Err(format!(
                "`{name}`'s symbol size is {} bytes, not the {len} composed bytes",
                symbol.size
            ));
        }
        if let Some(relocation) = records.relocations.iter().find(|relocation| {
            relocation.target_section == index && inside(relocation.record.r_offset, symbol.value)
        }) {
            return Err(format!(
                "`{name}`: a relocation (type {}) patches section offset {:#x}, inside the \
                 composed bytes",
                relocation.record.reloc_type, relocation.record.r_offset
            ));
        }
        let start = usize::try_from(section.offset).map_err(|_| "offset does not fit")?;
        let end = start.saturating_add(usize::try_from(section.size).unwrap_or(usize::MAX));
        let data = object
            .get(start..end)
            .ok_or_else(|| format!("`{name}`'s section leaves the object"))?;
        return slice(data, symbol.value);
    }
    let records = crate::macho::reparse::read_object_records(object)
        .map_err(|error| format!("the object does not parse as Mach-O: {error}"))?;
    let stored = format!("_{name}");
    let symbol = records
        .symbols
        .iter()
        .find(|symbol| !symbol.is_stab() && symbol.n_sect != 0 && symbol.name == stored)
        .ok_or_else(|| format!("`{stored}` has no defining symbol"))?;
    let section = records
        .section(symbol.n_sect)
        .ok_or_else(|| format!("`{stored}`'s section is not in the object"))?;
    let offset = symbol
        .n_value
        .checked_sub(section.addr)
        .ok_or_else(|| format!("`{stored}` lies before its section"))?;
    let bytes = slice(&section.data, offset)?;
    // The symbol's extent: up to the next symbol defined in the section.
    let others = records.symbols.iter().filter(|other| {
        !other.is_stab() && other.n_sect == symbol.n_sect && other.n_value != symbol.n_value
    });
    let mut extent_end = section.size;
    for other in others {
        let at = other.n_value.saturating_sub(section.addr);
        if inside(at, offset) {
            return Err(format!(
                "`{stored}`: `{}` is defined at section offset {at:#x}, inside the composed \
                 bytes",
                other.name
            ));
        }
        if at > offset {
            extent_end = extent_end.min(at);
        }
    }
    let tail_start = usize::try_from(offset.saturating_add(len)).map_err(|_| "tail")?;
    let tail_end = usize::try_from(extent_end).map_err(|_| "extent")?;
    let tail = section
        .data
        .get(tail_start..tail_end.max(tail_start))
        .unwrap_or_default();
    if !tail.len().is_multiple_of(4) || tail.chunks(4).any(|word| word != AARCH64_NOP) {
        return Err(format!(
            "`{stored}`'s extent holds {} byte(s) past the composed bytes that are not NOP \
             padding",
            tail.len()
        ));
    }
    let section_index = usize::from(symbol.n_sect) - 1;
    if let Some(relocation) = records
        .section_relocations
        .get(section_index)
        .into_iter()
        .flatten()
        .find(|relocation| inside(u64::from(relocation.r_address), offset))
    {
        return Err(format!(
            "`{stored}`: a relocation (type {}) patches section offset {:#x}, inside the composed \
             bytes",
            relocation.r_type, relocation.r_address
        ));
    }
    Ok(bytes)
}

/// Refuse unless, for every record in a TrustIR-bound legalization check's
/// domain, the record composes and the object carries exactly its
/// terminal bytes for the function, as the function's whole symbol extent
/// with no relocation inside ([`object_function_bytes`]). Returns the number
/// of functions whose composition was required and published.
pub fn require_object_publication(
    object: &[u8],
    records: &[(&str, Option<&TransitionRecord>)],
) -> Result<usize, CompositionRefusal> {
    let mut published = 0;
    for (function, record) in records {
        let Some(composed) = require_composition(function, *record)? else {
            continue;
        };
        let len = composed.terminal_len.unwrap_or(0);
        let bytes = object_function_bytes(object, function, len).map_err(|reason| {
            CompositionRefusal::NotComposed {
                function: function.to_string(),
                stage: LinkStage::Encoding,
                reason: format!(
                    "the object's bytes for the function are not bound to the chain: {reason}"
                ),
            }
        })?;
        composed.check_published(&bytes)?;
        published += 1;
    }
    Ok(published)
}

/// Corruption hooks for this crate's route tests: an unvalidated rewrite
/// between the optimizer and allocation, a rewrite run inside the optimizer
/// driver through its own validation and transition recording, and a byte
/// changed after the encoding link; and a promotion waiver that lets a route
/// test reach the publication checks that run after proof promotion on a
/// host whose proof tools refuse promotion. Each is armed per thread and
/// does nothing otherwise; none exists outside this crate's unit tests.
#[cfg(test)]
pub(crate) mod test_hooks {
    use std::cell::Cell;
    use trust_cg_ir::{InstFlags, MachFunction, MachOperand};
    use trust_cg_opt::{
        FunctionInterfaceDigest, MachinePass, PassValidationConfig, PassValidationSummary,
    };

    /// A rewrite [`optimizer_step`] runs.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub(crate) enum OptimizerStep {
        /// A pass with no dedicated validator changes a constant and says so.
        ReportedRewrite,
        /// The same rewrite reported as no change.
        SilentRewrite,
        /// The rewrite as a step outside the pass manager no validator
        /// covers (how CEGIS and the extended loop rotation are recorded).
        UncoveredStep,
    }

    impl OptimizerStep {
        /// The run's name in the record.
        pub(crate) fn name(self) -> &'static str {
            match self {
                Self::ReportedRewrite => "test-reported-rewrite",
                Self::SilentRewrite => "test-silent-rewrite",
                Self::UncoveredStep => "test-uncovered-step",
            }
        }
    }

    thread_local! {
        static UNVALIDATED_STEP: Cell<bool> = const { Cell::new(false) };
        static FLIP_PUBLISHED_BYTE: Cell<bool> = const { Cell::new(false) };
        static OPTIMIZER_STEP: Cell<Option<OptimizerStep>> = const { Cell::new(None) };
        static PROMOTION_WAIVED: Cell<bool> = const { Cell::new(false) };
    }

    /// Disarms its hook when dropped, so a panicking body leaves the thread
    /// clean for the next test.
    struct Disarm(fn());

    impl Drop for Disarm {
        fn drop(&mut self) {
            (self.0)();
        }
    }

    /// Run `body` with the unvalidated rewrite armed.
    // Called only by the AArch64 verify route tests (compiler.rs).
    #[cfg(all(feature = "verify", target_arch = "aarch64"))]
    pub(crate) fn with_unvalidated_step<T>(body: impl FnOnce() -> T) -> T {
        UNVALIDATED_STEP.with(|armed| armed.set(true));
        let _disarm = Disarm(|| UNVALIDATED_STEP.with(|armed| armed.set(false)));
        body()
    }

    /// Run `body` with the published-byte flip armed.
    // Called only by the AArch64 verify route tests (compiler.rs).
    #[cfg(all(feature = "verify", target_arch = "aarch64"))]
    pub(crate) fn with_flipped_published_byte<T>(body: impl FnOnce() -> T) -> T {
        FLIP_PUBLISHED_BYTE.with(|armed| armed.set(true));
        let _disarm = Disarm(|| FLIP_PUBLISHED_BYTE.with(|armed| armed.set(false)));
        body()
    }

    /// Run `body` with `step` armed in the optimizer driver.
    pub(crate) fn with_optimizer_step<T>(step: OptimizerStep, body: impl FnOnce() -> T) -> T {
        OPTIMIZER_STEP.with(|armed| armed.set(Some(step)));
        let _disarm = Disarm(|| OPTIMIZER_STEP.with(|armed| armed.set(None)));
        body()
    }

    /// Run `body` with proof promotion waived on the routes that publish
    /// after it, so a route test reaches their publication checks on a host
    /// whose proof tools refuse promotion. Only the composed transition
    /// route tests arm it; it changes nothing else a route checks.
    // Called only by the AArch64 verify route tests (compiler.rs).
    #[cfg(all(feature = "verify", target_arch = "aarch64"))]
    pub(crate) fn with_promotion_waived<T>(body: impl FnOnce() -> T) -> T {
        PROMOTION_WAIVED.with(|armed| armed.set(true));
        let _disarm = Disarm(|| PROMOTION_WAIVED.with(|armed| armed.set(false)));
        body()
    }

    /// Whether [`with_promotion_waived`] is armed on this thread.
    pub(crate) fn promotion_waived() -> bool {
        PROMOTION_WAIVED.with(Cell::get)
    }

    /// Adds one to the immediate addend of the first `ADD`/`SUB #imm` in
    /// layout order: a change of the function's result (a dead constant
    /// would be a rewrite the validators rightly accept) that no dedicated
    /// validator owns.
    struct BumpImmediate {
        name: &'static str,
        report: bool,
    }

    impl MachinePass for BumpImmediate {
        fn name(&self) -> &str {
            self.name
        }

        fn run(&mut self, func: &mut MachFunction) -> bool {
            bump_first_immediate(func);
            self.report
        }
    }

    fn bump_first_immediate(func: &mut MachFunction) {
        use trust_cg_ir::AArch64Opcode::{AddRI, SubRI};
        let order = func.block_order.clone();
        for block in order {
            for id in func.block(block).insts.clone() {
                let inst = func.inst_mut(id);
                if matches!(inst.opcode, AddRI | SubRI)
                    && let Some(MachOperand::Imm(value)) = inst.operands.get_mut(2)
                    && (0..4094).contains(value)
                {
                    *value += 1;
                    return;
                }
            }
        }
        panic!("`{}` carries no ADD/SUB immediate to rewrite", func.name);
    }

    /// When armed, run the armed rewrite on `func` the way the optimizer
    /// driver runs a mutating step: a pass through
    /// [`trust_cg_opt::pass_validation::run_validated_with_transitions`]
    /// under the function's validation `config` and transition `digest`,
    /// or an unvalidated step recorded with
    /// [`trust_cg_opt::pass_validation::record_unvalidated_transition`].
    pub(crate) fn optimizer_step(
        func: &mut MachFunction,
        config: PassValidationConfig,
        digest: Option<FunctionInterfaceDigest>,
        summary: &mut PassValidationSummary,
    ) {
        let Some(step) = OPTIMIZER_STEP.with(Cell::get) else {
            return;
        };
        match step {
            OptimizerStep::ReportedRewrite | OptimizerStep::SilentRewrite => {
                trust_cg_opt::pass_validation::run_validated_with_transitions(
                    config,
                    digest,
                    &mut BumpImmediate {
                        name: step.name(),
                        report: step == OptimizerStep::ReportedRewrite,
                    },
                    func,
                    summary,
                );
            }
            OptimizerStep::UncoveredStep => {
                let before = digest.map(|digest| digest(func));
                bump_first_immediate(func);
                trust_cg_opt::pass_validation::record_unvalidated_change(
                    config,
                    step.name(),
                    func,
                    summary,
                );
                trust_cg_opt::pass_validation::record_unvalidated_transition(
                    digest,
                    step.name(),
                    before,
                    func,
                    summary,
                );
            }
        }
    }

    /// When armed, mark the first entry instruction reorderable: a rewrite of
    /// the function's interface that no validator sees and that changes no
    /// encoded word.
    pub(crate) fn unvalidated_step(func: &mut MachFunction) {
        if !UNVALIDATED_STEP.with(Cell::get) {
            return;
        }
        let entry = func.entry;
        if let Some(&first) = func.block(entry).insts.first() {
            let flags = &mut func.inst_mut(first).flags;
            if flags.contains(InstFlags::PROOF_REORDERABLE) {
                flags.remove(InstFlags::PROOF_REORDERABLE);
            } else {
                flags.insert(InstFlags::PROOF_REORDERABLE);
            }
        }
    }

    /// When armed, flip the low bit of the first published byte.
    pub(crate) fn flip_published_byte(code: &mut [u8]) {
        if FLIP_PUBLISHED_BYTE.with(Cell::get)
            && let Some(byte) = code.first_mut()
        {
            *byte ^= 1;
        }
    }

    /// When armed, a copy of `object` with the low bit of the first code
    /// byte of the first function whose record composes flipped (located
    /// by its bytes); `None` otherwise.
    pub(crate) fn flip_object_function_byte(
        object: &[u8],
        records: &[(&str, Option<&super::TransitionRecord>)],
    ) -> Option<Vec<u8>> {
        if !FLIP_PUBLISHED_BYTE.with(Cell::get) {
            return None;
        }
        let (name, len) = records.iter().find_map(|(name, record)| {
            let composed = (*record)?.compose().ok()?;
            Some((*name, composed.terminal_len?))
        })?;
        let bytes = super::object_function_bytes(object, name, len).ok()?;
        let at = object
            .windows(bytes.len())
            .position(|window| window == bytes.as_slice())?;
        let mut flipped = object.to_vec();
        flipped[at] ^= 1;
        Some(flipped)
    }
}

#[cfg(test)]
#[path = "composed_transition_tests.rs"]
mod tests;
