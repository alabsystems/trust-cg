// trust-cg-verify/composed_transition.rs - composed per-function transition chain
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The composed transition record of one AArch64 function (ledger L09-P3).
//!
//! Each stage check of the backend relates two representations of one
//! function: the TrustIR/LIR/raw-MachIR affine check
//! ([`crate::aarch64_affine_lowering::check_aarch64_trust_ir_affine_lowering`]),
//! the per-pass validators (`trust_cg_opt::pass_validation`), the
//! post-allocation value-flow comparison ([`crate::post_ra_value_flow`]) and
//! the encoder's own word checks (ENC-5's independent decode of every
//! emitted word, the final-layout cross-check and the switch binding). On
//! their own they are disjoint: a receipt from one stage says nothing about
//! the program the next stage receives. A [`TransitionRecord`] chains them.
//! Each [`TransitionLink`] names its relation, the check that decided it, its
//! model, its evidence strength and the exact interface at both ends: the
//! [`Interface`] digest of the program it read and of the program it
//! produced or compared against. [`TransitionRecord::compose`] accepts the
//! chain only when
//!
//! * the links run in the canonical order — legalization
//!   (TrustIR → LIR), selection (LIR → raw MachIR), one pass run per
//!   interface-changing run of a mutating optimizer step (MachIR → MachIR,
//!   none when nothing changed the function), the post-allocation
//!   comparison (pre-allocation MachIR → final MachIR, one link or the two
//!   split windows) and encoding (final MachIR → bytes) — with every
//!   required stage present;
//! * every link's endpoints have its stage's representations;
//! * every link was established by its check;
//! * every adjacent pair shares one interface: the program a link produced
//!   is, digest for digest, the program the next link read. An unchecked
//!   mutation between two links, an unvalidated pass, a dropped link or a
//!   swapped digest therefore breaks the chain by name.
//!
//! [`ComposedTransition::check_published`] then binds the chain's terminal to
//! the bytes a route actually publishes, so a byte changed after the last
//! link is refused as well.
//!
//! # What an accepted composition establishes
//!
//! For the function's TrustIR source (the module-owned function the adapter
//! translated), on every input where that source is defined under the
//! legalization check's domain premises, the published code bytes compute
//! the source's result — **provided** each link's relation holds under its
//! own model ([`TransitionLink::model`]): the affine check's exact modular
//! interpretation of TrustIR, LIR and the selected AArch64 instructions; the
//! pass validators' machine model, which shares the optimizer's operand-role
//! and memory-effect tables; the post-allocation comparison's model (affine
//! forms of at most eight atoms, everything else uninterpreted, calls and
//! the frame under its stated ABI premises); and ENC-5's independent A64
//! decoder, which shows each word decodes to its instruction. Every model is
//! a sound abstraction of AArch64 only to the extent its Rust implementation
//! is; that implementation, the digests and the encoder's relocation-free
//! output are trusted. The chain composes equalities, so its strength is
//! the weakest link's ([`EvidenceStrength`]); no link is ever upgraded, and
//! nothing here is a machine-checked proof unless every link is
//! [`EvidenceStrength::Formal`].
//!
//! Today legalization is checked only inside the affine check's domain (a
//! one-block or one-diamond function of homogeneous I32/U32/I64/U64 values,
//! constants, copies, wrapping add/sub, comparisons and flat selects, at most
//! eight register parameters, no calls, memory or control beyond the
//! diamond). Outside it the record says [`NotComposed`] at the legalization
//! stage, and no TrustIR-to-bytes claim exists for that function.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fmt;
use std::hash::Hasher;
use trust_cg_ir::MachFunction;

/// Format tag of a [`TransitionRecord`].
pub const RECORD_FORMAT: &str = "trust-cg.composed-transition.v1";

/// Diagnostic prefix of every composition refusal.
pub const TAG: &str = "[TCG-COMPOSED-TRANSITION]";

/// What a link's relation reads or produces.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Representation {
    /// One module-owned TrustIR function ([`trust_ir_function_interface`]).
    TrustIr,
    /// The adapter's LIR function ([`lir_function_interface`]).
    Lir,
    /// A machine-IR function ([`mach_function_interface`]).
    MachIr,
    /// Encoded code bytes ([`bytes_interface`]).
    Bytes,
}

impl Representation {
    /// Stable spelling.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::TrustIr => "trust-ir",
            Self::Lir => "lir",
            Self::MachIr => "mach-ir",
            Self::Bytes => "bytes",
        }
    }
}

/// One end of a link: a representation and the exact SHA-256 digest of the
/// program in it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Interface {
    pub representation: Representation,
    pub digest: [u8; 32],
}

impl Interface {
    /// The digest in lowercase hexadecimal.
    pub fn hex(&self) -> String {
        hex(&self.digest)
    }
}

impl fmt::Display for Interface {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.representation.as_str(), &self.hex()[..16])
    }
}

fn hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        let _ = write!(out, "{byte:02x}");
    }
    out
}

/// A [`Hasher`] that feeds SHA-256 through a buffer.
struct Sha256Hasher {
    hasher: Sha256,
    buffer: Vec<u8>,
}

impl Sha256Hasher {
    fn new(domain: &[u8]) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(domain);
        Self {
            hasher,
            buffer: Vec::with_capacity(1 << 14),
        }
    }

    fn finalize(mut self) -> [u8; 32] {
        self.hasher.update(&self.buffer);
        self.hasher.finalize().into()
    }
}

impl Hasher for Sha256Hasher {
    fn finish(&self) -> u64 {
        // Never consulted: the digest is `finalize`.
        0
    }

    fn write(&mut self, bytes: &[u8]) {
        self.buffer.extend_from_slice(bytes);
        if self.buffer.len() >= 1 << 14 {
            self.hasher.update(&self.buffer);
            self.buffer.clear();
        }
    }
}

impl fmt::Write for Sha256Hasher {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        Hasher::write(self, text.as_bytes());
        Ok(())
    }
}

/// The interface of the module-owned TrustIR function at `ordinal`: SHA-256
/// of its ordinal, its complete `Debug` rendering (name, identity, blocks,
/// instructions, proofs, attributes, linkage, calling convention, summary
/// and producer) and its function type's. `None` when `ordinal` is outside
/// the module or names a signature the module does not hold.
pub fn trust_ir_function_interface(module: &trust_ir::Module, ordinal: usize) -> Option<Interface> {
    use std::fmt::Write as _;
    let function = module.functions.get(ordinal)?;
    let signature = module.func_types.get(function.ty.index() as usize)?;
    let mut h = Sha256Hasher::new(b"trust-cg.composed-transition.trust-ir-function.v1\0");
    Hasher::write(&mut h, &(ordinal as u64).to_le_bytes());
    write!(h, "{function:?}\0{signature:?}").ok()?;
    Some(Interface {
        representation: Representation::TrustIr,
        digest: h.finalize(),
    })
}

/// The interface of an LIR function: SHA-256 of its compact verifier
/// identity ([`trust_cg_lower::Function::write_compact_verifier_identity`]),
/// the rendering that separates functions exactly as the canonical one does.
pub fn lir_function_interface(function: &trust_cg_lower::Function) -> Interface {
    let mut h = Sha256Hasher::new(b"trust-cg.composed-transition.lir-function.v1\0");
    function
        .write_compact_verifier_identity(&mut h)
        .expect("writing LIR into SHA-256 cannot fail");
    Interface {
        representation: Representation::Lir,
        digest: h.finalize(),
    }
}

/// SHA-256 of a machine function's interface
/// ([`trust_cg_opt::pass_validation::hash_function_interface`]): the
/// [`trust_cg_opt::FunctionInterfaceDigest`] the optimizer records pass
/// transitions with.
pub fn mach_function_interface_digest(function: &MachFunction) -> [u8; 32] {
    let mut h = Sha256Hasher::new(b"trust-cg.composed-transition.mach-function.v1\0");
    trust_cg_opt::pass_validation::hash_function_interface(function, &mut h);
    h.finalize()
}

/// [`mach_function_interface_digest`] as an [`Interface`].
pub fn mach_function_interface(function: &MachFunction) -> Interface {
    Interface {
        representation: Representation::MachIr,
        digest: mach_function_interface_digest(function),
    }
}

/// The interface of encoded code: the plain SHA-256 of the bytes (the digest
/// a JIT certificate records as its normalized machine-code digest).
pub fn bytes_interface(code: &[u8]) -> Interface {
    Interface {
        representation: Representation::Bytes,
        digest: Sha256::digest(code).into(),
    }
}

/// A link's place in the canonical chain.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum LinkStage {
    /// TrustIR → LIR.
    Legalization,
    /// LIR → raw (pre-optimization) MachIR.
    Selection,
    /// One run of a mutating optimizer step: MachIR → MachIR.
    PassRun,
    /// The post-allocation comparison: pre-allocation MachIR → final MachIR.
    PostAllocation,
    /// Final MachIR → encoded bytes.
    Encoding,
}

impl LinkStage {
    /// Stable spelling.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Legalization => "legalization",
            Self::Selection => "selection",
            Self::PassRun => "pass-run",
            Self::PostAllocation => "post-allocation",
            Self::Encoding => "encoding",
        }
    }

    /// The representations this stage reads and produces.
    pub fn endpoints(self) -> (Representation, Representation) {
        match self {
            Self::Legalization => (Representation::TrustIr, Representation::Lir),
            Self::Selection => (Representation::Lir, Representation::MachIr),
            Self::PassRun | Self::PostAllocation => {
                (Representation::MachIr, Representation::MachIr)
            }
            Self::Encoding => (Representation::MachIr, Representation::Bytes),
        }
    }

    /// The required stages, in order.
    pub const REQUIRED: [LinkStage; 4] = [
        Self::Legalization,
        Self::Selection,
        Self::PostAllocation,
        Self::Encoding,
    ];
}

/// The strength of the evidence a link's verdict carries, weakest first.
/// A composition is as strong as its weakest link and is never upgraded.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum EvidenceStrength {
    /// Sampled or bounded: the relation was tested, not decided.
    Statistical,
    /// Decided exactly over the link's model by an in-process check
    /// (trusted Rust); a positive verdict holds for every input the model
    /// covers.
    ExactlyDecided,
    /// A machine-checked proof of the relation, independently replayed.
    Formal,
}

impl EvidenceStrength {
    /// Stable spelling.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Statistical => "statistical",
            Self::ExactlyDecided => "exactly-decided",
            Self::Formal => "formal",
        }
    }
}

/// Whether a link's check established its relation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case", tag = "verdict")]
pub enum LinkVerdict {
    /// The check established the relation.
    Established,
    /// The check did not: `outcome` is its own verdict spelling (refuted,
    /// unproved, uncovered, rejected, ...), `reason` its detail.
    NotEstablished { outcome: String, reason: String },
}

impl LinkVerdict {
    /// Whether the relation was established.
    pub fn is_established(&self) -> bool {
        matches!(self, Self::Established)
    }
}

/// One checked transition of the function.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransitionLink {
    /// Its place in the chain.
    pub stage: LinkStage,
    /// What ran: the stage boundary, pass or step name.
    pub name: String,
    /// The relation the check decides between `from` and `to`.
    pub relation: String,
    /// The check that decided it.
    pub check: String,
    /// The model the relation is decided over (what is trusted).
    pub model: String,
    /// The program the check read.
    pub from: Interface,
    /// The program the check produced or compared against.
    pub to: Interface,
    /// The byte length of `to` when it is a [`Representation::Bytes`]
    /// interface (an encoding link), so a reader can locate the published
    /// bytes it must compare.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub to_len: Option<u64>,
    /// The evidence strength of an established verdict.
    pub strength: EvidenceStrength,
    /// The check's verdict.
    pub verdict: LinkVerdict,
}

/// Why a producer could not start or continue a chain.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NotComposed {
    /// The first stage no link could be produced for.
    pub stage: LinkStage,
    /// Why.
    pub reason: String,
}

/// The transition chain of one function, as its producer recorded it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransitionRecord {
    /// [`RECORD_FORMAT`].
    pub format: String,
    /// The function's symbol.
    pub function: String,
    /// The links, in the order the stages ran.
    pub links: Vec<TransitionLink>,
    /// Set when the producer could not build a link for some stage; the
    /// chain is then not composed whatever `links` holds.
    pub not_composed: Option<NotComposed>,
}

/// An accepted composition.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComposedTransition {
    /// The function's symbol.
    pub function: String,
    /// What the composition establishes ([`ComposedTransition::CLAIM`]),
    /// carried in every accepted composition so a report or census that
    /// prints it states the claim with the chain, under the strength below.
    pub claim: String,
    /// The TrustIR interface the chain starts from.
    pub origin: Interface,
    /// The bytes interface the chain ends at.
    pub terminal: Interface,
    /// The length of those bytes, as the encoding link recorded it.
    pub terminal_len: Option<u64>,
    /// The weakest link's strength: the composition's, never upgraded.
    pub strength: EvidenceStrength,
    /// Every link's stage, name and strength, in chain order, so the
    /// strength of each link stays visible next to the composition's.
    pub link_strengths: Vec<(LinkStage, String, EvidenceStrength)>,
    /// Links composed.
    pub links: usize,
    /// Of them, optimizer pass runs.
    pub pass_runs: usize,
}

/// Why a chain does not compose, or does not reach the published bytes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, thiserror::Error)]
#[serde(rename_all = "kebab-case", tag = "refusal")]
pub enum CompositionRefusal {
    /// The producer could not build a link for `stage`.
    #[error("{TAG} `{function}`: not composed at the {} stage: {reason}", stage.as_str())]
    NotComposed {
        function: String,
        stage: LinkStage,
        reason: String,
    },
    /// The record is not this module's format.
    #[error("{TAG} `{function}`: record format `{found}` is not `{RECORD_FORMAT}`")]
    Format { function: String, found: String },
    /// A required stage has no link.
    #[error("{TAG} `{function}`: missing the {} link", stage.as_str())]
    MissingLink { function: String, stage: LinkStage },
    /// A link sits where its stage may not: after a later stage, or a
    /// second legalization, selection or encoding.
    #[error(
        "{TAG} `{function}`: link {index} `{name}` ({}) is out of order after a {} link",
        stage.as_str(),
        after.as_str()
    )]
    OutOfOrder {
        function: String,
        index: usize,
        name: String,
        stage: LinkStage,
        after: LinkStage,
    },
    /// A link's endpoint is not its stage's representation.
    #[error(
        "{TAG} `{function}`: link {index} `{name}` ({}) reads {} and produces {}, \
         not {} and {}",
        stage.as_str(),
        found.0.as_str(),
        found.1.as_str(),
        expected.0.as_str(),
        expected.1.as_str()
    )]
    RepresentationMismatch {
        function: String,
        index: usize,
        name: String,
        stage: LinkStage,
        expected: (Representation, Representation),
        found: (Representation, Representation),
    },
    /// A link's check did not establish its relation.
    #[error(
        "{TAG} `{function}`: link {index} `{name}` ({}) was not established: {outcome}: {reason}",
        stage.as_str()
    )]
    LinkNotEstablished {
        function: String,
        index: usize,
        name: String,
        stage: LinkStage,
        outcome: String,
        reason: String,
    },
    /// Two adjacent links do not share an interface: the program one link
    /// produced is not the program the next one read.
    #[error(
        "{TAG} `{function}`: link {index} `{left_name}` ends at {left} but link {} \
         `{right_name}` starts at {right}",
        index + 1
    )]
    InterfaceMismatch {
        function: String,
        index: usize,
        left_name: String,
        right_name: String,
        /// Boxed so a refusal stays small (two inline interfaces would
        /// make every `Result` carrying one large).
        left: Box<Interface>,
        right: Box<Interface>,
    },
    /// The chain starts from another program than the one expected.
    #[error("{TAG} `{function}`: the chain starts at {found}, not the source {expected}")]
    OriginMismatch {
        function: String,
        expected: Interface,
        found: Interface,
    },
    /// The published bytes are not the bytes the chain ends at.
    #[error("{TAG} `{function}`: the published bytes {published} are not the composed {terminal}")]
    PublishedBytesMismatch {
        function: String,
        terminal: Interface,
        published: Interface,
    },
    /// The chain is weaker than the caller requires.
    #[error(
        "{TAG} `{function}`: the composition is {} (link `{weakest}`), weaker than the required {}",
        strength.as_str(),
        required.as_str()
    )]
    InsufficientStrength {
        function: String,
        weakest: String,
        strength: EvidenceStrength,
        required: EvidenceStrength,
    },
}

impl CompositionRefusal {
    /// Stable kebab-case name of the refusal class.
    pub fn class(&self) -> &'static str {
        match self {
            Self::NotComposed { .. } => "not-composed",
            Self::Format { .. } => "format",
            Self::MissingLink { .. } => "missing-link",
            Self::OutOfOrder { .. } => "out-of-order",
            Self::RepresentationMismatch { .. } => "representation-mismatch",
            Self::LinkNotEstablished { .. } => "link-not-established",
            Self::InterfaceMismatch { .. } => "interface-mismatch",
            Self::OriginMismatch { .. } => "origin-mismatch",
            Self::PublishedBytesMismatch { .. } => "published-bytes-mismatch",
            Self::InsufficientStrength { .. } => "insufficient-strength",
        }
    }

    /// The stage the refusal names, when it names one.
    pub fn stage(&self) -> Option<LinkStage> {
        match self {
            Self::NotComposed { stage, .. }
            | Self::MissingLink { stage, .. }
            | Self::OutOfOrder { stage, .. }
            | Self::RepresentationMismatch { stage, .. }
            | Self::LinkNotEstablished { stage, .. } => Some(*stage),
            Self::OriginMismatch { .. } => Some(LinkStage::Legalization),
            Self::PublishedBytesMismatch { .. } => Some(LinkStage::Encoding),
            Self::Format { .. }
            | Self::InterfaceMismatch { .. }
            | Self::InsufficientStrength { .. } => None,
        }
    }
}

impl TransitionRecord {
    /// An empty record for `function`.
    pub fn new(function: impl Into<String>) -> Self {
        Self {
            format: RECORD_FORMAT.to_string(),
            function: function.into(),
            links: Vec::new(),
            not_composed: None,
        }
    }

    /// A record whose chain could not be started or continued at `stage`.
    pub fn not_composed(
        function: impl Into<String>,
        stage: LinkStage,
        reason: impl Into<String>,
    ) -> Self {
        let mut record = Self::new(function);
        record.mark_not_composed(stage, reason);
        record
    }

    /// Record that no link could be produced for `stage` (the first such
    /// stage wins).
    pub fn mark_not_composed(&mut self, stage: LinkStage, reason: impl Into<String>) {
        if self.not_composed.is_none() {
            self.not_composed = Some(NotComposed {
                stage,
                reason: reason.into(),
            });
        }
    }

    /// Whether a TrustIR-bound legalization check covers the function: the
    /// producer did not give up at the legalization stage (no TrustIR source,
    /// or a source outside the check's domain). A route that requires
    /// compositions refuses a function in this domain whose record does not
    /// compose; outside it no TrustIR-to-bytes claim exists to require.
    pub fn in_legalization_domain(&self) -> bool {
        !matches!(
            &self.not_composed,
            Some(NotComposed {
                stage: LinkStage::Legalization,
                ..
            })
        )
    }

    /// Append a link.
    pub fn push(&mut self, link: TransitionLink) {
        self.links.push(link);
    }

    /// Whether the producer could still extend the chain: nothing marked it
    /// not composed and every link so far was established.
    pub fn is_open(&self) -> bool {
        self.not_composed.is_none() && self.links.iter().all(|l| l.verdict.is_established())
    }

    /// Check the chain (see the module documentation) and return what it
    /// composes to.
    pub fn compose(&self) -> Result<ComposedTransition, CompositionRefusal> {
        let function = || self.function.clone();
        if self.format != RECORD_FORMAT {
            return Err(CompositionRefusal::Format {
                function: function(),
                found: self.format.clone(),
            });
        }
        if let Some(NotComposed { stage, reason }) = &self.not_composed {
            return Err(CompositionRefusal::NotComposed {
                function: function(),
                stage: *stage,
                reason: reason.clone(),
            });
        }
        // Link by link, in chain order: its place, its representations, the
        // interface it shares with the previous link, then its verdict. The
        // first problem along the chain is the one named.
        let mut previous: Option<&TransitionLink> = None;
        for (index, link) in self.links.iter().enumerate() {
            let after = previous.map(|link| link.stage);
            if let Some(after) = after {
                let repeatable =
                    matches!(link.stage, LinkStage::PassRun | LinkStage::PostAllocation)
                        && link.stage == after;
                if link.stage < after || (link.stage == after && !repeatable) {
                    return Err(CompositionRefusal::OutOfOrder {
                        function: function(),
                        index,
                        name: link.name.clone(),
                        stage: link.stage,
                        after,
                    });
                }
            }
            // A required stage skipped over is missing.
            for required in LinkStage::REQUIRED {
                if after.is_none_or(|p| required > p) && required < link.stage {
                    return Err(CompositionRefusal::MissingLink {
                        function: function(),
                        stage: required,
                    });
                }
            }
            let expected = link.stage.endpoints();
            let found = (link.from.representation, link.to.representation);
            if found != expected {
                return Err(CompositionRefusal::RepresentationMismatch {
                    function: function(),
                    index,
                    name: link.name.clone(),
                    stage: link.stage,
                    expected,
                    found,
                });
            }
            if let Some(left) = previous
                && left.to != link.from
            {
                return Err(CompositionRefusal::InterfaceMismatch {
                    function: function(),
                    index: index - 1,
                    left_name: left.name.clone(),
                    right_name: link.name.clone(),
                    left: Box::new(left.to),
                    right: Box::new(link.from),
                });
            }
            if let LinkVerdict::NotEstablished { outcome, reason } = &link.verdict {
                return Err(CompositionRefusal::LinkNotEstablished {
                    function: function(),
                    index,
                    name: link.name.clone(),
                    stage: link.stage,
                    outcome: outcome.clone(),
                    reason: reason.clone(),
                });
            }
            previous = Some(link);
        }
        for required in LinkStage::REQUIRED {
            if previous.is_none_or(|p| required > p.stage) {
                return Err(CompositionRefusal::MissingLink {
                    function: function(),
                    stage: required,
                });
            }
        }
        let (first, last) = match (self.links.first(), self.links.last()) {
            (Some(first), Some(last)) => (first, last),
            _ => {
                return Err(CompositionRefusal::MissingLink {
                    function: function(),
                    stage: LinkStage::Legalization,
                });
            }
        };
        let strength = self
            .links
            .iter()
            .map(|link| link.strength)
            .min()
            .unwrap_or(EvidenceStrength::Statistical);
        Ok(ComposedTransition {
            function: function(),
            claim: ComposedTransition::CLAIM.to_string(),
            origin: first.from,
            terminal: last.to,
            terminal_len: last.to_len,
            strength,
            link_strengths: self
                .links
                .iter()
                .map(|link| (link.stage, link.name.clone(), link.strength))
                .collect(),
            links: self.links.len(),
            pass_runs: self
                .links
                .iter()
                .filter(|link| link.stage == LinkStage::PassRun)
                .count(),
        })
    }

    /// The weakest link's name, for a strength refusal.
    fn weakest_link(&self) -> String {
        self.links
            .iter()
            .min_by_key(|link| link.strength)
            .map(|link| link.name.clone())
            .unwrap_or_default()
    }

    /// [`Self::compose`], then require at least `required` strength.
    pub fn compose_at_least(
        &self,
        required: EvidenceStrength,
    ) -> Result<ComposedTransition, CompositionRefusal> {
        let composed = self.compose()?;
        if composed.strength < required {
            return Err(CompositionRefusal::InsufficientStrength {
                function: self.function.clone(),
                weakest: self.weakest_link(),
                strength: composed.strength,
                required,
            });
        }
        Ok(composed)
    }
}

impl ComposedTransition {
    /// What an accepted composition establishes, for records and reports.
    pub const CLAIM: &'static str = "the published code bytes are reached from the TrustIR \
        function through the listed checked transitions with no unchecked mutation of a \
        digested interface field between them; under the conjunction of the links' models \
        (each trusted Rust) they compute the source's result on every input where the source \
        is defined; the claim is only as strong as the weakest link and is not a proof unless \
        every link is formal";

    /// Refuse unless the chain starts at `expected`.
    pub fn check_origin(&self, expected: &Interface) -> Result<(), CompositionRefusal> {
        if self.origin != *expected {
            return Err(CompositionRefusal::OriginMismatch {
                function: self.function.clone(),
                expected: *expected,
                found: self.origin,
            });
        }
        Ok(())
    }

    /// Refuse unless `published` are exactly the bytes the chain ends at.
    pub fn check_published(&self, published: &[u8]) -> Result<(), CompositionRefusal> {
        self.check_published_interface(&bytes_interface(published))
    }

    /// Refuse unless `published` is the chain's terminal interface.
    pub fn check_published_interface(
        &self,
        published: &Interface,
    ) -> Result<(), CompositionRefusal> {
        if self.terminal != *published {
            return Err(CompositionRefusal::PublishedBytesMismatch {
                function: self.function.clone(),
                terminal: self.terminal,
                published: *published,
            });
        }
        Ok(())
    }
}

/// The relations, checks and models of the links the codegen pipeline
/// produces, spelled once so every producer and report agrees.
pub mod relations {
    /// Legalization: TrustIR → LIR.
    pub const LEGALIZATION_NAME: &str = "trust-ir->lir";
    pub const LEGALIZATION_RELATION: &str = "the LIR function returns the TrustIR function's \
        affine value or integer predicate on every input (equal coefficients over Z/2^W)";
    pub const AFFINE_CHECK: &str = "check_aarch64_trust_ir_affine_lowering";
    pub const LEGALIZATION_MODEL: &str = "exact modular affine interpretation of the admitted \
        TrustIR domain (one block or one diamond; homogeneous I32/U32/I64/U64; constants, \
        copies, wrapping add/sub, comparisons, flat selects; nonvariadic C ABI, at most eight \
        register parameters); trusted Rust checker";
    /// Selection: LIR → raw MachIR.
    pub const SELECTION_NAME: &str = "lir->raw-mach-ir";
    pub const SELECTION_RELATION: &str = "the raw selected AArch64 function returns the LIR \
        function's affine value or predicate in the ABI return register on every input, with \
        every instruction checked and TV-3 dataflow integrity enforced";
    pub const SELECTION_MODEL: &str = "exact modular affine interpretation of the selected \
        AArch64 rows (immediates and MOVZ/MOVN/MOVK expansions, CMP/CSET with reaching flags, \
        CSEL), physical registers with X/W aliasing; trusted Rust checker";
    /// Pass runs.
    pub const PASS_RUN_RELATION: &str = "the run's output computes the same values, memory, \
        effects and control decisions as its input";
    pub const PASS_RUN_MODEL: &str = "trust-cg-opt pass validation machine model (normalized \
        terms, byte-level memory with store forwarding, operand-role and memory-effect tables \
        shared with the passes); trusted Rust validator";
    /// Post-allocation.
    pub const POST_ALLOCATION_RELATION: &str = "the final resolved stream performs the \
        allocation input's effects on equal values and decides every branch the same way, \
        with callee-saved and frame obligations met";
    pub const POST_ALLOCATION_CHECK: &str = "post_ra_value_flow::compare";
    pub const POST_ALLOCATION_MODEL: &str = "post-allocation value-flow model (moves, \
        constants, zero extension and affine add/sub/shift forms of at most eight atoms \
        interpreted, everything else uninterpreted; AAPCS64/DarwinPCS calls; FP control, \
        stack-protector guard and callee stack discipline assumed); trusted Rust comparison";
    /// Encoding.
    pub const ENCODING_NAME: &str = "encode";
    pub const ENCODING_RELATION: &str = "every emitted word decodes to its machine instruction \
        and every branch, ADR, literal and jump-table offset matches the final layout; the \
        function carries no symbolic fixup a later relocation could rewrite";
    pub const ENCODING_CHECK: &str = "ENC-5 decode check (enforce, undecoded words refused) + \
        final-layout cross-check (CFG-bound) + switch dispatch binding";
    pub const ENCODING_MODEL: &str = "independent A64 decoder and layout re-derivation; \
        trusted Rust";
}

#[cfg(test)]
#[path = "composed_transition_tests.rs"]
mod tests;
