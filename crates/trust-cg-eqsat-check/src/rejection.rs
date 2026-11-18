// trust-cg-eqsat-check/src/rejection.rs - every reason the checker refuses, with its stable class
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! [`Rejection`]: one variant per distinct reason the checker refuses a
//! (module, input, output, derivation, registry) tuple. Each variant carries
//! the position needed to debug it (block, instruction, skeleton ordinal,
//! operand, term or proof index) and has a stable snake_case
//! [`Rejection::class`].

use std::fmt;

/// Which of the two bodies a rejection is about.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Body {
    Input,
    Output,
}

impl fmt::Display for Body {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Body::Input => "input",
            Body::Output => "output",
        })
    }
}

/// A byte-level decoding failure (section 7.2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecodeError {
    /// The bytes end before a field of `needed` bytes.
    Truncated { needed: usize },
    /// The first eight bytes are not `TCGEQSAT`.
    BadMagic,
    /// The version is not the one the check reads (1 for a function, 2 for
    /// a region).
    BadVersion { version: u32 },
    /// An unknown term, proof or opdesc tag.
    BadTag { what: &'static str, tag: u8 },
    /// An unknown type or operator code.
    BadCode { what: &'static str, code: u8 },
    /// A `str` is not UTF-8.
    BadUtf8,
    /// An index names no entry.
    IndexOutOfRange {
        what: &'static str,
        index: u32,
        limit: usize,
    },
    /// Bytes follow the claims.
    TrailingBytes { count: usize },
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DecodeError::Truncated { needed } => {
                write!(f, "truncated: {needed} more byte(s) needed")
            }
            DecodeError::BadMagic => f.write_str("bad magic (expected TCGEQSAT)"),
            DecodeError::BadVersion { version } => write!(
                f,
                "bad version {version} (a function derivation is version 1, a region derivation version 2)"
            ),
            DecodeError::BadTag { what, tag } => write!(f, "bad {what} tag {tag:#04x}"),
            DecodeError::BadCode { what, code } => write!(f, "bad {what} code {code:#04x}"),
            DecodeError::BadUtf8 => f.write_str("string is not UTF-8"),
            DecodeError::IndexOutOfRange { what, index, limit } => {
                write!(f, "{what} index {index} out of range (have {limit})")
            }
            DecodeError::TrailingBytes { count } => {
                write!(f, "{count} trailing byte(s) after the claims")
            }
        }
    }
}

/// Which canonicity rule of section 7.2 an encoding breaks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NonCanonicalKind {
    /// A term names a term at or after its own index.
    TermOrder,
    /// A proof names a proof at or after its own index.
    ProofOrder,
    /// Two term entries are equal.
    DuplicateTerm,
    /// Two proof entries are equal.
    DuplicateProof,
    /// A term no claim reaches.
    UnreachableTerm,
    /// A proof no claim reaches.
    UnreachableProof,
    /// A rule-table entry no claim reaches.
    UnreachableRule,
    /// Claims not strictly increasing.
    ClaimsOrder,
    /// Rule bindings not strictly sorted by name bytes.
    UnsortedBindings,
    /// The rule table not strictly sorted by name bytes.
    UnsortedRuleTable,
}

impl NonCanonicalKind {
    pub fn as_str(self) -> &'static str {
        match self {
            NonCanonicalKind::TermOrder => "term_order",
            NonCanonicalKind::ProofOrder => "proof_order",
            NonCanonicalKind::DuplicateTerm => "duplicate_term",
            NonCanonicalKind::DuplicateProof => "duplicate_proof",
            NonCanonicalKind::UnreachableTerm => "unreachable_term",
            NonCanonicalKind::UnreachableProof => "unreachable_proof",
            NonCanonicalKind::UnreachableRule => "unreachable_rule",
            NonCanonicalKind::ClaimsOrder => "claims_order",
            NonCanonicalKind::UnsortedBindings => "unsorted_bindings",
            NonCanonicalKind::UnsortedRuleTable => "unsorted_rule_table",
        }
    }
}

/// Where a term-level failure was found.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TermSite {
    /// Entry `index` of the derivation's term table.
    TermTable(usize),
    /// A term built while replaying proof `index`.
    Proof(usize),
    /// A term read from a body at an instruction.
    Body { body: Body, block: u32, inst: usize },
}

impl fmt::Display for TermSite {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TermSite::TermTable(i) => write!(f, "term {i}"),
            TermSite::Proof(i) => write!(f, "proof {i}"),
            TermSite::Body { body, block, inst } => {
                write!(f, "{body} body bb{block} instruction {inst}")
            }
        }
    }
}

/// Why the checker refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Rejection {
    /// A function falls in a section 2.5 class (`class` is the irmid name).
    Ineligible {
        body: Body,
        class: &'static str,
        detail: String,
    },
    /// The two functions differ in a field other than `blocks` and
    /// `value_names`.
    FunctionFieldMismatch { field: &'static str },
    /// A body is not structurally readable (duplicate block id, missing
    /// entry, missing or misplaced terminator, edge to no block, result
    /// count not that of `result_tys`, a `LandingPad` that is not the first
    /// instruction of its block, a `Resume` of a literal or of a landing
    /// pad's selector, or a `Resume` in a function with no `LandingPad`).
    MalformedBody {
        body: Body,
        block: Option<u32>,
        inst: Option<usize>,
        detail: String,
    },
    /// The block lists differ (count, id, order, parameter count or types).
    BlockShapeMismatch { block_index: usize, detail: String },
    /// A value is defined more than once in a body.
    DuplicateDefinition { body: Body, value: u32 },
    /// A use its definition does not make available (section 4: dominance,
    /// and the normal-edge rule for terminator results), or a use that names
    /// no definition.
    NotDominated {
        body: Body,
        block: u32,
        inst: usize,
        value: u32,
        detail: String,
    },
    /// A block has a different number of skeleton instructions.
    SkeletonCountMismatch {
        block: u32,
        input: usize,
        output: usize,
    },
    /// A skeleton instruction differs beyond its value operands.
    SkeletonInstructionMismatch {
        block: u32,
        ordinal: usize,
        input_inst: usize,
        output_inst: usize,
        detail: String,
    },
    /// A skeleton operand's terms differ and no claim concludes the pair.
    OperandUnjustified {
        block: u32,
        ordinal: usize,
        operand: usize,
        input_term: String,
        output_term: String,
    },
    /// A claim starts at a skeleton operand's input term but concludes a
    /// different output term.
    ConclusionMismatch {
        block: u32,
        ordinal: usize,
        operand: usize,
        claim: usize,
        expected: String,
        concluded: String,
    },
    /// A claim justifies no skeleton operand whose terms differ, or repeats
    /// another claim's conclusion.
    ClaimMismatch {
        claim: usize,
        proof: u32,
        detail: String,
    },
    /// The bytes are not a version-1 derivation.
    Decode { offset: usize, detail: DecodeError },
    /// The bytes decode but are not the canonical encoding.
    NonCanonical {
        kind: NonCanonicalKind,
        index: usize,
    },
    /// The derivation names another function.
    FunctionNameMismatch {
        derivation: String,
        function: String,
    },
    /// A term is ill typed.
    IllTypedTerm { site: TermSite, detail: String },
    /// A term names a leaf the input body does not have.
    UnknownLeaf { site: TermSite, leaf: String },
    /// A maybe-poison leaf under an operator or bound to a rule variable.
    MaybePoisonLeaf { site: TermSite, leaf: String },
    /// A rule-table entry names no registry rule.
    UnknownRule { index: usize, name: String },
    /// A rule-table entry's digest is not the registry's.
    DigestMismatch { index: usize, name: String },
    /// A rule step's instance type is not in the rule's domain (or has no
    /// established width in this module).
    TypeNotInDomain {
        proof: usize,
        rule: String,
        ty: &'static str,
    },
    /// A rule step's substitution is not exactly the rule's variables with
    /// terms of the right sorts and kinds.
    BindingMismatch {
        proof: usize,
        rule: String,
        detail: String,
    },
    /// A rule step's premises are not exactly `0..k`.
    PremiseMismatch {
        proof: usize,
        rule: String,
        expected: usize,
        found: Vec<u32>,
    },
    /// A rule step's side condition does not hold.
    SideConditionFailed {
        proof: usize,
        rule: String,
        condition: usize,
    },
    /// `Sym` of a `refines` conclusion.
    SymOfRefines { proof: usize },
    /// `Trans` whose middle terms differ.
    TransMiddleMismatch {
        proof: usize,
        left_rhs: String,
        right_lhs: String,
    },
    /// `Congr` whose children do not fit its operator.
    CongrMismatch { proof: usize, detail: String },
    /// An `Impl` step (a region derivation only) that names no order-free
    /// node of the input region, or an order outside that node's family.
    ImplementMismatch { proof: usize, detail: String },
    /// A literal-sensitive operand (section 2.5: the lane index of
    /// `ExtractElement` / `InsertElement`, either `PtrFromParts` operand, a
    /// `Resume` operand) is defined by a `Const` in the output, and the input
    /// operand is not defined by a `Const` of equal type and value. trust-ir's
    /// validator reads these operands through their defining instruction, so
    /// a `Const` introduced there can turn a valid input into an invalid
    /// output.
    LiteralIntroduced {
        block: u32,
        ordinal: usize,
        operand: usize,
        detail: String,
    },
    /// The provenance of a `Switch` selector that trust-ir-build reads
    /// through its definition changed. Either the selector of an
    /// `exhaustive` `Switch` traces (through `Copy` and widening casts) to an
    /// enum's tag in the output, and the input selector does not trace to the
    /// same tag through the same casts (trust-ir-build holds the case set to
    /// the enum only when the trace resolves); or the input selector of any
    /// `Switch` is defined directly by an `ExtractField` and the output
    /// selector is not defined directly by the skeleton-paired one
    /// (trust-ir-build counts a switch as a handle-lane tag guard only when
    /// its selector is directly a field-0 read, so a copy in front of it
    /// removes the guard).
    TagProvenanceChanged {
        block: u32,
        ordinal: usize,
        detail: String,
    },
    /// The module carries refinement predicates. trust-ir-build then decides
    /// every refined consumption site, and every declared refinement, with
    /// forward fact propagation over the defining instructions (a `Const` is
    /// its value, an `Add`/`Sub`/cast an interval, anything else `top`), so
    /// any graph rewrite can change its verdict; the checker does not model
    /// that propagation and refuses the module.
    RefinementPredicates { predicates: usize },
}

impl Rejection {
    /// A stable snake_case name per variant.
    pub fn class(&self) -> &'static str {
        match self {
            Rejection::Ineligible { .. } => "ineligible",
            Rejection::FunctionFieldMismatch { .. } => "function_field_mismatch",
            Rejection::MalformedBody { .. } => "malformed_body",
            Rejection::BlockShapeMismatch { .. } => "block_shape_mismatch",
            Rejection::DuplicateDefinition { .. } => "duplicate_definition",
            Rejection::NotDominated { .. } => "not_dominated",
            Rejection::SkeletonCountMismatch { .. } => "skeleton_count_mismatch",
            Rejection::SkeletonInstructionMismatch { .. } => "skeleton_instruction_mismatch",
            Rejection::OperandUnjustified { .. } => "operand_unjustified",
            Rejection::ConclusionMismatch { .. } => "conclusion_mismatch",
            Rejection::ClaimMismatch { .. } => "claim_mismatch",
            Rejection::Decode { .. } => "decode",
            Rejection::NonCanonical { .. } => "non_canonical",
            Rejection::FunctionNameMismatch { .. } => "function_name_mismatch",
            Rejection::IllTypedTerm { .. } => "ill_typed_term",
            Rejection::UnknownLeaf { .. } => "unknown_leaf",
            Rejection::MaybePoisonLeaf { .. } => "maybe_poison_leaf",
            Rejection::UnknownRule { .. } => "unknown_rule",
            Rejection::DigestMismatch { .. } => "digest_mismatch",
            Rejection::TypeNotInDomain { .. } => "type_not_in_domain",
            Rejection::BindingMismatch { .. } => "binding_mismatch",
            Rejection::PremiseMismatch { .. } => "premise_mismatch",
            Rejection::SideConditionFailed { .. } => "side_condition_failed",
            Rejection::SymOfRefines { .. } => "sym_of_refines",
            Rejection::TransMiddleMismatch { .. } => "trans_middle_mismatch",
            Rejection::CongrMismatch { .. } => "congr_mismatch",
            Rejection::ImplementMismatch { .. } => "implement_mismatch",
            Rejection::LiteralIntroduced { .. } => "literal_introduced",
            Rejection::TagProvenanceChanged { .. } => "tag_provenance_changed",
            Rejection::RefinementPredicates { .. } => "refinement_predicates",
        }
    }
}

impl fmt::Display for Rejection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: ", self.class())?;
        match self {
            Rejection::Ineligible {
                body,
                class,
                detail,
            } => write!(f, "{body} function is ineligible ({class}): {detail}"),
            Rejection::FunctionFieldMismatch { field } => {
                write!(f, "input and output functions differ in field `{field}`")
            }
            Rejection::MalformedBody {
                body,
                block,
                inst,
                detail,
            } => {
                write!(f, "{body} body")?;
                if let Some(b) = block {
                    write!(f, " bb{b}")?;
                }
                if let Some(i) = inst {
                    write!(f, " instruction {i}")?;
                }
                write!(f, ": {detail}")
            }
            Rejection::BlockShapeMismatch {
                block_index,
                detail,
            } => write!(f, "block at index {block_index}: {detail}"),
            Rejection::DuplicateDefinition { body, value } => {
                write!(f, "{body} body defines %{value} more than once")
            }
            Rejection::NotDominated {
                body,
                block,
                inst,
                value,
                detail,
            } => write!(
                f,
                "{body} body bb{block} instruction {inst}: use of %{value} not dominated by its definition ({detail})"
            ),
            Rejection::SkeletonCountMismatch {
                block,
                input,
                output,
            } => write!(
                f,
                "bb{block}: input has {input} skeleton instruction(s), output has {output}"
            ),
            Rejection::SkeletonInstructionMismatch {
                block,
                ordinal,
                input_inst,
                output_inst,
                detail,
            } => write!(
                f,
                "bb{block} skeleton #{ordinal} (input instruction {input_inst}, output instruction {output_inst}): {detail}"
            ),
            Rejection::OperandUnjustified {
                block,
                ordinal,
                operand,
                input_term,
                output_term,
            } => write!(
                f,
                "bb{block} skeleton #{ordinal} operand {operand}: input term {input_term} and output term {output_term} differ and no claim concludes them"
            ),
            Rejection::ConclusionMismatch {
                block,
                ordinal,
                operand,
                claim,
                expected,
                concluded,
            } => write!(
                f,
                "bb{block} skeleton #{ordinal} operand {operand}: claim {claim} concludes {concluded}, the output operand's term is {expected}"
            ),
            Rejection::ClaimMismatch {
                claim,
                proof,
                detail,
            } => write!(f, "claim {claim} (proof {proof}): {detail}"),
            Rejection::Decode { offset, detail } => write!(f, "at byte {offset}: {detail}"),
            Rejection::NonCanonical { kind, index } => {
                write!(f, "{} at entry {index}", kind.as_str())
            }
            Rejection::FunctionNameMismatch {
                derivation,
                function,
            } => write!(
                f,
                "derivation names function {derivation:?}, the function is {function:?}"
            ),
            Rejection::IllTypedTerm { site, detail } => write!(f, "{site}: {detail}"),
            Rejection::UnknownLeaf { site, leaf } => {
                write!(f, "{site}: leaf {leaf} does not exist in the input body")
            }
            Rejection::MaybePoisonLeaf { site, leaf } => write!(
                f,
                "{site}: leaf {leaf} may be poison and is used under an operator or bound to a rule variable"
            ),
            Rejection::UnknownRule { index, name } => {
                write!(
                    f,
                    "rule-table entry {index} names {name:?}, which the registry does not hold"
                )
            }
            Rejection::DigestMismatch { index, name } => write!(
                f,
                "rule-table entry {index} ({name}) carries a statement digest other than the registry's"
            ),
            Rejection::TypeNotInDomain { proof, rule, ty } => write!(
                f,
                "proof {proof}: rule {rule} used at {ty}, which is not in its domain here"
            ),
            Rejection::BindingMismatch {
                proof,
                rule,
                detail,
            } => write!(f, "proof {proof}: rule {rule}: {detail}"),
            Rejection::PremiseMismatch {
                proof,
                rule,
                expected,
                found,
            } => write!(
                f,
                "proof {proof}: rule {rule} has {expected} side condition(s); premises {found:?} are not 0..{expected}"
            ),
            Rejection::SideConditionFailed {
                proof,
                rule,
                condition,
            } => write!(
                f,
                "proof {proof}: rule {rule}: side condition {condition} does not hold"
            ),
            Rejection::SymOfRefines { proof } => {
                write!(f, "proof {proof}: Sym of a refines conclusion")
            }
            Rejection::TransMiddleMismatch {
                proof,
                left_rhs,
                right_lhs,
            } => write!(
                f,
                "proof {proof}: Trans middle terms differ ({left_rhs} vs {right_lhs})"
            ),
            Rejection::CongrMismatch { proof, detail }
            | Rejection::ImplementMismatch { proof, detail } => {
                write!(f, "proof {proof}: {detail}")
            }
            Rejection::LiteralIntroduced {
                block,
                ordinal,
                operand,
                detail,
            } => write!(
                f,
                "bb{block} skeleton #{ordinal} operand {operand}: a literal-sensitive operand is a `Const` the input did not have there ({detail})"
            ),
            Rejection::TagProvenanceChanged {
                block,
                ordinal,
                detail,
            } => write!(
                f,
                "bb{block} skeleton #{ordinal}: the switch selector's enum-tag provenance changed ({detail})"
            ),
            Rejection::RefinementPredicates { predicates } => write!(
                f,
                "the module carries {predicates} refinement predicate(s); refinement consumption is decided by fact propagation over graph instructions, which the checker does not model"
            ),
        }
    }
}

impl std::error::Error for Rejection {}
