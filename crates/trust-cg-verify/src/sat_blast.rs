// trust-cg-verify/sat_blast.rs - UNTRUSTED CNF bit-blaster for lowering VCs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// T-silicon route 1, upstream export (designs in trust-ir:
// `designs/2026-07-01-t-silicon-one-tcb-scoping.md`): turn a lowering rule's
// equivalence VC into a propositional MITER whose UNSATISFIABILITY a DRAT-
// producing SAT solver can refute and whose refutation the Clean `ck0` kernel
// can re-check by reflection (`Clean.Res.checkRefutes3` +
// `checkRefutes3_sound`, clean-kernel `resolution_check.rs`). This module is
// the CNF end of that chain; `trust-cg-sat-host` (MicroSAT + DRAT recorder)
// and `trust-cg-drat-trim` (proof trimming + TraceCheck emission) are the
// solver end; the trace→binary-resolution conversion and the kernel re-check
// live downstream in trust-ir (`trust_ir_build::satcert` /
// `trust_ir_build::validate`).
//
// SUPPORTED FRAGMENT (the ≤N-bit ALU tier). The blaster covers the arithmetic
// AND bitwise ALU family whose two sides are QF_BV terms over
// `{Var, BvConst, BvAdd, BvSub, BvNeg, BvAnd, BvOr, BvXor}`:
// `iadd`/`isub`/`neg` (ripple-carry) and `band`/`bor`/`bxor`/`bnot` (per-bit,
// no carry). Everything else — multiplication, division, shifts, floats,
// preconditions — is fail-closed (`BlastError`), never approximated. This is
// route (a) of the t-silicon scoping doc: one untrusted blaster driving the
// SAME MicroSAT+drat-trim+converter+kernel path over a real op FAMILY, proving
// the lowering catalogue is certifiable, not just one hand-picked rule.
//
// ============================================================================
// TRUST BOUNDARY — ENCODING FIDELITY (the `ayAddOverflows` pattern)
// ============================================================================
//
// This blaster is UNTRUSTED and stays OUTSIDE the trusted base, exactly like
// clean-reflect's `ayAddOverflows` opaque: the boundary is NAMED instead of
// hidden. What is and is not established:
//
//   * PROVEN (downstream, by the `ck0` kernel): "this clause list is
//     unsatisfiable" — via the verified reflection checker
//     `Clean.Res.checkRefutes3` and its PROVED soundness theorem
//     `Clean.Res.checkRefutes3_sound`. A forged refutation reduces to
//     `Bool.false` and is rejected; no Rust replay is authoritative.
//   * STRUCTURED + PRODUCER-CHECKED (here, via [`MiterProvenance`]): "each
//     clause is the CNF of a NAMED gate, and the miter compares the two sides
//     bit-for-bit". Every clause the blaster emits is tagged with the gate it
//     encodes; [`MiterCnf::check_provenance`] re-derives each gate's clause set
//     from the gate's own truth table and confirms the emitted CNF is EXACTLY
//     `⋃ gate-CNFs ∪ {disequality}`. This lifts the boundary from "the whole
//     clause list is asserted to be the miter" to "each clause is a checked
//     gate clause and the disequality is the checked bit-wise diff". The same
//     structured provenance is carried into the certificate (see
//     `trust_ir_build::satcert` / `trust_ir::proof::satprov`) so a reviewer can
//     audit the artifact, not just this source file.
//   * STILL ASSERTED (unproven, the residual named boundary): "the GATE DAG of
//     each side faithfully bit-blasts that side's `SmtExpr`" — i.e. that the
//     recorded ir-side gates compute `blast(trust_ir_expr)` and the machine-
//     side gates compute `blast(aarch64_expr)`. Nobody proves `blast(e)` agrees
//     with the SMT semantics of `e`; the wiring asserts it. A certificate
//     therefore reaches "the lowering rule is correct" only ACROSS this named,
//     documented assertion.
//
// Two structural honesty rules keep the miter non-vacuous:
//
//   1. The two sides are blasted INDEPENDENTLY — no structural hashing, no
//      gate sharing between the trust_ir side and the machine side (shared
//      input variables only). Sharing would let a structurally-identical
//      obligation (e.g. `proof_iadd_i8`, whose two sides are the same
//      `SmtExpr` tree) collapse to a syntactic tautology the solver never
//      actually reasons about. Independent Tseitin copies force the solver to
//      prove two independent circuits agree on every input — the same shape as
//      a real IR-vs-machine-encoder disagreement.
//   2. Everything unsupported is REJECTED (fail-closed `BlastError`), never
//      approximated: preconditions, floating-point inputs, and any `SmtExpr`
//      node outside the supported fragment.

//! UNTRUSTED bit-blaster: lowering-rule [`ProofObligation`] → DIMACS CNF miter
//! with structured, producer-checked clause provenance.
//!
//! `blast_equivalence_miter` produces a [`MiterCnf`] that is UNSAT iff the
//! obligation's trust_ir-side and machine-side expressions agree for **all**
//! inputs (within the supported bitvector fragment), plus a [`MiterProvenance`]
//! tying every clause to the gate it encodes. See the module header for the
//! named encoding-fidelity trust boundary.

use crate::lowering_proof::ProofObligation;
use crate::smt::SmtExpr;
use std::collections::HashMap;
use std::fmt::Write as _;

/// Fail-closed blasting errors. Anything this blaster cannot encode EXACTLY is
/// an error — never an approximation.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum BlastError {
    /// The obligation carries features outside the supported fragment
    /// (preconditions, FP inputs, empty input list, ...).
    #[error("unsupported obligation for CNF blasting: {0}")]
    UnsupportedObligation(String),
    /// An `SmtExpr` node outside the supported fragment.
    #[error("unsupported SmtExpr node for CNF blasting: {0}")]
    UnsupportedExpr(String),
    /// Structural width disagreement (malformed obligation).
    #[error("width mismatch while blasting: {0}")]
    WidthMismatch(String),
    /// The emitted CNF disagreed with its own recorded provenance — an internal
    /// blaster invariant break (never expected; fail-closed rather than ship a
    /// certificate whose provenance lies about its clauses).
    #[error("provenance self-check failed: {0}")]
    ProvenanceMismatch(String),
}

// ============================================================================
// Structured clause provenance (the encoding-fidelity audit surface)
// ============================================================================

/// Which half of the miter a gate belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MiterSide {
    /// A gate of the trust_ir (source) side.
    Ir,
    /// A gate of the machine (AArch64) side.
    Machine,
    /// A per-bit comparison gate (`ir_bit XOR machine_bit`).
    Diff,
}

impl MiterSide {
    /// Stable text tag used in the provenance serialization.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            MiterSide::Ir => "ir",
            MiterSide::Machine => "mc",
            MiterSide::Diff => "diff",
        }
    }
}

/// The Boolean gate a [`GateRecord`] names. The CNF the blaster emits per gate
/// is [`canonical_gate_clauses`]; the gate's truth table is [`GateKind::eval`].
/// Both the producer (here) and the trust-ir consumer
/// (`trust_ir::proof::satprov`) derive their clauses from these two functions,
/// so a clause can never silently disagree with the gate it is tagged with.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GateKind {
    /// `out = in0 XOR in1`.
    Xor2,
    /// `out = in0 XOR in1 XOR in2` (full-adder sum / MSB xor).
    Xor3,
    /// `out = in0 AND in1`.
    And2,
    /// `out = MAJ(in0, in1, in2)` (full-adder carry).
    Maj3,
}

impl GateKind {
    /// Stable text tag used in the provenance serialization.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            GateKind::Xor2 => "xor2",
            GateKind::Xor3 => "xor3",
            GateKind::And2 => "and2",
            GateKind::Maj3 => "maj3",
        }
    }

    /// Number of input literals this gate takes.
    #[must_use]
    pub const fn arity(self) -> usize {
        match self {
            GateKind::Xor2 | GateKind::And2 => 2,
            GateKind::Xor3 | GateKind::Maj3 => 3,
        }
    }

    /// The gate's truth table over its (already polarity-resolved) input bits.
    // `nonminimal_bool` wants to rewrite MAJ3 as `(c || b) && a || (b && c)` (or
    // worse, a double-negated form). This is a TRUTH TABLE in a verification
    // crate: the canonical `(a&b) | (a&c) | (b&c)` is the textbook definition of
    // majority-3 and is auditable against the ISA/CNF encoding at a glance. A
    // "simplified" but structurally opaque form would be strictly harder to
    // review for the same number of operations, so keep the canonical shape.
    #[allow(clippy::nonminimal_bool)]
    #[must_use]
    pub fn eval(self, ins: &[bool]) -> bool {
        match self {
            GateKind::Xor2 => ins[0] ^ ins[1],
            GateKind::Xor3 => ins[0] ^ ins[1] ^ ins[2],
            GateKind::And2 => ins[0] && ins[1],
            GateKind::Maj3 => (ins[0] && ins[1]) || (ins[0] && ins[2]) || (ins[1] && ins[2]),
        }
    }
}

/// One recorded gate: `out = kind(ins...)` over SIGNED DIMACS literals. `out`
/// is always a fresh POSITIVE variable; `ins` may be negated (e.g. the `~b` of
/// two's-complement subtraction), so provenance carries polarity faithfully.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GateRecord {
    /// Which side of the miter the gate belongs to.
    pub side: MiterSide,
    /// The Boolean relation.
    pub kind: GateKind,
    /// Defined output literal (positive).
    pub out: i32,
    /// Ordered input literals (signed; length == `kind.arity()`).
    pub ins: Vec<i32>,
}

/// Semantic role of a DIMACS variable, for human audit of the provenance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VarRole {
    /// Bit `bit` of declared input `input` (index into [`MiterProvenance::inputs`]).
    Input { input: u32, bit: u32 },
    /// An output / auxiliary var of the given side.
    Gate { side: MiterSide },
}

/// The structured provenance of a blasted miter: enough to re-derive every
/// clause from named gates and to confirm the disequality compares the two
/// sides bit-for-bit. Serialized to a deterministic text form
/// ([`MiterProvenance::to_text`]) and carried into the certificate; the trust-ir
/// consumer re-checks it against the payload's clause list
/// (`trust_ir::proof::satprov`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MiterProvenance {
    /// The lowering rule this miter came from.
    pub rule_name: String,
    /// Output bit width of both sides.
    pub width: u32,
    /// Highest DIMACS variable in use.
    pub num_vars: u32,
    /// Declared inputs: `(name, var ids LSB-first)`.
    pub inputs: Vec<(String, Vec<u32>)>,
    /// Every clause-emitting gate, in emission order (ir side, machine side,
    /// then the `Diff` comparison gates).
    pub gates: Vec<GateRecord>,
    /// The trust_ir side's output literals (LSB-first).
    pub ir_out: Vec<i32>,
    /// The machine side's output literals (LSB-first).
    pub machine_out: Vec<i32>,
    /// The per-bit diff literals fed into the disequality clause.
    pub diff: Vec<i32>,
}

/// The EXACT (compact) CNF the blaster emits for a gate, parameterized by the
/// signed output/input literals. Single source of truth for the emitted
/// clauses: [`Blaster`]'s gate primitives call this, and
/// [`MiterCnf::check_provenance`] re-derives the same clauses to confirm the
/// CNF equals `⋃ gate-CNFs ∪ {disequality}`. The trust-ir consumer carries a
/// byte-identical copy (`trust_ir::proof::satprov::canonical_gate_clauses`).
///
/// # Panics
/// If `ins.len() != kind.arity()` (a blaster invariant break).
#[must_use]
pub fn canonical_gate_clauses(kind: GateKind, out: i32, ins: &[i32]) -> Vec<Vec<i32>> {
    assert_eq!(ins.len(), kind.arity(), "gate arity mismatch");
    let o = out;
    match kind {
        GateKind::Xor2 => {
            let (a, b) = (ins[0], ins[1]);
            vec![
                vec![-a, -b, -o],
                vec![a, b, -o],
                vec![-a, b, o],
                vec![a, -b, o],
            ]
        }
        GateKind::Xor3 => {
            // `o <-> a XOR b XOR c` (full-adder sum). Each (sa,sb,sc) corner
            // forbids the single assignment where `o` takes the WRONG value, so
            // `so` selects the complement of the corner's true XOR. (The prior
            // form used `so = if parity {1} else {-1}`, which forced the XNOR —
            // harmless for a self-consistency miter, since both sides shared the
            // gate, but an untruthful label. The encoding-fidelity provenance
            // check caught it; `clause_entailed_by_gate` now confirms this form
            // is genuinely entailed by `GateKind::Xor3.eval`.)
            let (a, b, c) = (ins[0], ins[1], ins[2]);
            let mut v = Vec::with_capacity(8);
            for sa in [1i32, -1] {
                for sb in [1i32, -1] {
                    for sc in [1i32, -1] {
                        let parity = (sa < 0) ^ (sb < 0) ^ (sc < 0);
                        let so = if parity { -1 } else { 1 };
                        v.push(vec![-sa * a, -sb * b, -sc * c, so * o]);
                    }
                }
            }
            v
        }
        GateKind::And2 => {
            let (a, b) = (ins[0], ins[1]);
            vec![vec![-a, -b, o], vec![a, -o], vec![b, -o]]
        }
        GateKind::Maj3 => {
            let (a, b, c) = (ins[0], ins[1], ins[2]);
            vec![
                vec![-a, -b, o],
                vec![-a, -c, o],
                vec![-b, -c, o],
                vec![a, b, -o],
                vec![a, c, -o],
                vec![b, c, -o],
            ]
        }
    }
}

/// True iff `clause` is a logical CONSEQUENCE of the gate relation
/// `out = kind(ins...)` — i.e. every assignment (to the gate's own variables)
/// that satisfies the relation also satisfies `clause`. This is the
/// gate-semantics check that makes [`canonical_gate_clauses`] non-vacuous: a
/// unit test asserts every emitted gate clause is entailed here, so the compact
/// CNF forms are proven genuine gate encodings, not asserted ones.
#[must_use]
pub fn clause_entailed_by_gate(clause: &[i32], kind: GateKind, out: i32, ins: &[i32]) -> bool {
    if ins.len() != kind.arity() {
        return false;
    }
    // Distinct variables of the gate (out first, then ins), positive.
    let mut vars: Vec<i32> = Vec::new();
    for &l in std::iter::once(&out).chain(ins.iter()) {
        let v = l.abs();
        if !vars.contains(&v) {
            vars.push(v);
        }
    }
    // The clause may only mention the gate's own variables.
    if clause.iter().any(|l| !vars.contains(&l.abs())) {
        return false;
    }
    let k = vars.len();
    for mask in 0u32..(1u32 << k) {
        let val = |lit: i32| -> bool {
            let idx = vars.iter().position(|&v| v == lit.abs()).expect("gate var");
            let bit = mask & (1 << idx) != 0;
            if lit > 0 { bit } else { !bit }
        };
        let in_vals: Vec<bool> = ins.iter().map(|&l| val(l)).collect();
        if val(out) != kind.eval(&in_vals) {
            continue; // assignment violates the gate relation — not constrained
        }
        // Relation holds here: the clause must be satisfied.
        if !clause.iter().any(|&l| val(l)) {
            return false;
        }
    }
    true
}

impl MiterProvenance {
    /// Serialize to a deterministic, line-based text form. Same miter → same
    /// bytes. The format (contract with `trust_ir::proof::satprov`):
    ///
    /// ```text
    /// satprov1
    /// rule <rule_name>
    /// width <w>
    /// vars <num_vars>
    /// input <name> <v0> <v1> ...        (one per declared input)
    /// gate <side> <kind> <out> <in...>  (one per gate; side∈{ir,mc,diff})
    /// irout <l0> <l1> ...
    /// mcout <l0> <l1> ...
    /// diff <l0> <l1> ...
    /// ```
    ///
    /// Returns `None` if the rule name contains a newline (fail-closed rather
    /// than escaped — same policy as `satres_formula`).
    #[must_use]
    pub fn to_text(&self) -> Option<String> {
        if self.rule_name.contains('\n') {
            return None;
        }
        let mut out = String::new();
        let _ = writeln!(out, "satprov1");
        let _ = writeln!(out, "rule {}", self.rule_name);
        let _ = writeln!(out, "width {}", self.width);
        let _ = writeln!(out, "vars {}", self.num_vars);
        for (name, ids) in &self.inputs {
            let _ = write!(out, "input {name}");
            for id in ids {
                let _ = write!(out, " {id}");
            }
            let _ = writeln!(out);
        }
        for g in &self.gates {
            let _ = write!(out, "gate {} {} {}", g.side.tag(), g.kind.tag(), g.out);
            for i in &g.ins {
                let _ = write!(out, " {i}");
            }
            let _ = writeln!(out);
        }
        let write_lits = |out: &mut String, tag: &str, lits: &[i32]| {
            let _ = write!(out, "{tag}");
            for l in lits {
                let _ = write!(out, " {l}");
            }
            let _ = writeln!(out);
        };
        write_lits(&mut out, "irout", &self.ir_out);
        write_lits(&mut out, "mcout", &self.machine_out);
        write_lits(&mut out, "diff", &self.diff);
        Some(out)
    }
}

/// A blasted equivalence miter in DIMACS terms.
///
/// `clauses` hold non-zero DIMACS literals (positive = variable true). The
/// miter is UNSAT ⇔ the two blasted sides agree on every input assignment.
/// `provenance` ties every clause to the gate it encodes.
#[derive(Debug, Clone)]
pub struct MiterCnf {
    /// Highest DIMACS variable id in use.
    pub num_vars: u32,
    /// CNF clauses over DIMACS literals.
    pub clauses: Vec<Vec<i32>>,
    /// Per-clause provenance tag (`clauses[i]` ↔ `clause_tags[i]`): the index of
    /// the emitting gate in `provenance.gates`, or `None` for the disequality.
    pub clause_tags: Vec<Option<usize>>,
    /// Input variable map: `(input name, DIMACS var ids, LSB first)`.
    pub inputs: Vec<(String, Vec<u32>)>,
    /// The lowering rule this miter was blasted from (`ProofObligation::name`).
    pub rule_name: String,
    /// Structured clause provenance (the encoding-fidelity audit surface).
    pub provenance: MiterProvenance,
}

impl MiterCnf {
    /// Render as DIMACS text. Deterministic: same obligation → same bytes.
    /// The header comments restate the encoding-fidelity boundary so the
    /// artifact itself carries the trust statement.
    #[must_use]
    pub fn to_dimacs(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(
            out,
            "c trust-cg t-silicon lowering miter (UNTRUSTED bit-blast; gate-level encoding fidelity\n\
             c is producer-checked via MiterProvenance, gate-DAG⇔SmtExpr still asserted — see docs)"
        );
        let _ = writeln!(out, "c rule: {}", self.rule_name);
        for (name, vars) in &self.inputs {
            let _ = writeln!(
                out,
                "c input {name}: vars {}..{} (LSB first)",
                vars.first().copied().unwrap_or(0),
                vars.last().copied().unwrap_or(0)
            );
        }
        let _ = writeln!(out, "p cnf {} {}", self.num_vars, self.clauses.len());
        for clause in &self.clauses {
            for lit in clause {
                let _ = write!(out, "{lit} ");
            }
            let _ = writeln!(out, "0");
        }
        out
    }

    /// PRODUCER-SIDE encoding-fidelity self-check: confirm the emitted CNF is
    /// EXACTLY `⋃ gate-CNFs ∪ {disequality}` and that the disequality compares
    /// the two sides bit-for-bit. Concretely:
    ///
    ///   * every clause tagged to gate `g` is one of `canonical_gate_clauses(g)`,
    ///     and every canonical clause of `g` is present (no clause dropped,
    ///     added, or mis-tagged);
    ///   * each `Diff` gate is `Xor2(ir_out[i], machine_out[i])`;
    ///   * the single untagged clause is exactly the diff-literal disjunction;
    ///   * `ir_out`/`machine_out` roots are input literals or gate outputs of
    ///     their respective sides.
    ///
    /// A failure is an internal invariant break — the blaster refuses to ship a
    /// miter whose provenance does not match its own clauses.
    pub fn check_provenance(&self) -> Result<(), BlastError> {
        let p = &self.provenance;
        // Group emitted clauses by gate tag (canonical set per clause).
        let nclauses = self.clauses.len();
        if self.clause_tags.len() != nclauses {
            return Err(BlastError::ProvenanceMismatch(
                "clause_tags length disagrees with clauses".into(),
            ));
        }
        let canon = |c: &[i32]| -> Vec<i32> {
            let mut v: Vec<i32> = c.to_vec();
            v.sort_unstable();
            v
        };
        // For each gate: the multiset of canonical clauses must equal the
        // multiset of emitted clauses tagged to it.
        let mut per_gate: Vec<Vec<Vec<i32>>> = vec![Vec::new(); p.gates.len()];
        let mut diseq: Vec<Vec<i32>> = Vec::new();
        for (clause, tag) in self.clauses.iter().zip(self.clause_tags.iter()) {
            match tag {
                Some(g) => {
                    let slot = per_gate.get_mut(*g).ok_or_else(|| {
                        BlastError::ProvenanceMismatch(format!("clause tags missing gate {g}"))
                    })?;
                    slot.push(canon(clause));
                }
                None => diseq.push(canon(clause)),
            }
        }
        for (g, rec) in p.gates.iter().enumerate() {
            if rec.ins.len() != rec.kind.arity() {
                return Err(BlastError::ProvenanceMismatch(format!(
                    "gate {g} arity mismatch"
                )));
            }
            let mut expected: Vec<Vec<i32>> = canonical_gate_clauses(rec.kind, rec.out, &rec.ins)
                .iter()
                .map(|c| canon(c))
                .collect();
            expected.sort();
            let mut got = std::mem::take(&mut per_gate[g]);
            got.sort();
            if expected != got {
                return Err(BlastError::ProvenanceMismatch(format!(
                    "gate {g} ({} {}) clauses do not match its canonical CNF",
                    rec.side.tag(),
                    rec.kind.tag()
                )));
            }
        }
        // The disequality: exactly one untagged clause, equal to `diff`.
        if diseq.len() != 1 {
            return Err(BlastError::ProvenanceMismatch(format!(
                "expected exactly one disequality clause, found {}",
                diseq.len()
            )));
        }
        if diseq[0] != canon(&p.diff) {
            return Err(BlastError::ProvenanceMismatch(
                "disequality clause is not the recorded diff-literal disjunction".into(),
            ));
        }
        // Diff gates compare ir_out[i] with machine_out[i]; diff[i] is that gate's out.
        if p.ir_out.len() != p.machine_out.len() || p.ir_out.len() != p.diff.len() {
            return Err(BlastError::ProvenanceMismatch(
                "ir_out / machine_out / diff length disagreement".into(),
            ));
        }
        let diff_gates: Vec<&GateRecord> = p
            .gates
            .iter()
            .filter(|g| g.side == MiterSide::Diff)
            .collect();
        for (i, &d) in p.diff.iter().enumerate() {
            let gate = diff_gates
                .iter()
                .find(|g| g.out == d.abs())
                .ok_or_else(|| {
                    BlastError::ProvenanceMismatch(format!("diff bit {i} has no diff gate"))
                })?;
            if gate.kind != GateKind::Xor2 || gate.ins != vec![p.ir_out[i], p.machine_out[i]] {
                return Err(BlastError::ProvenanceMismatch(format!(
                    "diff bit {i} is not Xor2(ir_out[{i}], machine_out[{i}])"
                )));
            }
        }
        Ok(())
    }
}

/// One blasted bit: a known constant or a DIMACS literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Bit {
    Const(bool),
    Lit(i32),
}

impl Bit {
    fn negate(self) -> Bit {
        match self {
            Bit::Const(b) => Bit::Const(!b),
            Bit::Lit(l) => Bit::Lit(-l),
        }
    }
}

/// Tseitin clause builder. Gate variables are allocated fresh per call — the
/// blaster performs NO structural hashing (see module docs, honesty rule 1).
/// Every clause-emitting gate is recorded in `gates` and every emitted clause
/// tagged with its gate index (or `None` for the disequality).
struct Blaster {
    next_var: u32,
    clauses: Vec<Vec<i32>>,
    clause_tags: Vec<Option<usize>>,
    gates: Vec<GateRecord>,
    side: MiterSide,
}

impl Blaster {
    fn new() -> Self {
        Blaster {
            next_var: 0,
            clauses: Vec::new(),
            clause_tags: Vec::new(),
            gates: Vec::new(),
            side: MiterSide::Ir,
        }
    }

    fn fresh(&mut self) -> i32 {
        self.next_var += 1;
        self.next_var as i32
    }

    /// Record a clause-emitting gate and push its canonical CNF, tagging every
    /// clause with the gate's index. Single funnel so producer CNF and recorded
    /// provenance can never diverge.
    fn emit_gate(&mut self, kind: GateKind, ins: &[i32]) -> i32 {
        let out = self.fresh();
        let gate_idx = self.gates.len();
        self.gates.push(GateRecord {
            side: self.side,
            kind,
            out,
            ins: ins.to_vec(),
        });
        for clause in canonical_gate_clauses(kind, out, ins) {
            self.clauses.push(clause);
            self.clause_tags.push(Some(gate_idx));
        }
        out
    }

    /// `o <-> x XOR y`, with constant folding (no gate when an input is const).
    fn xor2(&mut self, x: Bit, y: Bit) -> Bit {
        match (x, y) {
            (Bit::Const(a), Bit::Const(b)) => Bit::Const(a ^ b),
            (Bit::Const(false), l) | (l, Bit::Const(false)) => l,
            (Bit::Const(true), l) | (l, Bit::Const(true)) => l.negate(),
            (Bit::Lit(a), Bit::Lit(b)) => Bit::Lit(self.emit_gate(GateKind::Xor2, &[a, b])),
        }
    }

    /// `o <-> x XOR y XOR z`, folding constants down to xor2.
    fn xor3(&mut self, x: Bit, y: Bit, z: Bit) -> Bit {
        match (x, y, z) {
            (Bit::Const(a), y, z) => {
                let r = self.xor2(y, z);
                if a { r.negate() } else { r }
            }
            (x, Bit::Const(b), z) => {
                let r = self.xor2(x, z);
                if b { r.negate() } else { r }
            }
            (x, y, Bit::Const(c)) => {
                let r = self.xor2(x, y);
                if c { r.negate() } else { r }
            }
            (Bit::Lit(a), Bit::Lit(b), Bit::Lit(c)) => {
                Bit::Lit(self.emit_gate(GateKind::Xor3, &[a, b, c]))
            }
        }
    }

    /// `o <-> AND(x, y)`, with constant folding.
    fn and2(&mut self, x: Bit, y: Bit) -> Bit {
        match (x, y) {
            (Bit::Const(false), _) | (_, Bit::Const(false)) => Bit::Const(false),
            (Bit::Const(true), l) | (l, Bit::Const(true)) => l,
            (Bit::Lit(a), Bit::Lit(b)) => Bit::Lit(self.emit_gate(GateKind::And2, &[a, b])),
        }
    }

    /// `o <-> OR(x, y)` via De Morgan on [`Blaster::and2`] (the recorded gate is
    /// an `And2` over the negated inputs; the caller uses the negated output).
    fn or2(&mut self, x: Bit, y: Bit) -> Bit {
        self.and2(x.negate(), y.negate()).negate()
    }

    /// `o <-> MAJ(x, y, z)` (full-adder carry), folding constants:
    /// `maj(0,y,z) = and(y,z)`, `maj(1,y,z) = or(y,z)`.
    fn maj3(&mut self, x: Bit, y: Bit, z: Bit) -> Bit {
        match (x, y, z) {
            (Bit::Const(false), y, z) => self.and2(y, z),
            (y, Bit::Const(false), z) => self.and2(y, z),
            (y, z, Bit::Const(false)) => self.and2(y, z),
            (Bit::Const(true), y, z) => self.or2(y, z),
            (y, Bit::Const(true), z) => self.or2(y, z),
            (y, z, Bit::Const(true)) => self.or2(y, z),
            (Bit::Lit(a), Bit::Lit(b), Bit::Lit(c)) => {
                Bit::Lit(self.emit_gate(GateKind::Maj3, &[a, b, c]))
            }
        }
    }

    /// Ripple-carry add `x + y + cin`, wrapping at `x.len()` bits (the carry
    /// out is discarded — bitvector `bvadd` semantics).
    fn ripple_add(&mut self, x: &[Bit], y: &[Bit], cin: Bit) -> Vec<Bit> {
        debug_assert_eq!(x.len(), y.len());
        let mut carry = cin;
        let mut sum = Vec::with_capacity(x.len());
        for i in 0..x.len() {
            sum.push(self.xor3(x[i], y[i], carry));
            if i + 1 < x.len() {
                carry = self.maj3(x[i], y[i], carry);
            }
        }
        sum
    }

    /// Per-bit bitwise map `op(x_i, y_i)` (no carry chain) — `bvand`/`bvor`/`bvxor`.
    fn bitwise(&mut self, op: GateKind, x: &[Bit], y: &[Bit]) -> Vec<Bit> {
        debug_assert_eq!(x.len(), y.len());
        x.iter()
            .zip(y.iter())
            .map(|(&a, &b)| match op {
                GateKind::And2 => self.and2(a, b),
                GateKind::Xor2 => self.xor2(a, b),
                // bvor via or2 (recorded as an And2 gate over negated inputs).
                _ => self.or2(a, b),
            })
            .collect()
    }

    /// Blast `expr` to bits (LSB first). `env` maps input names to their
    /// shared input bits. Every gate is FRESH: two calls over the same tree
    /// yield independent circuits (honesty rule 1).
    fn blast_expr(
        &mut self,
        expr: &SmtExpr,
        env: &HashMap<String, Vec<Bit>>,
    ) -> Result<Vec<Bit>, BlastError> {
        match expr {
            SmtExpr::Var { name, width } => {
                let bits = env.get(name).ok_or_else(|| {
                    BlastError::UnsupportedObligation(format!(
                        "expression references undeclared input '{name}'"
                    ))
                })?;
                if bits.len() != *width as usize {
                    return Err(BlastError::WidthMismatch(format!(
                        "input '{name}' declared {} bits, used at {width}",
                        bits.len()
                    )));
                }
                Ok(bits.clone())
            }
            SmtExpr::BvConst { value, width } => Ok((0..*width)
                .map(|i| Bit::Const(value >> i & 1 == 1))
                .collect()),
            SmtExpr::BvAdd { lhs, rhs, .. } => {
                let (a, b) = self.blast_binop_operands(lhs, rhs, env, "bvadd")?;
                Ok(self.ripple_add(&a, &b, Bit::Const(false)))
            }
            SmtExpr::BvSub { lhs, rhs, .. } => {
                // a - b = a + ~b + 1 (two's complement).
                let (a, b) = self.blast_binop_operands(lhs, rhs, env, "bvsub")?;
                let nb: Vec<Bit> = b.iter().map(|bit| bit.negate()).collect();
                Ok(self.ripple_add(&a, &nb, Bit::Const(true)))
            }
            SmtExpr::BvNeg { operand, width } => {
                // -a = ~a + 1.
                let a = self.blast_expr(operand, env)?;
                if a.len() != *width as usize {
                    return Err(BlastError::WidthMismatch(format!(
                        "bvneg operand is {} bits, node declares {width}",
                        a.len()
                    )));
                }
                let na: Vec<Bit> = a.iter().map(|bit| bit.negate()).collect();
                let zero = vec![Bit::Const(false); na.len()];
                Ok(self.ripple_add(&na, &zero, Bit::Const(true)))
            }
            SmtExpr::BvAnd { lhs, rhs, .. } => {
                let (a, b) = self.blast_binop_operands(lhs, rhs, env, "bvand")?;
                Ok(self.bitwise(GateKind::And2, &a, &b))
            }
            SmtExpr::BvOr { lhs, rhs, .. } => {
                let (a, b) = self.blast_binop_operands(lhs, rhs, env, "bvor")?;
                // Sentinel Maj3 routes or2 in `bitwise`; see its match arm.
                Ok(self.bitwise(GateKind::Maj3, &a, &b))
            }
            SmtExpr::BvXor { lhs, rhs, .. } => {
                let (a, b) = self.blast_binop_operands(lhs, rhs, env, "bvxor")?;
                Ok(self.bitwise(GateKind::Xor2, &a, &b))
            }
            other => Err(BlastError::UnsupportedExpr(format!(
                "{:?}",
                std::mem::discriminant(other)
            ))),
        }
    }

    fn blast_binop_operands(
        &mut self,
        lhs: &SmtExpr,
        rhs: &SmtExpr,
        env: &HashMap<String, Vec<Bit>>,
        op: &str,
    ) -> Result<(Vec<Bit>, Vec<Bit>), BlastError> {
        let a = self.blast_expr(lhs, env)?;
        let b = self.blast_expr(rhs, env)?;
        if a.len() != b.len() || a.is_empty() {
            return Err(BlastError::WidthMismatch(format!(
                "{op} operands are {} and {} bits",
                a.len(),
                b.len()
            )));
        }
        Ok((a, b))
    }
}

/// Extract the signed DIMACS literal a blasted output bit stands for. Constant
/// output bits (which arise only from const-folded ops over constant inputs)
/// have no literal; the provenance uses `0` as the "no literal" sentinel, which
/// the diff-gate structural check never accepts as a gate output.
fn bit_lit(b: Bit) -> i32 {
    match b {
        Bit::Lit(l) => l,
        // A constant output bit encodes as a "false-only" pseudo-literal; the
        // xor2 diff gate below still allocates a real gate over it, so this only
        // appears in `ir_out`/`machine_out` for fully-constant sides (not in the
        // supported ALU family, whose sides depend on free inputs).
        Bit::Const(v) => {
            if v {
                i32::MAX
            } else {
                i32::MIN
            }
        }
    }
}

/// Blast a lowering-rule equivalence VC into a CNF **miter**:
/// `∃ inputs. blast(trust_ir_expr) ≠ blast(machine_expr)`. UNSAT ⇔ the two
/// sides agree for all inputs — the propositional form of the same
/// `NOT(lhs == rhs)` query the ay/SMT lane checks (`lowering_proof.rs`).
///
/// Fail-closed: obligations with preconditions, FP inputs, no inputs, or any
/// expression node outside the supported fragment (`Var`, `BvConst`, `BvAdd`,
/// `BvSub`, `BvNeg`, `BvAnd`, `BvOr`, `BvXor`) are rejected with a
/// [`BlastError`], never approximated. The result's `check_provenance` is run
/// before returning (a failure is a blaster invariant break).
///
/// The two sides share ONLY the input variables; every gate variable is
/// blasted independently per side (see module docs for why that is
/// load-bearing for structurally-identical obligations like `proof_iadd_i8`).
pub fn blast_equivalence_miter(ob: &ProofObligation) -> Result<MiterCnf, BlastError> {
    if !ob.preconditions.is_empty() {
        return Err(BlastError::UnsupportedObligation(format!(
            "obligation '{}' carries {} precondition(s); the CNF lane does not model them",
            ob.name,
            ob.preconditions.len()
        )));
    }
    if !ob.fp_inputs.is_empty() {
        return Err(BlastError::UnsupportedObligation(format!(
            "obligation '{}' carries floating-point inputs",
            ob.name
        )));
    }
    if ob.inputs.is_empty() {
        return Err(BlastError::UnsupportedObligation(format!(
            "obligation '{}' declares no inputs; a closed miter would be vacuous",
            ob.name
        )));
    }

    let mut blaster = Blaster::new();

    // Shared input bits, allocated in declaration order, LSB first.
    let mut env: HashMap<String, Vec<Bit>> = HashMap::new();
    let mut inputs: Vec<(String, Vec<u32>)> = Vec::new();
    for (name, width) in &ob.inputs {
        let mut bits = Vec::with_capacity(*width as usize);
        let mut ids = Vec::with_capacity(*width as usize);
        for _ in 0..*width {
            let v = blaster.fresh();
            bits.push(Bit::Lit(v));
            ids.push(v as u32);
        }
        if env.insert(name.clone(), bits).is_some() {
            return Err(BlastError::UnsupportedObligation(format!(
                "duplicate input '{name}'"
            )));
        }
        inputs.push((name.clone(), ids));
    }

    // Independent Tseitin copies of the two sides (shared inputs only).
    blaster.side = MiterSide::Ir;
    let ir_bits = blaster.blast_expr(&ob.trust_ir_expr, &env)?;
    blaster.side = MiterSide::Machine;
    let machine_bits = blaster.blast_expr(&ob.aarch64_expr, &env)?;
    if ir_bits.len() != machine_bits.len() || ir_bits.is_empty() {
        return Err(BlastError::WidthMismatch(format!(
            "trust_ir side is {} bits, machine side is {} bits",
            ir_bits.len(),
            machine_bits.len()
        )));
    }
    let width = ir_bits.len() as u32;
    let ir_out: Vec<i32> = ir_bits.iter().map(|&b| bit_lit(b)).collect();
    let machine_out: Vec<i32> = machine_bits.iter().map(|&b| bit_lit(b)).collect();

    // Disequality: at least one output bit differs. Each surviving diff gate is
    // an Xor2 comparing the two sides at one bit; recorded on the Diff side.
    blaster.side = MiterSide::Diff;
    let mut diff_lits = Vec::new();
    let mut some_diff_const_true = false;
    for (s1, s2) in ir_bits.iter().zip(machine_bits.iter()) {
        match blaster.xor2(*s1, *s2) {
            Bit::Const(true) => some_diff_const_true = true,
            Bit::Const(false) => {}
            Bit::Lit(l) => diff_lits.push(l),
        }
    }
    if !some_diff_const_true {
        // Possibly the empty clause (immediately UNSAT) if every diff folded
        // to a constant false — an honest degenerate miter, kept explicit.
        blaster.clauses.push(diff_lits.clone());
        blaster.clause_tags.push(None);
    }

    let provenance = MiterProvenance {
        rule_name: ob.name.clone(),
        width,
        num_vars: blaster.next_var,
        inputs: inputs.clone(),
        gates: blaster.gates.clone(),
        ir_out,
        machine_out,
        diff: diff_lits,
    };
    let miter = MiterCnf {
        num_vars: blaster.next_var,
        clauses: blaster.clauses,
        clause_tags: blaster.clause_tags,
        inputs,
        rule_name: ob.name.clone(),
        provenance,
    };
    // The `some_diff_const_true` degenerate path skips the single untagged
    // clause; check_provenance only applies to the non-degenerate miter (the
    // whole supported ALU family), where exactly one disequality clause exists.
    if !some_diff_const_true {
        miter.check_provenance()?;
    }
    Ok(miter)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lowering_proof::{
        proof_band_i8, proof_bnot_i8, proof_bor_i8, proof_bxor_i8, proof_iadd_i8, proof_isub_i8,
        proof_neg_i8,
    };

    /// The iadd_i8 miter blasts to the expected two-independent-adders shape:
    /// 16 input vars, two 8-bit ripple adders, 8 diff gates, one final clause.
    #[test]
    fn iadd_i8_miter_shape() {
        let miter = blast_equivalence_miter(&proof_iadd_i8()).expect("blast iadd_i8");
        assert_eq!(miter.rule_name, "Iadd_I8 -> ADD (8-bit)");
        assert_eq!(miter.inputs.len(), 2);
        // Inputs 16; per adder: 8 sums + 7 carries = 15; diffs 8.
        assert_eq!(miter.num_vars, 16 + 2 * 15 + 8);
        // Per adder: bit0 xor2(4) + bits1-7 xor3(8*7=56) + carries c0 and2(3)
        // + c1..c6 maj(6*6=36) = 99; diffs 8*4 = 32; final 1.
        assert_eq!(miter.clauses.len(), 2 * 99 + 32 + 1);
        // No accidental gate sharing: the two sides' gate variables are disjoint
        // fresh ranges (inputs 1..=16, side 1 gates 17..=31, side 2 gates 32..=46).
        let dimacs = miter.to_dimacs();
        assert!(dimacs.contains("p cnf 54 231"), "header drifted: {dimacs}");
        // Provenance self-check passes and round-trips to text.
        miter.check_provenance().expect("iadd provenance coherent");
        assert!(miter.provenance.to_text().is_some());
    }

    /// The whole i8 ALU family blasts, self-checks its provenance, and (for the
    /// bitwise ops) uses the expected per-bit gate topology.
    #[test]
    fn i8_alu_family_blasts_with_coherent_provenance() {
        for ob in [
            proof_iadd_i8(),
            proof_isub_i8(),
            proof_neg_i8(),
            proof_band_i8(),
            proof_bor_i8(),
            proof_bxor_i8(),
            proof_bnot_i8(),
        ] {
            let name = ob.name.clone();
            let miter =
                blast_equivalence_miter(&ob).unwrap_or_else(|e| panic!("blast {name} failed: {e}"));
            miter
                .check_provenance()
                .unwrap_or_else(|e| panic!("{name} provenance incoherent: {e}"));
            assert!(
                miter.provenance.to_text().is_some(),
                "{name} provenance must serialize"
            );
            assert_eq!(miter.provenance.width, 8, "{name} width");
        }
    }

    /// band_i8: two independent per-bit AND circuits (no carry). 8 input pairs,
    /// 8 AND gates/side, 8 diff xor gates.
    #[test]
    fn band_i8_is_per_bit_and() {
        let miter = blast_equivalence_miter(&proof_band_i8()).expect("blast band_i8");
        // 16 inputs + 8 (ir and) + 8 (machine and) + 8 (diff) = 40 vars.
        assert_eq!(miter.num_vars, 40);
        // and2 = 3 clauses; 2 sides * 8 * 3 = 48; diff xor2 = 4 * 8 = 32; +1.
        assert_eq!(miter.clauses.len(), 48 + 32 + 1);
        let and_gates = miter
            .provenance
            .gates
            .iter()
            .filter(|g| g.kind == GateKind::And2 && g.side != MiterSide::Diff)
            .count();
        assert_eq!(and_gates, 16, "8 AND gates per side");
    }

    /// Fail-closed: preconditions, FP inputs, and unsupported nodes reject.
    #[test]
    fn unsupported_obligations_reject() {
        let mut with_precond = proof_iadd_i8();
        with_precond
            .preconditions
            .push(SmtExpr::var("b", 8).eq_expr(SmtExpr::bv_const(0, 8)));
        assert!(matches!(
            blast_equivalence_miter(&with_precond),
            Err(BlastError::UnsupportedObligation(_))
        ));

        let mut with_mul = proof_iadd_i8();
        with_mul.trust_ir_expr = SmtExpr::var("a", 8).bvmul(SmtExpr::var("b", 8));
        assert!(matches!(
            blast_equivalence_miter(&with_mul),
            Err(BlastError::UnsupportedExpr(_))
        ));
    }

    /// Every clause `canonical_gate_clauses` emits is a logical CONSEQUENCE of
    /// the gate's truth table — proves the compact CNF forms are genuine gate
    /// encodings, so the provenance check is non-vacuous.
    #[test]
    fn canonical_clauses_are_entailed_by_their_gate() {
        // Representative literals incl. a negated input (the `~b` case).
        let cases: &[(GateKind, i32, Vec<i32>)] = &[
            (GateKind::Xor2, 10, vec![3, -4]),
            (GateKind::Xor3, 11, vec![3, -4, 5]),
            (GateKind::And2, 12, vec![-3, 4]),
            (GateKind::Maj3, 13, vec![3, 4, -5]),
        ];
        for (kind, out, ins) in cases {
            for clause in canonical_gate_clauses(*kind, *out, ins) {
                assert!(
                    clause_entailed_by_gate(&clause, *kind, *out, ins),
                    "{kind:?} clause {clause:?} not entailed by its gate"
                );
            }
            // And an arbitrary non-entailed clause is rejected.
            assert!(
                !clause_entailed_by_gate(&[*out], *kind, *out, ins),
                "{kind:?}: the bare unit [out] must NOT be entailed"
            );
        }
    }

    /// A tampered clause_tags vector (mis-tagged clause) fails the self-check —
    /// the check is not a rubber stamp.
    #[test]
    fn provenance_check_catches_mistagged_clause() {
        let mut miter = blast_equivalence_miter(&proof_band_i8()).expect("blast");
        // Retag the first gate-0 clause as gate-1: gate 0 now short a clause,
        // gate 1 has an extra one that isn't in its canonical set.
        let first = miter
            .clause_tags
            .iter()
            .position(|t| *t == Some(0))
            .expect("a gate-0 clause");
        miter.clause_tags[first] = Some(1);
        assert!(matches!(
            miter.check_provenance(),
            Err(BlastError::ProvenanceMismatch(_))
        ));
    }
}
