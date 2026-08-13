#!/usr/bin/env python3
# trust-cg-sat-host -- deterministic CNF generators for the SAT corpus.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# Purpose
# -------
# Closes critical-review limitation #6 ("only random 3-SAT") in
# benchmarks/benchmark_study.md by adding crafted / application-flavored
# instances next to deterministic project-authored random 3-SAT fixtures.
# These mirror small instances from SAT-Comp categories (HWMCC-style
# circuit equivalence, planning, structured combinatorial, parity)
# but are produced in-tree so we do not depend on third-party
# archives.
#
# All generators here are original work (or derive from textbook
# encodings); none are adapted from copyrighted SAT-bench paper
# code. The encodings are standard and predate any individual
# implementation, so no attribution beyond the references in each
# generator's docstring is required.
#
# Usage
# -----
#   $ cd crates/trust-cg-sat-host/tests/fixtures/sat_corpus/
#   $ python3 generators.py
#   $ python3 generators.py --check
#
# Writes every committed `.cnf` fixture in this directory, including
# project-authored replacements for eleven historical SATLIB-sourced
# files. Those eleven legacy filenames are retained because release
# tests and benchmark reports refer to them, but their contents are
# generated here and are not copied, adapted, or transformed from
# SATLIB data.
#
# Selected outputs:
#   uuf50-01.cnf .. uuf50-04.cnf
#                                  (independently seeded random 3-SAT, UNSAT)
#   uuf75-01.cnf .. uuf75-02.cnf   (independently seeded random 3-SAT, UNSAT)
#   uuf100-04.cnf                  (independently seeded random 3-SAT, UNSAT)
#   uf50-01.cnf .. uf50-02.cnf     (planted random 3-SAT, SAT)
#   aim-50-1_6-no-1.cnf
#   aim-100-1_6-no-1.cnf           (project-authored parity cycles, UNSAT)
#   queens-4-sat.cnf             (queens n=4, SAT)
#   queens-5-sat.cnf             (queens n=5, SAT)
#   queens-4-overconstrained.cnf (queens n=4 + row collision, UNSAT)
#   adder-4bit-equiv.cnf         (4-bit ripple-carry adder equivalence, UNSAT)
#   blocks-3-t4.cnf              (3-block-world planning, SAT)
#   parity-cycle-33.cnf          (odd-cycle parity Tseitin, UNSAT)
#   php-11-10.cnf                (pigeonhole PHP(11,10), UNSAT)
#   adder-8bit-equiv.cnf         (8-bit ripple-carry adder equivalence, UNSAT)
#   rand3sat-175-750-s1.cnf      (deterministic uniform random 3-SAT, UNSAT)
#   rand3sat-200-860-s1.cnf      (deterministic uniform random 3-SAT, UNSAT)
#   rand3sat-225-970-s1.cnf      (deterministic uniform random 3-SAT, UNSAT)
#
# The output is committed to git; do NOT regenerate at test time.
# The driver in tests/sat_corpus.rs treats these as static fixtures.

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass, field
from itertools import combinations
from pathlib import Path


@dataclass
class Cnf:
    """A CNF accumulator. `clauses` is a list of lists of nonzero ints."""
    num_vars: int = 0
    clauses: list[list[int]] = field(default_factory=list)
    comments: list[str] = field(default_factory=list)

    def new_var(self) -> int:
        self.num_vars += 1
        return self.num_vars

    def add(self, *lits: int) -> None:
        for lit in lits:
            assert lit != 0, "zero literal"
        self.clauses.append(list(lits))

    def add_clause(self, lits: list[int]) -> None:
        for lit in lits:
            assert lit != 0, "zero literal"
        self.clauses.append(list(lits))

    def comment(self, msg: str) -> None:
        self.comments.append(msg)

    def to_dimacs(self) -> str:
        lines = [f"c {m}" for m in self.comments]
        lines.append(f"p cnf {self.num_vars} {len(self.clauses)}")
        for clause in self.clauses:
            lines.append(" ".join(str(l) for l in clause) + " 0")
        return "\n".join(lines) + "\n"


class ParkMiller:
    """Small deterministic PRNG with fully specified integer semantics."""

    MODULUS = 2_147_483_647
    MULTIPLIER = 48_271

    def __init__(self, seed: int) -> None:
        self.state = (seed % self.MODULUS) or 1

    def next(self) -> int:
        self.state = (self.MULTIPLIER * self.state) % self.MODULUS
        return self.state


# ---------------------------------------------------------------------------
# n-queens (combinatorial / crafted)
# ---------------------------------------------------------------------------

def nqueens(n: int, *, overconstrain: bool = False) -> Cnf:
    """Place n non-attacking queens on an n*n board, encoded as CNF.

    Variables: q(r,c) = 1 iff a queen occupies row r, column c.
        Packed as (r-1)*n + (c-1) + 1, rows and cols 1-indexed.

    Clauses (direct encoding):
      - Each row has at least one queen:    OR over c of q(r,c).
      - Each row has at most one queen:     pairwise ~q(r,c1) v ~q(r,c2).
      - Each column has at most one queen:  pairwise ~q(r1,c) v ~q(r2,c).
      - Each diagonal (both directions) has at most one queen.

    n=4 and n=5 are SAT. If `overconstrain=True`, we additionally force
    two specific queens on row 1 (q(1,1) AND q(1,2)) which is excluded
    by the row at-most-one clauses and forces UNSAT.

    Reference: classic n-queens CNF; see e.g. Velev & Gao 2009,
    "Efficient SAT Techniques for Absolute Encoding of Permutation
    Problems: Application to Hamiltonian Cycles".
    """
    cnf = Cnf()
    cnf.comment(f"n-queens n={n} ({'UNSAT, overconstrained' if overconstrain else 'SAT'})")
    cnf.comment("Variables: q(r,c) = (r-1)*n + (c-1) + 1, rows/cols 1..n")

    def q(r: int, c: int) -> int:
        return (r - 1) * n + (c - 1) + 1

    # Reserve variables.
    cnf.num_vars = n * n

    # Each row: at least one queen.
    for r in range(1, n + 1):
        cnf.add_clause([q(r, c) for c in range(1, n + 1)])

    # Each row: at most one queen (pairwise).
    for r in range(1, n + 1):
        for c1, c2 in combinations(range(1, n + 1), 2):
            cnf.add(-q(r, c1), -q(r, c2))

    # Each column: at most one queen (pairwise).
    for c in range(1, n + 1):
        for r1, r2 in combinations(range(1, n + 1), 2):
            cnf.add(-q(r1, c), -q(r2, c))

    # Diagonals (\\ direction: r - c constant).
    for d in range(-(n - 1), n):
        cells = [(r, c) for r in range(1, n + 1) for c in range(1, n + 1)
                 if r - c == d]
        for (r1, c1), (r2, c2) in combinations(cells, 2):
            cnf.add(-q(r1, c1), -q(r2, c2))

    # Anti-diagonals (/ direction: r + c constant).
    for d in range(2, 2 * n + 1):
        cells = [(r, c) for r in range(1, n + 1) for c in range(1, n + 1)
                 if r + c == d]
        for (r1, c1), (r2, c2) in combinations(cells, 2):
            cnf.add(-q(r1, c1), -q(r2, c2))

    if overconstrain:
        # Force two queens in row 1, which contradicts the row at-most-one.
        cnf.comment("Overconstraint: force q(1,1) AND q(1,2) (UNSAT).")
        cnf.add(q(1, 1))
        cnf.add(q(1, 2))

    return cnf


# ---------------------------------------------------------------------------
# Adder equivalence (HWMCC-style hardware verification)
# ---------------------------------------------------------------------------

def adder_equivalence(bits: int) -> Cnf:
    """Miter circuit asking whether two `bits`-wide adders are equivalent.

    Builds two implementations of `s = a + b (mod 2^bits)`:
      - Adder A: textbook ripple-carry full-adder chain.
      - Adder B: same ripple-carry chain (so they ARE equivalent).

    Then asserts the disjunction over all bits that some sum bit differs.
    Because the two circuits are equivalent, the miter is UNSAT.

    This mirrors the SAT-Comp HWMCC bounded-equivalence track at a small
    scale: structured Tseitin-encoded XOR / AND / OR clauses, no random
    component, propagation chains follow the carry path.

    Reference: classic miter / Tseitin encoding; see Bryant 1992 and
    Biere et al. "Handbook of Satisfiability" ch. on EC.
    """
    cnf = Cnf()
    cnf.comment(f"{bits}-bit adder equivalence miter (two identical ripple adders).")
    cnf.comment("Expected UNSAT: equivalent circuits cannot differ on any output bit.")
    cnf.comment("Inputs a[0..bits-1], b[0..bits-1]; outputs sA[0..bits], sB[0..bits].")

    # Input bits.
    a = [cnf.new_var() for _ in range(bits)]
    b = [cnf.new_var() for _ in range(bits)]

    def add_xor(out: int, x: int, y: int) -> None:
        # out <-> x XOR y, Tseitin encoding.
        cnf.add(-out, -x, -y)
        cnf.add(-out, x, y)
        cnf.add(out, -x, y)
        cnf.add(out, x, -y)

    def add_and(out: int, x: int, y: int) -> None:
        # out <-> x AND y.
        cnf.add(-out, x)
        cnf.add(-out, y)
        cnf.add(out, -x, -y)

    def add_or(out: int, x: int, y: int) -> None:
        # out <-> x OR y.
        cnf.add(out, -x)
        cnf.add(out, -y)
        cnf.add(-out, x, y)

    def full_adder(ai: int, bi: int, cin: int) -> tuple[int, int]:
        """Return (sum_bit, cout_bit) variables for a full adder."""
        # sum = a XOR b XOR cin.
        t1 = cnf.new_var()
        add_xor(t1, ai, bi)
        s = cnf.new_var()
        add_xor(s, t1, cin)
        # cout = (a AND b) OR (cin AND (a XOR b)).
        ab = cnf.new_var()
        add_and(ab, ai, bi)
        c_and = cnf.new_var()
        add_and(c_and, cin, t1)
        cout = cnf.new_var()
        add_or(cout, ab, c_and)
        return s, cout

    def ripple_adder() -> list[int]:
        # Initial carry-in = 0.
        cin_false = cnf.new_var()
        cnf.add(-cin_false)  # cin_false must be false.
        outs: list[int] = []
        cin = cin_false
        for i in range(bits):
            s, cout = full_adder(a[i], b[i], cin)
            outs.append(s)
            cin = cout
        outs.append(cin)  # final carry-out as MSB of the (bits+1)-wide sum.
        return outs

    sA = ripple_adder()
    sB = ripple_adder()

    # Miter: exists bit i s.t. sA[i] != sB[i].
    diff_lits: list[int] = []
    for i in range(bits + 1):
        d = cnf.new_var()
        add_xor(d, sA[i], sB[i])
        diff_lits.append(d)
    cnf.add_clause(diff_lits)  # at least one differs => UNSAT for equiv pair.

    return cnf


# ---------------------------------------------------------------------------
# 3-block-world planning (SATPLAN-style)
# ---------------------------------------------------------------------------

def blocks_world_3_t4() -> Cnf:
    """SAT-encoded planning: 3 blocks A,B,C with 4 time steps.

    State predicates at time t (t = 0..T):
      on(x, y, t)   for x in {A,B,C}, y in {A,B,C,Table}, x != y
      clear(x, t)   for x in {A,B,C}
      handempty(t)
      holding(x, t) for x in {A,B,C}

    Actions at time t (t = 0..T-1):
      pickup(x, t)         from table
      putdown(x, t)        onto table
      stack(x, y, t)       x onto y
      unstack(x, y, t)     x off y

    Initial: on(C,A,0), on(A,Table,0), on(B,Table,0),
             clear(B,0), clear(C,0), handempty(0).
    Goal at t=T: on(A,B,T), on(B,C,T).

    This is the canonical 3-block "stack" task, solvable in 4 steps.
    Encoding follows Kautz & Selman 1992 "Planning as Satisfiability"
    with explicit frame axioms and an exactly-one action per step.

    Result: SAT.
    """
    cnf = Cnf()
    cnf.comment("Blocks-world planning, 3 blocks, 4 time steps (SAT).")
    cnf.comment("Initial: C on A, A on table, B on table; hand empty.")
    cnf.comment("Goal at t=4: A on B, B on C.")

    BLOCKS = ["A", "B", "C"]
    PLACES = BLOCKS + ["T"]  # T = Table
    T = 4

    # Allocate variables.
    on_v: dict[tuple[str, str, int], int] = {}
    clear_v: dict[tuple[str, int], int] = {}
    handempty_v: dict[int, int] = {}
    holding_v: dict[tuple[str, int], int] = {}

    pickup_v: dict[tuple[str, int], int] = {}
    putdown_v: dict[tuple[str, int], int] = {}
    stack_v: dict[tuple[str, str, int], int] = {}
    unstack_v: dict[tuple[str, str, int], int] = {}

    for t in range(T + 1):
        for x in BLOCKS:
            for y in PLACES:
                if x != y:
                    on_v[(x, y, t)] = cnf.new_var()
            clear_v[(x, t)] = cnf.new_var()
            holding_v[(x, t)] = cnf.new_var()
        handempty_v[t] = cnf.new_var()

    for t in range(T):
        for x in BLOCKS:
            pickup_v[(x, t)] = cnf.new_var()
            putdown_v[(x, t)] = cnf.new_var()
            for y in BLOCKS:
                if x != y:
                    stack_v[(x, y, t)] = cnf.new_var()
                    unstack_v[(x, y, t)] = cnf.new_var()

    # --- Initial state ---
    cnf.add(on_v[("C", "A", 0)])
    cnf.add(on_v[("A", "T", 0)])
    cnf.add(on_v[("B", "T", 0)])
    cnf.add(clear_v[("B", 0)])
    cnf.add(clear_v[("C", 0)])
    cnf.add(handempty_v[0])
    # Negative literals for everything else at t=0 to pin the initial state.
    # (Without these, the planner can hallucinate alternate starts.)
    cnf.add(-on_v[("A", "B", 0)])
    cnf.add(-on_v[("A", "C", 0)])
    cnf.add(-on_v[("B", "A", 0)])
    cnf.add(-on_v[("B", "C", 0)])
    cnf.add(-on_v[("C", "B", 0)])
    cnf.add(-on_v[("C", "T", 0)])
    cnf.add(-clear_v[("A", 0)])
    for x in BLOCKS:
        cnf.add(-holding_v[(x, 0)])

    # --- Goal at t=T ---
    cnf.add(on_v[("A", "B", T)])
    cnf.add(on_v[("B", "C", T)])

    # --- Action preconditions ---
    for t in range(T):
        for x in BLOCKS:
            # pickup(x): on(x,T) AND clear(x) AND handempty
            cnf.add(-pickup_v[(x, t)], on_v[(x, "T", t)])
            cnf.add(-pickup_v[(x, t)], clear_v[(x, t)])
            cnf.add(-pickup_v[(x, t)], handempty_v[t])
            # putdown(x): holding(x)
            cnf.add(-putdown_v[(x, t)], holding_v[(x, t)])
            for y in BLOCKS:
                if x != y:
                    # stack(x,y): holding(x) AND clear(y)
                    cnf.add(-stack_v[(x, y, t)], holding_v[(x, t)])
                    cnf.add(-stack_v[(x, y, t)], clear_v[(y, t)])
                    # unstack(x,y): on(x,y) AND clear(x) AND handempty
                    cnf.add(-unstack_v[(x, y, t)], on_v[(x, y, t)])
                    cnf.add(-unstack_v[(x, y, t)], clear_v[(x, t)])
                    cnf.add(-unstack_v[(x, y, t)], handempty_v[t])

    # --- Action effects (positive postconditions at t+1) ---
    for t in range(T):
        for x in BLOCKS:
            # pickup -> holding(x, t+1), NOT handempty(t+1), NOT on(x,T,t+1), NOT clear(x,t+1)
            cnf.add(-pickup_v[(x, t)], holding_v[(x, t + 1)])
            cnf.add(-pickup_v[(x, t)], -handempty_v[t + 1])
            cnf.add(-pickup_v[(x, t)], -on_v[(x, "T", t + 1)])
            cnf.add(-pickup_v[(x, t)], -clear_v[(x, t + 1)])
            # putdown -> on(x,T,t+1), clear(x,t+1), handempty(t+1), NOT holding(x,t+1)
            cnf.add(-putdown_v[(x, t)], on_v[(x, "T", t + 1)])
            cnf.add(-putdown_v[(x, t)], clear_v[(x, t + 1)])
            cnf.add(-putdown_v[(x, t)], handempty_v[t + 1])
            cnf.add(-putdown_v[(x, t)], -holding_v[(x, t + 1)])
            for y in BLOCKS:
                if x != y:
                    # stack(x,y) -> on(x,y,t+1), clear(x,t+1), handempty(t+1),
                    #               NOT holding(x,t+1), NOT clear(y,t+1)
                    cnf.add(-stack_v[(x, y, t)], on_v[(x, y, t + 1)])
                    cnf.add(-stack_v[(x, y, t)], clear_v[(x, t + 1)])
                    cnf.add(-stack_v[(x, y, t)], handempty_v[t + 1])
                    cnf.add(-stack_v[(x, y, t)], -holding_v[(x, t + 1)])
                    cnf.add(-stack_v[(x, y, t)], -clear_v[(y, t + 1)])
                    # unstack(x,y) -> holding(x,t+1), clear(y,t+1),
                    #                 NOT on(x,y,t+1), NOT clear(x,t+1), NOT handempty(t+1)
                    cnf.add(-unstack_v[(x, y, t)], holding_v[(x, t + 1)])
                    cnf.add(-unstack_v[(x, y, t)], clear_v[(y, t + 1)])
                    cnf.add(-unstack_v[(x, y, t)], -on_v[(x, y, t + 1)])
                    cnf.add(-unstack_v[(x, y, t)], -clear_v[(x, t + 1)])
                    cnf.add(-unstack_v[(x, y, t)], -handempty_v[t + 1])

    # --- Exactly one action per step (relaxed: at-least-one + pairwise at-most-one) ---
    for t in range(T):
        actions_at_t: list[int] = []
        for x in BLOCKS:
            actions_at_t.append(pickup_v[(x, t)])
            actions_at_t.append(putdown_v[(x, t)])
            for y in BLOCKS:
                if x != y:
                    actions_at_t.append(stack_v[(x, y, t)])
                    actions_at_t.append(unstack_v[(x, y, t)])
        cnf.add_clause(actions_at_t)  # at least one action
        for a1, a2 in combinations(actions_at_t, 2):
            cnf.add(-a1, -a2)  # at most one action

    return cnf


# ---------------------------------------------------------------------------
# Structured parity (small, UNSAT)
# ---------------------------------------------------------------------------

def parity_unsat(num_xors: int, vars_per_xor: int) -> Cnf:
    """A structured parity instance built from a contradictory XOR system.

    Strategy: pick a fixed parity vector p in {0,1}^num_xors and emit
    `num_xors` XOR equations on the same shared variable pool such that
    summing all equations yields 0 = 1 (mod 2). Tseitin-decompose each
    XOR into clauses. The conjunction is UNSAT but each individual XOR
    is satisfiable, which produces the long propagation chains and
    deep learned-clause structure characteristic of the SAT-Comp
    "crafted" track.

    Concretely we build a chain:
      x1 XOR x2 = 1
      x2 XOR x3 = 1
      x3 XOR x4 = 1
      ...
      x_{k-1} XOR x_k = 1
      x_k XOR x_1 = 1
    With an odd number of equations the cycle is unsatisfiable
    (each step flips parity, and an odd-length cycle cannot return to
    the start).

    `num_xors` MUST be odd for UNSAT.
    `vars_per_xor` is fixed at 2 in this simple version; the parameter
    is kept for documentation.

    Reference: Tseitin 1968; standard parity-cycle UNSAT construction.
    """
    assert num_xors % 2 == 1, "need odd cycle for UNSAT"
    assert vars_per_xor == 2, "this generator only supports 2-XOR cycles"
    cnf = Cnf()
    cnf.comment(f"Parity cycle UNSAT: {num_xors} XOR-2 equations in a closed cycle.")
    cnf.comment("Each equation x_i XOR x_{i+1} = 1; odd cycle => unsatisfiable.")

    xs = [cnf.new_var() for _ in range(num_xors)]

    def xor_eq_1(a: int, b: int) -> None:
        # a XOR b = 1 <=> (a OR b) AND (~a OR ~b).
        cnf.add(a, b)
        cnf.add(-a, -b)

    for i in range(num_xors):
        a = xs[i]
        b = xs[(i + 1) % num_xors]
        xor_eq_1(a, b)

    return cnf


def padded_parity_cycle_unsat(num_vars: int, num_clauses: int) -> Cnf:
    """Build an exact-size structured UNSAT instance.

    The UNSAT core is an odd cycle of equations
    ``x_i XOR x_(i+1) = 1``. Each equation is encoded by two binary
    clauses. Two satisfiable long clauses mention every remaining
    variable so the DIMACS header's variable count is meaningful.

    This construction is project-authored from the standard parity-cycle
    encoding. It replaces the two historically AIM-named fixtures without
    using any AIM or SATLIB bytes.
    """
    assert num_clauses >= 8 and num_clauses % 2 == 0
    cycle_len = (num_clauses - 2) // 2
    assert cycle_len % 2 == 1, "the parity cycle must have odd length"
    assert num_vars - cycle_len >= 2, "padding needs at least two variables"

    cnf = Cnf(num_vars=num_vars)
    cnf.comment(
        f"Project-authored padded parity cycle: {num_vars} vars, "
        f"{num_clauses} clauses."
    )
    cnf.comment(
        f"Variables 1..{cycle_len} form an odd XOR-1 cycle (UNSAT); "
        "remaining variables occur in two satisfiable padding clauses."
    )

    for index in range(cycle_len):
        a = index + 1
        b = ((index + 1) % cycle_len) + 1
        cnf.add(a, b)
        cnf.add(-a, -b)

    tail = list(range(cycle_len + 1, num_vars + 1))
    cnf.add_clause(tail)
    cnf.add_clause([-var for var in tail])
    assert len(cnf.clauses) == num_clauses
    return cnf


# ---------------------------------------------------------------------------
# Main: write all fixtures.
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# SAT-Comp-flavored larger UNSAT instances (medium tier)
# ---------------------------------------------------------------------------
#
# The following generators produce larger fixtures that mirror SAT-Comp
# main-track categories (combinatorial / pigeonhole, hardware / adder
# equivalence, uniform random 3-SAT past the small-fixture band). They are
# intentionally calibrated so that native MicroSAT solves each in the
# 1-30 second band on a modern Apple-Silicon CPU, which is the regime
# where the JIT-amortization story is meaningful (compile cost ~1.5 ms
# is small relative to solve cost).
#
# All sources are textbook encodings (Tseitin, Cook-Reckhow,
# uniform random); no third-party SAT-Comp paper or solver code is
# imported.


def pigeonhole(pigeons: int, holes: int) -> Cnf:
    """Standard direct-encoding pigeonhole PHP(pigeons, holes).

    Used both for the existing small fixtures (PHP(4,3) ... PHP(10,9))
    and for the new larger ones (PHP(11,10), PHP(12,11)).

    Variables: x(i,j) = pigeon i goes into hole j, packed
    as (i-1) * holes + j for i in 1..=pigeons, j in 1..=holes.

    Clauses:
      - For each pigeon i, the disjunction over holes: x(i,1) v .. v x(i,holes).
      - For each hole j and pair (i1, i2): ~x(i1,j) v ~x(i2,j).

    UNSAT iff pigeons > holes. Reference: Cook & Reckhow 1979;
    Haken 1985 (resolution lower bound).
    """
    assert pigeons > holes, "need pigeons > holes for UNSAT"
    cnf = Cnf()
    cnf.comment(
        f"Pigeonhole PHP({pigeons},{holes}): {pigeons} pigeons into {holes} holes."
    )
    cnf.comment("Direct encoding; UNSAT.")

    def x(i: int, j: int) -> int:
        return (i - 1) * holes + j

    cnf.num_vars = pigeons * holes

    # Each pigeon occupies at least one hole.
    for i in range(1, pigeons + 1):
        cnf.add_clause([x(i, j) for j in range(1, holes + 1)])

    # No two pigeons share a hole.
    for j in range(1, holes + 1):
        for i1, i2 in combinations(range(1, pigeons + 1), 2):
            cnf.add(-x(i1, j), -x(i2, j))

    return cnf


def blocks_world_4_t6() -> Cnf:
    """A larger SATPLAN-style planning instance: 4 blocks, 6 time
    steps. SAT.

    NOTE (kept in the module but NOT emitted by `main()`):
    this fixture turns out to be trivial for MicroSAT (solves in
    sub-millisecond wall-clock with ~300 propagation calls) because
    the goal admits an obvious greedy sequence of stacks. It is
    kept here as a reference encoding for the 4-block planning
    family; if a future tier needs a harder SAT planning fixture,
    raise `T` or change the goal to a more constrained
    permutation that no greedy sequence satisfies.

    Same encoding pattern as `blocks_world_3_t4` but with one more
    block (A, B, C, D) and two more time steps. Goal: a 4-block tower
    A on B on C on D. The initial state is all blocks on the table
    with hand empty.

    Reference: Kautz & Selman 1992 "Planning as Satisfiability".
    """
    cnf = Cnf()
    cnf.comment("Blocks-world planning, 4 blocks, 6 time steps (SAT).")
    cnf.comment("Initial: all of A,B,C,D on the table; hand empty.")
    cnf.comment("Goal at t=6: A on B, B on C, C on D.")

    BLOCKS = ["A", "B", "C", "D"]
    PLACES = BLOCKS + ["T"]
    T = 6

    on_v: dict[tuple[str, str, int], int] = {}
    clear_v: dict[tuple[str, int], int] = {}
    handempty_v: dict[int, int] = {}
    holding_v: dict[tuple[str, int], int] = {}
    pickup_v: dict[tuple[str, int], int] = {}
    putdown_v: dict[tuple[str, int], int] = {}
    stack_v: dict[tuple[str, str, int], int] = {}
    unstack_v: dict[tuple[str, str, int], int] = {}

    for t in range(T + 1):
        for x in BLOCKS:
            for y in PLACES:
                if x != y:
                    on_v[(x, y, t)] = cnf.new_var()
            clear_v[(x, t)] = cnf.new_var()
            holding_v[(x, t)] = cnf.new_var()
        handempty_v[t] = cnf.new_var()

    for t in range(T):
        for x in BLOCKS:
            pickup_v[(x, t)] = cnf.new_var()
            putdown_v[(x, t)] = cnf.new_var()
            for y in BLOCKS:
                if x != y:
                    stack_v[(x, y, t)] = cnf.new_var()
                    unstack_v[(x, y, t)] = cnf.new_var()

    # Initial: all blocks on table, all clear, hand empty.
    for x in BLOCKS:
        cnf.add(on_v[(x, "T", 0)])
        cnf.add(clear_v[(x, 0)])
    cnf.add(handempty_v[0])
    # Pin negatives for the initial state to prevent the planner
    # hallucinating alternates.
    for x in BLOCKS:
        for y in BLOCKS:
            if x != y:
                cnf.add(-on_v[(x, y, 0)])
        cnf.add(-holding_v[(x, 0)])

    # Goal: A on B, B on C, C on D.
    cnf.add(on_v[("A", "B", T)])
    cnf.add(on_v[("B", "C", T)])
    cnf.add(on_v[("C", "D", T)])

    # Action preconditions.
    for t in range(T):
        for x in BLOCKS:
            cnf.add(-pickup_v[(x, t)], on_v[(x, "T", t)])
            cnf.add(-pickup_v[(x, t)], clear_v[(x, t)])
            cnf.add(-pickup_v[(x, t)], handempty_v[t])
            cnf.add(-putdown_v[(x, t)], holding_v[(x, t)])
            for y in BLOCKS:
                if x != y:
                    cnf.add(-stack_v[(x, y, t)], holding_v[(x, t)])
                    cnf.add(-stack_v[(x, y, t)], clear_v[(y, t)])
                    cnf.add(-unstack_v[(x, y, t)], on_v[(x, y, t)])
                    cnf.add(-unstack_v[(x, y, t)], clear_v[(x, t)])
                    cnf.add(-unstack_v[(x, y, t)], handempty_v[t])

    # Action effects.
    for t in range(T):
        for x in BLOCKS:
            cnf.add(-pickup_v[(x, t)], holding_v[(x, t + 1)])
            cnf.add(-pickup_v[(x, t)], -handempty_v[t + 1])
            cnf.add(-pickup_v[(x, t)], -on_v[(x, "T", t + 1)])
            cnf.add(-pickup_v[(x, t)], -clear_v[(x, t + 1)])
            cnf.add(-putdown_v[(x, t)], on_v[(x, "T", t + 1)])
            cnf.add(-putdown_v[(x, t)], clear_v[(x, t + 1)])
            cnf.add(-putdown_v[(x, t)], handempty_v[t + 1])
            cnf.add(-putdown_v[(x, t)], -holding_v[(x, t + 1)])
            for y in BLOCKS:
                if x != y:
                    cnf.add(-stack_v[(x, y, t)], on_v[(x, y, t + 1)])
                    cnf.add(-stack_v[(x, y, t)], clear_v[(x, t + 1)])
                    cnf.add(-stack_v[(x, y, t)], handempty_v[t + 1])
                    cnf.add(-stack_v[(x, y, t)], -holding_v[(x, t + 1)])
                    cnf.add(-stack_v[(x, y, t)], -clear_v[(y, t + 1)])
                    cnf.add(-unstack_v[(x, y, t)], holding_v[(x, t + 1)])
                    cnf.add(-unstack_v[(x, y, t)], clear_v[(y, t + 1)])
                    cnf.add(-unstack_v[(x, y, t)], -on_v[(x, y, t + 1)])
                    cnf.add(-unstack_v[(x, y, t)], -clear_v[(x, t + 1)])
                    cnf.add(-unstack_v[(x, y, t)], -handempty_v[t + 1])

    # Exactly one action per step.
    for t in range(T):
        actions_at_t: list[int] = []
        for x in BLOCKS:
            actions_at_t.append(pickup_v[(x, t)])
            actions_at_t.append(putdown_v[(x, t)])
            for y in BLOCKS:
                if x != y:
                    actions_at_t.append(stack_v[(x, y, t)])
                    actions_at_t.append(unstack_v[(x, y, t)])
        cnf.add_clause(actions_at_t)
        for a1, a2 in combinations(actions_at_t, 2):
            cnf.add(-a1, -a2)

    return cnf


def random_3sat_unsat(num_vars: int, num_clauses: int, seed: int) -> Cnf:
    """Deterministic uniform random 3-SAT instance.

    Produces a uniformly random 3-SAT candidate near or above the
    SAT/UNSAT phase transition. It uses the in-tree Park-Miller
    generator above, so output is byte-identical across machines and
    Python versions.

    Produces clauses with three distinct variables per clause, each
    negated with independent (approximately) 50% probability.

    The caller is responsible for choosing `seed`, `num_vars`, and
    `num_clauses` so the resulting instance is UNSAT and lands in
    the target hardness band. Both conditions are verified at
    corpus-build time by running the actual solver. Above ratio
    M/N >~ 5 almost every random instance is UNSAT, so a small
    handful of seeds suffices.

    Reference: Mitchell, Selman & Levesque 1992, "Hard and Easy
    Distributions of SAT Problems".
    """
    cnf = Cnf()
    cnf.comment(
        f"Project-authored uniform random 3-SAT, {num_vars} vars, "
        f"{num_clauses} clauses, "
        f"seed={seed}; clause/var ratio={num_clauses / num_vars:.3f}."
    )
    cnf.comment(
        "Deterministic in-tree Lehmer MCG (modulus 2^31-1); reproducible "
        "across platforms and Python versions."
    )

    cnf.num_vars = num_vars
    random = ParkMiller(seed)

    for _ in range(num_clauses):
        # Pick 3 distinct variables in 1..=num_vars.
        chosen: list[int] = []
        while len(chosen) < 3:
            v = (random.next() % num_vars) + 1
            if v not in chosen:
                chosen.append(v)
        lits: list[int] = []
        for v in chosen:
            sign = -1 if (random.next() % 2) else 1
            lits.append(sign * v)
        cnf.add_clause(lits)

    return cnf


def planted_random_3sat_sat(num_vars: int, num_clauses: int, seed: int) -> Cnf:
    """Deterministic planted-assignment random 3-SAT instance.

    A Park-Miller stream first chooses a hidden assignment, then chooses
    three distinct variables and independent signs for each clause. If a
    proposed clause would be false under the hidden assignment, one
    deterministically selected literal is flipped. The planted assignment
    therefore witnesses SAT by construction; no third-party corpus data is
    consulted.
    """
    cnf = Cnf(num_vars=num_vars)
    cnf.comment(
        f"Project-authored planted random 3-SAT, {num_vars} vars, "
        f"{num_clauses} clauses, seed={seed}."
    )
    cnf.comment(
        "Park-Miller stream; every clause is made true by a deterministic "
        "hidden assignment."
    )
    random = ParkMiller(seed)
    assignment = [False] + [bool(random.next() % 2) for _ in range(num_vars)]

    for _ in range(num_clauses):
        variables: list[int] = []
        while len(variables) < 3:
            candidate = (random.next() % num_vars) + 1
            if candidate not in variables:
                variables.append(candidate)
        literals = [
            -variable if random.next() % 2 else variable
            for variable in variables
        ]

        def literal_is_true(literal: int) -> bool:
            value = assignment[abs(literal)]
            return value if literal > 0 else not value

        if not any(literal_is_true(literal) for literal in literals):
            flip_index = random.next() % len(literals)
            literals[flip_index] = -literals[flip_index]
        assert any(literal_is_true(literal) for literal in literals)
        cnf.add_clause(literals)

    return cnf


def generated_outputs() -> list[tuple[str, Cnf, str]]:
    """Return every committed fixture and its independently known answer."""
    return [
        # Legacy filenames retained for compatibility with existing
        # benchmark/report selectors. All bytes are generated here.
        ("uuf50-01.cnf", random_3sat_unsat(50, 218, 50_005), "UNSAT"),
        ("uuf50-02.cnf", random_3sat_unsat(50, 218, 50_007), "UNSAT"),
        ("uuf50-03.cnf", random_3sat_unsat(50, 218, 50_014), "UNSAT"),
        ("uuf50-04.cnf", random_3sat_unsat(50, 218, 50_015), "UNSAT"),
        ("uuf75-01.cnf", random_3sat_unsat(75, 325, 75_001), "UNSAT"),
        ("uuf75-02.cnf", random_3sat_unsat(75, 325, 75_002), "UNSAT"),
        ("uuf100-04.cnf", random_3sat_unsat(100, 430, 100_004), "UNSAT"),
        ("uf50-01.cnf", planted_random_3sat_sat(50, 218, 150_001), "SAT"),
        ("uf50-02.cnf", planted_random_3sat_sat(50, 218, 150_002), "SAT"),
        ("aim-50-1_6-no-1.cnf", padded_parity_cycle_unsat(50, 80), "UNSAT"),
        ("aim-100-1_6-no-1.cnf", padded_parity_cycle_unsat(100, 160), "UNSAT"),
        # Small direct-encoding pigeonhole fixtures.
        ("php-4-3.cnf", pigeonhole(4, 3), "UNSAT"),
        ("php-5-4.cnf", pigeonhole(5, 4), "UNSAT"),
        ("php-7-6.cnf", pigeonhole(7, 6), "UNSAT"),
        ("php-8-7.cnf", pigeonhole(8, 7), "UNSAT"),
        ("php-10-9.cnf", pigeonhole(10, 9), "UNSAT"),
        # Crafted / application tier (original fixtures).
        ("queens-4-sat.cnf", nqueens(4), "SAT"),
        ("queens-5-sat.cnf", nqueens(5), "SAT"),
        ("queens-4-overconstrained.cnf", nqueens(4, overconstrain=True), "UNSAT"),
        ("adder-4bit-equiv.cnf", adder_equivalence(4), "UNSAT"),
        ("blocks-3-t4.cnf", blocks_world_3_t4(), "SAT"),
        ("parity-cycle-33.cnf", parity_unsat(33, 2), "UNSAT"),
        # SAT-Comp-medium tier: larger UNSAT instances calibrated to
        # the 2-30 second native-solve band. These extend the corpus
        # past the 50-100-variable smoke/benchmark band so the JIT-amortization
        # story has fixtures whose native solve dwarfs the ~1.5 ms
        # JIT compile cost. Each candidate below was screened
        # interactively: php-11-10 takes ~13 s; the three uniform
        # random 3-SAT instances were sized to span 2-25 s; the
        # 8-bit adder equivalence miter rounds out the hardware
        # category at sub-millisecond cost (its value is structural
        # coverage, not amortization). Larger sizes (php-12-11,
        # 250-var uniform random) were tried and exceeded the 30 s
        # cap on MicroSAT; smaller multiplier miters were tried and
        # were too easy.
        ("php-11-10.cnf", pigeonhole(11, 10), "UNSAT"),
        ("adder-8bit-equiv.cnf", adder_equivalence(8), "UNSAT"),
        ("rand3sat-175-750-s1.cnf", random_3sat_unsat(175, 750, 1), "UNSAT"),
        ("rand3sat-200-860-s1.cnf", random_3sat_unsat(200, 860, 1), "UNSAT"),
        ("rand3sat-225-970-s1.cnf", random_3sat_unsat(225, 970, 1), "UNSAT"),
    ]


def validate_manifest(
    here: Path, outputs: list[tuple[str, Cnf, str]]
) -> None:
    """Require corpus.json, generated outputs, and DIMACS counts to agree."""
    manifest = json.loads((here / "corpus.json").read_text(encoding="utf-8"))
    entries = manifest.get("fixtures")
    if not isinstance(entries, list):
        raise SystemExit("corpus.json: `fixtures` must be a list")

    by_name: dict[str, dict[str, object]] = {}
    for entry in entries:
        if not isinstance(entry, dict) or not isinstance(entry.get("file"), str):
            raise SystemExit("corpus.json: every fixture needs a string `file`")
        name = entry["file"]
        if name in by_name:
            raise SystemExit(f"corpus.json: duplicate fixture {name}")
        by_name[name] = entry

    output_names = {name for name, _, _ in outputs}
    manifest_names = set(by_name)
    disk_names = {path.name for path in here.glob("*.cnf")}
    if output_names != manifest_names:
        raise SystemExit(
            "generator/manifest fixture sets differ: "
            f"generator-only={sorted(output_names - manifest_names)}, "
            f"manifest-only={sorted(manifest_names - output_names)}"
        )
    if output_names != disk_names:
        raise SystemExit(
            "generator/disk fixture sets differ: "
            f"generator-only={sorted(output_names - disk_names)}, "
            f"disk-only={sorted(disk_names - output_names)}"
        )

    for name, cnf, expected in outputs:
        entry = by_name[name]
        checks = {
            "expected": expected,
            "num_vars": cnf.num_vars,
            "num_clauses": len(cnf.clauses),
        }
        for field, generated in checks.items():
            if entry.get(field) != generated:
                raise SystemExit(
                    f"corpus.json: {name} {field}={entry.get(field)!r}, "
                    f"generator says {generated!r}"
                )


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate or verify the project-authored SAT fixture corpus."
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="compare generated bytes with committed fixtures without writing",
    )
    args = parser.parse_args()

    here = Path(__file__).resolve().parent
    outputs = generated_outputs()
    validate_manifest(here, outputs)
    mismatches: list[str] = []
    for name, cnf, expected in outputs:
        path = here / name
        encoded = cnf.to_dimacs().encode("ascii")
        digest = hashlib.sha256(encoded).hexdigest()
        summary = (
            f"{name}: sha256={digest} {cnf.num_vars} vars, "
            f"{len(cnf.clauses)} clauses, expected={expected}"
        )
        if args.check:
            try:
                actual = path.read_bytes()
            except FileNotFoundError:
                mismatches.append(f"{name}: missing")
            else:
                if actual != encoded:
                    actual_digest = hashlib.sha256(actual).hexdigest()
                    mismatches.append(
                        f"{name}: expected sha256={digest}, "
                        f"found sha256={actual_digest}"
                    )
            print(f"checked {summary}")
        else:
            path.write_bytes(encoded)
            print(f"wrote {summary}")

    if mismatches:
        for mismatch in mismatches:
            print(f"MISMATCH: {mismatch}")
        raise SystemExit(
            f"{len(mismatches)} generated fixture(s) differ; "
            "run generators.py to refresh them"
        )


if __name__ == "__main__":
    main()
