#!/usr/bin/env python3
"""Slice-18 rule mutants: guard each rule behind `TCG_S18_MUTANT=<name>`, so one
test build runs every mutant (scripts/trust_cargo.sh hands TCG_* variables to the
test binary; run_mutants.sh sets it on the binary directly). Restore the files
with `git checkout` afterwards; never commit them.

usage: mutate.py <worktree root> [stage...]   (stages: 1 2 3; default: every stage present)
       S18_MUTANTS=a,b mutate.py ...           (only the named mutants)

Stage 1 (OD-187, the canonical spelling). Sweep controls (each must fail
`slice18::canonical_spelling_preserves_every_fixture_theorem` or another
control):
  bitnorm-other-operand   bit_normalized concatenates adjacent extracts of two
                          DIFFERENT terms of one width as one extract
  unify-operator-only     unify_definitions numbers a right-hand side by its
                          operator and width only
  drop-any-equation       the value-numbered spelling drops every equation
                          claim, not only identities
  bitmoves-extract-offset bit_moves_normalized folds x[h2:l2][h:l] to x[h:l]
                          (the inner offset lost)
  bitmoves-bvadd          substitute_bit_moves also substitutes a definition
                          that adds (an EXACT substitution: expected to move
                          golden bytes only, never a sampled value)
Rule mutants (each must fail a golden digest or a control):
  no-cascade              a theorem slice 17's spelling empties goes straight
                          to the plain spelling (no slice-16 step)
  min-two                 a spelled theorem must keep two claims (slice 17's
                          rule)
  in-bounds-only          only a theorem with an in-bounds claim is spelled
                          (slice 17's predicate)
  identities-stated       an emptied spelling is stated with its identity
                          claims, its structural check skipped
"""
import os, sys

root = sys.argv[1]
stages = sys.argv[2:] or ["1", "2", "3"]
M = 'std::env::var("TCG_S18_MUTANT").is_ok_and(|mutant| mutant == "{}")'
OWNER = 'crates/trust-cg-verify/src/x86_source_bound_body.rs'
SPLIT = 'crates/trust-cg-verify/src/x86_source_bound_body/split.rs'

STAGE1 = [
    ("bitnorm-other-operand", SPLIT,
     ') if *l1 == *h2 + 1 && (std::sync::Arc::ptr_eq(a, b) || a == b) => {\n'
     '                    Some(whole(a.as_ref(), *h1, *l2))',
     ') if *l1 == *h2 + 1\n                    && (std::sync::Arc::ptr_eq(a, b)\n'
     f'                        || a == b\n                        || ({M.format("bitnorm-other-operand")} && a.bv_width() == b.bv_width())) =>\n'
     '                {\n                    Some(whole(a.as_ref(), *h1, *l2))'),
    ("unify-operator-only", SPLIT,
     '        let key = expr.to_string();\n        if let Some(earlier) = numbered.get(&key) {\n'
     '            env.insert(name, E::var(earlier.clone(), expr.bv_width()));',
     f'        let key = if {M.format("unify-operator-only")} {{\n'
     '            format!("{}:{}", expr.to_string().split_whitespace().next().unwrap_or_default(), expr.bv_width())\n'
     '        } else {\n            expr.to_string()\n        };\n'
     '        if let Some(earlier) = numbered.get(&key) {\n'
     '            env.insert(name, E::var(earlier.clone(), expr.bv_width()));'),
    ("drop-any-equation", OWNER,
     '        let mut emptied = false;\n        loop {\n            match drop_identities(&stated) {\n'
     '                Some((dropped, true)) => {\n                    let (next, _, next_claims) =\n'
     '                        inline_single_use(kept, E::bool_const(true), dropped);\n'
     '                    kept = next;\n                    stated = next_claims;\n                }\n'
     '                Some((_, false)) => break,\n                None => {\n'
     '                    emptied = true;\n                    break;\n                }\n            }\n        }\n'
     '        if emptied {\n            // Never stated by identities alone (slice 9\'s rule): the next\n',
     '        let mut emptied = false;\n        loop {\n'
     f'            match if {M.format("drop-any-equation")} {{\n'
     '                mutant_drop_equations(&stated)\n            } else {\n'
     '                drop_identities(&stated)\n            } {\n'
     '                Some((dropped, true)) => {\n                    let (next, _, next_claims) =\n'
     '                        inline_single_use(kept, E::bool_const(true), dropped);\n'
     '                    kept = next;\n                    stated = next_claims;\n                }\n'
     '                Some((_, false)) => break,\n                None => {\n'
     '                    emptied = true;\n                    break;\n                }\n            }\n        }\n'
     '        if emptied {\n            // Never stated by identities alone (slice 9\'s rule): the next\n'),
    ("drop-any-equation", OWNER,
     '/// Structural non-vacuity: every premise defines a fresh name that is not a\n',
     '/// Mutant `drop-any-equation`: drop every equation claim.\n'
     'fn mutant_drop_equations(claims: &E) -> Option<(E, bool)> {\n'
     '    let mut terms = Vec::new();\n    let mut rest = claims;\n'
     '    while let E::And { lhs, rhs } = rest {\n        terms.push(lhs.as_ref().clone());\n        rest = rhs.as_ref();\n    }\n'
     '    terms.push(rest.clone());\n    let count = terms.len();\n'
     '    let kept: Vec<E> = terms.into_iter().filter(|term| !matches!(term, E::Eq { .. })).collect();\n'
     '    let dropped = kept.len() != count;\n'
     '    kept.into_iter().rev().reduce(|tail, term| term.and_expr(tail)).map(|claims| (claims, dropped))\n}\n\n'
     '/// Structural non-vacuity: every premise defines a fresh name that is not a\n'),
    ("bitmoves-extract-offset", SPLIT,
     '                            .extract(high + inner_low, low + inner_low),\n',
     f'                            .extract(\n                                high + if {M.format("bitmoves-extract-offset")} {{ 0 }} else {{ *inner_low }},\n'
     f'                                low + if {M.format("bitmoves-extract-offset")} {{ 0 }} else {{ *inner_low }},\n'
     '                            ),\n'),
    ("bitmoves-bvadd", SPLIT,
     '            E::Concat { hi, lo, .. } => moves_bits(hi, budget) && moves_bits(lo, budget),\n'
     '            _ => false,\n',
     '            E::Concat { hi, lo, .. } => moves_bits(hi, budget) && moves_bits(lo, budget),\n'
     f'            E::BvAdd {{ lhs, rhs, .. }} if {M.format("bitmoves-bvadd")} => {{\n'
     '                moves_bits(lhs, budget) && moves_bits(rhs, budget)\n            }\n'
     '            _ => false,\n'),
    ("no-cascade", OWNER,
     '            ValueNumbering::Every if self.bit_moves => Self {\n',
     f'            ValueNumbering::Every if self.bit_moves && !{M.format("no-cascade")} => Self {{\n'),
    ("min-two", OWNER,
     '            ValueNumbering::InBounds => check_definitional(&obligation, &free),\n'
     '            _ => check_definitional_part(&obligation, &free),\n',
     '            ValueNumbering::InBounds => check_definitional(&obligation, &free),\n'
     f'            _ if {M.format("min-two")} => check_definitional(&obligation, &free),\n'
     '            _ => check_definitional_part(&obligation, &free),\n'),
    ("in-bounds-only", OWNER,
     '            ValueNumbering::Every => true,\n        };\n',
     f'            ValueNumbering::Every => !{M.format("in-bounds-only")} || states_indexed.get(),\n        }};\n'),
    ("identities-stated", OWNER,
     '        if emptied {\n            // Never stated by identities alone (slice 9\'s rule): the next\n',
     f'        if emptied && !{M.format("identities-stated")} {{\n            // Never stated by identities alone (slice 9\'s rule): the next\n'),
    ("identities-stated", OWNER,
     '        if checked.is_err() {\n            return build_theorem(body, walks, encoding.next_spelling());\n',
     f'        if checked.is_err() && !{M.format("identities-stated")} {{\n'
     '            return build_theorem(body, walks, encoding.next_spelling());\n'),
]

EDITS = {"1": STAGE1}
here = os.path.dirname(os.path.abspath(__file__))
for extra in ("2", "3"):
    path = os.path.join(here, f"mutants_stage{extra}.py")
    if os.path.exists(path):
        scope = {"M": M, "OWNER": OWNER, "SPLIT": SPLIT}
        exec(open(path).read(), scope)
        EDITS[extra] = scope["EDITS"]

def outdented(block):
    """`block` with four spaces less indentation on every line (an anchor written
    for a nested function, applied after stage 2 hoisted it to module level)."""
    return "\n".join(line[4:] if line.startswith("    ") else line for line in block.split("\n"))


ONLY = set(filter(None, os.environ.get("S18_MUTANTS", "").split(",")))
for stage in stages:
    for name, path, old, new in EDITS.get(stage, []):
        if ONLY and name not in ONLY:
            continue
        full = os.path.join(root, path)
        text = open(full).read()
        count = text.count(old)
        if count != 1 and text.count(outdented(old)) == 1:
            old, new = outdented(old), outdented(new)
            count = 1
        if count != 1:
            sys.exit(f"{name}: the anchor occurs {count} times in {path}")
        open(full, "w").write(text.replace(old, new))
        print(f"applied {name} ({path})")
