#!/usr/bin/env python3
"""Slice-23 rule mutants: guard each slice-23 rule behind `TCG_S23_MUTANT=<name>`, so one test
build runs every mutant (the test runner forwards TCG_* variables to the test binary). Restore
the files with `git checkout` afterwards; never commit them.

usage: mutate23.py <worktree root>

Mutants (each breaks one slice-23 rule; a control the rule exists for must fail):
 OD-205 (23a), arithmetic congruence pairing
  pair-no-operand-claims   the paired row's operands are not claimed equal
  key-no-width             a row pairs with a source operation of its operation at any width
  key-no-signedness        a row pairs with a source operation of either signedness
  pair-stamp-only          a row pairs on its stamp and key, its own transcription unchecked
  shift-key-full-count     a shift claims its whole counts equal (zero-extended to the wider)
  comm-creation-order      `comm` orders a product's operands by the table's creation order
 OD-206 (23b), the generalization over arithmetic leaves
  generalized-sat-refutes  a satisfiable generalization refutes the obligation (OD-200 ignored)
  generalize-not-rederived a consumer accepts a recorded generalization without re-deriving it
  leaf-creation-order      the leaves are numbered in the table's creation order
  generalize-first         the generalization is the owner's theorem (the default spelling)
 OD-205's arbiter (a departure from the design, added with it)
  paired-refutation-stands a paired theorem's refutation refutes the body (no theorem without the
                           pairing decides it)
 OD-205's theorem-level gate (a departure from the design, added with it)
  pairing-never-absorbed   a pairing the theorem's spelling absorbs is kept (its bytes move)
 The hostile review of 9f7aa5b2b (2026-10-28)
  shift-no-value-claim     a shift claims only its count, not its shifted value (operand 0)
  pair-psabi-walk-only     the clean-bool walk pairs nothing (only the psABI walk does)
  unpaired-units-are-paired the theorem without the pairing replays the paired theorem's parts
  shift-key-any-width      a shift key of any power-of-two width (8 and 16 bits) is admitted
  narrow-shift-row-generic an 8- or 16-bit variable shift row is refused without its name
 The pairing record every consumer re-derives (OD-205, after the hostile review)
  pairing-not-rederived    a consumer accepts a pairing record without re-deriving it
  pairing-unbound          a consumer re-checks the record but not that the statement is its spelling
  record-walk-from-key     the record's walk definitions are computed as K(c, d), not read from the walk
"""
import sys

root = sys.argv[1]
M = 'std::env::var("TCG_S23_MUTANT").is_ok_and(|mutant| mutant == "{}")'
OWNER = 'crates/trust-cg-verify/src/x86_source_bound_body.rs'
NORMAL = 'crates/trust-cg-verify/src/x86_source_bound_body/normal.rs'
REQUEST = 'crates/trust-cg-verify/src/function_request.rs'
EDITS = [
    ("pair-no-operand-claims", OWNER,
     '            if source != machine {\n                pairing.claims.push((*unit, source.eq_expr(machine)));\n',
     '            if source != machine && !' + M.format("pair-no-operand-claims") + ' {\n'
     '                pairing.claims.push((*unit, source.eq_expr(machine)));\n'),
    ("key-no-width/key-no-signedness", OWNER,
     'fn same_key(machine: ArithKey, source: ArithKey) -> bool {\n    machine == source\n}\n',
     'fn same_key(machine: ArithKey, source: ArithKey) -> bool {\n'
     '    let unsigned = |op: ArithOp| match op {\n'
     '        ArithOp::SMulWide => ArithOp::UMulWide,\n'
     '        ArithOp::Sdiv => ArithOp::Udiv,\n'
     '        ArithOp::Srem => ArithOp::Urem,\n'
     '        ArithOp::Ashr => ArithOp::Lshr,\n'
     '        other => other,\n'
     '    };\n'
     '    if ' + M.format("key-no-width") + ' {\n'
     '        return machine.op == source.op;\n    }\n'
     '    if ' + M.format("key-no-signedness") + ' {\n'
     '        return unsigned(machine.op) == unsigned(source.op) && machine.bits == source.bits;\n    }\n'
     '    machine == source\n}\n'),
    # key-no-width: the paired term is built at the source's width; the claims are fitted.
    ("key-no-width", OWNER,
     '        let (c, d) = &row.operands;\n        if !row.key.admits(c, d)\n',
     '        let (c, d) = &row.operands;\n'
     '        let fitted;\n'
     '        let (c, d) = if ' + M.format("key-no-width") + ' && row.key.bits != key.bits {\n'
     '            let fit_to = |x: &E| fit(x.clone(), x.bv_width(), key.bits);\n'
     '            fitted = (fit_to(c), fit_to(d));\n'
     '            (&fitted.0, &fitted.1)\n'
     '        } else {\n            (c, d)\n        };\n'
     '        if !(row.key.admits(c, d) || ' + M.format("key-no-width") + ')\n'),
    ("key-no-width", OWNER,
     '        let own = row.results.iter().all(|(name, part)| {\n'
     '            defined.get(name) == Some(&part.of(transcribed.clone(), row.key.bits))\n'
     '        });\n',
     '        let own = ' + M.format("key-no-width") + ' || row.results.iter().all(|(name, part)| {\n'
     '            defined.get(name) == Some(&part.of(transcribed.clone(), row.key.bits))\n'
     '        });\n'),
    ("key-no-width", OWNER,
     '            pairing\n                .definitions\n                .insert(name.clone(), part.of(paired.clone(), row.key.bits));\n',
     '            let paired = if ' + M.format("key-no-width") + ' && row.key.bits != key.bits {\n'
     '                fit(paired.clone(), paired.bv_width(), if *part == ArithPart::High { 2 * row.key.bits } else { row.key.bits })\n'
     '            } else {\n                paired.clone()\n            };\n'
     '            pairing\n                .definitions\n                .insert(name.clone(), part.of(paired, row.key.bits));\n'),
    ("pair-stamp-only", OWNER,
     '        if !own && !stamp_only_pairing() {\n            continue;\n        }\n',
     '        if !own && !stamp_only_pairing() && !' + M.format("pair-stamp-only") + ' {\n'
     '            continue;\n        }\n'),
    ("shift-key-full-count", OWNER,
     '            let source = key.read_operand(k, source.clone());\n'
     '            let machine = key.read_operand(k, machine.clone());\n',
     '            let (source, machine) = if ' + M.format("shift-key-full-count") + ' && k == 1 && key.is_shift() {\n'
     '                let wide = source.bv_width().max(machine.bv_width());\n'
     '                (fit(source.clone(), source.bv_width(), wide), fit(machine.clone(), machine.bv_width(), wide))\n'
     '            } else {\n'
     '                (key.read_operand(k, source.clone()), key.read_operand(k, machine.clone()))\n'
     '            };\n'),
    ("comm-creation-order", NORMAL,
     '    fn operand_order(&mut self, id: Id) -> u128 {\n        self.structural_key(id)\n    }\n',
     '    fn operand_order(&mut self, id: Id) -> u128 {\n'
     '        if ' + M.format("comm-creation-order") + ' {\n            return u128::from(id);\n        }\n'
     '        self.structural_key(id)\n    }\n'),
    ("leaf-creation-order", NORMAL,
     '    fn leaf_order(&self, first_occurrence: Vec<Id>) -> Vec<Id> {\n        first_occurrence\n    }\n',
     '    fn leaf_order(&self, mut first_occurrence: Vec<Id>) -> Vec<Id> {\n'
     '        if ' + M.format("leaf-creation-order") + ' {\n            first_occurrence.sort_unstable();\n        }\n'
     '        first_occurrence\n    }\n'),
    ("generalized-sat-refutes", REQUEST,
     '        (Some(VerificationResult::Invalid { .. }), _) => {\n'
     '            crate::x86_64_function_verifier::X86_BODY_GENERALIZED_SAT.to_owned()\n        }\n',
     '        (Some(VerificationResult::Invalid { counterexample }), general_why) => {\n'
     '            if ' + M.format("generalized-sat-refutes") + ' {\n'
     '                return (Some(VerificationResult::Invalid { counterexample }), general_why, false);\n'
     '            }\n'
     '            crate::x86_64_function_verifier::X86_BODY_GENERALIZED_SAT.to_owned()\n        }\n'),
    ("generalize-not-rederived", OWNER,
     '                if split::generalize(unit)? != *whole {\n',
     '                if !' + M.format("generalize-not-rederived") + ' && split::generalize(unit)? != *whole {\n'),
    ("generalize-not-rederived", OWNER,
     '                if let Some(generalized) = generalized\n                    && split::generalize(claim)? != *generalized\n',
     '                if let Some(generalized) = generalized\n'
     '                    && !' + M.format("generalize-not-rederived") + '\n'
     '                    && split::generalize(claim)? != *generalized\n'),
    ("generalize-first", OWNER,
     '    Ok(Theorem {\n        obligation,\n        free,\n',
     '    let obligation = if ' + M.format("generalize-first") + ' {\n'
     '        split::generalize(&obligation).unwrap_or(obligation)\n    } else {\n        obligation\n    };\n'
     '    Ok(Theorem {\n        obligation,\n        free,\n'),
    ("pairing-never-absorbed", OWNER,
     '    if absorbed {\n        return Ok((unpaired, None));\n    }\n',
     '    if absorbed && !' + M.format("pairing-never-absorbed") + ' {\n        return Ok((unpaired, None));\n    }\n'),
    ("shift-no-value-claim", OWNER,
     '        for (k, (source, machine)) in [(a, c), (b, d)].into_iter().enumerate() {\n',
     '        for (k, (source, machine)) in [(a, c), (b, d)].into_iter().enumerate() {\n'
     '            if k == 0 && key.is_shift() && ' + M.format("shift-no-value-claim") + ' {\n'
     '                continue;\n            }\n'),
    ("pair-psabi-walk-only", OWNER,
     '        let arithmetic = if pairs {\n',
     '        let arithmetic = if pairs\n'
     '            && !(names.convention == BoolArguments::Clean32 && ' + M.format("pair-psabi-walk-only") + ')\n'
     '        {\n'),
    ("unpaired-units-are-paired", OWNER,
     '                Some(unpaired) => unpaired.parts.parts.iter().collect(),\n',
     '                Some(_) if ' + M.format("unpaired-units-are-paired") + ' => self.replayed_units(),\n'
     '                Some(unpaired) => unpaired.parts.parts.iter().collect(),\n'),
    ("shift-key-any-width", OWNER,
     '            matches!(self.bits, 32 | 64) && a == self.bits && b >= self.bits.trailing_zeros()\n',
     '            (matches!(self.bits, 32 | 64)\n'
     '                || (' + M.format("shift-key-any-width") + ' && self.bits.is_power_of_two() && self.bits >= 2))\n'
     '                && a == self.bits\n'
     '                && b >= self.bits.trailing_zeros()\n'),
    ("narrow-shift-row-generic", OWNER,
     'fn narrow_variable_shift(inst: &X86ISelInst) -> Option<u32> {\n',
     'fn narrow_variable_shift(inst: &X86ISelInst) -> Option<u32> {\n'
     '    if ' + M.format("narrow-shift-row-generic") + ' {\n        return None;\n    }\n'),
    ("pairing-not-rederived", OWNER,
     '    pub fn check(&self, statement: &ProofObligation) -> Result<(), String> {\n        let derived = self\n',
     '    pub fn check(&self, statement: &ProofObligation) -> Result<(), String> {\n'
     '        if ' + M.format("pairing-not-rederived") + ' {\n            return Ok(());\n        }\n'
     '        let derived = self\n'),
    ("pairing-unbound", OWNER,
     '            .map_err(Clone::clone)?;\n        if statement.trust_ir_expr != derived.source_side\n',
     '            .map_err(Clone::clone)?;\n'
     '        if ' + M.format("pairing-unbound") + ' {\n            return Ok(());\n        }\n'
     '        if statement.trust_ir_expr != derived.source_side\n'),
    ("record-walk-from-key", OWNER,
     '                .map(|(name, part)| Some((name.clone(), *part, walked(name)?)))\n',
     '                .map(|(name, part)| {\n'
     '                    if ' + M.format("record-walk-from-key") + ' {\n'
     '                        let (c, d) = row.machine.clone();\n'
     '                        return Some((name.clone(), *part, part.of(row.key.apply(c, d), row.key.bits)));\n'
     '                    }\n'
     '                    Some((name.clone(), *part, walked(name)?))\n'
     '                })\n'),
    ("paired-refutation-stands", REQUEST,
     '        let (verdict, why, claims, theorem) = if refuted && body.is_paired() {\n',
     '        let (verdict, why, claims, theorem) = if refuted\n'
     '            && body.is_paired()\n'
     '            && !' + M.format("paired-refutation-stands") + '\n        {\n'),
]

for name, rel, old, new in EDITS:
    path = f"{root}/{rel}"
    text = open(path).read()
    n = text.count(old)
    if n != 1:
        sys.exit(f"{name}: {n} matches in {rel} for:\n{old}")
    open(path, "w").write(text.replace(old, new))
    print(f"applied {name} in {rel}")
