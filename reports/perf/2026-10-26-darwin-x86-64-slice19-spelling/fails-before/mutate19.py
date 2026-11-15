#!/usr/bin/env python3
"""Slice-19 rule mutants: guard each rule behind `TCG_S19_MUTANT=<name>`, so one test build
runs every mutant (the test binary reads the variable directly). Restore the files with
`git checkout` afterwards; never commit them.

usage: mutate19.py <worktree root> <stage>   (stage 1: OD-195; 2: OD-196; 3: OD-197)

Each mutant makes its rule WRONG (unsound) unless marked exact; each must fail a control.
"""
import os, sys
root, stage = sys.argv[1], sys.argv[2]
NORMAL = 'crates/trust-cg-verify/src/x86_source_bound_body/normal.rs'
SPLIT = 'crates/trust-cg-verify/src/x86_source_bound_body/split.rs'
OWNER = 'crates/trust-cg-verify/src/x86_source_bound_body.rs'
def M(name):
    return f'super::normal::mutant("{name}")'
def MN(name):
    return f'mutant("{name}")'

HELPER = ('use super::*;\nuse std::sync::Arc;\n',
          'use super::*;\nuse std::sync::Arc;\n\n/// Fails-before only (never committed).\n'
          'pub(super) fn mutant(name: &str) -> bool {\n'
          '    std::env::var("TCG_S19_MUTANT").is_ok_and(|mutant| mutant == name)\n}\n')

STAGE1 = [
 # --- slice 18's "v18" groups
 ("ext-above-sign-zero", "zeros above a SIGN extension too", NORMAL,
  "                        if zero && low >= wy {",
  f"                        if (zero || {MN('ext-above-sign-zero')}) && low >= wy {{"),
 ("ext-low-kind", "the low bits of a sign extension rebuilt as a zero extension", NORMAL,
  "                                let extended = if zero {",
  f"                                let extended = if zero || {MN('ext-low-kind')} {{"),
 ("ext-concat-half", "an extract inside a concatenation's low half read from its high half", NORMAL,
  "                        if high < low_width {\n                            let bits = self.extract(lo, high, low);",
  f"                        if high < low_width {{\n                            let bits = self.extract(if {MN('ext-concat-half')} {{ hi }} else {{ lo }}, high, low);"),
 ("ext-sext-of-zext", "the sign extension of ANY zero extension (by 0 too) is a zero extension", NORMAL,
  "                    Op::ZeroExtend(inner) if !zero && inner >= 1 => {",
  f"                    Op::ZeroExtend(inner) if !zero && (inner >= 1 || {MN('ext-sext-of-zext')}) => {{"),
 ("ext-zero-high", "concat(0, x) is a SIGN extension", NORMAL,
  "                    let extended = self.mk(Op::ZeroExtend(self.width(hi)), vec![lo]);",
  f"                    let extended = if {MN('ext-zero-high')} {{ self.mk(Op::SignExtend(self.width(hi)), vec![lo]) }} else {{ self.mk(Op::ZeroExtend(self.width(hi)), vec![lo]) }};"),
 ("fold-distinct-true", "an equation of two distinct constants is TRUE", NORMAL,
  "                    // Two distinct constants (one id per term).\n                    return self.g(Groups::FOLD, self.f);",
  f"                    // Two distinct constants (one id per term).\n                    return self.g(Groups::FOLD, if {MN('fold-distinct-true')} {{ self.t }} else {{ self.f }});"),
 ("bool-eq-false", "(= x false) is x", NORMAL,
  "                    if y == self.f && self.has(Groups::BOOL) {\n                        return Some(self.not(x));",
  f"                    if y == self.f && self.has(Groups::BOOL) {{\n                        return Some(if {MN('bool-eq-false')} {{ x }} else {{ self.not(x) }});"),
 ("bool-ite-negated", "(ite c true false) is (not c)", NORMAL,
  "                if t == self.t && e == self.f {\n                    return self.g(Groups::BOOL, c);",
  f"                if t == self.t && e == self.f {{\n                    let c = if {MN('bool-ite-negated')} {{ self.not(c) }} else {{ c }};\n                    return self.g(Groups::BOOL, c);"),
 ("bit1-polarity", "the one-bit encoding's polarity ignored", NORMAL,
  "                            return Some(if y_value == t_value { c } else { self.not(c) });",
  f"                            return Some(if y_value == t_value || {MN('bit1-polarity')} {{ c }} else {{ self.not(c) }});"),
 ("ovf-offset", "the widening overflow test reads from bit n-1", NORMAL,
  "                                let top = self.extract(y, wide - 1, narrow);\n                                let zero = self.zero(wide - narrow);\n                                return Some(self.eq(top, zero));\n                            }\n                        }\n                    }\n                }\n                // `(= (bvsub x y) 0)` is `(= x y)`.",
  f"                                let n = if {MN('ovf-offset')} {{ narrow - 1 }} else {{ narrow }};\n                                let top = self.extract(y, wide - 1, n);\n                                let zero = self.zero(wide - n);\n                                return Some(self.eq(top, zero));\n                            }}\n                        }}\n                    }}\n                }}\n                // `(= (bvsub x y) 0)` is `(= x y)`."),
 ("subz-any-constant", "(= (bvsub x y) C) is (= x y) for any constant C", NORMAL,
  "                        && self.constant(y) == Some(0)\n                        && let Op::BvSub = self.op(x)",
  f"                        && (self.constant(y) == Some(0) || ({MN('subz-any-constant')} && self.constant(y).is_some()))\n                        && let Op::BvSub = self.op(x)"),
 ("arith-and-zero", "x & 0 is x", NORMAL,
  "                            if value == 0 {\n                                return Some(self.zero(width));",
  f"                            if value == 0 {{\n                                if {MN('arith-and-zero')} {{ return Some(x); }}\n                                return Some(self.zero(width));"),
 ("arith-sub-self", "x - x is x", NORMAL,
  "                if a == b {\n                    let zero = self.zero(width);\n                    return self.g(Groups::ARITH, zero);\n                }\n                self.fold(node)\n            }\n            Op::BvAnd => {",
  f"                if a == b {{\n                    if {MN('arith-sub-self')} {{ return Some(a); }}\n                    let zero = self.zero(width);\n                    return self.g(Groups::ARITH, zero);\n                }}\n                self.fold(node)\n            }}\n            Op::BvAnd => {{"),
 # --- the slice-19 groups
 ("mullo-udiv", "the low bits of a QUOTIENT taken as the quotient of the low bits", NORMAL,
  "                    Op::BvMul if self.has(Groups::MULLO) => {",
  f"                    Op::BvMul | Op::BvUDiv if self.has(Groups::MULLO) => {{\n                        if inner == Op::BvUDiv && !{MN('mullo-udiv')} {{ return None; }}"),
 ("addlo-lshr", "the low bits of a logical shift taken from the operands' low bits", NORMAL,
  "                    Op::BvAdd | Op::BvSub | Op::BvAnd | Op::BvOr | Op::BvXor\n                        if self.has(Groups::ADDLO) =>\n                    {",
  f"                    Op::BvAdd | Op::BvSub | Op::BvAnd | Op::BvOr | Op::BvXor | Op::BvLshr\n                        if self.has(Groups::ADDLO) =>\n                    {{\n                        if inner == Op::BvLshr && !{MN('addlo-lshr')} {{ return None; }}"),
 ("shr-sign", "a logical shift right fills with the sign bit", NORMAL,
  "                    let bits = self.extract(x, width - 1, k);\n                    self.mk(Op::ZeroExtend(k), vec![bits])",
  f"                    let bits = self.extract(x, width - 1, k);\n                    if {MN('shr-sign')} {{ self.mk(Op::SignExtend(k), vec![bits]) }} else {{ self.mk(Op::ZeroExtend(k), vec![bits]) }}"),
 ("cmp-strict", "(bvule a b) is (bvult a b)", NORMAL,
  "                Op::Ule => {\n                    let lt = self.mk(Op::Ult, vec![b, a]);\n                    return Some(self.not(lt));",
  f"                Op::Ule => {{\n                    if {MN('cmp-strict')} {{ return Some(self.mk(Op::Ult, vec![a, b])); }}\n                    let lt = self.mk(Op::Ult, vec![b, a]);\n                    return Some(self.not(lt));"),
 ("cmp-or-direction", "(or (bvult p q) (= p q)) is (not (bvult p q))", NORMAL,
  "                            if compared == equated {\n                                let lt = self.mk(Op::Ult, vec![q, p]);",
  f"                            if compared == equated {{\n                                let lt = if {MN('cmp-or-direction')} {{ self.mk(Op::Ult, vec![p, q]) }} else {{ self.mk(Op::Ult, vec![q, p]) }};"),
 ("ovf2-unchecked", "ovf2/sovf without checking the extended term is the product's low bits", NORMAL,
  "                if self.normalized(bits) != low {\n                    continue;\n                }",
  f"                if self.normalized(bits) != low && !{MN('ovf2-unchecked')} {{\n                    continue;\n                }}"),
 ("sovf-top", "the sign test reads from bit n, not n-1", NORMAL,
  "        let top_width = wide - narrow + 1;",
  f"        let narrow = if {MN('sovf-top')} {{ narrow + 1 }} else {{ narrow }};\n        if narrow > wide {{ return None; }}\n        let top_width = wide - narrow + 1;"),
 ("mulpow2-off", "a product by 2^k is a shift by k+1", NORMAL,
  "                    let k = value.trailing_zeros();\n                    if k < width {",
  f"                    let k = value.trailing_zeros() + u32::from({MN('mulpow2-off')});\n                    if k < width {{"),
 ("cse-operand", "a term whose first operand is a kept right-hand side renamed to that name", NORMAL,
  "        self.rewrite(root, &mut |terms, node| {\n            let name = numbered.get(&node)?;",
  f"        self.rewrite(root, &mut |terms, node| {{\n            let first = terms.args(node).first().copied();\n            let probe = if {MN('cse-operand')} && first.is_some_and(|f| numbered.contains_key(&f) && terms.width(f) == terms.width(node)) {{ first.unwrap() }} else {{ node }};\n            let name = numbered.get(&probe)?;"),
 ("look-window", "look reads the definition's low bits whatever the window", NORMAL,
  "            let bits = terms.extract(rhs, high, low);\n            let candidate = terms.normalized(bits);",
  f"            let (h, l) = if {MN('look-window')} {{ (high - low, 0) }} else {{ (high, low) }};\n            let bits = terms.extract(rhs, h, l);\n            let candidate = terms.normalized(bits);"),
 ("itepull-mixed", "an ite of a zero and a sign extension pulled as the first's", NORMAL,
  "            if to == eo\n                && matches!(to, Op::ZeroExtend(_) | Op::SignExtend(_) | Op::Extract(..))",
  f"            let same = to == eo || ({MN('itepull-mixed')} && matches!((&to, &eo), (Op::ZeroExtend(a), Op::SignExtend(b)) if a == b));\n            if same\n                && matches!(to, Op::ZeroExtend(_) | Op::SignExtend(_) | Op::Extract(..))"),
 ("peel-window", "peel for any extract starting at bit 0 of a narrower width", NORMAL,
  "                if high + 1 == terms.width(t) {",
  f"                if high + 1 == terms.width(t) || ({MN('peel-window')} && high < terms.width(t)) {{"),
 # --- the pipeline
 ("drop-any-equation", "drop_identities drops every equation", NORMAL,
  "        let identity = |terms: &Self, term: Id| {\n            *terms.op(term) == Op::Eq && terms.arg(term, 0) == terms.arg(term, 1)\n        };",
  f"        let identity = |terms: &Self, term: Id| {{\n            *terms.op(term) == Op::Eq && (terms.arg(term, 0) == terms.arg(term, 1) || {MN('drop-any-equation')})\n        }};"),
 ("claims-drop-true-guard", "an item whose guard has a literal normalized to true is dropped", NORMAL,
  "                    literals.retain(|&literal| literal != self.t);",
  f"                    if {MN('claims-drop-true-guard')} && literals.contains(&self.t) {{\n                        continue;\n                    }}\n                    literals.retain(|&literal| literal != self.t);"),
 ("moves-bits-add", "(exact) a definition that adds is substituted as a bit move", NORMAL,
  "            Op::Var(..) | Op::Const(..) => true,\n            Op::Extract(..) | Op::ZeroExtend(_) | Op::SignExtend(_) => {",
  f"            Op::Var(..) | Op::Const(..) => true,\n            Op::BvAdd if {MN('moves-bits-add')} => {{\n                self.moves_bits(self.arg(expr, 0), budget)\n                    && self.moves_bits(self.arg(expr, 1), budget)\n            }}\n            Op::Extract(..) | Op::ZeroExtend(_) | Op::SignExtend(_) => {{"),
 # --- where the spelling applies
 ("no-normal-parts", "parts are not spelled by slice 19", SPLIT,
  "            normal_groups(normal::Groups::CANONICAL),\n        ) {",
  f"            if {M('no-normal-parts')} {{ normal::Groups::NONE }} else {{ normal_groups(normal::Groups::CANONICAL) }},\n        ) {{"),
 ("no-normal-one-path", "one-path theorems are not spelled", OWNER,
  "        } else {\n            match normal::spelled_pair(&definitions, &source_side, &machine_side, groups) {",
  f"        }} else if normal::mutant(\"no-normal-one-path\") {{\n            (spelling, source_side, machine_side)\n        }} else {{\n            match normal::spelled_pair(&definitions, &source_side, &machine_side, groups) {{"),
 ("normal-unchecked", "a spelled theorem that fails the structural check is kept", OWNER,
  "        if checked.is_err() {\n            return build_theorem(\n                body,\n                walks,\n                PathEncoding {\n                    normal: normal::Groups::NONE,",
  f"        if checked.is_err() && !normal::mutant(\"normal-unchecked\") {{\n            return build_theorem(\n                body,\n                walks,\n                PathEncoding {{\n                    normal: normal::Groups::NONE,"),
]

STAGE1W = [
 ("wide-bits-off", "(exact) a single-use name for bits of a wide term is inlined (the design's pipeline)", NORMAL,
  "            if uses.get(&name).copied().unwrap_or(0) <= 1 && !self.wide_bits(rhs) {",
  f"            if uses.get(&name).copied().unwrap_or(0) <= 1 && (!self.wide_bits(rhs) || {MN('wide-bits-off')}) {{"),
]

STAGE1P = [
 ("wide-bits-products", "the wide-bits name kept for the half of a product too", NORMAL,
  "            .any(|id| *self.op(id) == Op::BvMul)",
  f"            .any(|id| *self.op(id) == Op::BvMul && !{MN('wide-bits-products')})"),
]

STAGE2 = [
 ("magic-unchecked", "the Granlund-Montgomery inequality skipped: any divisor ceil(2^k/m) below 2^n", NORMAL,
  "    match max_of(n).checked_mul(e) {\n        Some(product) if below_pow2(product, k) => Some(d),",
  f"    if {MN('magic-unchecked')} {{\n        return Some(d);\n    }}\n    match max_of(n).checked_mul(e) {{\n        Some(product) if below_pow2(product, k) => Some(d),"),
 ("magic-wrap", "a multiply-high whose product may wrap its width admitted", NORMAL,
  "                Some(top) if below_pow2(top, wide) => top,",
  f"                Some(top) if below_pow2(top, wide) || {MN('magic-wrap')} || {MN('magic-wrap-high')} => top,"),
 ("magic-high-bits", "a multiply-high with quotient bits above hi admitted", NORMAL,
  "            if !below_pow2(top >> low, high - low + 1) {",
  f"            if !below_pow2(top >> low, high - low + 1) && !{MN('magic-high-bits')} && !{MN('magic-wrap-high')} {{"),
 ("magic-add-other-x", "the add shape's x - h not checked to read the multiplied x", NORMAL,
  "                || !self.same(self.arg(difference, 0), x)",
  f"                || (!self.same(self.arg(difference, 0), x) && !{MN('magic-add-other-x')})"),
 ("magic-add-window", "the add shape read through any extract window", NORMAL,
  "                || high != n - 1\n",
  f"                || (high != n - 1 && !{MN('magic-add-window')})\n"),
 ("range-unbounded", "the quotient range without its bound", NORMAL,
  "        if !below_pow2(max_of(n) / u128::from(divisor), r) || j + r < n {",
  f"        if (!below_pow2(max_of(n) / u128::from(divisor), r) && !{MN('range-unbounded')}) || j + r < n {{"),
 ("uremdef-swapped", "a remainder by a constant defined as its quotient", NORMAL,
  "        Some(self.mk(Op::BvSub, vec![x, product]))",
  f"        if {MN('uremdef-swapped')} {{\n            return Some(quotient);\n        }}\n        Some(self.mk(Op::BvSub, vec![x, product]))"),
 ("magic-no-names", "(exact) magic does not look through kept names", NORMAL,
  "            if self.has(Groups::MAGIC) {\n                self.rhs_of.insert(name.clone(), rhs);",
  f"            if self.has(Groups::MAGIC) && !{MN('magic-no-names')} {{\n                self.rhs_of.insert(name.clone(), rhs);"),
]

STAGE1B = [
 ("cse-operator-only", "cse renames a term to an earlier kept name of the same operator and width", NORMAL,
  "        self.rewrite(root, &mut |terms, node| {\n            let name = numbered.get(&node)?;",
  f"        self.rewrite(root, &mut |terms, node| {{\n            let wrong = {MN('cse-operator-only')}\n                .then(|| {{\n                    numbered\n                        .keys()\n                        .filter(|key| terms.op(**key).clone() == terms.op(node).clone() && terms.width(**key) == terms.width(node))\n                        .min()\n                        .copied()\n                }})\n                .flatten();\n            let name = numbered.get(&wrong.unwrap_or(node))?;"),
]

FUNCTION_REQUEST = 'crates/trust-cg-verify/src/function_request.rs'
AY_BRIDGE = 'crates/trust-cg-verify/src/ay_bridge.rs'
MEMO = 'crates/trust-cg-verify/src/source_bound_negative_memo.rs'
def ME(name):
    return f'std::env::var("TCG_S19_MUTANT").is_ok_and(|mutant| mutant == "{name}")'

STAGE3 = [
 # (a) the claim split
 ("claims-drop-last", "the last claim of a split never stated (credit without it)", SPLIT,
  "    if !claims.contains(&rest) {\n        claims.push(rest);",
  f"    if !claims.contains(&rest) && !{ME('claims-drop-last')} {{\n        claims.push(rest);"),
 ("claims-any-valid", "an obligation credited at its first Valid claim", FUNCTION_REQUEST,
  "            (Some(VerificationResult::Valid), _) => {}",
  f"            (Some(VerificationResult::Valid), _) => {{\n                if {ME('claims-any-valid')} {{\n                    return (Some(VerificationResult::Valid), None, true);\n                }}\n            }}"),
 ("claims-record-unchecked", "a published claim record not re-derived", OWNER,
  "                && split::claim_parts(unit)? != *claims",
  f"                && !{ME('claims-record-unchecked')}\n                && split::claim_parts(unit)? != *claims"),
 # (b) the fresh replay after a resident deadline, and memo v5
 ("fresh-retry-off", "(liveness) a resident deadline ends the replay (main's route)", AY_BRIDGE,
  "                if !query.fresh_after_resident_timeout {",
  f"                if !query.fresh_after_resident_timeout || {ME('fresh-retry-off')} {{"),
 ("fresh-expiry-unnoted", "the fresh route's deadline not noted: a resident deadline alone recorded", AY_BRIDGE,
  "        Err(SolverInvocationError::Timeout(expiry)) => {\n            witness.note_expiry(Some(expiry));\n            (AYResult::Timeout, AyVerdictSource::LiveSolve)",
  f"        Err(SolverInvocationError::Timeout(expiry)) => {{\n            if !{ME('fresh-expiry-unnoted')} {{\n                witness.note_expiry(Some(expiry));\n            }}\n            (AYResult::Timeout, AyVerdictSource::LiveSolve)"),
 ("memo-any-exhausting", "a timeout recorded when ANY deadline used its budget", MEMO,
  "        if !self.exhausting_expiry.load(Ordering::Relaxed)\n            || self.unproven_expiry.load(Ordering::Relaxed)",
  f"        if !self.exhausting_expiry.load(Ordering::Relaxed)\n            || (self.unproven_expiry.load(Ordering::Relaxed) && !{ME('memo-any-exhausting')})"),
 ("memo-reads-v4", "a v4 entry (a resident deadline alone) read", MEMO,
  "        if next_line(&mut rest)? != SCHEMA\n",
  f"        if ({{\n            let line = next_line(&mut rest)?;\n            line != SCHEMA\n                && !({ME('memo-reads-v4')} && line == \"tcg-source-bound-negative-memo-v4\")\n        }})\n"),
]

stages = {"1": STAGE1, "2": STAGE2 + STAGE1B, "3": STAGE3,
          # Slice 19 on main fc03f94f2: one build for the wide-bits rule, stage 2 and stage 3.
          "all": STAGE1W + STAGE2 + STAGE1B + STAGE3,
          # The wide-bits rule's product exclusion, on its own build.
          "1p": STAGE1W + STAGE1P}
for name, what, path, old, new in stages[stage]:
    p = os.path.join(root, path)
    s = open(p).read()
    assert s.count(old) == 1, f"{name}: {s.count(old)} matches in {path}"
    s = s.replace(old, new)
    open(p, "w").write(s)
p = os.path.join(root, NORMAL)
s = open(p).read()
if stage != "3" and 'fn mutant(' not in s:
    assert s.count(HELPER[0]) == 1
    s = s.replace(HELPER[0], HELPER[1])
    open(p, "w").write(s)
for name, what, *_ in stages[stage]:
    print(f"{name:24s} {what}")
