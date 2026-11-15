#!/usr/bin/env python3
"""Slice-22 rule mutants: guard each slice-22 rule behind `TCG_S22_MUTANT=<name>`, so one test
build runs every mutant (the test runner forwards TCG_* variables to the test binary). Restore
the files with `git checkout` afterwards; never commit them.

usage: mutate.py <worktree root> <stage: a | b | c>...

Mutants (each breaks one slice-22 rule; a control the rule exists for must fail):
 OD-202 (stage a), an I128 division as its routine's call; the I128 guard
  div-no-call-event          the division's call is no event of the trace (the machine's call
                             then pairs with nothing)
  div-args-unobserved        the division's call observes no argument (and its row's argument
                             registers are not checked)
  div-symbol-unchecked       a division's call row may name any of the four routines
  guard128-low-half-only     the I128 guard fires where the divisor's LOW half is zero
  guard128-wide-constant-stops   a nonzero 128-bit constant with a high half is a stop
  liveness-division-no-call  the byte liveness reads nothing at an I128 division
  i128-division-stops        an I128 division makes a several-path source a DAG (slice 14's rule)
 OD-203 (stage b), the 128-bit product by its 64-bit limbs
  limb-one-cross             `limb` keeps one cross product (inexact)
  limb-widening              `limb` also rewrites a widening product of two extensions
  addhi0-any-low             `addhi0` applies whatever constant fills the low bits
  acmul-unscoped             `acmul` sorts every limb-wide sum, product leaf or not
  acmul-creation-order       `acmul` sorts by the table's creation order, not by structure
  guard-fold-off             a guarded claim whose guard's double negation was folded is not
                             read back as guarded (the theorem keeps slice 18's spelling)
 OD-204 (stage c), the bit-move normal form
  catnf-halves-swapped       an extract across a concatenation's halves joins them high below
  catnf-or-any-tail          the `bvor` rule merges a chain whatever constant ends it
  catnf-merge-any            extracts of one term at a chain's head merge even when not adjacent
"""
import sys

root = sys.argv[1]
stages = set(sys.argv[2:]) or {"a"}
M = 'std::env::var("TCG_S22_MUTANT").is_ok_and(|mutant| mutant == "{}")'
OWNER = 'crates/trust-cg-verify/src/x86_source_bound_body.rs'
SPLIT = 'crates/trust-cg-verify/src/x86_source_bound_body/split.rs'
NORMAL = 'crates/trust-cg-verify/src/x86_source_bound_body/normal.rs'
EDITS = {"a": [
    ("div-no-call-event", OWNER,
     '                events.push(SourceEvent::Call(k));\n',
     '                if !(' + M.format("div-no-call-event") + ' && i128_division) {\n'
     '                    events.push(SourceEvent::Call(k));\n                }\n'),
    ("div-args-unobserved", OWNER,
     '                            i128_division_routine(&inst.opcode).to_owned(),\n'
     '                            false,\n                            None,\n                            &inst.args[..],\n',
     '                            i128_division_routine(&inst.opcode).to_owned(),\n'
     '                            false,\n                            None,\n'
     '                            if ' + M.format("div-args-unobserved") + ' { &inst.args[..0] } else { &inst.args[..] },\n'),
    ("div-args-unobserved", OWNER,
     '    if inst.call_arg_regs != expected_args {\n',
     '    if inst.call_arg_regs != expected_args\n'
     '        && !(' + M.format("div-args-unobserved") + ' && call.name.ends_with("ti3"))\n    {\n'),
    ("div-symbol-unchecked", OWNER,
     '            if *symbol != call.name || exact_module != call.exact_module {\n',
     '            let any_routine = ' + M.format("div-symbol-unchecked") + '\n'
     '                && symbol.ends_with("ti3")\n                && call.name.ends_with("ti3");\n'
     '            if (*symbol != call.name && !any_routine) || exact_module != call.exact_module {\n'),
    ("guard128-low-half-only", OWNER,
     '                        let fire = divisor.eq_expr(E::bv_const(0, width));\n',
     '                        let fire = if ' + M.format("guard128-low-half-only") + ' && width == 128 {\n'
     '                            divisor.extract(63, 0).eq_expr(E::bv_const(0, 64))\n'
     '                        } else {\n'
     '                            divisor.eq_expr(E::bv_const(0, width))\n                        };\n'),
    ("guard128-wide-constant-stops", OWNER,
     '                || (ty == Carrier::I128\n',
     '                || (ty == Carrier::I128\n'
     '                    && !' + M.format("guard128-wide-constant-stops") + '\n'),
    ("liveness-division-no-call", SPLIT,
     '    let wide_divisions = i128_divisions(source);\n',
     '    let wide_divisions = if ' + M.format("liveness-division-no-call") + ' {\n'
     '        HashSet::new()\n    } else {\n        i128_divisions(source)\n    };\n'),
    ("i128-division-stops", OWNER,
     '            let calls = split::i128_divisions(source);\n',
     '            let calls = if ' + M.format("i128-division-stops") + ' {\n'
     '                HashSet::new()\n            } else {\n'
     '                split::i128_divisions(source)\n            };\n'),
], "b": [
    ("guard-fold-off", NORMAL,
     '        if !self.has(Groups::GUARD) || *self.op(item) != Op::Or {\n',
     '        if !self.has(Groups::GUARD) || *self.op(item) != Op::Or || ' + M.format("guard-fold-off") + ' {\n'),
    ("limb-one-cross", NORMAL,
     '        let cross = self.mk(Op::BvAdd, vec![high_low, low_high]);\n',
     '        let cross = if ' + M.format("limb-one-cross") + ' {\n'
     '            high_low\n        } else {\n'
     '            self.mk(Op::BvAdd, vec![high_low, low_high])\n        };\n'),
    ("limb-widening", NORMAL,
     '        if self.is_limb_extension(x) && self.is_limb_extension(y) {\n',
     '        if self.is_limb_extension(x)\n            && self.is_limb_extension(y)\n'
     '            && !' + M.format("limb-widening") + '\n        {\n'),
    ("addhi0-any-low", NORMAL,
     '            if self.width(zeros) == low && self.constant(zeros) == Some(0) {\n',
     '            if self.width(zeros) == low\n'
     '                && (self.constant(zeros) == Some(0)\n'
     '                    || (' + M.format("addhi0-any-low") + ' && self.constant(zeros).is_some()))\n'
     '            {\n'),
    ("acmul-unscoped", NORMAL,
     '        if !leaves.iter().any(|&leaf| self.is_product_leaf(leaf)) {\n',
     '        if !leaves.iter().any(|&leaf| self.is_product_leaf(leaf))\n'
     '            && !' + M.format("acmul-unscoped") + '\n        {\n'),
    ("acmul-creation-order", NORMAL,
     '            .map(|&leaf| (self.structural_key(leaf), leaf))\n',
     '            .map(|&leaf| {\n'
     '                if ' + M.format("acmul-creation-order") + ' {\n'
     '                    (u128::from(leaf), leaf)\n                } else {\n'
     '                    (self.structural_key(leaf), leaf)\n                }\n            })\n'),
], "c": [
    ("catnf-halves-swapped", NORMAL,
     '                            return Some(self.mk(Op::Concat, vec![top, bottom]));\n',
     '                            return Some(if ' + M.format("catnf-halves-swapped") + ' {\n'
     '                                self.mk(Op::Concat, vec![bottom, top])\n'
     '                            } else {\n'
     '                                self.mk(Op::Concat, vec![top, bottom])\n'
     '                            });\n'),
    ("catnf-or-any-tail", NORMAL,
     '                    if self.constant(tail) == Some(0) && self.width(tail) == self.width(x) {\n',
     '                    if (self.constant(tail) == Some(0)\n'
     '                        || (' + M.format("catnf-or-any-tail") + ' && self.constant(tail).is_some()))\n'
     '                        && self.width(tail) == self.width(x)\n                    {\n'),
    ("catnf-merge-any", NORMAL,
     '                        && l1 == h2 + 1\n',
     '                        && (l1 == h2 + 1 || (' + M.format("catnf-merge-any") + ' && l1 > h2))\n'),
]}
for stage in sorted(stages):
    for name, path, old, new in EDITS[stage]:
        full = f"{root}/{path}"
        text = open(full).read()
        if text.count(old) != 1:
            sys.exit(f"{name}: anchor found {text.count(old)} times in {path}")
        open(full, "w").write(text.replace(old, new))
        print(f"applied {name}")
