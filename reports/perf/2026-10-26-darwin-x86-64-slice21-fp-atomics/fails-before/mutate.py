#!/usr/bin/env python3
"""Slice-21 rule mutants: guard each slice-21 rule behind
`TCG_S21_MUTANT=<name>`, so one test build runs every mutant (the test runner
forwards TCG_* variables to the test binary). Restore the files with
`git checkout` afterwards; never commit them.

usage: mutate.py <worktree root>

Mutants (each breaks one slice-21 rule; a control the rule exists for must
fail):
 OD-198, rounding operations as paired events
  key-no-format          every SSE arithmetic row is keyed binary64 (the key
                         without its format)
  key-no-rounding        a key pairs whatever its rounding direction
  key-no-operation       a key pairs whatever its operation
  no-operand-claims      a pairing observes no operand (the result shared on
                         the key alone)
  uint-no-top-bit        an unsigned conversion pairs with a signed one
                         without its bit 63 claimed clear
  stamp-ignored          a row pairs whatever instruction its stamp names
  ucomis-pf-zero         `ucomisd` leaves PF clear (unordered not signalled)
  fcmp-olt-as-ult        LIR `LessThan` holds of an unordered pair
  cvtt-saturating        `cvttsd2si` saturates out of range instead of the
                         integer indefinite
 OD-199, the saturating conversion
  saturation-dropped     `FcvtToInt` is its event alone (raw `fptosi`)
 OD-200, an abstract theorem's satisfying model
  fp-abstract-never      no theorem is FP-abstract: its sat is a refutation
 OD-201, the I128 atomic load and the atomic exchange
  cmpxchg16b-halves-swapped  the pseudo row's RAX is the high half
  rbx-refused            the pseudo row's RBX write is a preserved write
  cas-result-from-r10    the exchange's result is its operand
  pseudo-pairs-plain     a pseudo-lowered access pairs with a plain `mov`
  pseudo-any-access      a pseudo row pairs with any source access
"""
import sys

root = sys.argv[1]
M = 'std::env::var("TCG_S21_MUTANT").is_ok_and(|mutant| mutant == "{}")'
OWNER = 'crates/trust-cg-verify/src/x86_source_bound_body.rs'
VERIFIER = 'crates/trust-cg-verify/src/x86_64_function_verifier.rs'
EDITS = [
    ("key-no-format", OWNER,
     '    Some(FloatKey {\n        op,\n        format,\n        rounding,\n    })\n}\n',
     '    let format = if ' + M.format("key-no-format") + ' && !matches!(op, FloatEventOp::FromInt64 | FloatEventOp::ToInt64) {\n'
     '        Carrier::F64\n    } else {\n        format\n    };\n'
     '    Some(FloatKey {\n        op,\n        format,\n        rounding,\n    })\n}\n'),
    ("key-no-rounding", OWNER,
     '    fn pairs_with(self, machine: FloatKey) -> bool {\n        self == machine\n    }\n',
     '    fn pairs_with(self, machine: FloatKey) -> bool {\n'
     '        (self.op == machine.op || ' + M.format("key-no-operation") + ')\n'
     '            && self.format == machine.format\n'
     '            && (self.rounding == machine.rounding || ' + M.format("key-no-rounding") + ')\n'
     '    }\n'),
    ("no-operand-claims", OWNER,
     '                            let mut args = operands.clone();\n',
     '                            let mut args = if ' + M.format("no-operand-claims") + ' {\n'
     '                                Vec::new()\n                            } else {\n'
     '                                operands.clone()\n                            };\n'),
    ("no-operand-claims", OWNER,
     '                        let mut items: Vec<(E, bool)> = float\n                            .args\n                            .iter()\n',
     '                        let mut items: Vec<(E, bool)> = float\n                            .args\n                            .iter()\n'
     '                            .filter(|_| !' + M.format("no-operand-claims") + ')\n'),
    ("uint-no-top-bit", OWNER,
     '                            if source.unsigned {\n                                args.push(E::bv_const(0, 1));\n',
     '                            if source.unsigned && !' + M.format("uint-no-top-bit") + ' && !' + M.format("no-operand-claims") + ' {\n'
     '                                args.push(E::bv_const(0, 1));\n'),
    ("uint-no-top-bit", OWNER,
     '                        if float.unsigned {\n',
     '                        if float.unsigned && !' + M.format("uint-no-top-bit") + ' && !' + M.format("no-operand-claims") + ' {\n'),
    ("stamp-ignored", OWNER,
     '                                && stamp.is_none_or(|stamp| stamp == (source.block, source.index))\n',
     '                                && (' + M.format("stamp-ignored") + '\n'
     '                                    || stamp.is_none_or(|stamp| stamp == (source.block, source.index)))\n'),
    ("ucomis-pf-zero", OWNER,
     '            pf: Some(unordered.clone()),\n',
     '            pf: Some(if ' + M.format("ucomis-pf-zero") + ' {\n'
     '                E::bool_const(false)\n            } else {\n                unordered.clone()\n            }),\n'),
    ("fcmp-olt-as-ult", OWNER,
     '            FloatCC::LessThan => less,\n',
     '            FloatCC::LessThan if ' + M.format("fcmp-olt-as-ult") + ' => unordered.or_expr(less),\n'
     '            FloatCC::LessThan => less,\n'),
    ("cvtt-saturating", OWNER,
     '                        FloatEventOp::ToInt64 => E::ite(\n',
     '                        FloatEventOp::ToInt64 if ' + M.format("cvtt-saturating") + ' => {\n'
     '                            saturating_f64_to_i64(&operands[0], leaf)\n                        }\n'
     '                        FloatEventOp::ToInt64 => E::ite(\n'),
    ("saturation-dropped", OWNER,
     '                    saturating_f64_to_i64(&value(v), E::var(float_event_name(*site), 64))\n',
     '                    if ' + M.format("saturation-dropped") + ' {\n'
     '                        E::var(float_event_name(*site), 64)\n                    } else {\n'
     '                        saturating_f64_to_i64(&value(v), E::var(float_event_name(*site), 64))\n'
     '                    }\n'),
    ("fp-abstract-never", OWNER,
     '    pub fn is_fp_abstract(&self) -> bool {\n        self.fp_abstract\n    }\n',
     '    pub fn is_fp_abstract(&self) -> bool {\n        self.fp_abstract && !' + M.format("fp-abstract-never") + '\n    }\n'),
    ("cmpxchg16b-halves-swapped", OWNER,
     '                let high = halves.pop().expect("two halves");\n                let low = halves.pop().expect("two halves");\n',
     '                let high = halves.pop().expect("two halves");\n                let low = halves.pop().expect("two halves");\n'
     '                let (low, high) = if ' + M.format("cmpxchg16b-halves-swapped") + ' {\n'
     '                    (high, low)\n                } else {\n                    (low, high)\n                };\n'),
    ("rbx-refused", OWNER,
     '                vec![\n                    (Root::Physical(RAX), low),\n',
     '                if ' + M.format("rbx-refused") + ' {\n'
     '                    return Err(mismatch(X86BodyMismatch::PreservedWrite {\n'
     '                        row: row.ordinal,\n                        register: ROOT_NAMES[RBX as usize],\n'
     '                    }));\n                }\n'
     '                vec![\n                    (Root::Physical(RAX), low),\n'),
    ("cas-result-from-r10", OWNER,
     '                let old = widen(E::var(memory_load_name(load), bits), bits);\n',
     '                let old = if ' + M.format("cas-result-from-r10") + ' {\n'
     '                    widen(low(source.expr.clone(), bits), bits)\n                } else {\n'
     '                    widen(E::var(memory_load_name(load), bits), bits)\n                };\n'),
    ("pseudo-pairs-plain", OWNER,
     '                    if source_access.pseudo.is_some() {\n',
     '                    if source_access.pseudo.is_some() && !' + M.format("pseudo-pairs-plain") + ' {\n'),
    ("pseudo-any-access", OWNER,
     '                if source_access.pseudo != Some(expected) {\n',
     '                if source_access.pseudo != Some(expected) && !' + M.format("pseudo-any-access") + ' {\n'),
]
for name, path, old, new in EDITS:
    full = f"{root}/{path}"
    text = open(full).read()
    count = text.count(old)
    if count != 1:
        sys.exit(f"{name}: anchor found {count} times in {path}")
    open(full, "w").write(text.replace(old, new))
    print(f"applied {name}")
