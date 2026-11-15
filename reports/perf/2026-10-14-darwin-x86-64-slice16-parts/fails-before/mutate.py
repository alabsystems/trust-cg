#!/usr/bin/env python3
"""Slice-16 rule mutants: guard each slice-16 rule behind
`TCG_S16_MUTANT=<name>`, so one test build runs every mutant (the test runner
forwards TCG_* variables to the test binary). Restore the files with
`git checkout` afterwards; never commit them.

usage: mutate.py <worktree root>

Mutants (each disables one slice-16 rule; a control that the rule exists for
must fail):
  no-cut-relation          no relation is stated on any edge into a cut
  relation-first-edge-only the relation is stated only on the first edge
                           (least source block) into each cut
  carry-first-edge         an unpaired machine register starts as the first
                           edge's term, whatever the other edges leave
  no-byte-items            a cut's bytes are inputs on both sides but their
                           relation is not stated
  machine-bytes-unchecked  a byte the machine writes and the cut does not
                           relate is not refused (it starts unwritten)
  upper-zero-unchecked     an item's register is assumed zero above the item
                           whatever an edge leaves there
  part-credit-any          a theorem in parts is credited when any part is
                           Valid
  no-inventory-check       the parts are replayed although their inventory
                           does not check against the statement
  parts-incomplete-export  an export's parts are published without the
                           inventory check
  split-small              every function is stated in parts (within the
                           single-query bounds too)
  split-flags              a mid-block point is a clean split although a flag
                           reader follows it before a writer
"""
import sys

root = sys.argv[1]
M = 'std::env::var("TCG_S16_MUTANT").is_ok_and(|mutant| mutant == "{}")'
SPLIT = 'crates/trust-cg-verify/src/x86_source_bound_body/split.rs'
OWNER = 'crates/trust-cg-verify/src/x86_source_bound_body.rs'
REQUEST = 'crates/trust-cg-verify/src/function_request.rs'
EDITS = [
    (SPLIT,
     '    let mut pairs = Vec::new();\n'
     '    let walked = std::iter::once((&exits.0, BoolArguments::PsAbi))\n'
     '        .chain(exits.1.as_ref().map(|exit| (exit, BoolArguments::Clean32)));\n'
     '    for (exit, convention) in walked {\n'
     '        for (i, ((value, _), root)) in cut.items.iter().zip(roots).enumerate() {\n',
     '    let mut pairs = Vec::new();\n'
     f'    if {M.format("no-cut-relation")} {{\n'
     '        return Ok(pairs);\n'
     '    }\n'
     '    let walked = std::iter::once((&exits.0, BoolArguments::PsAbi))\n'
     '        .chain(exits.1.as_ref().map(|exit| (exit, BoolArguments::Clean32)));\n'
     '    for (exit, convention) in walked {\n'
     '        for (i, ((value, _), root)) in cut.items.iter().zip(roots).enumerate() {\n'),
    (OWNER,
     '                        Some(cuts) => split::split_relation(\n',
     f'                        Some(_) if {M.format("relation-first-edge-only")}\n'
     '                            && loops\n'
     '                                .regions\n'
     '                                .iter()\n'
     '                                .flat_map(|region| region.cuts.keys())\n'
     '                                .filter(|(_, to)| to == target)\n'
     '                                .map(|(from, _)| *from)\n'
     '                                .min()\n'
     '                                != Some(block) =>\n'
     '                        {\n'
     '                            Vec::new()\n'
     '                        }\n'
     '                        Some(cuts) => split::split_relation(\n'),
    (SPLIT,
     '        let joined = on_edges\n'
     '            .into_iter()\n'
     '            .reduce(|a, b| match (a, b) {\n',
     f'        let joined = if {M.format("carry-first-edge")} {{\n'
     '            on_edges.into_iter().next().unwrap_or(CutReg::Absent)\n'
     '        } else {\n'
     '            on_edges\n'
     '            .into_iter()\n'
     '            .reduce(|a, b| match (a, b) {\n'),
    (SPLIT,
     '            .unwrap_or(CutReg::Absent);\n'
     '        regs.push((root, joined));\n',
     '            .unwrap_or(CutReg::Absent)\n'
     '        };\n'
     '        regs.push((root, joined));\n'),
    (SPLIT,
     '        for run in runs {\n'
     '            let source_part: Vec<Option<SlotByte>> = run\n',
     f'        for run in runs.into_iter().filter(|_| !{M.format("no-byte-items")}) {{\n'
     '            let source_part: Vec<Option<SlotByte>> = run\n'),
    (SPLIT,
     '                    (None, Some(_)) => {\n'
     '                        return Err(no_claim(format!(\n'
     '                            "the machine writes private stack slot',
     '                    (None, Some(_)) => {\n'
     f'                        if {M.format("machine-bytes-unchecked")} {{\n'
     '                            continue;\n'
     '                        }\n'
     '                        return Err(no_claim(format!(\n'
     '                            "the machine writes private stack slot'),
    (SPLIT,
     '        if !clean {\n'
     '            wide.insert(i);\n'
     '        }\n',
     f'        if !clean && !{M.format("upper-zero-unchecked")} {{\n'
     '            wide.insert(i);\n'
     '        }\n'),
    (REQUEST,
     '    for (k, (verdict, why)) in outcomes.into_iter().enumerate() {\n',
     f'    if {M.format("part-credit-any")}\n'
     '        && outcomes\n'
     '            .iter()\n'
     '            .any(|(verdict, _)| matches!(verdict, Some(VerificationResult::Valid)))\n'
     '    {\n'
     '        return (Some(VerificationResult::Valid), None);\n'
     '    }\n'
     '    for (k, (verdict, why)) in outcomes.into_iter().enumerate() {\n'),
    (REQUEST,
     '    let refusal = inventory\n'
     '        .err()\n'
     '        .map(',
     '    let refusal = inventory\n'
     '        .err()\n'
     f'        .filter(|_| !{M.format("no-inventory-check")})\n'
     '        .map('),
    (REQUEST,
     '                self.check_x86_body_parts()?;\n',
     f'                if !{M.format("parts-incomplete-export")} {{\n'
     '                    self.check_x86_body_parts()?;\n'
     '                }\n'),
    (SPLIT,
     '    source.blocks.len() <= MAX_BODY_BLOCKS\n'
     '        && instructions <= MAX_BODY_INSTRUCTIONS\n'
     '        && machine.blocks.len() <= MAX_MACHINE_BLOCKS\n'
     '        && rows <= MAX_MACHINE_ROWS\n',
     f'    !{M.format("split-small")}\n'
     '        && source.blocks.len() <= MAX_BODY_BLOCKS\n'
     '        && instructions <= MAX_BODY_INSTRUCTIONS\n'
     '        && machine.blocks.len() <= MAX_MACHINE_BLOCKS\n'
     '        && rows <= MAX_MACHINE_ROWS\n'),
    (SPLIT,
     '        if reads_flags(inst.opcode) && !flags_written {\n',
     f'        if reads_flags(inst.opcode) && !flags_written && !{M.format("split-flags")} {{\n'),
]
texts = {}
for path, old, new in EDITS:
    full = f'{root}/{path}'
    text = texts.get(full) or open(full).read()
    count = text.count(old)
    if count != 1:
        sys.exit(f'{path}: edit anchor found {count} times:\n{old}')
    texts[full] = text.replace(old, new)
for full, text in texts.items():
    open(full, 'w').write(text)
print(f'applied {len(EDITS)} edits to {len(texts)} files')
