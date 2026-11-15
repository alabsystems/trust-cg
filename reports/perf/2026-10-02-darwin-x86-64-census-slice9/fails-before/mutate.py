#!/usr/bin/env python3
"""Slice-9 rule mutants: apply a patch that guards each slice-9 rule behind
`TCG_S9_MUTANT=<name>`, so one test build runs every mutant (the test runner
forwards TCG_* variables to the test binary). Restore the file with
`git checkout` afterwards; never commit it.

usage: mutate.py <x86_source_bound_body.rs> [<x86_source_bound_body_slice9_tests.rs>]

Mutants (each disables or weakens one slice-9 rule; a control that the rule
exists for must fail):
  no-edge-literals      a DAG edge's machine `jcc` literals are not stated
  unguarded-items       a block's observed items are stated on every input,
                        not under the block's guard
  constant-join-guard   a join's guard is 1 (every join reached)
  first-edge-phi        a source value at a join is the first incoming
                        edge's, not chosen by the edges' guards
  machine-first-phi     a machine register at a join is the first incoming
                        edge's
  no-merged-bytes       a private byte the edges into a join leave
                        differently is the first edge's (source side)
  no-machine-merged-bytes  the same on the machine side
  merged-bool-any       a `bool` read of a merged byte is admitted whatever
                        the incoming bytes
  flags-cross-blocks    flags a predecessor's compare wrote reach the next
                        block's readers in a DAG walk
  no-escape-agreement   a join of paths on which different slots escaped is
                        admitted (the first edge's escaped set kept)
  no-mixed-roots        a root of different kinds at a join is the first
                        edge's
  no-switch-distinct    a `Switch` with two cases of one value is admitted
  no-redefinition-check a block may redefine a value some path into it
                        defined
  no-size-bounds        the block and instruction bounds are not checked
  same-edge-test        every edge of a conditional block takes the first
                        edge's test as its guard
  no-inline             a DAG's theorem keeps every single-use definition
                        (a spelling rule: the pinned digest is its control)
  no-inline-fallback    an inlined theorem that fails the structural check
                        is not re-stated without inlining
  no-cone               a DAG's theorem states every definition, not only
                        the ones its claims reach (a spelling rule)
  no-drop-identities    an inlined claim equation that is an identity is
                        kept (the theorem then falls back to the uninlined
                        spelling)
  alu-flags-cross       flags a slice-10 ALU row (`add`, `sub`, `imul`, `mul`)
                        wrote cross a block boundary, on a path and in a DAG
                        walk (the merge of slices 9 and 10)
  fixed-stride          (the test file) the sampler's constant phase steps
                        every input at the fixed stride `2 rank + 1`, not one
                        coprime with the number of constants
"""
import sys

path = sys.argv[1]
text = open(path).read()
M = 'std::env::var("TCG_S9_MUTANT").is_ok_and(|mutant| mutant == "{}")'
EDITS = [
    # The edge claims.
    ('                if let Some(literals) = conjunction(literals) {\n'
     '                    conjuncts.push(\n',
     f'                if let Some(literals) = conjunction(literals).filter(|_| !{M.format("no-edge-literals")}) {{\n'
     '                    conjuncts.push(\n'),
    # The block items' guard.
    ('            if guard == E::bv_const(1, 1) {\n'
     '                conjuncts.extend(items);\n',
     f'            if guard == E::bv_const(1, 1) || {M.format("unguarded-items")} {{\n'
     '                conjuncts.extend(items);\n'),
    # The join guard.
    ('                        define(&mut definitions, &format!("c{}", block.0), reached);\n',
     f'                        let reached = if {M.format("constant-join-guard")} {{ E::bv_const(1, 1) }} else {{ reached }};\n'
     '                        define(&mut definitions, &format!("c{}", block.0), reached);\n'),
    # Source joined values.
    ('                            if terms.iter().all(|term| *term == terms[0]) {\n',
     f'                            if terms.iter().all(|term| *term == terms[0]) || {M.format("first-edge-phi")} {{\n'),
    # Machine joined registers.
    ('                if slots.iter().all(|slot| slot.expr == head.expr) {\n',
     f'                if slots.iter().all(|slot| slot.expr == head.expr) || {M.format("machine-first-phi")} {{\n'),
    # Source merged bytes.
    ('            if alike && resolvable {\n'
     '                continue;\n'
     '            }\n',
     f'            if (alike && resolvable) || {M.format("no-merged-bytes")} {{\n'
     '                continue;\n'
     '            }\n'),
    # Machine merged bytes.
    ('            if alike {\n'
     '                continue;\n'
     '            }\n'
     '            let address = FrameAddr {\n'
     '                slot: slot as u32,\n'
     '                offset: offset as i64,\n'
     '            };\n'
     '            let joined = join_terms(\n',
     f'            if alike || {M.format("no-machine-merged-bytes")} {{\n'
     '                continue;\n'
     '            }\n'
     '            let address = FrameAddr {\n'
     '                slot: slot as u32,\n'
     '                offset: offset as i64,\n'
     '            };\n'
     '            let joined = join_terms(\n'),
    # A bool read of a merged byte.
    ('            let bool_read = brought.iter().all(|byte| match byte {\n',
     f'            let bool_read = {M.format("merged-bool-any")} || brought.iter().all(|byte| match byte {{\n'),
    # Flags at a DAG block's entry.
    ('        if *block != entry_block\n'
     '            && matches!(\n'
     '                entry.flags,\n',
     f'        if *block != entry_block && !{M.format("flags-cross-blocks")}\n'
     '            && matches!(\n'
     '                entry.flags,\n'),
    # The escaped sets at a source join.
    ('    if states.iter().any(|state| state.escaped != first.escaped) {\n',
     f'    if !{M.format("no-escape-agreement")} && states.iter().any(|state| state.escaped != first.escaped) {{\n'),
    # Mixed roots.
    ('            _ => RegValue::Mixed,\n',
     f'            _ if {M.format("no-mixed-roots")} => values[0].clone(),\n'
     '            _ => RegValue::Mixed,\n'),
    # Distinct switch cases.
    ('            if patterns.iter().collect::<HashSet<_>>().len() != patterns.len() {\n',
     f'            if !{M.format("no-switch-distinct")} && patterns.iter().collect::<HashSet<_>>().len() != patterns.len() {{\n'),
    # Redefinitions after a join.
    ('        if let Some(value) = redefined.first() {\n',
     f'        if let Some(value) = redefined.first().filter(|_| !{M.format("no-redefinition-check")}) {{\n'),
    # The size bounds.
    ('    if source.blocks.is_empty() || source.blocks.len() > MAX_BODY_BLOCKS {\n',
     f'    if source.blocks.is_empty() || (source.blocks.len() > MAX_BODY_BLOCKS && !{M.format("no-size-bounds")}) {{\n'),
    ('    if instructions > MAX_BODY_INSTRUCTIONS {\n',
     f'    if instructions > MAX_BODY_INSTRUCTIONS && !{M.format("no-size-bounds")} {{\n'),
    # Each edge's own test.
    ('            for (branch, target) in program.branches.iter().zip(&dag.successors[&block]) {\n',
     '            for (branch, target) in program.branches.iter().zip(&dag.successors[&block]) {\n'
     f'                let branch = if {M.format("same-edge-test")} {{ &program.branches[0] }} else {{ branch }};\n'),
    # Identities an inlining makes.
    ('            while let Some((dropped, true)) = drop_identities(&machine_side) {\n',
     f'            while let Some((dropped, true)) = drop_identities(&machine_side).filter(|_| !{M.format("no-drop-identities")}) {{\n'),
    # ALU flags at a block boundary (DAG entry, then the path walk).
    ('                entry.flags,\n'
     '                Flags::Compare { .. } | Flags::Test { .. } | Flags::Alu(_)\n'
     '            )\n',
     '                entry.flags,\n'
     '                Flags::Compare { .. } | Flags::Test { .. } | Flags::Alu(_)\n'
     f'            ) && !({M.format("alu-flags-cross")} && matches!(entry.flags, Flags::Alu(_)))\n'),
    ('                flags,\n'
     '                Flags::Compare { .. } | Flags::Test { .. } | Flags::Alu(_)\n'
     '            ) {\n',
     '                flags,\n'
     '                Flags::Compare { .. } | Flags::Test { .. } | Flags::Alu(_)\n'
     f'            ) && !({M.format("alu-flags-cross")} && matches!(flags, Flags::Alu(_))) {{\n'),
    # The spelling: inlining, its fallback, the cone of influence.
    ('    let inline = encoding.inline_single_use\n',
     f'    let inline = encoding.inline_single_use && !{M.format("no-inline")}\n'),
    ('    if inline && check_definitional(&obligation, &free).is_err() {\n',
     f'    if inline && !{M.format("no-inline-fallback")} && check_definitional(&obligation, &free).is_err() {{\n'),
    ('    if trimmed && encoding.cone_of_influence {\n'
     '        let by_name',
     f'    if trimmed && encoding.cone_of_influence && !{M.format("no-cone")} {{\n'
     '        let by_name'),
]
for old, new in EDITS:
    count = text.count(old)
    if count != 1:
        sys.exit(f'edit anchor found {count} times:\n{old}')
    text = text.replace(old, new)
open(path, 'w').write(text)
print(f'applied {len(EDITS)} edits')

# The sampler of the library gate (the slice-9 test file).
TEST_EDITS = [
    ('            let stride = coprime_stride(2 * rank + 1, n);\n',
     f'            let stride = if {M.format("fixed-stride")} {{ 2 * rank + 1 }} else {{ coprime_stride(2 * rank + 1, n) }};\n'),
]
if len(sys.argv) > 2:
    tests = sys.argv[2]
    text = open(tests).read()
    for old, new in TEST_EDITS:
        count = text.count(old)
        if count != 1:
            sys.exit(f'edit anchor found {count} times:\n{old}')
        text = text.replace(old, new)
    open(tests, 'w').write(text)
    print(f'applied {len(TEST_EDITS)} test-file edits')
