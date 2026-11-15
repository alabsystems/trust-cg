#!/usr/bin/env python3
"""Slice-7 walk-rule mutants: apply (or with --check, verify the anchors of) a
patch that guards each slice-7 rule behind `TCG_S7_MUTANT=<name>`, so one test
build runs every mutant (the test runner forwards TCG_* variables to the test
binary). Restore the file with `git checkout` afterwards; never commit it.

usage: mutate.py <x86_source_bound_body.rs>

Mutants (each disables one rule on BOTH sides, so a correct fixture still
holds and only the controls that rule exists for can notice):
  no-redefine   a call leaves the escaped slots' bytes as they were
  no-observe    a call observes no escaped slot's contents
  no-retention  a call reads and redefines only the slots passed to it
  no-frame-check  a machine argument may pass any private address
  no-taint      an incoming access through an escape-derived address is admitted
"""
import sys

path = sys.argv[1]
text = open(path).read()
M = 'std::env::var("TCG_S7_MUTANT").is_ok_and(|mutant| mutant == "{}")'
EDITS = [
    # Source: retention (the escaped set is this call's slots only).
    ('                escaped.extend(frame_args.iter().flatten().map(|address| address.slot));\n',
     f'                if {M.format("no-retention")} {{ escaped.clear(); }}\n'
     '                escaped.extend(frame_args.iter().flatten().map(|address| address.slot));\n'),
    # Source: observation.
    ('                let slot_reads: Vec<(u32, Vec<Option<SlotByte>>)> = escaped\n'
     '                    .iter()\n',
     '                let slot_reads: Vec<(u32, Vec<Option<SlotByte>>)> = escaped\n'
     '                    .iter()\n'
     f'                    .filter(|_| !{M.format("no-observe")})\n'),
    # Source: redefinition.
    ('                    slot_bytes[*slot as usize].fill(Some(SlotByte::Call(site)));\n',
     f'                    if !{M.format("no-redefine")} {{ slot_bytes[*slot as usize].fill(Some(SlotByte::Call(site))); }}\n'),
    # Source: taint (load, store).
    ('                        if tainted.contains(&inst.args[0]) {\n',
     f'                        if tainted.contains(&inst.args[0]) && !{M.format("no-taint")} {{\n'),
    ('                        if tainted.contains(&address) {\n',
     f'                        if tainted.contains(&address) && !{M.format("no-taint")} {{\n'),
    # Machine: frame check.
    ('                                if found != expected {\n',
     f'                                if found != expected && !{M.format("no-frame-check")} {{\n'),
    # Machine: retention (clear before this call's slots are added).
    ('                    let mut args = Vec::with_capacity(call.args.len());\n'
     '                    let mut arg_affine = Vec::with_capacity(call.args.len());\n'
     '                    for (argument, (((_, ty), expected), root)) in call\n',
     f'                    if {M.format("no-retention")} {{ escaped.clear(); }}\n'
     '                    let mut args = Vec::with_capacity(call.args.len());\n'
     '                    let mut arg_affine = Vec::with_capacity(call.args.len());\n'
     '                    for (argument, (((_, ty), expected), root)) in call\n'),
    # Machine: observation.
    ('                    let mut slots: Vec<E> = Vec::new();\n'
     '                    for slot in &escaped {\n',
     '                    let mut slots: Vec<E> = Vec::new();\n'
     f'                    for slot in escaped.iter().filter(|_| !{M.format("no-observe")}) {{\n'),
    # Machine: redefinition.
    ('                    for slot in &escaped {\n'
     '                        for (offset, byte) in stack[*slot as usize].iter_mut().enumerate() {\n',
     f'                    for slot in escaped.iter().filter(|_| !{M.format("no-redefine")}) {{\n'
     '                        for (offset, byte) in stack[*slot as usize].iter_mut().enumerate() {\n'),
]
for old, new in EDITS:
    count = text.count(old)
    assert count == 1, (count, old)
    text = text.replace(old, new)
open(path, 'w').write(text)
print(f'applied {len(EDITS)} edits')
