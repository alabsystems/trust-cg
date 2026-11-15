#!/usr/bin/env python3
"""Render the robustness probe's `ROB17` table as Markdown, with totals.

usage: table.py <probe log> [replay]"""
import re
import sys

log = sys.argv[1]
replay = len(sys.argv) > 2
rows = []
for line in open(log, errors='replace'):
    m = re.match(r'^ROB17 (C\d+ .*?)\s+(\d+ \|.*)$', line.rstrip('\n'))
    if not m:
        continue
    nums = [int(x) for x in re.findall(r'\d+', m.group(2))]
    if len(nums) != 20:
        continue
    rows.append((m.group(1).strip(), nums))
# n, unsup, mismatch, theorem, sampled, ay_ce, ay_ce_not_sampled, ay_valid, ay_other, credited,
# wrong, w_unsup, w_mismatch, w_refuted, w_credited, correct_refuted, gt_na, und, und_ref, und_holds
total = [sum(r[1][i] for r in rows) for i in range(20)]
if replay:
    print('| Class | Mutants | Theorem | Sampler refutes | AY countermodel | AY countermodel the sampler missed | AY certifies | Credited | GT-wrong: refused / mismatch / refuted / **credited** | Undecided: refuted / **holds** |')
    print('| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |')
    for name, n in rows + [('**all**', total)]:
        print(f'| {name} | {n[0]} | {n[3]} | {n[4]} | {n[5]} | {n[6]} | {n[7]} | {n[9]} | {n[10]}: {n[11]} / {n[12]} / {n[13]} / **{n[14]}** | {n[17]}: {n[18]} / **{n[19]}** |')
else:
    print('| Class | Mutants | Owner refuses | Named mismatch | Theorem | Sampler refutes | GT-wrong: refused / mismatch / refuted / **not refuted** | GT-correct but refuted | GT n/a | Undecided: refuted / **holds** |')
    print('| --- | ---: | ---: | ---: | ---: | ---: | --- | ---: | ---: | --- |')
    for name, n in rows + [('**all**', total)]:
        print(f'| {name} | {n[0]} | {n[1]} | {n[2]} | {n[3]} | {n[4]} | {n[10]}: {n[11]} / {n[12]} / {n[13]} / **{n[14]}** | {n[15]} | {n[16]} | {n[17]}: {n[18]} / **{n[19]}** |')
