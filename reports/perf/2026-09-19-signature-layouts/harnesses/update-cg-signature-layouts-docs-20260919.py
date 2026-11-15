from pathlib import Path
import json,subprocess
r=Path('/home/ayates/trust-cg-soundness-20260914');p=Path('/home/ayates/trust-cg-output-byte-binding-20260917')
assert json.loads((r/'cg-signature-layouts-integration-first/results.json').read_text())['passed']
assert json.loads((r/'cg-signature-layouts-frontend-third/results.json').read_text())['passed']
assert json.loads((r/'cg-signature-layouts-capture-fourth/results.json').read_text())['passed']
f=p/'publish/DECISIONS.md';s=f.read_text().replace('92628062f11a1477163e82927c1b7eb236ca5f19','25422eb43e61a04376db66ae3a9720e3bdfd69a1').replace('adopted with canonical byte Copy replay, 2026-09-19','adopted with typed pointer and declared tuple reflection, 2026-09-19');f.write_text(s)
f=p/'docs/core-byte-store-replay.md';s=f.read_text();s=s[:s.index('The current dependency family is')]+'''The current dependency family is TrustIR `25422eb4` / Clean `55a85e99`.
Clean's canonical byte dispatcher checks and executes `Copy`; TrustIR reflects
its actual operands, the four thin reference/raw-pointer types and producer
specified tuple allocation layouts. Tuple values in SSA remain unsupported.
The [signature layout integration record](../reports/perf/2026-09-19-signature-layouts/README.md)
retains the pin transaction, canonical Store/Return replay, frontend builds and
fresh captures. The direct optional Clean dependencies remain coherent with
all three lockfiles; AY remains `849c19fa`.

The Rust bridge preserves the five RefMut-to-Ptr extractions as explicit typed
casts. It now supplies target facts and, for the restricted C signature profile,
actual rustc pointee offsets, size and alignment. Structural tuple collisions,
opaque aggregate shells and unsupported uses receive no invented descriptor.
Lowering retains validated descriptors through pointer transport; by-value tuple
layout operations remain refused. Batching declines these modules until its
structural interner can preserve their layouts.

Fresh O0–O3 writer modules differ from the previous typed-Copy captures only
in target and tuple metadata. Their descriptor has type-table ID 5, size 40,
alignment 8 and offsets 0/8/16/24/32. The complete O1 module now reflects into
Core. This is data reconstruction, not a checked execution claim for the writer.
The O0 module retains five discharged bounds claims without certificates or
matching sites and its fifteen validation errors; Core still rejects it.
All four native writer compilations still fail the frame/opcode proof check.
Caller ownership, Rust reference validity, whole-writer replay and the complete
source-to-native proof remain open. All L01–L14 remain OPEN.
''';f.write_text(s)
f=p/'docs/canonical-byte-arithmetic-proof-plan-2026-09-10.md';s=f.read_text().replace('TrustIR `92628062` family','TrustIR `25422eb4` family').replace('Exact instruction reflection preserves BinOp and Copy within its supported type profile; references/tuples remain unsupported.','Exact reflection preserves BinOp, Copy, thin reference/raw-pointer carriers and declared tuple allocation layouts; tuple SSA values remain unsupported.');f.write_text(s)
f=p/'docs/aarch64-completion-audit-2026-09-17.md';s=f.read_text().replace('| L08-P3 | L08 | both | M | OPEN | Faithful Copy constructor and reflection are absent (explicit refusal) |','| L08-P3 | L08 | both | M | PARTIAL | Copy replay needs universal laws and frontend adequacy |').replace('### L08-P3 Faithful Copy constructor and reflection are absent (explicit refusal)','### L08-P3 Copy replay needs universal laws and frontend adequacy')
start=s.index('### L08-P3 ');end=s.index('### L08-P4 ',start);part=s[start:end];marker='Platform: both · Effort: M · Category: implementation\n\n';assert marker in part
part=part.replace(marker,marker+'''**2026-09-19 layout integration:** TrustIR `25422eb4` adds checked pointer
carrier reflection and actual nominal tuple-layout identities, qualified by 124
upstream tests. CG now adopts it and emits rustc target/layout facts for a
bounded signature profile. Its [integration record](../reports/perf/2026-09-19-signature-layouts/README.md)
retains 15 actual frontend captures, independent field-layout measurements,
Core reflection of the complete O1 writer and the unchanged O0 proof refusals.
Pointer-only lowering preserves descriptors; merge/layout-sensitive paths
refuse unsupported uses. Universal Copy laws, frontend adequacy, ownership and
native memory/frame proof composition remain open. Earlier absence findings
below describe the previous revisions.

''',1);s=s[:start]+part+s[end:];f.write_text(s)
report=p/'reports/perf/2026-09-19-signature-layouts';report.mkdir();(report/'README.md').write_text((r/'cg-signature-layouts-report-draft.md').read_text())
subprocess.run(['python3','scripts/check_documentation.py','--write'],cwd=p,check=True)
subprocess.run(['python3','scripts/check_documentation.py','--check'],cwd=p,check=True)
