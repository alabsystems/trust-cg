#!/usr/bin/env python3
"""Slice-13 rule mutants: guard each slice-13 rule of the owner behind
`TCG_S13_MUTANT=<name>`, so one test build runs every mutant (the test runner
forwards TCG_* variables to the test binary). Restore the file with
`git checkout` afterwards; never commit it.

usage: mutate.py <x86_source_bound_body.rs>

Mutants (each disables or weakens one slice-13 rule; a control the rule
exists for must fail):
  store-no-escape         an address stored to incoming memory does not
                          make its slot escape (source and machine)
  no-escape-closure       a slot that escapes does not take along the slots
                          whose addresses it holds (source and machine)
  escaped-store-no-escape an address stored into an escaped slot does not
                          make its slot escape (source and machine)
  address-no-offset       a stored address's term drops its offset
  one-slot-name           every slot's address is the same free input
  partial-address-read    a partial read of a stored address reads bytes
  escape-sets-unchecked   the machine's escaped slots at a call are not
                          compared with the source's
  stack-param-at-8        the incoming stack area starts at [rbp + 8]
  rbp-any-disp            any RBP read at or above 16 is the first stack
                          parameter
  stack-arg-at-8          the outgoing argument area starts at [rsp + 8]
  stack-args-unobserved   stack arguments are not observed
  unwritten-outgoing-ok   an unwritten outgoing byte reads as zero
  rsp-unbalanced          any `add rsp` closes the outgoing area
  memset-is-memcpy        `Memset` calls `memcpy`
  atomic-pairs-plain      an atomic source access pairs with any row
  seqcst-store-admitted   a SeqCst atomic store is admitted
  join-first-escapes      a DAG join keeps the first edge's escaped slots,
                          not their union (run on the slice-9 filter too)
  rsp-open-at-return      a return with the outgoing area open is admitted
  bool-byte-refused       a bool read of another store's byte is refused
"""
import sys

path = sys.argv[1]
text = open(path).read()
M = 'std::env::var("TCG_S13_MUTANT").is_ok_and(|mutant| mutant == "{}")'


def on(name):
    return M.format(name)


EDITS = [
    # store-no-escape (source)
    ('''                        if let Some(stored) = stored_address {
                            escape_source(escaped, slot_bytes, [stored.slot]);
                        }''',
     f'''                        if let Some(stored) = stored_address
                            && !{on("store-no-escape")}
                        {{
                            escape_source(escaped, slot_bytes, [stored.slot]);
                        }}'''),
    # store-no-escape (machine)
    ('''                            escape_machine(escaped, stack.as_slice(), [stored.slot]);
                            bound_rows.push(row.ordinal);
                            continue;
                        }
                        (false, AccessKind::Store(_)) => {''',
     f'''                            if !{on("store-no-escape")} {{
                                escape_machine(escaped, stack.as_slice(), [stored.slot]);
                            }}
                            bound_rows.push(row.ordinal);
                            continue;
                        }}
                        (false, AccessKind::Store(_)) => {{'''),
    # no-escape-closure (source)
    ('''        if escaped.insert(slot) {
            pending.extend(
                slot_bytes[slot as usize]''',
     f'''        if escaped.insert(slot) && !{on("no-escape-closure")} {{
            pending.extend(
                slot_bytes[slot as usize]'''),
    # no-escape-closure (machine)
    ('''        if escaped.insert(slot) {
            pending.extend(
                stack[slot as usize]''',
     f'''        if escaped.insert(slot) && !{on("no-escape-closure")} {{
            pending.extend(
                stack[slot as usize]'''),
    # escaped-store-no-escape (source)
    ('''                        if let Some(stored) = stored_address
                            && escaped.contains(&address.slot)
                        {''',
     f'''                        if let Some(stored) = stored_address
                            && escaped.contains(&address.slot)
                            && !{on("escaped-store-no-escape")}
                        {{'''),
    # escaped-store-no-escape (machine)
    ('''                        if escaped.contains(&address.slot) {
                            escape_machine(escaped, stack.as_slice(), [stored.slot]);
                        }''',
     f'''                        if escaped.contains(&address.slot) && !{on("escaped-store-no-escape")} {{
                            escape_machine(escaped, stack.as_slice(), [stored.slot]);
                        }}'''),
    # address-no-offset
    ('''    match address.offset {
        0 => base,
        offset => base.bvadd(E::bv_const(offset as u64, 64)),
    }''',
     f'''    match address.offset {{
        _ if {on("address-no-offset")} => base,
        0 => base,
        offset => base.bvadd(E::bv_const(offset as u64, 64)),
    }}'''),
    # one-slot-name
    ('''fn slot_address_name(slot: u32) -> String {
    format!("slot{slot}")
}''',
     f'''fn slot_address_name(slot: u32) -> String {{
    if {on("one-slot-name")} {{
        return "slot0".into();
    }}
    format!("slot{{slot}}")
}}'''),
    # partial-address-read (machine: a partial read reads the bytes' term)
    ('''                    if form.load
                        && stack[slot][range.clone()]
                            .iter()
                            .any(|byte| byte.as_ref().is_some_and(|byte| byte.frame.is_some()))
                    {''',
     f'''                    if form.load
                        && !({on("partial-address-read")} && form.bytes != 8)
                        && stack[slot][range.clone()]
                            .iter()
                            .any(|byte| byte.as_ref().is_some_and(|byte| byte.frame.is_some()))
                    {{'''),
    # escape-sets-unchecked
    ('''                    if !escaped
                        .iter()
                        .copied()
                        .eq(call.slot_reads.iter().map(|(slot, _)| *slot))
                    {''',
     f'''                    if !{on("escape-sets-unchecked")}
                        && !escaped
                            .iter()
                            .copied()
                            .eq(call.slot_reads.iter().map(|(slot, _)| *slot))
                    {{'''),
    # stack-param-at-8
    ('''    let (mut integer, mut sse, mut stack) = (0usize, 0usize, 16i32);''',
     f'''    let (mut integer, mut sse, mut stack) =
        (0usize, 0usize, if {on("stack-param-at-8")} {{ 8i32 }} else {{ 16i32 }});'''),
    # rbp-any-disp
    ('''                    let parameter = program.params.iter().position(|param| {
                        param.stack.is_some_and(|stack| i64::from(stack) == disp)
                    });''',
     f'''                    let parameter = program.params.iter().position(|param| {{
                        param.stack.is_some_and(|stack| {{
                            i64::from(stack) == disp || ({on("rbp-any-disp")} && disp >= 16)
                        }})
                    }});'''),
    # stack-arg-at-8
    ('''    let (mut integer, mut sse, mut offset) = (0usize, 0usize, 0i32);''',
     f'''    let (mut integer, mut sse, mut offset) =
        (0usize, 0usize, if {on("stack-arg-at-8")} {{ 8i32 }} else {{ 0i32 }});'''),
    # stack-args-unobserved (source)
    ('''                    let stack_arguments = call.stack_args.iter().filter_map(|(arg, _)| match arg {
                        CallArg::Scalar(value, ty) => {''',
     f'''                    let stack_arguments = call.stack_args.iter().filter_map(|(arg, _)| match arg {{
                        CallArg::Scalar(..) if {on("stack-args-unobserved")} => None,
                        CallArg::Scalar(value, ty) => {{'''),
    # stack-args-unobserved (machine)
    ('''                                let part: Vec<Option<MachineByte>> =
                                    written.into_iter().cloned().map(Some).collect();
                                args.push(''',
     f'''                                let part: Vec<Option<MachineByte>> =
                                    written.into_iter().cloned().map(Some).collect();
                                if !{on("stack-args-unobserved")} {{ args.push('''),
    ('''                                    concat_bytes(
                                        part.iter()
                                            .map(|byte| byte.as_ref().expect("written").expr())
                                            .collect(),
                                    )
                                }));''',
     '''                                    concat_bytes(
                                        part.iter()
                                            .map(|byte| byte.as_ref().expect("written").expr())
                                            .collect(),
                                    )
                                })); }'''),
    # unwritten-outgoing-ok
    ('''                        let written: Option<Vec<&MachineByte>> =
                            part.iter().map(Option::as_ref).collect();''',
     f'''                        let zero = MachineByte {{
                            term: E::bv_const(0, 8),
                            width: 8,
                            byte: 0,
                            affine: None,
                            frame: None,
                        }};
                        let written: Option<Vec<&MachineByte>> = part
                            .iter()
                            .map(|byte| byte.as_ref().or(({on("unwritten-outgoing-ok")}).then_some(&zero)))
                            .collect();'''),
    # rsp-unbalanced
    ('''                (X86Opcode::AddRI, Some(area)) if area.len() as i64 == *bytes => {''',
     f'''                (X86Opcode::AddRI, Some(area))
                    if area.len() as i64 == *bytes || {on("rsp-unbalanced")} =>
                {{'''),
    # memset-is-memcpy
    ('''                            _ => ("memset", Carrier::I32),''',
     f'''                            _ if {on("memset-is-memcpy")} => ("memcpy", Carrier::I32),
                            _ => ("memset", Carrier::I32),'''),
    # atomic-pairs-plain
    ('''                    if source_access.atomic != inst.proof_origin.is_some() {''',
     f'''                    if source_access.atomic != inst.proof_origin.is_some()
                        && !{on("atomic-pairs-plain")}
                    {{'''),
    # seqcst-store-admitted
    ('''            Ordering::Relaxed | Ordering::Release => {}
            Ordering::SeqCst => {''',
     f'''            Ordering::Relaxed | Ordering::Release => {{}}
            Ordering::SeqCst if {on("seqcst-store-admitted")} => {{}}
            Ordering::SeqCst => {{'''),
    # join-first-escapes (source and machine)
    ('''        states
            .iter()
            .flat_map(|state| state.escaped.iter().copied()),''',
     f'''        states
            .iter()
            .take(if {on("join-first-escapes")} {{ 1 }} else {{ usize::MAX }})
            .flat_map(|state| state.escaped.iter().copied()),'''),
    ('''        incoming
            .iter()
            .flat_map(|(_, state)| state.escaped.iter().copied()),''',
     f'''        incoming
            .iter()
            .take(if {on("join-first-escapes")} {{ 1 }} else {{ usize::MAX }})
            .flat_map(|(_, state)| state.escaped.iter().copied()),'''),
    # rsp-open-at-return
    ('''                    if outgoing.is_some() {''',
     f'''                    if outgoing.is_some() && !{on("rsp-open-at-return")} {{'''),
    # bool-byte-refused
    ('''        ) || matches!(self, Self::Stored(byte) if byte.carrier != Carrier::B1)''',
     f'''        ) || (!{on("bool-byte-refused")}
            && matches!(self, Self::Stored(byte) if byte.carrier != Carrier::B1))'''),
]

for old, new in EDITS:
    count = text.count(old)
    if count != 1:
        sys.exit(f"edit anchor found {count} times:\n{old}")
    text = text.replace(old, new)
open(path, 'w').write(text)
print(f"applied {len(EDITS)} edits")
