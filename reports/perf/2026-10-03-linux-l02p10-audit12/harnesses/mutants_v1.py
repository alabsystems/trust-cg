#!/usr/bin/env python3
"""Apply (or revert) the mutation guards of the first verifier's repair.

The same scheme as mutants.py: each guard turns one check of the repair off
when L02P10_MUTANT names it, so one build serves every mutant.
`mutants_v1.py apply` writes them into link_driver.rs (a backup is kept);
`mutants_v1.py revert` restores the backup. Never committed applied.
"""
import os
import shutil
import sys

# The checkout's link_driver.rs: $REPO/crates/trust-cg-codegen/src/link_driver.rs.
PATH = os.path.join(os.environ.get("REPO", "."), "crates/trust-cg-codegen/src/link_driver.rs")
BACKUP = PATH + ".mutants-backup"

HELPER = '''
/// Mutation harness (never committed): whether the mutant `name` is on.
fn mutant(name: &str) -> bool {
    std::env::var("L02P10_MUTANT").as_deref() == Ok(name)
}
'''

# (id, anchor text, replacement text)
EDITS = [
    # An image without section headers and a PT_TLS with memory.
    ("nsh-tls",
     "        return Ok(template.map(|template| {\n",
     "        return Ok(template.filter(|_| !mutant(\"nsh-tls\")).map(|template| {\n"),
    # The first-section rule's two reasons.
    ("tls-before",
     "    if first.address < template.address {\n",
     "    if first.address < template.address && !mutant(\"tls-before\") {\n"),
    # LLD's own `.eh_frame` pieces.
    ("lld-own-pieces",
     "                    if own.names(&file) {\n                        output.own_pieces.push(",
     "                    if own.names(&file) && !mutant(\"lld-own-pieces\") {\n                        output.own_pieces.push("),
    ("lld-unplaced-pieces",
     "            if output.other {\n                files.push(piece.file.clone());\n",
     "            if output.other && !mutant(\"lld-unplaced-pieces\") {\n                files.push(piece.file.clone());\n"),
    # gold's merged data, inline and wrapped.
    ("gold-merged",
     "                            if merged {\n                                map.merged_eh_frame.push((address, size));\n",
     "                            if merged && !mutant(\"gold-merged\") {\n                                map.merged_eh_frame.push((address, size));\n"),
    ("gold-merged-wrapped",
     "                            wrapped_merged = merged;\n",
     "                            wrapped_merged = merged && !mutant(\"gold-merged-wrapped\");\n"),
    # Its attribution to own objects, and the rule reading it.
    ("merged-attribution",
     "    let merged = if map.merged_eh_frame.is_empty() {\n",
     "    let merged = if map.merged_eh_frame.is_empty() || mutant(\"merged-attribution\") {\n"),
    ("merged-has",
     "        if !has_eh_frame || placed {\n",
     "        if (!has_eh_frame && !mutant(\"merged-has\")) || (placed && !mutant(\"merged-placed\")) {\n"),
    ("merged-check",
     "        .or_else(|| own_section_lacking(&segments, merged, &needed).map(|found| (found, true)));\n",
     "        .or_else(|| {\n            own_section_lacking(&segments, merged, &needed)\n                .filter(|_| !mutant(\"merged-check\"))\n                .map(|found| (found, true))\n        });\n"),
    # trust-cg's own sections loaded where the map places them.
    ("own-map-path",
     "            let read = OwnObjectRecords::read_all(&request.objects);\n            // An input the map places neither way is refused by the read\n",
     "            if mutant(\"own-map-path\") {\n                return Vec::new();\n            }\n            let read = OwnObjectRecords::read_all(&request.objects);\n            // An input the map places neither way is refused by the read\n"),
    ("own-unloaded",
     "        }) else {\n            return Ok(Some(format!(\n                \"{span} lies in the memory of no PT_LOAD segment",
     "        }) else {\n            if mutant(\"own-unloaded\") {\n                continue;\n            }\n            return Ok(Some(format!(\n                \"{span} lies in the memory of no PT_LOAD segment"),
    ("own-zero-fill",
     "            if end(input.address, input.size) > file_end {\n",
     "            if end(input.address, input.size) > file_end && !mutant(\"own-zero-fill\") {\n"),
    ("own-nobits",
     "        if let Some(nonzero) = first_nonzero_byte(image, at, width)? {\n            return Ok(Some(format!(\n                \"{span}, which is zero fill",
     "        if let Some(nonzero) = first_nonzero_byte(image, at, width)?.filter(|_| !mutant(\"own-nobits\")) {\n            return Ok(Some(format!(\n                \"{span}, which is zero fill"),
    ("own-contents-type",
     "        Some(contents.unwrap_or(false) || record.sh_type != SHT_NOBITS)\n",
     "        Some(contents.unwrap_or(false) || (record.sh_type != SHT_NOBITS && !mutant(\"own-contents-type\")))\n"),
    # A gold input its map places neither way (finding 3).
    ("gold-located-err",
     "        Err(why) => why,\n    };\n    vec![LinkDiagnostic {\n        kind: LinkDiagnosticKind::Unclassified,\n        subject: None,\n        relocation: None,\n        function: None,\n        line: format!(\n            \"[TCG-LINK-SEGMENT-PERMISSIONS]",
     "        Err(_) if mutant(\"gold-located-err\") => return Vec::new(),\n        Err(why) => why,\n    };\n    vec![LinkDiagnostic {\n        kind: LinkDiagnosticKind::Unclassified,\n        subject: None,\n        relocation: None,\n        function: None,\n        line: format!(\n            \"[TCG-LINK-SEGMENT-PERMISSIONS]"),
]

MUTANTS = [edit[0] for edit in EDITS] + ["merged-placed"]


def apply():
    shutil.copyfile(PATH, BACKUP)
    text = open(PATH).read()
    for name, old, new in EDITS:
        count = text.count(old)
        if count != 1:
            raise SystemExit(f"{name}: anchor found {count} times")
        text = text.replace(old, new)
    text = text.replace("\n#[cfg(test)]\nmod tests {\n", HELPER + "\n#[cfg(test)]\nmod tests {\n", 1)
    open(PATH, "w").write(text)


def revert():
    shutil.copyfile(BACKUP, PATH)


if __name__ == "__main__":
    {"apply": apply, "revert": revert, "list": lambda: print("\n".join(MUTANTS))}[sys.argv[1]]()
