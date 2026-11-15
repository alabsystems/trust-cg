#!/usr/bin/env python3
"""Apply (or revert) the L02-P10 twelfth-audit mutation guards.

Each guard turns one new check off when L02P10_MUTANT names it, so one build
serves every mutant. `mutants.py apply` writes them into link_driver.rs (a
backup is kept); `mutants.py revert` restores the backup. Never committed.
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
    ("tls-image",
     "fn tls_template_disagreement(image: ImageBytes<'_>) -> Result<Option<String>, String> {\n",
     "fn tls_template_disagreement(image: ImageBytes<'_>) -> Result<Option<String>, String> {\n    if mutant(\"tls-image\") {\n        return Ok(None);\n    }\n"),
    ("tls-one-template",
     "        [template] => **template,\n        more => {\n",
     "        [template] => **template,\n        [template, ..] if mutant(\"tls-one-template\") => **template,\n        more => {\n"),
    ("tls-align",
     "    if !align.is_power_of_two() || template.address % align != 0 {\n",
     "    if !mutant(\"tls-align\") && (!align.is_power_of_two() || template.address % align != 0) {\n"),
    ("tls-filesz",
     "    if template.file_size > template.memory_size {\n        return Err(format!(\n            \"its PT_TLS segment at {span} holds more file bytes",
     "    if template.file_size > template.memory_size && !mutant(\"tls-filesz\") {\n        return Err(format!(\n            \"its PT_TLS segment at {span} holds more file bytes"),
    ("tls-loaded",
     "    if template.file_size == 0 {\n        return Ok(Some((template, None)));\n    }\n",
     "    if template.file_size == 0 || mutant(\"tls-loaded\") {\n        return Ok(Some((template, None)));\n    }\n"),
    ("tls-overlap",
     "        if u128::from(later.address) < end(earlier.address, earlier.size) {\n            return Ok(Some(format!(\n                \"its thread-local sections {} and {} overlap",
     "        if u128::from(later.address) < end(earlier.address, earlier.size) && !mutant(\"tls-overlap\") {\n            return Ok(Some(format!(\n                \"its thread-local sections {} and {} overlap"),
    ("tls-first",
     "    if first.address != template.address {\n",
     "    if first.address != template.address && !mutant(\"tls-first\") {\n"),
    ("tls-memsz",
     "        if end(section.address, section.size) > end(template.address, template.memory_size) {\n",
     "        if end(section.address, section.size) > end(template.address, template.memory_size)\n            && !mutant(\"tls-memsz\")\n        {\n"),
    ("tls-filepart",
     "        if section.kind != SHT_NOBITS && end(section.address, section.size) > file_end {\n",
     "        if section.kind != SHT_NOBITS && end(section.address, section.size) > file_end && !mutant(\"tls-filepart\") {\n"),
    ("tls-other",
     "    if let Some(other) = headers.iter().find(|section| {\n        section.flags & SHF_ALLOC != 0\n            && section.flags & SHF_TLS == 0\n",
     "    if let Some(other) = headers.iter().find(|section| {\n        !mutant(\"tls-other\")\n            && section.flags & SHF_ALLOC != 0\n            && section.flags & SHF_TLS == 0\n"),
    ("tls-nobits",
     "        .filter(|section| section.kind == SHT_NOBITS && overlapping(section))\n",
     "        .filter(|section| section.kind == SHT_NOBITS && overlapping(section) && !mutant(\"tls-nobits\"))\n"),
    ("own-placement",
     "        if input.address < template.address\n            || end(input.address, input.size) > end(template.address, limit)\n        {\n",
     "        if !mutant(\"own-placement\")\n            && (input.address < template.address\n                || end(input.address, input.size) > end(template.address, limit))\n        {\n"),
    ("own-tprel",
     "    if matches!(\n        kind,\n        ElfLinkedKind::Executable | ElfLinkedKind::PositionIndependentExecutable\n    ) {\n",
     "    if !mutant(\"own-tprel\") && matches!(\n        kind,\n        ElfLinkedKind::Executable | ElfLinkedKind::PositionIndependentExecutable\n    ) {\n"),
    ("own-symtab",
     "    if wanted.is_empty() {\n        return Ok(None);\n    }\n    let Some(headers) = elf_section_headers(image)? else {\n",
     "    if wanted.is_empty() || mutant(\"own-symtab\") {\n        return Ok(None);\n    }\n    let Some(headers) = elf_section_headers(image)? else {\n"),
    ("perm-r",
     "    let needed = |section: &MapInputSection| needs(section) & (SEGMENT_PF_R | SEGMENT_PF_X);\n",
     "    let needed = |section: &MapInputSection| {\n        needs(section)\n            & (SEGMENT_PF_R | SEGMENT_PF_X)\n            & if mutant(\"perm-r\") { !SEGMENT_PF_R } else { u32::MAX }\n            & if mutant(\"perm-x\") { !SEGMENT_PF_X } else { u32::MAX }\n    };\n"),
    ("perm-tbss",
     "            let readable = if record.sh_type == SHT_NOBITS && record.sh_flags & SHF_TLS != 0 {\n",
     "            let readable = if record.sh_type == SHT_NOBITS && record.sh_flags & SHF_TLS != 0 && !mutant(\"perm-tbss\") {\n"),
    ("bc-magic",
     "    prefix.starts_with(RAW) || prefix.starts_with(WRAPPER)\n",
     "    !mutant(\"bc-magic\") && (prefix.starts_with(RAW) || prefix.starts_with(WRAPPER))\n"),
    ("bc-objects",
     "    let Some(first) = examination.bitcode.first().cloned() else {\n        return;\n    };\n",
     "    let Some(first) = examination.bitcode.first().cloned() else {\n        return;\n    };\n    if mutant(\"bc-objects\") {\n        return;\n    }\n"),
    ("bc-relink",
     "    let lto_objects: Result<PathBuf, String> = if traced && trace_names_bitcode(&linked.stdout) {\n",
     "    let lto_objects: Result<PathBuf, String> = if traced && !mutant(\"bc-relink\") && trace_names_bitcode(&linked.stdout) {\n"),
    ("bc-empty",
     "        if bytes.is_empty() {\n            return Err(format!(\n                \"LLD wrote no bytes to {} for one of the objects it links",
     "        if bytes.is_empty() && !mutant(\"bc-empty\") {\n            return Err(format!(\n                \"LLD wrote no bytes to {} for one of the objects it links"),
    ("bc-standin",
     "            if let Some(examined) = self.examined()\n                && let (Some(first), Some(unread)) =\n",
     "            if let Some(examined) = self.examined().filter(|_| !mutant(\"bc-standin\"))\n                && let (Some(first), Some(unread)) =\n"),
    ("gold-symbols",
     "            let base = bases.next()?;\n            bases.all(|other| other == base).then_some(base)\n",
     "            let base = bases.next()?;\n            if mutant(\"gold-symbols\") {\n                return None;\n            }\n            bases.all(|other| other == base).then_some(base)\n"),
    ("gold-unplaced",
     "                    if map.own_sections.len() > before\n                        && input.address == u64::MAX\n",
     "                    if map.own_sections.len() > before\n                        && !mutant(\"gold-unplaced\")\n                        && input.address == u64::MAX\n"),
]

MUTANTS = [edit[0] for edit in EDITS] + ["perm-x"]


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
