// trust-cg-codegen/macho/linked_image/object.rs - independent reader for the linked objects
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Reads an arm64 `MH_OBJECT` from its bytes alone (sections, symbols and
//! relocation records) and splits each section into the atoms a static
//! linker may place independently: with `MH_SUBSECTIONS_VIA_SYMBOLS` every
//! defined symbol starts an atom, otherwise the section is one atom.

use sha2::{Digest, Sha256};

use super::abi::*;

/// One relocation record, as written.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ObjReloc {
    /// Offset of the patched field within its section.
    pub address: u32,
    pub symbolnum: u32,
    pub pcrel: bool,
    /// log2 of the field size.
    pub length: u8,
    pub external: bool,
    pub kind: u8,
}

/// One `section_64` of an object.
#[derive(Debug, Clone)]
pub(super) struct ObjSection {
    pub segment: String,
    pub name: String,
    pub addr: u64,
    pub size: u64,
    pub flags: u32,
    /// File bytes; empty for zero-fill.
    pub data: Vec<u8>,
    pub relocs: Vec<ObjReloc>,
}

impl ObjSection {
    pub fn section_type(&self) -> u32 {
        self.flags & SECTION_TYPE
    }

    pub fn is_zero_fill(&self) -> bool {
        matches!(
            self.section_type(),
            S_ZEROFILL | S_GB_ZEROFILL | S_THREAD_LOCAL_ZEROFILL
        )
    }

    pub fn is_code(&self) -> bool {
        self.flags & (S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS) != 0
    }

    /// Sections a static linker consumes rather than places
    /// (`__LD,__compact_unwind`, `__DWARF`).
    pub fn is_consumed(&self) -> bool {
        self.flags & S_ATTR_DEBUG != 0
    }

    /// Data dyld makes read-only once its fixups are applied.
    pub fn is_read_only_after_fixups(&self) -> bool {
        self.segment == "__DATA_CONST" || (self.segment == "__DATA" && self.name == "__const")
    }

    pub fn label(&self) -> String {
        format!("{},{}", self.segment, self.name)
    }
}

/// One non-debug `nlist_64` of an object.
#[derive(Debug, Clone)]
pub(super) struct ObjSymbol {
    pub name: String,
    pub n_type: u8,
    pub n_sect: u8,
    pub n_desc: u16,
    pub n_value: u64,
}

impl ObjSymbol {
    pub fn is_defined(&self) -> bool {
        self.n_type & N_TYPE == N_SECT
    }

    pub fn is_undefined(&self) -> bool {
        self.n_type & N_TYPE == N_UNDF
    }

    pub fn is_external(&self) -> bool {
        self.n_type & N_EXT != 0
    }

    pub fn is_private_extern(&self) -> bool {
        self.n_type & N_PEXT != 0
    }

    pub fn is_weak_def(&self) -> bool {
        self.n_desc & N_WEAK_DEF != 0
    }

    pub fn is_weak_ref(&self) -> bool {
        self.n_desc & N_WEAK_REF != 0
    }
}

/// A contiguous piece of one section a linker places as a unit.
#[derive(Debug, Clone)]
pub(super) struct Atom {
    pub section: usize,
    /// Section-relative range.
    pub start: u64,
    pub end: u64,
    /// Symbol indices defined in this atom with their offsets in it.
    pub anchors: Vec<(usize, u64)>,
}

/// A parsed object and its atoms.
#[derive(Debug, Clone)]
pub(super) struct Object {
    pub name: String,
    pub sha256: [u8; 32],
    pub size: usize,
    pub flags: u32,
    pub sections: Vec<ObjSection>,
    pub symbols: Vec<ObjSymbol>,
    pub atoms: Vec<Atom>,
    /// Per section: indices of its atoms in address order.
    section_atoms: Vec<Vec<usize>>,
    pub build: Option<(u32, u32, u32)>,
}

type Parse<T> = Result<T, String>;

fn need<T>(value: Option<T>, what: &str) -> Parse<T> {
    value.ok_or_else(|| format!("truncated or out-of-range {what}"))
}

impl Object {
    pub fn parse(name: &str, bytes: &[u8]) -> Parse<Self> {
        let magic = need(read_u32(bytes, 0), "mach header")?;
        if magic != MH_MAGIC_64 {
            return Err(format!("magic {magic:#x} is not MH_MAGIC_64"));
        }
        if need(read_u32(bytes, 4), "mach header")? != CPU_TYPE_ARM64 {
            return Err("cputype is not CPU_TYPE_ARM64".into());
        }
        if need(read_u32(bytes, 12), "mach header")? != MH_OBJECT {
            return Err("filetype is not MH_OBJECT".into());
        }
        let ncmds = need(read_u32(bytes, 16), "mach header")? as usize;
        let sizeofcmds = need(read_u32(bytes, 20), "mach header")? as usize;
        let flags = need(read_u32(bytes, 24), "mach header")?;
        let commands_end = 32usize
            .checked_add(sizeofcmds)
            .filter(|end| *end <= bytes.len())
            .ok_or("load commands exceed the file")?;
        let mut object = Object {
            name: name.to_string(),
            sha256: Sha256::digest(bytes).into(),
            size: bytes.len(),
            flags,
            sections: Vec::new(),
            symbols: Vec::new(),
            atoms: Vec::new(),
            section_atoms: Vec::new(),
            build: None,
        };
        let mut segments = 0;
        let mut at = 32usize;
        for index in 0..ncmds {
            let what = format!("load command {index}");
            let cmd = need(read_u32(bytes, at), &what)?;
            let cmdsize = need(read_u32(bytes, at + 4), &what)? as usize;
            let end = at
                .checked_add(cmdsize)
                .filter(|end| cmdsize >= 8 && *end <= commands_end)
                .ok_or_else(|| format!("{what} exceeds sizeofcmds"))?;
            match cmd {
                LC_SEGMENT_64 => {
                    segments += 1;
                    object.parse_sections(bytes, at, cmdsize)?;
                }
                LC_SYMTAB => object.parse_symtab(bytes, at)?,
                LC_BUILD_VERSION => {
                    object.build = Some((
                        need(read_u32(bytes, at + 8), "LC_BUILD_VERSION")?,
                        need(read_u32(bytes, at + 12), "LC_BUILD_VERSION")?,
                        need(read_u32(bytes, at + 16), "LC_BUILD_VERSION")?,
                    ));
                }
                LC_DYSYMTAB | LC_VERSION_MIN_MACOSX | LC_DATA_IN_CODE | LC_LINKER_OPTION => {}
                LC_LINKER_OPTIMIZATION_HINT => {
                    return Err(
                        "LC_LINKER_OPTIMIZATION_HINT: linker optimization hints let ld64 rewrite \
                         instruction pairs, which this replay does not model"
                            .into(),
                    );
                }
                other => {
                    return Err(format!(
                        "{what} ({other:#x}) is not an object load command this replay models"
                    ));
                }
            }
            at = end;
        }
        if segments != 1 {
            return Err(format!("{segments} LC_SEGMENT_64 commands (expected one)"));
        }
        object.atomize()?;
        Ok(object)
    }

    fn parse_sections(&mut self, bytes: &[u8], at: usize, cmdsize: usize) -> Parse<()> {
        let nsects = need(read_u32(bytes, at + 64), "LC_SEGMENT_64")? as usize;
        if 72 + nsects * 80 > cmdsize || nsects > 255 {
            return Err("object sections exceed the segment command".into());
        }
        for index in 0..nsects {
            let header = at + 72 + index * 80;
            let what = "section_64";
            let segment = need(fixed_name(bytes, header + 16), what)?;
            let name = need(fixed_name(bytes, header), what)?;
            let addr = need(read_u64(bytes, header + 32), what)?;
            let size = need(read_u64(bytes, header + 40), what)?;
            let offset = need(read_u32(bytes, header + 48), what)? as usize;
            let reloff = need(read_u32(bytes, header + 56), what)? as usize;
            let nreloc = need(read_u32(bytes, header + 60), what)? as usize;
            let flags = need(read_u32(bytes, header + 64), what)?;
            let zero_fill = matches!(
                flags & SECTION_TYPE,
                S_ZEROFILL | S_GB_ZEROFILL | S_THREAD_LOCAL_ZEROFILL
            );
            let data = if zero_fill {
                Vec::new()
            } else {
                let end = offset
                    .checked_add(size as usize)
                    .filter(|end| *end <= bytes.len())
                    .ok_or_else(|| format!("section {segment},{name} lies outside the file"))?;
                bytes[offset..end].to_vec()
            };
            let mut relocs = Vec::with_capacity(nreloc);
            for reloc in 0..nreloc {
                let entry = reloff + reloc * 8;
                let address = need(read_u32(bytes, entry), "relocation_info")?;
                let info = need(read_u32(bytes, entry + 4), "relocation_info")?;
                if address & 0x8000_0000 != 0 {
                    return Err(format!(
                        "section {segment},{name}: scattered relocations are not modeled"
                    ));
                }
                if u64::from(address) >= size.max(1) {
                    return Err(format!(
                        "section {segment},{name}: relocation at {address:#x} lies outside the section"
                    ));
                }
                relocs.push(ObjReloc {
                    address,
                    symbolnum: info & 0x00FF_FFFF,
                    pcrel: (info >> 24) & 1 == 1,
                    length: ((info >> 25) & 3) as u8,
                    external: (info >> 27) & 1 == 1,
                    kind: (info >> 28) as u8,
                });
            }
            self.sections.push(ObjSection {
                segment,
                name,
                addr,
                size,
                flags,
                data,
                relocs,
            });
        }
        Ok(())
    }

    fn parse_symtab(&mut self, bytes: &[u8], at: usize) -> Parse<()> {
        let symoff = need(read_u32(bytes, at + 8), "LC_SYMTAB")? as usize;
        let nsyms = need(read_u32(bytes, at + 12), "LC_SYMTAB")? as usize;
        let stroff = need(read_u32(bytes, at + 16), "LC_SYMTAB")? as usize;
        let strsize = need(read_u32(bytes, at + 20), "LC_SYMTAB")? as usize;
        let strend = stroff
            .checked_add(strsize)
            .filter(|end| *end <= bytes.len())
            .ok_or("string table lies outside the file")?;
        for index in 0..nsyms {
            let entry = symoff + index * 16;
            let strx = need(read_u32(bytes, entry), "nlist_64")? as usize;
            let n_type = *need(bytes.get(entry + 4), "nlist_64")?;
            // Keep symbol indices aligned with relocation `r_symbolnum`: a
            // debug entry is kept with an empty name and never used.
            let name = if n_type & N_STAB != 0 || strx == 0 {
                String::new()
            } else {
                need(
                    c_string(bytes, stroff.saturating_add(strx), strend),
                    "symbol name",
                )?
            };
            self.symbols.push(ObjSymbol {
                name,
                n_type,
                n_sect: *need(bytes.get(entry + 5), "nlist_64")?,
                n_desc: need(read_u16(bytes, entry + 6), "nlist_64")?,
                n_value: need(read_u64(bytes, entry + 8), "nlist_64")?,
            });
        }
        Ok(())
    }

    /// Split every placed section into atoms.
    fn atomize(&mut self) -> Parse<()> {
        let subsections = self.flags & MH_SUBSECTIONS_VIA_SYMBOLS != 0;
        self.section_atoms = vec![Vec::new(); self.sections.len()];
        for (section_index, section) in self.sections.iter().enumerate() {
            if section.is_consumed() {
                continue;
            }
            let ordinal = section_index + 1;
            let mut defined: Vec<(u64, usize)> = Vec::new();
            for (symbol_index, symbol) in self.symbols.iter().enumerate() {
                if symbol.n_type & N_STAB != 0
                    || !symbol.is_defined()
                    || usize::from(symbol.n_sect) != ordinal
                {
                    continue;
                }
                let offset = symbol
                    .n_value
                    .checked_sub(section.addr)
                    .filter(|offset| *offset <= section.size)
                    .ok_or_else(|| {
                        format!(
                            "symbol {} lies outside its section {}",
                            symbol.name,
                            section.label()
                        )
                    })?;
                defined.push((offset, symbol_index));
            }
            defined.sort();
            let mut starts: Vec<u64> = if subsections {
                defined
                    .iter()
                    .map(|(offset, _)| *offset)
                    .filter(|offset| *offset < section.size)
                    .collect()
            } else {
                Vec::new()
            };
            if starts.first() != Some(&0) {
                starts.insert(0, 0);
            }
            starts.dedup();
            // `defined` and `starts` are both sorted: walk them together.
            let mut next = 0;
            for (position, &start) in starts.iter().enumerate() {
                let end = starts.get(position + 1).copied().unwrap_or(section.size);
                let last = position + 1 == starts.len();
                let mut anchors = Vec::new();
                while let Some(&(offset, symbol)) = defined.get(next)
                    && (offset < end || (last && offset == end))
                {
                    anchors.push((symbol, offset - start));
                    next += 1;
                }
                self.section_atoms[section_index].push(self.atoms.len());
                self.atoms.push(Atom {
                    section: section_index,
                    start,
                    end,
                    anchors,
                });
            }
        }
        Ok(())
    }

    /// `(atom index, offset in atom)` of section-relative `offset`.
    pub fn atom_of(&self, section: usize, offset: u64) -> Option<(usize, u64)> {
        let atoms = self.section_atoms.get(section)?;
        // The last atom starting at or before `offset`.
        let position = atoms.partition_point(|&index| self.atoms[index].start <= offset);
        let index = *atoms.get(position.checked_sub(1)?)?;
        let atom = &self.atoms[index];
        (offset < atom.end || (offset == atom.end && atom.start == atom.end))
            .then(|| (index, offset - atom.start))
    }

    /// Per section, whether each byte lies in a relocation field.
    pub fn relocation_masks(&self) -> Vec<Vec<bool>> {
        self.sections
            .iter()
            .map(|section| {
                let mut mask = vec![false; section.data.len()];
                for reloc in &section.relocs {
                    let width = match reloc.kind {
                        ARM64_RELOC_ADDEND => 0,
                        ARM64_RELOC_UNSIGNED
                        | ARM64_RELOC_SUBTRACTOR
                        | ARM64_RELOC_POINTER_TO_GOT => 1usize << reloc.length,
                        _ => 4,
                    };
                    let start = reloc.address as usize;
                    let end = (start + width).min(mask.len());
                    for byte in mask.iter_mut().take(end).skip(start) {
                        *byte = true;
                    }
                }
                mask
            })
            .collect()
    }
}
