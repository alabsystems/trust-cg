// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! A clean-room reader for 64-bit AArch64 Mach-O relocatable objects.
//!
//! Written from `mach-o/loader.h`, `mach-o/nlist.h` and
//! `mach-o/arm64/reloc.h` field layouts, not from trust-cg's writer
//! (`trust-cg-codegen/src/macho/writer.rs`) or its parsers. It reads only
//! what the exception-table obligations need: section headers and contents,
//! the symbol table and each section's relocation records. Anything outside
//! that profile (another CPU, a fat or 32-bit file, scattered relocations,
//! a truncated table) is refused rather than guessed.

use super::{EhObligationKind, Violation};

const MH_MAGIC_64: u32 = 0xfeed_facf;
const CPU_TYPE_ARM64: u32 = 0x0100_000c;
const MH_OBJECT: u32 = 1;
const LC_SEGMENT_64: u32 = 0x19;
const LC_SYMTAB: u32 = 0x2;
const SECTION_64_SIZE: usize = 80;
const SEGMENT_64_HEADER_SIZE: usize = 72;
const NLIST_64_SIZE: usize = 16;
const R_SCATTERED: u32 = 0x8000_0000;
const N_STAB: u8 = 0xe0;
const N_TYPE: u8 = 0x0e;
const N_UNDF: u8 = 0x0;
const N_SECT: u8 = 0xe;
const SECTION_TYPE_MASK: u32 = 0xff;
const S_ZEROFILL: u32 = 0x1;

/// `ARM64_RELOC_UNSIGNED`.
pub(crate) const ARM64_RELOC_UNSIGNED: u8 = 0;
/// `ARM64_RELOC_SUBTRACTOR`.
pub(crate) const ARM64_RELOC_SUBTRACTOR: u8 = 1;
/// `ARM64_RELOC_BRANCH26`.
pub(crate) const ARM64_RELOC_BRANCH26: u8 = 2;
/// `ARM64_RELOC_POINTER_TO_GOT`.
pub(crate) const ARM64_RELOC_POINTER_TO_GOT: u8 = 7;

fn decode_error(detail: impl Into<String>) -> Violation {
    Violation::object(EhObligationKind::ObjectDecode, detail)
}

fn read_u32(data: &[u8], offset: usize) -> Result<u32, Violation> {
    data.get(offset..offset.saturating_add(4))
        .and_then(|bytes| bytes.try_into().ok())
        .map(u32::from_le_bytes)
        .ok_or_else(|| decode_error(format!("u32 at file offset {offset} is out of bounds")))
}

fn read_u64(data: &[u8], offset: usize) -> Result<u64, Violation> {
    data.get(offset..offset.saturating_add(8))
        .and_then(|bytes| bytes.try_into().ok())
        .map(u64::from_le_bytes)
        .ok_or_else(|| decode_error(format!("u64 at file offset {offset} is out of bounds")))
}

fn fixed_name(data: &[u8], offset: usize) -> Result<String, Violation> {
    let bytes = data
        .get(offset..offset.saturating_add(16))
        .ok_or_else(|| decode_error(format!("16-byte name at {offset} is out of bounds")))?;
    let end = bytes.iter().position(|&b| b == 0).unwrap_or(16);
    String::from_utf8(bytes[..end].to_vec())
        .map_err(|_| decode_error(format!("name at {offset} is not UTF-8")))
}

/// One `relocation_info` record.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Reloc {
    /// Offset of the relocated field within its section.
    pub(crate) address: u32,
    /// Symbol table index (extern) or 1-based section ordinal (local).
    pub(crate) symbolnum: u32,
    pub(crate) pcrel: bool,
    /// log2 of the field width.
    pub(crate) length: u8,
    pub(crate) is_extern: bool,
    pub(crate) kind: u8,
}

/// One `section_64` with its bytes and relocations.
#[derive(Debug, Clone)]
pub(crate) struct Section {
    pub(crate) segname: String,
    pub(crate) sectname: String,
    pub(crate) addr: u64,
    pub(crate) bytes: Vec<u8>,
    pub(crate) relocs: Vec<Reloc>,
}

impl Section {
    /// Every relocation record at `address`, in table order.
    pub(crate) fn relocs_at(&self, address: u32) -> Vec<Reloc> {
        self.relocs
            .iter()
            .copied()
            .filter(|reloc| reloc.address == address)
            .collect()
    }

    pub(crate) fn end(&self) -> u64 {
        self.addr.saturating_add(self.bytes.len() as u64)
    }
}

/// One `nlist_64` entry (stab entries are kept but never resolved).
#[derive(Debug, Clone)]
pub(crate) struct Symbol {
    pub(crate) name: String,
    pub(crate) n_type: u8,
    /// 1-based section ordinal of a defined symbol.
    pub(crate) n_sect: u8,
    pub(crate) n_value: u64,
}

impl Symbol {
    pub(crate) fn is_defined(&self) -> bool {
        self.n_type & N_STAB == 0 && self.n_type & N_TYPE == N_SECT
    }

    pub(crate) fn is_undefined(&self) -> bool {
        self.n_type & N_STAB == 0 && self.n_type & N_TYPE == N_UNDF
    }
}

/// A parsed relocatable object.
#[derive(Debug, Clone)]
pub(crate) struct Object {
    pub(crate) sections: Vec<Section>,
    pub(crate) symbols: Vec<Symbol>,
}

impl Object {
    pub(crate) fn parse(data: &[u8]) -> Result<Self, Violation> {
        if read_u32(data, 0)? != MH_MAGIC_64 {
            return Err(decode_error("not a 64-bit little-endian Mach-O file"));
        }
        let cputype = read_u32(data, 4)?;
        if cputype != CPU_TYPE_ARM64 {
            return Err(decode_error(format!(
                "cputype {cputype:#x} is not CPU_TYPE_ARM64"
            )));
        }
        let filetype = read_u32(data, 12)?;
        if filetype != MH_OBJECT {
            return Err(decode_error(format!(
                "filetype {filetype} is not MH_OBJECT"
            )));
        }
        let ncmds = read_u32(data, 16)? as usize;
        let sizeofcmds = read_u32(data, 20)? as usize;
        let mut cursor = 32usize;
        let end_of_commands = cursor
            .checked_add(sizeofcmds)
            .filter(|&end| end <= data.len())
            .ok_or_else(|| decode_error("load commands exceed the file"))?;
        let mut sections = Vec::new();
        let mut symtab = None;
        for index in 0..ncmds {
            let cmd = read_u32(data, cursor)?;
            let cmdsize = read_u32(data, cursor + 4)? as usize;
            if cmdsize < 8 || cursor + cmdsize > end_of_commands {
                return Err(decode_error(format!(
                    "load command {index} has size {cmdsize} outside the command area"
                )));
            }
            match cmd {
                LC_SEGMENT_64 => {
                    let nsects = read_u32(data, cursor + 64)? as usize;
                    if SEGMENT_64_HEADER_SIZE + nsects * SECTION_64_SIZE > cmdsize {
                        return Err(decode_error(format!(
                            "segment command {index} declares {nsects} sections beyond its size"
                        )));
                    }
                    for s in 0..nsects {
                        let base = cursor + SEGMENT_64_HEADER_SIZE + s * SECTION_64_SIZE;
                        sections.push(parse_section(data, base)?);
                    }
                }
                LC_SYMTAB => {
                    symtab = Some((
                        read_u32(data, cursor + 8)? as usize,
                        read_u32(data, cursor + 12)? as usize,
                        read_u32(data, cursor + 16)? as usize,
                        read_u32(data, cursor + 20)? as usize,
                    ));
                }
                _ => {}
            }
            cursor += cmdsize;
        }
        let mut symbols = Vec::new();
        if let Some((symoff, nsyms, stroff, strsize)) = symtab {
            let strings = data
                .get(stroff..stroff.saturating_add(strsize))
                .ok_or_else(|| decode_error("string table exceeds the file"))?;
            for index in 0..nsyms {
                let base = symoff + index * NLIST_64_SIZE;
                let strx = read_u32(data, base)? as usize;
                let n_type = *data
                    .get(base + 4)
                    .ok_or_else(|| decode_error("symbol table exceeds the file"))?;
                let n_sect = *data
                    .get(base + 5)
                    .ok_or_else(|| decode_error("symbol table exceeds the file"))?;
                let n_value = read_u64(data, base + 8)?;
                let name_bytes = strings.get(strx..).ok_or_else(|| {
                    decode_error(format!(
                        "symbol {index} string index {strx} is out of bounds"
                    ))
                })?;
                let end = name_bytes.iter().position(|&b| b == 0).ok_or_else(|| {
                    decode_error(format!("symbol {index} name is not NUL-terminated"))
                })?;
                let name = String::from_utf8(name_bytes[..end].to_vec())
                    .map_err(|_| decode_error(format!("symbol {index} name is not UTF-8")))?;
                symbols.push(Symbol {
                    name,
                    n_type,
                    n_sect,
                    n_value,
                });
            }
        }
        Ok(Self { sections, symbols })
    }

    pub(crate) fn section(&self, segname: &str, sectname: &str) -> Option<(usize, &Section)> {
        self.sections
            .iter()
            .enumerate()
            .find(|(_, section)| section.segname == segname && section.sectname == sectname)
    }

    pub(crate) fn symbol(&self, index: u32) -> Result<&Symbol, Violation> {
        self.symbols
            .get(index as usize)
            .ok_or_else(|| decode_error(format!("relocation names symbol {index} past the table")))
    }

    /// The defined non-stab symbols at `address` in section ordinal `n_sect`.
    pub(crate) fn symbols_at(&self, n_sect: u8, address: u64) -> Vec<&Symbol> {
        self.symbols
            .iter()
            .filter(|symbol| {
                symbol.is_defined() && symbol.n_sect == n_sect && symbol.n_value == address
            })
            .collect()
    }
}

fn parse_section(data: &[u8], base: usize) -> Result<Section, Violation> {
    let sectname = fixed_name(data, base)?;
    let segname = fixed_name(data, base + 16)?;
    let addr = read_u64(data, base + 32)?;
    let size = read_u64(data, base + 40)?;
    let offset = read_u32(data, base + 48)? as usize;
    let reloff = read_u32(data, base + 56)? as usize;
    let nreloc = read_u32(data, base + 60)? as usize;
    let flags = read_u32(data, base + 64)?;
    let size = usize::try_from(size)
        .map_err(|_| decode_error(format!("section {segname},{sectname} size overflows")))?;
    let bytes = if flags & SECTION_TYPE_MASK == S_ZEROFILL {
        vec![0; size]
    } else {
        data.get(offset..offset.saturating_add(size))
            .ok_or_else(|| {
                decode_error(format!(
                    "section {segname},{sectname} contents exceed the file"
                ))
            })?
            .to_vec()
    };
    let mut relocs = Vec::with_capacity(nreloc);
    for index in 0..nreloc {
        let at = reloff + index * 8;
        let address = read_u32(data, at)?;
        if address & R_SCATTERED != 0 {
            return Err(decode_error(format!(
                "section {segname},{sectname} relocation {index} is scattered"
            )));
        }
        let info = read_u32(data, at + 4)?;
        relocs.push(Reloc {
            address,
            symbolnum: info & 0x00ff_ffff,
            pcrel: (info >> 24) & 1 == 1,
            length: ((info >> 25) & 3) as u8,
            is_extern: (info >> 27) & 1 == 1,
            kind: ((info >> 28) & 0xf) as u8,
        });
    }
    Ok(Section {
        segname,
        sectname,
        addr,
        bytes,
        relocs,
    })
}

/// What a relocated or literal pointer-sized field resolves to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Term {
    /// An address inside this object (a defined symbol or a section address).
    Address(u64),
    /// An undefined (imported) symbol, by object-level name.
    Import(String),
    /// The GOT slot the linker creates for a symbol, by object-level name.
    GotOf(String),
}

/// A field's link-time value: `plus - minus + addend`, where the literal
/// bytes stored in the field are the addend.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FieldValue {
    pub(crate) plus: Option<Term>,
    pub(crate) minus: Option<Term>,
    pub(crate) addend: i64,
    /// The field is PC-relative per its relocation (POINTER_TO_GOT).
    pub(crate) reloc_pcrel: bool,
}

impl Object {
    fn symbol_term(&self, reloc: Reloc, got: bool) -> Result<Term, Violation> {
        if !reloc.is_extern {
            if got {
                return Err(decode_error(
                    "a POINTER_TO_GOT relocation must name a symbol",
                ));
            }
            // A local relocation's symbolnum is a 1-based section ordinal and
            // the literal field already holds the target's object address.
            return Ok(Term::Address(0));
        }
        let symbol = self.symbol(reloc.symbolnum)?;
        if got {
            return Ok(Term::GotOf(symbol.name.clone()));
        }
        if symbol.is_defined() {
            Ok(Term::Address(symbol.n_value))
        } else if symbol.is_undefined() {
            Ok(Term::Import(symbol.name.clone()))
        } else {
            Err(decode_error(format!(
                "relocation names symbol `{}` of unsupported type {:#x}",
                symbol.name, symbol.n_type
            )))
        }
    }

    /// Resolve the `width`-byte field at `offset` of section `section_index`
    /// through its relocation records. Only the record shapes an object's
    /// unwind and exception sections may carry are accepted: none, one
    /// UNSIGNED, a SUBTRACTOR/UNSIGNED pair, or one pc-relative
    /// POINTER_TO_GOT.
    pub(crate) fn field(
        &self,
        section_index: usize,
        offset: u32,
        width: usize,
    ) -> Result<FieldValue, Violation> {
        let section = &self.sections[section_index];
        let start = offset as usize;
        let bytes = section
            .bytes
            .get(start..start.saturating_add(width))
            .ok_or_else(|| {
                decode_error(format!(
                    "{width}-byte field at {},{}+{offset} is out of bounds",
                    section.segname, section.sectname
                ))
            })?;
        let raw = match width {
            4 => i64::from(i32::from_le_bytes(bytes.try_into().expect("width 4"))),
            8 => i64::from_le_bytes(bytes.try_into().expect("width 8")),
            _ => return Err(decode_error(format!("unsupported field width {width}"))),
        };
        let expected_length = if width == 8 { 3 } else { 2 };
        let relocs = section.relocs_at(offset);
        let where_ = || format!("{},{}+{offset}", section.segname, section.sectname);
        for reloc in &relocs {
            if reloc.length != expected_length {
                return Err(decode_error(format!(
                    "relocation at {} has length {} for a {width}-byte field",
                    where_(),
                    reloc.length
                )));
            }
        }
        match relocs.as_slice() {
            [] => Ok(FieldValue {
                plus: None,
                minus: None,
                addend: raw,
                reloc_pcrel: false,
            }),
            [single] if single.kind == ARM64_RELOC_UNSIGNED && !single.pcrel => {
                let plus = self.symbol_term(*single, false)?;
                Ok(FieldValue {
                    plus: Some(plus),
                    minus: None,
                    addend: raw,
                    reloc_pcrel: false,
                })
            }
            [single] if single.kind == ARM64_RELOC_POINTER_TO_GOT => {
                if !single.pcrel || width != 4 {
                    return Err(decode_error(format!(
                        "POINTER_TO_GOT at {} is not a pc-relative 4-byte field",
                        where_()
                    )));
                }
                Ok(FieldValue {
                    plus: Some(self.symbol_term(*single, true)?),
                    minus: None,
                    addend: raw,
                    reloc_pcrel: true,
                })
            }
            [sub, unsigned]
                if sub.kind == ARM64_RELOC_SUBTRACTOR
                    && unsigned.kind == ARM64_RELOC_UNSIGNED
                    && sub.is_extern
                    && !sub.pcrel
                    && !unsigned.pcrel =>
            {
                Ok(FieldValue {
                    plus: Some(self.symbol_term(*unsigned, false)?),
                    minus: Some(self.symbol_term(*sub, false)?),
                    addend: raw,
                    reloc_pcrel: false,
                })
            }
            other => Err(decode_error(format!(
                "unsupported relocation shape at {}: {other:?}",
                where_()
            ))),
        }
    }
}

/// The object address of `section_index`'s byte at `offset`.
pub(crate) fn address_of(object: &Object, section_index: usize, offset: u32) -> u64 {
    object.sections[section_index]
        .addr
        .saturating_add(u64::from(offset))
}

/// Evaluate a resolved field as a pointer under DWARF `DW_EH_PE` application
/// `pcrel` (relative to the field's own object address `field_address`).
///
/// The result is an object address, an imported symbol, or the GOT slot of a
/// symbol. Mixed forms that cannot be one of those are refused.
pub(crate) fn evaluate_pointer(
    value: &FieldValue,
    pcrel: bool,
    field_address: u64,
) -> Result<Term, Violation> {
    let base = if pcrel { field_address as i128 } else { 0 };
    match (&value.plus, &value.minus) {
        (None, None) => {
            let target = base + i128::from(value.addend);
            u64::try_from(target)
                .map(Term::Address)
                .map_err(|_| decode_error(format!("pointer evaluates to {target}")))
        }
        (Some(Term::Address(a)), None) => {
            let target = base + i128::from(*a) + i128::from(value.addend);
            u64::try_from(target)
                .map(Term::Address)
                .map_err(|_| decode_error(format!("pointer evaluates to {target}")))
        }
        (Some(Term::Address(a)), Some(Term::Address(b))) => {
            let target = base + i128::from(*a) - i128::from(*b) + i128::from(value.addend);
            u64::try_from(target)
                .map(Term::Address)
                .map_err(|_| decode_error(format!("pointer evaluates to {target}")))
        }
        (Some(Term::Import(name)), None) if !pcrel && value.addend == 0 => {
            Ok(Term::Import(name.clone()))
        }
        (Some(Term::GotOf(name)), None) if pcrel && value.reloc_pcrel && value.addend == 0 => {
            Ok(Term::GotOf(name.clone()))
        }
        (plus, minus) => Err(decode_error(format!(
            "pointer field {plus:?} - {minus:?} + {} is not an object address, an import or a GOT slot (pcrel={pcrel})",
            value.addend
        ))),
    }
}
