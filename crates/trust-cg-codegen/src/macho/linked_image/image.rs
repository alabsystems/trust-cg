// trust-cg-codegen/macho/linked_image/image.rs - independent reader for linked arm64 Mach-O images
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Reads a linked arm64 `MH_EXECUTE` or `MH_DYLIB` image from its bytes alone:
//! load commands, segments and sections, the symbol table, the dependent
//! dylibs in ordinal order, the exports trie, and every pointer fixup dyld
//! applies (chained fixups in the `DYLD_CHAINED_PTR_64` and
//! `DYLD_CHAINED_PTR_64_OFFSET` formats, or `LC_DYLD_INFO` rebase, bind, lazy
//! bind and weak bind opcodes). A construct this reader does not model is an
//! error naming it, never skipped: a load command outside the list below,
//! classic relocation entries, threaded binds, compressed import names, or a
//! chain that leaves its page.

use std::collections::{BTreeMap, BTreeSet};

use super::abi::*;

/// One `LC_SEGMENT_64`.
#[derive(Debug, Clone)]
pub(super) struct Segment {
    pub name: String,
    pub vmaddr: u64,
    pub vmsize: u64,
    pub fileoff: u64,
    pub filesize: u64,
    pub maxprot: u32,
    pub initprot: u32,
    pub flags: u32,
}

/// One `section_64` of an image.
#[derive(Debug, Clone)]
pub(super) struct Section {
    pub segment: String,
    pub name: String,
    pub addr: u64,
    pub size: u64,
    pub flags: u32,
    pub reserved2: u32,
}

impl Section {
    pub fn section_type(&self) -> u32 {
        self.flags & SECTION_TYPE
    }

    pub fn is_zero_fill(&self) -> bool {
        matches!(
            self.section_type(),
            S_ZEROFILL | S_GB_ZEROFILL | S_THREAD_LOCAL_ZEROFILL
        )
    }

    /// Pointer slots the static linker synthesizes (GOT, lazy and
    /// TLV-pointer slots): where the image's fixups outside object content
    /// may lie.
    pub fn is_linker_pointer_slots(&self) -> bool {
        matches!(
            self.section_type(),
            S_NON_LAZY_SYMBOL_POINTERS | S_LAZY_SYMBOL_POINTERS | S_THREAD_LOCAL_VARIABLE_POINTERS
        )
    }

    /// A section the static linker fills itself rather than from object
    /// atoms: pointer slots, `__stubs`, ld64's `__stub_helper` and
    /// `__unwind_info`.
    pub fn is_linker_synthesized(&self) -> bool {
        self.is_linker_pointer_slots()
            || self.section_type() == S_SYMBOL_STUBS
            || (self.segment == "__TEXT"
                && matches!(self.name.as_str(), "__stub_helper" | "__unwind_info"))
    }

    pub fn contains(&self, address: u64, len: u64) -> bool {
        address >= self.addr
            && address
                .checked_add(len)
                .is_some_and(|end| end <= self.addr.saturating_add(self.size))
    }

    pub fn label(&self) -> String {
        format!("{},{}", self.segment, self.name)
    }
}

/// A dependent dylib; its ordinal is its index plus one.
#[derive(Debug, Clone)]
pub(super) struct Dylib {
    pub command: &'static str,
    pub install_name: String,
    pub current_version: u32,
    pub compatibility_version: u32,
}

/// One non-debug `nlist_64` of the image.
#[derive(Debug, Clone)]
pub(super) struct ImageSymbol {
    pub name: String,
    pub n_type: u8,
    pub n_value: u64,
}

impl ImageSymbol {
    pub fn is_defined_in_section(&self) -> bool {
        self.n_type & N_TYPE == N_SECT
    }
}

/// One exports-trie terminal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Export {
    pub flags: u64,
    /// Image-relative offset of a regular, thread-local or absolute export.
    pub offset: Option<u64>,
    /// `(ordinal, imported name)` of a re-export.
    pub reexport: Option<(u64, String)>,
}

/// A bind: dyld resolves the pointer to `symbol` of library `ordinal`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Bind {
    pub ordinal: i32,
    pub symbol: String,
    pub addend: i64,
    pub weak_import: bool,
}

/// Every fixup the image's dyld metadata places at one pointer location.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(super) struct Fixup {
    /// Unslid target of a rebase.
    pub rebase: Option<u64>,
    pub bind: Option<Bind>,
    /// `LC_DYLD_INFO` lazy bind (the rebase is then the pre-bind value).
    pub lazy_bind: Option<Bind>,
    /// `LC_DYLD_INFO` weak-bind entry: `(symbol, addend)`.
    pub weak_bind: Option<(String, i64)>,
}

/// What a pointer location holds once dyld has applied its fixups.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Resolution {
    /// A rebase: the unslid address `target`, slid with the image.
    Local { target: u64 },
    /// A bind to an import (or a special ordinal other than weak lookup).
    Import {
        ordinal: i32,
        symbol: String,
        addend: i64,
        weak_import: bool,
        lazy: bool,
    },
    /// dyld's weak-definition lookup of `symbol`: the first definition in
    /// load order. `fallback` is the image's own address when the metadata
    /// records one (an `LC_DYLD_INFO` rebase under a weak-bind entry).
    WeakLookup {
        symbol: String,
        addend: i64,
        fallback: Option<u64>,
    },
}

impl Fixup {
    /// The effective resolution, or why the combination is not modeled.
    pub fn resolution(&self) -> Result<Resolution, String> {
        match (&self.rebase, &self.bind, &self.lazy_bind, &self.weak_bind) {
            (Some(target), None, None, None) => Ok(Resolution::Local { target: *target }),
            (None, Some(bind), None, None) => Ok(bind_resolution(bind, false)),
            (Some(_), None, Some(bind), None) => Ok(bind_resolution(bind, true)),
            (Some(target), None, None, Some((symbol, addend))) => Ok(Resolution::WeakLookup {
                symbol: symbol.clone(),
                addend: *addend,
                fallback: Some(*target),
            }),
            _ => Err(format!("an unmodeled combination of fixups: {self:?}")),
        }
    }
}

fn bind_resolution(bind: &Bind, lazy: bool) -> Resolution {
    if bind.ordinal == BIND_SPECIAL_DYLIB_WEAK_LOOKUP {
        Resolution::WeakLookup {
            symbol: bind.symbol.clone(),
            addend: bind.addend,
            fallback: None,
        }
    } else {
        Resolution::Import {
            ordinal: bind.ordinal,
            symbol: bind.symbol.clone(),
            addend: bind.addend,
            weak_import: bind.weak_import,
            lazy,
        }
    }
}

/// Which dyld metadata carries the fixups.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FixupFormat {
    ChainedPtr64,
    ChainedPtr64Offset,
    DyldInfo,
    None,
}

impl FixupFormat {
    pub fn label(self) -> &'static str {
        match self {
            Self::ChainedPtr64 => "LC_DYLD_CHAINED_FIXUPS DYLD_CHAINED_PTR_64",
            Self::ChainedPtr64Offset => "LC_DYLD_CHAINED_FIXUPS DYLD_CHAINED_PTR_64_OFFSET",
            Self::DyldInfo => "LC_DYLD_INFO_ONLY opcodes",
            Self::None => "none",
        }
    }
}

/// `LC_BUILD_VERSION`.
#[derive(Debug, Clone)]
pub(super) struct BuildVersion {
    pub platform: u32,
    pub minos: u32,
    pub sdk: u32,
    pub tools: Vec<(u32, u32)>,
}

/// A parsed linked image.
#[derive(Debug)]
pub(super) struct Image<'a> {
    pub bytes: &'a [u8],
    pub filetype: u32,
    pub flags: u32,
    /// Unslid address of the Mach-O header.
    pub base: u64,
    pub segments: Vec<Segment>,
    pub sections: Vec<Section>,
    pub dylibs: Vec<Dylib>,
    pub install_name: Option<String>,
    pub entry_offset: Option<u64>,
    pub dylinker: Option<String>,
    pub uuid: Option<[u8; 16]>,
    pub build: Option<BuildVersion>,
    pub rpaths: Vec<String>,
    pub load_commands: Vec<String>,
    pub symbols: Vec<ImageSymbol>,
    pub exports: BTreeMap<String, Export>,
    pub fixups: BTreeMap<u64, Fixup>,
    pub fixup_format: FixupFormat,
    /// `LC_DYLD_INFO` weak-bind names marked `BIND_SYMBOL_FLAGS_NON_WEAK_DEFINITION`.
    pub strong_overrides: BTreeSet<String>,
    pub code_signature: Option<(u32, u32)>,
}

type Parse<T> = Result<T, String>;

fn need<T>(value: Option<T>, what: &str) -> Parse<T> {
    value.ok_or_else(|| format!("truncated or out-of-range {what}"))
}

fn load_command_name(cmd: u32) -> Option<&'static str> {
    Some(match cmd {
        LC_SEGMENT_64 => "LC_SEGMENT_64",
        LC_SYMTAB => "LC_SYMTAB",
        LC_DYSYMTAB => "LC_DYSYMTAB",
        LC_LOAD_DYLIB => "LC_LOAD_DYLIB",
        LC_ID_DYLIB => "LC_ID_DYLIB",
        LC_LOAD_DYLINKER => "LC_LOAD_DYLINKER",
        LC_LOAD_WEAK_DYLIB => "LC_LOAD_WEAK_DYLIB",
        LC_UUID => "LC_UUID",
        LC_RPATH => "LC_RPATH",
        LC_CODE_SIGNATURE => "LC_CODE_SIGNATURE",
        LC_REEXPORT_DYLIB => "LC_REEXPORT_DYLIB",
        LC_DYLD_INFO => "LC_DYLD_INFO",
        LC_DYLD_INFO_ONLY => "LC_DYLD_INFO_ONLY",
        LC_LOAD_UPWARD_DYLIB => "LC_LOAD_UPWARD_DYLIB",
        LC_LAZY_LOAD_DYLIB => "LC_LAZY_LOAD_DYLIB",
        LC_VERSION_MIN_MACOSX => "LC_VERSION_MIN_MACOSX",
        LC_FUNCTION_STARTS => "LC_FUNCTION_STARTS",
        LC_MAIN => "LC_MAIN",
        LC_DATA_IN_CODE => "LC_DATA_IN_CODE",
        LC_SOURCE_VERSION => "LC_SOURCE_VERSION",
        LC_NOTE => "LC_NOTE",
        LC_BUILD_VERSION => "LC_BUILD_VERSION",
        LC_DYLD_EXPORTS_TRIE => "LC_DYLD_EXPORTS_TRIE",
        LC_DYLD_CHAINED_FIXUPS => "LC_DYLD_CHAINED_FIXUPS",
        LC_ATOM_INFO => "LC_ATOM_INFO",
        _ => return None,
    })
}

/// `(dataoff, datasize)` of a `linkedit_data_command`, checked against the file.
fn linkedit_range(bytes: &[u8], at: usize, what: &str) -> Parse<(usize, usize)> {
    let off = need(read_u32(bytes, at + 8), what)? as usize;
    let size = need(read_u32(bytes, at + 12), what)? as usize;
    let end = off
        .checked_add(size)
        .filter(|end| *end <= bytes.len())
        .ok_or_else(|| format!("{what} lies outside the file"))?;
    Ok((off, end))
}

fn dylib_name(bytes: &[u8], at: usize, cmdsize: usize, what: &str) -> Parse<String> {
    let offset = need(read_u32(bytes, at + 8), what)? as usize;
    if offset >= cmdsize {
        return Err(format!("{what} name offset lies outside the command"));
    }
    need(c_string(bytes, at + offset, at + cmdsize), what)
}

impl<'a> Image<'a> {
    /// Parse `bytes` as a thin little-endian arm64 executable or dylib.
    pub fn parse(bytes: &'a [u8]) -> Parse<Self> {
        let magic = need(read_u32(bytes, 0), "mach header")?;
        if magic == FAT_MAGIC || magic == FAT_CIGAM {
            return Err("a universal (fat) file; record each thin slice separately".into());
        }
        if magic != MH_MAGIC_64 {
            return Err(format!("magic {magic:#x} is not MH_MAGIC_64"));
        }
        let cputype = need(read_u32(bytes, 4), "mach header")?;
        if cputype != CPU_TYPE_ARM64 {
            return Err(format!("cputype {cputype:#x} is not CPU_TYPE_ARM64"));
        }
        let cpusubtype = need(read_u32(bytes, 8), "mach header")?;
        if cpusubtype & 0x00FF_FFFF != 0 {
            return Err(format!(
                "cpusubtype {cpusubtype:#x} is not CPU_SUBTYPE_ARM64_ALL (arm64e images are not modeled)"
            ));
        }
        let filetype = need(read_u32(bytes, 12), "mach header")?;
        if filetype != MH_EXECUTE && filetype != MH_DYLIB {
            return Err(format!(
                "filetype {filetype:#x} is neither MH_EXECUTE nor MH_DYLIB"
            ));
        }
        let ncmds = need(read_u32(bytes, 16), "mach header")? as usize;
        let sizeofcmds = need(read_u32(bytes, 20), "mach header")? as usize;
        let flags = need(read_u32(bytes, 24), "mach header")?;
        let commands_end = 32usize
            .checked_add(sizeofcmds)
            .filter(|end| *end <= bytes.len())
            .ok_or("load commands exceed the file")?;

        let mut image = Image {
            bytes,
            filetype,
            flags,
            base: 0,
            segments: Vec::new(),
            sections: Vec::new(),
            dylibs: Vec::new(),
            install_name: None,
            entry_offset: None,
            dylinker: None,
            uuid: None,
            build: None,
            rpaths: Vec::new(),
            load_commands: Vec::new(),
            symbols: Vec::new(),
            exports: BTreeMap::new(),
            fixups: BTreeMap::new(),
            fixup_format: FixupFormat::None,
            strong_overrides: BTreeSet::new(),
            code_signature: None,
        };
        let mut symtab = None;
        let mut chained = None;
        let mut dyld_info = None;
        let mut exports_trie = None;
        let mut at = 32usize;
        for index in 0..ncmds {
            let what = format!("load command {index}");
            let cmd = need(read_u32(bytes, at), &what)?;
            let cmdsize = need(read_u32(bytes, at + 4), &what)? as usize;
            let end = at
                .checked_add(cmdsize)
                .filter(|end| cmdsize >= 8 && *end <= commands_end)
                .ok_or_else(|| format!("{what} exceeds sizeofcmds"))?;
            let name = load_command_name(cmd).ok_or_else(|| {
                format!("{what} ({cmd:#x}) is not a load command this replay models")
            })?;
            image.load_commands.push(name.to_string());
            match cmd {
                LC_SEGMENT_64 => image.parse_segment(at, cmdsize)?,
                LC_SYMTAB => symtab = Some(at),
                LC_DYSYMTAB => {
                    let extrel = need(read_u32(bytes, at + 68), "LC_DYSYMTAB")?;
                    let locrel = need(read_u32(bytes, at + 76), "LC_DYSYMTAB")?;
                    if extrel != 0 || locrel != 0 {
                        return Err(
                            "LC_DYSYMTAB lists classic external or local relocation entries, \
                             which this replay does not model"
                                .into(),
                        );
                    }
                }
                LC_LOAD_DYLIB | LC_LOAD_WEAK_DYLIB | LC_REEXPORT_DYLIB | LC_LOAD_UPWARD_DYLIB
                | LC_LAZY_LOAD_DYLIB => {
                    image.dylibs.push(Dylib {
                        command: name,
                        install_name: dylib_name(bytes, at, cmdsize, name)?,
                        current_version: need(read_u32(bytes, at + 16), name)?,
                        compatibility_version: need(read_u32(bytes, at + 20), name)?,
                    });
                }
                LC_ID_DYLIB => {
                    if image.install_name.is_some() {
                        return Err("more than one LC_ID_DYLIB".into());
                    }
                    image.install_name = Some(dylib_name(bytes, at, cmdsize, name)?);
                }
                LC_LOAD_DYLINKER => {
                    image.dylinker = Some(dylib_name(bytes, at, cmdsize, name)?);
                }
                LC_RPATH => image.rpaths.push(dylib_name(bytes, at, cmdsize, name)?),
                LC_UUID => {
                    let raw = need(bytes.get(at + 8..at + 24), "LC_UUID")?;
                    image.uuid = Some(raw.try_into().map_err(|_| "LC_UUID")?);
                }
                LC_MAIN => {
                    if image.entry_offset.is_some() {
                        return Err("more than one LC_MAIN".into());
                    }
                    image.entry_offset = Some(need(read_u64(bytes, at + 8), name)?);
                }
                LC_BUILD_VERSION => {
                    let ntools = need(read_u32(bytes, at + 20), name)? as usize;
                    if 24 + ntools * 8 > cmdsize {
                        return Err("LC_BUILD_VERSION tools exceed the command".into());
                    }
                    let mut tools = Vec::with_capacity(ntools);
                    for tool in 0..ntools {
                        let entry = at + 24 + tool * 8;
                        tools.push((
                            need(read_u32(bytes, entry), name)?,
                            need(read_u32(bytes, entry + 4), name)?,
                        ));
                    }
                    image.build = Some(BuildVersion {
                        platform: need(read_u32(bytes, at + 8), name)?,
                        minos: need(read_u32(bytes, at + 12), name)?,
                        sdk: need(read_u32(bytes, at + 16), name)?,
                        tools,
                    });
                }
                LC_DYLD_CHAINED_FIXUPS => {
                    if chained.replace(linkedit_range(bytes, at, name)?).is_some() {
                        return Err("more than one LC_DYLD_CHAINED_FIXUPS".into());
                    }
                }
                LC_DYLD_EXPORTS_TRIE => {
                    if exports_trie
                        .replace(linkedit_range(bytes, at, name)?)
                        .is_some()
                    {
                        return Err("more than one exports trie".into());
                    }
                }
                LC_DYLD_INFO | LC_DYLD_INFO_ONLY => {
                    if dyld_info.replace(at).is_some() {
                        return Err("more than one LC_DYLD_INFO".into());
                    }
                }
                LC_CODE_SIGNATURE => {
                    let (off, end) = linkedit_range(bytes, at, name)?;
                    image.code_signature = Some((off as u32, (end - off) as u32));
                }
                _ => {}
            }
            at = end;
        }

        image.base = image
            .segments
            .iter()
            .find(|segment| segment.fileoff == 0 && segment.filesize > 0)
            .map(|segment| segment.vmaddr)
            .ok_or("no segment maps the Mach-O header")?;
        if let Some(at) = symtab {
            image.parse_symtab(at)?;
        }
        if chained.is_some() && dyld_info.is_some() {
            return Err("both chained fixups and LC_DYLD_INFO are present".into());
        }
        if let Some((start, end)) = chained {
            image.parse_chained_fixups(start, end)?;
        }
        if let Some(at) = dyld_info {
            image.parse_dyld_info(at)?;
            let export_off = need(read_u32(bytes, at + 40), "LC_DYLD_INFO")? as usize;
            let export_size = need(read_u32(bytes, at + 44), "LC_DYLD_INFO")? as usize;
            if export_size != 0 {
                let end = export_off
                    .checked_add(export_size)
                    .filter(|end| *end <= bytes.len())
                    .ok_or("LC_DYLD_INFO exports lie outside the file")?;
                if exports_trie.replace((export_off, end)).is_some() {
                    return Err("exports trie named by two load commands".into());
                }
            }
        }
        if let Some((start, end)) = exports_trie {
            image.exports = parse_exports_trie(&bytes[start..end])?;
        }
        Ok(image)
    }

    fn parse_segment(&mut self, at: usize, cmdsize: usize) -> Parse<()> {
        let bytes = self.bytes;
        let what = "LC_SEGMENT_64";
        let segment = Segment {
            name: need(fixed_name(bytes, at + 8), what)?,
            vmaddr: need(read_u64(bytes, at + 24), what)?,
            vmsize: need(read_u64(bytes, at + 32), what)?,
            fileoff: need(read_u64(bytes, at + 40), what)?,
            filesize: need(read_u64(bytes, at + 48), what)?,
            maxprot: need(read_u32(bytes, at + 56), what)?,
            initprot: need(read_u32(bytes, at + 60), what)?,
            flags: need(read_u32(bytes, at + 68), what)?,
        };
        let nsects = need(read_u32(bytes, at + 64), what)? as usize;
        if 72 + nsects * 80 > cmdsize {
            return Err(format!(
                "segment {} sections exceed the command",
                segment.name
            ));
        }
        segment
            .fileoff
            .checked_add(segment.filesize)
            .filter(|end| *end <= bytes.len() as u64)
            .ok_or_else(|| format!("segment {} lies outside the file", segment.name))?;
        if segment.filesize > segment.vmsize {
            return Err(format!(
                "segment {} maps more file bytes than its virtual size",
                segment.name
            ));
        }
        for index in 0..nsects {
            let header = at + 72 + index * 80;
            let section = Section {
                name: need(fixed_name(bytes, header), what)?,
                segment: need(fixed_name(bytes, header + 16), what)?,
                addr: need(read_u64(bytes, header + 32), what)?,
                size: need(read_u64(bytes, header + 40), what)?,
                flags: need(read_u32(bytes, header + 64), what)?,
                reserved2: need(read_u32(bytes, header + 72), what)?,
            };
            let nreloc = need(read_u32(bytes, header + 60), what)?;
            if nreloc != 0 {
                return Err(format!(
                    "section {} carries {nreloc} classic relocation entries, which this replay \
                     does not model",
                    section.label()
                ));
            }
            let end = section
                .addr
                .checked_add(section.size)
                .ok_or_else(|| format!("section {} overflows", section.label()))?;
            if section.addr < segment.vmaddr || end > segment.vmaddr.saturating_add(segment.vmsize)
            {
                return Err(format!(
                    "section {} lies outside segment {}",
                    section.label(),
                    segment.name
                ));
            }
            if !section.is_zero_fill() && end > segment.vmaddr.saturating_add(segment.filesize) {
                return Err(format!(
                    "file-backed section {} extends past its segment's file bytes",
                    section.label()
                ));
            }
            self.sections.push(section);
        }
        self.segments.push(segment);
        Ok(())
    }

    fn parse_symtab(&mut self, at: usize) -> Parse<()> {
        let bytes = self.bytes;
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
            if n_type & N_STAB != 0 {
                continue;
            }
            let name = if strx == 0 {
                String::new()
            } else {
                need(
                    c_string(bytes, stroff.saturating_add(strx), strend),
                    "symbol name",
                )?
            };
            self.symbols.push(ImageSymbol {
                name,
                n_type,
                n_value: need(read_u64(bytes, entry + 8), "nlist_64")?,
            });
        }
        Ok(())
    }

    /// `<mach-o/fixup-chains.h>` chains.
    fn parse_chained_fixups(&mut self, start: usize, end: usize) -> Parse<()> {
        let bytes = self.bytes;
        let data = &bytes[start..end];
        let what = "chained fixups header";
        let version = need(read_u32(data, 0), what)?;
        let starts_offset = need(read_u32(data, 4), what)? as usize;
        let imports_offset = need(read_u32(data, 8), what)? as usize;
        let symbols_offset = need(read_u32(data, 12), what)? as usize;
        let imports_count = need(read_u32(data, 16), what)? as usize;
        let imports_format = need(read_u32(data, 20), what)?;
        let symbols_format = need(read_u32(data, 24), what)?;
        if version != 0 {
            return Err(format!("chained fixups version {version} is not 0"));
        }
        if symbols_format != 0 {
            return Err("compressed chained-import names are not modeled".into());
        }
        let entry_size = match imports_format {
            DYLD_CHAINED_IMPORT => 4,
            DYLD_CHAINED_IMPORT_ADDEND => 8,
            DYLD_CHAINED_IMPORT_ADDEND64 => 16,
            other => return Err(format!("chained imports format {other} is not modeled")),
        };
        let mut imports = Vec::with_capacity(imports_count);
        for index in 0..imports_count {
            let entry = imports_offset + index * entry_size;
            let (ordinal, weak_import, name_offset, addend) = match imports_format {
                DYLD_CHAINED_IMPORT | DYLD_CHAINED_IMPORT_ADDEND => {
                    let raw = need(read_u32(data, entry), "chained import")?;
                    let addend = if imports_format == DYLD_CHAINED_IMPORT_ADDEND {
                        i64::from(need(read_u32(data, entry + 4), "chained import")? as i32)
                    } else {
                        0
                    };
                    (
                        i32::from((raw & 0xFF) as u8 as i8),
                        raw & 0x100 != 0,
                        (raw >> 9) as usize,
                        addend,
                    )
                }
                _ => {
                    let raw = need(read_u64(data, entry), "chained import")?;
                    if (raw >> 17) & 0x7FFF != 0 {
                        return Err("reserved bits of a chained import are set".into());
                    }
                    (
                        i32::from((raw & 0xFFFF) as u16 as i16),
                        raw & 0x1_0000 != 0,
                        (raw >> 32) as usize,
                        need(read_u64(data, entry + 8), "chained import")? as i64,
                    )
                }
            };
            let symbol = need(
                c_string(data, symbols_offset.saturating_add(name_offset), data.len()),
                "chained import name",
            )?;
            imports.push(Bind {
                ordinal,
                symbol,
                addend,
                weak_import,
            });
        }

        let seg_count = need(read_u32(data, starts_offset), "chained starts")? as usize;
        if seg_count != self.segments.len() {
            return Err(format!(
                "chained starts cover {seg_count} segments, the image has {}",
                self.segments.len()
            ));
        }
        let mut format = None;
        for segment_index in 0..seg_count {
            let info = need(
                read_u32(data, starts_offset + 4 + segment_index * 4),
                "chained starts",
            )? as usize;
            if info == 0 {
                continue;
            }
            let seg = starts_offset + info;
            let what = "chained starts in segment";
            let page_size = u64::from(need(read_u16(data, seg + 4), what)?);
            let pointer_format = need(read_u16(data, seg + 6), what)?;
            let segment_offset = need(read_u64(data, seg + 8), what)?;
            let page_count = need(read_u16(data, seg + 20), what)? as u64;
            let this_format = match pointer_format {
                DYLD_CHAINED_PTR_64 => FixupFormat::ChainedPtr64,
                DYLD_CHAINED_PTR_64_OFFSET => FixupFormat::ChainedPtr64Offset,
                other => {
                    return Err(format!(
                        "chained pointer format {other} is not modeled (arm64 images use 2 or 6)"
                    ));
                }
            };
            if *format.get_or_insert(this_format) != this_format {
                return Err("segments use different chained pointer formats".into());
            }
            if page_size != 0x4000 && page_size != 0x1000 {
                return Err(format!("chained page size {page_size:#x} is not modeled"));
            }
            let segment = self.segments[segment_index].clone();
            if segment.vmaddr.checked_sub(self.base) != Some(segment_offset) {
                return Err(format!(
                    "chained starts place segment {} at offset {segment_offset:#x}, its load \
                     command at {:#x}",
                    segment.name, segment.vmaddr
                ));
            }
            for page in 0..page_count {
                let first = need(
                    read_u16(data, seg + 22 + page as usize * 2),
                    "chained page start",
                )?;
                if first == DYLD_CHAINED_PTR_START_NONE {
                    continue;
                }
                if first & DYLD_CHAINED_PTR_START_MULTI != 0 {
                    return Err("multiple chain starts per page are not modeled".into());
                }
                let page_base = page * page_size;
                let mut offset = page_base + u64::from(first);
                loop {
                    if offset + 8 > segment.filesize || offset >= page_base + page_size {
                        return Err(format!(
                            "a chain in segment {} leaves its page or file bytes",
                            segment.name
                        ));
                    }
                    let file = (segment.fileoff + offset) as usize;
                    let raw = need(read_u64(bytes, file), "chained pointer")?;
                    let address = segment.vmaddr.wrapping_add(offset);
                    let mut fixup = Fixup::default();
                    if raw >> 63 == 1 {
                        if (raw >> 32) & 0x7_FFFF != 0 {
                            return Err(format!(
                                "reserved bits of the chained bind at {address:#x} are set"
                            ));
                        }
                        let index = (raw & 0xFF_FFFF) as usize;
                        let mut bind = imports.get(index).cloned().ok_or_else(|| {
                            format!(
                                "chained bind at {address:#x} names import {index} of {}",
                                imports.len()
                            )
                        })?;
                        bind.addend += ((raw >> 24) & 0xFF) as i64;
                        fixup.bind = Some(bind);
                    } else {
                        if (raw >> 44) & 0x7F != 0 {
                            return Err(format!(
                                "reserved bits of the chained rebase at {address:#x} are set"
                            ));
                        }
                        let target = raw & 0xF_FFFF_FFFF;
                        let high8 = ((raw >> 36) & 0xFF) << 56;
                        let unslid = match this_format {
                            FixupFormat::ChainedPtr64 => target | high8,
                            _ => self.base.wrapping_add(target) | high8,
                        };
                        fixup.rebase = Some(unslid);
                    }
                    if self.fixups.insert(address, fixup).is_some() {
                        return Err(format!("two chain entries at {address:#x}"));
                    }
                    let next = (raw >> 51) & 0xFFF;
                    if next == 0 {
                        break;
                    }
                    offset += next * 4;
                }
            }
        }
        self.fixup_format = format.unwrap_or(FixupFormat::ChainedPtr64Offset);
        Ok(())
    }

    /// Address of `segment_index` plus `offset`, for dyld-info opcodes.
    fn opcode_address(&self, segment_index: usize, offset: u64, what: &str) -> Parse<u64> {
        let segment = self
            .segments
            .get(segment_index)
            .ok_or_else(|| format!("{what} names segment {segment_index}"))?;
        if offset.checked_add(8).is_none_or(|end| end > segment.vmsize) {
            return Err(format!(
                "{what} writes {offset:#x} beyond segment {}",
                segment.name
            ));
        }
        Ok(segment.vmaddr.wrapping_add(offset))
    }

    fn file_pointer(&self, address: u64) -> Parse<u64> {
        let file = self
            .file_offset(address, 8)
            .ok_or_else(|| format!("fixup location {address:#x} has no file bytes"))?;
        need(read_u64(self.bytes, file), "pointer")
    }

    /// `LC_DYLD_INFO` rebase and bind opcodes (`<mach-o/loader.h>`).
    fn parse_dyld_info(&mut self, at: usize) -> Parse<()> {
        let bytes = self.bytes;
        let range = |field: usize| -> Parse<(usize, usize)> {
            let off = need(read_u32(bytes, at + field), "LC_DYLD_INFO")? as usize;
            let size = need(read_u32(bytes, at + field + 4), "LC_DYLD_INFO")? as usize;
            let end = off
                .checked_add(size)
                .filter(|end| *end <= bytes.len())
                .ok_or("LC_DYLD_INFO opcodes lie outside the file")?;
            Ok((off, end))
        };
        self.fixup_format = FixupFormat::DyldInfo;

        // Rebase opcodes.
        let (mut pc, end) = range(8)?;
        let (mut segment, mut offset) = (usize::MAX, 0u64);
        let mut rebases: Vec<u64> = Vec::new();
        while pc < end {
            let byte = bytes[pc];
            pc += 1;
            let (opcode, immediate) = (byte & 0xF0, u64::from(byte & 0x0F));
            let what = "rebase opcode";
            let mut rebase = |segment: usize, offset: u64| -> Parse<()> {
                rebases.push(self.opcode_address(segment, offset, what)?);
                Ok(())
            };
            match opcode {
                0x00 => break,
                0x10 => {
                    if immediate != 1 {
                        return Err(format!(
                            "rebase type {immediate} is not REBASE_TYPE_POINTER"
                        ));
                    }
                }
                0x20 => {
                    segment = immediate as usize;
                    offset = need(read_uleb(bytes, &mut pc, end), what)?;
                }
                0x30 => offset = offset.wrapping_add(need(read_uleb(bytes, &mut pc, end), what)?),
                0x40 => offset = offset.wrapping_add(immediate * 8),
                0x50 => {
                    for _ in 0..immediate {
                        rebase(segment, offset)?;
                        offset = offset.wrapping_add(8);
                    }
                }
                0x60 => {
                    let count = need(read_uleb(bytes, &mut pc, end), what)?;
                    for _ in 0..count.min(1 << 24) {
                        rebase(segment, offset)?;
                        offset = offset.wrapping_add(8);
                    }
                }
                0x70 => {
                    rebase(segment, offset)?;
                    offset = offset
                        .wrapping_add(need(read_uleb(bytes, &mut pc, end), what)?)
                        .wrapping_add(8);
                }
                0x80 => {
                    let count = need(read_uleb(bytes, &mut pc, end), what)?;
                    let skip = need(read_uleb(bytes, &mut pc, end), what)?;
                    for _ in 0..count.min(1 << 24) {
                        rebase(segment, offset)?;
                        offset = offset.wrapping_add(skip).wrapping_add(8);
                    }
                }
                other => return Err(format!("rebase opcode {other:#x} is not modeled")),
            }
        }
        for address in rebases {
            let target = self.file_pointer(address)?;
            let entry = self.fixups.entry(address).or_default();
            if entry.rebase.replace(target).is_some() {
                return Err(format!("two rebases at {address:#x}"));
            }
        }

        // Bind, lazy-bind and weak-bind opcodes share one encoding.
        for (field, kind) in [
            (16, BindKind::Bind),
            (32, BindKind::Lazy),
            (24, BindKind::Weak),
        ] {
            let (start, end) = range(field)?;
            for (address, bind) in self.decode_binds(start, end, kind)? {
                let entry = self.fixups.entry(address).or_default();
                let clash = match kind {
                    BindKind::Bind => entry.bind.replace(bind).is_some(),
                    BindKind::Lazy => entry.lazy_bind.replace(bind).is_some(),
                    BindKind::Weak => entry
                        .weak_bind
                        .replace((bind.symbol, bind.addend))
                        .is_some(),
                };
                if clash {
                    return Err(format!("two {kind:?} entries at {address:#x}"));
                }
            }
        }
        Ok(())
    }

    fn decode_binds(
        &mut self,
        start: usize,
        end: usize,
        kind: BindKind,
    ) -> Parse<Vec<(u64, Bind)>> {
        let bytes = self.bytes;
        let what = "bind opcode";
        let mut out = Vec::new();
        let mut pc = start;
        let (mut segment, mut offset) = (usize::MAX, 0u64);
        let (mut ordinal, mut symbol, mut addend, mut flags) = (0i32, String::new(), 0i64, 0u8);
        while pc < end {
            let byte = bytes[pc];
            pc += 1;
            let (opcode, immediate) = (byte & 0xF0, byte & 0x0F);
            match opcode {
                0x00 => {
                    if kind != BindKind::Lazy {
                        break;
                    }
                }
                0x10 => ordinal = i32::from(immediate),
                0x20 => {
                    ordinal = i32::try_from(need(read_uleb(bytes, &mut pc, end), what)?)
                        .map_err(|_| "bind ordinal overflows")?
                }
                0x30 => {
                    ordinal = if immediate == 0 {
                        0
                    } else {
                        i32::from((0xF0 | immediate) as i8)
                    }
                }
                0x40 => {
                    flags = immediate;
                    let name_end = bytes[pc..end]
                        .iter()
                        .position(|&b| b == 0)
                        .ok_or("unterminated bind symbol name")?;
                    symbol = String::from_utf8_lossy(&bytes[pc..pc + name_end]).into_owned();
                    pc += name_end + 1;
                    if kind == BindKind::Weak && flags & 0x8 != 0 {
                        self.strong_overrides.insert(symbol.clone());
                    }
                }
                0x50 => {
                    if immediate != 1 {
                        return Err(format!("bind type {immediate} is not BIND_TYPE_POINTER"));
                    }
                }
                0x60 => addend = need(read_sleb(bytes, &mut pc, end), what)?,
                0x70 => {
                    segment = usize::from(immediate);
                    offset = need(read_uleb(bytes, &mut pc, end), what)?;
                }
                0x80 => offset = offset.wrapping_add(need(read_uleb(bytes, &mut pc, end), what)?),
                0x90 | 0xA0 | 0xB0 | 0xC0 => {
                    let (count, skip) = match opcode {
                        0x90 => (1, 0),
                        0xA0 => (1, need(read_uleb(bytes, &mut pc, end), what)?),
                        0xB0 => (1, u64::from(immediate) * 8),
                        _ => (
                            need(read_uleb(bytes, &mut pc, end), what)?,
                            need(read_uleb(bytes, &mut pc, end), what)?,
                        ),
                    };
                    for _ in 0..count.min(1 << 24) {
                        let address = self.opcode_address(segment, offset, what)?;
                        out.push((
                            address,
                            Bind {
                                ordinal,
                                symbol: symbol.clone(),
                                addend,
                                weak_import: flags & 0x1 != 0,
                            },
                        ));
                        offset = offset.wrapping_add(8).wrapping_add(skip);
                    }
                }
                0xD0 => return Err("threaded bind opcodes are not modeled".into()),
                other => return Err(format!("bind opcode {other:#x} is not modeled")),
            }
        }
        Ok(out)
    }

    /// File offset of `[address, address + len)` when every byte is file-backed.
    pub fn file_offset(&self, address: u64, len: u64) -> Option<usize> {
        self.segments.iter().find_map(|segment| {
            let start = address.checked_sub(segment.vmaddr)?;
            let end = start.checked_add(len)?;
            (end <= segment.filesize).then(|| (segment.fileoff + start) as usize)
        })
    }

    pub fn read(&self, address: u64, len: u64) -> Option<&'a [u8]> {
        let at = self.file_offset(address, len)?;
        self.bytes.get(at..at + len as usize)
    }

    pub fn read_u32_at(&self, address: u64) -> Option<u32> {
        self.read(address, 4)
            .map(|raw| u32::from_le_bytes(raw.try_into().expect("four bytes")))
    }

    pub fn read_u64_at(&self, address: u64) -> Option<u64> {
        self.read(address, 8)
            .map(|raw| u64::from_le_bytes(raw.try_into().expect("eight bytes")))
    }

    pub fn segment_at(&self, address: u64) -> Option<&Segment> {
        self.segments.iter().find(|segment| {
            address >= segment.vmaddr && address < segment.vmaddr.saturating_add(segment.vmsize)
        })
    }

    pub fn section_at(&self, address: u64, len: u64) -> Option<&Section> {
        self.sections
            .iter()
            .find(|section| section.contains(address, len.max(1)))
    }

    /// The slot a `__stubs` entry at `address` loads and branches through.
    pub fn stub_slot(&self, address: u64) -> Result<u64, String> {
        let section = self
            .section_at(address, 12)
            .filter(|section| section.section_type() == S_SYMBOL_STUBS)
            .ok_or_else(|| format!("{address:#x} is not in an S_SYMBOL_STUBS section"))?;
        let stride = if section.reserved2 == 0 {
            12
        } else {
            u64::from(section.reserved2)
        };
        if stride != 12 || !(address - section.addr).is_multiple_of(stride) {
            return Err(format!(
                "{address:#x} is not the start of a 12-byte stub of {}",
                section.label()
            ));
        }
        let word = |at: u64| {
            self.read_u32_at(at)
                .ok_or_else(|| format!("stub word at {at:#x} has no file bytes"))
        };
        let (adrp, ldr, br) = (word(address)?, word(address + 4)?, word(address + 8)?);
        if adrp & 0x9F00_001F != 0x9000_0010
            || ldr & 0xFFC0_03FF != 0xF940_0210
            || br != 0xD61F_0200
        {
            return Err(format!(
                "the stub at {address:#x} is not `adrp x16; ldr x16, [x16, #off]; br x16` \
                 ({adrp:#010x} {ldr:#010x} {br:#010x})"
            ));
        }
        let page = adrp_target(address, adrp);
        Ok(page.wrapping_add(u64::from((ldr >> 10) & 0xFFF) * 8))
    }

    /// The effective resolution of the pointer at `address`, if it has fixups.
    pub fn resolution_at(&self, address: u64) -> Option<Result<Resolution, String>> {
        self.fixups.get(&address).map(Fixup::resolution)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BindKind {
    Bind,
    Lazy,
    Weak,
}

/// The page an `ADRP` at `pc` materializes.
pub(super) fn adrp_target(pc: u64, word: u32) -> u64 {
    let immlo = u64::from((word >> 29) & 0x3);
    let immhi = u64::from((word >> 5) & 0x7_FFFF);
    let imm = ((immhi << 2) | immlo) << 12;
    // Sign-extend the 33-bit page displacement.
    let imm = ((imm << 31) as i64 >> 31) as u64;
    (pc & !0xFFF).wrapping_add(imm)
}

/// Every terminal of an exports trie, by name.
fn parse_exports_trie(trie: &[u8]) -> Parse<BTreeMap<String, Export>> {
    let mut found = BTreeMap::new();
    let mut pending = vec![(0usize, Vec::new())];
    let mut visited = BTreeSet::new();
    while let Some((node, prefix)) = pending.pop() {
        if !visited.insert(node) || visited.len() > 1 << 20 {
            return Err("the exports trie revisits a node".into());
        }
        let mut at = node;
        let limit = trie.len();
        let terminal = need(read_uleb(trie, &mut at, limit), "exports trie")? as usize;
        let children = at
            .checked_add(terminal)
            .filter(|end| *end <= limit)
            .ok_or("exports trie terminal overruns")?;
        if terminal != 0 {
            let flags = need(read_uleb(trie, &mut at, children), "export flags")?;
            let export = if flags & EXPORT_SYMBOL_FLAGS_REEXPORT != 0 {
                let ordinal = need(read_uleb(trie, &mut at, children), "re-export")?;
                let name = need(c_string(trie, at, children), "re-export name")?;
                Export {
                    flags,
                    offset: None,
                    reexport: Some((ordinal, name)),
                }
            } else {
                Export {
                    flags,
                    offset: Some(need(read_uleb(trie, &mut at, children), "export offset")?),
                    reexport: None,
                }
            };
            let name = String::from_utf8(prefix.clone()).map_err(|_| "non-UTF-8 export")?;
            found.insert(name, export);
        }
        at = children;
        let count = *need(trie.get(at), "exports trie children")?;
        at += 1;
        for _ in 0..count {
            let end = trie[at..]
                .iter()
                .position(|&b| b == 0)
                .map(|len| at + len)
                .ok_or("unterminated exports trie edge")?;
            let mut name = prefix.clone();
            name.extend_from_slice(&trie[at..end]);
            at = end + 1;
            let child = need(read_uleb(trie, &mut at, limit), "exports trie child")? as usize;
            if child >= limit {
                return Err("exports trie child lies outside the trie".into());
            }
            pending.push((child, name));
        }
    }
    Ok(found)
}

/// `(install name, exported names, thread-local exports)` of a dylib image,
/// read independently.
pub(super) fn dylib_exports(bytes: &[u8]) -> Parse<(String, BTreeSet<String>, BTreeSet<String>)> {
    let image = Image::parse(bytes)?;
    if image.filetype != MH_DYLIB {
        return Err("not an MH_DYLIB image".into());
    }
    let install_name = image.install_name.clone().ok_or("no LC_ID_DYLIB")?;
    let thread_locals = image
        .exports
        .iter()
        .filter(|(_, export)| {
            export.flags & EXPORT_SYMBOL_FLAGS_KIND_MASK == EXPORT_SYMBOL_FLAGS_KIND_THREAD_LOCAL
        })
        .map(|(name, _)| name.clone())
        .collect();
    Ok((
        install_name,
        image.exports.keys().cloned().collect(),
        thread_locals,
    ))
}
