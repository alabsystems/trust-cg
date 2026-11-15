// trust-cg-codegen/macho/linked_image/replay.rs - replay object relocations against a linked image
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Placement, relocation replay and the image-level checks behind
//! [`super::record_linked_image`]. Every check appends a named finding; the
//! record is assembled only when none was found.

use std::collections::{BTreeMap, BTreeSet};

use sha2::{Digest, Sha256};
use trust_cg_verify::ObjectRelocationKind;

use super::abi::*;
use super::image::{Image, Resolution, Section, adrp_target};
use super::object::{ObjReloc, ObjSection, Object};
use super::*;

type Findings = Vec<ImageFinding>;

fn finding(findings: &mut Findings, code: &'static str, detail: impl Into<String>) {
    findings.push(ImageFinding {
        code,
        detail: detail.into(),
    });
}

/// How an atom's address was established.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PlacedBy {
    SymbolTable,
    SectionAddress,
    /// Named in no image symbol: dead-stripped, or a coalesced weak copy.
    NotInImage,
    /// Not placed: a weak duplicate another object's copy replaced.
    Coalesced,
}

/// The winning definition of a global name.
#[derive(Debug, Clone, Copy)]
struct Definition {
    object: usize,
    symbol: usize,
}

/// What a relocation's target resolves to.
#[derive(Debug, Clone)]
enum Target {
    Defined {
        name: String,
        object: usize,
        symbol: usize,
        address: Option<u64>,
    },
    Import {
        name: String,
        weak_ref: bool,
    },
}

impl Target {
    fn name(&self) -> &str {
        match self {
            Self::Defined { name, .. } | Self::Import { name, .. } => name,
        }
    }
}

/// GOT-style slot families.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum SlotFamily {
    Got,
    Tlv,
}

/// What a pointer slot's fixup names: an imported or weak-looked-up name,
/// or a rebased address.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum SlotKey {
    Name(String),
    Address(u64),
}

/// A pointer slot of a GOT (`S_NON_LAZY_SYMBOL_POINTERS`) or TLV-pointer
/// (`S_THREAD_LOCAL_VARIABLE_POINTERS`) section.
#[derive(Debug, Clone)]
struct Slot {
    address: u64,
    section_type: u32,
    resolution: Resolution,
}

/// The replay state over one image and its objects.
struct Replay<'r, 'a> {
    image: &'r Image<'a>,
    objects: &'r [Object],
    /// Per object, per atom: image address.
    atom_address: Vec<Vec<Option<u64>>>,
    placed_by: Vec<Vec<PlacedBy>>,
    /// Per object: symbol index -> (atom, offset in atom).
    symbol_atom: Vec<BTreeMap<usize, (usize, u64)>>,
    definitions: BTreeMap<String, Definition>,
    /// Names every referencing object marks `N_WEAK_REF`.
    weak_refs: BTreeMap<String, bool>,
    tlv_base: Option<u64>,
    /// Pointer locations explained by object relocations.
    object_fixups: BTreeSet<u64>,
    /// Slot locations the replay used.
    used_slots: BTreeSet<u64>,
    /// GOT and TLV-pointer slots by what their fixup names.
    slots: BTreeMap<SlotKey, Vec<Slot>>,
    /// Imports reached through `TLVP_LOAD` relocations, and through others.
    tlv_imports: BTreeSet<String>,
    other_imports: BTreeSet<String>,
    findings: Findings,
    rows: Vec<RelocationRecord>,
    consumed: usize,
    paired: usize,
    not_in_image: usize,
    by_kind: BTreeMap<String, usize>,
}

pub(super) fn run(request: &LinkedImageRequest<'_>) -> Result<LinkedImageRecord, Findings> {
    let mut findings = Findings::new();
    let image = match Image::parse(request.image) {
        Ok(image) => image,
        Err(detail) => {
            finding(
                &mut findings,
                CODE_PARSE,
                format!("image {}: {detail}", request.image_name),
            );
            return Err(findings);
        }
    };
    let mut objects = Vec::with_capacity(request.objects.len());
    for input in &request.objects {
        match Object::parse(input.name, input.bytes) {
            Ok(object) => objects.push(object),
            Err(detail) => finding(
                &mut findings,
                CODE_PARSE,
                format!("object {}: {detail}", input.name),
            ),
        }
    }
    if objects.is_empty() && findings.is_empty() {
        finding(&mut findings, CODE_PARSE, "no input objects were given");
    }
    if !findings.is_empty() {
        return Err(findings);
    }
    let signature = match super::super::codesign::verify_ad_hoc_signature(request.image) {
        Ok(signature) => Some(signature),
        Err(error) => {
            finding(&mut findings, CODE_SIGNATURE, error.to_string());
            None
        }
    };
    let mut replay = Replay::new(&image, &objects, findings);
    replay.check_supported();
    replay.place(request.placement);
    replay.resolve_definitions();
    replay.check_placement_against_symbols(request.placement);
    replay.replay_relocations();
    replay.check_content();
    replay.check_unaccounted_content();
    replay.check_protection();
    replay.check_fixup_accounting();
    replay.check_exports();
    replay.check_header();
    let imports = replay.check_binds(&request.providers);
    if !replay.findings.is_empty() {
        return Err(replay.findings);
    }
    let signature = signature.expect("no signature finding");
    Ok(replay.record(request, signature, imports))
}

fn hex_address(address: u64) -> String {
    format!("{address:#x}")
}

fn sign_extend(value: u64, bits: u32) -> i64 {
    ((value << (64 - bits)) as i64) >> (64 - bits)
}

fn inventory_kind(kind: u8) -> ObjectRelocationKind {
    match kind {
        ARM64_RELOC_UNSIGNED => ObjectRelocationKind::AArch64MachOUnsigned,
        ARM64_RELOC_SUBTRACTOR => ObjectRelocationKind::AArch64MachOSubtractor,
        ARM64_RELOC_BRANCH26 => ObjectRelocationKind::AArch64MachOBranch26,
        ARM64_RELOC_PAGE21 => ObjectRelocationKind::AArch64MachOPage21,
        ARM64_RELOC_PAGEOFF12 => ObjectRelocationKind::AArch64MachOPageoff12,
        ARM64_RELOC_GOT_LOAD_PAGE21 => ObjectRelocationKind::AArch64MachOGotLoadPage21,
        ARM64_RELOC_GOT_LOAD_PAGEOFF12 => ObjectRelocationKind::AArch64MachOGotLoadPageoff12,
        ARM64_RELOC_TLVP_LOAD_PAGE21 => ObjectRelocationKind::AArch64MachOTlvpLoadPage21,
        ARM64_RELOC_TLVP_LOAD_PAGEOFF12 => ObjectRelocationKind::AArch64MachOTlvpLoadPageoff12,
        other => ObjectRelocationKind::AArch64MachOOther(other),
    }
}

/// `(scale, non-immediate mask)` of a `PAGEOFF12` instruction: `ADD`
/// (immediate) or an unsigned-offset load/store.
fn pageoff_form(word: u32) -> Option<u32> {
    // ADD (immediate) without the LSL #12 shift.
    if word & 0x7FC0_0000 == 0x1100_0000 {
        return Some(0);
    }
    if word & 0x3B00_0000 == 0x3900_0000 {
        let size = word >> 30;
        let vector = (word >> 26) & 1 == 1;
        let opc = (word >> 22) & 3;
        return Some(if vector && size == 0 && opc >= 2 {
            4
        } else {
            size
        });
    }
    None
}

const IMM12_MASK: u32 = 0xFFC0_03FF;

impl<'r, 'a> Replay<'r, 'a> {
    fn new(image: &'r Image<'a>, objects: &'r [Object], findings: Findings) -> Self {
        let tlv_base = image
            .sections
            .iter()
            .filter(|section| {
                matches!(
                    section.section_type(),
                    S_THREAD_LOCAL_REGULAR | S_THREAD_LOCAL_ZEROFILL
                )
            })
            .map(|section| section.addr)
            .min();
        let mut slots: BTreeMap<SlotKey, Vec<Slot>> = BTreeMap::new();
        for section in &image.sections {
            let section_type = section.section_type();
            if !matches!(
                section_type,
                S_NON_LAZY_SYMBOL_POINTERS | S_THREAD_LOCAL_VARIABLE_POINTERS
            ) {
                continue;
            }
            for (&address, fixup) in image
                .fixups
                .range(section.addr..section.addr.saturating_add(section.size))
            {
                let Ok(resolution) = fixup.resolution() else {
                    continue;
                };
                let key = match &resolution {
                    Resolution::Import { symbol, .. } | Resolution::WeakLookup { symbol, .. } => {
                        SlotKey::Name(symbol.clone())
                    }
                    Resolution::Local { target } => SlotKey::Address(*target),
                };
                slots.entry(key).or_default().push(Slot {
                    address,
                    section_type,
                    resolution,
                });
            }
        }
        Self {
            image,
            objects,
            atom_address: objects
                .iter()
                .map(|object| vec![None; object.atoms.len()])
                .collect(),
            placed_by: objects
                .iter()
                .map(|object| vec![PlacedBy::NotInImage; object.atoms.len()])
                .collect(),
            symbol_atom: objects
                .iter()
                .map(|object| {
                    let mut map = BTreeMap::new();
                    for (atom_index, atom) in object.atoms.iter().enumerate() {
                        for &(symbol, offset) in &atom.anchors {
                            map.insert(symbol, (atom_index, offset));
                        }
                    }
                    map
                })
                .collect(),
            definitions: BTreeMap::new(),
            weak_refs: BTreeMap::new(),
            tlv_base,
            object_fixups: BTreeSet::new(),
            used_slots: BTreeSet::new(),
            slots,
            tlv_imports: BTreeSet::new(),
            other_imports: BTreeSet::new(),
            findings,
            rows: Vec::new(),
            consumed: 0,
            paired: 0,
            not_in_image: 0,
            by_kind: BTreeMap::new(),
        }
    }

    fn push(&mut self, code: &'static str, detail: impl Into<String>) {
        finding(&mut self.findings, code, detail);
    }

    fn site_label(&self, object: usize, section: usize, offset: u64) -> String {
        let object_ref = &self.objects[object];
        format!(
            "{} {}+{offset:#x}",
            object_ref.name,
            object_ref.sections[section].label()
        )
    }

    /// Constructs outside the modeled envelope, refused by name.
    fn check_supported(&mut self) {
        if self.image.flags & MH_TWOLEVEL == 0 {
            self.push(
                CODE_UNSUPPORTED,
                "the image uses the flat namespace (no MH_TWOLEVEL): dyld binds every reference \
                 by name in load order, which this replay does not model",
            );
        }
        let mut unsupported = Vec::new();
        for object in self.objects {
            for section in &object.sections {
                if section.is_consumed() {
                    continue;
                }
                let why = match section.section_type() {
                    S_CSTRING_LITERALS | S_4BYTE_LITERALS | S_8BYTE_LITERALS
                    | S_16BYTE_LITERALS | S_LITERAL_POINTERS => {
                        Some("a literal section, which ld64 deduplicates across objects")
                    }
                    S_NON_LAZY_SYMBOL_POINTERS
                    | S_LAZY_SYMBOL_POINTERS
                    | S_SYMBOL_STUBS
                    | S_MOD_INIT_FUNC_POINTERS
                    | S_MOD_TERM_FUNC_POINTERS
                    | S_INTERPOSING
                    | S_DTRACE_DOF
                    | S_LAZY_DYLIB_SYMBOL_POINTERS
                    | S_THREAD_LOCAL_VARIABLE_POINTERS
                    | S_THREAD_LOCAL_INIT_FUNCTION_POINTERS
                    | S_INIT_FUNC_OFFSETS => {
                        Some("a section type whose meaning depends on linker processing")
                    }
                    _ if section.name == "__eh_frame" => {
                        Some("__eh_frame, whose entries ld64 rewrites and prunes")
                    }
                    _ => None,
                };
                if let Some(why) = why {
                    unsupported.push(format!(
                        "object {} section {}: {why}",
                        object.name,
                        section.label()
                    ));
                }
                for reloc in &section.relocs {
                    if !reloc.external
                        && !matches!(reloc.kind, ARM64_RELOC_ADDEND | ARM64_RELOC_SUBTRACTOR)
                    {
                        unsupported.push(format!(
                            "object {} {}+{:#x}: a section-relative (r_extern = 0) {}",
                            object.name,
                            section.label(),
                            reloc.address,
                            arm64_reloc_name(reloc.kind)
                        ));
                    }
                }
            }
        }
        for detail in unsupported {
            self.push(CODE_UNSUPPORTED, detail);
        }
        for section in &self.image.sections {
            if section.size > 0
                && matches!(
                    section.section_type(),
                    S_MOD_INIT_FUNC_POINTERS
                        | S_MOD_TERM_FUNC_POINTERS
                        | S_INIT_FUNC_OFFSETS
                        | S_INTERPOSING
                        | S_THREAD_LOCAL_INIT_FUNCTION_POINTERS
                        | S_DTRACE_DOF
                )
            {
                self.push(
                    CODE_UNSUPPORTED,
                    format!(
                        "image section {} runs or redirects code at load time and no input \
                         object declares it",
                        section.label()
                    ),
                );
            }
        }
    }

    /// Establish each atom's image address.
    fn place(&mut self, placement: AtomPlacement<'_>) {
        match placement {
            AtomPlacement::SectionAddresses(addresses) => self.place_by_sections(addresses),
            AtomPlacement::ImageSymbolTable => self.place_by_symbol_table(),
        }
        self.check_overlaps();
    }

    fn place_by_sections(&mut self, addresses: &[Vec<Option<u64>>]) {
        if addresses.len() != self.objects.len() {
            self.push(
                CODE_PLACEMENT,
                format!(
                    "the linker's placement lists {} objects, the request {}",
                    addresses.len(),
                    self.objects.len()
                ),
            );
            return;
        }
        for (object_index, object) in self.objects.iter().enumerate() {
            let sections = &addresses[object_index];
            if sections.len() != object.sections.len() {
                self.push(
                    CODE_PLACEMENT,
                    format!(
                        "the linker's placement lists {} sections of {}, which has {}",
                        sections.len(),
                        object.name,
                        object.sections.len()
                    ),
                );
                continue;
            }
            for (atom_index, atom) in object.atoms.iter().enumerate() {
                match sections[atom.section] {
                    Some(base) => {
                        self.atom_address[object_index][atom_index] =
                            Some(base.wrapping_add(atom.start));
                        self.placed_by[object_index][atom_index] = PlacedBy::SectionAddress;
                    }
                    None => {
                        let section = &object.sections[atom.section];
                        if atom.end > atom.start {
                            self.push(
                                CODE_PLACEMENT,
                                format!(
                                    "the linker did not place {} {}",
                                    object.name,
                                    section.label()
                                ),
                            );
                        }
                    }
                }
            }
        }
    }

    fn place_by_symbol_table(&mut self) {
        // Image definitions by (name, external). ld64 turns a private
        // extern (`N_PEXT`) into a local symbol of the image.
        let mut by_name: BTreeMap<(&str, bool), Vec<u64>> = BTreeMap::new();
        for symbol in &self.image.symbols {
            if symbol.is_defined_in_section() && !symbol.name.is_empty() {
                by_name
                    .entry((symbol.name.as_str(), symbol.n_type & N_EXT != 0))
                    .or_default()
                    .push(symbol.n_value);
            }
        }
        if by_name.is_empty() {
            self.push(
                CODE_PLACEMENT,
                "the image has no defined symbols to place atoms by; supply the linker's section \
                 addresses",
            );
            return;
        }
        // How many object definitions share each name among the ones that
        // become local symbols of the image (locals and private externs).
        let mut local_definers: BTreeMap<&str, usize> = BTreeMap::new();
        for object in self.objects {
            for symbol in &object.symbols {
                if symbol.is_defined()
                    && !symbol.name.is_empty()
                    && (!symbol.is_external() || symbol.is_private_extern())
                {
                    *local_definers.entry(symbol.name.as_str()).or_default() += 1;
                }
            }
        }
        let winners = self.winning_definitions();
        let mut placements: Vec<(usize, usize, Option<u64>, PlacedBy)> = Vec::new();
        let mut problems = Vec::new();
        for (object_index, object) in self.objects.iter().enumerate() {
            for (atom_index, atom) in object.atoms.iter().enumerate() {
                let section = &object.sections[atom.section];
                let mut address: Option<u64> = None;
                let mut placed_by = PlacedBy::NotInImage;
                for &(symbol_index, offset) in &atom.anchors {
                    let symbol = &object.symbols[symbol_index];
                    let name = symbol.name.as_str();
                    let exported = symbol.is_external() && !symbol.is_private_extern();
                    if symbol.is_external()
                        && let Some(winner) = winners.get(name)
                        && (winner.object, winner.symbol) != (object_index, symbol_index)
                    {
                        // A weak copy another object's definition replaced.
                        placed_by = PlacedBy::Coalesced;
                        continue;
                    }
                    // An exported definition is external in the image unless
                    // the link hid it (an exported-symbols list makes it
                    // local); a local or hidden one is local unless the link
                    // kept private externs external.
                    let (values, local) = match (
                        by_name.get(&(name, exported)),
                        by_name.get(&(name, !exported)),
                    ) {
                        (Some(values), _) => (values, !exported),
                        (None, Some(values)) => (values, exported),
                        (None, None) => continue,
                    };
                    // Object definitions that could own a local image symbol.
                    let owners = if local {
                        local_definers.get(name).copied().unwrap_or(0) + usize::from(exported)
                    } else {
                        1
                    };
                    if values.len() != 1 || owners != 1 {
                        problems.push(format!(
                            "{} {}: the image names {name} {} times and {owners} object \
                             definitions could own it, so the symbol table does not locate it",
                            object.name,
                            section.label(),
                            values.len(),
                        ));
                        continue;
                    }
                    let candidate = values[0].wrapping_sub(offset);
                    match address {
                        None => {
                            address = Some(candidate);
                            placed_by = PlacedBy::SymbolTable;
                        }
                        Some(previous) if previous != candidate => problems.push(format!(
                            "{} {}: the image places the atom's symbols at {previous:#x} and \
                             {candidate:#x}",
                            object.name,
                            section.label()
                        )),
                        Some(_) => {}
                    }
                }
                if address.is_none()
                    && placed_by == PlacedBy::NotInImage
                    && atom.anchors.is_empty()
                    && atom.end > atom.start
                {
                    problems.push(format!(
                        "{} {}+{:#x}: {} bytes before the section's first symbol cannot be placed \
                         by the symbol table",
                        object.name,
                        section.label(),
                        atom.start,
                        atom.end - atom.start
                    ));
                }
                placements.push((object_index, atom_index, address, placed_by));
            }
        }
        for detail in problems {
            self.push(CODE_PLACEMENT, detail);
        }
        for (object_index, atom_index, address, placed_by) in placements {
            self.atom_address[object_index][atom_index] = address;
            self.placed_by[object_index][atom_index] = placed_by;
        }
    }

    /// Placed atoms must not overlap and must each lie in one image section.
    fn check_overlaps(&mut self) {
        let mut ranges: Vec<(u64, u64, String)> = Vec::new();
        let mut problems = Vec::new();
        for (object_index, object) in self.objects.iter().enumerate() {
            for (atom_index, atom) in object.atoms.iter().enumerate() {
                let Some(address) = self.atom_address[object_index][atom_index] else {
                    continue;
                };
                let size = atom.end - atom.start;
                let label = self.site_label(object_index, atom.section, atom.start);
                if size == 0 {
                    continue;
                }
                if self.image.section_at(address, size).is_none() {
                    problems.push(format!(
                        "{label} ({size} bytes) placed at {address:#x} does not lie in one image \
                         section"
                    ));
                }
                ranges.push((address, address.saturating_add(size), label));
            }
        }
        ranges.sort();
        for pair in ranges.windows(2) {
            if pair[1].0 < pair[0].1 {
                problems.push(format!(
                    "{} and {} overlap at {:#x}",
                    pair[0].2, pair[1].2, pair[1].0
                ));
            }
        }
        for detail in problems {
            self.push(CODE_PLACEMENT, detail);
        }
    }

    /// Strong over weak, the first weak in object order otherwise.
    fn winning_definitions(&self) -> BTreeMap<String, Definition> {
        let mut winners: BTreeMap<String, (Definition, bool)> = BTreeMap::new();
        for (object_index, object) in self.objects.iter().enumerate() {
            for (symbol_index, symbol) in object.symbols.iter().enumerate() {
                if !symbol.is_defined() || !symbol.is_external() || symbol.name.is_empty() {
                    continue;
                }
                let candidate = Definition {
                    object: object_index,
                    symbol: symbol_index,
                };
                let weak = symbol.is_weak_def();
                match winners.get(&symbol.name) {
                    None => {
                        winners.insert(symbol.name.clone(), (candidate, weak));
                    }
                    Some((_, true)) if !weak => {
                        winners.insert(symbol.name.clone(), (candidate, weak));
                    }
                    _ => {}
                }
            }
        }
        winners
            .into_iter()
            .map(|(name, (definition, _))| (name, definition))
            .collect()
    }

    fn resolve_definitions(&mut self) {
        self.definitions = self.winning_definitions();
        let mut strong: BTreeMap<&str, usize> = BTreeMap::new();
        let mut weak_refs: BTreeMap<String, bool> = BTreeMap::new();
        for object in self.objects {
            for symbol in &object.symbols {
                if symbol.name.is_empty() {
                    continue;
                }
                if symbol.is_defined() && symbol.is_external() && !symbol.is_weak_def() {
                    *strong.entry(symbol.name.as_str()).or_default() += 1;
                }
                if symbol.is_undefined() && symbol.is_external() {
                    let entry = weak_refs.entry(symbol.name.clone()).or_insert(true);
                    *entry &= symbol.is_weak_ref();
                }
            }
        }
        let duplicates: Vec<String> = strong
            .into_iter()
            .filter(|(_, count)| *count > 1)
            .map(|(name, count)| format!("{name} has {count} strong definitions"))
            .collect();
        for detail in duplicates {
            self.push(CODE_PLACEMENT, detail);
        }
        self.weak_refs = weak_refs;
    }

    fn symbol_address(&self, object: usize, symbol: usize) -> Option<u64> {
        let (atom, offset) = *self.symbol_atom[object].get(&symbol)?;
        self.atom_address[object][atom].map(|address| address.wrapping_add(offset))
    }

    /// The image symbol table must agree with every placed definition.
    fn check_placement_against_symbols(&mut self, placement: AtomPlacement<'_>) {
        if matches!(placement, AtomPlacement::ImageSymbolTable) {
            return;
        }
        let mut problems = Vec::new();
        let mut defined: BTreeMap<&str, Vec<(usize, usize)>> = BTreeMap::new();
        for (object_index, object) in self.objects.iter().enumerate() {
            for (symbol_index, symbol) in object.symbols.iter().enumerate() {
                if symbol.is_defined() && !symbol.name.is_empty() {
                    defined
                        .entry(symbol.name.as_str())
                        .or_default()
                        .push((object_index, symbol_index));
                }
            }
        }
        for symbol in &self.image.symbols {
            if !symbol.is_defined_in_section() || symbol.name.is_empty() {
                continue;
            }
            if let Some(&[(object, index)]) = defined.get(symbol.name.as_str()).map(Vec::as_slice)
                && let Some(address) = self.symbol_address(object, index)
                && address != symbol.n_value
            {
                problems.push(format!(
                    "the image symbol table places {} at {:#x}, the linker's placement at \
                     {address:#x}",
                    symbol.name, symbol.n_value
                ));
            }
        }
        for detail in problems {
            self.push(CODE_PLACEMENT, detail);
        }
    }

    /// Resolve the target of relocation `reloc` of `object`.
    fn target(&self, object: usize, reloc: &ObjReloc) -> Result<Target, String> {
        let objects = self.objects;
        let symbol = objects[object]
            .symbols
            .get(reloc.symbolnum as usize)
            .ok_or_else(|| {
                format!(
                    "names symbol {} of {}",
                    reloc.symbolnum,
                    objects[object].symbols.len()
                )
            })?;
        if symbol.name.is_empty() {
            return Err("names an unnamed symbol".into());
        }
        if symbol.is_defined() && !symbol.is_external() {
            return Ok(Target::Defined {
                name: symbol.name.clone(),
                object,
                symbol: reloc.symbolnum as usize,
                address: self.symbol_address(object, reloc.symbolnum as usize),
            });
        }
        if symbol.is_defined() || symbol.is_undefined() {
            if let Some(definition) = self.definitions.get(&symbol.name) {
                return Ok(Target::Defined {
                    name: symbol.name.clone(),
                    object: definition.object,
                    symbol: definition.symbol,
                    address: self.symbol_address(definition.object, definition.symbol),
                });
            }
            if symbol.is_undefined() {
                return Ok(Target::Import {
                    name: symbol.name.clone(),
                    weak_ref: self.weak_refs.get(&symbol.name).copied().unwrap_or(false),
                });
            }
        }
        Err(format!(
            "names {}, whose nlist type {:#x} is not modeled",
            symbol.name, symbol.n_type
        ))
    }

    fn definition_symbol(&self, object: usize, symbol: usize) -> &super::object::ObjSymbol {
        &self.objects[object].symbols[symbol]
    }

    fn definition_section(&self, object: usize, symbol: usize) -> Option<&ObjSection> {
        let symbol = self.definition_symbol(object, symbol);
        self.objects[object]
            .sections
            .get(usize::from(symbol.n_sect).checked_sub(1)?)
    }

    /// A weak, default-visibility definition the image exports for dyld's
    /// coalescing: every reference must go through dyld's weak lookup.
    fn coalescable(&self, target: &Target) -> bool {
        let Target::Defined {
            name,
            object,
            symbol,
            ..
        } = target
        else {
            return false;
        };
        let definition = self.definition_symbol(*object, *symbol);
        definition.is_weak_def()
            && definition.is_external()
            && !definition.is_private_extern()
            && self
                .image
                .exports
                .get(name)
                .is_some_and(|export| export.flags & EXPORT_SYMBOL_FLAGS_WEAK_DEFINITION != 0)
    }

    /// Whether the pointer resolution `resolution` is what `target` plus
    /// `addend` needs; `Ok` names the resolution.
    fn check_pointer(
        &self,
        resolution: &Resolution,
        target: &Target,
        addend: i64,
    ) -> Result<String, (&'static str, String)> {
        match (target, resolution) {
            (
                Target::Defined {
                    address: None,
                    name,
                    ..
                },
                _,
            ) => Err((
                CODE_DEAD_STRIP,
                format!("the image does not contain {name}"),
            )),
            (
                Target::Defined {
                    address: Some(address),
                    name,
                    ..
                },
                Resolution::Local { target: value },
            ) => {
                let expected = address.wrapping_add(addend as u64);
                if self.coalescable(target) {
                    Err((
                        CODE_WEAK_DIRECT,
                        format!(
                            "rebases to {value:#x}, statically, a reference to {name}, which the \
                             image exports for dyld's weak coalescing"
                        ),
                    ))
                } else if *value == expected {
                    Ok(format!("rebase to {expected:#x}"))
                } else {
                    Err((
                        CODE_POINTER,
                        format!("rebases to {value:#x}; {name}+{addend} is at {expected:#x}"),
                    ))
                }
            }
            (
                Target::Defined {
                    address: Some(address),
                    name,
                    ..
                },
                Resolution::WeakLookup {
                    symbol,
                    addend: bound_addend,
                    fallback,
                },
            ) => {
                let expected = address.wrapping_add(addend as u64);
                if symbol != name || *bound_addend != addend {
                    Err((
                        CODE_POINTER,
                        format!("weak-lookup binds {symbol}+{bound_addend}, not {name}+{addend}"),
                    ))
                } else if !self.coalescable(target) {
                    Err((
                        CODE_IMPORT_BINDING,
                        format!(
                            "binds {name} through dyld's weak lookup, but the image does not \
                             export it as a weak definition"
                        ),
                    ))
                } else if fallback.is_some_and(|fallback| fallback != expected) {
                    Err((
                        CODE_POINTER,
                        format!(
                            "the weak-lookup fallback is {:#x}; {name}+{addend} is at \
                             {expected:#x}",
                            fallback.unwrap_or(0)
                        ),
                    ))
                } else {
                    Ok(format!(
                        "dyld weak lookup of {name} (this image's definition at {expected:#x})"
                    ))
                }
            }
            (
                Target::Defined { name, .. },
                Resolution::Import {
                    symbol, ordinal, ..
                },
            ) => Err((
                CODE_IMPORT_BINDING,
                format!(
                    "binds {symbol} to library ordinal {ordinal}, but the objects define {name} \
                     in this image"
                ),
            )),
            (
                Target::Import { name, weak_ref },
                Resolution::Import {
                    ordinal,
                    symbol,
                    addend: bound_addend,
                    weak_import,
                    lazy,
                },
            ) => {
                if symbol != name || *bound_addend != addend {
                    Err((
                        CODE_POINTER,
                        format!("binds {symbol}+{bound_addend}, not {name}+{addend}"),
                    ))
                } else if weak_import != weak_ref {
                    Err((
                        CODE_IMPORT_BINDING,
                        format!(
                            "binds {name} with weak_import={weak_import}, the objects' \
                             reference is {}",
                            if *weak_ref { "weak" } else { "strong" }
                        ),
                    ))
                } else {
                    Ok(format!(
                        "{}bind {name} from ordinal {ordinal}",
                        if *lazy { "lazy " } else { "" }
                    ))
                }
            }
            (Target::Import { name, .. }, other) => Err((
                CODE_POINTER,
                format!("resolves the import {name} as {other:?}"),
            )),
        }
    }

    /// The unique slot of `family` whose fixup resolves correctly for
    /// `target`, or why there is none.
    fn slot(&self, family: SlotFamily, target: &Target) -> Result<u64, (&'static str, String)> {
        let code = match family {
            SlotFamily::Got => CODE_GOT,
            SlotFamily::Tlv => CODE_TLV,
        };
        // ld64 may keep a thread-local import's pointer in `__got`.
        let wanted = |section_type: u32| match family {
            SlotFamily::Got => section_type == S_NON_LAZY_SYMBOL_POINTERS,
            SlotFamily::Tlv => matches!(
                section_type,
                S_THREAD_LOCAL_VARIABLE_POINTERS | S_NON_LAZY_SYMBOL_POINTERS
            ),
        };
        let mut candidates: Vec<&Slot> = self
            .slots
            .get(&SlotKey::Name(target.name().to_string()))
            .into_iter()
            .flatten()
            .collect();
        if let Target::Defined {
            address: Some(address),
            ..
        } = target
        {
            candidates.extend(
                self.slots
                    .get(&SlotKey::Address(*address))
                    .into_iter()
                    .flatten(),
            );
        }
        let mut matching = Vec::new();
        let mut wrong = Vec::new();
        for slot in candidates {
            if !wanted(slot.section_type) {
                continue;
            }
            match self.check_pointer(&slot.resolution, target, 0) {
                Ok(_) => matching.push(slot.address),
                Err((_, detail)) => wrong.push(format!("{:#x} {detail}", slot.address)),
            }
        }
        matching.sort_unstable();
        matching.dedup();
        match (matching.as_slice(), wrong.first()) {
            ([slot], None) => Ok(*slot),
            ([], Some(detail)) => Err((code, format!("its slot {detail}"))),
            ([], None) => Err((
                code,
                format!(
                    "no {family:?} slot of the image resolves to {}",
                    target.name()
                ),
            )),
            _ => Err((
                code,
                format!(
                    "{} has {} {family:?} slots ({:x?}); the replay needs exactly one",
                    target.name(),
                    matching.len() + wrong.len(),
                    matching
                ),
            )),
        }
    }

    fn replay_relocations(&mut self) {
        // The form (slot or relaxed) of every GOT/TLV target, from its
        // PAGEOFF12 sites: `true` when ld64 relaxed the load to an ADD.
        let mut relaxed: BTreeMap<(SlotFamily, String), BTreeSet<bool>> = BTreeMap::new();
        for (object_index, object) in self.objects.iter().enumerate() {
            for (section_index, section) in object.sections.iter().enumerate() {
                for reloc in &section.relocs {
                    let family = match reloc.kind {
                        ARM64_RELOC_GOT_LOAD_PAGEOFF12 => SlotFamily::Got,
                        ARM64_RELOC_TLVP_LOAD_PAGEOFF12 => SlotFamily::Tlv,
                        _ => continue,
                    };
                    let Some(site) =
                        self.site_address(object_index, section_index, u64::from(reloc.address))
                    else {
                        continue;
                    };
                    let (Some(word), Ok(target)) = (
                        self.image.read_u32_at(site),
                        self.target(object_index, reloc),
                    ) else {
                        continue;
                    };
                    relaxed
                        .entry((family, target.name().to_string()))
                        .or_default()
                        .insert(word & 0xFFC0_0000 == 0x9100_0000);
                }
            }
        }
        let mut mixed = Vec::new();
        let forms: BTreeMap<(SlotFamily, String), bool> = relaxed
            .into_iter()
            .map(|(key, forms)| {
                if forms.len() > 1 {
                    mixed.push(format!(
                        "{} loads of {} are relaxed at some sites and not at others",
                        match key.0 {
                            SlotFamily::Got => "GOT",
                            SlotFamily::Tlv => "TLV",
                        },
                        key.1
                    ));
                }
                let relaxed = forms.contains(&true);
                (key, relaxed)
            })
            .collect();
        for detail in mixed {
            self.push(CODE_GOT, detail);
        }

        for object_index in 0..self.objects.len() {
            for section_index in 0..self.objects[object_index].sections.len() {
                let section = &self.objects[object_index].sections[section_index];
                if section.is_consumed() {
                    self.consumed += section.relocs.len();
                    continue;
                }
                let relocs = section.relocs.clone();
                let mut index = 0;
                while index < relocs.len() {
                    let current = &relocs[index];
                    let next = relocs
                        .get(index + 1)
                        .filter(|next| next.address == current.address);
                    let pairs = match current.kind {
                        ARM64_RELOC_ADDEND => next.is_some_and(|next| {
                            matches!(
                                next.kind,
                                ARM64_RELOC_BRANCH26 | ARM64_RELOC_PAGE21 | ARM64_RELOC_PAGEOFF12
                            )
                        }),
                        ARM64_RELOC_SUBTRACTOR => next.is_some_and(|next| {
                            next.kind == ARM64_RELOC_UNSIGNED && next.length == current.length
                        }),
                        _ => {
                            self.replay_one(object_index, section_index, current, 0, None, &forms);
                            index += 1;
                            continue;
                        }
                    };
                    let next = next.filter(|_| pairs);
                    if next.is_some() {
                        self.paired += 1;
                    }
                    match (current.kind, next) {
                        (ARM64_RELOC_ADDEND, Some(next)) => {
                            let addend = sign_extend(u64::from(current.symbolnum), 24);
                            self.replay_one(
                                object_index,
                                section_index,
                                next,
                                addend,
                                None,
                                &forms,
                            );
                        }
                        (ARM64_RELOC_SUBTRACTOR, Some(next)) => {
                            self.replay_one(
                                object_index,
                                section_index,
                                next,
                                0,
                                Some(current),
                                &forms,
                            );
                        }
                        (kind, _) => {
                            let label = self.site_label(
                                object_index,
                                section_index,
                                u64::from(current.address),
                            );
                            self.push(
                                CODE_UNSUPPORTED,
                                format!(
                                    "{label}: {} is not followed by the relocation it pairs with \
                                     at its address",
                                    arm64_reloc_name(kind)
                                ),
                            );
                            index += 1;
                            continue;
                        }
                    }
                    index += 2;
                }
            }
        }
    }

    /// Image address of section-relative `offset` of an object section,
    /// when the atom holding it is placed.
    fn site_address(&self, object: usize, section: usize, offset: u64) -> Option<u64> {
        let (atom, within) = self.objects[object].atom_of(section, offset)?;
        self.atom_address[object][atom].map(|address| address.wrapping_add(within))
    }

    fn replay_one(
        &mut self,
        object_index: usize,
        section_index: usize,
        reloc: &ObjReloc,
        addend: i64,
        subtrahend: Option<&ObjReloc>,
        forms: &BTreeMap<(SlotFamily, String), bool>,
    ) {
        let objects = self.objects;
        let object = &objects[object_index];
        let section = &object.sections[section_index];
        let offset = u64::from(reloc.address);
        let label = self.site_label(object_index, section_index, offset);
        let kind_name = arm64_reloc_name(reloc.kind);
        let Some(site) = self.site_address(object_index, section_index, offset) else {
            let (atom, _) = object
                .atom_of(section_index, offset)
                .unwrap_or((usize::MAX, 0));
            if atom != usize::MAX
                && matches!(
                    self.placed_by[object_index][atom],
                    PlacedBy::NotInImage | PlacedBy::Coalesced
                )
            {
                self.not_in_image += 1;
            } else {
                self.push(CODE_PLACEMENT, format!("{label}: the site is not placed"));
            }
            return;
        };
        let target = match self.target(object_index, reloc) {
            Ok(target) => target,
            Err(detail) => {
                self.push(CODE_UNSUPPORTED, format!("{label} {kind_name} {detail}"));
                return;
            }
        };
        *self
            .by_kind
            .entry(inventory_kind(reloc.kind).to_string())
            .or_default() += 1;
        if let Target::Import { name, .. } = &target {
            if matches!(
                reloc.kind,
                ARM64_RELOC_TLVP_LOAD_PAGE21 | ARM64_RELOC_TLVP_LOAD_PAGEOFF12
            ) {
                self.tlv_imports.insert(name.clone());
            } else {
                self.other_imports.insert(name.clone());
            }
        }
        let data_field = || -> Option<u64> {
            let width = 1usize << reloc.length;
            let start = offset as usize;
            let raw = section.data.get(start..start + width)?;
            Some(match width {
                8 => u64::from_le_bytes(raw.try_into().ok()?),
                4 => u64::from(u32::from_le_bytes(raw.try_into().ok()?)),
                _ => return None,
            })
        };
        let object_word = section
            .data
            .get(offset as usize..offset as usize + 4)
            .map(|raw| u32::from_le_bytes(raw.try_into().expect("four bytes")));
        let image_word = self.image.read_u32_at(site);

        let outcome: Result<(String, String), (&'static str, String)> = match reloc.kind {
            ARM64_RELOC_BRANCH26 => {
                self.replay_branch26(site, object_word, image_word, &target, addend)
            }
            ARM64_RELOC_PAGE21 => {
                self.replay_adrp(site, object_word, image_word, &target, addend, CODE_PAGE)
            }
            ARM64_RELOC_PAGEOFF12 => {
                self.replay_pageoff(object_word, image_word, &target, addend, CODE_PAGE)
            }
            ARM64_RELOC_GOT_LOAD_PAGE21 | ARM64_RELOC_TLVP_LOAD_PAGE21 => {
                let family = if reloc.kind == ARM64_RELOC_GOT_LOAD_PAGE21 {
                    SlotFamily::Got
                } else {
                    SlotFamily::Tlv
                };
                let relaxed = forms
                    .get(&(family, target.name().to_string()))
                    .copied()
                    .unwrap_or(false);
                self.replay_slot_page(site, object_word, image_word, &target, family, relaxed)
            }
            ARM64_RELOC_GOT_LOAD_PAGEOFF12 | ARM64_RELOC_TLVP_LOAD_PAGEOFF12 => {
                let family = if reloc.kind == ARM64_RELOC_GOT_LOAD_PAGEOFF12 {
                    SlotFamily::Got
                } else {
                    SlotFamily::Tlv
                };
                self.replay_slot_pageoff(object_word, image_word, &target, family)
            }
            ARM64_RELOC_UNSIGNED if subtrahend.is_some() => self.replay_difference(
                object_index,
                site,
                reloc,
                subtrahend.expect("paired"),
                &target,
                data_field(),
            ),
            ARM64_RELOC_UNSIGNED => self.replay_pointer(
                object_index,
                section_index,
                site,
                reloc,
                &target,
                data_field(),
            ),
            ARM64_RELOC_POINTER_TO_GOT if reloc.pcrel && reloc.length == 2 => {
                self.replay_pointer_to_got(site, &target)
            }
            other => Err((
                CODE_UNSUPPORTED,
                format!(
                    "{} (pcrel={}, length={}) is not a relocation this replay models",
                    arm64_reloc_name(other),
                    reloc.pcrel,
                    reloc.length
                ),
            )),
        };
        match outcome {
            Ok((expected, resolution)) => self.rows.push(RelocationRecord {
                object: object_index,
                section: section.label(),
                offset,
                kind: kind_name.to_string(),
                symbol: target.name().to_string(),
                addend,
                site: hex_address(site),
                target: expected,
                resolution,
            }),
            Err((code, detail)) => self.push(
                code,
                format!(
                    "{label} {kind_name} {}{} at {site:#x}: {detail}",
                    target.name(),
                    if addend != 0 {
                        format!("{addend:+}")
                    } else {
                        String::new()
                    }
                ),
            ),
        }
    }

    fn defined_address(
        &self,
        target: &Target,
        addend: i64,
        code: &'static str,
    ) -> Result<u64, (&'static str, String)> {
        match target {
            Target::Defined {
                address: Some(address),
                name,
                ..
            } => {
                if self.coalescable(target) {
                    Err((
                        CODE_WEAK_DIRECT,
                        format!(
                            "a direct reference to {name}, which the image exports for dyld's \
                             weak coalescing: dyld can bind other images to another definition \
                             while this site keeps this image's copy"
                        ),
                    ))
                } else {
                    Ok(address.wrapping_add(addend as u64))
                }
            }
            Target::Defined {
                address: None,
                name,
                ..
            } => Err((
                CODE_DEAD_STRIP,
                format!("the image does not contain {name}"),
            )),
            Target::Import { name, .. } => Err((
                code,
                format!("a direct reference to the import {name}, which no fixup can resolve"),
            )),
        }
    }

    fn replay_branch26(
        &mut self,
        site: u64,
        object_word: Option<u32>,
        image_word: Option<u32>,
        target: &Target,
        addend: i64,
    ) -> Result<(String, String), (&'static str, String)> {
        let (Some(object_word), Some(word)) = (object_word, image_word) else {
            return Err((CODE_BRANCH26, "the site has no instruction bytes".into()));
        };
        if object_word & 0x7C00_0000 != 0x1400_0000
            || word & 0xFC00_0000 != object_word & 0xFC00_0000
        {
            return Err((
                CODE_BRANCH26,
                format!(
                    "the image holds {word:#010x} where the object's B/BL is {object_word:#010x}"
                ),
            ));
        }
        let destination =
            site.wrapping_add(sign_extend(u64::from(word & 0x03FF_FFFF) << 2, 28) as u64);
        let in_stubs = self
            .image
            .section_at(destination, 4)
            .is_some_and(|section| section.section_type() == S_SYMBOL_STUBS);
        if in_stubs {
            if addend != 0 {
                return Err((
                    CODE_BRANCH26,
                    format!("branches through a stub with addend {addend}"),
                ));
            }
            let slot = self
                .image
                .stub_slot(destination)
                .map_err(|detail| (CODE_BRANCH26, detail))?;
            let resolution = match self.image.resolution_at(slot) {
                Some(Ok(resolution)) => resolution,
                Some(Err(detail)) => {
                    return Err((CODE_BRANCH26, format!("stub slot {slot:#x}: {detail}")));
                }
                None => {
                    return Err((
                        CODE_BRANCH26,
                        format!("the stub at {destination:#x} loads {slot:#x}, which has no fixup"),
                    ));
                }
            };
            let via = self
                .check_pointer(&resolution, target, 0)
                .map_err(|(code, detail)| {
                    let code = if code == CODE_POINTER {
                        CODE_BRANCH26
                    } else {
                        code
                    };
                    (
                        code,
                        format!("the stub at {destination:#x} loads {slot:#x}, which {detail}"),
                    )
                })?;
            self.used_slots.insert(slot);
            return Ok((
                target.name().to_string(),
                format!("stub {destination:#x} -> slot {slot:#x}: {via}"),
            ));
        }
        let expected = self.defined_address(target, addend, CODE_BRANCH26)?;
        if destination != expected {
            return Err((
                CODE_BRANCH26,
                format!("branches to {destination:#x}; the target is at {expected:#x}"),
            ));
        }
        Ok((hex_address(expected), "direct".into()))
    }

    fn replay_adrp(
        &self,
        site: u64,
        object_word: Option<u32>,
        image_word: Option<u32>,
        target: &Target,
        addend: i64,
        code: &'static str,
    ) -> Result<(String, String), (&'static str, String)> {
        let expected = self.defined_address(target, addend, code)?;
        self.check_adrp(site, object_word, image_word, expected, code)?;
        Ok((
            hex_address(expected),
            format!("page {:#x}", expected & !0xFFF),
        ))
    }

    fn check_adrp(
        &self,
        site: u64,
        object_word: Option<u32>,
        image_word: Option<u32>,
        expected: u64,
        code: &'static str,
    ) -> Result<(), (&'static str, String)> {
        let (Some(object_word), Some(word)) = (object_word, image_word) else {
            return Err((code, "the site has no instruction bytes".into()));
        };
        if object_word & 0x9F00_0000 != 0x9000_0000
            || word & 0x9F00_001F != object_word & 0x9F00_001F
        {
            return Err((
                code,
                format!(
                    "the image holds {word:#010x} where the object's ADRP is {object_word:#010x}"
                ),
            ));
        }
        let page = adrp_target(site, word);
        if page != expected & !0xFFF {
            return Err((
                code,
                format!(
                    "the ADRP materializes page {page:#x}; {expected:#x} is on page {:#x}",
                    expected & !0xFFF
                ),
            ));
        }
        Ok(())
    }

    fn replay_pageoff(
        &self,
        object_word: Option<u32>,
        image_word: Option<u32>,
        target: &Target,
        addend: i64,
        code: &'static str,
    ) -> Result<(String, String), (&'static str, String)> {
        let expected = self.defined_address(target, addend, code)?;
        let via = check_pageoff(object_word, image_word, expected, code)?;
        Ok((hex_address(expected), via))
    }

    fn replay_slot_page(
        &mut self,
        site: u64,
        object_word: Option<u32>,
        image_word: Option<u32>,
        target: &Target,
        family: SlotFamily,
        relaxed: bool,
    ) -> Result<(String, String), (&'static str, String)> {
        let code = match family {
            SlotFamily::Got => CODE_GOT,
            SlotFamily::Tlv => CODE_TLV,
        };
        if relaxed {
            let expected = self.relaxed_target(target, family)?;
            self.check_adrp(site, object_word, image_word, expected, code)?;
            return Ok((
                hex_address(expected),
                format!("relaxed: page {:#x} of the definition", expected & !0xFFF),
            ));
        }
        let slot = self.slot(family, target)?;
        self.check_adrp(site, object_word, image_word, slot, code)?;
        self.used_slots.insert(slot);
        Ok((
            hex_address(slot),
            format!("page {:#x} of slot {slot:#x}", slot & !0xFFF),
        ))
    }

    fn replay_slot_pageoff(
        &mut self,
        object_word: Option<u32>,
        image_word: Option<u32>,
        target: &Target,
        family: SlotFamily,
    ) -> Result<(String, String), (&'static str, String)> {
        let code = match family {
            SlotFamily::Got => CODE_GOT,
            SlotFamily::Tlv => CODE_TLV,
        };
        let (Some(object_word), Some(word)) = (object_word, image_word) else {
            return Err((code, "the site has no instruction bytes".into()));
        };
        if object_word & 0xFFC0_0000 != 0xF940_0000 {
            return Err((
                code,
                format!("the object's instruction {object_word:#010x} is not a 64-bit LDR"),
            ));
        }
        if word & 0xFFC0_0000 == 0x9100_0000 {
            // ld64 relaxed `LDR Xt, [Xn, #slot]` into `ADD Xt, Xn, #target`.
            let expected = self.relaxed_target(target, family)?;
            if word & 0x3FF != object_word & 0x3FF {
                return Err((
                    code,
                    format!(
                        "the relaxed ADD {word:#010x} changes the registers of the object's LDR \
                         {object_word:#010x}"
                    ),
                ));
            }
            if u64::from((word >> 10) & 0xFFF) != expected & 0xFFF {
                return Err((
                    code,
                    format!(
                        "the relaxed ADD adds {:#x}; {expected:#x} needs {:#x}",
                        (word >> 10) & 0xFFF,
                        expected & 0xFFF
                    ),
                ));
            }
            return Ok((
                hex_address(expected),
                format!(
                    "relaxed LDR -> ADD {:#x} of the definition",
                    expected & 0xFFF
                ),
            ));
        }
        let slot = self.slot(family, target)?;
        if word & IMM12_MASK != object_word & IMM12_MASK {
            return Err((
                code,
                format!(
                    "the image holds {word:#010x} where the object's LDR is {object_word:#010x}"
                ),
            ));
        }
        if u64::from((word >> 10) & 0xFFF) * 8 != slot & 0xFFF {
            return Err((
                code,
                format!(
                    "the LDR reads offset {:#x}; slot {slot:#x} is at {:#x}",
                    u64::from((word >> 10) & 0xFFF) * 8,
                    slot & 0xFFF
                ),
            ));
        }
        self.used_slots.insert(slot);
        Ok((hex_address(slot), format!("LDR slot {slot:#x}")))
    }

    /// The address a relaxed GOT/TLV load materializes.
    fn relaxed_target(
        &self,
        target: &Target,
        family: SlotFamily,
    ) -> Result<u64, (&'static str, String)> {
        let code = match family {
            SlotFamily::Got => CODE_GOT,
            SlotFamily::Tlv => CODE_TLV,
        };
        let expected = self.defined_address(target, 0, code)?;
        if family == SlotFamily::Tlv {
            let Target::Defined { object, symbol, .. } = target else {
                unreachable!("defined_address accepted only a definition");
            };
            if self
                .definition_section(*object, *symbol)
                .is_none_or(|section| section.section_type() != S_THREAD_LOCAL_VARIABLES)
            {
                return Err((
                    code,
                    format!(
                        "{} is not a thread-local variable descriptor",
                        target.name()
                    ),
                ));
            }
        }
        Ok(expected)
    }

    fn replay_pointer(
        &mut self,
        object_index: usize,
        section_index: usize,
        site: u64,
        reloc: &ObjReloc,
        target: &Target,
        field: Option<u64>,
    ) -> Result<(String, String), (&'static str, String)> {
        if reloc.pcrel || reloc.length != 3 {
            return Err((
                CODE_UNSUPPORTED,
                format!(
                    "an UNSIGNED of length {} (pcrel={}) has no slidable encoding",
                    1u32 << reloc.length,
                    reloc.pcrel
                ),
            ));
        }
        let addend =
            field.ok_or((CODE_POINTER, "the object field has no bytes".to_string()))? as i64;
        let section = &self.objects[object_index].sections[section_index];
        // A TLV descriptor's third word holds the template offset.
        if section.section_type() == S_THREAD_LOCAL_VARIABLES
            && let Some((_, within)) =
                self.objects[object_index].atom_of(section_index, u64::from(reloc.address))
            && within % 24 == 16
        {
            return self.replay_tlv_offset(site, target, addend);
        }
        self.object_fixups.insert(site);
        let resolution = match self.image.resolution_at(site) {
            Some(Ok(resolution)) => resolution,
            Some(Err(detail)) => return Err((CODE_POINTER, detail)),
            None => {
                return Err((
                    CODE_POINTER,
                    "the image has no fixup at the site, so dyld neither slides nor binds the \
                     pointer"
                        .into(),
                ));
            }
        };
        let via = self.check_pointer(&resolution, target, addend)?;
        Ok((format!("{}{addend:+}", target.name()), via))
    }

    fn replay_tlv_offset(
        &self,
        site: u64,
        target: &Target,
        addend: i64,
    ) -> Result<(String, String), (&'static str, String)> {
        let Target::Defined {
            object,
            symbol,
            address: Some(address),
            ..
        } = target
        else {
            return Err((
                CODE_TLV,
                format!(
                    "the descriptor's template {} is not in the image",
                    target.name()
                ),
            ));
        };
        if self
            .definition_section(*object, *symbol)
            .is_none_or(|section| {
                !matches!(
                    section.section_type(),
                    S_THREAD_LOCAL_REGULAR | S_THREAD_LOCAL_ZEROFILL
                )
            })
        {
            return Err((
                CODE_TLV,
                format!("{} is not a thread-local template", target.name()),
            ));
        }
        let base = self.tlv_base.ok_or((
            CODE_TLV,
            "the image has no thread-local template".to_string(),
        ))?;
        if self.image.fixups.contains_key(&site) {
            return Err((
                CODE_TLV,
                "the descriptor's template offset carries a fixup".into(),
            ));
        }
        let expected = address.wrapping_add(addend as u64).wrapping_sub(base);
        let value = self
            .image
            .read_u64_at(site)
            .ok_or((CODE_TLV, "the descriptor has no file bytes".to_string()))?;
        if value != expected {
            return Err((
                CODE_TLV,
                format!(
                    "the descriptor holds template offset {value:#x}; {} is at {expected:#x} \
                     from the template base {base:#x}",
                    target.name()
                ),
            ));
        }
        Ok((
            format!("template offset {expected:#x}"),
            "no fixup (offset from the thread-local template)".into(),
        ))
    }

    fn replay_difference(
        &self,
        object_index: usize,
        site: u64,
        reloc: &ObjReloc,
        subtrahend: &ObjReloc,
        minuend: &Target,
        field: Option<u64>,
    ) -> Result<(String, String), (&'static str, String)> {
        let subtracted = self
            .target(object_index, subtrahend)
            .map_err(|detail| (CODE_UNSUPPORTED, detail))?;
        let low = self.defined_address(&subtracted, 0, CODE_DIFFERENCE)?;
        let high = self.defined_address(minuend, 0, CODE_DIFFERENCE)?;
        let width = 1u32 << reloc.length;
        let raw = field.ok_or((CODE_DIFFERENCE, "the object field has no bytes".to_string()))?;
        let addend = if width == 4 {
            sign_extend(raw, 32)
        } else {
            raw as i64
        };
        if self.image.fixups.contains_key(&site) {
            return Err((CODE_DIFFERENCE, "the difference carries a fixup".into()));
        }
        let expected = high.wrapping_sub(low).wrapping_add(addend as u64);
        let value = match width {
            8 => self.image.read_u64_at(site),
            4 => self
                .image
                .read_u32_at(site)
                .map(|value| sign_extend(u64::from(value), 32) as u64),
            _ => None,
        }
        .ok_or((CODE_DIFFERENCE, "the site has no file bytes".to_string()))?;
        if width == 4 && sign_extend(expected, 32) as u64 != expected {
            return Err((
                CODE_DIFFERENCE,
                format!("{expected:#x} does not fit the 32-bit field"),
            ));
        }
        if value != expected {
            return Err((
                CODE_DIFFERENCE,
                format!(
                    "holds {value:#x}; {} - {} {addend:+} is {expected:#x}",
                    minuend.name(),
                    subtracted.name()
                ),
            ));
        }
        Ok((
            format!("{} - {}", minuend.name(), subtracted.name()),
            format!("difference {expected:#x}, no fixup"),
        ))
    }

    fn replay_pointer_to_got(
        &mut self,
        site: u64,
        target: &Target,
    ) -> Result<(String, String), (&'static str, String)> {
        let slot = self.slot(SlotFamily::Got, target)?;
        if self.image.fixups.contains_key(&site) {
            return Err((CODE_GOT, "the pc-relative GOT delta carries a fixup".into()));
        }
        let value = self
            .image
            .read_u32_at(site)
            .ok_or((CODE_GOT, "the site has no file bytes".to_string()))?;
        let expected = slot.wrapping_sub(site);
        if sign_extend(u64::from(value), 32) as u64 != expected {
            return Err((
                CODE_GOT,
                format!("holds delta {value:#x}; slot {slot:#x} is {expected:#x} away"),
            ));
        }
        self.used_slots.insert(slot);
        Ok((
            hex_address(slot),
            "pc-relative delta to the GOT slot".into(),
        ))
    }

    /// Relocation fields of each atom, section-relative `[start, end)`.
    fn check_content(&mut self) {
        let mut problems = Vec::new();
        for (object_index, object) in self.objects.iter().enumerate() {
            let masks = object.relocation_masks();
            for (atom_index, atom) in object.atoms.iter().enumerate() {
                let Some(address) = self.atom_address[object_index][atom_index] else {
                    continue;
                };
                let section = &object.sections[atom.section];
                let size = atom.end - atom.start;
                if size == 0 {
                    continue;
                }
                let label = self.site_label(object_index, atom.section, atom.start);
                if section.is_zero_fill() {
                    match self.image.read(address, size) {
                        None => {
                            let zero_fill = self
                                .image
                                .section_at(address, size)
                                .is_some_and(|image_section| image_section.is_zero_fill());
                            if !zero_fill {
                                problems.push(format!(
                                    "{label}: the zero-fill atom at {address:#x} is neither \
                                     file-backed nor in a zero-fill image section"
                                ));
                            }
                        }
                        Some(bytes) if bytes.iter().any(|&b| b != 0) => problems.push(format!(
                            "{label}: the image holds nonzero bytes where the object's zero-fill \
                             atom lies"
                        )),
                        Some(_) => {}
                    }
                    continue;
                }
                let mask = &masks[atom.section][atom.start as usize..atom.end as usize];
                let object_bytes = &section.data[atom.start as usize..atom.end as usize];
                let image_bytes = match self.image.read(address, size) {
                    Some(bytes) => bytes,
                    None => {
                        let zero_fill = self
                            .image
                            .section_at(address, size)
                            .is_some_and(|image_section| image_section.is_zero_fill());
                        if zero_fill
                            && object_bytes.iter().all(|&b| b == 0)
                            && !mask.iter().any(|&field| field)
                        {
                            continue;
                        }
                        problems.push(format!(
                            "{label}: {size} bytes at {address:#x} are not file-backed in the image"
                        ));
                        continue;
                    }
                };
                let mut mismatches = 0usize;
                let mut first = None;
                for (index, ((&expected, &found), &field)) in
                    object_bytes.iter().zip(image_bytes).zip(mask).enumerate()
                {
                    if !field && expected != found {
                        mismatches += 1;
                        first.get_or_insert((index as u64, expected, found));
                    }
                }
                if let Some((index, expected, found)) = first {
                    problems.push(format!(
                        "{label}: {mismatches} byte{} outside relocation fields differ; first at \
                         {:#x} (object {expected:#04x}, image {found:#04x})",
                        if mismatches == 1 { "" } else { "s" },
                        address + index
                    ));
                }
            }
        }
        for detail in problems {
            self.push(CODE_CONTENT, detail);
        }
    }

    /// Image content no input object accounts for: every byte of a
    /// file-backed image section the linker does not synthesize
    /// ([`Section::is_linker_synthesized`]) must lie in a placed object atom
    /// or be zero (alignment padding, ld64's `__dyld_private`). Code or data
    /// from a link input the request did not name (a `-Wl` object, an
    /// archive member) is refused here.
    fn check_unaccounted_content(&mut self) {
        let image = self.image;
        let mut covered: BTreeMap<usize, Vec<(u64, u64)>> = BTreeMap::new();
        for (object_index, object) in self.objects.iter().enumerate() {
            for (atom_index, atom) in object.atoms.iter().enumerate() {
                let Some(address) = self.atom_address[object_index][atom_index] else {
                    continue;
                };
                let size = atom.end - atom.start;
                if size == 0 {
                    continue;
                }
                if let Some(index) = image
                    .sections
                    .iter()
                    .position(|section| section.contains(address, size))
                {
                    covered
                        .entry(index)
                        .or_default()
                        .push((address, address + size));
                }
            }
        }
        let mut problems = Vec::new();
        for (index, section) in image.sections.iter().enumerate() {
            if section.size == 0 || section.is_zero_fill() || section.is_linker_synthesized() {
                continue;
            }
            let Some(bytes) = image.read(section.addr, section.size) else {
                problems.push(format!(
                    "image section {} ({} bytes at {:#x}) is neither zero-fill nor file-backed",
                    section.label(),
                    section.size,
                    section.addr
                ));
                continue;
            };
            let mut ranges = covered.remove(&index).unwrap_or_default();
            ranges.sort_unstable();
            let end = section.addr + section.size;
            let mut cursor = section.addr;
            let mut unaccounted: Vec<(u64, u64, u64, usize)> = Vec::new();
            for (start, stop) in ranges.into_iter().chain(std::iter::once((end, end))) {
                if start > cursor {
                    let gap =
                        &bytes[(cursor - section.addr) as usize..(start - section.addr) as usize];
                    if let Some(first) = gap.iter().position(|&b| b != 0) {
                        let nonzero = gap.iter().filter(|&&b| b != 0).count();
                        unaccounted.push((cursor, start, cursor + first as u64, nonzero));
                    }
                }
                cursor = cursor.max(stop);
            }
            let Some(&(start, stop, first, nonzero)) = unaccounted.first() else {
                continue;
            };
            let symbol = image
                .symbols
                .iter()
                .filter(|symbol| {
                    symbol.is_defined_in_section()
                        && symbol.n_value <= first
                        && section.contains(symbol.n_value, 1)
                })
                .max_by_key(|symbol| symbol.n_value)
                .map(|symbol| format!(" (image symbol {} at {:#x})", symbol.name, symbol.n_value))
                .unwrap_or_default();
            problems.push(format!(
                "image section {} holds nonzero bytes that no input object atom accounts for in \
                 {} range{}; the first, [{start:#x}, {stop:#x}), has {nonzero} nonzero byte{} \
                 from {first:#x}{symbol}: a link input the request does not name",
                section.label(),
                unaccounted.len(),
                if unaccounted.len() == 1 { "" } else { "s" },
                if nonzero == 1 { "" } else { "s" },
            ));
        }
        for detail in problems {
            self.push(CODE_UNACCOUNTED_CONTENT, detail);
        }
    }

    fn check_protection(&mut self) {
        let mut problems: Vec<(&'static str, String)> = Vec::new();
        for (object_index, object) in self.objects.iter().enumerate() {
            for (atom_index, atom) in object.atoms.iter().enumerate() {
                let Some(address) = self.atom_address[object_index][atom_index] else {
                    continue;
                };
                if atom.end == atom.start {
                    continue;
                }
                let section = &object.sections[atom.section];
                let label = self.site_label(object_index, atom.section, atom.start);
                let (Some(segment), Some(image_section)) = (
                    self.image.segment_at(address),
                    self.image.section_at(address, atom.end - atom.start),
                ) else {
                    continue;
                };
                let where_ = format!("{} in segment {}", image_section.label(), segment.name);
                if section.is_code() {
                    if segment.initprot & (VM_PROT_READ | VM_PROT_EXECUTE)
                        != VM_PROT_READ | VM_PROT_EXECUTE
                    {
                        problems.push((
                            CODE_PROTECTION,
                            format!("{label}: code placed in {where_}, which is not executable"),
                        ));
                    }
                } else if section.is_read_only_after_fixups() {
                    if segment.name != "__DATA_CONST"
                        || segment.flags & SG_READ_ONLY == 0
                        || segment.initprot & VM_PROT_EXECUTE != 0
                    {
                        problems.push((
                            CODE_CONST_WRITABLE,
                            format!(
                                "{label}: read-only-after-fixup data placed in {where_}; it must \
                                 lie in __DATA_CONST, which dyld makes read-only once its fixups \
                                 are applied (SG_READ_ONLY{})",
                                if segment.flags & SG_READ_ONLY == 0 {
                                    ", absent here: dyld leaves the segment writable"
                                } else {
                                    ""
                                }
                            ),
                        ));
                    }
                } else if section.segment != "__TEXT"
                    && (segment.initprot & VM_PROT_WRITE == 0 || segment.flags & SG_READ_ONLY != 0)
                {
                    problems.push((
                        CODE_PROTECTION,
                        format!("{label}: writable data placed in {where_}, which is not writable"),
                    ));
                }
                let tlv = |kind: u32| {
                    matches!(
                        kind,
                        S_THREAD_LOCAL_REGULAR | S_THREAD_LOCAL_ZEROFILL | S_THREAD_LOCAL_VARIABLES
                    )
                };
                let object_type = section.section_type();
                let image_type = image_section.section_type();
                if (tlv(object_type) || tlv(image_type))
                    && !(object_type == image_type
                        || (object_type == S_THREAD_LOCAL_ZEROFILL
                            && image_type == S_THREAD_LOCAL_REGULAR))
                {
                    problems.push((
                        CODE_PROTECTION,
                        format!(
                            "{label}: section type {object_type:#x} placed in {where_} of type \
                             {image_type:#x}; dyld finds thread-local templates and descriptors \
                             by section type"
                        ),
                    ));
                }
            }
        }
        for (code, detail) in problems {
            self.push(code, detail);
        }
    }

    /// Every fixup inside a placed atom must be at an object pointer site.
    fn check_fixup_accounting(&mut self) {
        let mut problems = Vec::new();
        let mut unwritable = Vec::new();
        // Placed atoms by address; they do not overlap (checked at placement).
        let mut placed: Vec<(u64, u64, usize, usize)> = Vec::new();
        for (object_index, object) in self.objects.iter().enumerate() {
            for (atom_index, atom) in object.atoms.iter().enumerate() {
                if let Some(address) = self.atom_address[object_index][atom_index]
                    && atom.end > atom.start
                {
                    placed.push((
                        address,
                        address.saturating_add(atom.end - atom.start),
                        object_index,
                        atom_index,
                    ));
                }
            }
        }
        placed.sort_unstable();
        for (&location, fixup) in &self.image.fixups {
            if self
                .image
                .segment_at(location)
                .is_none_or(|segment| segment.initprot & VM_PROT_WRITE == 0)
            {
                unwritable.push(format!(
                    "the image has a fixup at {location:#x}, in no segment dyld can write"
                ));
            }
            if self.object_fixups.contains(&location) {
                continue;
            }
            // The atoms whose bytes the 8-byte pointer at `location` touches.
            let first = placed.partition_point(|&(_, end, _, _)| end <= location);
            let owner = placed[first..]
                .iter()
                .take_while(|&&(start, _, _, _)| start < location.saturating_add(8))
                .map(|&(start, _, object_index, atom_index)| {
                    let atom = &self.objects[object_index].atoms[atom_index];
                    self.site_label(
                        object_index,
                        atom.section,
                        atom.start + location.saturating_sub(start),
                    )
                })
                .next();
            let section = self.image.section_at(location, 8);
            if let Some(owner) = owner {
                problems.push(format!(
                    "the image has a fixup at {location:#x} ({owner}) where the object has no \
                     pointer relocation: {fixup:?}"
                ));
            } else if !section.is_some_and(Section::is_linker_pointer_slots) {
                // Outside object content only the linker's own GOT, lazy and
                // TLV-pointer slots carry fixups; one elsewhere belongs to
                // content no input object accounts for.
                problems.push(format!(
                    "the image has a fixup at {location:#x} (in {}) outside every object atom \
                     and every linker pointer-slot section: {fixup:?}",
                    section.map_or_else(|| "no section".to_string(), Section::label)
                ));
            } else if let Err(detail) = fixup.resolution() {
                problems.push(format!("the fixup at {location:#x}: {detail}"));
            }
        }
        for detail in problems {
            self.push(CODE_UNEXPLAINED_FIXUP, detail);
        }
        for detail in unwritable {
            self.push(CODE_PROTECTION, detail);
        }
    }

    fn check_exports(&mut self) {
        let mut problems = Vec::new();
        let executable = self.image.filetype == MH_EXECUTE;
        let mut named: BTreeSet<&str> = BTreeSet::new();
        for (object_index, object) in self.objects.iter().enumerate() {
            for (symbol_index, symbol) in object.symbols.iter().enumerate() {
                if !symbol.is_defined() || symbol.name.is_empty() {
                    continue;
                }
                named.insert(symbol.name.as_str());
                let export = self.image.exports.get(&symbol.name);
                let exported_definition = symbol.is_external() && !symbol.is_private_extern();
                let winner = self
                    .definitions
                    .get(&symbol.name)
                    .is_some_and(|d| (d.object, d.symbol) == (object_index, symbol_index));
                match export {
                    // A hidden definition takes part in the winning-definition
                    // choice (it carries `N_EXT`), so its export is refused
                    // whether or not it won: a name any object hides is not
                    // one this replay lets the image publish.
                    Some(_) if symbol.is_external() && symbol.is_private_extern() => {
                        problems.push(format!(
                            "the image exports {}, which {} defines hidden (N_PEXT)",
                            symbol.name, object.name
                        ));
                    }
                    // A local's name may be exported only as another
                    // object's external definition of the same name.
                    Some(_) if !exported_definition => {
                        if !self.definitions.contains_key(&symbol.name) {
                            problems.push(format!(
                                "the image exports {}, which {} defines local",
                                symbol.name, object.name
                            ));
                        }
                    }
                    Some(export) if winner => {
                        let Some(address) = self.symbol_address(object_index, symbol_index) else {
                            problems.push(format!(
                                "the image exports {}, whose definition it does not contain",
                                symbol.name
                            ));
                            continue;
                        };
                        let section_type = object
                            .sections
                            .get(usize::from(symbol.n_sect).wrapping_sub(1))
                            .map(ObjSection::section_type);
                        let thread_local = section_type == Some(S_THREAD_LOCAL_VARIABLES);
                        let kind = export.flags & EXPORT_SYMBOL_FLAGS_KIND_MASK;
                        let exported_at = export
                            .offset
                            .map(|offset| self.image.base.wrapping_add(offset));
                        if export.reexport.is_some()
                            || export.flags & EXPORT_SYMBOL_FLAGS_STUB_AND_RESOLVER != 0
                            || kind == EXPORT_SYMBOL_FLAGS_KIND_ABSOLUTE
                        {
                            problems.push(format!(
                                "the image exports {} as a re-export, resolver or absolute symbol",
                                symbol.name
                            ));
                        } else if exported_at != Some(address) {
                            problems.push(format!(
                                "the image exports {} at {:#x}; its definition is at {address:#x}",
                                symbol.name,
                                exported_at.unwrap_or(0)
                            ));
                        } else if (kind == EXPORT_SYMBOL_FLAGS_KIND_THREAD_LOCAL) != thread_local {
                            problems.push(format!(
                                "the image exports {} with kind {kind}, the definition is {}a \
                                 thread-local descriptor",
                                symbol.name,
                                if thread_local { "" } else { "not " }
                            ));
                        } else if (export.flags & EXPORT_SYMBOL_FLAGS_WEAK_DEFINITION != 0)
                            != symbol.is_weak_def()
                        {
                            problems.push(format!(
                                "the image exports {} with weak={}, the definition is {}",
                                symbol.name,
                                export.flags & EXPORT_SYMBOL_FLAGS_WEAK_DEFINITION != 0,
                                if symbol.is_weak_def() {
                                    "weak"
                                } else {
                                    "strong"
                                }
                            ));
                        }
                    }
                    None if exported_definition && winner && !executable => {
                        problems.push(format!(
                            "the dylib does not export {}, a default-visibility definition",
                            symbol.name
                        ));
                    }
                    _ => {}
                }
            }
        }
        for (name, export) in &self.image.exports {
            if named.contains(name.as_str()) {
                continue;
            }
            let header = executable && name == "__mh_execute_header" && export.offset == Some(0);
            if !header {
                problems.push(format!(
                    "the image exports {name}, which no input object defines"
                ));
            }
        }
        for detail in problems {
            self.push(CODE_EXPORT, detail);
        }
    }

    fn check_header(&mut self) {
        let image = self.image;
        let mut problems: Vec<(&'static str, String)> = Vec::new();
        if image.filetype == MH_EXECUTE {
            if image.flags & MH_PIE == 0 {
                problems.push((CODE_HEADER, "the executable is not MH_PIE".into()));
            }
            if image.dylinker.as_deref() != Some("/usr/lib/dyld") {
                problems.push((
                    CODE_HEADER,
                    format!("the executable's dynamic linker is {:?}", image.dylinker),
                ));
            }
            match (image.entry_offset, self.definitions.get("_main").copied()) {
                (Some(entry), Some(main)) => {
                    let entry = image.base.wrapping_add(entry);
                    match self.symbol_address(main.object, main.symbol) {
                        Some(address) if address == entry => {}
                        other => problems.push((
                            CODE_ENTRY,
                            format!(
                                "LC_MAIN enters at {entry:#x}; the objects' _main is at {other:x?}"
                            ),
                        )),
                    }
                }
                (entry, main) => problems.push((
                    CODE_ENTRY,
                    format!(
                        "LC_MAIN {entry:x?} and an object _main ({}) are both required",
                        main.is_some()
                    ),
                )),
            }
        } else {
            if image.install_name.is_none() {
                problems.push((CODE_HEADER, "the dylib has no LC_ID_DYLIB".into()));
            }
            if image.entry_offset.is_some() {
                problems.push((CODE_HEADER, "the dylib has an LC_MAIN".into()));
            }
        }
        let weak_lookups = image
            .fixups
            .values()
            .any(|fixup| matches!(fixup.resolution(), Ok(Resolution::WeakLookup { .. })));
        if weak_lookups && image.flags & MH_BINDS_TO_WEAK == 0 {
            problems.push((
                CODE_HEADER,
                "the image binds through dyld's weak lookup without MH_BINDS_TO_WEAK".into(),
            ));
        }
        let weak_exports = image
            .exports
            .values()
            .any(|export| export.flags & EXPORT_SYMBOL_FLAGS_WEAK_DEFINITION != 0);
        if weak_exports && image.flags & MH_WEAK_DEFINES == 0 {
            problems.push((
                CODE_HEADER,
                "the image exports weak definitions without MH_WEAK_DEFINES, so dyld does not \
                 coalesce them"
                    .into(),
            ));
        }
        let descriptors = image
            .sections
            .iter()
            .any(|section| section.section_type() == S_THREAD_LOCAL_VARIABLES && section.size > 0);
        if descriptors && image.flags & MH_HAS_TLV_DESCRIPTORS == 0 {
            problems.push((
                CODE_HEADER,
                "the image has TLV descriptors without MH_HAS_TLV_DESCRIPTORS, so dyld does not \
                 initialize them"
                    .into(),
            ));
        }
        // Retention: a `N_NO_DEAD_STRIP` definition or `S_ATTR_NO_DEAD_STRIP`
        // section must be in the image.
        for (object_index, object) in self.objects.iter().enumerate() {
            for (atom_index, atom) in object.atoms.iter().enumerate() {
                if self.placed_by[object_index][atom_index] != PlacedBy::NotInImage {
                    continue;
                }
                let section = &object.sections[atom.section];
                let retained = section.flags & S_ATTR_NO_DEAD_STRIP != 0
                    || atom
                        .anchors
                        .iter()
                        .any(|&(symbol, _)| object.symbols[symbol].n_desc & N_NO_DEAD_STRIP != 0);
                if retained {
                    problems.push((
                        CODE_DEAD_STRIP,
                        format!(
                            "{}: a retained (no-dead-strip) atom is not in the image",
                            self.site_label(object_index, atom.section, atom.start)
                        ),
                    ));
                }
            }
        }
        for (code, detail) in problems {
            self.push(code, detail);
        }
    }

    /// Check every bind against the supplied export lists.
    fn check_binds(&mut self, providers: &[ProviderExports]) -> Vec<ImportRecord> {
        let image = self.image;
        let mut problems: Vec<(&'static str, String)> = Vec::new();
        let mut imports: BTreeMap<(String, i32, bool), usize> = BTreeMap::new();
        let mut ordinals: BTreeMap<String, BTreeSet<i32>> = BTreeMap::new();
        for fixup in image.fixups.values() {
            if let Ok(Resolution::Import {
                ordinal,
                symbol,
                weak_import,
                ..
            }) = fixup.resolution()
            {
                *imports
                    .entry((symbol.clone(), ordinal, weak_import))
                    .or_default() += 1;
                ordinals.entry(symbol).or_default().insert(ordinal);
            }
        }
        for (symbol, set) in &ordinals {
            if set.len() > 1 {
                problems.push((
                    CODE_IMPORT_BINDING,
                    format!("{symbol} is bound through library ordinals {set:?}"),
                ));
            }
        }
        // A dependent dylib no bind names is loaded, and its initializers
        // run, with no object reference to justify it. libSystem, which the
        // C driver and the standalone linker link into every image and dyld
        // requires of an executable, is the one exception.
        let bound: BTreeSet<i32> = ordinals.values().flatten().copied().collect();
        for (index, dylib) in image.dylibs.iter().enumerate() {
            let ordinal = i32::try_from(index + 1).unwrap_or(i32::MAX);
            if !bound.contains(&ordinal) && dylib.install_name != LIBSYSTEM_INSTALL_NAME {
                problems.push((
                    CODE_UNUSED_DYLIB,
                    format!(
                        "the image loads {} ({}, ordinal {ordinal}), which no bind uses: dyld \
                         loads it and runs its initializers with no object reference to it",
                        dylib.install_name, dylib.command
                    ),
                ));
            }
        }
        let mut records = Vec::new();
        for ((symbol, ordinal, weak_import), locations) in imports {
            let dylib = usize::try_from(ordinal)
                .ok()
                .and_then(|ordinal| ordinal.checked_sub(1))
                .and_then(|index| image.dylibs.get(index));
            let Some(dylib) = dylib else {
                problems.push((
                    CODE_IMPORT_BINDING,
                    format!(
                        "{symbol} is bound to library ordinal {ordinal}, which names none of the \
                         image's {} dylibs",
                        image.dylibs.len()
                    ),
                ));
                continue;
            };
            if self.definitions.contains_key(&symbol) {
                problems.push((
                    CODE_IMPORT_BINDING,
                    format!(
                        "{symbol} is bound to {} although the objects define it in this image",
                        dylib.install_name
                    ),
                ));
            }
            if let Some(&weak_ref) = self.weak_refs.get(&symbol)
                && weak_ref != weak_import
            {
                problems.push((
                    CODE_IMPORT_BINDING,
                    format!(
                        "{symbol} is bound with weak_import={weak_import}; the objects' \
                         reference is {}",
                        if weak_ref { "weak" } else { "strong" }
                    ),
                ));
            }
            let provider = providers
                .iter()
                .find(|provider| provider.install_name == dylib.install_name);
            let provider_note = match provider {
                None => {
                    problems.push((
                        CODE_IMPORT_PROVIDER,
                        format!(
                            "{symbol} is bound to ordinal {ordinal} ({}), whose export list was \
                             not supplied",
                            dylib.install_name
                        ),
                    ));
                    continue;
                }
                Some(provider) if !provider.symbols.contains(&symbol) => {
                    let exporters: Vec<&str> = providers
                        .iter()
                        .filter(|other| other.symbols.contains(&symbol))
                        .map(|other| other.install_name.as_str())
                        .collect();
                    problems.push((
                        CODE_IMPORT_BINDING,
                        format!(
                            "{symbol} is bound to ordinal {ordinal} ({}), which does not export \
                             it (exported by {exporters:?})",
                            dylib.install_name
                        ),
                    ));
                    continue;
                }
                Some(provider) => {
                    if let Some(thread_locals) = &provider.thread_local_symbols {
                        let thread_local = thread_locals.contains(&symbol);
                        if self.tlv_imports.contains(&symbol) && !thread_local {
                            problems.push((
                                CODE_TLV,
                                format!(
                                    "{symbol} is reached through TLV loads, but {} exports it as \
                                     a regular symbol",
                                    dylib.install_name
                                ),
                            ));
                        }
                        if self.other_imports.contains(&symbol) && thread_local {
                            problems.push((
                                CODE_TLV,
                                format!(
                                    "{symbol} is a thread-local variable of {}, but is reached \
                                     by relocations that are not TLV loads",
                                    dylib.install_name
                                ),
                            ));
                        }
                    }
                    provider.source.clone()
                }
            };
            records.push(ImportRecord {
                symbol,
                ordinal,
                library: dylib.install_name.clone(),
                weak_import,
                provider: provider_note,
                locations,
            });
        }
        for (code, detail) in problems {
            self.push(code, detail);
        }
        records
    }

    fn record(
        self,
        request: &LinkedImageRequest<'_>,
        signature: crate::macho::codesign::AdHocSignature,
        imports: Vec<ImportRecord>,
    ) -> LinkedImageRecord {
        let image = self.image;
        let flag_names = [
            (0x1, "MH_NOUNDEFS"),
            (0x4, "MH_DYLDLINK"),
            (MH_TWOLEVEL, "MH_TWOLEVEL"),
            (MH_WEAK_DEFINES, "MH_WEAK_DEFINES"),
            (MH_BINDS_TO_WEAK, "MH_BINDS_TO_WEAK"),
            (MH_PIE, "MH_PIE"),
            (0x10_0000, "MH_NO_REEXPORTED_DYLIBS"),
            (MH_HAS_TLV_DESCRIPTORS, "MH_HAS_TLV_DESCRIPTORS"),
        ];
        let mut flags: Vec<String> = flag_names
            .iter()
            .filter(|(bit, _)| image.flags & bit != 0)
            .map(|(_, name)| name.to_string())
            .collect();
        let known: u32 = flag_names.iter().map(|(bit, _)| bit).sum();
        if image.flags & !known != 0 {
            flags.push(format!("{:#x}", image.flags & !known));
        }
        let cdhash = code_directory_hash(request.image, &signature).unwrap_or_default();
        let identity = ImageIdentity {
            name: request.image_name.to_string(),
            size: request.image.len() as u64,
            sha256: hex(&Sha256::digest(request.image)),
            filetype: if image.filetype == MH_EXECUTE {
                "MH_EXECUTE".into()
            } else {
                "MH_DYLIB".into()
            },
            flags: flags.join("|"),
            uuid: image.uuid.map(|uuid| hex(&uuid)),
            install_name: image.install_name.clone(),
            entry: image
                .entry_offset
                .map(|offset| hex_address(image.base.wrapping_add(offset))),
            dylinker: image.dylinker.clone(),
            rpaths: image.rpaths.clone(),
            load_commands: image.load_commands.clone(),
            code_signature: CodeSignatureRecord {
                identifier: signature.code_directory.identifier.clone(),
                cdhash,
                code_limit: signature.code_directory.code_limit,
                page_size: signature.code_directory.page_size,
                linker_signed: signature.code_directory.is_linker_signed(),
            },
        };
        let linker = LinkerRecord {
            declared: request.linker.clone(),
            image_tools: image
                .build
                .as_ref()
                .map(|build| {
                    build
                        .tools
                        .iter()
                        .map(|(tool, version)| {
                            format!("{} {}", build_tool_name(*tool), version_string(*version))
                        })
                        .collect()
                })
                .unwrap_or_default(),
            build_version: image.build.as_ref().map(|build| {
                format!(
                    "platform {} minos {} sdk {}",
                    build.platform,
                    version_string(build.minos),
                    version_string(build.sdk)
                )
            }),
        };
        let objects: Vec<ObjectRecord> = self
            .objects
            .iter()
            .enumerate()
            .map(|(index, object)| {
                let mut digest = Sha256::new();
                let mut inventory: BTreeMap<String, usize> = BTreeMap::new();
                let mut count = 0;
                for section in &object.sections {
                    for reloc in &section.relocs {
                        count += 1;
                        *inventory
                            .entry(inventory_kind(reloc.kind).to_string())
                            .or_default() += 1;
                        let symbol = if reloc.external {
                            object
                                .symbols
                                .get(reloc.symbolnum as usize)
                                .map(|symbol| symbol.name.clone())
                                .unwrap_or_default()
                        } else {
                            format!("section {}", reloc.symbolnum)
                        };
                        digest.update(
                            format!(
                                "{}|{:#x}|{}|{}|{}|{}|{symbol}\n",
                                section.label(),
                                reloc.address,
                                arm64_reloc_name(reloc.kind),
                                reloc.pcrel,
                                reloc.length,
                                reloc.external
                            )
                            .as_bytes(),
                        );
                    }
                }
                ObjectRecord {
                    index,
                    build_version: object.build.map(|(platform, minos, sdk)| {
                        format!(
                            "platform {platform} minos {} sdk {}",
                            version_string(minos),
                            version_string(sdk)
                        )
                    }),
                    name: object.name.clone(),
                    size: object.size as u64,
                    sha256: hex(&object.sha256),
                    relocations: count,
                    inventory_digest: hex(&digest.finalize()),
                    inventory,
                }
            })
            .collect();
        let segments = image
            .segments
            .iter()
            .map(|segment| SegmentRecord {
                name: segment.name.clone(),
                vmaddr: hex_address(segment.vmaddr),
                vmsize: hex_address(segment.vmsize),
                fileoff: segment.fileoff,
                filesize: segment.filesize,
                maxprot: protection(segment.maxprot),
                initprot: protection(segment.initprot),
                read_only_after_fixups: segment.flags & SG_READ_ONLY != 0,
            })
            .collect();
        let dylibs = image
            .dylibs
            .iter()
            .enumerate()
            .map(|(index, dylib)| DylibRecord {
                ordinal: index + 1,
                command: format!(
                    "{} (current {}, compatibility {})",
                    dylib.command,
                    version_string(dylib.current_version),
                    version_string(dylib.compatibility_version)
                ),
                install_name: dylib.install_name.clone(),
                provider: request
                    .providers
                    .iter()
                    .find(|provider| provider.install_name == dylib.install_name)
                    .map(|provider| provider.source.clone()),
            })
            .collect();
        let mut fixup_digest = Sha256::new();
        let (mut rebases, mut binds, mut lazy, mut weak) = (0, 0, 0, 0);
        let mut linker_fixups = Vec::new();
        for (location, fixup) in &image.fixups {
            let resolution = fixup.resolution().expect("accounted fixups resolve");
            match &resolution {
                Resolution::Local { .. } => rebases += 1,
                Resolution::Import { lazy: true, .. } => lazy += 1,
                Resolution::Import { .. } => binds += 1,
                Resolution::WeakLookup { .. } => weak += 1,
            }
            fixup_digest.update(format!("{location:#x} {resolution:?}\n").as_bytes());
            if !self.object_fixups.contains(location) {
                linker_fixups.push(LinkerFixupRecord {
                    address: hex_address(*location),
                    section: image
                        .section_at(*location, 8)
                        .map(|section| section.label())
                        .unwrap_or_default(),
                    resolution: describe(&resolution),
                    used_by_replay: self.used_slots.contains(location),
                });
            }
        }
        let fixups = FixupsRecord {
            format: image.fixup_format.label().to_string(),
            locations: image.fixups.len(),
            rebases,
            binds,
            lazy_binds: lazy,
            weak_lookups: weak,
            digest: hex(&fixup_digest.finalize()),
        };
        let mut exports = Vec::new();
        for (name, export) in &image.exports {
            let object = self
                .definitions
                .get(name)
                .map(|definition| definition.object);
            exports.push(ExportRecord {
                symbol: name.clone(),
                address: export
                    .offset
                    .map(|offset| hex_address(image.base.wrapping_add(offset)))
                    .unwrap_or_default(),
                kind: match export.flags & EXPORT_SYMBOL_FLAGS_KIND_MASK {
                    EXPORT_SYMBOL_FLAGS_KIND_THREAD_LOCAL => "thread-local".into(),
                    EXPORT_SYMBOL_FLAGS_KIND_ABSOLUTE => "absolute".into(),
                    _ => "regular".into(),
                },
                weak: export.flags & EXPORT_SYMBOL_FLAGS_WEAK_DEFINITION != 0,
                object,
            });
        }
        let mut atoms = Vec::new();
        let (mut placed, mut missing, mut const_atoms) = (0, 0, 0);
        for (object_index, object) in self.objects.iter().enumerate() {
            for (atom_index, atom) in object.atoms.iter().enumerate() {
                let section = &object.sections[atom.section];
                let address = self.atom_address[object_index][atom_index];
                let size = atom.end - atom.start;
                if address.is_some() {
                    placed += 1;
                    if section.is_read_only_after_fixups() && size > 0 {
                        const_atoms += 1;
                    }
                } else {
                    missing += 1;
                }
                atoms.push(AtomRecord {
                    object: object_index,
                    section: section.label(),
                    symbol: atom
                        .anchors
                        .first()
                        .map(|&(symbol, _)| object.symbols[symbol].name.clone())
                        .unwrap_or_default(),
                    offset: atom.start,
                    size,
                    address: address.map(hex_address),
                    image_section: address.and_then(|address| {
                        image
                            .section_at(address, size.max(1))
                            .map(|section| section.label())
                    }),
                    placement: match self.placed_by[object_index][atom_index] {
                        PlacedBy::SymbolTable => "image symbol table",
                        PlacedBy::SectionAddress => "linker section address (content-checked)",
                        PlacedBy::NotInImage => "not in the image",
                        PlacedBy::Coalesced => "coalesced into another object's definition",
                    }
                    .to_string(),
                });
            }
        }
        let summary = ReplaySummary {
            relocations_replayed: self.rows.len(),
            relocations_paired: self.paired,
            relocations_by_kind: self.by_kind,
            relocations_consumed: self.consumed,
            relocations_not_in_image: self.not_in_image,
            atoms_placed: placed,
            atoms_not_in_image: missing,
            object_fixups: self.object_fixups.len(),
            linker_fixups: linker_fixups.len(),
            read_only_after_fixup_atoms: const_atoms,
        };
        LinkedImageRecord {
            schema: LINKED_IMAGE_RECORD_SCHEMA.to_string(),
            evidence: "independent replay of object relocations against the linked image \
                       (redundancy evidence on this image's bytes; not a proof)"
                .to_string(),
            image: identity,
            linker,
            objects,
            placement: match request.placement {
                AtomPlacement::ImageSymbolTable => "image symbol table".into(),
                AtomPlacement::SectionAddresses(_) => {
                    "linker section addresses, checked against content, exports and entry".into()
                }
            },
            segments,
            dylibs,
            fixups,
            imports,
            exports,
            atoms,
            relocations: self.rows,
            linker_fixups,
            summary,
            boundary: BOUNDARY.iter().map(|line| line.to_string()).collect(),
        }
    }
}

fn check_pageoff(
    object_word: Option<u32>,
    image_word: Option<u32>,
    expected: u64,
    code: &'static str,
) -> Result<String, (&'static str, String)> {
    let (Some(object_word), Some(word)) = (object_word, image_word) else {
        return Err((code, "the site has no instruction bytes".into()));
    };
    let scale = pageoff_form(object_word).ok_or_else(|| {
        (
            code,
            format!("the object's instruction {object_word:#010x} is not an ADD or unsigned-offset load/store"),
        )
    })?;
    if word & IMM12_MASK != object_word & IMM12_MASK {
        return Err((
            code,
            format!(
                "the image holds {word:#010x} where the object's instruction is {object_word:#010x}"
            ),
        ));
    }
    let low = expected & 0xFFF;
    if low & ((1 << scale) - 1) != 0 {
        return Err((
            code,
            format!(
                "{expected:#x} is not aligned to the access size {}",
                1u32 << scale
            ),
        ));
    }
    let encoded = u64::from((word >> 10) & 0xFFF) << scale;
    if encoded != low {
        return Err((
            code,
            format!(
                "the instruction encodes page offset {encoded:#x}; {expected:#x} needs {low:#x}"
            ),
        ));
    }
    Ok(format!(
        "page offset {low:#x} (access size {})",
        1u32 << scale
    ))
}

fn protection(prot: u32) -> String {
    format!(
        "{}{}{}",
        if prot & VM_PROT_READ != 0 { "r" } else { "-" },
        if prot & VM_PROT_WRITE != 0 { "w" } else { "-" },
        if prot & VM_PROT_EXECUTE != 0 {
            "x"
        } else {
            "-"
        }
    )
}

fn describe(resolution: &Resolution) -> String {
    match resolution {
        Resolution::Local { target } => format!("rebase {target:#x}"),
        Resolution::Import {
            ordinal,
            symbol,
            addend,
            weak_import,
            lazy,
        } => format!(
            "{}bind {symbol}{} ordinal {ordinal}{}",
            if *lazy { "lazy " } else { "" },
            if *addend != 0 {
                format!("{addend:+}")
            } else {
                String::new()
            },
            if *weak_import { " weak-import" } else { "" }
        ),
        Resolution::WeakLookup { symbol, addend, .. } => format!(
            "weak lookup {symbol}{}",
            if *addend != 0 {
                format!("{addend:+}")
            } else {
                String::new()
            }
        ),
    }
}

/// SHA-256 of the CodeDirectory blob in slot 0, truncated to 20 bytes.
fn code_directory_hash(
    image: &[u8],
    signature: &crate::macho::codesign::AdHocSignature,
) -> Option<String> {
    let start = usize::try_from(signature.signature_offset).ok()?;
    let blob = image.get(start..start.checked_add(signature.signature_size as usize)?)?;
    let be32 = |at: usize| -> Option<u32> {
        Some(u32::from_be_bytes(blob.get(at..at + 4)?.try_into().ok()?))
    };
    let count = be32(8)? as usize;
    for index in 0..count {
        let entry = 12 + index * 8;
        if be32(entry)? == 0 {
            let offset = be32(entry + 4)? as usize;
            let length = be32(offset + 4)? as usize;
            let directory = blob.get(offset..offset.checked_add(length)?)?;
            return Some(hex(&Sha256::digest(directory)[..20]));
        }
    }
    None
}

/// What the record does not bind (written into every record).
const BOUNDARY: &[&str] = &[
    "dyld's run-time choices beyond the fixup semantics decoded here: load order, which image a \
     weak-definition lookup or an interposition selects, and whether the dylibs named by ordinal \
     load at all (a dependent dylib no bind uses is refused, libSystem excepted)",
    "the exports of a dylib are bound only through the export list supplied for it (an image's \
     exports trie, a TAPI stub, or a declared list); what the dylib loaded at run time exports is \
     not observed",
    "image content outside the object atoms is accepted only in linker-synthesized sections \
     (__stubs, __stub_helper, __unwind_info, GOT, lazy and TLV pointer slots) or as zero bytes \
     (alignment padding, ld64's __dyld_private, zero-fill), and fixups outside the atoms only in \
     the pointer slots; the linker's own code (stub helpers) is not replayed: a branch from object \
     code into it is refused, the entry point and every export must name an object definition, \
     and __stubs entries and GOT/TLV slots are decoded only where a replayed relocation reaches \
     them (the other slots' fixups are listed); all-zero or zero-fill content of a link input the \
     request does not name is not attributed",
    "__unwind_info, __eh_frame and relocations in sections the linker consumes \
     (__LD,__compact_unwind, S_ATTR_DEBUG) are counted, not replayed",
    "the code signature is verified for byte consistency; signing policy (hardened runtime, \
     library validation, entitlements) is not decided",
    "the object bytes themselves are bound by the per-compile reparse gate and relocation \
     inventory, not by this record",
];
