// Copyright 2026 Andrew Yates | Apache-2.0
//! Narrow same-object/local-atom byte custody. No source, call-effect or
//! no-normal-return authority is conferred by placement alone.
use super::{
    abi::*,
    image::{Image, Resolution},
    object::{Atom, Object},
};

#[derive(Debug)]
pub struct CheckedClosedCallSite {
    offset: usize,
    symbol: String,
    destination: u64,
}
impl CheckedClosedCallSite {
    pub fn offset(&self) -> usize {
        self.offset
    }
    pub fn symbol(&self) -> &str {
        &self.symbol
    }
    /// Actual BL destination (a checked named text entry or checked import stub).
    pub fn destination(&self) -> u64 {
        self.destination
    }
}

#[derive(Debug)]
pub struct CheckedClosedCallPlacement<'a> {
    object: &'a [u8],
    image: &'a [u8],
    caller: &'a [u8],
    callee: &'a [u8],
    caller_address: u64,
    callee_address: u64,
    call_offset: usize,
    callee_calls: Vec<CheckedClosedCallSite>,
}
impl<'a> CheckedClosedCallPlacement<'a> {
    pub fn object(&self) -> &'a [u8] {
        self.object
    }
    pub fn image(&self) -> &'a [u8] {
        self.image
    }
    pub fn caller_bytes(&self) -> &'a [u8] {
        self.caller
    }
    pub fn callee_bytes(&self) -> &'a [u8] {
        self.callee
    }
    pub fn caller_address(&self) -> u64 {
        self.caller_address
    }
    pub fn callee_address(&self) -> u64 {
        self.callee_address
    }
    pub fn call_offset(&self) -> usize {
        self.call_offset
    }
    pub fn callee_calls(&self) -> &[CheckedClosedCallSite] {
        &self.callee_calls
    }
}

fn object_atom<'o>(object: &'o Object, name: &str) -> Result<(usize, &'o Atom), String> {
    let mut found = object
        .symbols
        .iter()
        .enumerate()
        .filter(|(_, s)| s.name == name);
    let (index, symbol) = found.next().ok_or("missing object definition")?;
    if found.next().is_some()
        || !symbol.is_defined()
        || symbol.is_weak_def()
        || symbol.is_weak_ref()
        || (symbol.is_external() && !symbol.is_private_extern())
    {
        return Err("object definition is ambiguous, weak or interposable".into());
    }
    let section_index = usize::from(symbol.n_sect)
        .checked_sub(1)
        .ok_or("invalid symbol section")?;
    let section = object
        .sections
        .get(section_index)
        .ok_or("missing symbol section")?;
    if section.segment != "__TEXT"
        || section.name != "__text"
        || !section.is_code()
        || section.is_zero_fill()
        || section.is_consumed()
    {
        return Err("definition is not ordinary text".into());
    }
    let offset = symbol
        .n_value
        .checked_sub(section.addr)
        .ok_or("symbol before section")?;
    let (atom_index, interior) = object
        .atom_of(section_index, offset)
        .ok_or("symbol outside atom")?;
    let atom = &object.atoms[atom_index];
    if interior != 0
        || atom.end <= atom.start
        || atom.start % 4 != 0
        || atom.end % 4 != 0
        || atom.anchors.as_slice() != [(index, 0)]
    {
        return Err("definition is an aliased/interior/empty/non-word atom".into());
    }
    Ok((index, atom))
}

fn overlaps(start: u64, end: u64, other_start: u64, size: u64) -> bool {
    size != 0
        && other_start < end
        && other_start
            .checked_add(size)
            .is_none_or(|other_end| start < other_end)
}

fn image_entry(image: &Image<'_>, name: &str, private: bool) -> Result<u64, String> {
    let mut named = image.symbols.iter().filter(|s| s.name == name);
    let symbol = named.next().ok_or("missing image symbol")?;
    if named.next().is_some()
        || !symbol.is_defined_in_section()
        || (private && symbol.n_type & N_EXT != 0 && symbol.n_type & N_PEXT == 0)
        || image.strong_overrides.contains(name)
    {
        return Err("image definition is ambiguous or interposable".into());
    }
    let address = symbol.n_value;
    let end = address.checked_add(4).ok_or("image entry end overflow")?;
    let section = image
        .section_at(address, 4)
        .ok_or("image entry outside section")?;
    if image
        .sections
        .iter()
        .filter(|s| overlaps(address, end, s.addr, s.size))
        .count()
        != 1
    {
        return Err("ambiguous image entry section".into());
    }
    let mut segments = image
        .segments
        .iter()
        .filter(|s| overlaps(address, end, s.vmaddr, s.vmsize));
    let segment = segments.next().ok_or("image entry outside segment")?;
    if segments.next().is_some() {
        return Err("ambiguous image entry segment".into());
    }
    if address % 4 != 0
        || section.addr.checked_add(section.size).is_none()
        || segment.vmaddr.checked_add(segment.vmsize).is_none()
        || section.segment != "__TEXT"
        || section.name != "__text"
        || section.is_zero_fill()
        || section.is_linker_synthesized()
        || segment.initprot & VM_PROT_EXECUTE == 0
        || segment.initprot & VM_PROT_WRITE != 0
        || image
            .symbols
            .iter()
            .filter(|s| s.is_defined_in_section() && s.n_value == address)
            .count()
            != 1
        || (private && image.exports.contains_key(name))
    {
        return Err("image entry is aliased, exported or not immutable text".into());
    }
    Ok(address)
}

fn placed_atom<'a>(image: &Image<'a>, name: &str, length: u64) -> Result<(u64, &'a [u8]), String> {
    let address = image_entry(image, name, true)?;
    let end = address
        .checked_add(length)
        .ok_or("image atom end overflow")?;
    let section = image
        .section_at(address, length)
        .ok_or("image atom crosses section/hole")?;
    if image
        .sections
        .iter()
        .filter(|s| overlaps(address, end, s.addr, s.size))
        .count()
        != 1
    {
        return Err("ambiguous image atom section".into());
    }
    let next = image
        .symbols
        .iter()
        .filter(|s| {
            s.is_defined_in_section() && s.n_value > address && section.contains(s.n_value, 1)
        })
        .map(|s| s.n_value)
        .min()
        .unwrap_or(
            section
                .addr
                .checked_add(section.size)
                .ok_or("section end overflow")?,
        );
    if next != end
        || image
            .fixups
            .range(address.saturating_sub(7)..end)
            .next()
            .is_some()
    {
        return Err("image atom extent differs or contains runtime fixups".into());
    }
    // A partial overlap also makes the runtime bytes ambiguous.
    let mut segments = image
        .segments
        .iter()
        .filter(|s| overlaps(address, end, s.vmaddr, s.vmsize));
    let segment = segments.next().ok_or("image atom outside segment")?;
    if segments.next().is_some()
        || segment.vmaddr.checked_add(segment.vmsize).is_none()
        || segment.initprot & VM_PROT_EXECUTE == 0
        || segment.initprot & VM_PROT_WRITE != 0
    {
        return Err("ambiguous or writable image atom".into());
    }
    let relative = address
        .checked_sub(segment.vmaddr)
        .ok_or("atom before segment")?;
    if relative
        .checked_add(length)
        .is_none_or(|end| end > segment.filesize || end > segment.vmsize)
    {
        return Err("image atom is not completely file-backed".into());
    }
    let file = segment
        .fileoff
        .checked_add(relative)
        .ok_or("atom file offset overflow")?;
    let start = usize::try_from(file).map_err(|_| "file offset overflow")?;
    let len = usize::try_from(length).map_err(|_| "atom length overflow")?;
    let bytes = image
        .bytes
        .get(start..start.checked_add(len).ok_or("file range overflow")?)
        .ok_or("image atom exceeds file")?;
    Ok((address, bytes))
}

fn branch_destination(pc: u64, word: u32) -> Result<u64, String> {
    if word & 0xfc00_0000 != 0x9400_0000 {
        return Err("relocation is not an actual BL".into());
    }
    // Same signed BRANCH26 decoding as the independent linked-image replay.
    let displacement = ((u64::from(word & 0x03ff_ffff) << 38) as i64) >> 36;
    pc.checked_add_signed(displacement)
        .ok_or_else(|| "BL destination overflow".into())
}

fn check_call_target(image: &Image<'_>, symbol: &str, destination: u64) -> Result<(), String> {
    if image
        .symbols
        .iter()
        .any(|s| s.name == symbol && s.is_defined_in_section())
    {
        if image_entry(image, symbol, false)? != destination {
            return Err("BL misses named image entry".into());
        }
        return Ok(());
    }
    // An imported call may go only to a genuine stub whose decoded pointer
    // binding names this exact import. This proves no provider behavior.
    let slot = image.stub_slot(destination)?;
    match image
        .resolution_at(slot)
        .ok_or("stub has no pointer binding")??
    {
        Resolution::Import {
            ordinal,
            symbol: actual,
            addend: 0,
            weak_import: false,
            ..
        } if ordinal > 0 && actual == symbol => Ok(()),
        _ => Err("stub import identity is weak/ambiguous/different".into()),
    }
}

fn compare_atom(
    object: &Object,
    atom: &Atom,
    image: &Image<'_>,
    address: u64,
    linked: &[u8],
) -> Result<Vec<CheckedClosedCallSite>, String> {
    let section = &object.sections[atom.section];
    let start = usize::try_from(atom.start).map_err(|_| "atom offset overflow")?;
    let end = usize::try_from(atom.end).map_err(|_| "atom end overflow")?;
    let original = section
        .data
        .get(start..end)
        .ok_or("atom exceeds object bytes")?;
    if original.len() != linked.len() {
        return Err("atom length differs".into());
    }
    let mut masks = vec![0u32; original.len() / 4];
    let mut calls = Vec::new();
    for r in &section.relocs {
        let at = u64::from(r.address);
        if at < atom.start || at >= atom.end {
            let width = 1u64
                .checked_shl(u32::from(r.length))
                .ok_or("relocation width overflow")?;
            if at < atom.end && at.checked_add(width).is_none_or(|end| end > atom.start) {
                return Err("relocation overlaps selected atom boundary".into());
            }
            continue;
        }
        if at % 4 != 0
            || at.checked_add(4).is_none_or(|e| e > atom.end)
            || r.length != 2
            || !r.external
        {
            return Err("unsupported/misaligned relocation in atom".into());
        }
        let relative = usize::try_from(at - atom.start).map_err(|_| "relative offset overflow")?;
        let raw = read_u32(original, relative).ok_or("missing original word")?;
        let word = read_u32(linked, relative).ok_or("missing linked word")?;
        if masks[relative / 4] != 0 {
            return Err("overlapping/addend relocation".into());
        }
        masks[relative / 4] = match r.kind {
            ARM64_RELOC_BRANCH26 if r.pcrel && raw == 0x9400_0000 => {
                let symbol = object
                    .symbols
                    .get(r.symbolnum as usize)
                    .ok_or("missing relocation symbol")?;
                if symbol.is_weak_def() || symbol.is_weak_ref() {
                    return Err("weak call target".into());
                }
                let pc = address
                    .checked_add(relative as u64)
                    .ok_or("call address overflow")?;
                let destination = branch_destination(pc, word)?;
                check_call_target(image, &symbol.name, destination)?;
                calls.push(CheckedClosedCallSite {
                    offset: relative,
                    symbol: symbol.name.clone(),
                    destination,
                });
                0x03ff_ffff
            }
            ARM64_RELOC_PAGE21 | ARM64_RELOC_GOT_LOAD_PAGE21 | ARM64_RELOC_TLVP_LOAD_PAGE21
                if r.pcrel
                    && raw & 0x9f00_0000 == 0x9000_0000
                    && word & 0x9f00_0000 == 0x9000_0000 =>
            {
                0x60ff_ffe0
            }
            ARM64_RELOC_PAGEOFF12
            | ARM64_RELOC_GOT_LOAD_PAGEOFF12
            | ARM64_RELOC_TLVP_LOAD_PAGEOFF12
                if !r.pcrel =>
            {
                let add = raw & 0xffc0_0000 == 0x9100_0000;
                let load = raw & 0xffc0_0000 == 0xf940_0000;
                if !add && !load {
                    return Err("unsupported PAGEOFF12 instruction".into());
                }
                if load
                    && r.kind == ARM64_RELOC_GOT_LOAD_PAGEOFF12
                    && word & 0xffc0_0000 == 0x9100_0000
                {
                    // ld64's documented GOT LDR -> ADD relaxation preserves both registers.
                    0xffc0_0000 | 0x003f_fc00
                } else {
                    0x003f_fc00
                }
            }
            _ => return Err("unsupported relocation in selected atom".into()),
        };
    }
    for (index, (a, b)) in original
        .chunks_exact(4)
        .zip(linked.chunks_exact(4))
        .enumerate()
    {
        let a = u32::from_le_bytes(a.try_into().map_err(|_| "object word")?);
        let b = u32::from_le_bytes(b.try_into().map_err(|_| "image word")?);
        if (a ^ b) & !masks[index] != 0 {
            return Err(format!("nonrelocated atom bytes differ at {}", index * 4));
        }
    }
    calls.sort_by_key(|c| c.offset);
    Ok(calls)
}

/// Check one exact same-object private direct call in a linked arm64 image.
/// Relocation fields are compared only at their known encoding bits; their
/// data-address semantics are NOT certified by this narrow owner. All normal
/// BL relocations in both selected atoms are independently target-checked.
/// The result grants no callable/storage, source or no-return authority.
pub fn check_closed_call_placement<'a>(
    object_bytes: &'a [u8],
    image_bytes: &'a [u8],
    caller: &str,
    callee: &str,
    call_offset: usize,
) -> Result<CheckedClosedCallPlacement<'a>, String> {
    if caller == callee || caller.is_empty() || callee.is_empty() {
        return Err("distinct nonempty symbols required".into());
    }
    if read_u32(object_bytes, 8).is_none_or(|subtype| subtype & 0x00ff_ffff != 0) {
        return Err("object CPU subtype is not ARM64_ALL".into());
    }
    let object = Object::parse("closed-call", object_bytes)?;
    let image = Image::parse(image_bytes)?;
    if object.flags & MH_SUBSECTIONS_VIA_SYMBOLS == 0 || image.flags & MH_TWOLEVEL == 0 {
        return Err("atomized object/two-level image required".into());
    }
    let (caller_index, caller_atom) = object_atom(&object, caller)?;
    let (callee_index, callee_atom) = object_atom(&object, callee)?;
    let (caller_address, caller_bytes) =
        placed_atom(&image, caller, caller_atom.end - caller_atom.start)?;
    let (callee_address, callee_bytes) =
        placed_atom(&image, callee, callee_atom.end - callee_atom.start)?;
    if caller_address
        < callee_address
            .checked_add(callee_bytes.len() as u64)
            .ok_or("callee end overflow")?
        && callee_address
            < caller_address
                .checked_add(caller_bytes.len() as u64)
                .ok_or("caller end overflow")?
    {
        return Err("placed atoms overlap".into());
    }
    if call_offset % 4 != 0
        || call_offset
            .checked_add(4)
            .is_none_or(|end| end > caller_bytes.len())
    {
        return Err("call offset outside caller".into());
    }
    let calls = compare_atom(&object, caller_atom, &image, caller_address, caller_bytes)?;
    let callee_calls = compare_atom(&object, callee_atom, &image, callee_address, callee_bytes)?;
    let call = calls
        .iter()
        .find(|c| c.offset == call_offset)
        .ok_or("call offset has no exact BL relocation")?;
    if call.symbol != callee || call.destination != callee_address {
        return Err("caller BL does not reach selected callee".into());
    }
    let section = &object.sections[caller_atom.section];
    let absolute = caller_atom
        .start
        .checked_add(call_offset as u64)
        .ok_or("call offset overflow")?;
    if section
        .relocs
        .iter()
        .filter(|r| u64::from(r.address) == absolute && r.symbolnum as usize == callee_index)
        .count()
        != 1
        || caller_index == callee_index
    {
        return Err("caller relocation does not bind exact object definition".into());
    }
    Ok(CheckedClosedCallPlacement {
        object: object_bytes,
        image: image_bytes,
        caller: caller_bytes,
        callee: callee_bytes,
        caller_address,
        callee_address,
        call_offset,
        callee_calls,
    })
}
