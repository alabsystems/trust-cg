// trust-cg-codegen/elf/dwarf.rs - DWARF debug sections in AArch64 ELF objects
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: DWARF Debugging Information Format Version 4, sections 7.4-7.5
// Reference: ARM IHI 0056, "ELF for the Arm 64-bit Architecture" (static data relocations)

//! Place a [`DwarfSectionImage`] in an AArch64 ELF relocatable object.
//!
//! The image comes from [`crate::dwarf_info::DwarfDebugInfo::try_emit_section_image`],
//! the same producer the Mach-O path uses. Attachment has three phases that
//! follow the ELF writer's checked symbol protocol:
//!
//! 1. [`ElfDwarfSections::add_sections`] adds the non-allocated `SHT_PROGBITS`
//!    `.debug_*` sections. Every relocated field is cleared to zero first
//!    (the GNU `SHT_RELA` convention), so a lost relocation reads as zero
//!    instead of an object-local value that is accidentally right for a
//!    single object.
//! 2. [`ElfDwarfSections::add_anchor_symbols`] adds one local `STT_SECTION`
//!    symbol per section a relocation targets (and a `.text` one unless the
//!    emitter already has it) through [`ElfWriter::add_checked_symbol`], before
//!    the emitter freezes its table.
//! 3. [`ElfDwarfSections::add_relocations`] adds, after every index is final,
//!    `R_AARCH64_ABS64` for each code address (`DW_FORM_addr`,
//!    `DW_LNE_set_address`) and `R_AARCH64_ABS32` for each DWARF32 section
//!    offset (`DW_FORM_strp`, `DW_FORM_sec_offset`, the unit header's
//!    abbreviation offset and `DW_AT_stmt_list`), each with its explicit addend.
//!
//! DWARF4 `.debug_loc` entries are offsets from the compile unit's base
//! address and carry no relocation. The object then goes through the
//! pipeline's `finish_elf_object` funnel, whose reparse gate checks every
//! section, symbol and relocation record against the writer's intent.

use super::constants::{SHT_PROGBITS, STT_SECTION, STV_DEFAULT};
use super::reloc::{AArch64RelocType, Elf64Rela};
use super::writer::{ElfSymbol, ElfSymbolError, ElfSymbolId, ElfWriter};
use crate::dwarf_info::{
    DwarfEmitError, DwarfRelocTarget, DwarfRelocWidth, DwarfSectionImage, DwarfSectionKind,
};

/// DWARF sections added to an [`ElfWriter`], awaiting anchors and relocations.
#[derive(Debug, Clone)]
pub struct ElfDwarfSections {
    /// The image as placed in the object (relocated fields cleared).
    image: DwarfSectionImage,
    /// 1-based section header index of each placed section.
    placed: Vec<(DwarfSectionKind, u16)>,
    /// 1-based section header index of the text section the code-address
    /// relocations target.
    text_shndx: u16,
}

/// Symbol handles issued by [`ElfDwarfSections::add_anchor_symbols`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElfDwarfAnchors {
    text: ElfSymbolId,
    sections: Vec<(DwarfSectionKind, ElfSymbolId)>,
}

/// Final `.symtab` indices of [`ElfDwarfAnchors`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElfDwarfAnchorIndices {
    text: u32,
    sections: Vec<(DwarfSectionKind, u32)>,
}

impl ElfDwarfAnchors {
    /// Resolve every anchor to its final `.symtab` index. Like any
    /// [`ElfWriter::final_symbol_index`] call this freezes the table, so call
    /// it only after every other symbol has been added.
    pub fn final_indices(
        &self,
        writer: &mut ElfWriter,
    ) -> Result<ElfDwarfAnchorIndices, ElfSymbolError> {
        let text = writer.final_symbol_index(self.text)?;
        let sections = self
            .sections
            .iter()
            .map(|(kind, id)| Ok((*kind, writer.final_symbol_index(*id)?)))
            .collect::<Result<_, ElfSymbolError>>()?;
        Ok(ElfDwarfAnchorIndices { text, sections })
    }
}

impl ElfDwarfSections {
    /// Add the image's sections after every section already in `writer`.
    ///
    /// `text_shndx` is the 1-based section header index of the object's text
    /// section, against which every code address is relocated.
    pub fn add_sections(
        writer: &mut ElfWriter,
        image: &DwarfSectionImage,
        text_shndx: u16,
    ) -> Result<Self, DwarfEmitError> {
        let mut image = image.clone();
        image.clear_relocated_fields()?;
        let mut placed = Vec::with_capacity(DwarfSectionKind::ALL.len());
        for kind in DwarfSectionKind::ALL {
            if let Some(bytes) = image.section(kind) {
                let shndx = writer
                    .add_section(kind.elf_name(), bytes, SHT_PROGBITS, 0, 1)
                    .map_err(|error| DwarfEmitError::SectionRefused(error.to_string()))?;
                placed.push((kind, shndx));
            }
        }
        Ok(Self {
            image,
            placed,
            text_shndx,
        })
    }

    /// The image as placed in the object, with every relocated field zero.
    pub fn placed_image(&self) -> &DwarfSectionImage {
        &self.image
    }

    /// 1-based section header index of `kind`, when placed.
    pub fn section_index(&self, kind: DwarfSectionKind) -> Option<u16> {
        self.placed
            .iter()
            .find(|(placed, _)| *placed == kind)
            .map(|(_, shndx)| *shndx)
    }

    /// Add a local `STT_SECTION` symbol for each DWARF section that some
    /// relocation targets, and for the text section unless `text_anchor`
    /// already names the emitter's own `.text` section symbol.
    pub fn add_anchor_symbols(
        &self,
        writer: &mut ElfWriter,
        text_anchor: Option<ElfSymbolId>,
    ) -> Result<ElfDwarfAnchors, ElfSymbolError> {
        let section_symbol = |name: &str, section: u16| ElfSymbol {
            name: name.to_string(),
            section,
            value: 0,
            size: 0,
            is_global: false,
            sym_type: STT_SECTION,
            is_weak: false,
            visibility: STV_DEFAULT,
        };
        let text = match text_anchor {
            Some(id) => id,
            None => writer.add_checked_symbol(section_symbol(".text", self.text_shndx))?,
        };
        let mut sections = Vec::new();
        for (kind, shndx) in &self.placed {
            let targeted = self
                .image
                .relocations
                .iter()
                .any(|reloc| reloc.target == DwarfRelocTarget::Section(*kind));
            if targeted {
                let id = writer.add_checked_symbol(section_symbol(kind.elf_name(), *shndx))?;
                sections.push((*kind, id));
            }
        }
        Ok(ElfDwarfAnchors { text, sections })
    }

    /// Add one AArch64 relocation record per relocated DWARF field.
    pub fn add_relocations(
        &self,
        writer: &mut ElfWriter,
        anchors: &ElfDwarfAnchorIndices,
    ) -> Result<(), DwarfEmitError> {
        for reloc in &self.image.relocations {
            let shndx = self.section_index(reloc.section).ok_or_else(|| {
                DwarfEmitError::RelocationFailed(format!(
                    "{:?} field at {:#x} lies in a section that was not placed",
                    reloc.section, reloc.offset
                ))
            })?;
            let (symbol, kind) = match (reloc.target, reloc.width) {
                (DwarfRelocTarget::Text, DwarfRelocWidth::Bits64) => {
                    (anchors.text, AArch64RelocType::Abs64)
                }
                (DwarfRelocTarget::Section(target), DwarfRelocWidth::Bits32) => {
                    let symbol = anchors
                        .sections
                        .iter()
                        .find(|(kind, _)| *kind == target)
                        .map(|(_, index)| *index)
                        .ok_or_else(|| {
                            DwarfEmitError::RelocationFailed(format!(
                                "no anchor symbol for relocation target {target:?}"
                            ))
                        })?;
                    // `S` is the section's offset in the linked debug
                    // section, never negative: an addend above the window
                    // overflows in every link. The rest of the window is the
                    // linker's check of `S + A`.
                    let Some(window) = AArch64RelocType::Abs32.displacement_window() else {
                        return Err(DwarfEmitError::RelocationFailed(
                            "R_AARCH64_ABS32 has no displacement window".to_string(),
                        ));
                    };
                    if i128::from(reloc.addend) > i128::from(window.max) {
                        return Err(DwarfEmitError::Abs32AddendOutOfWindow {
                            section: reloc.section,
                            offset: reloc.offset,
                            addend: reloc.addend,
                            max: window.max,
                        });
                    }
                    (symbol, AArch64RelocType::Abs32)
                }
                (target, width) => {
                    return Err(DwarfEmitError::RelocationFailed(format!(
                        "{:?} field at {:#x} pairs target {target:?} with width {width:?}; \
                         code addresses are 64-bit and section offsets DWARF32",
                        reloc.section, reloc.offset
                    )));
                }
            };
            let addend = i64::try_from(reloc.addend).map_err(|_| {
                DwarfEmitError::RelocationFailed(format!(
                    "{:?} field at {:#x} has unrepresentable addend {:#x}",
                    reloc.section, reloc.offset, reloc.addend
                ))
            })?;
            writer.add_relocation(
                usize::from(shndx) - 1,
                Elf64Rela::aarch64(u64::from(reloc.offset), symbol, kind, addend),
            );
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dwarf_info::{
        BaseType, DwarfDebugInfo, FunctionDebugInfo, FunctionParam, SourceLanguage,
        SourceLineEntry, VariableLocation,
    };
    use crate::elf::ElfMachine;
    use crate::elf::constants::STT_FUNC;
    use crate::elf::reparse::{ElfReparseMode, run_elf_reparse_gate};

    fn debug_info() -> DwarfDebugInfo {
        let mut dbg = DwarfDebugInfo::new("unit.rs", "/src", SourceLanguage::Rust);
        dbg.add_base_type(BaseType::i64());
        dbg.add_function(FunctionDebugInfo {
            name: "f".to_string(),
            linkage_name: None,
            low_pc: 0,
            size: 8,
            params: vec![FunctionParam {
                name: "x".to_string(),
                type_index: 0,
                location: VariableLocation::location_list(0, 4, VariableLocation::Register(0)),
            }],
            variables: vec![],
            scopes: vec![],
            line_entries: vec![
                SourceLineEntry {
                    address: 0,
                    line: 3,
                    column: 1,
                    is_stmt: true,
                },
                SourceLineEntry {
                    address: 4,
                    line: 4,
                    column: 1,
                    is_stmt: true,
                },
            ],
            decl_file: 1,
            decl_line: 3,
        });
        dbg.add_function(FunctionDebugInfo {
            name: "g".to_string(),
            linkage_name: None,
            low_pc: 8,
            size: 4,
            params: vec![],
            variables: vec![],
            scopes: vec![],
            line_entries: vec![SourceLineEntry {
                address: 8,
                line: 7,
                column: 1,
                is_stmt: true,
            }],
            decl_file: 1,
            decl_line: 7,
        });
        dbg
    }

    fn object(image: &DwarfSectionImage) -> (ElfWriter, ElfDwarfSections) {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0x1F, 0x20, 0x03, 0xD5].repeat(3));
        let sections = ElfDwarfSections::add_sections(&mut writer, image, 1).unwrap();
        let anchors = sections.add_anchor_symbols(&mut writer, None).unwrap();
        writer
            .add_checked_symbol(ElfSymbol {
                name: "f".to_string(),
                section: 1,
                value: 0,
                size: 8,
                is_global: true,
                sym_type: STT_FUNC,
                is_weak: false,
                visibility: STV_DEFAULT,
            })
            .unwrap();
        let indices = anchors.final_indices(&mut writer).unwrap();
        sections.add_relocations(&mut writer, &indices).unwrap();
        (writer, sections)
    }

    #[test]
    fn every_relocated_field_gets_one_aarch64_record() {
        let image = debug_info().try_emit_section_image().unwrap().unwrap();
        let (writer, sections) = object(&image);
        let intent = writer.reparse_object_intent();
        let bytes = writer.write_checked().unwrap();
        run_elf_reparse_gate(&intent, &bytes, ElfReparseMode::Enforce).unwrap();

        let info = sections.section_index(DwarfSectionKind::Info).unwrap();
        let line = sections.section_index(DwarfSectionKind::Line).unwrap();
        let info_relocs = &intent.section_relocs[usize::from(info) - 1];
        let line_relocs = &intent.section_relocs[usize::from(line) - 1];
        let expected_info = image
            .relocations
            .iter()
            .filter(|reloc| reloc.section == DwarfSectionKind::Info)
            .count();
        assert_eq!(info_relocs.len(), expected_info);
        assert!(
            info_relocs
                .iter()
                .any(|reloc| reloc.reloc_type == AArch64RelocType::Abs32.to_type_val())
        );
        assert!(
            info_relocs
                .iter()
                .any(|reloc| reloc.reloc_type == AArch64RelocType::Abs64.to_type_val())
        );
        // g's set_address carries the function's text offset as its addend.
        assert!(
            line_relocs
                .iter()
                .all(|reloc| reloc.reloc_type == AArch64RelocType::Abs64.to_type_val())
        );
        assert!(line_relocs.iter().any(|reloc| reloc.r_addend == 8));
        // `.debug_loc` exists but is never relocated (CU-base relative).
        let loc = sections.section_index(DwarfSectionKind::Loc).unwrap();
        assert!(intent.section_relocs[usize::from(loc) - 1].is_empty());
    }

    #[test]
    fn placed_image_clears_every_relocated_field() {
        let image = debug_info().try_emit_section_image().unwrap().unwrap();
        let (_, sections) = object(&image);
        let placed = sections.placed_image();
        for reloc in &placed.relocations {
            let bytes = placed.section(reloc.section).unwrap();
            let start = reloc.offset as usize;
            assert!(
                bytes[start..start + reloc.width.bytes()]
                    .iter()
                    .all(|b| *b == 0),
                "{reloc:?} must be zero in place"
            );
        }
        // The original image still holds the addends in place.
        assert_ne!(placed.info, image.info);
    }

    #[test]
    fn existing_text_anchor_is_reused() {
        let image = debug_info().try_emit_section_image().unwrap().unwrap();
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0; 12]);
        let text = writer
            .add_checked_symbol(ElfSymbol {
                name: ".text".to_string(),
                section: 1,
                value: 0,
                size: 0,
                is_global: false,
                sym_type: STT_SECTION,
                is_weak: false,
                visibility: STV_DEFAULT,
            })
            .unwrap();
        let sections = ElfDwarfSections::add_sections(&mut writer, &image, 1).unwrap();
        let anchors = sections
            .add_anchor_symbols(&mut writer, Some(text))
            .unwrap();
        assert_eq!(anchors.text, text);
        // .debug_abbrev, .debug_str, .debug_line and .debug_loc are targets;
        // .debug_info is not.
        assert_eq!(anchors.sections.len(), 4);
        assert!(
            anchors
                .sections
                .iter()
                .all(|(kind, _)| *kind != DwarfSectionKind::Info)
        );
    }

    #[test]
    fn late_anchor_after_freeze_fails_closed() {
        let image = debug_info().try_emit_section_image().unwrap().unwrap();
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0; 12]);
        let f = writer
            .add_checked_symbol(ElfSymbol {
                name: "f".to_string(),
                section: 1,
                value: 0,
                size: 8,
                is_global: true,
                sym_type: STT_FUNC,
                is_weak: false,
                visibility: STV_DEFAULT,
            })
            .unwrap();
        writer.final_symbol_index(f).unwrap();
        let sections = ElfDwarfSections::add_sections(&mut writer, &image, 1).unwrap();
        assert!(matches!(
            sections.add_anchor_symbols(&mut writer, None),
            Err(ElfSymbolError::SymbolTableFrozen { .. })
        ));
    }

    /// Relocate `image` into a fresh object, returning the relocation step's
    /// result and, on success, the checked bytes.
    fn relocate(image: &DwarfSectionImage) -> Result<(ElfWriter, Vec<u8>), DwarfEmitError> {
        let mut writer = ElfWriter::new(ElfMachine::AArch64);
        writer.add_text_section(&[0x1F, 0x20, 0x03, 0xD5].repeat(3));
        let sections = ElfDwarfSections::add_sections(&mut writer, image, 1)?;
        let anchors = sections.add_anchor_symbols(&mut writer, None).unwrap();
        let indices = anchors.final_indices(&mut writer).unwrap();
        sections.add_relocations(&mut writer, &indices)?;
        let bytes = writer.write_checked().expect("checked write");
        Ok((writer, bytes))
    }

    /// A DWARF32 section offset whose `ABS32` addend alone is above the
    /// psABI window (`S + A < 2^32`, `S >= 0`) is refused by name; the
    /// addend at the window's edge is emitted with that exact addend.
    #[test]
    fn abs32_section_offset_addend_is_refused_above_the_psabi_window() {
        let image = debug_info().try_emit_section_image().unwrap().unwrap();
        let index = image
            .relocations
            .iter()
            .position(|reloc| reloc.width == DwarfRelocWidth::Bits32)
            .expect("a DWARF32 section offset");
        let with_addend = |addend: u64| {
            let mut image = image.clone();
            image.relocations[index].addend = addend;
            image
        };

        let edge = u64::from(u32::MAX);
        let (writer, _) = relocate(&with_addend(edge)).expect("addend 2^32 - 1 is in the window");
        let intent = writer.reparse_object_intent();
        let edge_records: Vec<_> = intent
            .section_relocs
            .iter()
            .flatten()
            .filter(|rela| rela.reloc_type == AArch64RelocType::Abs32.to_type_val())
            .filter(|rela| rela.r_addend == i64::from(u32::MAX))
            .collect();
        assert_eq!(
            edge_records.len(),
            1,
            "one ABS32 record carries the edge addend"
        );

        let error = relocate(&with_addend(edge + 1))
            .map(|_| ())
            .expect_err("addend 2^32 overflows in every link");
        assert!(
            matches!(
                error,
                DwarfEmitError::Abs32AddendOutOfWindow { addend, max, .. }
                    if addend == 1 << 32 && max == (1 << 32) - 1
            ),
            "{error:?}"
        );
        assert!(
            error.to_string().starts_with("[TCG-RELOC-WINDOW-ABS32] "),
            "{error}"
        );
    }
}
