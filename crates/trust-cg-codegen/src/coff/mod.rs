// trust-cg-codegen/coff/mod.rs - COFF object file support
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Minimal COFF relocatable object writer for x86-64 Windows AOT.
//!
//! This module emits little-endian AMD64 COFF `.obj` files with section
//! headers, section data, relocations, a COFF symbol table, and a string table.
//! The first production slice intentionally uses short COFF section names only
//! and rejects section relocation counts that exceed the 16-bit COFF header
//! field.

pub mod writer;

pub use writer::{
    CoffError, CoffRelocation, CoffResult, CoffSection, CoffSymbol, CoffWriter,
    IMAGE_COMDAT_SELECT_ANY, IMAGE_COMDAT_SELECT_ASSOCIATIVE, IMAGE_COMDAT_SELECT_EXACT_MATCH,
    IMAGE_COMDAT_SELECT_LARGEST, IMAGE_COMDAT_SELECT_NODUPLICATES, IMAGE_COMDAT_SELECT_SAME_SIZE,
    IMAGE_FILE_MACHINE_AMD64, IMAGE_REL_AMD64_ADDR32, IMAGE_REL_AMD64_ADDR32NB,
    IMAGE_REL_AMD64_ADDR64, IMAGE_REL_AMD64_REL32, IMAGE_REL_AMD64_SECREL, IMAGE_REL_AMD64_SECREL7,
    IMAGE_REL_AMD64_SECTION, IMAGE_REL_AMD64_TOKEN, IMAGE_SCN_ALIGN_4BYTES, IMAGE_SCN_ALIGN_8BYTES,
    IMAGE_SCN_ALIGN_16BYTES, IMAGE_SCN_CNT_CODE, IMAGE_SCN_CNT_INITIALIZED_DATA,
    IMAGE_SCN_LNK_COMDAT, IMAGE_SCN_MEM_EXECUTE, IMAGE_SCN_MEM_READ, IMAGE_SYM_CLASS_EXTERNAL,
    IMAGE_SYM_CLASS_STATIC, IMAGE_SYM_DTYPE_FUNCTION, IMAGE_SYM_TYPE_NULL,
};
