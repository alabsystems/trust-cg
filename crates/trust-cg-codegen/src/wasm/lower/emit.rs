// trust-cg-codegen/wasm/lower/emit.rs - index and address immediates
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Every immediate that names another entity — a function, a global, a data
//! address, a type, the table — is emitted through this file.
//!
//! In a closed module the entity's final index or address is known, so the
//! immediate is its minimal LEB128 (byte-identical to the pre-object lowering).
//! In a relocatable object it is not: the immediate is a 5-byte padded LEB128
//! holding the object-local value, and a relocation records where it is and
//! what it names, for `wasm-ld` to rewrite. Keeping both spellings in one
//! place is what stops a new call site from forgetting the relocation.

use super::super::encode::{
    Reloc, RelocKind, RelocTarget, closed_table_index, op, write_padded_sleb128,
    write_padded_uleb128, write_sleb128, write_uleb128,
};
use super::{DataAddr, Lowering};

impl Lowering<'_> {
    fn reloc_here(&mut self, kind: RelocKind, target: RelocTarget, addend: i32) {
        self.relocs.push(Reloc {
            kind,
            offset: self.code.len() as u32,
            target,
            addend,
        });
    }

    /// `call $func` (a wasm function index).
    pub(super) fn emit_call(&mut self, func: u32) {
        self.code.push(op::CALL);
        if self.object {
            self.reloc_here(RelocKind::FunctionIndexLeb, RelocTarget::Func(func), 0);
            write_padded_uleb128(&mut self.code, func);
        } else {
            write_uleb128(&mut self.code, u64::from(func));
        }
    }

    /// `i32.const <table index of $func>` — a function pointer.
    pub(super) fn emit_func_ptr(&mut self, func: u32) {
        self.code.push(op::I32_CONST);
        if self.object {
            self.reloc_here(RelocKind::TableIndexSleb, RelocTarget::Func(func), 0);
            write_padded_sleb128(&mut self.code, func as i32);
        } else {
            // Closed module: the table holds every function at element
            // `closed_table_index(funcidx)`; element 0 is the null funcref, so
            // no function pointer is the null pointer.
            write_sleb128(&mut self.code, i64::from(closed_table_index(func) as i32));
        }
    }

    /// `global.get` / `global.set` of the shadow stack pointer (or any global).
    pub(super) fn emit_global_op(&mut self, opcode: u8, global: u32) {
        self.code.push(opcode);
        if self.object {
            self.reloc_here(RelocKind::GlobalIndexLeb, RelocTarget::Global(global), 0);
            write_padded_uleb128(&mut self.code, global);
        } else {
            write_uleb128(&mut self.code, u64::from(global));
        }
    }

    /// `i32.const <address>` of static data (a global or a pooled constant),
    /// plus `addend` bytes.
    pub(super) fn emit_data_addr(&mut self, addr: DataAddr, addend: i32) {
        self.code.push(op::I32_CONST);
        match addr.item {
            Some(item) if self.object => {
                self.reloc_here(RelocKind::MemoryAddrSleb, RelocTarget::Data(item), addend);
                write_padded_sleb128(&mut self.code, (addr.addr as i32).wrapping_add(addend));
            }
            _ => write_sleb128(
                &mut self.code,
                i64::from((addr.addr as i32).wrapping_add(addend)),
            ),
        }
    }

    /// The type-index and table immediates of `call_indirect`.
    pub(super) fn emit_call_indirect(&mut self, type_idx: u32) {
        self.code.push(op::CALL_INDIRECT);
        if self.object {
            self.reloc_here(RelocKind::TypeIndexLeb, RelocTarget::Type(type_idx), 0);
            write_padded_uleb128(&mut self.code, type_idx);
            self.reloc_here(RelocKind::TableNumberLeb, RelocTarget::Table, 0);
            write_padded_uleb128(&mut self.code, 0);
        } else {
            write_uleb128(&mut self.code, u64::from(type_idx));
            write_uleb128(&mut self.code, 0); // table 0
        }
    }
}
