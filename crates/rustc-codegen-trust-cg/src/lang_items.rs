// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0

//! The retained language-item enum, selected by build.rs's checked import.
//! This alias does not restore removed memory variants or supply a callee's
//! identity, signature or ABI authority.

#[cfg(rustc_attr_ir_lang_items)]
pub(crate) use rustc_attr_ir::lang_items::LangItem;
#[cfg(not(rustc_attr_ir_lang_items))]
pub(crate) use rustc_hir::LangItem;
