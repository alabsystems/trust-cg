// trust-cg-lower/trust_ir_compat.rs - trust_ir re-exports for crates without a
// direct trust-ir dependency
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Re-exports of the trust_ir items that the fuzz targets (fuzz/ has no direct
// trust-ir dependency), the rustc bridge's mem_refine.rs and adapter.rs import
// through this path. It defines no types of its own.

pub use trust_ir::Ordering as MemoryOrdering;
pub use trust_ir::{
    BinOp, Block, BlockId, Constant, FuncId, FuncTy, Function, ICmpOp, Inst, InstrNode, Module, Ty,
    ValueId,
};
