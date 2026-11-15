//! Errors shared by register-allocation phases.

use crate::machine_types::RegClass;
use thiserror::Error;

/// Errors that can occur during register allocation.
#[derive(Debug, Error)]
pub enum AllocError {
    #[error("cannot spill fixed interval for {0}")]
    CannotSpillFixed(String),
    #[error("no allocatable registers for class {0:?}")]
    NoRegistersForClass(RegClass),
    #[error("virtual-register ID space exhausted")]
    VirtualRegisterExhausted,
    #[error("stack-slot ID space exhausted")]
    StackSlotExhausted,
    #[error("register allocation failed: {0}")]
    Failed(String),
    #[error("register allocation translation validation failed: {0}")]
    ValidationFailed(String),
}
