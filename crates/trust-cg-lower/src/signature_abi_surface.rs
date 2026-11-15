// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Wire-v60 records source placement separately from the IR carrier census.
//! Contextless and WASM entries cannot consume these claims. The explicit
//! compiler-selected native scalar C entry validates its finite profile before
//! projection; every entry using this floor still refuses all recorded rows.
//! Structural IR validation and exact record custody do not establish that
//! emitted calls implement hidden results, source modes, or extensions.

use super::AdapterError;
use trust_ir::{FuncTy, Module};

pub(super) fn refuse_recorded(module: &Module) -> Result<(), AdapterError> {
    // Include unused rows and first-class callable signatures. Checking only
    // Function.ty would let a recorded indirect signature bypass the floor.
    for (signature, function_type) in module.func_types.iter().enumerate() {
        // A future signature field must be classified rather than ignored.
        let FuncTy {
            params: _,
            returns: _,
            is_vararg: _,
            abi,
        } = function_type;
        if abi.is_some() {
            return Err(AdapterError::UnsupportedSignatureAbi {
                module: module.name.clone(),
                signature,
            });
        }
    }
    Ok(())
}

#[cfg(test)]
#[path = "signature_abi_surface_tests.rs"]
mod tests;
