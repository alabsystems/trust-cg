// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
// Compile and execute actual production models against both private APIs.
// These are model/descriptor tests, not modern backend codegen or proof credit.
#![feature(rustc_private)]
extern crate rustc_abi;
// The compiler package supplies private crates through this shared driver.
extern crate rustc_driver;
extern crate rustc_target;
extern crate trust_cg_lower;
extern crate trust_ir;

#[path = "../../../src/aapcs64_hfa.rs"]
mod aapcs64_hfa;
#[path = "../../../src/abi_primitive.rs"]
mod abi_primitive;
#[path = "../../../src/abi_reg_lanes.rs"]
mod abi_reg_lanes;
#[path = "../../../src/cast_abi.rs"]
mod cast_abi;
#[path = "../../../src/indirect_abi.rs"]
mod indirect_abi;
#[path = "../../../src/integer_cast_args.rs"]
mod integer_cast_args;
#[path = "../../../src/scalar_abi_admission.rs"]
mod scalar_abi_admission;
#[path = "../../../src/scalar_pair.rs"]
mod scalar_pair;
