// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
// Authored ordinary Trust frontend fixture; not an executed frontend result.
// A qualification must compile this source through the actual Trust backend,
// retain its emitted LIR/machine/bytes and compare all output/canary bytes.
// Diagnostic query acceptance does not prove the caller-memory premise or
// permit proof-required publication. No callback/call support is implied.
#![no_std]

#[unsafe(no_mangle)]
pub extern "C" fn output_memory_writer(
    output: &mut [u64; 5],
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
) {
    output[0] = a;
    output[1] = b;
    output[2] = c;
    output[3] = d;
    output[4] = e;
}
