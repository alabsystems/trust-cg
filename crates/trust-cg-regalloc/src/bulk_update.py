import os
import re

files = [
    "machine_types.rs",
    "x86_adapter.rs",
    "call_clobber.rs",
    "coalesce.rs",
    "spill_slot_reuse.rs",
    "greedy.rs",
    "lib.rs",
    "liveness.rs",
    "spill.rs",
    "remat.rs",
    "post_ra_opt.rs",
    "post_ra_coalesce.rs",
    "phi_elim.rs",
    "split.rs"
]

for filename in files:
    if not os.path.exists(filename):
        continue
    with open(filename, 'r') as f:
        content = f.read()
    
    # Add tied_operands: Vec::new() to literals.
    # We look for "flags:" since it's the last field in most cases.
    new_content = content.replace("flags:", "tied_operands: Vec::new(),\n            flags:")
    
    # Also handle MachInst { ... } and RegAllocInst { ... }
    # if flags: is missing or formatted differently.
    
    with open(filename, 'w') as f:
        f.write(new_content)

