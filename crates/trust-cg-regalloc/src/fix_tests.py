import os
import re

for filename in ["greedy.rs", "linear_scan.rs"]:
    with open(filename, 'r') as f:
        content = f.read()
    
    # We replace .allocate() with .allocate(&func)
    # This might break if the local variable is named something else, but let's try.
    # We also have scan64.allocate() -> scan64.allocate(&func)
    content = re.sub(r'\.allocate\(\)', '.allocate(&func)', content)
    
    with open(filename, 'w') as f:
        f.write(content)

with open("machine_types.rs", 'r') as f:
    content = f.read()
    content = content.replace("flags: InstFlags::default(),", "tied_operands: Vec::new(),\n            flags: InstFlags::default(),")
with open("machine_types.rs", 'w') as f:
    f.write(content)

