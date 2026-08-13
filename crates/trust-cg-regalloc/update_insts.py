import os
import re

def update_file(filepath):
    with open(filepath, 'r') as f:
        content = f.read()

    # Just search for `flags: ` and append `tied_operands: vec![],` on the next line
    # Only if it isn't already there.
    # We can match `flags: (.*?)(,?)(\r?\n)`
    # Wait, what if there's no comma? We can add one.
    
    # Let's use a function for re.sub to check if tied_operands is already next
    def repl(m):
        flag_expr = m.group(1)
        newline = m.group(3)
        indent = m.group(4)
        # return the matched flags + tied_operands
        return f"flags: {flag_expr},{newline}{indent}tied_operands: vec![],{newline}"

    # We match the indentation of the next line or current line to make it look nice.
    # Actually, easier to capture the indentation of the `flags:` line.
    
    pattern = re.compile(r'^([ \t]*)flags:\s*(.*?)(,?)(\r?\n)', re.MULTILINE)
    
    def repl_with_indent(m):
        indent = m.group(1)
        expr = m.group(2)
        newline = m.group(4)
        return f"{indent}flags: {expr},{newline}{indent}tied_operands: vec![],{newline}"
        
    new_content = pattern.sub(repl_with_indent, content)
    
    # But wait, in `machine_types.rs`, `pub flags: InstFlags` is matched!
    # Let's filter out `pub flags: InstFlags,`
    if "pub flags:" in new_content:
        new_content = new_content.replace("    pub flags: InstFlags,\n    tied_operands: vec![],\n", "    pub flags: InstFlags,\n")
    
    # Handle the duplicate addition if already run
    new_content = re.sub(r'([ \t]*)tied_operands: vec!\[\],\r?\n([ \t]*)tied_operands: vec!\[\],\r?\n', r'\1tied_operands: vec![],\n', new_content)
    
    # We might have also messed up the struct definition in machine_types.rs
    # `pub flags: InstFlags,\n    pub tied_operands: Vec<(u32, u32)>`
    # Let's just fix `machine_types.rs` manually after the script.
    
    if new_content != content:
        with open(filepath, 'w') as f:
            f.write(new_content)
        print(f"Updated {filepath}")

for root, _, files in os.walk('trust-cg/crates/trust-cg-regalloc'):
    for file in files:
        if file.endswith('.rs'):
            update_file(os.path.join(root, file))
