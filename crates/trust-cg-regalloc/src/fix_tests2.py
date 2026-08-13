import re

with open("greedy.rs", "r") as f:
    content = f.read()

content = content.replace("let mut _func = make_test_func(20);", "let mut func = make_test_func(20);")
content = content.replace("let mut _func = make_test_func(30);", "let mut func = make_test_func(30);")

with open("greedy.rs", "w") as f:
    f.write(content)

with open("linear_scan.rs", "r") as f:
    content = f.read()

content = content.replace(".try_alloc_free_reg(1, RegClass::Gpr64)", ".try_alloc_free_reg(1, RegClass::Gpr64, None)")

with open("linear_scan.rs", "w") as f:
    f.write(content)

