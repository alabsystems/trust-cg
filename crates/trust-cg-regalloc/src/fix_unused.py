import re

with open("greedy.rs", "r") as f:
    content = f.read()

content = content.replace("let mut func = make_test_func(20);", "let mut _func = make_test_func(20);")
content = content.replace("let mut func = make_test_func(30);", "let mut _func = make_test_func(30);")
content = content.replace(".try_assign(vreg, func)", ".try_assign(vreg, Some(func))")

with open("greedy.rs", "w") as f:
    f.write(content)

