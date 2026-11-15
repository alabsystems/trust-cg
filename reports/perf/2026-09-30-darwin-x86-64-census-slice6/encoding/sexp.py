"""Tiny SMT-LIB s-expression parser/printer and path-theorem transformers."""
import re

TOKEN = re.compile(r"\(|\)|[^\s()]+")


def parse_all(text):
    tokens = TOKEN.findall(text)
    pos = 0
    out = []

    def parse():
        nonlocal pos
        tok = tokens[pos]
        pos += 1
        if tok == "(":
            items = []
            while tokens[pos] != ")":
                items.append(parse())
            pos += 1
            return items
        return tok

    while pos < len(tokens):
        out.append(parse())
    return out


def show(e):
    if isinstance(e, list):
        return "(" + " ".join(show(x) for x in e) + ")"
    return e


def conjuncts(e):
    out = []
    while isinstance(e, list) and e and e[0] == "and" and len(e) == 3:
        out.append(e[1])
        e = e[2]
    out.append(e)
    return out


def nest_and(terms):
    acc = terms[-1]
    for t in reversed(terms[:-1]):
        acc = ["and", t, acc]
    return acc


def split(text):
    """(header commands, definitions, goal) of a body theorem query."""
    cmds = parse_all(text)
    header = [c for c in cmds if not (isinstance(c, list) and c[0] in ("assert", "check-sat", "exit"))]
    assertion = next(c for c in cmds if isinstance(c, list) and c[0] == "assert")[1]
    terms = conjuncts(assertion)
    negated = terms[-1]
    assert negated[0] == "not"
    eq = negated[1]
    assert eq[0] == "=" and eq[1] == "true", show(eq)[:200]
    return header, terms[:-1], eq[2]


def render(header, definitions, goal):
    body = nest_and(definitions + [["not", ["=", "true", goal]]])
    return "\n".join(show(c) for c in header) + "\n" + show(["assert", body]) + "\n(check-sat)\n(exit)\n"


def paths(goal):
    """[(C, X)] of a path-form goal."""
    out = []
    for p in conjuncts(goal):
        assert p[0] == "or" and p[1][0] == "not", show(p)[:200]
        out.append((p[1][1], p[2]))
    return out
