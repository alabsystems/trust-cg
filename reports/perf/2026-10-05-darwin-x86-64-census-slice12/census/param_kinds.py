import collections, re, sys
c = collections.Counter()
for line in open(sys.argv[1]):
    r = line.rstrip("\n").split("\t")
    for header, body in re.findall(r"h(\d+)\[(.*?)\](?= h|$)", r[10] if len(r) > 10 else ""):
        params = re.search(r"params=\(([^)]*)\)", body).group(1)
        kinds = set(params.split(",")) if params else set()
        if not kinds:
            c["none"] += 1
        elif "I128" in kinds:
            c["with I128"] += 1
        elif kinds <= {"I64"}:
            c["I64 only"] += 1
        else:
            c["with a narrower one"] += 1
print(dict(c))
