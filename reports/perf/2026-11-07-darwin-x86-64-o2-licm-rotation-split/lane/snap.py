"""snap.py <dump-dir> <snap-dir> <stop-file>: copy every new version of every file in dump-dir
into snap-dir as <name>.<n>.<sha12> (n = order first seen), until stop-file exists, then one
last sweep. A later codegen attempt overwrites the same dump names; this keeps each version."""
import hashlib, os, sys, time, shutil
src, dst, stop = sys.argv[1], sys.argv[2], sys.argv[3]
os.makedirs(dst, exist_ok=True)
seen = {}; order = 0
def sweep():
    global order
    try: names = sorted(os.listdir(src))
    except FileNotFoundError: return
    for n in names:
        p = os.path.join(src, n)
        try: b = open(p, 'rb').read()
        except OSError: continue
        h = hashlib.sha256(b).hexdigest()[:12]
        if (n, h) in seen: continue
        order += 1; seen[(n, h)] = order
        open(os.path.join(dst, f'{n}.{order:04d}.{h}'), 'wb').write(b)
        print(f'{time.strftime("%H:%M:%S")} {order:04d} {n} {h} {len(b)}', flush=True)
while not os.path.exists(stop):
    sweep(); time.sleep(0.1)
sweep()
