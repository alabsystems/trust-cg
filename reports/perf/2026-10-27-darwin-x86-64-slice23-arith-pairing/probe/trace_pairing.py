#!/usr/bin/env python3
"""Temporary (never committed): eprintln traces in pair_arithmetic under S23_TRACE_PAIRING.
Restore with `git -C <wt> checkout crates/trust-cg-verify/src/x86_source_bound_body.rs`."""
import sys
p = sys.argv[1] + '/crates/trust-cg-verify/src/x86_source_bound_body.rs'
t = open(p).read()
T = 'std::env::var_os("S23_TRACE_PAIRING").is_some()'
def rep(old, new):
    global t
    assert t.count(old) == 1, old
    t = t.replace(old, new)
rep('''        let [(unit, key, a, b)] = lowered.as_slice() else {
            continue;
        };''', '''        if %s { eprintln!("S23T row stamp={:?} key={:?} results={:?} lowered={}", row.stamp, row.key, row.results.iter().map(|(n, _)| n).collect::<Vec<_>>(), lowered.len()); }
        let [(unit, key, a, b)] = lowered.as_slice() else {
            continue;
        };''' % T)
rep('''                .any(|operand| closed_term(operand, defined, &mut closed))
        {
            continue;
        }''', '''                .any(|operand| closed_term(operand, defined, &mut closed))
        {
            if %s { eprintln!("S23T   skip: admits/closed a={a} b={b} c={c} d={d}"); }
            continue;
        }''' % T)
rep('''        if !own {
            continue;
        }''', '''        if !own {
            if %s { eprintln!("S23T   skip: not own; transcribed={transcribed}; defs={:?}", row.results.iter().map(|(n, _)| defined.get(n).map(|e| e.to_string())).collect::<Vec<_>>()); }
            continue;
        }''' % T)
rep('''        if spelled_alike(&paired, &transcribed, ordered) {
            continue;
        }''', '''        if spelled_alike(&paired, &transcribed, ordered) {
            if %s { eprintln!("S23T   skip: spelled alike paired={paired} transcribed={transcribed}"); }
            continue;
        }
        if %s { eprintln!("S23T   PAIRED a={a} b={b} c={c} d={d}"); }''' % (T, T))
open(p, 'w').write(t)
print("traced")
