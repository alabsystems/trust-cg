#!/usr/bin/env python3
"""Temporary (never committed): trace_pairing.py plus, in spelled_alike, the full-context
answer, its time, and the cone. Restore the file with git checkout afterwards."""
import subprocess, sys
root = sys.argv[1]
subprocess.check_call([sys.executable, __file__.replace('trace_pairing2', 'trace_pairing'), root])
p = root + '/crates/trust-cg-verify/src/x86_source_bound_body.rs'
t = open(p).read()
old = '''    matches!(
        normal::spelled(&cone, &claim, normal::Groups::CANONICAL),
        normal::Normal::Emptied
    )
}'''
new = '''    let local = matches!(
        normal::spelled(&cone, &claim, normal::Groups::CANONICAL),
        normal::Normal::Emptied
    );
    if std::env::var_os("S23_TRACE_PAIRING").is_some() && x != y {
        let started = std::time::Instant::now();
        let full = normal::spelled(ordered, &claim, normal::Groups::CANONICAL);
        let ms = started.elapsed().as_millis();
        let full_alike = matches!(full, normal::Normal::Emptied);
        eprintln!("S23T   alike local={local} full={full_alike} full_ms={ms} cone={} ordered={}", cone.len(), ordered.len());
        if let normal::Normal::Spelled((kept, stated)) = &full {
            let s = stated.to_string();
            eprintln!("S23T     full stated[..400]={} kept={}", &s[..s.len().min(400)], kept.len());
        }
        if std::env::var_os("S23_TRACE_CONE").is_some() {
            for (name, expr) in &cone {
                let s = expr.to_string();
                eprintln!("S23T     cone {name} := {}", &s[..s.len().min(300)]);
            }
            if let normal::Normal::Spelled((kept, stated)) = normal::spelled(&cone, &claim, normal::Groups::CANONICAL) {
                eprintln!("S23T     cone spelled kept={} stated={}", kept.len(), stated);
            }
        }
    }
    local
}'''
assert t.count(old) == 1
t = t.replace(old, new)
open(p, 'w').write(t)
print("traced2")
