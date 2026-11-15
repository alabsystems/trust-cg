"""Apply (or revert) env-guarded fails-before mutations of the slice-6 checks.

Temporary: the mutated file is never committed. Each mutation disables ONE
slice-6 check when TCG_S6_MUTANT names it, so one build serves every run.
"""
import shutil
import sys

SRC = ('~/trust-cg/.claude/worktrees/agent-a5088c5df59865bdd/'
       'crates/trust-cg-verify/src/x86_source_bound_body.rs')
BACKUP = ('<scratch>
          '03d2cfdb-f305-414e-850d-d6c2ce00de82/scratchpad/slice6/'
          'x86_source_bound_body.rs.orig')

if sys.argv[1:] == ['revert']:
    shutil.copyfile(BACKUP, SRC)
    print('reverted')
    sys.exit(0)

shutil.copyfile(SRC, BACKUP)
s = open(SRC).read()


def rep(a, b):
    global s
    assert s.count(a) == 1, (a[:90], s.count(a))
    s = s.replace(a, b)


MUT = 'std::env::var("TCG_S6_MUTANT").ok().as_deref() == Some'

# 1. flags cross a block boundary
rep("""            if matches!(flags, Flags::Compare { .. } | Flags::Test { .. }) {
                flags = Flags::Unmodelled;
            }""", """            if matches!(flags, Flags::Compare { .. } | Flags::Test { .. })
                && !(%s("flagblock"))
            {
                flags = Flags::Unmodelled;
            }""" % MUT)

# 2. a laid-out block no path reaches
rep("""        .filter(|block| !visited.contains(*block))
        .min()
    {""", """        .filter(|block| !visited.contains(*block))
        .min()
        && !(%s("unreached"))
    {""" % MUT)

# 3. the machine's jcc literals (M_P) dropped from the claim
rep("""            let holds = flags.condition(cc, row.ordinal, inst.opcode)?;
            literals.push(""", """            let holds = flags.condition(cc, row.ordinal, inst.opcode)?;
            if !(%s("nomp")) { literals.push(""" % MUT)
rep("""                holds.not_expr()
            });
            bound_rows.push(row.ordinal);
            continue;""", """                holds.not_expr()
            }); }
            bound_rows.push(row.ordinal);
            continue;""")

# 4. an ALU flag writer leaves the compare's flags in place
rep("""        if writes_unmodelled_flags(inst.opcode) {
            flags = Flags::Unmodelled;
        }""", """        if writes_unmodelled_flags(inst.opcode) && !(%s("clobber")) {
            flags = Flags::Unmodelled;
        }""" % MUT)

# 5. a call leaves the compare's flags in place
rep("""                    flags = Flags::Undefined;
                    calls.push(WalkedCall {""", """                    if !(%s("callflags")) {
                        flags = Flags::Undefined;
                    }
                    calls.push(WalkedCall {""" % MUT)

# 6. a ret/ud2 where the source path continues
rep("""                (X86Opcode::Ret | X86Opcode::Ud2, _) => {
                    if let Some(next) = next {""", """                (X86Opcode::Ret | X86Opcode::Ud2, _) => {
                    if let Some(next) = next.filter(|_| !(%s("retud2"))) {""" % MUT)

# 7. a jcc whose fallthrough also reaches its target
rep("""                        if also {
                            return Err(unsupported(X86BodyUnsupported::MachineRow {""",
    """                        if also && !(%s("also")) {
                            return Err(unsupported(X86BodyUnsupported::MachineRow {""" % MUT)

open(SRC, 'w').write(s)
print('mutated')
