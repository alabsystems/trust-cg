#!/bin/sh
# Cargo target runner: the native link tests must find LLD and gold. The
# requirement reaches only the test executable, never the Trust compiler,
# which refuses TCG_* variables as untracked compiler controls.
export TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1
exec "$@"
