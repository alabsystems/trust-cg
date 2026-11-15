# Focused pipeline watch qualification

This independent test workspace compiles the production pipeline identity and
watch-plan sources directly by path. It avoids compiling unrelated CG/TY
libraries or acquiring their Git histories to test the watch algorithm. Its
`pipeline_source_identity` test target is the same source target as the parent
package, with registry-only SHA256 and temporary-file dependencies.

For an actual native content observation, select `CG_WATCH_PLAN_INPUT` as an
absolute path to an original jit-matrix build script's complete stdout watch
inventory and `CG_WATCH_PLAN_ROOT` as that script's original package directory.
Both are explicit data selections. Relative original declarations are joined
to that original directory without canonicalization. Unknown lines, incomplete
or oversized data, empty input and missing paired inputs refuse. No prior
snapshot, output receipt, compiler executable or stored verdict is read.

The fixture's build script executes the production std-only compactor, emits
the resulting real paths and writes original/compact counts to its own
`OUT_DIR/watch-counts.txt`. Native Targo independently observes those paths and
decides cache eligibility. Use one owned target/build directory outside all
watched trees, an explicit unverified lane and the same genuine selected compiler.
Enroll a newly discovered watch set first: the initial execution cannot seal
external paths absent from its original window. A subsequent dirty execution
can capture them under the recorded full window. After a non-null snapshot is
published, run two identical builds. Retain the current native fingerprint's non-null
snapshot, bounds/counts and the second build's freshness observations. A null
snapshot remains a refusal, never a zero-byte or successful observation.

These controls qualify declaration compaction and native observation of the
selected real readset. They do not qualify a different full-CG dependency graph,
an installed SDK, a soundness attestation, an executable-buffer proof or release.
