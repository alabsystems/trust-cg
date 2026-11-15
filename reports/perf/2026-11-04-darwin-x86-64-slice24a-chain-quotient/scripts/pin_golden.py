"""Pin SLICE_TWENTY_FOUR_SNAPSHOT_SHA256 to the SHA-256 of the golden file as
written (the golden's diff is reviewed before it is committed)."""
import hashlib, pathlib, re, sys
wt = pathlib.Path(sys.argv[1])
golden = wt / "crates/trust-cg-verify/tests/fixtures/x86_source_bound_body/slice24_snapshots.smt2"
digest = hashlib.sha256(golden.read_bytes()).hexdigest()
src = wt / "crates/trust-cg-verify/src/x86_source_bound_body_slice24_tests.rs"
text = src.read_text()
new, n = re.subn(r'(const SLICE_TWENTY_FOUR_SNAPSHOT_SHA256: &str =\n    ")[0-9a-f]{64}(";)', r"\g<1>" + digest + r"\g<2>", text)
assert n == 1, "the pin is not where it is expected"
if new != text:
    src.write_text(new)
print("SLICE_TWENTY_FOUR_SNAPSHOT_SHA256", digest, "changed" if new != text else "unchanged")
