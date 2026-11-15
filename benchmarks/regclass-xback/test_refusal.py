#!/usr/bin/env python3
# Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
"""Diagnostic-classification contracts, not executions of a Trust backend."""

import json
import unittest

from refusal import MAX_BYTES, is_abi_refusal


def diagnostic(message, level="error", **extra):
    return {"$message_type": "diagnostic", "message": message, "level": level,
            "code": None, "children": [], **extra}


def encoded(*records):
    return b"\n".join(json.dumps(record).encode() for record in records) + b"\n"


class RefusalContract(unittest.TestCase):
    def test_explicit_normal_refusals(self):
        for tag in ["ARG", "RET"]:
            error = diagnostic(f"bridge could not lower input: [TCG-{tag}-ABI] disagreement")
            for records in [(error,), (error, diagnostic("aborting due to 1 previous error")),
                            (diagnostic("context", "warning"), error)]:
                with self.subTest(tag=tag, records=records):
                    self.assertTrue(is_abi_refusal(1, encoded(*records)))

    def test_abnormal_status_never_declines(self):
        data = encoded(diagnostic("[TCG-ARG-ABI] mismatch"))
        for status in [-9, 0, 2, 101, 124, 125, 126, 127, 132, 134, 137, 139]:
            with self.subTest(status=status):
                self.assertFalse(is_abi_refusal(status, data))

    def test_unrelated_errors_are_not_abi_refusals(self):
        good = diagnostic("[TCG-ARG-ABI] mismatch")
        for bad in [diagnostic("could not load backend"), diagnostic("internal compiler error"),
                    diagnostic("[TCG-ARG-ABI] [TCG-UNSUPPORTED] incomplete"),
                    diagnostic("[TCG-ARG-ABI] type error", code={"code": "E0308"}),
                    diagnostic("[TCG-ARG-ABI] context", children=[diagnostic("other error")]),
                    diagnostic("aborting due to 2 previous errors")]:
            with self.subTest(bad=bad):
                self.assertFalse(is_abi_refusal(1, encoded(good, bad)))
        self.assertFalse(is_abi_refusal(1, encoded(diagnostic("[TCG-ARG-ABI] context", "note"))))

    def test_malformed_and_oversized_transcripts_refuse(self):
        good = encoded(diagnostic("[TCG-ARG-ABI] mismatch"))
        for data in [b"", b"\xff", b"not JSON", b"{}", b"[]", b"null", b"\n" + good,
                     good + b"panicked at: compiler failure\n", b" " * (MAX_BYTES + 1),
                     good.replace(b'"level": "error"', b'"level": "error", "level": "error"'),
                     encoded(diagnostic("[TCG-ARG-ABI] mismatch", children=None)),
                     good + encoded(diagnostic("aborting due to 1 previous error")) + good]:
            with self.subTest(size=len(data)):
                self.assertFalse(is_abi_refusal(1, data))


if __name__ == "__main__":
    unittest.main()
