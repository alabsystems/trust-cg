"""Diagnostic/population controls only; these tests grant no native Trust credit."""
import importlib.util
from pathlib import Path
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "check_trust_proof_debt.py"
SPEC = importlib.util.spec_from_file_location("trust_proof_debt", SCRIPT)
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)


class ProofDebtControls(unittest.TestCase):
    def test_positive_requires_exact_complete_declaration_population(self):
        names = sorted(GATE.DECLARATIONS)
        text = "Clean island kernel-checked: 4 declaration(s) registered (" + ", ".join(names) + ")"
        self.assertTrue(GATE.positive_accepted(text, 0, True))
        for changed in [
            text.replace("4 declaration", "0 declaration"),
            text.replace(names[0], names[1]),
            text.replace(names[0], "unrelated"),
            text + "\n" + text,
        ]:
            self.assertFalse(GATE.positive_accepted(changed, 0, True))
        self.assertFalse(GATE.positive_accepted(text, 1, True))
        self.assertFalse(GATE.positive_accepted(text, 0, False))

    def test_actual_publish_audit_refusal_is_named_and_atomic(self):
        text = (
            "error: error: the publish audit refused this batch; nothing was registered\n"
            "  - `" + GATE.THEOREM + "` reaches the incomplete-proof marker `sorryAx`. Finish the proof.\n"
            "  = note: the Clean island was rejected during resolver checking (two-language design E10)"
        )
        self.assertEqual(GATE.debt_refusal(text, 101, False), "publish-audit-sorryAx")
        for changed in [
            text.replace(GATE.THEOREM, "another.theorem"),
            text.replace("sorryAx", "UnknownConstant"),
            text.replace("nothing was registered", "some definitions were registered"),
            text.replace("resolver checking", "code generation"),
        ]:
            self.assertIsNone(GATE.debt_refusal(changed, 101, False))
        for code, exists in [(0, False), (1, False), (-9, False), (101, True)]:
            self.assertIsNone(GATE.debt_refusal(text, code, exists))

    def test_reviewed_strict_island_refusal_is_named(self):
        text = (
            "error: Clean island declaration `" + GATE.THEOREM
            + "` uses explicit `sorry`; strict islands reject all trust debt"
        )
        self.assertEqual(GATE.debt_refusal(text, 101, False), "strict-island-explicit-sorry")
        self.assertIsNone(GATE.debt_refusal(text.replace(GATE.THEOREM, "wrong"), 101, False))

    def test_generic_parser_producer_and_missing_input_errors_do_not_count(self):
        for text in [
            "error: unknown constant " + GATE.THEOREM,
            "error: failed to read explicit sorry source",
            "error: unsupported Type-valued definition",
            "error: " + GATE.THEOREM + " contains sorry but parser failed",
        ]:
            self.assertIsNone(GATE.debt_refusal(text, 101, False))


    def test_decoy_name_cannot_qualify_another_theorems_refusal(self):
        for actual_name in ["another.theorem", GATE.THEOREM + "_suffix"]:
            publish = (
                "note: checking " + GATE.THEOREM + "\n"
                "error: the publish audit refused this batch; nothing was registered\n"
                "  - `" + actual_name + "` reaches the incomplete-proof marker `sorryAx`.\n"
                "  = note: the Clean island was rejected during resolver checking\n"
            )
            strict = (
                "note: checking " + GATE.THEOREM + "\n"
                "error: Clean island declaration `" + actual_name
                + "` uses explicit `sorry`; strict islands reject all trust debt\n"
            )
            self.assertIsNone(GATE.debt_refusal(publish, 101, False))
            self.assertIsNone(GATE.debt_refusal(strict, 101, False))

    def test_publish_evidence_cannot_be_combined_across_errors(self):
        header = "error: the publish audit refused this batch; nothing was registered\n"
        issue = "  - `" + GATE.THEOREM + "` reaches the incomplete-proof marker `sorryAx`.\n"
        phase = "  = note: the Clean island was rejected during resolver checking\n"
        self.assertIsNone(GATE.debt_refusal(
            header + issue + "error: an unrelated parser failure\n" + phase, 101, False))
        self.assertIsNone(GATE.debt_refusal(
            header + phase + "error: another failure\n" + issue, 101, False))

    def test_source_and_help_echoes_are_not_semantic_diagnostics(self):
        named = ("Clean island declaration `" + GATE.THEOREM
                 + "` uses explicit `sorry`; strict islands reject all trust debt")
        for echo in ["  | " + named, "  = help: " + named, "note: " + named]:
            self.assertIsNone(GATE.debt_refusal("error: unrelated failure\n" + echo, 101, False))
        # Both unwrapped Clean and rustc-wrapped canonical publish headers count.
        for prefix in [
            "error: ",
            "error: error: ",
            "error: Clean island batch has no source-local recovery boundary: error: ",
        ]:
            text = (prefix + "the publish audit refused this batch; nothing was registered\n"
                    "  - `" + GATE.THEOREM + "` reaches the incomplete-proof marker `sorryAx`.\n"
                    "  = note: the Clean island was rejected during resolver checking\n")
            self.assertEqual(GATE.debt_refusal(text, 101, False), "publish-audit-sorryAx")

if __name__ == "__main__":
    unittest.main()
