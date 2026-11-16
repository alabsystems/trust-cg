"""Synthetic transcript controls only; no compiler, native or proof credit."""
import importlib.util
from pathlib import Path
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / 'check_trust_clean_units.py'
SPEC = importlib.util.spec_from_file_location('register_refusal_gate', SCRIPT)
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)
THEOREM = 'trust_cg_x86_low3_body'


def refusal(theorem=THEOREM, reason='Type mismatch: expected UInt8, got Bool'):
    return ('error: `' + theorem + '` did not elaborate: ' + reason
            + '\n  --> low3-mutant.lean:5:1\n'
            + '  |\n5 | theorem ' + theorem + ' := rfl\n  | ^^^^^^^\n'
            + '  = note: the Clean island was rejected during resolver checking\n')


class RegisterRefusalTests(unittest.TestCase):
    def accepted(self, text, code=101, artifact=False, theorem=THEOREM):
        return GATE.register_body_refused(text, code, artifact, theorem)

    def test_exact_named_semantic_failures_for_all_three_original_theorems(self):
        for name in sorted(n for n in GATE.REGISTER_DECLARATIONS if n.endswith('_body')):
            for prefix in [
                'error: `' + name + '` did not elaborate: ',
                'error: error: `' + name + '` did not elaborate: ',
                'error: Clean island declaration `' + name + '` failed to elaborate: ',
                'error: Clean island declaration `' + name + '` failed the reference kernel recheck: ',
            ]:
                with self.subTest(name=name, prefix=prefix):
                    self.assertTrue(self.accepted(prefix + 'Type mismatch: expected true, got false\n',
                                                  theorem=name))

    def test_theorem_identity_cannot_come_from_another_error_or_source_echo(self):
        for text in [
            refusal(THEOREM + '_decoy'),
            refusal('prefix_' + THEOREM),
            refusal('other') + '\nerror: `' + THEOREM + '` did not elaborate: unknown constant\n',
            refusal('other') + '\nhelp: expected `' + THEOREM + '` Type mismatch\n',
            'error: unknown constant\n  --> mutant.lean:5:1\n'
                + '5 | theorem ' + THEOREM + ' : Type mismatch := rfl\n',
            'warning: `' + THEOREM + '` did not elaborate: Type mismatch\n',
        ]:
            with self.subTest(text=text):
                self.assertFalse(self.accepted(text))

    def test_type_mismatch_must_belong_to_the_same_primary_semantic_error(self):
        for text in [
            refusal(reason='unknown constant') + '\nerror: Type mismatch\n',
            refusal(reason='unknown constant') + '\nhelp: Type mismatch\n',
            'error: `' + THEOREM + '` did not elaborate: unknown constant\n'
                + '  = note: Type mismatch\n',
            'error: `' + THEOREM + '` did not elaborate: unknown constant\n'
                + '  --> mutant.lean:5:1\n5 | Type mismatch\n',
            'error: Clean island failed to parse: `' + THEOREM + '` Type mismatch\n',
        ]:
            with self.subTest(text=text):
                self.assertFalse(self.accepted(text))

    def test_resources_process_status_and_callable_artifacts_never_count_as_refusal(self):
        for code, artifact in [(0, False), (1, False), (2, False), (-9, False), (101, True)]:
            with self.subTest(code=code, artifact=artifact):
                self.assertFalse(self.accepted(refusal(), code, artifact))
        for resource in ['timeout', 'timed out', 'out of memory', 'resource limit',
                         'panicked', 'internal compiler error']:
            with self.subTest(resource=resource):
                self.assertFalse(self.accepted(refusal(reason='Type mismatch: ' + resource)))

    def test_exact_complete_positive_census_and_artifact_are_required(self):
        names = sorted(GATE.REGISTER_DECLARATIONS)
        def census(items, count=6):
            return ('Clean island kernel-checked: ' + str(count)
                    + ' declaration(s) registered (' + ', '.join(items) + ')\n')
        good = census(names)
        self.assertTrue(GATE.register_source_accepted(good, 0, True))
        for text, code, artifact in [
            (good, 1, True), (good, 0, False), (good + good, 0, True),
            (census(names[:-1], 5), 0, True),
            (census(names[:-1] + [names[0]]), 0, True),
            (census(names[:-1] + ['unrelated']), 0, True),
            (census(names, 2), 0, True),
        ]:
            with self.subTest(text=text, code=code, artifact=artifact):
                self.assertFalse(GATE.register_source_accepted(text, code, artifact))


if __name__ == '__main__':
    unittest.main()
