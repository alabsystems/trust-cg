"""Transcript-parser regressions; these do not run Trust or grant native credit."""
import importlib.util
from pathlib import Path
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / 'check_trust_clean_units.py'
SPEC = importlib.util.spec_from_file_location('trust_clean_register_population', SCRIPT)
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)


def transcript(names, summary):
    return ''.join('test x86_64::encode::register_bits_tests::' + name + ' ... ok\n'
                   for name in names) + summary + '\n'


class RegisterPopulationTests(unittest.TestCase):
    def test_zero_tests_cannot_pass_even_with_printed_names(self):
        with self.assertRaises(SystemExit):
            GATE.require_register_controls(transcript(GATE.REGISTER_CONTROLS,
                'test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 900 filtered out;'))

    def test_failures_ignores_missing_and_multiple_summaries_are_rejected(self):
        good = 'test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 900 filtered out;'
        for text in [
            transcript(GATE.REGISTER_CONTROLS, good.replace('0 ignored', '1 ignored')),
            transcript(GATE.REGISTER_CONTROLS, good.replace('0 failed', '1 failed')),
            transcript(GATE.REGISTER_CONTROLS[:-1], good),
            transcript(GATE.REGISTER_CONTROLS, good + '\n' + good),
            transcript(GATE.REGISTER_CONTROLS, good.replace('ok.', 'FAILED.')),
        ]:
            with self.subTest(text=text), self.assertRaises(SystemExit):
                GATE.require_register_controls(text)

    def test_unrelated_tests_cannot_replace_actual_encoder_callers(self):
        text = transcript(['unrelated_' + name for name in GATE.REGISTER_CONTROLS],
            'test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 900 filtered out;')
        with self.assertRaises(SystemExit):
            GATE.require_register_controls(text)

    def test_exact_population_retains_intentional_filter_count(self):
        result = GATE.require_register_controls(transcript(GATE.REGISTER_CONTROLS,
            'test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 900 filtered out;'))
        self.assertEqual(result['filtered_out'], 900)
        self.assertEqual(result['required'], list(GATE.REGISTER_CONTROLS))


if __name__ == '__main__':
    unittest.main()
