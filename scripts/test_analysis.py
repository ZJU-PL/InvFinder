#!/usr/bin/env python3
"""Checks for common sets and exact bound metrics."""
import unittest
import summarize


def row(file, method, *, complete=True, seconds=2, calls=10, info='[#x00][#x0a]'):
    return {'File': file, 'Method': method, 'Mode': 'synthesis', 'Domain': 'interval',
            'Iteration Limit': 'unlimited', 'Bad Solve': '0' if complete else '1',
            'Time Cost': str(seconds), 'Calls': str(calls), 'Info': info}


class AnalysisTests(unittest.TestCase):
    def test_common_counts_and_excludes_timeout(self):
        rows = [row('a', 'm1', seconds=3, calls=6), row('a', 'm2', seconds=1, calls=4),
                row('b', 'm1', seconds=30), row('b', 'm2', complete=False, info='TIMEOUT')]
        header, output = summarize.summarize(rows, 'common', ['m1', 'm2'])
        records = [dict(zip(header, r)) for r in output]
        self.assertEqual([r['common_completed'] for r in records], [1, 1])
        self.assertEqual(records[0]['completed_seconds'], '3.000000')
        self.assertEqual(records[0]['completed_calls'], 6)
        self.assertEqual(records[0]['milliseconds_per_call'], '500.000000')
        _, missing = summarize.summarize(rows, 'common', ['m1', 'absent'])
        self.assertTrue(all(r[4] == 0 for r in missing))

    def test_mismatched_bounds_and_duplicates_rejected(self):
        with self.assertRaisesRegex(ValueError, 'disagree'):
            summarize.summarize([row('a', 'm1'), row('a', 'm2', info='[#x00][#x09]')], 'common', ['m1', 'm2'])
        with self.assertRaisesRegex(ValueError, 'explicit --methods'):
            summarize.summarize([row('a', 'm1')], 'common')
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            summarize.summarize([row('a', 'm1'), row('a', 'm1')])

    def test_width_intersection_all_methods_and_widths(self):
        rows = []
        for case in ['inc', 'other']:
            for width in [32, 64, 128]:
                for method in ['m1', 'm2']:
                    file = f'/data/{width}bit/LIA/group/{case}.sl_{width}bits_unsigned.sl_{width}bits_unsigned.smt2'
                    good = not (case == 'other' and width == 128 and method == 'm2')
                    rows.append(row(file, method, complete=good, seconds=width))
        header, output = summarize.summarize(rows, 'width', ['m1', 'm2'])
        records = [dict(zip(header, r)) for r in output]
        self.assertEqual(len(records), 6)
        self.assertTrue(all(r['common_benchmarks'] == 1 for r in records))
        self.assertEqual([r['completed_seconds'] for r in records[:3]], ['32.000000', '64.000000', '128.000000'])
        rows = [r for r in rows if '/128bit/' not in r['File']]
        _, output = summarize.summarize(rows, 'width', ['m1', 'm2'])
        self.assertTrue(all(r[4] == 0 for r in output))
        w, identity = summarize.width_identity('/data/32bit/LIA/sum32.sl_32bits_unsigned.sl_32bits_unsigned.smt2')
        self.assertEqual(w, 32)
        self.assertIn('sum32', identity)
        with self.assertRaisesRegex(ValueError, 'expected one width'):
            summarize.width_identity('counter.smt2')

    def test_128_bit_and_singleton_and_bottom(self):
        self.assertEqual(summarize.differing_bit('[#x00000000000000000000000000000000][#x80000000000000000000000000000000]'), 128)
        self.assertEqual(summarize.differing_bit('[#b00101][#b00101]'), 0)
        self.assertEqual(summarize.differing_bit('[(_ bv0 128)][(_ bv8 128)]'), 4)
        self.assertIsNone(summarize.differing_bit('[bottom][bottom]'))
        rows = [row('a', 'm1', info='[bottom][bottom]'), row('b', 'm1', complete=False, info='TIMEOUT')]
        header, output = summarize.summarize(rows, 'differing-bit')
        self.assertEqual(len(output), 1)
        result = dict(zip(header, output[0]))
        self.assertEqual(result['metric_status'], 'bottom')
        self.assertEqual(result['differing_bit'], '')


if __name__ == '__main__':
    unittest.main()
