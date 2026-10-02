#!/usr/bin/env python3
"""Exercise the integrated CHC CLI and replay obligations through the linked Z3."""
import ctypes as C
import json
from pathlib import Path
import subprocess
import sys
import tempfile

chc, standalone, root, library = map(Path, sys.argv[1:])
example = root / 'examples/reduced_product/mutual_interval_bits.smt2'


def invoke(binary, arguments, code=0):
    process = subprocess.run([str(binary), *map(str, arguments)], text=True,
                             capture_output=True, timeout=30)
    assert process.returncode == code, (arguments, process.returncode, process.stdout, process.stderr)
    return process.stdout


for binary in (chc, standalone):
    assert 'Z3' in invoke(binary, ['--version'])
    assert 'quantified|cegis' in invoke(binary, ['--help'])
    for arguments in (['--timeout', '1oops'], ['--timeout', 'nan'], ['--max-queries', '3x'],
                      ['--max-candidates', '-2'], ['--method', 'invalid'], ['--timeout']):
        path = example if binary == chc else root / 'examples/reduced_product/mutual_interval_bits.rp'
        invoke(binary, [path, *arguments], 2)

with tempfile.TemporaryDirectory() as directory:
    prefix = Path(directory) / 'certificate'
    solver = C.CDLL(str(library))
    for name, args, result in (
        ('Z3_mk_config', [], C.c_void_p), ('Z3_del_config', [C.c_void_p], None),
        ('Z3_mk_context', [C.c_void_p], C.c_void_p), ('Z3_del_context', [C.c_void_p], None),
        ('Z3_eval_smtlib2_string', [C.c_void_p, C.c_char_p], C.c_char_p),
    ):
        function = getattr(solver, name); function.argtypes = args; function.restype = result
    for method in ('quantified', 'cegis'):
        data = json.loads(invoke(chc, ['-F', example, '-D', 'interval+knownbits', '-M', method,
                                      '--certify', '--dump', prefix]))
        assert data['complete'] and data['sound'] and data['bestness_certified'], data
        assert data['ranges'][0]['lower'] == '0' and data['ranges'][0]['upper'] == '10', data
        assert data['flats'][0]['enabled'] and data['flats'][0]['constant'] == '0', data
        for suffix in ('init', 'step', 'best'):
            cfg = solver.Z3_mk_config(); ctx = solver.Z3_mk_context(cfg); solver.Z3_del_config(cfg)
            try:
                replay = solver.Z3_eval_smtlib2_string(ctx, Path(str(prefix) + f'.{suffix}.smt2').read_bytes())
                assert replay.decode().strip() == 'unsat', (suffix, replay)
            finally:
                solver.Z3_del_context(ctx)
        replay = subprocess.run([sys.executable, str(root / 'scripts/replay_obligations.py'),
                                 '--library', str(library),
                                 *[str(prefix) + f'.{suffix}.smt2' for suffix in ('init', 'step', 'best')]],
                                text=True, capture_output=True, timeout=30)
        assert replay.returncode == 0, (replay.stdout, replay.stderr)
        data = json.loads(invoke(chc, [example, '--method', method, '--max-queries', '0', '--dump', prefix], 3))
        assert not data['complete'] and data['sound'] and data['stats']['total_calls'] == 0, data
        assert not Path(str(prefix) + '.best.smt2').exists(), 'Stale bestness obligation'
    for domain in ('', 'interval+', 'interval++knownbits', 'interval+interval', 'congruence:1', 'congruence:16'):
        invoke(chc, [example, '--domain', domain], 2)
    for flags in (['--no-reduction'], ['--no-promotion'], ['--range-first'], ['--max-candidates', '0']):
        data = json.loads(invoke(chc, [example, *flags], 3 if flags[0] == '--max-candidates' else 0))
        assert data['sound'], data
print('PASS: RP CLI options, CHC results, interruption reporting, and obligation replay')
with tempfile.TemporaryDirectory() as directory:
    output = Path(directory) / 'experiment.csv'
    process = subprocess.run([sys.executable, str(root / 'scripts/run_experiments.py'),
                              '--mode', 'reduced-product', '-P', str(chc),
                              '-D', str(example.parent), '-O', str(output), '--certify', '-T', '10'],
                             text=True, capture_output=True, timeout=30)
    assert process.returncode == 0, (process.stdout, process.stderr)
    import csv
    rows = list(csv.DictReader(output.open()))
    assert len(rows) == 2 and all(r['Result'] == 'complete' for r in rows), rows
    assert all(json.loads(r['Info'])['bestness_certified'] for r in rows), rows
    assert json.loads(output.with_suffix('.csv.json').read_text())['binary_sha256']
    process = subprocess.run([sys.executable, str(root / 'scripts/summarize.py'), str(output),
                              '--analysis', 'common', '--methods', 'quantified,cegis'],
                             text=True, capture_output=True, timeout=10)
    assert process.returncode == 0, (process.stdout, process.stderr)
print('PASS: reduced-product experiment runner and common-instance summary')
