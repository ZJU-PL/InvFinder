#!/usr/bin/env python3
"""Exercise the command-line interface, including incomplete results."""
import subprocess
import csv
import os
import re
import sys
import tempfile
from pathlib import Path

bestinv, kinductor, source = sys.argv[1:]
source = Path(source)


def run(executable, *args, ok=True, env=None):
    result = subprocess.run([executable, *map(str, args)], capture_output=True, text=True, timeout=20, env=env)
    if ok:
        assert result.returncode == 0, result.stdout + result.stderr
    else:
        assert result.returncode != 0, result.stdout
    return result.stdout + result.stderr


version = run(bestinv, "--version")
assert version.startswith("InvFinder; Z3 "), version
assert "--validate" in run(bestinv, "--help")
run(bestinv, "-F", source / "examples/counter.smt2", "-T", "nan", ok=False)
run(bestinv, "-F", source / "examples/counter.smt2", "-M", "efsolve,optimal", ok=False)
for method in ("efsolve", "bitwise", "bounded", "optimal", "bitbase", "bsearch", "bilater", "fixbsrh"):
    output = run(bestinv, "-F", source / "examples/counter.smt2", "-M", method, "--validate")
    assert "Synthesis status: good" in output, output
    assert "initiation=unsat, consecution=unsat" in output, output
output = run(bestinv, "-F", source / "examples/counter.smt2", "-T", "0", "--validate")
assert "Synthesis status: bad" in output and "Optimality: not established" in output, output
assert "Result: safe" in run(kinductor, "-F", source / "examples/counter.smt2")
assert "Result: safe" in run(kinductor, "-F", source / "examples/counter.smt2", "-D", "interval")
assert "Result: unknown" in run(kinductor, "-F", source / "examples/counter.smt2", "-T", "0")
run(kinductor, "-F", source / "examples/counter.smt2", "-K", "-1", ok=False)

counter = source / "examples/counter.smt2"
for method in ("efsolve", "bitwise", "bounded", "optimal", "bitbase", "bsearch", "bilater", "fixbsrh"):
    output = run(kinductor, "-F", counter, "--inv-tactic", method, "--inv-iterations", "1")
    assert f"Invariant tactic: {method}\n" in output, output
    assert "Invariant iterations: 1\n" in output, output
    assert "Invariant iteration limit: 1\n" in output and "Result: safe" in output, output
    partial = run(bestinv, "-F", counter, "-M", method, "--iterations", "1", "--validate")
    assert "Iterations: 1\n" in partial and "Synthesis status: partial\n" in partial, partial
    assert "initiation=unsat, consecution=unsat" in partial, partial
for limit in ("-1", "unlimited"):
    output = run(kinductor, "-F", counter, "--inv-tactic", "optimal", "--inv-iterations", limit)
    assert "Invariant iteration limit: unlimited\n" in output and "Auxiliary synthesis: complete" in output, output
for invalid in ("-2", "1.5", "junk", "9223372036854775808"):
    run(kinductor, "-F", counter, "--inv-iterations", invalid, ok=False)
output = run(kinductor, "-F", counter, "-I", "0")
assert "Invariant iterations: 0\n" in output and "Auxiliary synthesis: partial" in output, output
assert "Result: safe" in output and "Auxiliary stop reason: iteration limit" in output, output
run(kinductor, "-F", counter, "--inv-domain", "none", "--inv-tactic", "optimal", ok=False)
run(kinductor, "-F", counter, "--inv-domain", "none", "--inv-iterations", "0", ok=False)
run(kinductor, "-F", counter, "--inv-domain", "interval", "--inv-tactic", "none", ok=False)
assert "Result: safe" in run(kinductor, "-F", counter, "--inv-domain", "interval", "--inv-tactic", "bounded", "-I", "1")

with tempfile.TemporaryDirectory() as tmp:
    leap = Path(tmp) / "bounded_leap.smt2"
    leap.write_text("""(set-logic HORN)
(declare-fun inv ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> (bvule x #x80) (inv x))))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
  (=> (and (inv x) (= y x)) (inv y))))
(assert (forall ((x (_ BitVec 8))) (=> (inv x) (bvule x #x80))))
""")
    partial = run(bestinv, "-F", leap, "-M", "optimal", "--iterations", "1", "--validate")
    assert "Iterations: 1\n" in partial and "SMT(OMT) calls: 3\n" in partial, partial
    assert "Synthesis status: partial\n" in partial, partial
    assert "Invariant: [#x00][#xff]" not in partial, partial
    assert "initiation=unsat, consecution=unsat" in partial, partial

    trace = run(bestinv, "-F", leap, "-M", "optimal", "--validate",
                env={**os.environ, "BESTINV_TRACE": "1"})
    checks = re.findall(r"\[InvFinder:optimal\] (refine|bounded-leap) check=(sat|unsat|unknown)", trace)
    assert checks and ("bounded-leap", "sat") in checks, trace
    for position, check in enumerate(checks):
        if check[0] == "bounded-leap":
            assert position > 0 and checks[position - 1] == ("refine", "unsat"), trace
    rounds = int(re.search(r"^Iterations: (\d+)$", trace, re.MULTILINE).group(1))
    assert rounds == sum(phase == "refine" for phase, _ in checks), trace
    assert len(checks) <= 4 * 8, trace
    assert "Invariant: [#x00][#x80]" in trace, trace

    bad = Path(tmp) / "unsupported.smt2"
    bad.write_text("(declare-fun p (Int) Bool)\n(assert (forall ((x Int)) (=> (= x 0) (p x))))\n")
    run(bestinv, "-F", bad, ok=False)
    results = Path(tmp) / "results.csv"
    run(sys.executable, source / "scripts/run_experiments.py", "-P", kinductor,
        "-D", source / "examples", "-A", "none,interval", "-M", "optimal", "--mode", "verification",
        "--inv-iterations", "0", "-O", results, "--limit", "1", "-T", "5")
    with results.open(newline="") as stream:
        rows = list(csv.DictReader(stream))
    assert len(rows) == 2 and all(row["Result"] == "safe" for row in rows), rows
    assisted = next(row for row in rows if row["Domain"] == "interval")
    assert assisted["Iteration Limit"] == "0" and assisted["Iterations"] == "0", assisted
    assert assisted["Auxiliary Status"] == "partial", assisted
print("CLI checks passed")
