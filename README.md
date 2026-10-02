# InvFinder

InvFinder computes best inductive invariants for fixed bit-vector templates and reduced products, and uses sound auxiliary invariants to strengthen k-induction. Its C++ API represents formulas, models, quantifiers, and solver queries directly with Z3.

## Build and test

Requirements: CMake 3.17+, a C++17 compiler, matching Z3 C++ headers/library, and Boost.Multiprecision headers. Use Z3 4.12.2 for fixed-version experiment runs; Z3 4.13.4 is also supported. Python 3.9+ enables CLI tests and experiment scripts; synthesis requires no Python packages.

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j4
ctest --test-dir build --output-on-failure
```

For a custom Z3 installation, add `-DZ3_ROOT=/path/to/z3` to the configure command. Use headers and the library from the same installation. CMake prints both selected paths. The build uses locally installed dependencies.

For an isolated Z3 4.12.2 installation, the Python wheel provides matching C++ headers and a shared library:

```sh
python3 -m pip install --target build-deps/z3-4.12.2 z3-solver==4.12.2.0
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DZ3_ROOT="$PWD/build-deps/z3-4.12.2/z3"
cmake --build build -j4
ctest --test-dir build --output-on-failure
```

```sh
./build/bestInv --version
./build/bestInv -F examples/counter.smt2 -D interval -M optimal --validate
./build/native_example
```

`--validate` independently checks initiation and consecution with two additional SMT queries, each with a 10-second limit. These checks are outside synthesis time/count statistics; a failed or incomplete validation returns exit code 2.

## Synthesis methods and domains

| Tactic | Algorithm |
| --- | --- |
| `efsolve` | Joint strict bound refinement |
| `bitwise` | Merged bitwise greedy proposals |
| `bounded` | Bitwise greedy with learned boundary limits |
| `optimal` | Bitwise greedy with boundary limits and bounded leap |
| `fixbsrh` | Chaotic iteration with binary-search symbolic abstraction |
| `bilater` | Chaotic iteration with bilateral symbolic abstraction |
| `bitbase` | Per-row bitwise refinement |
| `bsearch` | Merged binary-search refinement |

| Domain | Template rows |
| --- | --- |
| `interval` | Each state variable |
| `zones` | Variables and `x_i - x_j`, for `i < j` |
| `octagon` | Variables and `x_i + x_j`, `x_i - x_j`, for `i < j` |
| `polyhedra` | Octagon rows plus `x_i ± x_j ± x_k`, for `i < j < k` |
| `knownbits` | Each individual bit as a one-bit row |

`octagon-forward` is an alias of `octagon`, and `template-polyhedra` is an alias of `polyhedra`. All template bounds use unsigned comparison. Arithmetic is modular at the row width. For mixed-width rows, operands are zero-extended to the maximum participating width; equal-width sums retain that width. The transition formula retains its own signed/unsigned operators.

The `optimal` tactic starts every refinement with a standard bitwise query. After an UNSAT result it updates the boundary limits and issues at most one bounded-leap query when the boundary underapproximation is nonempty. Failed directions are consumed before the next proposal. With exact solver answers, `bitwise` uses at most `2W` refinement queries and `optimal` at most `4W`, where `W` is the sum of the template-row widths. Reported SMT-call totals also include the initial emptiness check; validation calls are separate.

Quantified synthesis queries enable Z3's model-based quantifier instantiation (`mbqi=true`). With Z3 4.12.2, E-matching is disabled (`ematching=false`) to avoid incomplete-quantifier results on incremental bit-vector queries; other versions retain their default E-matching setting. Solver UNKNOWN results and timeouts remain incomplete results.

`bestInv` defaults to tactic `optimal`, domain `interval`, and a 60-second synthesis budget. `-T -1` disables its deadline; `-T 0` returns an incomplete result without making a solver call. Each invocation selects one tactic. `BESTINV_TRACE=1` enables refinement diagnostics.

`--iterations N` (or `-I N`) caps synthesis iterations. The default is `unlimited`, also written `-1`; a limit of zero returns top without solver calls. Iteration counts follow the definitions in the verification section.

`Synthesis status: good` means the search completed and established bestness. `partial` means synthesis reached its iteration limit. `bad` means it stopped on a timeout, UNKNOWN, or solver failure. In both incomplete cases the reported invariant remains sound, but optimality is not established. Interrupted chaotic-iteration methods report top until convergence. An empty initial set produces `[bottom][bottom]`. Synthesis concerns initialization and induction, independently of the safety property; a best invariant need not prove safety.

## Reduced-product synthesis

`rp_bestInv` integrates ACR (`quantified`) and CARE (`cegis`) for joint synthesis
in products of range templates and flat facts. Products include
`interval+knownbits`, `octagon+knownbits`, `interval+signed+knownbits`, and
`interval+congruence:3`.

```sh
./build/rp_bestInv examples/reduced_product/mutual_interval_bits.smt2 \
  --domain interval+knownbits --method cegis --certify
./build/rp_synth examples/reduced_product/mutual_interval_mod3.rp --method quantified --certify
```

The first example yields `0 <=u x <=u 10 AND bit0(x) = 0`, whereas each component
alone yields TOP. JSON output distinguishes completion, soundness, and independent
bestness certification. Interrupted runs retain a sound invariant. Exit codes are
0 (complete), 3 (incomplete), and 2 (input/validation error).

The native `ReducedProductInvariant` API is in [include/reduced_product.h](include/reduced_product.h);
link target `invfinder_rp`. Its formula can strengthen `k_induction` through the
existing auxiliary-invariant API. See [the reduced-product guide](docs/reduced_products.md)
for options, custom observations, certificate replay, experiments, and proofs.

## Construct formulas directly

[examples/native.cpp](examples/native.cpp) builds a three-bit counter loop with `z3::context`, `z3::expr`, `z3::ult`, and `ctx.bv_val`, then constructs:

```cpp
invfinder::transitionSystem loop(init, transition, property, {x}, {x_next});
invfinder::UBVInvariant engine(loop, "interval");
engine.set_timer(10);
engine.runTactic("optimal");
z3::expr invariant = engine.get_inv_with_var({x});
```

The Z3 context must outlive the system and engine. Use distinct current/next state constants, explicitly bind nondeterministic local values, and construct a new engine for each independent synthesis run. Public headers are in [include/](include/).

`engine.runTactic("optimal", 3)` caps this run at three refinement attempts. The optional second argument defaults to `-1` for unlimited iterations. `engine.iterations` reports the count, and `engine.iteration_limit_reached` identifies a stop caused by this limit.

## CHC inputs

The reader uses Z3's native SMT-LIB parser. It supports `assert` clauses with one positive-arity invariant relation over bit-vector state, and at most one relation occurrence in a conjunctive rule body. Multiple initial, transition, and safety clauses are combined. Nonlinear bit-vector arithmetic is supported; nonlinear CHCs with multiple recursive body atoms are rejected.

Quantified clause-local variables are projected into the transition system; safety locals must be respected universally. Unsupported multi-relation systems, non-BV state, free global parameters, and fixedpoint `rule/query` commands are rejected explicitly. The native API also accepts formulas directly.

## Verification

`kInductor` runs k-induction with an optional auxiliary invariant. To run it without auxiliary synthesis:

```sh
./build/kInductor -F examples/counter.smt2 -K 64 -T 60
```

Select a synthesis tactic and a finite iteration budget to precompute a partial invariant, validate it, and use it throughout verification:

```sh
./build/kInductor -F examples/counter.smt2 --inv-tactic optimal --inv-domain interval --inv-iterations 1 --synthesis-timeout 10 -K 64 -T 60
```

For synthesis with an unlimited iteration budget:

```sh
./build/kInductor -F examples/counter.smt2 --inv-tactic optimal --inv-domain interval --inv-iterations unlimited --synthesis-timeout 10 -K 64 -T 60
```

| Option | Meaning |
| --- | --- |
| `--inv-tactic NAME`, `-M NAME` | Auxiliary synthesis tactic; default `optimal` when synthesis is enabled |
| `--inv-domain DOMAIN`, `-D DOMAIN` | Auxiliary template domain; `none` selects pure k-induction |
| `--inv-iterations N`, `-I N` | Maximum auxiliary synthesis iterations; `-1` or `unlimited` removes this limit |
| `--synthesis-timeout SECONDS` | Auxiliary synthesis time budget; default 10 seconds |
| `-K N` | Maximum k-induction transition depth |
| `-T SECONDS` | Overall verification time budget, including auxiliary synthesis; default 60 seconds |

Explicitly selecting an auxiliary tactic or iteration budget enables synthesis with the interval domain unless a domain is specified. The default iteration budget is unlimited. A finite budget allows synthesis to finish early if it establishes the best invariant before reaching the limit.

Use `--inv-domain none` for pure k-induction without auxiliary options; combining it with an explicit auxiliary tactic or iteration limit is an error. An iteration limit of zero supplies top without making synthesis solver calls.

For top-down tactics, each propose-and-refine attempt counts as one iteration. An `optimal` iteration includes its standard query and the optional bounded leap following a failed standard query; an iteration cap never splits those two queries, although the time budget still applies to each query. For `fixbsrh` and `bilater`, each completed abstraction round counts as one iteration, including the initial-state abstraction and each subsequent transition abstraction. A round may contain several SMT queries; a round interrupted by a timeout does not count. If either method stops before convergence, it supplies top as the sound auxiliary invariant. The initial emptiness check is outside the iteration count.

Iteration and time limits apply independently: `--inv-iterations -1` does not disable either time budget. `--synthesis-timeout -1` removes the synthesis phase's own deadline; the overall `-T` budget still applies. `-T -1` removes the overall deadline. The supplied auxiliary invariant remains sound when synthesis stops early; it may be less precise than the best invariant.

Verification output reports the auxiliary tactic, iteration count and limit, and supplied invariant. Reaching the iteration limit reports partial auxiliary synthesis with stop reason `iteration limit`, then proceeds with verification.

Results distinguish `safe`, `unsafe` (a reachable counterexample), and `unknown`. Exhausting a time or depth budget yields `unknown` unless a result has already been established.

## Benchmarks and experiment scripts

[benchmarks/efmc](benchmarks/efmc) contains 195 EFMC bit-vector CHC benchmarks from the `safe_or_undetermined` subset: 65 inputs at each of 32, 64, and 128 bits. [benchmarks/manifest.json](benchmarks/manifest.json) records their relative paths and SHA-256 hashes.

Script paths are relative to the current working directory:

```sh
# Fast end-to-end smoke run
python3 scripts/run_experiments.py -P build/bestInv -D examples -A interval,octagon -M efsolve,bitwise,bounded,optimal,fixbsrh,bilater -O results/smoke.csv -T 5
python3 scripts/summarize.py results/smoke.csv

# Synthesis over the bundled benchmarks
python3 scripts/run_experiments.py -P build/bestInv -D benchmarks/efmc -A interval -M efsolve,optimal,fixbsrh,bilater -O results/interval.csv -T 60

# Verification with and without one-iteration interval invariants
python3 scripts/run_experiments.py --mode verification -P build/kInductor -D examples -A none,interval -M optimal --inv-iterations 1 -O results/verification.csv -T 10
```

Each CSV has a companion JSON file recording options, the binary hash, linked Z3 version, and input hashes. Incomplete runs are not counted as solved. Summaries report each method's completed set. Use common-instance analysis when comparing speedups across methods. Optional plotting requires `matplotlib`: `python3 scripts/summarize.py results/smoke.csv --plot results/cactus.pdf`.

Synthesis presets select the method/domain combinations for comparisons (`rq1`), bit-width sensitivity (`rq2`), and ablation (`rq3`). Each preset uses every input in the supplied directory; it does not apply a dataset-selection filter. The timeout defaults to 60 seconds per run.

```sh
python3 scripts/run_experiments.py --suite rq1 -P build/bestInv -D benchmarks/efmc -O results/rq1.csv
python3 scripts/summarize.py results/rq1.csv --analysis common --methods efsolve,optimal,fixbsrh,bilater
python3 scripts/run_experiments.py --suite rq2 -P build/bestInv -D benchmarks/efmc -O results/rq2.csv
python3 scripts/summarize.py results/rq2.csv --analysis width --methods bilater,efsolve,optimal
python3 scripts/summarize.py results/rq2.csv --analysis differing-bit --methods bilater,efsolve,optimal > results/differing_bits.csv
python3 scripts/run_experiments.py --suite rq3 -P build/bestInv -D benchmarks/efmc -O results/rq3.csv
python3 scripts/summarize.py results/rq3.csv --analysis common --methods efsolve,bitwise,bounded,optimal
```

Common-instance analysis compares methods only on their intersection of completed inputs and checks that the resulting bounds agree. Width analysis matches the same benchmark across 32-, 64-, and 128-bit inputs and requires completion by every selected method at every width. Both analyses require an explicit `--methods` list so that a missing configuration cannot silently narrow the comparison. The differing-bit metric is `max((lower_i XOR upper_i).bit_length())` across interval rows; zero denotes singleton rows, and bottom has a blank metric. This analysis exports each completed method/input pair, not only the common set. Solver-call totals include the initial emptiness check. These analyses report the results in the supplied CSV, with incomplete runs excluded from comparisons.

## Layout

- `src/invariant.cpp`: single-domain synthesis algorithms and template construction.
- `src/reduced_product.cpp`: ACR, CARE, semantic reduction, and bestness certificates.
- `include/reduced_product.h`: native Z3 reduced-product adapter.
- `docs/`: reduced-product usage and algorithm notes.
- `src/transition_system.cpp`: native-Z3 CHC reader and state validation.
- `src/k_induction.cpp`: bounded k-induction with validated auxiliary invariants.
- `src/*_main.cpp`: command-line programs.
- `tests/`: finite-state invariant oracle, parser equivalence tests, timeout and 128-bit checks, verification regressions, and CLI checks.
- `examples/`, `benchmarks/`, `scripts/`: API example, inputs, and experiment runners.
