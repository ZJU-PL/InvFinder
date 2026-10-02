# Reduced-product synthesis

InvFinder provides ACR (`quantified`) and CARE (`cegis`) for joint best inductive
invariants in products of fixed BV ranges and flat constant facts. Build normally
with matching Z3 headers/library and Boost.Multiprecision headers.

## Run

```sh
./build/rp_bestInv examples/reduced_product/mutual_interval_bits.smt2 \
  --domain interval+knownbits --method cegis --certify
./build/rp_synth examples/reduced_product/mutual_interval_mod3.rp \
  --method quantified --certify
```

`rp_bestInv` reads CHCs; `rp_synth` reads the tab-separated `.rp` examples.
The mutual-support example yields `0 <=u x <=u 10 AND bit0(x) = 0`, while
synthesizing either component alone yields TOP.

Combine components with `+`: `interval`, `zones`, `octagon`, `polyhedra`,
`signed`, `knownbits`, and `congruence:M`. Existing numerical-domain aliases
also work. A congruence factor is TOP or one fixed residue; decimal M must be
at least 2 and fit each variable's width. All row arithmetic remains modular.

## Options and results

Use `--help` for all options. The default method is `cegis` and timeout is
30 seconds; `--timeout -1` disables the deadline. `--max-queries` and
`--max-candidates` bound solver calls and CARE candidates. Ablations are
`--no-reduction`, `--no-promotion`, and `--range-first`.

JSON distinguishes `complete`, `sound`, and `bestness_certified`, and includes
bounds, facts, the stop reason, and solver statistics. `--certify` independently
checks bestness. Interrupted runs retain the last sound invariant, initially TOP.
Exit codes: 0 complete, 3 incomplete, 2 input/validation error. The synthesis
budget includes certificates but excludes CHC parsing and output.

`--dump PREFIX` exports initiation, consecution, and completed-run bestness
obligations. All should replay as UNSAT using the build's Z3 library:

```sh
python3 scripts/replay_obligations.py --library /path/to/libz3.dylib \
  PREFIX.init.smt2 PREFIX.step.smt2 PREFIX.best.smt2
```

## Native API

Link target `invfinder_rp` and include `reduced_product.h`:

```cpp
invfinder::ReducedProductInvariant engine(loop);
engine.add_product("interval+knownbits+congruence:3");
invfinder::rp::Options options;
options.certify_best = true;
const auto& result = engine.run(options);
z3::expr auxiliary = engine.get_inv_with_var(loop.vars);
auto verification = invfinder::k_induction(loop, {}, &auxiliary);
```

Include `k_induction.h` for verification. Add custom observations with
`add_range(label, expr)` or `add_flat(label, expr)` before running; choose BV
widths explicitly. Keep the Z3 context alive and use a fresh engine per run.
Reduced-product auxiliaries use the native verification API. CHC-local
quantifiers remain in verifier queries; UNKNOWN means incomplete synthesis.

## Experiments and validation

```sh
python3 scripts/run_experiments.py --mode reduced-product -P build/rp_bestInv \
  -D examples/reduced_product --certify -O results/rp.csv
python3 scripts/summarize.py results/rp.csv --analysis common --methods quantified,cegis
ctest --test-dir build --output-on-failure
```

CSV `Info` retains full RP JSON; incomplete runs are excluded from comparisons.
The tests cover 104 synthesis runs against finite-state oracles, native/CHC
adapters, budget interruptions, certificate replay, and auxiliary k-induction.
Oracle records go to `build/rp_regressions.json`. The integrated suite passed on
Z3 4.12.2.0; full benchmark evaluation remains separate.

See [the algorithm notes](reduced_product_design.md) for the correctness arguments.
