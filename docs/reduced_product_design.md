# Reduced-product algorithm notes

ACR and CARE compute the joint best inductive invariant (BII) for a fixed finite
BV transition system. The objective uses initialization and consecution;
the safety postcondition does not constrain synthesis.

## Representation and anchor

A range observation `f_i` tracks unsigned bounds `[l_i,u_i]`. A flat observation
`g_j` tracks TOP or equality to one constant. Known bits, fixed-modulus
congruences, and Boolean predicate observations are flat factors. Signed ranges
use XOR with the sign bit; arithmetic retains its specified BV width.

If initialization is empty, return bottom. Otherwise sample an initial state
`s0`. Every inductive invariant contains `s0`, so any enabled flat factor must
use `c_j = g_j(s0)`. Only its enable flag needs synthesis. This specialization
does not imply that the fact holds at other initial states or is inductive.

The anchored tuples are finite and their inductive members are closed under
componentwise meet, which represents concrete intersection exactly. They
therefore have a unique least tuple `A*`. Exact reduction
`rho(A) = alpha(gamma(A))` preserves meaning and inductiveness. Leastness forces
`rho(A*) = A*`, so the least anchored tuple is the reduced-product BII.

## ACR: anchor-coupled refinement

Maintain a sound published tuple `U`, initially TOP, plus endpoint search limits
and blocked flat flags. Propose a binary threshold on an endpoint or activate a
flat factor. Query for a tuple below `U` satisfying the proposal, current limits,
and both initiation and consecution. All other components may strengthen jointly.

Before that query, optionally check whether `U` already implies the proposed
state constraint. UNSAT permits a semantics-preserving reduction shortcut.
Otherwise, a feasible tuple is independently validated before publication;
UNSAT excludes only the tested threshold or flag. UNKNOWN or a budget stop
returns the last published tuple.

Every accepted tuple remains above `A*`, and failed proposals preserve `A*`
as a feasible choice. Resolving all endpoints and flags therefore yields `A*`.
For total range width `W` and `K` flat observations, there are at most `2W + K`
outer proposals. Reduction, validation, and certification add solver calls.

## CARE: shared counterexamples and promotion

CARE uses the same outer search with a persistent parameter solver instead of
the quantified feasibility query. Failed initiation learns a positive example.
Failed consecution learns an implication `membership(s) => membership(t)` for
an actual transition `s -> t`. The target is not automatically positive:
another component may exclude its source.

Maintain a lower envelope `L = alpha(P)` of justified positive examples.
Initially `P = {s0}` and `L <= A*`. If a recorded transition source belongs to
`gamma(L)`, it also belongs to the inductive `gamma(A*)`; consequently its target
belongs to `gamma(A*)` and can be promoted. Repeat this closure as `L` grows,
and use its bounds/facts to restrict subsequent candidates.

Envelope membership can justify unreachable states: it expresses an abstract
lower bound on the BII, rather than a reachable-state approximation. Positive
and implication constraints persist across proposals. Every rejected candidate
violates a newly learned constraint; finite parameter space gives termination
with exact, unlimited solver answers. The outer bound remains `2W + K`, but
CARE's inner candidate/verifier calls can be much larger.

## Validation and scope

Candidates pass fresh initiation and consecution checks before publication.
Reduction shortcuts require implication proofs. Optional bestness certification
asks a fresh solver whether any strictly smaller inductive tuple exists, without
learned examples or search limits. UNSAT certifies the BII. Exported obligations
are replayable SMT formulas, not kernel-checked proof objects.

The implementation supports fixed range/flat observations, not arbitrary modulus
or coefficient inference. The existing single-domain search already couples
rows globally; row concatenation alone is not a new contribution. The proposed
extensions are anchor specialization, reduction-aware refinement, and justified
abstract-envelope promotion. Publication priority and performance advantages
require separate evaluation.

Background: reduced products (Cousot, Cousot, Mauborgne, FoSSaCS 2011),
implication-example learning (Garg et al., ICE, CAV 2014), and
[reduced-product transformer synthesis](https://arxiv.org/abs/2408.04040).
See [the usage guide](reduced_products.md) for commands and tests.
