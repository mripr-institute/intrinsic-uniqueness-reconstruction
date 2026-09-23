# Completed P5 survival boundaries

Starting commit: `5add737bd96c45ac65769b8ca54279c73ea775e9`.

Only the singular-survival regularity boundary remained. Reused the existing
native anchor counterexample, logarithmic pushforward hazard, and full Gamma
self-survival-shift classification without altering their proofs.

New modules:

- `SigmaProbCantorMeasure.lean`: explicit injective ternary coding establishes
  uncountability of the native Cantor set. A Standard-Borel equivalence transports
  the native atomless Gamma probability to an actual atomless Cantor probability.
  The witness need not be the uniform Cantor distribution.
- `SigmaProbCantorNull.lean`: recursive pre-Cantor measure bounds tend to zero.
- `SigmaProbSingularCDF.lean`: the shifted CDF is continuous and monotone, equals
  zero before level one and one after level two, and has derivative zero almost
  everywhere by local constancy off the closed null support.
- `SigmaProbSingularSurvival.lean`: constructs the actual Stieltjes probability
  with survival GammaSurvival times exp(-C), proves its atomlessness, positive
  support, strict decrease, continuity, positivity, anchor and endpoint limit,
  both a.e. hazard equations, nonidentity and failure of local integral AC.
- `SigmaProbSurvivalRegularityBoundary.lean`: discharges every singular-function
  premise and gives the unconditional final probability counterexample.

Whole named-statement independent adversarial audit: PASS, including fresh checks
of the previously complete clauses. Final assembly targeted compilation: PASS.

One integration gate: source proof-escape audit PASS; SigmaFormalization build
PASS; final transitive axiom checks for new foundations and both new and reused
final statements PASS. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
Project-owned warnings: zero. SigmaAxioms is synchronized. No repeated broad
verifier was launched.

Coverage: 80 items; 2 definitions, 53 complete, 17 partial, 8 missing.
Pre-existing uncommitted work remains untouched and outside this milestone.
