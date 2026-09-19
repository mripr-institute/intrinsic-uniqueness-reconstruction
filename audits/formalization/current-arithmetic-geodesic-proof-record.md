# Arithmetic transport and matrix path milestone

Parent commit: `1dff9bbf6181aa656f8554616cb67fcb6a2f70b6`.

## Exact additions

- B3: the exact integer carrier starts at two; the prescribed binary operation
  exists iff the code is injective. Every collision contradicts multiplication
  after dilation by two. A separately adjoined unit yields an actual labelled
  positive-integer monoid equivalence, with the encoding formula proved.
- B3: factorization inverse/uniqueness, actual divisibility and valuation maximum,
  gcd/lcm universal properties and valuation formulas, ordered divisor-to-submultiset
  bijection, arbitrary prime-permutation automorphisms, and an explicit nonadditive
  automorphism exchanging two and three. The shifted sampling formula is proved.
- M3: actual symmetric spectral logarithm, matrix exponential path, SPD positivity,
  endpoints, derivatives, geodesic differential equation, constant speed and actual
  interval-integral length. Rank one additionally has a variational distance defined
  by an infimum over native C1 matrix paths, an attaining path, a lower bound for
  every admissible path, and divergence symmetrization in that distance.

## Verification and independent review

- `lake build SigmaFormalization`: PASS; no project-owned warnings.
- Existing full `Verify.py` run for the preceding frozen milestone completed PASS.
- Current source proof-escape audit: PASS.
- Focused `#print axioms` for all new material public claims: PASS; only `propext`,
  `Classical.choice`, and `Quot.sound` occur. Checks added to `SigmaAxioms.lean`.
- Independent adversarial reviewer `/root/coverage_realizations`: AUDIT PASS for
  the bounded claims and mappings in the stable four-module batch.
- Independent older-coverage sampling `/root/coverage_core_closure`: AUDIT PASS
  for P2, P3, F1, with their complete actual analytic/algebraic signatures checked.

## Explicit remaining scope

B3 and M3 remain partial. Arithmetic irreducibles, full exponent boxes/counts,
Mobius/convolution, multiplicative functions, totient, and remaining deletion
boundaries are not claimed from these lemmas. Higher-rank global matrix distance
and minimizer uniqueness are not proved by the differential equation. The paper's
piecewise-C1 path category includes corners and one-sided endpoints, whereas the
rank-one module in this milestone proves the narrower native C1 infimum; the
category bridge remains recorded as a genuine residual component.

Named totals remain 80: 2 definitions, 36 complete, 32 partial, 10 missing.
Classifications are fresh; unchanged counts do not mean unchanged component coverage.
Unfinished files from parallel work are excluded from this milestone commit.
