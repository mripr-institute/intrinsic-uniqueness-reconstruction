# Divisor inventory, exact rank-one geometry, arbitrary Todd powers

Terminology: this record concerns Lean formalization of proofs supplied in the paper. Coverage gaps refer to Lean, not to unproved mathematical results.

Parent commit: `90ae8eb7838f3b7eb7bf08936b80c2d47490bec5`.

## Exact mathematical additions

- B3: actual irreducibles are exactly the marked numerical primes; total and
  distinct factor counts use the finite prime multiset and its valuation support.
  A finite enumeration has membership iff actual monoid divisibility. Its cardinal
  is the product of valuation-plus-one. An explicit two-sided inverse identifies
  the divisor lattice with the finite product of exponent intervals and preserves
  divisibility as coordinatewise order, including the empty support at the unit.
- M3, rank one: arbitrary piecewise-C1 native matrix paths allow corners and
  one-sided endpoint regularity. Segment FTC, a.e. speed comparison and telescoping
  prove lower bounds for total length and every subinterval. The canonical path
  attains the genuine path-infimum distance. Every a.e. constant-speed minimizing
  path is the unique logarithmic interpolation, also for coincident endpoints.
  This interpolation is proved equal to the literal spectral matrix square-root,
  logarithm and exponential formula, with the exact log-norm distance and native
  divergence symmetrization. The previous narrower C1 results are retained.
- `final:todd-arbitrary-power`: the finite weighted-multiplicity formula is proved
  for arbitrary scalar exponents in every commutative rational algebra, including
  zero divisors. The formal power uses standard binomial coefficients applied to
  native powers of F-1, not the desired multiplicity formula as its definition.
  Native natural-power compatibility and the characteristic-zero field bridge are
  proved. The multiplicity index set is fully characterized, including degree zero.

## Adversarial review and verification

Independent reviewer `/root/coverage_realizations`: AUDIT PASS for all eight
modules and scoped mappings. Its two earlier defects were fixed, not waived:
piecewise-C1 rather than everywhere-C1 paths, and rational algebras rather than
only fields. The Todd labelled equation is now complete with no residual clauses.

- Aggregate `lake build SigmaFormalization`: PASS, zero project-owned warnings.
- Source proof-escape audit: PASS.
- Focused new-public-declaration axiom checks: PASS, only ordinary Lean foundations.
- Coverage source/declaration check: PASS, 842 valid mapped declarations.
- Full `Verify.py` rerun started for this frozen batch; focused checks are complete.

Named statement totals remain 2 definitions, 36 complete, 32 partial, 10 missing.
The separate labelled-result inventory now has 13 complete and 2 missing. B3 still
requires Mobius/Dirichlet/multiplicative-function and totient content plus remaining
boundaries. M3 retains higher-rank global minimality/uniqueness and equal-distance
boundary witnesses. No claim of whole-paper completion is made.
