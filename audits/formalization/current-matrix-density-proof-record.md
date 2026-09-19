# Matrix deletion boundaries and density/Levy components

Parent milestone: `a403ecc3cd6a0868e09eaf37539256a584821547`, pushed to main.
The two full verifier/explicit axiom runs pending in its record both subsequently
completed successfully. No proof escapes or unexpected dependencies appeared.

## Exact mathematical changes

- M1 is complete. The basis-dependent family adds the sum of squared
  off-diagonal entries to the existing matrix potential. It retains the scalar
  seed, nonnegativity and full block additivity, but fails invariance at a
  rational orthogonal conjugate of diag(2,1). The rank-dependent family adds
  zero at rank one and one otherwise. It retains the seed, nonnegativity and
  orthogonal invariance, but fails scalar recursion at identity blocks.
  These are alternative valid witnesses to the named necessity statements,
  not claims that the paper proof's particular example formulas were formalized.
- C8's independent-amplitude family now has actual all-order derivatives,
  exact single zeros, recovery of rate and shape from consecutive indexed
  zeros, positive-ray mass, and amplitude identification from that mass.
  No normalization hypothesis is substituted for the amplitude conclusion.
- P8-selfdecomposition now has the displayed nonnegative jump density,
  integrability, the integral -2 log c, and an actual finite withDensity measure
  with that mass. Compound-Poisson identification of the existing residual law
  remains unproved; the ledger explicitly preserves that distinction.

## Verification and independent review

Each changed module compiled; the aggregate SigmaFormalization build passed
with zero project-owned warnings. Mathlib-only doc-string warnings remain.
All 559 coverage declaration mappings elaborate. The source proof-escape audit
passes. All 24 new material theorem checks in SigmaAxioms pass, with dependencies
limited to propext, Classical.choice and Quot.sound.

Separate adversarial reviews returned bounded AUDIT PASS for M1, C8's density
component, and the residual density/measure component. The M1 reviewer also
kernel-checked that the orthogonal witness remains positive definite using the
existing congruence theorem. No whole-paper completion is claimed.

Current named-statement totals: 80 items, 2 definitions, 31 complete,
34 partial, 13 missing, zero pending classifications.
