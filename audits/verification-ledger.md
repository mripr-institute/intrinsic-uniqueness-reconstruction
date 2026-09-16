# Sigma reconstruction: verification ledger

12 September 2026.

**PASS: 59 checks** — 32 symbolic identities and 27 numerical comparisons at 70 decimal digits. Numerical tolerance: relative error below 10⁻⁵⁵.

These checks supplement the written proofs. They do not constitute a rerun of the supplied MPFR instrument or a Lean, Coq, or Isabelle proof-kernel check.

| Check | Method | Result | Relative error |
|---|---|---|---|
| Riccati | symbolic identity | PASS | exact zero |
| Exact recentering | symbolic identity | PASS | exact zero |
| Group cocycle | symbolic identity | PASS | exact zero |
| Bregman quotient | symbolic identity | PASS | exact zero |
| Repeated root | symbolic identity | PASS | exact zero |
| Pearson | symbolic identity | PASS | exact zero |
| Self-survival derivative | symbolic identity | PASS | exact zero |
| Full coordinate identity | symbolic identity | PASS | exact zero |
| Sigma derivative order 2 | symbolic identity | PASS | exact zero |
| Sigma derivative order 3 | symbolic identity | PASS | exact zero |
| Sigma derivative order 4 | symbolic identity | PASS | exact zero |
| Sigma derivative order 5 | symbolic identity | PASS | exact zero |
| Sigma derivative order 6 | symbolic identity | PASS | exact zero |
| Sigma derivative order 7 | symbolic identity | PASS | exact zero |
| Sigma derivative order 8 | symbolic identity | PASS | exact zero |
| Laguerre eigenfunction 0 | symbolic identity | PASS | exact zero |
| Laguerre eigenfunction 1 | symbolic identity | PASS | exact zero |
| Laguerre eigenfunction 2 | symbolic identity | PASS | exact zero |
| Laguerre eigenfunction 3 | symbolic identity | PASS | exact zero |
| Laguerre eigenfunction 4 | symbolic identity | PASS | exact zero |
| Laguerre eigenfunction 5 | symbolic identity | PASS | exact zero |
| Laguerre eigenfunction 6 | symbolic identity | PASS | exact zero |
| Laguerre eigenfunction 7 | symbolic identity | PASS | exact zero |
| 4D OU radial generator | symbolic identity | PASS | exact zero |
| Deficit cumulant 1 | symbolic identity | PASS | exact zero |
| Deficit cumulant 2 | symbolic identity | PASS | exact zero |
| Deficit cumulant 3 | symbolic identity | PASS | exact zero |
| Deficit cumulant 4 | symbolic identity | PASS | exact zero |
| Deficit cumulant 5 | symbolic identity | PASS | exact zero |
| Deficit cumulant 6 | symbolic identity | PASS | exact zero |
| Deficit cumulant 7 | symbolic identity | PASS | exact zero |
| Deficit cumulant 8 | symbolic identity | PASS | exact zero |
| Deficit MGF integral s=-2 | 70-decimal numerical cross-check | PASS | 9.0556791e-72 |
| Deficit MGF integral s=-0.5 | 70-decimal numerical cross-check | PASS | 9.0556791e-72 |
| Deficit MGF integral s=0.3 | 70-decimal numerical cross-check | PASS | 1.467286e-71 |
| Deficit MGF integral s=0.8 | 70-decimal numerical cross-check | PASS | 2.5454237e-71 |
| Deficit raw moment 1 | 70-decimal numerical cross-check | PASS | 0.0 |
| Deficit raw moment 2 | 70-decimal numerical cross-check | PASS | 0.0 |
| Deficit raw moment 3 | 70-decimal numerical cross-check | PASS | 1.3350416e-71 |
| Deficit raw moment 4 | 70-decimal numerical cross-check | PASS | 0.0 |
| Conditional deficit MGF a=0.1 | 70-decimal numerical cross-check | PASS | 2.940666e-71 |
| Conditional deficit MGF a=0.8 | 70-decimal numerical cross-check | PASS | 1.4324244e-71 |
| Conditional deficit MGF a=2.0 | 70-decimal numerical cross-check | PASS | 1.2074873e-71 |
| Lambert level preservation 0.01 | 70-decimal numerical cross-check | PASS | 0.0 |
| Lambert involution 0.01 | 70-decimal numerical cross-check | PASS | 1.4149499e-73 |
| Lambert level preservation 0.2 | 70-decimal numerical cross-check | PASS | 9.0556791e-72 |
| Lambert involution 0.2 | 70-decimal numerical cross-check | PASS | 0.0 |
| Lambert level preservation 0.9 | 70-decimal numerical cross-check | PASS | 2.2639198e-72 |
| Lambert involution 0.9 | 70-decimal numerical cross-check | PASS | 1.8111358e-71 |
| Lambert level preservation 1.1 | 70-decimal numerical cross-check | PASS | 5.6597994e-72 |
| Lambert involution 1.1 | 70-decimal numerical cross-check | PASS | 4.9394613e-71 |
| Lambert level preservation 2.0 | 70-decimal numerical cross-check | PASS | 0.0 |
| Lambert involution 2.0 | 70-decimal numerical cross-check | PASS | 9.0556791e-72 |
| Lambert level preservation 10.0 | 70-decimal numerical cross-check | PASS | 0.0 |
| Lambert involution 10.0 | 70-decimal numerical cross-check | PASS | 0.0 |
| Global geodesic relation 0.2,3.0 | 70-decimal numerical cross-check | PASS | 1.1088587e-71 |
| Global geodesic relation 4.0,0.7 | 70-decimal numerical cross-check | PASS | 9.3134624e-72 |
| Levy exponent 0.1 | 70-decimal numerical cross-check | PASS | 0.0 |
| Levy exponent 2.0 | 70-decimal numerical cross-check | PASS | 0.0 |

## Supplied audit provenance

| File | SHA-256 |
|---|---|
| adversarial-audit-blind.txt | f6789cdebc719df8641873c16fbffcdc3c0e95c0ce5c1d71ef5c48ffbf06a65d |
| adversarial-audit-unblinded.txt | 66ecd6d6348c46cb3b83d5ed6ef8f318038bf005bc46185cb4545f0f8b75dd8c |

Each report records 32 CORE passes and zero CORE failures, 5 diagnostic passes, 60 core evaluations, 1479 deterministic trials and 1400 trials in its stochastic category, with zero reported violations. Their matching counts are not added as independent replications.

The printed cascade reaches 16384 bits. Phase 2 needs clarification of its zero-handling rule: zero residual at 256 bits is followed by a positive residual at 512 bits, so literal log-residual monotonicity does not follow from the table. The separate per-row tolerance bounds are satisfied.

The reports explicitly distinguish midpoint-radius diagnostics from rigorous outward-rounded enclosures, coordinate perturbations from observational noise, and synthetic catalog checks from empirical survey tests. Witness generation is reported; the printed cross-language verification command is not a completed parity result.

The mathematical conclusions are proved in the manuscript independently of these report predicates.
