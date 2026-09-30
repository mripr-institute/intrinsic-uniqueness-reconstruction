# O4 zeta determinant: complete independent review

> **Historical record.** Statuses, counts, commands and local paths below describe
> the recorded stage, not the current checkout. See [current coverage](../../lean-coverage.md)
> and the [archive guide](../README.md).

Date: 2026-09-26. Reviewer: `/root/paper_coverage_review` (independent read-only agent).

## Verdict

**COMPLETE PASS for `final:O4-zeta-determinant` and both special values, including the prime convention.**

- `laguerreHurwitzZeta` correctly translates every positive shift to Mathlib's circle-normalized Hurwitz parameter, subtracting the finite initial segment.
- Native shifted nuclear traces agree with this continuation on Re(s)>1; regularity at zero is proved.
- The determinant is literally exp(-deriv zeta 0).
- `laguerre_hurwitz_deriv_zero` proves the full Lerch formula for every a>0, and `laguerre_zeta_determinant_gamma` yields sqrt(2pi)/Gamma(a).
- The prime spectral multiplier kills exactly mode zero and equals n^-s on every positive mode. Its native trace is Riemann zeta and its determinant equals sqrt(2pi), as does the shift-one determinant.
- The derivation is noncircular: a uniformly convergent second-order analytic remainder gives the relative Gamma formula; shift 2 fixes the pole-removal derivative; half-shift duplication and Gamma(1/2) fix the absolute constant. No normalization is assumed.

All six complete sources independently elaborated successfully. Targeted transitive axioms for traces, prime mode convention, continuation identity, Lerch and Gamma formulas, and both special values were only `propext`, `Classical.choice`, and `Quot.sound`.

The enclosing `final:O4-determinants` remains partial for ordinary/regularized determinant basis/category identification and competing-operator zero-multiset reconstruction.
