# O4 determinants: complete independent paper-to-Lean review

> **Historical record.** Statuses, counts, commands and local paths below describe
> the recorded stage, not the current checkout. See [current coverage](../../lean-coverage.md)
> and the [archive guide](../README.md).

Date: 2026-09-27. Reviewer: `/root/missing_countermodels` (independent read-only agent).

## Verdict

**COMPLETE PASS for `final:O4-determinants`. No named-statement residuals remain.**

- The zeta determinant comes from the genuine shifted nuclear trace, with continuation regular at zero, a derived Lerch formula, and exact Gamma normalization for every positive shift.
- The prime multiplier removes exactly the zero mode. Both special determinants equal sqrt(2pi).
- The native category assumes nonnegative self-adjointness, a genuine shifted resolvent and nuclear resolvent square. Compactness and the complete eigenbasis are derived, and the conventional Hilbert-Schmidt premise implies category membership.
- Ordinary and regularized determinants are unordered products, independent of spectral basis and category witness, with locally uniform limits of actual finite spectral compression determinants.
- The entire sinh power-series formula includes the value one at zero and is independent of square-root choice. The Gamma formula holds at every complex argument, including zeros.
- Analytic zero orders equal spectral multiplicities. Equal full zero multisets recover arbitrary competing generators through a unitary preserving their entire domains.

## Verification

All 12 frozen source modules independently elaborate successfully; only style and unused-variable warnings occur. Eight targeted transitive axiom checks, covering compression convergence, choice independence, arbitrary-operator inversion, canonical reconstruction, both entire formulas, Lerch normalization and the prime value, report only `propext`, `Classical.choice`, and `Quot.sound`. Spectral data and reconstruction are derived, not assumed.
