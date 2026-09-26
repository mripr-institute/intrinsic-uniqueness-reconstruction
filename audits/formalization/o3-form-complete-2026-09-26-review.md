# O3-form: complete independent paper-to-Lean review

Date: 2026-09-26. Reviewer: `/root/paper_coverage_review` (read-only independent agent).

## Verdict

**COMPLETE PASS** for `final:O3-form`, including its exact domain equation `final:O3-form-domain`.

- The actual canonical graph closure is identified with the native self-adjoint nonnegative spectral operator; its square root and closed graph are established.
- Every square-root-domain vector has a literal locally absolutely continuous finite-energy representative.
- Conversely, every Gamma-weighted L2 class with such a representative belongs to the actual square-root domain. No endpoint traces, derivative identities, smoothness or spectral summability are assumed.
- The reverse proof establishes a.e. differentiability from literal AC, local derivative integrability from finite energy, and the genuine fundamental theorem using tagged partitions and AC control of the null exceptional set. The singular derivative component is excluded explicitly.
- Compact-interior integration by parts yields the actual native Hilbert-space weak-gradient pairing, which implies spectral square-root summability by the audited graph-core argument.
- The mixed form identity holds for arbitrary AC representatives of any pair in the full domain, with the correct complex conjugation convention and derived integrability.
- The genuine heat semigroup preserves nonnegative real inputs, one, and the Gamma probability integral for every nonnegative time, including zero.

## Checks

Independent source elaboration and targeted transitive axiom checks passed for the new foundation and final reverse-domain statements, returning only `propext`, `Classical.choice`, and `Quot.sound`. The Sigma umbrella build and source audit passed. The long full axiom job was not awaited and predates these new results.

The separate theorem `final:O3` retains its endpoint and maximal-domain obligations; this review does not claim that theorem complete.
