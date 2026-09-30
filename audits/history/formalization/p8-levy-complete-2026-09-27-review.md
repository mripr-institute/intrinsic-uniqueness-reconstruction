# P8-levy: complete paper-to-Lean review

> **Historical record.** Statuses, counts, commands and local paths below describe
> the recorded stage, not the current checkout. See [current coverage](../../lean-coverage.md)
> and the [archive guide](../README.md).

Date: 2026-09-27. Reviewer: `/root/paper_coverage_review` (independent read-only audit).

## Verdict

**COMPLETE PASS for `final:P8-levy`. No named-statement gaps remain.**

- Exact Gamma Levy measure, Levy integrability, exponent integral and both mixture identities are covered by the earlier reviewed native results.
- Complete Bernstein structure and the specified Stieltjes derivative are proved.
- The four zero-drift/asymptotic-ratio/support-infimum/mean tests apply to actual supplied probability subordinators with the exact linked Levy representation; no Gamma time-one law is assumed.
- The unconditional global Gamma process supplies the canonical subordinator.
- Every nonnegative drift is now realized on the same actual probability space, preserving measurable coordinates, zero start, stationary independent increments, and increasing right-continuous paths on one common full-measure event.
- Actual marginals equal `gammaDriftCompletion`; the exact all-time Laplace representation has the common `gammaCompletionLevyMeasure`, killing zero and stated drift.
- Unequal drifts have distinct actual time-one laws, making the Levy-measure-only nonidentification claim nonvacuous.

## Verification

The final SubordinatorPaths and SubordinatorExistence sources independently elaborate cleanly. Ten targeted declarations across global existence and drifted realization checks return only `propext`, `Classical.choice`, and `Quot.sound`. The full construction dependency chain has separate independent PASS reviews, as recorded in the P8 review.

## Probability chapter scope

All named probability mathematical statements are now covered. This does not assert coverage of every additional claim appearing inside paper proofs: the labelled-tree and ordered/unordered forest combinatorial counts remain separately unmapped. The broad original `final:P-formalization-scope` remark therefore remains explicitly qualified and excluded from mathematical theorem totals.
