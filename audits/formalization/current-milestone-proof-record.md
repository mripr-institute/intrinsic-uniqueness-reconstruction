# Coverage reconstruction and exact probability, discrete and Farey bridges

This milestone does not claim full-paper completion. It reconstructs the current
coverage inventory, closes two gaps discovered by independent review, and removes
the project-owned warnings. The authoritative starting state and initial counts
are recorded in `current-baseline.md`.

## Mathematics added

For `final:P7`, `CalibratedGammaDensity.entropy_integrable_of_divergence_ne_top`
derives integrability of the nonnegative entropy defect from finite divergence.
The already proved integrability of cross entropy, the candidate density, and
the reference density then derives integrability of `f * log f`.
`finite_extended_entropy_formula` and
`calibrated_gamma_finite_extended_entropy` use only finiteness of the extended
entropy, rather than adding ordinary entropy integrability as a premise.
Together with the existing maximum and equality case this closes P7.

For `final:P6`, `independent_nat_sum_measure` identifies the existing PMF
convolution with a product-measure pushforward. `independent_nat_sum_law`
transfers this identity to arbitrary supplied independent random variables.
`borel_independent_finset_law` inducts over finite sets using native joint
independence. `borel_independent_sum_probabilities` proves the displayed event
probability on any probability space for `n >= k >= 1`, including `n = k`.
It reuses all existing Borel coefficients, normalization, and analytic inverse
results. This closes P6 without claiming a Galton-Watson tree construction;
P6-gw and P6-boundaries remain separate unfinished obligations.

For `final:R2`, `quadratic_scale_calibration_nonzero` exports calibration at
any nonzero vector. The earlier unit-vector theorem remains available. This
removes the stronger hypothesis from the direct calibration mapping.

For `final:C8`, the discrete logarithmic curvature is proved on the exact
admissible domain. Both integer and half-lattice recurrence theorems recover
values from consecutive anchors. The half-lattice version requires no data
outside the domain and permits an interior anchor pair. A smooth sine
perturbation preserves every integer sample while changing the value at 1/4,
inside every admissible placed domain. The independent auditor requested both
the restricted recurrence and this explicit interior disagreement; both were
implemented and approved. C8's other clauses remain partial.

For `final:tree-integral`, `farey_left_integral` proves the interval integral
for every positive t, including reversed integration for t < 1 and t = 1.
That labelled formula is now complete; B2's other clauses remain partial.

No paper mathematics, candidate class, or observation was weakened. No new
theory replaced an existing development. Fourteen new declarations were added
to `SigmaAxioms.lean`.

## Warning cleanup and verification safeguards

62 initial project warning reports across 27 Lean files were eliminated:
deprecated `Continuous.exp` uses now call `Continuous.rexp`; redundant tactic
sequencing, dead tactics, unnecessary `simpa`, and unused binders were cleaned.
The unnecessary `DecidableEq` section assumption on
`symmetric_trace_square_eq_zero` was removed. Other old theorem assumptions and
conclusions were retained. Upstream Mathlib doc-string warnings were not edited
or suppressed. Informational `ring_nf` suggestions are not warnings.

`Verify.py` retains its existing build, source, and axiom checks and additionally
rejects project axiom declarations and printed dependencies outside `propext`,
`Classical.choice`, and `Quot.sound`.

`scripts/rebuild_coverage.py` generates the two top-level ledgers from the current
paper and independently inspected section maps. It preserves equation/component
labels, exact statement text/hashes and current source locations, rejects
unmapped completions, and can elaborate every declaration mapping with Lean.
Its `--require-complete` gate checks both the named environments and separately
labelled formulas. That gate intentionally fails while recorded gaps remain.

## Independent review

- Core/closure, probability, operator and realization statements were examined
  independently, comparing current signatures rather than trusting old statuses.
- A second auditor challenged P6 and P7 and found their missing bridges before
  implementation. After the fixes it returned bounded AUDIT PASS for each.
- Another auditor rechecked F1/F2/R2 and found the nonzero-vector calibration
  mapping issue; it approved the corrected theorem and mapping.
- Warning cleanup and verifier changes passed separate coverage-preservation
  review. O1, O1-kernel and O7 received a further adversarial operator review.
- C8's new components and the full-domain Farey integral received bounded
  AUDIT PASS after the domain refinements above. A final diff review found
  no weakening of existing mathematics.
- The remaining full-paper audit result is DEFECTS FOUND, documented without
  claiming that generic equivalences or scalar series replace missing native
  analytic, measure, operator, stochastic or topological statements.

## Coverage at this milestone

80 named mathematical environments: 2 definitions, 30 complete, 35 partial,
13 missing, zero pending classifications. Compared with the fresh initial audit,
P6 and P7 moved from partial to complete. The extra labelled-formula ledger has
15 component entries, of which four still have missing proofs; several are
components of already-partial named theorems, and the arbitrary-power Todd
formula is standalone. These must not be ignored in a full-paper completion claim.

Existing solved-but-stale components are credited in the new ledgers. Exact
remaining components and all 534 mapped declarations are available there.

## Validation

The aggregate build and all 534 mapped declaration checks pass. The aggregate
build has zero project-owned warnings. The source audit reports zero `sorry`,
`admit`, `sorryAx`, and project axiom declarations. Baseline and post-entropy-fix
full `Verify.py` runs passed. The final six C8/Farey additions separately passed
`#print axioms`, using only `propext`, `Classical.choice`, and `Quot.sound`.
The fresh aggregate build and declaration-map elaboration include all changes.
Two already-running full verifier/explicit axiom runs cover the probability
bridges; their completion is recorded in the next verification update rather
than launching redundant runs for the six independently checked additions.

The pre-existing Lake roots, unchanged Lean toolchain bytes, and dependency
manifest are intentionally retained in this milestone. No build products or
dependency-source modifications are included.
