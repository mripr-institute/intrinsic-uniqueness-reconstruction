# O6 functional-calculus inverse: canonical clause

**AUDIT PASS — canonical-A clause only.**

Scope: the second assertion of `final:O6-functional-calculus` in
`paper/sections/operators.tex`, lines 919–940: the full canonical operator
`2 log(Id+A)` is equivalently determined by the actual bounded operator
`J(A)=(Id+A)⁻²`, with the scalar functions retained as known data.

The generic first assertion for an arbitrary nonnegative self-adjoint `B`
and a strictly increasing Bernstein function is outside this audit and
remains unproved. This result therefore supports partial coverage of the
whole proposition, not complete coverage.

## Definitions and hypotheses checked

- `laguerreCanonicalOperator` is the closure of the actual compact-test
  differential operator. The existing `laguerre_canonical_eq_spectral`
  proves its equality, including its domain, to the integer spectral
  multiplier on the complete Laguerre basis of the original weighted L2
  Hilbert space.
- `laguerre_canonical_positive_shift_resolvent` supplies the existing bounded
  two-sided inverse of `1+A`, including range membership in the full domain.
  `laguerreSquaredResolvent 1 zero_lt_one` is literally its continuous-linear
  composition with itself, not a scalar series renamed as a resolvent.
- `laguerre_canonical_j_coordinate` and
  `laguerre_canonical_j_basis_action` identify this actual bounded operator
  on all vectors and on its proved complete basis. Its spectral coordinates
  are the positive numbers `(1+n)⁻²`.
- `integerBasisMultiplier` is an actual maximal complex `LinearPMap`; its
  domain consists of precisely those vectors whose multiplied complete-basis
  coordinates belong to l2. It is not restricted to finite spectral sums.
  `laguerreSpectralOperator gammaLaplaceExponent` has the same native domain
  construction, with `gammaLaplaceExponent t = 2 log(1+t)`.

## Exact clauses proved

- `laguerre_canonical_negative_log_j` identifies the maximal spectral
  application of the known Borel function `-log` to `J(A)` with the full
  canonical `2 log(1+A)` multiplier. Equality includes both domain and
  action. `laguerre_canonical_negative_log_j_selfAdjoint` proves native
  self-adjointness.
- `laguerre_canonical_negative_log_j_domain` gives the literal weighted-l2
  condition `∑ (2 log(1+n))² |x_n|² < ∞`; the action theorem gives every
  coordinate. No algebraic composition domain, positive spectral lower
  bound, or extra regularity is assumed.
- `laguerre_canonical_j_kernel_zero` proves that the actual complete bounded
  `J(A)` has no zero eigenspace. Together with the complete pure-point
  resolution, this rules out a spectral mass at the unattained endpoint
  zero. `laguerre_canonical_j_log_endpoint_independent` independently proves
  that changing a scalar function's assigned value at zero changes neither
  the maximal multiplier nor its domain.
- `laguerre_canonical_exponent_determined_by_j` reads the inverse scalar
  values from the actual squared resolvent's basis actions. Native
  self-adjointness and the complete spectral action force equality of the
  entire unbounded operator and its domain. The hypothesis specifies the
  known functional-calculus action on eigenspaces; it does not assume the
  desired global operator equality or maximal domain.
- `laguerre_canonical_exp_negative_log` proves the converse spectral
  reconstruction by the known function `exp(-t)`. The resulting maximal
  multiplier has domain top and equals the literal bounded squared
  resolvent on every vector. `laguerre_canonical_j_determined_by_exponent`
  extracts its scalar data from the full native exponent and proves
  uniqueness among bounded operators using complete-basis expansion.

These are actual operator reconstruction results on the original Hilbert
space, not only scalar identities. No strengthened hypothesis, weakened
conclusion, domain loss, omitted zero endpoint, or hidden target equality
was found for the canonical clause. A general Borel spectral-calculus API
or inverse theorem for arbitrary `B` is not claimed by these results.

## Verification evidence

The proving agent supplied PASS results for targeted compilation of
`SigmaOpInverseCalculusCanonical.lean`, `lake build SigmaFormalization`,
`Verify.source_audit()`, and transitive axiom checks on five materially new
final theorems (only `propext`, `Classical.choice`, and `Quot.sound`). This
audit independently inspected the theorem signatures, definitions and
proofs, and found no `sorry`, `admit`, `sorryAx`, or new axiom declaration
in that module. The supplied integration checks were not redundantly rerun
by this auditor. Neither a fresh full `Verify.py` run nor a fresh full
`SigmaAxioms.lean` run is claimed.
