# M3 global distance and uniqueness: independent coverage audit

**AUDIT PASS**

Scope: the complete theorem `final:M3` and its proof in
`paper/sections/series-realizations.tex`, lines 435–497, compared with the
actual Lean definitions and theorem signatures. No other coverage row was
audited.

## Previously unproved components

- Metric-geodesic interpretation, higher-rank global length minimality among
  admissible SPD paths, and the actual metric distance formula.
- Higher-rank uniqueness of the constant-speed minimizing curve in the full
  finite-piece C1 path class, including coincident endpoints.

Both components are now proved without strengthening the paper's hypotheses.

## Exact content checked

- `MatrixPiecewiseAdmissiblePath` retains continuous SPD curves on `[0,1]`, a
  finite strict partition, continuously extending segment velocities, and
  derivative identities only on segment interiors. It imposes neither global
  differentiability nor differentiability at corners or endpoints.
- `matrixHessianSpeed` uses the native derivative and the actual metric
  `precisionMetric (γ s)⁻¹`; `matrixHessianPathLength` is its interval integral.
  `matrixPiecewiseHessianDistance` is the infimum of these lengths over that
  path class, rather than a distance defined by the target formula.
- `matrix_piecewise_length_ge_spd_log_norm` applies to every such path.
  `matrix_piecewise_hessian_distance_eq_spd_log_norm` identifies that actual
  infimum with the Frobenius norm of the logarithm of the correctly oriented
  relative matrix. `matrix_spd_geodesic_globally_minimizing` proves attainment
  by the paper's literal square-root/exponential curve.
- The log-calculus premises of older intermediate results are discharged.
  The exponential differential is the actual Fréchet derivative, its
  noncommutative Duhamel formula is proved, and the spectral divided-difference
  inverse is constructed on the full matrix space. The inverse function
  theorem identifies its local inverse with the actual symmetric SPD
  logarithm. Log-path differentiation, log continuity, and continuity of its
  velocity are consequently derived, with repeated eigenvalues covered.
  Final path results require none of these conclusions as hypotheses.
- Intermediate globally SPD paths are obtained by a proved clamp extension
  preserving the original curve on `[0,1]`, its interior derivatives, and its
  length. No globally SPD assumption is added to final statements.
- `matrix_piecewise_constant_speed_minimizer_unique` assumes only membership
  in the original path class, actual minimizing length, and constant metric
  speed almost everywhere. It identifies the curve with the canonical formula
  at every point of the closed interval. It contains no distinct-endpoint or
  nonzero-distance premise; coincident endpoints are included. Its
  subinterval contraction and two-endpoint rigidity proof derive the claimed
  logarithmic lift and linear interpolation rather than assuming them.
- `matrix_spd_geodesic_metric_distance` proves the metric-geodesic identity
  `d(γ(s),γ(t)) = |t-s| d(X,Y)` for every pair of real parameters using that
  actual variational distance. Together with the existing native derivatives,
  constant speed, SPD membership and endpoint identities, this supplies the
  formerly missing metric-geodesic interpretation. The paper proof's energy
  Euler–Lagrange derivation is not separately claimed as a new formal result.
- The existing `matrix_divergence_relative_symmetrization` has precisely the
  actual relative-eigenvalue sum `4 * ∑ sinh(log(λᵢ)/2)^2`.
  `rank_one_piecewise_distance_divergence_symmetrization` gives its rank-one
  distance specialization. `matrix_symmetrized_divergence_not_distance_function`
  excludes every scalar recovery function in each rank at least two by actual
  SPD equal-distance witnesses. The alternative witness already recorded in
  the coverage map proves the theorem's boundary; this audit does not claim
  formalization of the paper proof's particular two-coordinate witness at
  every prescribed positive distance.

No stronger assumptions, weaker conclusions, lost endpoint cases, or hidden
target conclusions were found. The existing symmetrization and boundary
results together with the new distance, metric-geodesic and uniqueness
results cover the complete named paper statement.

## Verification evidence

The proving agent supplied PASS results for `lake build SigmaFormalization`,
`Verify.source_audit()`, and selected transitive axiom checks for all materially
new final theorems. These checks were not redundantly rerun by this auditor.
Independent source inspection of the nine new M3 proof modules found no
`sorry`, `admit`, `sorryAx`, or new axiom declarations. This is a bounded M3
coverage audit, not a fresh full `Verify.py` or `SigmaAxioms.lean` run.
