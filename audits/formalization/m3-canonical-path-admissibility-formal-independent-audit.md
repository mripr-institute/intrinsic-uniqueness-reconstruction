# Independent M3 canonical-path admissibility audit

Verdict: **AUDIT PASS** for the canonical-path admissibility and exact-length
clause only; this is not an audit pass for the full `final:M3` theorem.

The auditor compared `Sigma.matrix_spd_geodesic_admissible` with the exact
definition `MatrixPiecewiseAdmissiblePath` in `SigmaMatrixPathBounds.lean`.
The endpoints are discharged by the existing native endpoint identities. The
path is continuous on `[0,1]` by its actual derivative theorem, and its value
is positive definite at every parameter by `matrix_spd_geodesic_positive`.
The witness uses the valid strict partition with `N = 1` and node map
`a j = (j : ℝ)`. On the sole closed segment it supplies
`matrixExponentialCurveVelocity`, proves that velocity continuous using its
actual derivative, and proves the required `HasDerivAt` identity at every
interior point.

`matrix_spd_geodesic_is_admissible_with_exact_length` states the actual
`matrixHessianPathLength` equality and combines it with this path-class proof;
it does not substitute a scalar length surrogate. These declarations establish
that the canonical curve is a valid competitor of the exact class and has the
stated length. They do not establish that arbitrary paths are no shorter, do
not identify the infimum/distance, and do not prove higher-rank uniqueness.
Those residual clauses remain in the M3 audit, whose status stays `partial`.
