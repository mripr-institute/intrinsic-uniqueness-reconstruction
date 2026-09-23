# M3 canonical-path admissibility clause

Starting commit: `1006813f911edc93c427c26b75cf1413df57ef7`.

This milestone formalizes one residual component of `final:M3`: the canonical
higher-rank SPD curve is an element of the exact finite-piece admissible path
class used by the paper's variational problem. The declaration
`Sigma.matrix_spd_geodesic_admissible` in `lean/SigmaMatrixGlobalGeodesic.lean`
proves the original path-class predicate, including the actual SPD endpoints,
continuity on `[0,1]`, positive definiteness throughout, a strict one-segment
partition, continuous segment velocity on the closed segment, and the native
derivative identity on its open interior. The one-segment velocity is the
derivative of the actual matrix exponential path.

The companion theorem `Sigma.matrix_spd_geodesic_is_admissible_with_exact_length`
combines that admissibility witness with the existing exact interval-integral
length theorem. It supplies a genuine competitor in the paper's path class.
This milestone does not prove the all-rank lower bound for arbitrary paths,
the metric-distance formula, or uniqueness of higher-rank minimizing curves;
`final:M3` remains partial. No unrelated O4 changes are part of this milestone.

Targeted kernel elaboration of `SigmaMatrixGlobalGeodesic.lean` passed. The
independent clause audit is recorded in
`m3-canonical-path-admissibility-formal-independent-audit.md`.
