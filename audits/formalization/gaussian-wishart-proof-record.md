# Completed M4 milestone

Starting commit: `09a940822b98f1901778a1633032235942deb642`.

Reused the preserved local Gaussian product, measure, moments, likelihood,
Wishart transform/divergence, entropy and lower-rank proofs. Added only the
remaining full-rank and actual conditional-kernel sufficiency bridges:

- `SigmaMatrixScatterFullRank.lean`: native sample and Wishart scatter are
  positive definite almost surely iff sample count is at least dimension.
- `SigmaStatisticSufficiency.lean`: proved common conditional-kernel criterion
  for dominated statistic-dependent density tilts.
- `SigmaMatrixGaussianSufficiency.lean`: one parameter-independent conditional
  law of the entire Gaussian sample given scatter, for every SPD covariance.

Whole-statement independent adversarial audit: PASS.

One integration gate: source proof-escape audit PASS, full library build PASS,
and transitive axiom checks of sufficiency, full Wishart moment formula, rank
iff, unique MLE, singular nonattainment and m-copy KL all PASS. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. Project warnings: zero. No repeated
broad verifier was launched. `SigmaAxioms.lean` is synchronized.

Coverage after M4 completion: 80 items; 2 definitions, 50 complete, 20 partial,
8 missing. Other local WIP, including in-progress P6/P4 boundary proofs, is
preserved outside this commit.
