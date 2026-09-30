# R1 geometric clauses and five global-E contexts

> **Historical record.** Statuses, counts, commands and local paths below describe
> the recorded stage, not the current checkout. See [current coverage](../../lean-coverage.md)
> and the [archive guide](../README.md).

Date: 2026-09-27.

## Verdict

**Bounded independent PASS for all geometric clauses of R1 and the first five fixed-context clauses of global E.** R1 remains partial for its stochastic radial SDE. E remains partial for its universal Thom clause.

## Independent review

- `/root/missing_countermodels` reviewed root's SigmaRadialGaussian, SigmaRadialQuaternion and SigmaRadialIsotropy: literal Euclidean product Gaussian, native density, exact Gamma energy law, all orthogonal invariance and arbitrary isotropic-law uniqueness. Quaternion Gaussian averaging is a proved alternative to the paper's compact-group Haar averaging, with no angular-independence hypothesis.
- Root and `/root/paper_coverage_review` independently reviewed SigmaRadialSpherePolar and SigmaRadialSphereGaussian: normalized actual volume.toSphere, genuine polar-coordinate pushforward, radial product factorization, and arbitrary independent uniform-angle inverse. The sphere normalization is derived from positive finite geometric area; no area constant is assumed.
- `/root/missing_countermodels` independently reviewed SigmaRadialSphereCoordinates: actual direction-energy product law, uniform direction and native IndepFun, with an explicit unit-vector fallback at the null origin.
- `/root/paper_coverage_review` independently reviewed all five implemented clauses in SigmaClosureContexts: actual probability-convolution, marked self-adjoint operator, SPD-domain matrix, iid branching and isotropic Gaussian candidate categories. Their identifying conditions and reverse observations are retained; no candidate is defined by equality to a recipe.
- Root reviewed the four SigmaRadialOU prerequisite modules: genuine Brownian independent Gaussian increment category, actual finite-increment product law, literal continuous-path OU construction, integral equation, deterministic uniqueness and measurable normalization. Brownian existence and stochastic calculus are not claimed.

## Verification

Full `lake build Sigma` passed. Targeted axiom checks for Gaussian density, radial law, orthogonal invariance, isotropic uniqueness, uniform-sphere inverse, arbitrary supplied-variable inverse, direction-energy laws and continuous-path OU construction use only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining scope

R1 still needs the stochastic integral construction, norm-square Ito formula and the proof that the normalized unit-integrand integral is Brownian, yielding the actual radial SDE. The supplied Brownian category is not an existence theorem. Global E's Gaussian clause does not require that stochastic SDE; its only remaining context is the actual universal complex Thom/Chern correction and complete universal-line reverse observation.
