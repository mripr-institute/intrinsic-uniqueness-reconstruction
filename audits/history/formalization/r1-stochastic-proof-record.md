# R1 stochastic proof record

> **Historical record.** Statuses, counts, commands and local paths below describe
> the recorded stage, not the current checkout. See [current coverage](../../lean-coverage.md)
> and the [archive guide](../README.md).

Date: 2026-09-30

## Completion scope

R1 is complete relative to the general stochastic-calculus foundations
expressly retained by the paper. The theorem begins with a specified OU
process. Its Lean hypotheses supply a filtered Brownian probability space,
the general calculus, and a continuous progressive solution of the given
additive-noise OU equation.

This scope supersedes the older audit requirement to construct Brownian
existence and all stochastic calculus from scratch. Those foundational
constructions are not claimed. The choice of scope was explicitly confirmed
before the R1 completion. Existing independent reviews of R1's geometric
clauses remain applicable; the new stochastic proof received an
implementing-agent review, not a new independent external review.

## General supplied foundations

`SigmaItoLevyFoundations.lean` exposes `BrownianItoLevyCalculus` as an explicit
theorem parameter. It contains the following general laws:

| Foundation | Exact scope |
|---|---|
| Continuous-integrand approximation | Probability convergence of actual uniform-partition left-point sums to the supplied vector stochastic integral |
| Bounded-integrand martingale theorem | Every bounded progressive vector integrand has a native conditional-expectation martingale integral, starting at zero, with continuous paths |
| Square compensator | The square of that integral minus the actual Bochner time integral of the squared integrand norm is a native martingale |
| Itô formula | Every C² scalar function of every continuous progressive additive Brownian SDE, with its native Fréchet derivative and Euclidean Laplacian |
| Stochastic substitution | Integration of a continuous progressive scalar coefficient against an integral equals integration of the multiplied vector integrand against the original Brownian driver |
| Lévy characterization | A continuous native martingale starting at zero whose square minus time is a martingale has the real Gaussian independent-increment Brownian law |

None of these fields assumes an OU energy equation, a normalized Brownian
integral, a radial formula, or a dimension-four conclusion. The supplied
operations and the laws governing them are mathematical hypotheses, not
project-level Lean axiom declarations. A clean axiom print therefore does
not mean that the foundational hypotheses have themselves been constructed.

The probability measures, filtrations, martingales, independent increments,
Gaussian laws, ordinary integrals, differentiability and convergence in
measure are native Lean/mathlib objects.

## Derived stochastic equation

`SigmaRadialOUStochastic.lean` proves the following steps.

1. A progressive unit-vector integrand has squared norm one everywhere.
   Its actual time-integral compensator is therefore time. Applying the
   supplied general martingale and Lévy results proves the full real
   Brownian law, including Gaussian increment measures and independent
   finite increment families.
2. The existing Borel normalization `radialOUNormalize` preserves progressive
   measurability. It has norm one even at the origin, where it takes a fixed
   unit vector. Thus its stochastic integral is Brownian.
3. Native differentiation of `‖z‖²/2` gives gradient `z` and Laplacian `D`.
   Substitution in the universal C² Itô formula gives drift
   `D/2 - ‖Z‖²/2` and martingale term `∫ Z · dB`.
4. The actual identity `sqrt(2 * (‖z‖²/2)) • normalize(z) = z` holds also
   at zero. General stochastic substitution therefore replaces that
   martingale term by `∫ sqrt(2T) dβ`.
5. Choosing the first coordinate unit vector and specializing `D = 4`
   proves `dT = (2-T) dt + sqrt(2T) dβ` in integral form. The equation
   holds for every nonnegative time on one common full-measure event.

Principal declarations:

- `Sigma.BrownianItoLevyCalculus.unit_integral_brownian`
- `Sigma.BrownianItoLevyCalculus.normalized_integral_brownian`
- `Sigma.BrownianItoLevyCalculus.radial_ou_energy_ito`
- `Sigma.BrownianItoLevyCalculus.radial_ou_integral_substitution`
- `Sigma.BrownianItoLevyCalculus.radial_ou_stochastic_equation`
- `Sigma.radial_four_ou_stochastic_equation`

Together with the previously verified Gaussian/Gamma law, independent
uniform-sphere inverse, orthogonal-invariance uniqueness, radial-law
nonidentification and dimension-selecting generator, this covers R1's
whole named statement under the stated foundation scope.

## Additional native construction

Four additional modules prove useful stochastic prerequisites without the
supplied calculus interface:

- `SigmaRadialBrownianMoments.lean`: Gaussian fourth moments and the exact
  centered second moment of sums of independent squared Gaussian variables.
- `SigmaRadialBrownianProduct.lean`: native product-coordinate laws and
  independence, and Euclidean Gaussian squared-norm moments.
- `SigmaRadialBrownianQuadraticVariation.lean`: the exact error
  `E[(Qₙ - Dt)²] = 2Dt²/n` for positive uniform partition size, followed by
  mean-square and probability convergence of Brownian quadratic variation.
- `SigmaRadialBrownianSelfIntegral.lean`: an exact finite discrete energy
  identity and construction of `∫ B · dB` as a probability limit of actual
  left-point sums, with its quadratic energy identity and continuous paths.

These are independent supporting results. They do not purport to construct
the full general Itô/Lévy calculus used in the completed radial theorem.

## Validation

The complete `Sigma` umbrella builds with the pinned toolchain (3392 jobs).
The repository source audit finds no admissions or project axiom declarations.
All 13 targeted principal-declaration axiom checks report only `propext`,
`Classical.choice`, and `Quot.sound`. The coverage check resolves all 2057
mapped declarations through the compiled umbrella, and its completion gate
passes with 78/78 named statements and 15/15 labelled equations. These
counts retain the explicit supplied-foundation scope above.

The subsequent full `python3 Verify.py` run on commit `8869f70` passed:
the source audit, full library build, and all 2537 distinct declarations in
`SigmaAxioms.lean`. Every requested declaration produced a report, and the
only observed axioms were `propext`, `Classical.choice`, and `Quot.sound`.
The result and source hash are recorded in
[the full-project axiom audit](full-project-axiom-audit-2026-09-30.json).
