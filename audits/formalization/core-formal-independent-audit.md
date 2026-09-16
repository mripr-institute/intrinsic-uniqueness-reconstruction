# Independent audit of the final core formalization

The reviewed `complete` statuses for **C2, C3 and C4 are justified**. Their Lean premises match the draft's minimal regularity and calibration assumptions. The partial statuses for placement, C1, C8 and Z4 should remain partial. No reviewed theorem substitutes an assumed derivative hierarchy or desired reconstruction conclusion for its proof.

This audit compares `outputs/final-draft/core.tex` and `core-lean-map.json` against the eight source modules listed below and their relevant `SigmaAudit`/`PhaseIV` dependencies. It is a semantic statement audit, separate from the root's clean aggregate build. No root source was edited. The independent check file `work/SigmaFinalCoreAuditCheck.lean` compiled with Lean 4.14.0 using `python3 work/final_lean.py work/SigmaFinalCoreAuditCheck.lean`; its log is `work/final-SigmaFinalCoreAuditCheck.log`.

| Draft statement | Audit conclusion | Exact scope and remaining obligations |
| --- | --- | --- |
| `final:C0-placement` | Partial is conservative and accurate. | The affine-domain bijection, identity between the original and intrinsic placed formulas, actual first and second derivatives, closure, recovery of both parameters, intrinsic density bridge, and both open-ray integrals are proved. The manuscript's closed ray `r >= 0` still needs the null-endpoint rewrite. The map correctly declines to claim a packaged equivalence of admissible placed objects. |
| `final:C1` | Partial is conservative and accurate. | `curvature_reconstruction`, `riccati_reconstruction`, `exact_flow_identifies`, `unanchored_curvature_family` and `shifted_curvature_affine_family` prove genuine global converses on the specified open rays. Exact reciprocal flow is proved forward. Canonical forward second-derivative/Riccati and general affine-family forward clauses are not all exported together. |
| `final:C2` | Complete. | `recentering_iff` is the exact iff under differentiability on the positive ray and the single actual second-derivative datum at one. Both anchors and second differentiability elsewhere are derived. No global second differentiability, convexity or auxiliary anchors are assumed. |
| `final:C3` | Complete as a collection of proved components. | All group axioms, closure and inverse identities are proved on `(-1,infinity)`. `group_log_derivative_from_identity` derives differentiation away from zero, and the two uniqueness theorems assume a derivative only at zero. The independent check additionally packages the exact logarithm and cocycle iff statements, including canonical derivative normalizations, without adding global regularity. |
| `final:C3-automorphisms` | Partial must remain. | Actual differentiable-at-zero real endomorphisms are classified; injectivity forces nonzero slope; the explicit powers have composition, inverse and homomorphism identities. Continuous-only, measurable-only and monotone-only hypotheses, unrestricted additive-bijection countermodels, characteristic-zero formal automorphisms and integer-series statements are not all formally covered. |
| `final:C4` | Complete. | `Bregman` uses `deriv F`, and all candidates are genuinely differentiable on the positive ray. The exact scale-invariance iff and its entire affine family, calibration, parameter uniqueness, symmetric-slice inverse and ratio divergence are proved. No second differentiability or convexity is imposed. |
| `final:C8` | Partial must remain. | Actual all-order intrinsic density derivatives and normalized placed exponential-density derivatives are proved, with exact zero sets. The logarithmic placed-Sigma hierarchy for orders at least two, polynomial ambiguity, general unnormalized shape-family recovery, discrete curvature/interpolation and germ/global boundary assertions remain distinct obligations. |
| `final:Z4` | Partial must remain, while the negative characterization is established. | The explicit `k=2` rational density is positive, real analytic, integrable with mass one, unequal to Gamma and has all the same positive derivative-zero sets. The full real-parameter `k>1` family, endpoint limits, simple-zero/sign refinements, tail/log-concavity and transported counterdensity assertions are not all exported. |

## Minimal assumptions and native objects

The sources use functions on all of `R` whose hypotheses and conclusions are restricted to an open ray. This introduces no substantive regularity assumption outside the manuscript domain: differentiation at an interior point is local, and the proofs use eventual equality on that open ray. Every occurrence of `deriv` used in a converse is supported by a `DifferentiableAt` or `HasDerivAt` premise or by a derivative proved earlier. Consequently Lean's totalized derivative cannot make these converse hypotheses vacuous.

In C2, `HasDerivAt (deriv F) (-1) 1` expresses the draft's `F''(1)=-1` with existence included. The transport theorem constructs the derivative of `deriv F` at an arbitrary positive point by composing its derivative at one with an affine coordinate. The value and slope anchors are consequences of the recentering equation.

In C3, the potentially stronger global differentiability assumption in the older `PhaseIV.normalized_group_log_unique` is discharged by the new transport proof; it is not exposed as an assumption of `normalized_group_log_unique_at_identity`. The independent iff checks in `work/SigmaFinalCoreAuditCheck.lean` establish both canonical normalizations using the native logarithm derivative. Their axiom printouts contain only `propext`, `Classical.choice` and `Quot.sound`. The group laws are exported as explicit identities and domain-closure facts; the absence of a bundled group typeclass does not weaken the stated algebraic assertion.

In C4, `ScaleInvariantBregman` is a definition of the manuscript's universally quantified identity, not a custom axiom. The derivative classification differentiates the actual identity in its first variable and compares the cases with one scale fixed at two. `affinePotential_bregman` is a forward proof for every real triple `(A,B,C)`, so no convexity or positivity of `A` is hidden. The three calibration counterexamples remain in that family and their distinctness follows from proved parameter uniqueness.

The placement proofs often allow every `a>0`, which is stronger than the draft's `0<a<1`; omitting that upper bound is legitimate. Their analytic-domain condition is `0 < mu*r+a`, proved equivalent to `r > -a/mu` for positive `mu`. Recovery denominators are handled by the stated positive-domain assumptions.

## All-order derivatives and boundaries

`gamma_iteratedDeriv` proves equality of functions with native `iteratedDeriv n p` for every natural order. Its induction differentiates an explicit formula using the proved `gammaDerivative_step`. `zeroCounterdensity_iteratedDeriv` and `placed_density_iteratedDeriv` likewise induct through `iteratedDeriv_succ`, using eventual equality on the correct open domain before differentiating. The auxiliary formula functions are therefore proved derivative formulas, not free sequences renamed as derivatives.

The exact-zero theorems factor these actual derivative formulas and prove all remaining factors nonzero. Their inclusion of order zero is consistent: the positive-domain zero set is then empty. However, a unique zero is not by itself the exported simple-zero assertion, and proving only the normalized placed exponential density does not automatically export the full arbitrary-constant shape family or the logarithmic-Sigma hierarchy. The current partial coverage avoids those overclaims.

No full closure/minimality conclusion is certified by this audit. The differential component and generic inverse composition do not establish the entire presentation network. The map's distinction between those components and the unproved full closure is appropriate.

## Source fingerprints

- `outputs/lean/SigmaFinalCore.lean`: `9a692f29e5bf4b4293dd375462dd9ab75192d4a0e6d173e2b7d297dec6526135`
- `outputs/lean/SigmaFinalAffineCurvature.lean`: `e160997c04e148345fe5cf8934989d2d23eba15628ced3ba95c1481ff7e24a0a`
- `outputs/lean/SigmaFinalAutomorphisms.lean`: `e0137a74692752c8ed80de257ac98309230497d535000f6af239af74cd1ef7c8`
- `outputs/lean/SigmaFinalBregman.lean`: `8fece172635a8630a06f39fb49edecf83da2ef287a1df0d325e6ddea756ab5f2`
- `outputs/lean/SigmaFinalPlacement.lean`: `482de228dd69d5c202633a9f50d0cc98fc5d98fd1c9d1b99fbebb28a434a554c`
- `outputs/lean/SigmaFinalPlacementMeasure.lean`: `6f9a01c85793a1e3e19db744beadda1b210fdb9a7a712895e5f37c59e61a0486`
- `outputs/lean/SigmaFinalPlacedZeros.lean`: `75e753c4803d9e16ff449128f1c21d8a107957b574e012754601bded57c63258`
- `outputs/lean/SigmaFinalZeros.lean`: `dca925811f2a38e49b1f0f147b8dd6a8dad1c9a6bda6771175848e450bada707`
