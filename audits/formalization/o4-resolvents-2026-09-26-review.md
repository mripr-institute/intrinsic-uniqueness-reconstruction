# O4 resolvents: independent coverage review

Date: 2026-09-26. Reviewer: `/root/paper_coverage_review`, independent read-only agent.

## Verdict

**COMPLETE PASS for `final:O4-resolvents`.** No statement-level residuals found.

| Paper clause | Verified Lean evidence |
|---|---|
| Literal first and squared positive-time Laplace formulas | `laguerreLaplaceKernel`, `laguerre_laplace_kernel_eq_setIntegral`, with k = 0 and 1 |
| Actual weighted product-L2 kernels | `laguerre_laplace_kernel_vector_coe`, `laguerre_laplace_kernel_mem_l2` |
| Genuine time integrability almost everywhere and nonnegativity | `laguerre_laplace_kernel_integrable_ae`, `laguerre_laplace_kernel_nonnegative` |
| Actions on every complex Gamma-weighted L2 input | `laguerre_resolvent_kernel_action`, `laguerre_squared_resolvent_kernel_action` |
| First resolvent Hilbert-Schmidt, not trace class | `laguerre_resolvent_hilbert_schmidt`, `laguerre_resolvent_not_nuclear` |
| Squared resolvent trace class, trace zeta(2,a) for all a > 0 | `laguerre_squared_resolvent_nuclear`, `laguerre_squared_resolvent_trace`, and the three Hurwitz trace theorems |
| Resolvent difference trace psi(b)-psi(a) | `laguerre_resolvent_difference_nuclear`, `laguerre_resolvent_difference_trace_digamma` |
| Complete resolvent determines generator and domain | `operator_resolvent_domain`, `operator_resolvent_action`, `operator_full_resolvent_unique`, `laguerre_complete_resolvent_identifies` |
| Full marked positive-time heat operator determines generator and domain | `laguerre_marked_heat_inverse`, `laguerre_marked_heat_inverse_domain` |

The digamma function is the actual Gamma derivative divided by Gamma, with the correct normalization and sign. The Hurwitz formulas handle Mathlib's periodic shift convention with the required finite correction for every positive shift.

The kernel proof discharges its temporary vector-integrability premise in both final action theorems. Time integrals are proved genuinely integrable almost everywhere; the proof does not exploit the totalized value for nonintegrable integrals. The native operators are connected to the differential closure by `laguerre_canonical_eq_spectral`. No circular conclusion assumptions were found.

The sharp squared kernel norm and an explicit integrable norm bound supply the analytic estimates. Explicit spectral logarithms for the full marked heat operator prove this statement without claiming the separate general Borel-functional-calculus inverse result.

## Checks

- Reviewer independently elaborated the complete `SigmaOpResolventKernel.lean` and `SigmaOpHeatKernelNorm.lean` sources, and compiled `SigmaL2BochnerKernel.lean`.
- Reviewer checked transitive axioms for new kernel conclusions and principal ideal, trace, canonical-operator, and inverse conclusions: only `propext`, `Classical.choice`, and `Quot.sound`.
- Project source audit passed: no sorry, admit, sorryAx, or project axiom declarations.
- Whole project build passed.
- Repository-wide `SigmaAxioms.lean` print audit was running in the background at commit time; it is not recorded as finished here.

## O3-form clause review

The reviewer also passed native preservation of nonnegative real inputs, one, and the Gamma integral for all nonnegative times. `final:O3-form` remains **partial**: reverse weighted Sobolev-domain inclusion and the full sesquilinear identity remain. `final:O3` is also still partial.
