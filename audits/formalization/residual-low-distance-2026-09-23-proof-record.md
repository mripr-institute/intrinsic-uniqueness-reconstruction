# O2-boundaries completion and residual formalization milestone

Starting main: `502d9c74fe7c6bc7ece9e393820de3e87c69b15c`.
The only initial worktree item was the preserved untracked
`lean/SigmaProbCumulantCalibration.lean` experiment. It is neither imported nor
credited in this milestone. Paper statements and proofs are unchanged.

These are additions to the existing development, not replacement theories.
All status language below refers to Lean formalization, not to whether the
paper supplies mathematical proofs.

## Exact additions

| Paper item | Newly formalized components | Explicitly retained gaps |
|---|---|---|
| P5 | Native absolutely continuous probability hazard and marked-logistic inverses; survival continuity, integral representation and needed derivatives are derived from the Radon–Nikodym density. | Distributional Green inverse; actual Poisson-process second-arrival construction. |
| P6-boundaries | Native Stirling/Borel tail asymptotic and a distinct normalized probability with exactly the same tail from index three onward. | Smooth-density inverse-germ and non-Poisson offspring boundaries. |
| O2-boundaries | Actual self-adjoint operators on weighted complex L2 retain the constant and both probes but differ; the swapped operator has no local expression even a.e. Actual conservative reversible Gamma-refresh kernels preserve the positive ray, differ at every positive state and have explicit time rescaling. Together with existing smooth-positive probe irredundancy, the entire named proposition is complete. | None. |
| O3-spectrum | Exact Rodrigues formula; actual real/complex differential equations; weighted complex L2 membership; pairwise weighted integrals, inner products, orthonormality, unit norms, completeness and a native HilbertBasis. | Identification with the paper's actual self-adjoint differential domain, spectrum, compact resolvent and domain/energy formulas. |
| O5 | Actual finite signed/complex measure uniqueness from all integer Laplace samples, including zeroth-sample total mass; exact Gamma characterization. | Strong-operator mixing and extraction of samples from that operator identity. |
| M4 | Literal deterministic likelihood objective, covariance gap, unique SPD minimizer, singular unboundedness/nonattainment, actual finite sample scatter and Gram/PSD bridge. | Deriving likelihood from the actual multivariate Gaussian model; Wishart, sufficiency, KL and remaining probabilistic clauses. |
| R1 | Two distinct actual probability laws on Euclidean four-space with exactly the Gamma radial-energy law, distinguished by halfspace masses one and zero. | Native Gaussian/radial forward law, angular and invariant-law reconstruction, actual OU–Itô realization. |
| B4 | Native convergent numerical prime Euler product; convergence-derived bounded finiteness, countability and least real generator; empty-product criterion; convergent positive remainder after removing an entire multiplicity factor. | Actual operator trace, least-generator/multiplicity recovery limits, iterative full multiset reconstruction and uniqueness. |

## Independent adversarial review

The separate `coverage_realizations` agent compared complete paper clauses with
actual Lean signatures, and returned **AUDIT PASS for the corrected bounded
coverage**. It checked endpoints, arbitrary measure candidates, actual native
measure/operator categories, normalization, exact domains of scalar statements,
and retained assumptions. A subsequent whole-statement review returned
**AUDIT PASS for O2-boundaries**, which is promoted from partial to complete.

The whole-statement review caught one signature defect: initial refresh-kernel
distinctness was witnessed at zero, outside the positive state space. The
packaged theorem now proves different singleton transition probabilities at
**every positive state**. The reviewer rechecked the strengthened theorem and
found no remaining clause. The spectral counterexample uses equality with the
native partial-map adjoint, not just formal symmetry. The reversible dynamics
uses actual probability kernels and actual joint-measure detailed balance.
These alternative witnesses prove the named proposition; identifying the
compact-test minimal operator with the spectral construction is not assumed.

A fresh sample of previously complete O6 found an inherited mismatch:
`SigmaOpMarkedCalculus` supplies a genuine diagonal sequence-L2 calculus, but
there is no proved intertwining with the paper's weighted self-adjoint operator
A. O6 is therefore corrected to **partial**. Its scalar Bernstein uniqueness,
Levy-data recovery, and diagonal-model results are all retained. The absent
operator bridge is recorded explicitly; this milestone does not supply it.

Totals before inherited O6 correction: 80 items, 2 definitions, 47 complete,
21 partial, 10 missing. Corrected baseline: 2 definitions, 46 complete,
22 partial, 10 missing. After completing O2-boundaries:
**2 definitions, 47 complete, 21 partial, 10 missing**, with zero pending
classifications. The unchanged net total relative to the initial ledger
combines a real new completion with correction of the old O6 mapping.

## Integration and verification

All sixteen milestone modules are imported by Sigma and listed in the Lake library.
SigmaAxioms includes checks for the material new results. Existing signatures
were not weakened. The sole old project warning was removed by replacing the
unnecessary tactic sequencing in `gamma_rate_two_self_decomposition`.

The coverage rebuild script now generates the readable proved-result inventory
from the same independently reviewed maps as both coverage ledgers. This
removes its stale 41/27 counts without introducing a separate status source.

- Targeted compilation of each new module: PASS, no project warnings.
- Integrated `lake build SigmaFormalization`: PASS, no project-owned warnings.
- Source proof-escape audit: PASS; no sorry, admit, sorryAx or project axioms.
- Independent corrected-coverage audit: PASS.
- Full `Verify.py` for the preceding integrated ten-module residual batch:
  PASS, including the complete `SigmaAxioms.lean` run.
- Final sixteen-module milestone build and source proof-escape audit: PASS.
- All 1,268 current mapped declarations resolve in the integrated Sigma import:
  PASS.
- Every new milestone axiom check, rerun against the final integrated source:
  PASS, using only `propext`, `Classical.choice`, and `Quot.sound`. The final
  positive-state strengthening received separate explicit axiom checks too.

The full expanded `Verify.py` rerun was launched as well. Its build passed;
its repeated whole-project axiom traversal was still running when this record
was prepared. The milestone evidence above does not label that unfinished
rerun as a completed check.

Further local Euler-reconstruction, multivariate Gaussian/Wishart, radial
Gaussian and scatter-rank modules are preserved but not included in this
commit's imported development or completion counts. They will be integrated
at a separate independently reviewed milestone; this checkpoint does not
silently credit unimported work.

Upstream Mathlib doc-prime warnings remain untouched. Build logs are temporary
files outside the repository and are not committed.
