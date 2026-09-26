# O4 finite countermodels: independent paper-to-Lean review

Date: 2026-09-27. Reviewer: `/root/paper_coverage_review` (read-only independent agent).

## Verdict

**COMPLETE PASS for `final:O4-finite-countermodels`. No named-statement residuals remain.**

- Arbitrary finite real regular samples are covered by the `Finset ℝ` parameter.
- The continuous local family starts at the canonical operator and is nonconstant. Every sufficiently small nonzero parameter creates a spectral value absent from the original spectrum.
- Actual maximal native diagonal operators are nonnegative and self-adjoint. Only finitely many positive eigenvalues change, and their domains remain equal to the original domain.
- The entire finite correction is identified with the actual diagonal nuclear trace on Re(s)>1. All specified continued zeta values are preserved.
- The optional finite part at one and literal exp(-derivative at zero) determinant are preserved simultaneously.
- Entire corrections preserve all poles and principal parts, the residue at one, regularity exactly away from one, and the value at zero.

## Verification and scope

All three frozen source files independently elaborated. Targeted transitive axiom checks for the top theorem, local curve, actual changed spectrum, native nuclear trace, principal parts, finite part and common domain returned only `propext`, `Classical.choice`, and `Quot.sound`.

The proof uses geometric integer indices and a Vandermonde argument in place of the paper's general exponential-zero-count argument. Explicit two- and three-eigenvalue examples, the general level-manifold dimension statement, and a separate perturbed compact-resolvent theorem are proof-only details not asserted by this formalization; they omit no clause of the named theorem.
