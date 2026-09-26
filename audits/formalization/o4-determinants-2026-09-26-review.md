# O4-determinants: independent canonical construction review

Date: 2026-09-26. Reviewer: `/root/paper_coverage_review` (read-only independent agent).

## Verdict

**PASS for canonical compression constructions and formulas. The proposition remains partial.**

The matrices are genuine finite Hilbert-basis compressions of the native resolvents. The ordinary approximants use the squared resolvent; the regularized approximants use the first resolvent and the correct exponential trace correction. Both sequences converge at every complex argument. The limits satisfy the stated sinh power-series and reciprocal-Gamma identities, are entire, and have exactly the canonical zeros with simple multiplicity. The square-root quotient is branch independent with value one at zero. The Gamma formula includes its poles correctly.

Both complete sources independently elaborated successfully. Targeted transitive axioms for finite products, convergence, entire formulas, zero sets, and simple zeros were only `propext`, `Classical.choice`, and `Quot.sound`.

## Residual obligations

- Identify these canonical limits with basis-independent ordinary Fredholm and Hilbert-Schmidt regularized determinants. Only fixed-basis finite-cutoff convergence is currently proved; basis/exhaustion independence and local uniform or unordered convergence are not.
- Establish the continued Hurwitz derivative at zero, all-positive-shift zeta determinant formula, both special values and zero-mode conventions.
- Prove reconstruction among competing nonnegative operators from zero multisets with multiplicities in both stated determinant categories.
