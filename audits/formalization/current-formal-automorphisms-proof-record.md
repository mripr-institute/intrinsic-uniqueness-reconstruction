# Exact C3 automorphism classification

Terminology: this record concerns Lean formalization of proofs supplied in the paper. Coverage gaps refer to Lean, not to unproved mathematical results.

Parent milestone: `8f36146`.

`SigmaFormalAutomorphisms.lean` closes the previously remaining formal clause of
`final:C3-automorphisms`. The complete named proposition is now **complete**.

The proof uses the full bivariate formal group identity, not an assumed tangent
ODE. The actual Taylor pullback agrees with native powers of X+Y+XY and has the
proved total-degree locality. The identity implies the tangent ODE, which gives
the binomial classification. The converse full identity is proved. Genuine finite
coefficient substitution agrees with native polynomial evaluation for zero-constant
inner series. Composition multiplies parameters, both inverse compositions are
proved, and the nonzero tangent is derived from an actual inverse. Calibration and
all characteristic-zero-field scalar parameters are covered.

Independent reviewer `/root/coverage_realizations`: **AUDIT PASS** for the entire
named proposition, rechecking the older real continuity/measurability/monotonicity,
wild counterexample, signed-integer, inverse and calibration clauses as well.
The proposition explicitly uses characteristic-zero fields for the formal clause;
the separate later rational-algebra scope of Todd identities is not conflated here.

- Aggregate compilation: PASS, zero project-owned warnings.
- Source proof-escape audit: PASS.
- New public axiom checks added to `SigmaAxioms.lean`; focused check uses only
  `propext`, `Classical.choice`, `Quot.sound`.
- Coverage JSON and Markdown regenerated; exact residual array is empty for C3.

Named totals: 2 definitions, **37 complete, 31 partial, 10 missing**.
Other work in progress is excluded from this milestone.
