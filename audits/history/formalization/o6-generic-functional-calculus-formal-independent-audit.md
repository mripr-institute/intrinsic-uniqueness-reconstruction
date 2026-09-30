# O6 functional-calculus inverse: whole-statement independent audit

> **Historical record.** Statuses, counts, commands and local paths below describe
> the recorded stage, not the current checkout. See [current coverage](../../lean-coverage.md)
> and the [archive guide](../README.md).

**AUDIT PASS.**

Scope: only the complete proposition `final:O6-functional-calculus` and its
proof in `paper/sections/operators.tex`, lines 919–940. The generic clause is
checked against `SigmaOpNonnegativeResolvent.lean`, `SigmaOpCFCEigen.lean`,
`SigmaOpBorelInverse.lean`, and `SigmaOpBernsteinInverse.lean`. The canonical
clause reuses the bounded PASS record in
`o6-canonical-inverse-formal-independent-audit.md`.

## Generic operator clause

- The underlying input is an arbitrary native self-adjoint `LinearPMap` on
  a complex Hilbert space with its full domain. `OpNonnegative` is its actual
  nonnegative quadratic form. No compactness, separability, discrete spectrum,
  eigenbasis, or supplied resolvent is assumed.
- The bounded `opNonnegativeResolvent` is constructed from the inverse of
  `1+B` on its dense range. Its extension is proved to have image in the
  original native domain and satisfy both inverse equations. Self-adjointness,
  positivity, contraction, injectivity and its spectral inclusion in `[0,1]`
  are derived. This is the genuine shifted inverse, not a coordinate formula.
- For the known scalar function, the resolvent transform
  `q(r)=(1+f(r⁻¹-1))⁻¹` on `r>0` is extended at zero by its infimum limit.
  Continuity and strict increase on the full compact interval are proved.
  No zero endpoint limit is assumed: bounded strictly increasing functions,
  for which the added endpoint can be positive, are included.
- `opFunctionalResolvent` is the actual native bounded continuous functional
  calculus `q((1+B)⁻¹)`. Its injectivity and dense range are proved. The
  unbounded `opMonotoneFunctionalCalculus` is inverse-minus-identity on its
  entire range, with native self-adjointness and nonnegativity derived.
  This is a standard resolvent construction of the unbounded continuous
  functional calculus: on a spectral coordinate `r=(1+λ)⁻¹`, its scalar
  action is `q(r)⁻¹-1=f(λ)`. It uses genuine bounded CFC and native operator
  inverses; no additional scalar series or algebraic surrogate substitutes
  for the operator.
- The exact domain is proved to be the full range of that transformed
  resolvent, the natural maximal domain of this calculus. No finite-span
  restriction or incorrect inverse-image domain of an algebraic composition
  is introduced.
- `opKnownMonotoneInverse` takes the observed full native operator `C`, its
  derived self-adjointness/nonnegativity, and the retained known function.
  It constructs `(1+C)⁻¹`, applies the known inverse compact transform by
  actual CFC, then takes the native inverse-minus-identity. Reconstruction
  equals the original `B` as a whole native operator, not only on its domain
  core. The separate domain theorem gives equality of the complete domains.
  Equality of observations also proves equality of the original operators.
- The added endpoint has zero eigenspace, proved by CFC inverse recovery and
  injectivity of the original resolvent. This covers both a zero and a
  positive limiting transformed endpoint. An unattained limiting endpoint
  therefore contributes no spectral projection mass. The proof uses bounded
  resolvent coordinates instead of constructing an unrestricted Borel
  calculus API; it proves the same operator inverse and exact native domain.

## Original Bernstein hypotheses

The initial generic results explicitly used scalar continuity and
nonnegativity. The independent review identified the need to derive those
properties from the project's existing Bernstein representation category
before claiming exact paper coverage. `SigmaOpBernsteinInverse.lean`
addresses this:

- `BernsteinRepresentation.exponent_nonnegative` follows from its actual
  nonnegative killing/drift terms and positive-support Lévy integral.
- `BernsteinRepresentation.exponent_continuous` derives continuity on the
  closed nonnegative ray, including zero, by dominated convergence. The
  dominating function is a constant multiple of `min(1,x)`, whose
  integrability is exactly the existing representation premise.
- `HasBernsteinRepresentation.nonnegative` and `.continuous` transfer these
  results to the existing paper category without added hypotheses.
- `op_known_bernstein_inverse_reconstruction`,
  `op_known_bernstein_inverse_domain`, and
  `op_bernstein_functional_calculus_determines_operator` consequently take
  only the original nonnegative self-adjoint operator, membership in that
  Bernstein category, and the paper's strict-increase premise. Regularity
  is not imposed separately.

## Canonical clause and scope

The prior canonical audit proves the actual squared two-sided resolvent's
negative logarithm equals the maximal native `2 log(1+A)` multiplier,
including full domain, action, self-adjointness, zero endpoint independence,
and both operator reconstruction directions. That result is retained.

Together the generic Bernstein inverse and the canonical equivalence cover
both assertions of the named proposition. This does not audit or complete
the distinct unknown-function inverse question `final:O6`, the mixing
theorem `final:O5`, or unrelated F5 construction work.

## Verification evidence

The proving agent supplied PASS for integration build
`lake build SigmaFormalization`, `Verify.source_audit()`, and ten selected
O6/F5 final transitive axiom checks (only `propext`, `Classical.choice`, and
`Quot.sound`) before addition of the scalar-category wrapper. Targeted
kernel compilation and olean generation for `SigmaOpBernsteinInverse.lean`
subsequently passed with clean output, as supplied by its proving agent.
Four further selected transitive axiom checks for Bernstein continuity,
reconstruction, exact domain and operator determination passed, using only
`propext`, `Classical.choice`, and `Quot.sound`, as supplied by that agent.
This auditor did not redundantly run global checks. Subsequent integration
checks are the parent agent's responsibility.

No strengthened operator assumptions, hidden reconstruction conclusions,
weakened inverse directions, or lost domain/endpoint cases were found in
the inspected sources. The original scalar-category bridge is now present
and kernel-checked. Every formerly unproved component of the named
proposition is covered.
