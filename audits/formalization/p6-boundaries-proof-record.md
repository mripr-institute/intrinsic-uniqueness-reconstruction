# Completed P6 deletion boundaries

Starting commit: `ce3c5f8e912a935bb9e1d38d5fc1353d022c0d2a`.

Reused the existing native rooted path/star probability countermodels and exact
Borel-tail perturbation. Added only the two remaining witnesses:

- `SigmaProbSmoothDensityBoundary.lean`: a nonzero compactly supported derivative
  bump preserves normalization, positivity, both inverse germs, the unique
  canonical maximum, strict branch monotonicity and endpoint limits. The new
  smooth density differs even up to almost-everywhere equality.
- `SigmaRealTreesCriticalBoundary.lean`: an actual iid constant-one offspring
  array has mean one. Its active-word tree has exactly one vertex per generation,
  and its total-progeny probability law is concentrated at infinity, unlike Borel.

Whole named-statement independent adversarial audit: PASS. The criticality-alone
statement does not assume nondegeneracy or extinction. This witness does not
formalize the stronger finite-extinct binary example in the paper's proof, nor
the separate forest-marginal nonindependence discussion.

One integration gate: source proof-escape audit PASS; full SigmaFormalization
build PASS; final transitive axiom checks PASS (only `propext`, `Classical.choice`,
`Quot.sound`). No project-owned warning was emitted. SigmaAxioms is synchronized.

Coverage: 80 named items; 2 definitions, 51 complete, 19 partial, 8 missing.
Other uncommitted proof development remains outside this milestone.
