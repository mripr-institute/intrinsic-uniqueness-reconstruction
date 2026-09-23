# Completed B4 trace and arithmetic reconstruction

Starting commit: `52dd45a8e5557ef79265cd0f08c0bbd25c07017b`.

Reused and integrated the preserved local `SigmaArithmeticEulerRecovery`,
`SigmaArithmeticEulerErase`, and `SigmaArithmeticEulerUnique` modules. They prove
both displayed limits, full-factor removal, complete multiplicity reconstruction
and a genuine inverse on the terminal-ray positive-product candidate class.
No countability, local finiteness or multiplicative independence is imposed.

Added the genuinely missing operator layer:

- `SigmaOpNuclearTrace`: standard nuclear rank-one representations of actual
  bounded operators, absolute diagonal summability, representation trace formula
  and basis independence. The pinned Mathlib has no infinite-dimensional trace
  API, so these are proved rather than replaced by scalar trace definitions.
- `SigmaOpDiagonalNuclear`: nuclearity iff absolute summability for an actual
  operator diagonal in a complete Hilbert basis, with the genuine trace formula.
- `SigmaOpIntegerEigenbasis`: native self-adjointness and the supplied complete
  simple integer eigenbasis derive the exact maximal weighted domain and action.
- `SigmaOpIntegerEigenbasisInverse`: actual two-sided bounded inverse of 1+A.
- `SigmaOpZetaTrace`: maximal complex powers, exact trace-class iff for every
  complex s, trace equal to native riemannZeta, and identification of power one
  with that actual inverse. No boundedness restriction is added to the iff.

Fresh whole named-statement independent adversarial audit: PASS. It checked both
the numerical inverse and the operator definitions, domains and parameter range.

Single integration gate: source proof-escape audit PASS; full SigmaFormalization
build PASS, including all preserved arithmetic modules; final transitive axiom
checks PASS. Only propext, Classical.choice and Quot.sound occur. Project-owned
warnings: zero. SigmaAxioms is synchronized; no repeated broad verifier was run.

Coverage: 80 named items; 2 definitions, 54 complete, 16 partial, 8 missing.
Other pre-existing uncommitted proofs and experiments remain outside this commit.
