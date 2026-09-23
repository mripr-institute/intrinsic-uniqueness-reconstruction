# O4 compact-resolvent convergence boundary

Target: `final:O4-convergence-boundary` in `paper/sections/operators.tex`.

The paper asks for one nonnegative diagonal self-adjoint operator with compact
resolvent whose heat trace and every positive shifted-zeta trace diverge. The
Lean witness uses the alternative eigenvalue sequence
`lambda_n = sqrt (log (n + 3))`. It tends to infinity, so the native maximal
diagonal operator has compact shift-one resolvent; its resolvent satisfies
both inverse equations. The operator is self-adjoint and nonnegative on its
actual weighted-L2 domain. For every positive heat parameter and positive
zeta parameter, the coefficient tails dominate a divergent
`(n + 3)^(-1/2)` series, proving the actual diagonal heat and shifted-zeta
operators are not trace class.

The declarations are in `lean/SigmaOpConvergenceBoundary.lean`. Its public
theorem `Sigma.compact_resolvent_without_positive_traces` packages the exact
existential boundary clause. The exact-statement independent audit and
declaration map are in `audits/formalization/current-operator-audit.json`.
