# Complete M2 matrix duality and determinant clauses

Parent milestone: `061b289be4c5642416e9640048accbe74a4917a8`, pushed to main.

The arithmetic-mean determinant inequality is derived by rescaling the actual
SPD matrix to trace equal to rank and reusing the exponential determinant bound.
The equality case is exactly the positive scalar matrix. Strict concavity of
log determinant on the actual SPD cone follows from the existing strict
Bregman divergence and a weighted trace cancellation; it is not assumed.

`SigmaMatrixFenchel` defines the literal extended-real primal function (infinity
outside SPD) and its full supremum over matrices. The gap identity gives the
finite conjugate and its unique optimizer. Both Legendre round trips are proved.
For a symmetric dual matrix outside the finite domain, a nonpositive eigenvalue
produces an actual SPD spectral ray on which the objective is unbounded. This
includes the zero-eigenvalue endpoint, so the full finite/infinite formula is
exact. No spectral formula is substituted for an actual supremum.

Independent review returned AUDIT PASS for the entire named M2 statement and
the separately labelled matrix-conjugate formula. Their residual lists are now
empty. The reviewer retained separate notes about adjacent unformalized prose
claims (dual-Bregman equality, marked affine converses and alternative metrics);
this milestone does not assert those or whole-paper completeness.

Validation: aggregate build PASS, zero project-owned warnings; source audit
PASS; thirteen new material axiom checks PASS using only propext,
Classical.choice and Quot.sound. All coverage declarations elaborate.
Named-statement totals: 2 definitions, 33 complete, 32 partial, 13 missing.
The independent probability proving subagent's in-progress files are not part
of this commit and are not imported or credited yet.
