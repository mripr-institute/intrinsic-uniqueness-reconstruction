# Formal characteristic-series coverage

This scope audit compares `final:F1` and `final:F2` in `series-realizations.tex` with the actual native `PowerSeries` declarations listed in `realization-lean-map.json`. It records the author's statement check; it is not an independent review of these proofs.

## F1

The normalized Todd quotient is constructed from the native formal exponential by inverting the constant-one series `(1-exp(-X))/X`. The division by `X` is represented by coefficient shift, with its multiplication identity proved. No inverse of the nonunit `X` is used.

Formal differentiation gives the exact Riccati identity of this quotient. The derivative of its exponentially twisted powers gives a coefficient recurrence, which proves the displayed rising-factorial formula at every scalar twist. The rational twist polynomial is also proved equal to the rising-factorial polynomial, and its evaluation transports the formula to every commutative rational algebra. This is a proof of the draft's same statement by formal differentiation; the implementation does not claim a generic Laurent residue-substitution library theorem.

Triangular coefficient comparison proves normalized uniqueness and identifies the previously recursive rational tower with this actual quotient. The degree-zero equation is exactly normalization. Removing any individual positive-degree equation yields an explicit different tower over every characteristic-zero field.

The additional arbitrary-unit family in the proof prose is now constructed by well-founded coefficient recursion. `unnormalized_todd_family_over_Q_algebra_exists_unique` gives a unique series with any prescribed constant unit and all retained positive-degree tower observations equal to one. This theorem allows zero divisors and does not divide by a coefficient that has not been proved invertible. `unnormalized_todd_over_parameter_injective` proves that distinct marked units give distinct series. The corresponding field theorem is also available.

**Remaining:** the separate finite multi-index formula `final:todd-arbitrary-power` is not formalized. It is retained unchanged in the draft and is explicitly recorded as an obligation. The displayed F1 tower and all-twist theorem are proved.

## F2

`formalAhat`, `formalL`, and `formalChi` are the actual standard quotients or marked affine Todd expression, with constant-one normalization proved. The native quotient identities use the actual exponentials, not abstract units assumed to represent the named characteristic series. Both directions of the Todd/L and Todd/chi reconstruction maps are proved, together with the actual Todd/Ahat relations and both exponential-recovery formulas.

The square root used to reconstruct Todd from Ahat is explicitly constructed as `exp(X/2)+exp(-X/2)`. Its equation and constant term two are proved. Any other root with the required constant term equals this root: the factorized difference is annihilated by a series whose constant term is four, a unit in every rational algebra. Thus the reconstruction uses the prescribed formal branch and does not assume that its output already equals the exponential or Todd series.

The field chi inverse requires exactly `y != -1`. For arbitrary coefficient rings its general affine inverse is proved from a scalar unit, with no field assumption. The actual standard series over rational algebras then use exactly `IsUnit (1+y)`. `CharacteristicParameterRing` is the native localization of `Polynomial Rational` away from `1+X`; its unit condition and the resulting inverse substitution are instantiated explicitly. The degenerate specialization is `1+X`; an explicit pair of distinct normalized input series proves loss of injectivity at `y=-1`.

The rational-algebra versions of Todd, Ahat, and L are maps of the already proved rational standard quotients, packaged as genuine formal units. Their quotient and reconstruction equations are transported through the actual ring homomorphism, so these are identified standard series even over coefficient rings with zero divisors. Inversion of each standard unit is an involution. All displayed F2 formal claims are covered.

## Boundary of this result

F2 does not identify arbitrary global smooth functions from a formal series, and this audit does not count the F3 analytic continuation and global-extension assertions as proved. Native topology, the remaining matrix geometry and statistics, and the remaining arithmetic inventory obligations keep their separate statuses in the exact map. No incomplete theorem group is relabeled complete because F1/F2 progressed.

The pinned Lean compiler, per-file theorem names and hashes, build order, and kernel axiom report are recorded in `realization-lean-map.json`. The additional localization library module was compiled locally from the existing mathlib source.
