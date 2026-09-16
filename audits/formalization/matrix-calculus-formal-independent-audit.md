Independent audit of the native matrix calculus

The calculus components of `final:M2` are proved by the checked module `outputs/lean/SigmaFinalMatrixCalculus.lean`. The full M2 theorem remains partial. This review read the exact statements and proofs against `series-realizations.tex`, checked the underlying definitions in `SigmaFinalRealMatrix.lean`, and compiled an independent wrapper for the manuscript Hessian. No root source was edited.

The actual determinant is globally differentiable: the proof expands its finite Leibniz sum and uses native derivatives of the coordinate maps and products. The polynomial identity for `det(1+t U)` computes the derivative at the identity. Factoring `X+t U` through an invertible `X` and comparing genuine derivatives yields Jacobi's formula for the native `fderiv`. The invertibility assumption is precisely `IsUnit X.det`; positive definiteness supplies it in M2.

The potential is literally `trace X - log(det X) - card n`. Its native Frechet differential is proved to be `U` mapped to `trace((1-X inverse)U)`. Native matrix inverse differentiation comes from the Banach-algebra inverse theorem and establishes the actual derivative of the map `X` mapped to `1-X inverse`. The supplied proof uses the Frobenius normed-ring and normed-algebra structures. The independent check activates those same structures.

The gradient statement is expressed through the trace-pairing differential. This is exactly the draft's affine convention on symmetric matrices: at an SPD matrix, `1-X inverse` is symmetric, and the trace pairing agrees with the Frobenius pairing on symmetric tangents. The definition `matrixGradient` does not by itself assert that this is a native Riesz gradient on every nonsymmetric matrix. No such assertion is needed or used.

The strongest Hessian theorem is `matrixPotential_second_fderiv`, not just `matrix_hessian_metric`. It differentiates the actual function `Y` mapped to `fderiv matrixPotential Y U`. The proof first constructs a genuine `HasFDerivAt` for the trace pairing of the gradient map, then proves eventual equality with the actual first derivative using continuity of the determinant and its nonzero value at `X`. This avoids any assumption that the SPD cone is open in the full ambient matrix space. The open set of nonsingular matrices supplies a valid local extension of the potential; `Real.log(det X)` agrees with the draft on SPD matrices.

The resulting formula is `trace(X inverse V X inverse U)`. Cyclic trace changes this to the displayed manuscript order `trace(X inverse U X inverse V)`. The independent theorem `SigmaFinalIndependentAudit.manuscript_matrix_hessian` compiles with the exact symmetric-tangent interface and performs this conversion. Derivative existence is established inside the checked proof, so the totalized definition of `fderiv` is not concealing a nonexistent derivative. The representation is the actual Frechet derivative of the first derivative evaluated at a fixed direction, rather than a separately bundled second-derivative tensor.

The Bregman theorem now uses the actual `fderiv matrixPotential Y (X-Y)`, closing the earlier gap between a specified covector expression and a differential Bregman divergence. The existing native matrix file separately provides nonnegativity, the exact diagonal zero set, congruence invariance, inversion reversal, and the exponential determinant bound with equality.

The following M2 components still require proof:

- Strict Hessian positivity for every nonzero symmetric tangent, beyond the existing nonnegativity result.
- Congruence invariance and inversion isometry of the Hessian metric.
- The full extended-real conjugate, its exact domain and optimizer, Legendre inverse, and Bregman duality.
- The arithmetic-mean determinant bound, its scalar-matrix equality case, and strict concavity of `logdet`.
- The accompanying calibrated gradient/Hessian reconstruction converses and the positive parameter range for the alternative invariant metrics.

M3 geodesics and M4 Gaussian/Wishart claims are separate statements and are not covered by this calculus module. No full M2 or broader matrix-network completion is claimed.

Verification: `python3 work/final_lean.py work/SigmaFinalMatrixCalculusAuditCheck.lean` passed. All 13 module theorems and the independent manuscript wrapper depend only on `propext`, `Classical.choice`, and `Quot.sound`. Exact module hashes, theorem mappings, and the dependency record are in `matrix-calculus-lean-map.json` and `matrix-calculus-axiom-audit.json`; compiler output is in `work/final-SigmaFinalMatrixCalculusAuditCheck.log`.
