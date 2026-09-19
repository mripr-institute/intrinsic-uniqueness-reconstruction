# Actual radial calculus, subordinator drift, and SPD symmetrization

Terminology: this record concerns Lean formalization of proofs supplied in the paper. Coverage gaps refer to Lean, not to unproved mathematical results.

Parent: `d834fd899e82a4948b559485cb6ed741978ec61b`, pushed to main.

R3 is complete. The Laplacian is defined as the sum of actual second
directional derivatives along an arbitrary finite orthonormal basis. The
radial formula is derived from those derivatives, not built into the
definition, and only ordinary twice differentiability is used. Existing
conjugation, cancellation and nonidentification theorems supply the other
clauses. The origin is excluded exactly where the radial formula requires it.

R1's actual gradient, Laplacian and OU differential-operator computation is
also covered. Independent review caught an unnecessary zero-energy
differentiability premise in the initial off-origin interface. A local
eventual-equality proof now handles profiles differentiable only on the
positive ray. The separate origin-inclusive interface is retained. Actual
Gaussian-law and OU-process construction clauses remain open.

Probability additions prove the actual correlated-process deletion witness,
complete monotonicity of the Gamma Lévy density at every derivative order,
complete-Bernstein representation, and the Stieltjes witness 2 delta-one.
Drifted Gamma laws are actual translated measures with support [d,infinity)
and mean d+2. All four drift tests identify the actual convolution family,
and probability mass derives absence of killing. The native supplied-process
bridge derives convolution from stationary independent increments, transfers
the four tests to actual marginals and expectations, and constructs drift
transforms on the original probability space. The latter is explicitly
conditional on a supplied canonical process. Nonvacuous global process
existence/extension remains the shared P8/P8-levy residual.

M3 is now partial rather than missing: the exact symmetrization formula uses
the genuine relative SPD matrix, native positive square root, whitening,
and actual Hermitian eigenvalues. No surrogate distance is defined. Actual
geodesic/minimal-distance and equal-distance boundary obligations remain.

Independent bounded reviews PASS for R3, corrected R1 calculus, the probability
boundary/regularity/drift/native-process batches, and M3 symmetrization.
Aggregate build PASS with zero project-owned warnings; source proof-escape
and focused material axiom checks PASS, only standard Lean foundations.
New material declarations are synchronized in SigmaAxioms.

Named totals: 80 = 2 definitions + 36 complete + 32 partial + 10 missing.
The increase from 31 to 32 partial items is M3 moving out of missing, not a
regression of a complete statement. Whole-paper completion is not claimed.
The ongoing matrix-geodesic file is not part of this milestone.
