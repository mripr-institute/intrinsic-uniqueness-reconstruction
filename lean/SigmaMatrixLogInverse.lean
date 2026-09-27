import SigmaMatrixGeodesic
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog

namespace Sigma
noncomputable section
open scoped Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

/-- The native spectral logarithm is the continuous functional calculus logarithm. -/
theorem matrix_spd_log_eq_cfc_log (A : Matrix n n ℝ) (hA : A.PosDef) :
    matrixSPDLog A hA = CFC.log A := by
  rw [CFC.log, hA.isHermitian.cfc_eq]
  simp only [matrixSPDLog, Matrix.IsHermitian.cfc, RCLike.ofReal_real_eq_id,
    Function.comp_def, id_eq]

/-- The matrix exponential is injective on the real symmetric matrices. -/
theorem matrix_exp_symmetric_injective (Z W : Matrix n n ℝ)
    (hZ : Z.IsSymm) (hW : W.IsSymm)
    (h : NormedSpace.exp ℝ Z = NormedSpace.exp ℝ W) : Z = W := by
  have hZ' : IsSelfAdjoint Z := by
    simpa only [IsSelfAdjoint, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hZ
  have hW' : IsSelfAdjoint W := by
    simpa only [IsSelfAdjoint, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hW
  simpa only [CFC.log_exp Z hZ', CFC.log_exp W hW'] using congrArg CFC.log h

/-- Applying the actual spectral logarithm to a symmetric matrix exponential
recovers the matrix, including repeated eigenvalues. -/
theorem matrix_spd_log_exp (Z : Matrix n n ℝ) (hZ : Z.IsSymm)
    (hA : (NormedSpace.exp ℝ Z).PosDef) :
    matrixSPDLog (NormedSpace.exp ℝ Z) hA = Z := by
  apply matrix_exp_symmetric_injective _ _ (matrix_spd_log_symmetric _ _) hZ
  exact matrix_exp_spd_log _ hA

/-- There is precisely one symmetric logarithm of an SPD matrix. -/
theorem matrix_symmetric_log_unique (A Z : Matrix n n ℝ) (hA : A.PosDef)
    (hZ : Z.IsSymm) (hexp : NormedSpace.exp ℝ Z = A) :
    Z = matrixSPDLog A hA := by
  apply matrix_exp_symmetric_injective _ _ hZ (matrix_spd_log_symmetric _ _)
  rw [hexp, matrix_exp_spd_log]

end
end Sigma
