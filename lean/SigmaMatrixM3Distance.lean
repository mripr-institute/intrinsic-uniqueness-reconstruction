import SigmaMatrixLogPath
import SigmaMatrixPathClamp
import SigmaMatrixGlobalUnique

namespace Sigma
noncomputable section
open MeasureTheory
open scoped Matrix Topology
variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

/-- Logarithmic contraction for the original finite-piece path class. The
clamp merely extends the path outside the closed interval; it preserves the
original path, its derivative on the interior and its actual length. -/
theorem matrix_piecewise_log_endpoint_lower_bound
    (X Y : Matrix n n ℝ) (hX : X.PosDef) (hY : Y.PosDef)
    (γ : ℝ → Matrix n n ℝ) (hγ : MatrixPiecewiseAdmissiblePath X Y γ) :
    ‖matrixSPDLog Y hY - matrixSPDLog X hX‖ ≤ matrixHessianPathLength γ := by
  let δ := matrixClampedPath γ
  have hp : ∀ s, (δ s).PosDef := matrix_clamped_path_posDef γ hγ.2.2.2.1
  have hδ := matrix_clamped_path_admissible X Y γ hγ
  have hb := matrix_spd_log_piecewise_contraction X Y δ hδ hp
  have hb' : ‖CFC.log (δ 1) - CFC.log (δ 0)‖ ≤ matrixHessianPathLength δ := by
    simpa only [matrix_spd_log_eq_cfc_log] using hb
  have hd0 : δ 0 = X := hδ.1
  have hd1 : δ 1 = Y := hδ.2.1
  rw [hd0, hd1] at hb'
  change ‖CFC.log Y - CFC.log X‖ ≤ matrixHessianPathLength (matrixClampedPath γ) at hb'
  rw [matrix_clamped_path_length_eq] at hb'
  simpa only [matrix_spd_log_eq_cfc_log] using hb'

/-- The higher-rank global lower bound for every admissible SPD path. All
logarithmic regularity and the full finite-piece calculus are derived. -/
theorem matrix_piecewise_length_ge_spd_log_norm
    (X Y : Matrix n n ℝ) (hX : X.PosDef) (hY : Y.PosDef)
    (γ : ℝ → Matrix n n ℝ) (hγ : MatrixPiecewiseAdmissiblePath X Y γ) :
    ‖matrixSPDLog (matrixRelativeSPD X Y hX)
      (matrix_relative_spd_positive X Y hX hY)‖ ≤ matrixHessianPathLength γ := by
  let Q := hX.inv.posSemidef.sqrt
  have hQ : IsUnit Q := sqrt_positive_definite_isUnit X⁻¹ hX.inv
  have hQt : Qᵀ = Q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hX.inv.posSemidef.posSemidef_sqrt.isHermitian.eq
  let δ := fun s => matrixCongruence Q (γ s)
  have hy : matrixCongruence Q Y = matrixRelativeSPD X Y hX := by
    change Q * Y * Qᵀ = Q * Y * Q
    rw [hQt]
  have hδ : MatrixPiecewiseAdmissiblePath 1 (matrixRelativeSPD X Y hX) δ := by
    simpa only [matrix_inverse_sqrt_whitens X hX, hy] using
      matrix_congruence_piecewise_admissible Q hQ X Y γ hγ
  have hb := matrix_piecewise_log_endpoint_lower_bound 1 (matrixRelativeSPD X Y hX)
    Matrix.PosDef.one (matrix_relative_spd_positive X Y hX hY) δ hδ
  rw [matrix_spd_log_identity, sub_zero] at hb
  exact hb.trans_eq (matrix_congruence_path_length_eq Q hQ X Y γ hγ)

/-- The actual variational distance, defined as the infimum over the full
finite-piece SPD path class, has the paper's Frobenius-log formula. -/
theorem matrix_piecewise_hessian_distance_eq_spd_log_norm
    (X Y : Matrix n n ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    matrixPiecewiseHessianDistance X Y =
      ‖matrixSPDLog (matrixRelativeSPD X Y hX)
        (matrix_relative_spd_positive X Y hX hY)‖ := by
  apply le_antisymm (matrix_piecewise_distance_le_spd_log_norm X Y hX hY)
  apply le_csInf
  · exact ⟨_, ⟨matrixSPDGeodesic X Y hX hY,
      matrix_spd_geodesic_admissible X Y hX hY, rfl⟩⟩
  · rintro r ⟨γ, hγ, rfl⟩
    exact matrix_piecewise_length_ge_spd_log_norm X Y hX hY γ hγ

theorem matrix_spd_geodesic_globally_minimizing
    (X Y : Matrix n n ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    matrixHessianPathLength (matrixSPDGeodesic X Y hX hY) =
      matrixPiecewiseHessianDistance X Y := by
  rw [matrix_spd_geodesic_length X Y hX hY,
    matrix_piecewise_hessian_distance_eq_spd_log_norm X Y hX hY]

end
end Sigma
