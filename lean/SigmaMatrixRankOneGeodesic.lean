import SigmaMatrixPiecewiseRankOneUnique

namespace Sigma
noncomputable section
open scoped Matrix Topology ComplexOrder
open MeasureTheory

attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

theorem rank_one_matrix_mul_comm (A B : Matrix (Fin 1) (Fin 1) ℝ) : A*B = B*A := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem rank_one_matrix_mul_entry (A B : Matrix (Fin 1) (Fin 1) ℝ) :
    (A*B) 0 0 = A 0 0 * B 0 0 := by simp [Matrix.mul_apply]

theorem matrix_exp_rankOneMatrix (x : ℝ) :
    NormedSpace.exp ℝ (rankOneMatrix x) = rankOneMatrix (Real.exp x) := by
  have he (z : ℝ) : rankOneMatrix z = Matrix.diagonal (fun _ : Fin 1 => z) := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  rw [he, he, matrix_exp_diagonal_real]

theorem rank_one_matrix_exp_entry (A : Matrix (Fin 1) (Fin 1) ℝ) :
    (NormedSpace.exp ℝ A) 0 0 = Real.exp (A 0 0) := by
  have h := matrix_exp_rankOneMatrix (A 0 0)
  rw [rankOneMatrix_entry] at h
  exact congrArg (fun B => B 0 0) h

theorem rank_one_matrix_spd_log_entry (A : Matrix (Fin 1) (Fin 1) ℝ) (hA : A.PosDef) :
    matrixSPDLog A hA 0 0 = Real.log (A 0 0) := by
  have ha : 0 < A 0 0 := (rankOneMatrix_posDef_iff _).mp (by rwa [rankOneMatrix_entry])
  apply Real.exp_injective
  rw [Real.exp_log ha, ← rank_one_matrix_exp_entry, matrix_exp_spd_log]

theorem rank_one_matrix_relative_entry (X Y : Matrix (Fin 1) (Fin 1) ℝ) (hX : X.PosDef) :
    matrixRelativeSPD X Y hX 0 0 = Y 0 0 / X 0 0 := by
  have hx : 0 < X 0 0 := (rankOneMatrix_posDef_iff _).mp (by rwa [rankOneMatrix_entry])
  have hi : X⁻¹ 0 0 = (X 0 0)⁻¹ := by
    have hh := rankOneMatrix_inv (X 0 0) (ne_of_gt hx)
    rw [rankOneMatrix_entry] at hh
    exact congrArg (fun B => B 0 0) hh
  unfold matrixRelativeSPD
  rw [rank_one_matrix_mul_comm hX.inv.posSemidef.sqrt Y, Matrix.mul_assoc,
    hX.inv.posSemidef.sqrt_mul_self, rank_one_matrix_mul_entry, hi, div_eq_mul_inv]

/-- The rank-one scalar interpolation is exactly the paper's native
square-root / matrix-exponential / spectral-log formula. -/
theorem rank_one_canonical_matrix_geodesic (X Y : Matrix (Fin 1) (Fin 1) ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) (s : ℝ) :
    matrixSPDGeodesic X Y hX hY s =
      rankOneMatrix (rankOneExponentialPath (X 0 0) (Y 0 0) s) := by
  have hx : 0 < X 0 0 := (rankOneMatrix_posDef_iff _).mp (by rwa [rankOneMatrix_entry])
  have hy : 0 < Y 0 0 := (rankOneMatrix_posDef_iff _).mp (by rwa [rankOneMatrix_entry])
  have hsqrt : hX.posSemidef.sqrt 0 0 * hX.posSemidef.sqrt 0 0 = X 0 0 := by
    rw [← rank_one_matrix_mul_entry, hX.posSemidef.sqrt_mul_self]
  ext i j
  fin_cases i
  fin_cases j
  change matrixSPDGeodesic X Y hX hY s 0 0 = rankOneExponentialPath (X 0 0) (Y 0 0) s
  unfold matrixSPDGeodesic matrixExponentialCurve
  rw [rank_one_matrix_mul_entry, rank_one_matrix_mul_entry, rank_one_matrix_exp_entry]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [rank_one_matrix_spd_log_entry, rank_one_matrix_relative_entry,
    Real.log_div (ne_of_gt hy) (ne_of_gt hx), rankOneExponentialPath, Real.exp_add, Real.exp_log hx]
  rw [← hsqrt]
  ring

theorem rank_one_matrix_geodesic_piecewise_admissible
    (X Y : Matrix (Fin 1) (Fin 1) ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    RankOnePiecewiseAdmissiblePath X Y (matrixSPDGeodesic X Y hX hY) := by
  have hx : 0 < X 0 0 := (rankOneMatrix_posDef_iff _).mp (by rwa [rankOneMatrix_entry])
  have hy : 0 < Y 0 0 := (rankOneMatrix_posDef_iff _).mp (by rwa [rankOneMatrix_entry])
  have he : matrixSPDGeodesic X Y hX hY =
      fun s => rankOneMatrix (rankOneExponentialPath (X 0 0) (Y 0 0) s) :=
    funext (rank_one_canonical_matrix_geodesic X Y hX hY)
  rw [he]
  apply rank_one_c1_path_piecewise_admissible
  simpa only [rankOneMatrix_entry] using
    rank_one_exponential_native_path_admissible (X 0 0) (Y 0 0) hx hy

theorem rank_one_matrix_geodesic_minimizing
    (X Y : Matrix (Fin 1) (Fin 1) ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    matrixHessianPathLength (matrixSPDGeodesic X Y hX hY) =
      rankOnePiecewiseHessianDistance X Y := by
  have he : matrixSPDGeodesic X Y hX hY =
      fun s => rankOneMatrix (rankOneExponentialPath (X 0 0) (Y 0 0) s) :=
    funext (rank_one_canonical_matrix_geodesic X Y hX hY)
  rw [he, rank_one_exponential_path_length, rank_one_piecewise_hessian_distance X Y hX hY]

theorem rank_one_matrix_geodesic_constant_speed
    (X Y : Matrix (Fin 1) (Fin 1) ℝ) (hX : X.PosDef) (hY : Y.PosDef) (s : ℝ) :
    matrixHessianSpeed (matrixSPDGeodesic X Y hX hY) s =
      rankOnePiecewiseHessianDistance X Y := by
  have he : matrixSPDGeodesic X Y hX hY =
      fun s => rankOneMatrix (rankOneExponentialPath (X 0 0) (Y 0 0) s) :=
    funext (rank_one_canonical_matrix_geodesic X Y hX hY)
  rw [he, rank_one_exponential_path_speed, rank_one_piecewise_hessian_distance X Y hX hY]

theorem rank_one_piecewise_distance_matrix_log_norm
    (X Y : Matrix (Fin 1) (Fin 1) ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    rankOnePiecewiseHessianDistance X Y =
      ‖matrixSPDLog (matrixRelativeSPD X Y hX) (matrix_relative_spd_positive X Y hX hY)‖ := by
  rw [← matrix_spd_geodesic_length X Y hX hY, rank_one_matrix_geodesic_minimizing X Y hX hY]

theorem rank_one_matrix_geodesic_unique_piecewise_minimizer
    (X Y : Matrix (Fin 1) (Fin 1) ℝ) (hX : X.PosDef) (hY : Y.PosDef)
    (γ : ℝ → Matrix (Fin 1) (Fin 1) ℝ) (hγ : RankOnePiecewiseAdmissiblePath X Y γ)
    (c : ℝ) (hc : ∀ᵐ s : ℝ ∂volume,
      s ∈ Set.Icc (0:ℝ) 1 → matrixHessianSpeed γ s = c)
    (hmin : matrixHessianPathLength γ = rankOnePiecewiseHessianDistance X Y) :
    Set.EqOn γ (matrixSPDGeodesic X Y hX hY) (Set.Icc (0:ℝ) 1) := by
  intro s hs
  rw [rank_one_canonical_matrix_geodesic]
  exact rank_one_piecewise_constant_speed_minimizer_unique X Y hX hY γ hγ c hc hmin s hs

end
end Sigma
