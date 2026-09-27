import SigmaMatrixGlobalGeodesic

namespace Sigma
noncomputable section
open scoped Matrix Topology ComplexOrder BigOperators
open MeasureTheory

variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

theorem matrix_congruence_hasDerivAt (C : Matrix n n ℝ)
    {γ : ℝ → Matrix n n ℝ} {s : ℝ} {U : Matrix n n ℝ}
    (hγ : HasDerivAt γ U s) :
    HasDerivAt (fun t => matrixCongruence C (γ t)) (matrixCongruence C U) s := by
  unfold matrixCongruence
  exact (hγ.const_mul C).mul_const Cᵀ

theorem matrix_congruence_speed_eq (C : Matrix n n ℝ) (hC : IsUnit C)
    {γ : ℝ → Matrix n n ℝ} {s : ℝ} {U : Matrix n n ℝ}
    (hγ : HasDerivAt γ U s) :
    matrixHessianSpeed (fun t => matrixCongruence C (γ t)) s =
      matrixHessianSpeed γ s := by
  simp only [matrixHessianSpeed, (matrix_congruence_hasDerivAt C hγ).deriv,
    hγ.deriv, hessianMetric_congruence (γ s) U U C hC]

theorem matrix_congruence_segment_length_eq (C : Matrix n n ℝ) (hC : IsUnit C)
    (γ : ℝ → Matrix n n ℝ) (v : ℝ → Matrix n n ℝ) (a b : ℝ)
    (hab : a ≤ b) (hd : ∀ s ∈ Set.Ioo a b, HasDerivAt γ (v s) s) :
    (∫ s : ℝ in a..b, matrixHessianSpeed
      (fun t => matrixCongruence C (γ t)) s) =
      ∫ s : ℝ in a..b, matrixHessianSpeed γ s := by
  apply intervalIntegral.integral_congr_ae
  have hna : ∀ᵐ s : ℝ ∂volume, s ≠ a := by simp [ae_iff]
  have hnb : ∀ᵐ s : ℝ ∂volume, s ≠ b := by simp [ae_iff]
  filter_upwards [hna, hnb] with s hsa hsb hs
  rw [Set.uIoc_of_le hab] at hs
  exact matrix_congruence_speed_eq C hC
    (hd s ⟨hs.1, lt_of_le_of_ne hs.2 hsb⟩)

theorem matrix_congruence_piecewise_admissible (C : Matrix n n ℝ) (hC : IsUnit C)
    (X Y : Matrix n n ℝ) (γ : ℝ → Matrix n n ℝ)
    (hγ : MatrixPiecewiseAdmissiblePath X Y γ) :
    MatrixPiecewiseAdmissiblePath (matrixCongruence C X) (matrixCongruence C Y)
      (fun s => matrixCongruence C (γ s)) := by
  rcases hγ with ⟨h0, h1, hc, hp, N, a, v, hN, ha0, haN, ha, hstep, hv⟩
  have hCt : IsUnit Cᵀ := (Matrix.isUnit_iff_isUnit_det _).mpr (by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hC)
  have hcont (δ : ℝ → Matrix n n ℝ) (l r : ℝ)
      (h : ContinuousOn δ (Set.Icc l r)) :
      ContinuousOn (fun s => matrixCongruence C (δ s)) (Set.Icc l r) := by
    unfold matrixCongruence
    exact (continuousOn_const.mul h).mul continuousOn_const
  refine ⟨by simp [h0], by simp [h1], hcont γ 0 1 hc, ?_,
    N, a, (fun j s => matrixCongruence C (v j s)), hN, ha0, haN, ha, hstep, ?_⟩
  · intro s hs
    have h := positive_definite_congruence (γ s) Cᵀ (hp s hs) hCt
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_transpose, matrixCongruence] using h
  · intro j hj
    exact ⟨hcont (v j) _ _ (hv j hj).1,
      fun s hs => matrix_congruence_hasDerivAt C ((hv j hj).2 s hs)⟩

theorem matrix_congruence_path_length_eq (C : Matrix n n ℝ) (hC : IsUnit C)
    (X Y : Matrix n n ℝ) (γ : ℝ → Matrix n n ℝ)
    (hγ : MatrixPiecewiseAdmissiblePath X Y γ) :
    matrixHessianPathLength (fun s => matrixCongruence C (γ s)) =
      matrixHessianPathLength γ := by
  rcases hγ with ⟨h0, h1, hc, hp, N, a, v, hN, ha0, haN, ha, hstep, hv⟩
  have hsub j (hj : j < N) :
      Set.Icc (a j) (a (j+1)) ⊆ Set.Icc (0:ℝ) 1 :=
    Set.Icc_subset_Icc (ha j hj.le).1 (ha (j+1) (Nat.succ_le_of_lt hj)).2
  have hi j (hj : j < N) := matrix_segment_speed_integrable γ (v j)
    (a j) (a (j+1)) (hstep j hj).le (hc.mono (hsub j hj))
    (hv j hj).1 (fun s hs => hp s (hsub j hj hs)) (hv j hj).2
  have hCt : IsUnit Cᵀ := (Matrix.isUnit_iff_isUnit_det _).mpr (by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hC)
  have htc : ContinuousOn (fun s => matrixCongruence C (γ s)) (Set.Icc (0:ℝ) 1) := by
    unfold matrixCongruence
    exact (continuousOn_const.mul hc).mul continuousOn_const
  have htp (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
      (matrixCongruence C (γ s)).PosDef := by
    have h := positive_definite_congruence (γ s) Cᵀ (hp s hs) hCt
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_transpose, matrixCongruence] using h
  have htv j (hj : j < N) :
      ContinuousOn (fun s => matrixCongruence C (v j s)) (Set.Icc (a j) (a (j+1))) ∧
        ∀ s ∈ Set.Ioo (a j) (a (j+1)),
          HasDerivAt (fun t => matrixCongruence C (γ t)) (matrixCongruence C (v j s)) s := by
    constructor
    · unfold matrixCongruence
      exact (continuousOn_const.mul (hv j hj).1).mul continuousOn_const
    · intro s hs
      exact matrix_congruence_hasDerivAt C ((hv j hj).2 s hs)
  have hti j (hj : j < N) := matrix_segment_speed_integrable
    (fun s => matrixCongruence C (γ s)) (fun s => matrixCongruence C (v j s))
    (a j) (a (j+1)) (hstep j hj).le (htc.mono (hsub j hj))
    (htv j hj).1 (fun s hs => htp s (hsub j hj hs)) (htv j hj).2
  unfold matrixHessianPathLength
  calc
    (∫ s : ℝ in (0:ℝ)..1, matrixHessianSpeed
        (fun t => matrixCongruence C (γ t)) s) =
        ∑ j ∈ Finset.range N, ∫ s : ℝ in a j..a (j+1), matrixHessianSpeed
          (fun t => matrixCongruence C (γ t)) s := by
      rw [← ha0, ← haN, intervalIntegral.sum_integral_adjacent_intervals hti]
    _ = ∑ j ∈ Finset.range N, ∫ s : ℝ in a j..a (j+1), matrixHessianSpeed γ s := by
      apply Finset.sum_congr rfl
      intro j hj
      exact matrix_congruence_segment_length_eq C hC γ (v j) _ _
        (hstep j (Finset.mem_range.mp hj)).le (hv j (Finset.mem_range.mp hj)).2
    _ = ∫ s : ℝ in (0:ℝ)..1, matrixHessianSpeed γ s := by
      rw [← ha0, ← haN, intervalIntegral.sum_integral_adjacent_intervals hi]

theorem matrix_congruence_inv_apply (C Z : Matrix n n ℝ) (hC : IsUnit C) :
    matrixCongruence C⁻¹ (matrixCongruence C Z) = Z := by
  have hd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det _).mp hC
  have hdt : IsUnit Cᵀ.det := by rw [Matrix.det_transpose]; exact hd
  unfold matrixCongruence
  rw [Matrix.transpose_nonsing_inv]
  calc
    C⁻¹ * (C * Z * Cᵀ) * (Cᵀ)⁻¹ = (C⁻¹*C)*Z*(Cᵀ*(Cᵀ)⁻¹) := by
      simp only [Matrix.mul_assoc]
    _ = Z := by rw [Matrix.nonsing_inv_mul C hd, Matrix.mul_nonsing_inv Cᵀ hdt]; simp

theorem matrix_congruence_piecewise_distance_eq (C : Matrix n n ℝ) (hC : IsUnit C)
    (X Y : Matrix n n ℝ) :
    matrixPiecewiseHessianDistance (matrixCongruence C X) (matrixCongruence C Y) =
      matrixPiecewiseHessianDistance X Y := by
  have hCi : IsUnit C⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hC
  unfold matrixPiecewiseHessianDistance
  congr 1
  ext r
  constructor
  · rintro ⟨δ, hδ, hr⟩
    refine ⟨(fun s => matrixCongruence C⁻¹ (δ s)), ?_, ?_⟩
    · simpa only [matrix_congruence_inv_apply C X hC,
        matrix_congruence_inv_apply C Y hC] using
        matrix_congruence_piecewise_admissible C⁻¹ hCi
          (matrixCongruence C X) (matrixCongruence C Y) δ hδ
    · rw [matrix_congruence_path_length_eq C⁻¹ hCi _ _ δ hδ]
      exact hr
  · rintro ⟨γ, hγ, hr⟩
    exact ⟨(fun s => matrixCongruence C (γ s)),
      matrix_congruence_piecewise_admissible C hC X Y γ hγ,
      (matrix_congruence_path_length_eq C hC X Y γ hγ).trans hr⟩

theorem matrix_piecewise_distance_whiten (X Y : Matrix n n ℝ)
    (hX : X.PosDef) :
    matrixPiecewiseHessianDistance X Y =
      matrixPiecewiseHessianDistance 1 (matrixRelativeSPD X Y hX) := by
  let Q := hX.inv.posSemidef.sqrt
  have hQ : IsUnit Q := sqrt_positive_definite_isUnit X⁻¹ hX.inv
  have hQt : Qᵀ = Q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hX.inv.posSemidef.posSemidef_sqrt.isHermitian.eq
  have hY : matrixCongruence Q Y = matrixRelativeSPD X Y hX := by
    change Q * Y * Qᵀ = Q * Y * Q
    rw [hQt]
  rw [← matrix_congruence_piecewise_distance_eq Q hQ X Y,
    matrix_inverse_sqrt_whitens X hX, hY]

theorem matrix_piecewise_distance_nonnegative (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    0 ≤ matrixPiecewiseHessianDistance X Y := by
  unfold matrixPiecewiseHessianDistance
  apply le_csInf
  · exact ⟨_, ⟨matrixSPDGeodesic X Y hX hY,
      matrix_spd_geodesic_admissible X Y hX hY, rfl⟩⟩
  · rintro r ⟨γ, _, rfl⟩
    exact matrixHessianPathLength_nonnegative γ

theorem matrix_piecewise_distance_le_spd_log_norm (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    matrixPiecewiseHessianDistance X Y ≤
      ‖matrixSPDLog (matrixRelativeSPD X Y hX)
        (matrix_relative_spd_positive X Y hX hY)‖ := by
  unfold matrixPiecewiseHessianDistance
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨γ, _, rfl⟩
    exact matrixHessianPathLength_nonnegative γ
  · exact ⟨matrixSPDGeodesic X Y hX hY,
      matrix_spd_geodesic_admissible X Y hX hY,
      matrix_spd_geodesic_length X Y hX hY⟩

end
end Sigma
