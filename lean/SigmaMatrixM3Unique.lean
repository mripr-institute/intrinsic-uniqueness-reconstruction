import SigmaMatrixM3Distance

namespace Sigma
noncomputable section
open MeasureTheory
open scoped Matrix Topology
variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

theorem matrix_piecewise_differentiableAt_ae
    (X Y : Matrix n n ℝ) (γ : ℝ → Matrix n n ℝ)
    (hγ : MatrixPiecewiseAdmissiblePath X Y γ) :
    ∀ᵐ s : ℝ ∂volume, s ∈ Set.Icc (0:ℝ) 1 → DifferentiableAt ℝ γ s := by
  rcases hγ with ⟨h0, h1, hc, hp, N, a, v, hN, ha0, haN, ha, hstep, hv⟩
  have hne : ∀ᵐ s : ℝ ∂volume, ∀ j : ℕ, s ≠ a j := by
    rw [ae_all_iff]
    intro j
    simp [ae_iff]
  filter_upwards [hne] with s hs h01
  have hcover : ∀ k : ℕ, k ≤ N → a 0 < s → s < a k →
      ∃ j < k, s ∈ Set.Ioo (a j) (a (j+1)) := by
    intro k
    induction k with
    | zero => intro _ hleft hright; exact (not_lt_of_ge hleft.le hright).elim
    | succ k ih =>
      intro hk hleft hright
      by_cases hsk : s < a k
      · obtain ⟨j, hj, hjs⟩ := ih (Nat.le_of_succ_le hk) hleft hsk
        exact ⟨j, Nat.lt_succ_of_lt hj, hjs⟩
      · exact ⟨k, Nat.lt_succ_self k,
          ⟨lt_of_le_of_ne (le_of_not_gt hsk) (hs k).symm, hright⟩⟩
  have hs0 : a 0 < s := by rw [ha0]; exact lt_of_le_of_ne h01.1 (by simpa [ha0] using (hs 0).symm)
  have hs1 : s < a N := by rw [haN]; exact lt_of_le_of_ne h01.2 (by simpa [haN] using hs N)
  obtain ⟨j, hj, hjs⟩ := hcover N le_rfl hs0 hs1
  exact ((hv j hj).2 s hjs).differentiableAt

theorem matrix_congruence_piecewise_speed_eq_ae
    (C : Matrix n n ℝ) (hC : IsUnit C)
    (X Y : Matrix n n ℝ) (γ : ℝ → Matrix n n ℝ)
    (hγ : MatrixPiecewiseAdmissiblePath X Y γ) :
    ∀ᵐ s : ℝ ∂volume, s ∈ Set.Icc (0:ℝ) 1 →
      matrixHessianSpeed (fun t => matrixCongruence C (γ t)) s = matrixHessianSpeed γ s := by
  filter_upwards [matrix_piecewise_differentiableAt_ae X Y γ hγ] with s hs h01
  exact matrix_congruence_speed_eq C hC (hs h01).hasDerivAt

theorem matrix_clamped_path_speed_eq_ae (γ : ℝ → Matrix n n ℝ) :
    ∀ᵐ s : ℝ ∂volume, s ∈ Set.Icc (0:ℝ) 1 →
      matrixHessianSpeed (matrixClampedPath γ) s = matrixHessianSpeed γ s := by
  have h0 : ∀ᵐ s : ℝ ∂volume, s ≠ 0 := by simp [ae_iff]
  have h1 : ∀ᵐ s : ℝ ∂volume, s ≠ 1 := by simp [ae_iff]
  filter_upwards [h0, h1] with s hs0 hs1 hs
  exact matrix_clamped_path_speed_eq γ s
    ⟨lt_of_le_of_ne hs.1 hs0.symm, lt_of_le_of_ne hs.2 hs1⟩

/-- Uniqueness among all constant-speed minimizing finite-piece SPD curves,
in every rank and also for coincident endpoints. -/
theorem matrix_piecewise_constant_speed_minimizer_unique
    (X Y : Matrix n n ℝ) (hX : X.PosDef) (hY : Y.PosDef)
    (γ : ℝ → Matrix n n ℝ) (hγ : MatrixPiecewiseAdmissiblePath X Y γ)
    (c : ℝ) (hc : ∀ᵐ u : ℝ ∂volume,
      u ∈ Set.Icc (0:ℝ) 1 → matrixHessianSpeed γ u = c)
    (hmin : matrixHessianPathLength γ = matrixPiecewiseHessianDistance X Y)
    (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    γ s = matrixSPDGeodesic X Y hX hY s := by
  let Q := hX.inv.posSemidef.sqrt
  have hQ : IsUnit Q := sqrt_positive_definite_isUnit X⁻¹ hX.inv
  have hQt : Qᵀ = Q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hX.inv.posSemidef.posSemidef_sqrt.isHermitian.eq
  let δ := fun u => matrixCongruence Q (γ u)
  have hy : matrixCongruence Q Y = matrixRelativeSPD X Y hX := by
    change Q * Y * Qᵀ = Q * Y * Q
    rw [hQt]
  have hδ : MatrixPiecewiseAdmissiblePath 1 (matrixRelativeSPD X Y hX) δ := by
    simpa only [matrix_inverse_sqrt_whitens X hX, hy] using
      matrix_congruence_piecewise_admissible Q hQ X Y γ hγ
  let B := matrixClampedPath δ
  have hB := matrix_clamped_path_admissible 1 (matrixRelativeSPD X Y hX) δ hδ
  have hp : ∀ u, (B u).PosDef := matrix_clamped_path_posDef δ hδ.2.2.2.1
  let Z := matrixSPDLogPath B hp
  have hB0 : B 0 = 1 := hB.1
  have hB1 : B 1 = matrixRelativeSPD X Y hX := hB.2.1
  have hZ0 : Z 0 = 0 := by
    change matrixSPDLog (B 0) (hp 0) = 0
    rw [matrix_spd_log_eq_cfc_log, hB0, CFC.log_one]
  have hZ1 : Z 1 = matrixSPDLog (matrixRelativeSPD X Y hX)
      (matrix_relative_spd_positive X Y hX hY) := by
    change matrixSPDLog (B 1) (hp 1) = _
    simp only [matrix_spd_log_eq_cfc_log, hB1]
  have hLift (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) 1) :
      γ u = hX.posSemidef.sqrt * NormedSpace.exp ℝ (Z u) * hX.posSemidef.sqrt := by
    change γ u = hX.posSemidef.sqrt *
      NormedSpace.exp ℝ (matrixSPDLog (B u) (hp u)) * hX.posSemidef.sqrt
    rw [matrix_exp_spd_log]
    have hBu : B u = δ u := matrix_clamped_path_eq δ u hu
    rw [hBu]
    change γ u = hX.posSemidef.sqrt * (Q * γ u * Qᵀ) * hX.posSemidef.sqrt
    rw [hQt]
    exact (matrix_relative_spd_reconstruct X (γ u) hX).symm
  have he : ∀ᵐ u : ℝ ∂volume, u ∈ Set.Icc (0:ℝ) 1 →
      matrixHessianSpeed B u = matrixHessianSpeed γ u := by
    filter_upwards [matrix_clamped_path_speed_eq_ae δ,
      matrix_congruence_piecewise_speed_eq_ae Q hQ X Y γ hγ] with u hcl hcon hu
    exact (hcl hu).trans (hcon hu)
  have hbound (a b : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1)
      (hb : b ∈ Set.Icc (0:ℝ) 1) (hab : a ≤ b) :
      ‖Z b-Z a‖ ≤ ∫ u : ℝ in a..b, matrixHessianSpeed γ u := by
    have h := matrix_spd_log_piecewise_subinterval_contraction 1
      (matrixRelativeSPD X Y hX) B hB hp a b ha hb hab
    have hi : (∫ u : ℝ in a..b, matrixHessianSpeed B u) =
        ∫ u : ℝ in a..b, matrixHessianSpeed γ u := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [he] with u hu huab
      rw [Set.uIoc_of_le hab] at huab
      exact hu ⟨ha.1.trans huab.1.le, huab.2.trans hb.2⟩
    exact h.trans_eq hi
  apply matrix_constant_speed_unique_of_log_bounds X Y hX hY γ Z hZ0 hZ1
    hLift hbound c hc _ s hs
  exact hmin.trans (matrix_piecewise_hessian_distance_eq_spd_log_norm X Y hX hY)

end
end Sigma
