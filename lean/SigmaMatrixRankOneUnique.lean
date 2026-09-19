import SigmaMatrixRankOne

namespace Sigma
noncomputable section
open scoped Matrix Topology ComplexOrder

attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

/-- A scalar path with speed at most the endpoint logarithmic distance must
be the affine interpolation in logarithmic coordinates. -/
theorem rank_one_log_path_rigid (x y : ℝ) (f : ℝ → ℝ)
    (hf : RankOneAdmissiblePath x y f)
    (hbound : ∀ s ∈ Set.Icc (0:ℝ) 1,
      |deriv f s / f s| ≤ |Real.log y - Real.log x|)
    (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    f s = rankOneExponentialPath x y s := by
  rcases hf with ⟨h0, h1, hp, hd, _⟩
  have hlog t (ht : t ∈ Set.Icc (0:ℝ) 1) :
      HasDerivWithinAt (fun u => Real.log (f u)) (deriv f t / f t) (Set.Icc (0:ℝ) 1) t :=
    ((hd t ht).hasDerivAt.log (ne_of_gt (hp t ht))).hasDerivWithinAt
  have hb t (ht : t ∈ Set.Icc (0:ℝ) 1) :
      ‖deriv f t / f t‖ ≤ |Real.log y - Real.log x| := by
    rw [Real.norm_eq_abs]
    exact hbound t ht
  have hleft := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hlog hb
    (convex_Icc (0:ℝ) 1) (show (0:ℝ) ∈ Set.Icc (0:ℝ) 1 by simp) hs
  have hright := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hlog hb
    (convex_Icc (0:ℝ) 1) hs (show (1:ℝ) ∈ Set.Icc (0:ℝ) 1 by simp)
  simp only [h0, h1, Real.norm_eq_abs, sub_zero, abs_of_nonneg hs.1,
    abs_of_nonneg (sub_nonneg.mpr hs.2)] at hleft hright
  have he : Real.log (f s) = Real.log x + s * (Real.log y - Real.log x) := by
    rcases le_total (Real.log x) (Real.log y) with hxy | hyx
    · rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at hleft hright
      have hl := (abs_le.mp hleft).2
      have hr := (abs_le.mp hright).2
      nlinarith
    · rw [abs_of_nonpos (sub_nonpos.mpr hyx)] at hleft hright
      have hl := (abs_le.mp hleft).1
      have hr := (abs_le.mp hright).1
      nlinarith
  rw [rankOneExponentialPath, ← he, Real.exp_log (hp s hs)]

theorem rank_one_native_speed_bound_rigid (X Y : Matrix (Fin 1) (Fin 1) ℝ)
    (hX : X.PosDef) (hY : Y.PosDef)
    (γ : ℝ → Matrix (Fin 1) (Fin 1) ℝ) (hγ : RankOneMatrixAdmissiblePath X Y γ)
    (hbound : ∀ s ∈ Set.Icc (0:ℝ) 1,
      matrixHessianSpeed γ s ≤ rankOneMatrixHessianDistance X Y)
    (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    γ s = rankOneMatrix (rankOneExponentialPath (X 0 0) (Y 0 0) s) := by
  have hf := rank_one_native_path_scalar_admissible X Y γ hγ
  have he : γ s 0 0 = rankOneExponentialPath (X 0 0) (Y 0 0) s := by
    apply rank_one_log_path_rigid _ _ _ hf _ s hs
    intro t ht
    have hv := rankOneMatrix_speed (hf.2.2.2.1 t ht).hasDerivAt (ne_of_gt (hf.2.2.1 t ht))
    simp only [rankOneMatrix_entry] at hv
    rw [← hv, ← rank_one_native_hessian_distance X Y hX hY]
    exact hbound t ht
  rw [← he, rankOneMatrix_entry]

/-- Uniqueness of the actual constant-speed minimizing C1 SPD path in rank
one, including coincident endpoints. Minimality means its integral length
equals the variational infimum over all native admissible paths. -/
theorem rank_one_native_constant_speed_minimizer_unique
    (X Y : Matrix (Fin 1) (Fin 1) ℝ) (hX : X.PosDef) (hY : Y.PosDef)
    (γ : ℝ → Matrix (Fin 1) (Fin 1) ℝ) (hγ : RankOneMatrixAdmissiblePath X Y γ)
    (c : ℝ) (hc : ∀ s ∈ Set.Icc (0:ℝ) 1, matrixHessianSpeed γ s = c)
    (hmin : matrixHessianPathLength γ = rankOneMatrixHessianDistance X Y)
    (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    γ s = rankOneMatrix (rankOneExponentialPath (X 0 0) (Y 0 0) s) := by
  have hlen : matrixHessianPathLength γ = c := by
    unfold matrixHessianPathLength
    calc
      _ = ∫ _t : ℝ in (0:ℝ)..1, c := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
        exact hc t ht
      _ = c := by simp
  have hd : c = rankOneMatrixHessianDistance X Y := hlen.symm.trans hmin
  apply rank_one_native_speed_bound_rigid X Y hX hY γ hγ _ s hs
  intro t ht
  rw [hc t ht, hd]

end
end Sigma
