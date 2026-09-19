import SigmaMatrixPiecewiseRankOne

namespace Sigma
noncomputable section
open scoped Matrix Topology ComplexOrder BigOperators
open MeasureTheory

attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

/-- Every subinterval of a finite-piece path satisfies the logarithmic
length lower bound. Clipping a partition may create zero-length pieces;
these are handled explicitly rather than requiring a derivative at a corner. -/
theorem rank_one_piecewise_subinterval_length_lower_bound
    (X Y : Matrix (Fin 1) (Fin 1) ℝ)
    (γ : ℝ → Matrix (Fin 1) (Fin 1) ℝ) (hγ : RankOnePiecewiseAdmissiblePath X Y γ)
    (s t : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) (hst : s ≤ t) :
    |Real.log (γ t 0 0) - Real.log (γ s 0 0)| ≤
      ∫ u : ℝ in s..t, matrixHessianSpeed γ u := by
  rcases hγ with ⟨_, _, hc, hp, n, a, v, _, ha0, han, ha, hstep, hv⟩
  let c : ℕ → ℝ := fun j => max s (min t (a j))
  have hc0 : c 0 = s := by simp [c, ha0, ht.1, hs.1]
  have hcn : c n = t := by simp [c, han, ht.2, hst]
  have hseg j (hj : j < n) :
      IntervalIntegrable (matrixHessianSpeed γ) volume (c j) (c (j+1)) ∧
        |Real.log (γ (c (j+1)) 0 0) - Real.log (γ (c j) 0 0)| ≤
          ∫ u : ℝ in c j..c (j+1), matrixHessianSpeed γ u := by
    have hcmono : c j ≤ c (j+1) :=
      max_le_max_left s (min_le_min_left t (hstep j hj).le)
    by_cases heq : c j = c (j+1)
    · rw [heq]
      simp
    have haj : a j ≤ t := by
      by_contra hnot
      have hta : t < a j := lt_of_not_ge hnot
      have hta' : t ≤ a (j+1) := hta.le.trans (hstep j hj).le
      apply heq
      simp only [c, min_eq_left hta.le, min_eq_left hta']
    have haj' : s ≤ a (j+1) := by
      by_contra hnot
      have has : a (j+1) < s := lt_of_not_ge hnot
      apply heq
      have h1 : min t (a j) ≤ s := (min_le_right _ _).trans ((hstep j hj).le.trans has.le)
      have h2 : min t (a (j+1)) ≤ s := (min_le_right _ _).trans has.le
      simp only [c, max_eq_left h1, max_eq_left h2]
    have hsubold : Set.Icc (c j) (c (j+1)) ⊆ Set.Icc (a j) (a (j+1)) := by
      apply Set.Icc_subset_Icc
      · change a j ≤ max s (min t (a j))
        rw [min_eq_right haj]
        exact le_max_right _ _
      · exact max_le haj' (min_le_right _ _)
    have hsub : Set.Icc (c j) (c (j+1)) ⊆ Set.Icc (0:ℝ) 1 :=
      hsubold.trans (Set.Icc_subset_Icc (ha j hj.le).1 (ha (j+1) (Nat.succ_le_of_lt hj)).2)
    have hh := rank_one_segment_speed_integrable_and_bound
      (fun u => γ u 0 0) (fun u => v j u 0 0) (c j) (c (j+1)) hcmono
      (rankOneEntry.continuous.comp_continuousOn (hc.mono hsub))
      (fun u hu => (rankOneMatrix_posDef_iff _).mp (by
        rw [rankOneMatrix_entry]
        exact hp u (hsub hu)))
      (rankOneEntry.continuous.comp_continuousOn ((hv j hj).1.mono hsubold))
      (fun u hu => rankOneEntry.hasFDerivAt.comp_hasDerivAt u ((hv j hj).2 u (by
        have hends := hsubold ⟨hcmono, le_rfl⟩
        have hstarts := hsubold ⟨le_rfl, hcmono⟩
        exact ⟨lt_of_le_of_lt hstarts.1 hu.1, lt_of_lt_of_le hu.2 hends.2⟩)))
    simpa only [rankOneMatrix_entry] using hh
  have htel : (∑ j ∈ Finset.range n,
      (Real.log (γ (c (j+1)) 0 0) - Real.log (γ (c j) 0 0))) =
        Real.log (γ t 0 0) - Real.log (γ s 0 0) := by
    simpa only [hcn, hc0] using
      Finset.sum_range_sub (fun j => Real.log (γ (c j) 0 0)) n
  rw [← htel]
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        |Real.log (γ (c (j+1)) 0 0) - Real.log (γ (c j) 0 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, ∫ u : ℝ in c j..c (j+1), matrixHessianSpeed γ u := by
      apply Finset.sum_le_sum
      intro j hj
      exact (hseg j (Finset.mem_range.mp hj)).2
    _ = _ := by
      rw [intervalIntegral.sum_integral_adjacent_intervals (fun j hj => (hseg j hj).1), hc0, hcn]

/-- The constant-speed hypothesis is only almost everywhere. It imposes
no derivative or speed condition at partition corners or endpoints. -/
theorem rank_one_piecewise_constant_speed_minimizer_unique
    (X Y : Matrix (Fin 1) (Fin 1) ℝ) (hX : X.PosDef) (hY : Y.PosDef)
    (γ : ℝ → Matrix (Fin 1) (Fin 1) ℝ) (hγ : RankOnePiecewiseAdmissiblePath X Y γ)
    (c : ℝ) (hc : ∀ᵐ s : ℝ ∂volume,
      s ∈ Set.Icc (0:ℝ) 1 → matrixHessianSpeed γ s = c)
    (hmin : matrixHessianPathLength γ = rankOnePiecewiseHessianDistance X Y)
    (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    γ s = rankOneMatrix (rankOneExponentialPath (X 0 0) (Y 0 0) s) := by
  have hi (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
      (∫ u : ℝ in a..b, matrixHessianSpeed γ u) = (b-a)*c := by
    calc
      _ = ∫ _u : ℝ in a..b, c := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hc] with u hu huab
        rw [Set.uIoc_of_le hab] at huab
        exact hu ⟨ha.trans huab.1.le, huab.2.trans hb⟩
      _ = _ := by simp
  have hcd : c = |Real.log (Y 0 0) - Real.log (X 0 0)| := by
    have hh := hi 0 1 le_rfl le_rfl (by norm_num)
    change matrixHessianPathLength γ = _ at hh
    rw [hmin, rank_one_piecewise_hessian_distance X Y hX hY] at hh
    simpa using hh.symm
  have hleft := rank_one_piecewise_subinterval_length_lower_bound X Y γ hγ 0 s
    (by simp) hs hs.1
  have hright := rank_one_piecewise_subinterval_length_lower_bound X Y γ hγ s 1
    hs (by simp) hs.2
  rw [hγ.1, hi 0 s le_rfl hs.2 hs.1, hcd, sub_zero] at hleft
  rw [hγ.2.1, hi s 1 hs.1 le_rfl hs.2, hcd] at hright
  have he : Real.log (γ s 0 0) =
      Real.log (X 0 0) + s * (Real.log (Y 0 0) - Real.log (X 0 0)) := by
    rcases le_total (Real.log (X 0 0)) (Real.log (Y 0 0)) with hxy | hyx
    · rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at hleft hright
      have hl := (abs_le.mp hleft).2
      have hr := (abs_le.mp hright).2
      nlinarith
    · rw [abs_of_nonpos (sub_nonpos.mpr hyx)] at hleft hright
      have hl := (abs_le.mp hleft).1
      have hr := (abs_le.mp hright).1
      nlinarith
  have hp : 0 < γ s 0 0 := (rankOneMatrix_posDef_iff _).mp (by
    rw [rankOneMatrix_entry]
    exact hγ.2.2.2.1 s hs)
  have hval : γ s 0 0 = rankOneExponentialPath (X 0 0) (Y 0 0) s := by
    rw [rankOneExponentialPath, ← he, Real.exp_log hp]
  rw [← hval, rankOneMatrix_entry]

end
end Sigma
