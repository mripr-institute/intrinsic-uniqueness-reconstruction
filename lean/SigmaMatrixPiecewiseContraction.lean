import SigmaMatrixGlobalMinimality

namespace Sigma
noncomputable section
open MeasureTheory
open scoped BigOperators

/-- Every subinterval of a finite-piece differentiable curve inherits its
length bound. Clipped pieces of length zero impose no derivative condition
at endpoints or partition corners. -/
theorem piecewise_curve_subinterval_contraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Z : ℝ → E) (W : ℕ → ℝ → E) (speed : ℝ → ℝ)
    (N : ℕ) (a : ℕ → ℝ)
    (ha0 : a 0 = 0) (haN : a N = 1)
    (ha : ∀ j ≤ N, a j ∈ Set.Icc (0:ℝ) 1)
    (hstep : ∀ j < N, a j < a (j+1))
    (hZ : ContinuousOn Z (Set.Icc (0:ℝ) 1))
    (hW : ∀ j < N, ContinuousOn (W j) (Set.Icc (a j) (a (j+1))))
    (hd : ∀ j < N, ∀ u ∈ Set.Ioo (a j) (a (j+1)), HasDerivAt Z (W j u) u)
    (hi : ∀ j < N, IntervalIntegrable speed volume (a j) (a (j+1)))
    (hb : ∀ j < N, ∀ u ∈ Set.Ioo (a j) (a (j+1)), ‖W j u‖ ≤ speed u)
    (s t : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hst : s ≤ t) :
    ‖Z t - Z s‖ ≤ ∫ u : ℝ in s..t, speed u := by
  let c : ℕ → ℝ := fun j => max s (min t (a j))
  have hc0 : c 0 = s := by simp [c, ha0, ht.1, hs.1]
  have hcN : c N = t := by simp [c, haN, ht.2, hst]
  have hseg j (hj : j < N) :
      IntervalIntegrable speed volume (c j) (c (j+1)) ∧
        ‖Z (c (j+1)) - Z (c j)‖ ≤ ∫ u : ℝ in c j..c (j+1), speed u := by
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
    have hsubopen : Set.Ioo (c j) (c (j+1)) ⊆ Set.Ioo (a j) (a (j+1)) := by
      intro u hu
      have hends := hsubold ⟨hcmono, le_rfl⟩
      have hstarts := hsubold ⟨le_rfl, hcmono⟩
      exact ⟨lt_of_le_of_lt hstarts.1 hu.1, lt_of_lt_of_le hu.2 hends.2⟩
    have hint : IntervalIntegrable speed volume (c j) (c (j+1)) := by
      apply (hi j hj).mono_set
      simpa only [Set.uIcc_of_le hcmono, Set.uIcc_of_le (hstep j hj).le] using hsubold
    refine ⟨hint, ?_⟩
    exact matrix_log_curve_subinterval_contraction Z (W j) speed (c j) (c (j+1))
      hcmono (hZ.mono hsub) ((hW j hj).mono hsubold)
      (fun u hu => hd j hj u (hsubopen hu)) hint (fun u hu => hb j hj u (hsubopen hu))
  have htel : (∑ j ∈ Finset.range N, (Z (c (j+1)) - Z (c j))) = Z t - Z s := by
    simpa only [hcN, hc0] using Finset.sum_range_sub (fun j => Z (c j)) N
  rw [← htel]
  calc
    _ ≤ ∑ j ∈ Finset.range N, ‖Z (c (j+1)) - Z (c j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, ∫ u : ℝ in c j..c (j+1), speed u := by
      exact Finset.sum_le_sum fun j hj => (hseg j (Finset.mem_range.mp hj)).2
    _ = _ := by
      rw [intervalIntegral.sum_integral_adjacent_intervals (fun j hj => (hseg j hj).1), hc0, hcN]

end
end Sigma
