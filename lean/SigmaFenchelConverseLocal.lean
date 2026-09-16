import SigmaFenchelConverse

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology

theorem fenchel_intrinsic_left_strict : StrictAntiOn I (Ioc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 1)
    (fun t ht => (SigmaBase.potential_hasDerivAt ht.1).continuousAt.continuousWithinAt)
  intro x hx
  rw [interior_Ioc] at hx
  rw [(SigmaBase.potential_hasDerivAt hx.1).deriv]
  have hh : 1 < 1 / x := (one_lt_div hx.1).mpr hx.2
  linarith

theorem fenchel_intrinsic_right_strict : StrictMonoOn I (Ici 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    (fun t ht => (SigmaBase.potential_hasDerivAt (lt_of_lt_of_le (by norm_num) ht)).continuousAt.continuousWithinAt)
  intro x hx
  rw [interior_Ici] at hx
  have hx0 : 0 < x := lt_trans (by norm_num) hx
  rw [(SigmaBase.potential_hasDerivAt hx0).deriv]
  have hh : 1 / x < 1 := (div_lt_one hx0).mpr hx
  linarith

/-- A uniform positive objective gap outside any neighborhood of the minimizer. -/
theorem fenchel_intrinsic_gap_localizes {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ t > 0, I t < ε → |t - 1| < δ := by
  let d := min δ (1 / 2)
  have hd : 0 < d := lt_min hδ (by norm_num)
  have hd1 : d < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hl : 0 < I (1 - d) := by
    apply lt_of_le_of_ne (intrinsic_deficit_nonnegative (by linarith))
    intro hh
    have he := (intrinsic_deficit_zero_iff (show 0 < 1-d by linarith)).mp hh.symm
    linarith
  have hr : 0 < I (1 + d) := by
    apply lt_of_le_of_ne (intrinsic_deficit_nonnegative (by linarith))
    intro hh
    have he := (intrinsic_deficit_zero_iff (show 0 < 1+d by linarith)).mp hh.symm
    linarith
  refine ⟨min (I (1-d)) (I (1+d)), lt_min hl hr, ?_⟩
  intro t ht hgap
  have hlo : 1 - d < t := by
    by_contra hn
    have htd : t ≤ 1-d := le_of_not_gt hn
    have hm := fenchel_intrinsic_left_strict.antitoneOn
      (show t ∈ Ioc 0 1 from ⟨ht, by linarith⟩)
      (show 1-d ∈ Ioc 0 1 from ⟨by linarith, by linarith⟩) htd
    exact (not_lt_of_ge hm) (lt_of_lt_of_le hgap (min_le_left _ _))
  have hhi : t < 1 + d := by
    by_contra hn
    have hdt : 1+d ≤ t := le_of_not_gt hn
    have hm := fenchel_intrinsic_right_strict.monotoneOn
      (show 1+d ∈ Ici 1 by change 1 ≤ 1+d; linarith)
      (show t ∈ Ici 1 by change 1 ≤ t; linarith) hdt
    exact (not_lt_of_ge hm) (lt_of_lt_of_le hgap (min_le_right _ _))
  have hab : |t-1| < d := abs_lt.mpr ⟨by linarith, by linarith⟩
  exact lt_of_lt_of_le hab (min_le_left _ _)

/-- Near the exposed point, finite candidate values approximate the target from above.
Both location and value control are derived from the full conjugate. -/
theorem fenchel_candidate_local_contact (F : ℝ → EReal)
    (hc : fullFenchelConjugate F = intrinsicConjugateTarget)
    {t₀ δ ε : ℝ} (ht₀ : 0 < t₀) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ t r : ℝ, 0 < t ∧ |t-t₀| < δ ∧ F t = (r : EReal) ∧ r < I t₀ + ε := by
  let θ := 1 - 1/t₀
  have hθ : θ < 1 := by dsimp [θ]; linarith [one_div_pos.mpr ht₀]
  let d := min δ (ε / (2 * (|θ| + 1)))
  have hd : 0 < d := lt_min hδ (div_pos hε (by positivity))
  obtain ⟨η, hη, hloc⟩ := fenchel_intrinsic_gap_localizes (div_pos hd ht₀)
  obtain ⟨t, r, ht, htr, hnear⟩ := fenchel_candidate_approximate_optimizer F hc hθ
    (lt_min hη (show 0 < ε/2 by linarith))
  have hlow : I t ≤ r := by
    have hh := fenchel_candidate_lower_bound F hc t
    simpa only [extendedIntrinsic, if_pos ht, htr, EReal.coe_le_coe_iff] using hh
  have hnorm : (1-θ)*t = t/t₀ := by dsimp [θ]; ring
  have hid := fenchel_deficit_identity hθ ht
  rw [hnorm] at hid
  have hgap : I (t/t₀) < η := by
    have hm := min_le_left η (ε/2)
    linarith
  have hab := hloc (t/t₀) (div_pos ht ht₀) hgap
  have hab' : |t-t₀| < d := by
    rw [show t/t₀-1 = (t-t₀)/t₀ by field_simp, abs_div, abs_of_pos ht₀] at hab
    exact (div_lt_div_iff_of_pos_right ht₀).mp hab
  have he := (fenchel_equality_iff hθ ht₀).mpr
    (show t₀ = 1/(1-θ) by dsimp [θ]; field_simp)
  have hbound : θ*(t-t₀) < ε/2 := by
    have hdε : d ≤ ε/(2*(|θ|+1)) := min_le_right _ _
    have hprod : (|θ|+1)*|t-t₀| < ε/2 := by
      have hh := mul_lt_mul_of_pos_left (lt_of_lt_of_le hab' hdε) (show 0 < |θ|+1 by positivity)
      have heq : (|θ|+1)*(ε/(2*(|θ|+1))) = ε/2 := by field_simp; ring
      rwa [heq] at hh
    have hh : θ*(t-t₀) ≤ |θ| * |t-t₀| := by
      rw [← abs_mul]
      exact le_abs_self _
    exact lt_of_le_of_lt (hh.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num)) (abs_nonneg _))) hprod
  refine ⟨t,r,ht,lt_of_lt_of_le hab' (min_le_left _ _),htr,?_⟩
  have hm := min_le_right η (ε/2)
  rw [mul_sub] at hbound
  have hsum := add_lt_add hnear hbound
  rw [← he] at hsum
  linarith only [hsum, hm]

end
end Sigma
