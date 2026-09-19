import SigmaRealArithmetic
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions

namespace Sigma
noncomputable section
open Set
open Filter
open scoped Topology

theorem farey_left_strictMono : StrictMonoOn fareyLeft (Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  unfold fareyLeft
  apply (div_lt_div_iff₀ (by linarith [hx.1] : 0 < 1+x)
    (by linarith [hy.1] : 0 < 1+y)).mpr
  nlinarith

theorem farey_right_strictAnti : StrictAntiOn fareyRight (Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  unfold fareyRight
  apply (div_lt_div_iff₀ (by linarith [hy.1] : 0 < 1+y)
    (by linarith [hx.1] : 0 < 1+x)).mpr
  nlinarith

theorem farey_left_surjective : fareyLeft '' Icc (0:ℝ) 1 = Icc (0:ℝ) (1/2) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact farey_left_range x hx.1 hx.2
  · intro hy
    have hy0 : 0 ≤ y := hy.1
    have hy1 : y < 1 := lt_of_le_of_lt hy.2 (by norm_num)
    have hden : 0 < 1-y := by linarith
    have hx0 : 0 ≤ y/(1-y) := div_nonneg hy0 hden.le
    have hx1 : y/(1-y) ≤ 1 := (div_le_iff₀ hden).mpr (by nlinarith [hy.2])
    refine ⟨y/(1-y), ⟨hx0, hx1⟩, ?_⟩
    unfold fareyLeft
    field_simp [hden.ne']

theorem farey_right_surjective : fareyRight '' Icc (0:ℝ) 1 = Icc (1/2:ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact farey_right_range x hx.1 hx.2
  · intro hy
    have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy.1
    have hy1 : y ≤ 1 := hy.2
    have hx0 : 0 ≤ (1-y)/y := div_nonneg (by linarith) hy0.le
    have hx1 : (1-y)/y ≤ 1 := (div_le_iff₀ hy0).mpr (by nlinarith [hy.1])
    refine ⟨(1-y)/y, ⟨hx0, hx1⟩, ?_⟩
    unfold fareyRight
    field_simp [hy0.ne']

/-- The Farey branch integrates to the intrinsic potential on its whole positive domain. -/
theorem farey_left_integral {t : ℝ} (ht : 0 < t) :
    (∫ s in (0 : ℝ)..t-1, fareyLeft s) = SigmaBase.potential t := by
  have hp : ∀ s ∈ uIcc (0 : ℝ) (t-1), 0 < 1+s := by
    intro s hs
    rcases le_total (0 : ℝ) (t-1) with h | h
    · rw [uIcc_of_le h] at hs
      linarith [hs.1]
    · rw [uIcc_of_ge h] at hs
      linarith [hs.1]
  have hd : ∀ s ∈ uIcc (0 : ℝ) (t-1),
      HasDerivAt (fun x : ℝ => x-Real.log (1+x)) (fareyLeft s) s := by
    intro s hs
    convert (hasDerivAt_id s).sub (((hasDerivAt_id s).const_add 1).log (hp s hs).ne') using 1
    dsimp [fareyLeft]
    field_simp [(hp s hs).ne']
  have hi : IntervalIntegrable fareyLeft MeasureTheory.volume 0 (t-1) := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_id.div (continuous_const.add continuous_id).continuousOn
      (fun s hs => (hp s hs).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp [SigmaBase.potential]

/-- Numerical labels, not the abstract binary shape, identify the child maps. -/
theorem cw_labelled_child_maps_identify (L R : ℚ → ℚ)
    (hL : ∀ w, L (cwValue w)=cwValue (false::w))
    (hR : ∀ w, R (cwValue w)=cwValue (true::w)) :
    ∀ q > 0, L q=cwLeft q ∧ R q=cwRight q := by
  intro q hq
  obtain ⟨w, hw, _⟩ := cw_positive_rational_exists_unique q hq
  rw [← hw]
  exact ⟨hL w, hR w⟩

theorem mobius_left_three_point_extension (a b c d : ℝ)
    (h1 : c+d ≠ 0) (h2 : 2*c+d ≠ 0) (h3 : 3*c+d ≠ 0)
    (e1 : (a+b)/(c+d)=1/2) (e2 : (2*a+b)/(2*c+d)=2/3)
    (e3 : (3*a+b)/(3*c+d)=3/4) :
    ∀ x : ℝ, (a*x+b)/(c*x+d)=fareyLeft x := by
  have e1' := (div_eq_iff h1).mp e1
  have e2' := (div_eq_iff h2).mp e2
  have e3' := (div_eq_iff h3).mp e3
  have hb : b=0 := by linarith
  have hc : c=a := by linarith
  have hd : d=a := by linarith
  have ha : a ≠ 0 := by intro ha; apply h1; rw [hc, hd, ha]; ring
  intro x
  rw [hb, hc, hd, add_zero, show a*x+a=a*(1+x) by ring,
    mul_div_mul_left _ _ ha]
  rfl

theorem mobius_right_three_point_extension (a b c d : ℝ)
    (h1 : c+d ≠ 0) (h2 : 2*c+d ≠ 0) (h3 : 3*c+d ≠ 0)
    (e1 : (a+b)/(c+d)=2) (e2 : (2*a+b)/(2*c+d)=3)
    (e3 : (3*a+b)/(3*c+d)=4) :
    ∀ x : ℝ, (a*x+b)/(c*x+d)=1+x := by
  have e1' := (div_eq_iff h1).mp e1
  have e2' := (div_eq_iff h2).mp e2
  have e3' := (div_eq_iff h3).mp e3
  have hc : c=0 := by linarith
  have hb : b=a := by linarith
  have hd : d=a := by linarith
  have ha : a ≠ 0 := by simpa [hc, hd] using h1
  intro x
  rw [hc, hb, hd, zero_mul, zero_add, show a*x+a=(1+x)*a by ring,
    mul_div_cancel_right₀ _ ha]

theorem unlabelled_binary_tree_distinct_numerical_labels :
    ∃ f g : List Bool → ℚ, Function.Injective f ∧ Function.Injective g ∧
      (∀ w, 0 < f w ∧ 0 < g w) ∧ f [] ≠ g [] := by
  refine ⟨cwValue, fun w => 2*cwValue w, cwValue_injective, ?_, ?_, ?_⟩
  · intro u v h
    exact cwValue_injective (mul_left_cancel₀ (by norm_num : (2 : ℚ) ≠ 0) h)
  · intro w
    exact ⟨cwValue_positive w, mul_pos (by norm_num) (cwValue_positive w)⟩
  · norm_num [cwValue]

theorem analytic_extension_from_positive_rationals (f g : ℝ → ℝ)
    (hf : AnalyticOnNhd ℝ f (Ioi (-1))) (hg : AnalyticOnNhd ℝ g (Ioi (-1)))
    (he : ∀ q : ℚ, 0 < q → f q=g q) : EqOn f g (Ioi (-1)) := by
  let S : Set ℝ := (fun q : ℚ => (q : ℝ)) '' ((fun q : ℚ => (q : ℝ)) ⁻¹' Ioi 0)
  have hS : EqOn f g S := by
    rintro x ⟨q, hq, rfl⟩
    change (0 : ℝ) < (q : ℝ) at hq
    exact he q (by exact_mod_cast hq)
  have hsub : Ioi (0 : ℝ) ⊆ Ioi (-1) := by
    intro x hx
    change -1 < x
    linarith [show (0 : ℝ) < x from hx]
  have hpos : EqOn f g (Ioi 0) := hS.of_subset_closure
    (hf.continuousOn.mono hsub) (hg.continuousOn.mono hsub)
    (by rintro x ⟨q, hq, rfl⟩; exact hq)
    (Rat.denseRange_cast.subset_closure_image_preimage_of_isOpen isOpen_Ioi)
  have hnear : f =ᶠ[𝓝 (1 : ℝ)] g := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ)<1 by norm_num)] with x hx
    exact hpos hx
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_Ioi (-1 : ℝ)).isPreconnected
    (by norm_num : (1 : ℝ) ∈ Ioi (-1)) hnear

theorem analytic_farey_left_extension (f : ℝ → ℝ)
    (hf : AnalyticOnNhd ℝ f (Ioi (-1)))
    (he : ∀ q : ℚ, 0 < q → f q=fareyLeft q) : EqOn f fareyLeft (Ioi (-1)) := by
  apply analytic_extension_from_positive_rationals f fareyLeft hf _ he
  intro x hx
  exact analyticAt_id.div (analyticAt_const.add analyticAt_id) (by linarith [mem_Ioi.mp hx])

theorem mobius_left_positive_rational_extension (a b c d : ℝ)
    (he : ∀ q : ℚ, 0 < q → (a*q+b)/(c*q+d)=(cwLeft q : ℝ)) :
    ∀ x : ℝ, (a*x+b)/(c*x+d)=fareyLeft x := by
  have e1 := he 1 (by norm_num)
  have e2 := he 2 (by norm_num)
  have e3 := he 3 (by norm_num)
  norm_num [cwLeft, mul_comm] at e1 e2 e3
  rw [mul_comm a 2, mul_comm c 2] at e2
  rw [mul_comm a 3, mul_comm c 3] at e3
  have h1 : c+d ≠ 0 := by intro hz; norm_num [hz] at e1
  have h2 : 2*c+d ≠ 0 := by intro hz; norm_num [hz] at e2
  have h3 : 3*c+d ≠ 0 := by intro hz; norm_num [hz] at e3
  exact mobius_left_three_point_extension a b c d h1 h2 h3 e1 e2 e3

theorem mobius_right_positive_rational_extension (a b c d : ℝ)
    (he : ∀ q : ℚ, 0 < q → (a*q+b)/(c*q+d)=(cwRight q : ℝ)) :
    ∀ x : ℝ, (a*x+b)/(c*x+d)=1+x := by
  have e1 := he 1 (by norm_num)
  have e2 := he 2 (by norm_num)
  have e3 := he 3 (by norm_num)
  norm_num [cwRight, mul_comm] at e1 e2 e3
  rw [mul_comm a 2, mul_comm c 2] at e2
  rw [mul_comm a 3, mul_comm c 3] at e3
  have h1 : c+d ≠ 0 := by intro hz; norm_num [hz] at e1
  have h2 : 2*c+d ≠ 0 := by intro hz; norm_num [hz] at e2
  have h3 : 3*c+d ≠ 0 := by intro hz; norm_num [hz] at e3
  exact mobius_right_three_point_extension a b c d h1 h2 h3 e1 e2 e3

end
end Sigma
