import SigmaRealArithmetic
import Mathlib.MeasureTheory.Integral.FundThmCalculus

namespace Sigma
noncomputable section
open Set

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

end
end Sigma
