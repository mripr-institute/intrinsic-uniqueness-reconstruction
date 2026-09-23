import SigmaProbSmoothDensityBoundary
import SigmaProbCanonicalPair
import Mathlib.Order.Hom.Set

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The same compact level bump is applied on both canonical branches. -/
def deficitLevelShift (t : ℝ) : ℝ :=
  if 0 < t then continuationBump (SigmaBase.potential t) else 0

theorem deficit_level_bump_zero {v : ℝ} (hv : v ∉ Ioo (2 : ℝ) 3) :
    continuationBump v = 0 :=
  image_eq_zero_of_nmem_tsupport (fun h => hv (continuation_bump_support h))

theorem deficit_level_shift_zero_below (t : ℝ)
    (ht : t < (canonicalDeficitRoots 3).1) : deficitLevelShift t = 0 := by
  by_cases hp : 0 < t
  · rw [deficitLevelShift, if_pos hp]
    have hs := canonical_deficit_roots_spec 3 (by norm_num)
    have hI := intrinsic_potential_two_branch.left_strict
      ⟨hp, ht.le.trans hs.2.1⟩ ⟨hs.1, hs.2.1⟩ ht
    rw [hs.2.2.2.1] at hI
    exact deficit_level_bump_zero (fun hh => (not_lt_of_ge hI.le) hh.2)
  · simp only [deficitLevelShift, if_neg hp]

theorem deficit_level_shift_zero_above (t : ℝ)
    (ht : (canonicalDeficitRoots 3).2 < t) : deficitLevelShift t = 0 := by
  have hs := canonical_deficit_roots_spec 3 (by norm_num)
  have hp : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hs.2.2.1.trans ht.le)
  rw [deficitLevelShift, if_pos hp]
  have hI := intrinsic_potential_two_branch.right_strict hs.2.2.1 (hs.2.2.1.trans ht.le) ht
  rw [hs.2.2.2.2] at hI
  exact deficit_level_bump_zero (fun hh => (not_lt_of_ge hI.le) hh.2)

theorem deficit_level_shift_smooth : ContDiff ℝ ∞ deficitLevelShift := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : 0 < t
  · have hI : ContDiffAt ℝ ∞ SigmaBase.potential t :=
      (contDiffAt_id.sub contDiffAt_const).sub (contDiffAt_id.log ht.ne')
    apply (continuationBump.contDiff.contDiffAt.comp t hI).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with x hx
    change 0 < x at hx
    simp only [deficitLevelShift, if_pos hx, Function.comp_apply]
  · have ha := (canonical_deficit_roots_spec 3 (by norm_num)).1
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (show t < (canonicalDeficitRoots 3).1 by linarith)] with x hx
    exact deficit_level_shift_zero_below x hx

theorem deficit_level_shift_compact : HasCompactSupport deficitLevelShift := by
  apply HasCompactSupport.intro (K := Icc (canonicalDeficitRoots 3).1 (canonicalDeficitRoots 3).2)
    isCompact_Icc
  intro t ht
  simp only [mem_Icc, not_and_or, not_le] at ht
  exact ht.elim (deficit_level_shift_zero_below t) (deficit_level_shift_zero_above t)

theorem deficit_level_shift_anchor : deficitLevelShift 0 = 0 ∧ deficitLevelShift 1 = 0 := by
  constructor
  · simp [deficitLevelShift]
  · rw [deficitLevelShift, if_pos (by norm_num : (0 : ℝ) < 1)]
    simp only [SigmaBase.potential, sub_self, Real.log_one, sub_zero]
    exact deficit_level_bump_zero (by norm_num)

theorem deficit_level_shift_nonzero : ∃ t > 1, deficitLevelShift t = 1 := by
  let t := (canonicalDeficitRoots (5/2)).2
  have hs := canonical_deficit_roots_spec (5/2) (by norm_num)
  have ht : 1 < t := by
    by_contra hn
    have he : t = 1 := le_antisymm (le_of_not_gt hn) hs.2.2.1
    have hh := hs.2.2.2.2
    change SigmaBase.potential t = _ at hh
    rw [he] at hh
    norm_num [SigmaBase.potential] at hh
  refine ⟨t, ht, ?_⟩
  rw [deficitLevelShift, if_pos (by linarith : 0 < t), hs.2.2.2.2]
  exact continuationBump.one_of_mem_closedBall (by simp [continuationBump])

theorem deficit_level_shift_orderIso : ∃ ε : ℝ, 0 < ε ∧ ∃ e : ℝ ≃o ℝ,
    ∀ t : ℝ, e t = t+ε*deficitLevelShift t := by
  obtain ⟨B, hB⟩ := (deficit_level_shift_compact.deriv.abs.isCompact_range
    (deficit_level_shift_smooth.continuous_deriv (by simp)).abs).bddAbove
  let K := |B|+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hb (t : ℝ) : |deriv deficitLevelShift t| ≤ K := by
    have hh := hB (mem_range_self t)
    change |deriv deficitLevelShift t| ≤ B at hh
    dsimp [K]
    linarith [le_abs_self B]
  let ε := 1/(2*K)
  have he : 0 < ε := by dsimp [ε]; positivity
  have heK : ε*K = 1/2 := by dsimp [ε]; field_simp; ring
  let H : ℝ → ℝ := fun t => t+ε*deficitLevelShift t
  have hd (t : ℝ) : HasDerivAt H (1+ε*deriv deficitLevelShift t) t :=
    (hasDerivAt_id t).add
      (((deficit_level_shift_smooth.differentiable (by simp)) t).hasDerivAt.const_mul ε)
  have hm : StrictMono H := by
    apply strictMono_of_deriv_pos
    intro t
    rw [(hd t).deriv]
    have hh : |ε*deriv deficitLevelShift t| ≤ 1/2 := by
      rw [abs_mul, abs_of_pos he, ← heK]
      exact mul_le_mul_of_nonneg_left (hb t) he.le
    linarith [neg_abs_le (ε*deriv deficitLevelShift t)]
  have hc : Continuous H := continuous_id.add (continuous_const.mul deficit_level_shift_smooth.continuous)
  have htop : Tendsto H atTop atTop := by
    apply tendsto_id.congr'
    filter_upwards [eventually_gt_atTop (canonicalDeficitRoots 3).2] with t ht
    simp only [H, deficit_level_shift_zero_above t ht, mul_zero, add_zero, id_eq]
  have hbot : Tendsto H atBot atBot := by
    apply tendsto_id.congr'
    filter_upwards [eventually_lt_atBot (canonicalDeficitRoots 3).1] with t ht
    simp only [H, deficit_level_shift_zero_below t ht, mul_zero, add_zero, id_eq]
  let e := StrictMono.orderIsoOfSurjective H hm (hc.surjective htop hbot)
  exact ⟨ε, he, e, fun t => congrFun (StrictMono.coe_orderIsoOfSurjective H hm (hc.surjective htop hbot)) t⟩

theorem shifted_deficit_potential_two_branch (ε : ℝ) (e : ℝ ≃o ℝ)
    (he : ∀ t : ℝ, e t = t+ε*deficitLevelShift t) :
    TwoBranchPotential (SigmaBase.potential ∘ e.symm) := by
  have he0 : e 0 = 0 := by rw [he, deficit_level_shift_anchor.1]; ring
  have he1 : e 1 = 1 := by rw [he, deficit_level_shift_anchor.2]; ring
  have hi0 : e.symm 0 = 0 := by simpa only [he0] using e.symm_apply_apply 0
  have hi1 : e.symm 1 = 1 := by simpa only [he1] using e.symm_apply_apply 1
  have hipos {t : ℝ} (ht : 0 < t) : 0 < e.symm t := by
    rw [← hi0]
    exact e.symm.strictMono ht
  have hnear : (SigmaBase.potential ∘ e.symm) =ᶠ[𝓝[>] (0 : ℝ)] SigmaBase.potential := by
    have ha := (canonical_deficit_roots_spec 3 (by norm_num)).1
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ha)] with t ht
    have het : e t = t := by rw [he, deficit_level_shift_zero_below t ht]; ring
    have hit : e.symm t = t := by simpa only [het] using e.symm_apply_apply t
    simp only [Function.comp_apply, hit]
  have hfar : (SigmaBase.potential ∘ e.symm) =ᶠ[atTop] SigmaBase.potential := by
    filter_upwards [eventually_gt_atTop (canonicalDeficitRoots 3).2] with t ht
    have het : e t = t := by rw [he, deficit_level_shift_zero_above t ht]; ring
    have hit : e.symm t = t := by simpa only [het] using e.symm_apply_apply t
    simp only [Function.comp_apply, hit]
  refine ⟨intrinsic_potential_two_branch.measurable.comp e.symm.continuous.measurable,
    ?_, ?_, ?_, ?_, intrinsic_potential_two_branch.left_limit.congr' hnear.symm,
    intrinsic_potential_two_branch.right_limit.congr' hfar.symm⟩
  · exact intrinsic_potential_two_branch.continuous.comp e.symm.continuous.continuousOn
      (fun t ht => hipos ht)
  · simp only [Function.comp_apply, hi1, intrinsic_potential_two_branch.anchor]
  · intro x hx y hy hxy
    apply intrinsic_potential_two_branch.left_strict
      ⟨hipos hx.1, ?_⟩ ⟨hipos hy.1, ?_⟩ (e.symm.strictMono hxy)
    · simpa only [hi1] using e.symm.monotone hx.2
    · simpa only [hi1] using e.symm.monotone hy.2
  · intro x hx y hy hxy
    apply intrinsic_potential_two_branch.right_strict ?_ ?_ (e.symm.strictMono hxy)
    · simpa only [hi1] using e.symm.monotone hx
    · simpa only [hi1] using e.symm.monotone hy

theorem shifted_deficit_roots_and_width (ε : ℝ) (e : ℝ ≃o ℝ)
    (he : ∀ t : ℝ, e t = t+ε*deficitLevelShift t) (v : ℝ) (hv : 0 ≤ v) :
    0 < e (canonicalDeficitRoots v).1 ∧ e (canonicalDeficitRoots v).1 ≤ 1 ∧
    1 ≤ e (canonicalDeficitRoots v).2 ∧
    (SigmaBase.potential ∘ e.symm) (e (canonicalDeficitRoots v).1) = v ∧
    (SigmaBase.potential ∘ e.symm) (e (canonicalDeficitRoots v).2) = v ∧
    e (canonicalDeficitRoots v).2-e (canonicalDeficitRoots v).1 =
      (canonicalDeficitRoots v).2-(canonicalDeficitRoots v).1 := by
  have hs := canonical_deficit_roots_spec v hv
  have he0 : e 0 = 0 := by rw [he, deficit_level_shift_anchor.1]; ring
  have he1 : e 1 = 1 := by rw [he, deficit_level_shift_anchor.2]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [he0] using e.strictMono hs.1
  · simpa only [he1] using e.monotone hs.2.1
  · simpa only [he1] using e.monotone hs.2.2.1
  · simpa only [Function.comp_apply, e.symm_apply_apply] using hs.2.2.2.1
  · simpa only [Function.comp_apply, e.symm_apply_apply] using hs.2.2.2.2
  · rw [he, he]
    simp only [deficitLevelShift, if_pos hs.1,
      if_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hs.2.2.1), hs.2.2.2.1, hs.2.2.2.2]
    ring

theorem shifted_deficit_potential_noncanonical (ε : ℝ) (hε : 0 < ε) (e : ℝ ≃o ℝ)
    (he : ∀ t : ℝ, e t = t+ε*deficitLevelShift t) :
    ∃ t > 1, (SigmaBase.potential ∘ e.symm) t ≠ SigmaBase.potential t := by
  obtain ⟨t, ht, hb⟩ := deficit_level_shift_nonzero
  have het : e t = t+ε := by rw [he, hb, mul_one]
  refine ⟨e t, by rw [het]; linarith, ?_⟩
  simp only [Function.comp_apply, e.symm_apply_apply]
  have hlt := intrinsic_potential_two_branch.right_strict ht.le
    (show 1 ≤ e t by rw [het]; linarith) (show t < e t by rw [het]; linarith)
  exact hlt.ne

end
end Sigma
