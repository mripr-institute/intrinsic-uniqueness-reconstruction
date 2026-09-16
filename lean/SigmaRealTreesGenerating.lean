import SigmaRealTreesProbability
import Mathlib.Analysis.Normed.Group.Tannery

namespace Sigma
noncomputable section
open PowerSeries Filter Set
open scoped BigOperators Topology

theorem tree_exp_hasSum_of_summable (F : PowerSeries ℝ) (a : ℝ)
    (hF0 : constantCoeff ℝ F = 0) (hFn : ∀ n, 0 ≤ coeff ℝ n F)
    (hF : HasSum (fun n => coeff ℝ n F) a)
    (hE : Summable (fun n => coeff ℝ n (treeExp ℝ F))) :
    HasSum (fun n => coeff ℝ n (treeExp ℝ F)) (Real.exp a) := by
  have hlim : Tendsto (fun m => ∑' n, coeff ℝ n (treeExpPartial ℝ F m)) atTop
      (𝓝 (∑' n, coeff ℝ n (treeExp ℝ F))) := by
    apply tendsto_tsum_of_dominated_convergence hE
    · intro n
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop n] with m hm
      exact (tree_exp_partial_coeff ℝ F hF0 n m hm).symm
    · apply Eventually.of_forall
      intro m n
      rw [Real.norm_of_nonneg (tree_exp_partial_nonnegative F hFn m n)]
      exact tree_exp_partial_coefficient_le F hF0 hFn m n
  have hexp : HasSum (fun n : ℕ => a ^ n / (n.factorial : ℝ)) (Real.exp a) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp ℝ a
  have he : (fun m => ∑' n, coeff ℝ n (treeExpPartial ℝ F m)) =
      fun m => ∑ j ∈ Finset.range m, a ^ j / (j.factorial : ℝ) := by
    funext m
    exact (tree_exp_partial_hasSum F a hF hFn m).tsum_eq
  rw [he] at hlim
  have hu := tendsto_nhds_unique hlim hexp.tendsto_sum_nat
  exact hu ▸ hE.hasSum

def borelGenerating (s : ℝ) : ℝ := ∑' n, s ^ n * borelCoefficient n


theorem borel_generating_is_pgf (s : ℝ) :
    borelGenerating s = ∑' n, s ^ n * (borelPMF n).toReal := by
  simp only [borelGenerating, borel_pmf_apply,
    ENNReal.toReal_ofReal (borel_coefficient_nonnegative _)]

theorem borel_generating_hasSum (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    HasSum (fun n => coeff ℝ n (rescale s borelSeries)) (borelGenerating s) := by
  have hs : Summable (fun n => s ^ n * borelCoefficient n) := by
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg hs0 n)
      (borel_coefficient_nonnegative n)) _ borel_coefficients_summable
    intro n
    have hn : s ^ n ≤ 1 := pow_le_one₀ hs0 hs1
    exact (mul_le_mul_of_nonneg_right hn (borel_coefficient_nonnegative n)).trans_eq (one_mul _)
  simpa only [borelGenerating, coeff_rescale, borelCoefficient] using hs.hasSum

theorem borel_generating_zero : borelGenerating 0 = 0 := by
  unfold borelGenerating
  have hz : (fun n : ℕ => (0 : ℝ) ^ n * borelCoefficient n) = fun _ => 0 := by
    funext n
    cases n with
    | zero => simp [borel_coefficient_zero]
    | succ n => simp
  rw [hz, tsum_zero]

theorem borel_generating_one : borelGenerating 1 = 1 := by
  simpa [borelGenerating] using borel_coefficients_sum_one

theorem borel_generating_nonnegative (s : ℝ) (hs : 0 ≤ s) : 0 ≤ borelGenerating s := by
  exact tsum_nonneg fun n => mul_nonneg (pow_nonneg hs _) (borel_coefficient_nonnegative _)

theorem borel_generating_le_one (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : borelGenerating s ≤ 1 := by
  rw [← (borel_generating_hasSum s hs0 hs1).tsum_eq, ← borel_coefficients_sum_one]
  apply tsum_le_tsum _ ((borel_generating_hasSum s hs0 hs1).summable) borel_coefficients_summable
  intro n
  rw [coeff_rescale]
  change s ^ n * borelCoefficient n ≤ borelCoefficient n
  exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hs0 hs1) (borel_coefficient_nonnegative n)).trans_eq
    (one_mul _)

theorem scaled_borel_fixed_point (s : ℝ) :
    rescale s borelSeries = C ℝ (s * Real.exp (-1)) * X *
      treeExp ℝ (rescale s borelSeries) := by
  have h := congrArg (rescale s) borel_series_fixed_point
  simp only [map_mul, tree_rescale_constant, rescale_X, tree_exp_rescale] at h
  rw [map_mul]
  linear_combination h

theorem scaled_borel_exp_hasSum (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    HasSum (fun n => coeff ℝ n (treeExp ℝ (rescale s borelSeries)))
      (borelGenerating s / (s * Real.exp (-1))) := by
  have ha : s * Real.exp (-1) ≠ 0 := mul_ne_zero hs0.ne' (Real.exp_ne_zero _)
  have hc (n : ℕ) : coeff ℝ n (treeExp ℝ (rescale s borelSeries)) =
      coeff ℝ (n + 1) (rescale s borelSeries) / (s * Real.exp (-1)) := by
    have h := congrArg (coeff ℝ (n + 1)) (scaled_borel_fixed_point s)
    simp only [mul_assoc, coeff_C_mul, tree_coefficient_X_mul] at h
    rw [h, ← mul_assoc, mul_div_cancel_left₀ _ ha]
  have hz : coeff ℝ 0 (rescale s borelSeries) = 0 := by
    simp [coeff_rescale, borel_series_constant]
  have ht := borel_generating_hasSum s hs0.le hs1
  rw [← hasSum_nat_add_iff' 1] at ht
  simp only [Finset.sum_range_one, hz, add_zero, sub_zero] at ht
  have hh := ht.div_const (s * Real.exp (-1))
  simpa only [hc] using hh

theorem borel_generating_fixed_point (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    borelGenerating s = s * Real.exp (borelGenerating s - 1) := by
  rcases hs0.eq_or_lt with rfl | hs0
  · simp [borel_generating_zero]
  have hn : ∀ n, 0 ≤ coeff ℝ n (rescale s borelSeries) := by
    intro n
    rw [coeff_rescale]
    exact mul_nonneg (pow_nonneg hs0.le n) (borel_coefficient_nonnegative n)
  have hE := scaled_borel_exp_hasSum s hs0 hs1
  have he := tree_exp_hasSum_of_summable (rescale s borelSeries) (borelGenerating s)
    (by rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale]
        simp [coeff_zero_eq_constantCoeff_apply, borel_series_constant]) hn
    (borel_generating_hasSum s hs0.le hs1) hE.summable
  have hh := hE.unique he
  have ha : s * Real.exp (-1) ≠ 0 := mul_ne_zero hs0.ne' (Real.exp_ne_zero _)
  have hmul := (div_eq_iff ha).mp hh
  rw [sub_eq_add_neg, Real.exp_add]
  linear_combination hmul

end
end Sigma
