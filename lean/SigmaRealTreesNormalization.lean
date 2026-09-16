import SigmaRealTreesMassBound
import Mathlib.Analysis.Normed.Field.InfiniteSum
import Mathlib.Analysis.Normed.Algebra.Exponential

namespace Sigma
noncomputable section
open PowerSeries Filter
open scoped BigOperators Topology

theorem tree_series_product_hasSum (F G : PowerSeries ℝ) (a b : ℝ)
    (hF : HasSum (fun n => coeff ℝ n F) a) (hG : HasSum (fun n => coeff ℝ n G) b)
    (hFn : ∀ n, 0 ≤ coeff ℝ n F) (hGn : ∀ n, 0 ≤ coeff ℝ n G) :
    HasSum (fun n => coeff ℝ n (F * G)) (a * b) := by
  have hFnorm : Summable (fun n => ‖coeff ℝ n F‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hFn _)] using hF.summable
  have hGnorm : Summable (fun n => ‖coeff ℝ n G‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hGn _)] using hG.summable
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hFnorm hGnorm).of_norm
  have hv := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hFnorm hGnorm
  have hh := hs.hasSum
  rw [← hv, hF.tsum_eq, hG.tsum_eq] at hh
  simpa only [coeff_mul] using hh

theorem tree_series_power_hasSum (F : PowerSeries ℝ) (a : ℝ)
    (hF : HasSum (fun n => coeff ℝ n F) a) (hFn : ∀ n, 0 ≤ coeff ℝ n F) (k : ℕ) :
    HasSum (fun n => coeff ℝ n (F ^ k)) (a ^ k) := by
  induction k with
  | zero => simp only [pow_zero, coeff_one]; exact hasSum_ite_eq 0 1
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact tree_series_product_hasSum _ _ _ _ ih hF (tree_coeff_pow_nonnegative F hFn k) hFn

theorem tree_exp_partial_hasSum (F : PowerSeries ℝ) (a : ℝ)
    (hF : HasSum (fun n => coeff ℝ n F) a) (hFn : ∀ n, 0 ≤ coeff ℝ n F) (m : ℕ) :
    HasSum (fun n => coeff ℝ n (treeExpPartial ℝ F m))
      (∑ j ∈ Finset.range m, a ^ j / (j.factorial : ℝ)) := by
  induction m with
  | zero => simpa [treeExpPartial] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  | succ m ih =>
    have hh := ih.add ((tree_series_power_hasSum F a hF hFn m).mul_left
      ((m.factorial : ℝ)⁻¹))
    simpa only [treeExpPartial, Finset.sum_range_succ, map_add, coeff_C_mul,
      div_eq_mul_inv, mul_comm ((m.factorial : ℝ)⁻¹) (a ^ m)] using hh

theorem tree_exp_partial_coefficient_le (F : PowerSeries ℝ)
    (hF : constantCoeff ℝ F = 0) (hFn : ∀ n, 0 ≤ coeff ℝ n F) (m n : ℕ) :
    coeff ℝ n (treeExpPartial ℝ F m) ≤ coeff ℝ n (treeExp ℝ F) := by
  by_cases hnm : n < m
  · rw [tree_exp_partial_coeff ℝ F hF n m hnm]
  · simp only [treeExp, coeff_mk, treeExpPartial, map_sum, coeff_C_mul]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro j hj hjm
    exact mul_nonneg (by positivity) (tree_coeff_pow_nonnegative F hFn j n)

theorem borel_exponential_coefficient (n : ℕ) :
    coeff ℝ n (treeExp ℝ borelSeries) = Real.exp 1 * borelCoefficient (n + 1) := by
  have h := congrArg (coeff ℝ (n + 1)) borel_series_fixed_point
  simp only [mul_assoc, coeff_C_mul, tree_coefficient_X_mul] at h
  have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  change _ = Real.exp 1 * coeff ℝ (n + 1) borelSeries
  rw [h, ← mul_assoc, he, one_mul]

theorem borel_exponential_hasSum :
    HasSum (fun n => coeff ℝ n (treeExp ℝ borelSeries))
      (Real.exp 1 * ∑' n, borelCoefficient n) := by
  have hs : HasSum (fun n => borelCoefficient (n + 1)) (∑' n, borelCoefficient n) := by
    have h := borel_coefficients_summable.hasSum
    rw [← hasSum_nat_add_iff' 1] at h
    simpa [borel_coefficient_zero] using h
  simpa only [borel_exponential_coefficient] using hs.mul_left (Real.exp 1)

theorem borel_exponential_mass_lower_bound :
    Real.exp (∑' n, borelCoefficient n) ≤ Real.exp 1 * ∑' n, borelCoefficient n := by
  have hsum : HasSum (fun n : ℕ => (∑' i, borelCoefficient i) ^ n / (n.factorial : ℝ))
      (Real.exp (∑' i, borelCoefficient i)) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      NormedSpace.expSeries_div_hasSum_exp ℝ (∑' i, borelCoefficient i)
  apply le_of_tendsto_of_tendsto hsum.tendsto_sum_nat tendsto_const_nhds
  apply Filter.Eventually.of_forall
  intro m
  have hp := tree_exp_partial_hasSum borelSeries (∑' n, borelCoefficient n)
    borel_coefficients_summable.hasSum borel_coefficient_nonnegative m
  dsimp only
  rw [← hp.tsum_eq, ← borel_exponential_hasSum.tsum_eq]
  exact tsum_le_tsum
    (tree_exp_partial_coefficient_le borelSeries borel_series_constant borel_coefficient_nonnegative m)
    hp.summable borel_exponential_hasSum.summable

/-- The actual explicit Borel coefficients have total mass one. No probability
normalization was an input: finite polynomial iteration first proved summability. -/
theorem borel_coefficients_sum_one : (∑' n, borelCoefficient n) = 1 := by
  have hl := borel_exponential_mass_lower_bound
  have hx : Real.exp ((∑' n, borelCoefficient n) - 1) ≤ ∑' n, borelCoefficient n := by
    rw [Real.exp_sub]
    exact (div_le_iff₀ (Real.exp_pos 1)).mpr (by simpa [mul_comm] using hl)
  by_contra hne
  have hh := Real.add_one_lt_exp (sub_ne_zero.mpr hne)
  linarith

end
end Sigma
