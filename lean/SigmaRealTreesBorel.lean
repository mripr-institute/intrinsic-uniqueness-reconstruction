import SigmaRealTreesCoefficients

namespace Sigma
noncomputable section
open PowerSeries
open scoped BigOperators

section Fields
variable (K : Type*) [Field K]

theorem tree_rescale_constant (a b : K) : rescale a (C K b) = C K b := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_rescale, coeff_C]
  split_ifs with hn
  · subst n
    simp
  · simp

theorem tree_exp_partial_rescale (F : PowerSeries K) (a : K) (m : ℕ) :
    rescale a (treeExpPartial K F m) = treeExpPartial K (rescale a F) m := by
  simp only [treeExpPartial, map_sum, map_mul, map_pow, tree_rescale_constant]

theorem tree_exp_rescale (F : PowerSeries K) (a : K) :
    rescale a (treeExp K F) = treeExp K (rescale a F) := by
  apply PowerSeries.ext
  intro n
  simp only [treeExp, coeff_rescale, coeff_mk]
  rw [← tree_exp_partial_rescale, coeff_rescale]

end Fields

def borelSeries : PowerSeries ℝ := rescale (Real.exp (-1)) (rootedSeries ℝ)

def borelCoefficient (n : ℕ) : ℝ := coeff ℝ n borelSeries

theorem borel_series_constant : constantCoeff ℝ borelSeries = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, borelSeries, coeff_rescale]
  simp [coeff_zero_eq_constantCoeff_apply, rooted_series_constant]

theorem borel_series_fixed_point :
    borelSeries = C ℝ (Real.exp (-1)) * X * treeExp ℝ borelSeries := by
  have h := congrArg (rescale (Real.exp (-1))) (rooted_series_fixed_point ℝ)
  simpa only [map_mul, rescale_X, tree_exp_rescale, borelSeries] using h

theorem borel_series_unique (F : PowerSeries ℝ)
    (hF : F = C ℝ (Real.exp (-1)) * X * treeExp ℝ F) : F = borelSeries := by
  have he : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  have hg : rescale (Real.exp 1) F = X * treeExp ℝ (rescale (Real.exp 1) F) := by
    have h := congrArg (rescale (Real.exp 1)) hF
    simp only [map_mul, tree_rescale_constant, rescale_X, tree_exp_rescale] at h
    have hc := congrArg (C ℝ) he
    simp only [map_mul, map_one] at hc
    linear_combination h + X * treeExp ℝ (rescale (Real.exp 1) F) * hc
  have hu := rooted_series_unique ℝ (rescale (Real.exp 1) F) hg
  have hh := congrArg (rescale (Real.exp (-1))) hu
  have he' : Real.exp 1 * Real.exp (-1) = 1 := (mul_comm _ _).trans he
  simpa only [rescale_rescale, he', rescale_one, borelSeries, RingHom.id_apply] using hh

theorem borel_series_exists_unique :
    ∃! F : PowerSeries ℝ, F = C ℝ (Real.exp (-1)) * X * treeExp ℝ F :=
  ⟨borelSeries, borel_series_fixed_point, fun F hF => borel_series_unique F hF⟩

/-- Formal substitution into t exp(1-t) gives the inverse with its marked factor e. -/
theorem borel_series_inverse_identity :
    C ℝ (Real.exp 1) * borelSeries * treeExp ℝ (-borelSeries) = X := by
  have h := congrArg (rescale (Real.exp (-1))) (rooted_series_inverse_identity ℝ)
  simp only [map_mul, rescale_X, tree_exp_rescale, map_neg] at h
  change borelSeries * treeExp ℝ (-borelSeries) = C ℝ (Real.exp (-1)) * X at h
  have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  calc
    C ℝ (Real.exp 1) * borelSeries * treeExp ℝ (-borelSeries) =
      C ℝ (Real.exp 1) * (borelSeries * treeExp ℝ (-borelSeries)) := by ring
    _ = C ℝ (Real.exp 1) * (C ℝ (Real.exp (-1)) * X) := by rw [h]
    _ = X := by rw [← mul_assoc, ← map_mul, he, map_one, one_mul]

theorem borel_forest_coefficients (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    coeff ℝ n (borelSeries ^ k) =
      Real.exp (-(n : ℝ)) * ((k : ℝ) / (n : ℝ) *
        (n : ℝ) ^ (n - k) / ((n - k).factorial : ℝ)) := by
  rw [borelSeries, ← map_pow, coeff_rescale, rooted_power_coefficients ℝ n k hk hkn]
  have he : Real.exp (-1) ^ n = Real.exp (-(n : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]

theorem borel_coefficient_zero : borelCoefficient 0 = 0 := by
  simpa [borelCoefficient] using borel_series_constant

theorem borel_coefficient_formula (n : ℕ) :
    borelCoefficient (n + 1) = Real.exp (-((n + 1 : ℕ) : ℝ)) *
      ((n + 1 : ℕ) : ℝ) ^ n / ((n + 1).factorial : ℝ) := by
  rw [borelCoefficient, borelSeries, coeff_rescale, rooted_series_coefficients]
  have he : Real.exp (-1) ^ (n + 1) = Real.exp (-((n + 1 : ℕ) : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  ring

theorem borel_coefficient_positive (n : ℕ) : 0 < borelCoefficient (n + 1) := by
  rw [borel_coefficient_formula]
  positivity

theorem borel_coefficient_nonnegative (n : ℕ) : 0 ≤ borelCoefficient n := by
  cases n with
  | zero => rw [borel_coefficient_zero]
  | succ n => exact (borel_coefficient_positive n).le

end
end Sigma
