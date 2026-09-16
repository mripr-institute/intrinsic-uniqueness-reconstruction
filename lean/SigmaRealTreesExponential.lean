import SigmaRealCharacteristic

namespace Sigma
noncomputable section
open PowerSeries
open scoped BigOperators

variable (K : Type*) [Field K] [CharZero K]

/-- Finite Taylor polynomial of the formal exponential at a formal argument. -/
def treeExpPartial (F : PowerSeries K) (m : ℕ) : PowerSeries K :=
  ∑ j ∈ Finset.range m, C K ((j.factorial : K)⁻¹) * F ^ j

/-- Actual coefficientwise substitution exp(F), valid for F with zero constant.
Every coefficient is a finite sum of the native powers of F. -/
def treeExp (F : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => coeff K n (treeExpPartial K F (n + 1))

omit [CharZero K] in
theorem tree_power_coeff_congr (F G : PowerSeries K) (n j : ℕ)
    (h : ∀ i ≤ n, coeff K i F = coeff K i G) :
    coeff K n (F ^ j) = coeff K n (G ^ j) := by
  have hd : (X : PowerSeries K) ^ (n + 1) ∣ F - G := by
    apply X_pow_dvd_iff.mpr
    intro i hi
    simp [h i (by omega)]
  have hp := hd.trans (sub_dvd_pow_sub_pow F G j)
  have hc := X_pow_dvd_iff.mp hp n (Nat.lt_succ_self n)
  exact sub_eq_zero.mp (by simpa only [map_sub] using hc)

omit [CharZero K] in
theorem tree_power_coeff_above (F : PowerSeries K) (hF : constantCoeff K F = 0)
    (n j : ℕ) (hnj : n < j) : coeff K n (F ^ j) = 0 := by
  have hd : (X : PowerSeries K) ∣ F := X_dvd_iff.mpr hF
  exact X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hd j) n hnj

omit [CharZero K] in
theorem tree_exp_coeff_congr (F G : PowerSeries K) (n : ℕ)
    (h : ∀ i ≤ n, coeff K i F = coeff K i G) :
    coeff K n (treeExp K F) = coeff K n (treeExp K G) := by
  simp only [treeExp, coeff_mk, treeExpPartial, map_sum, coeff_C_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [tree_power_coeff_congr K F G n j h]

omit [CharZero K] in
theorem tree_exp_constant (F : PowerSeries K) : constantCoeff K (treeExp K F) = 1 := by
  simp [treeExp, treeExpPartial]

omit [CharZero K] in
theorem tree_exp_partial_coeff (F : PowerSeries K) (hF : constantCoeff K F = 0)
    (n m : ℕ) (hnm : n < m) :
    coeff K n (treeExpPartial K F m) = coeff K n (treeExp K F) := by
  simp only [treeExpPartial, map_sum, coeff_C_mul, treeExp, coeff_mk]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j hj hnot
  have hnj : n < j := by simpa only [Finset.mem_range, not_lt] using hnot
  rw [tree_power_coeff_above K F hF n j hnj, mul_zero]

omit [CharZero K] in
theorem tree_exp_partial_error (F : PowerSeries K) (hF : constantCoeff K F = 0)
    (m : ℕ) : (X : PowerSeries K) ^ m ∣ treeExp K F - treeExpPartial K F m := by
  apply X_pow_dvd_iff.mpr
  intro n hn
  simp only [map_sub, tree_exp_partial_coeff K F hF n m hn, sub_self]

theorem tree_factorial_inverse_succ (j : ℕ) :
    ((j + 1).factorial : K)⁻¹ * ((j + 1 : ℕ) : K) = (j.factorial : K)⁻¹ := by
  have hj : ((j + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev]
  rw [mul_assoc, inv_mul_cancel₀ hj, mul_one]

theorem tree_exp_partial_derivative (F : PowerSeries K) (m : ℕ) :
    derivative K (treeExpPartial K F (m + 1)) = derivative K F * treeExpPartial K F m := by
  induction m with
  | zero => simp [treeExpPartial]
  | succ m ih =>
    simp only [treeExpPartial, Finset.sum_range_succ] at ih ⊢
    rw [map_add, ih, Derivation.leibniz, derivative_C, smul_zero, add_zero,
      Derivation.leibniz_pow]
    simp only [Nat.succ_sub_one, smul_eq_mul, nsmul_eq_mul]
    have hc := congrArg (C K) (tree_factorial_inverse_succ K m)
    simp only [map_mul, map_natCast] at hc
    linear_combination (F ^ m * derivative K F) * hc

theorem tree_exp_derivative (F : PowerSeries K) (hF : constantCoeff K F = 0) :
    derivative K (treeExp K F) = derivative K F * treeExp K F := by
  apply PowerSeries.ext
  intro n
  have hd := tree_exp_partial_derivative K F (n + 1)
  have hl : coeff K n (derivative K (treeExpPartial K F (n + 1 + 1))) =
      coeff K n (derivative K (treeExp K F)) := by
    rw [coeff_derivative, coeff_derivative,
      tree_exp_partial_coeff K F hF (n + 1) (n + 1 + 1) (by omega)]
  have he := tree_exp_partial_error K F hF (n + 1)
  have hh := he.mul_left (derivative K F)
  have hh' := X_pow_dvd_iff.mp hh n (Nat.lt_succ_self n)
  rw [mul_sub, map_sub] at hh'
  have hr := sub_eq_zero.mp hh'
  rw [← hl, hd]
  exact hr.symm

theorem tree_exp_neg_product (F : PowerSeries K) (hF : constantCoeff K F = 0) :
    treeExp K F * treeExp K (-F) = 1 := by
  apply PowerSeries.derivative.ext
  · rw [Derivation.leibniz, tree_exp_derivative K F hF,
      tree_exp_derivative K (-F) (by simp [hF]), map_neg, Derivation.map_one_eq_zero]
    simp only [smul_eq_mul]
    ring
  · simp [tree_exp_constant]

end
end Sigma
