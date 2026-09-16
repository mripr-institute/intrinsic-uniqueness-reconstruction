import SigmaRealToddAlgebra

namespace Sigma
noncomputable section
open PowerSeries

variable (K : Type*) [Field K] [CharZero K]

def formalShift (F : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => coeff K (n + 1) F

omit [CharZero K] in
theorem formal_shift_mul_X (F : PowerSeries K) (hF : constantCoeff K F = 0) :
    formalShift K F * X = F := by
  have h := eq_shift_mul_X_add_const F
  simpa only [hF, map_zero, add_zero, formalShift] using h.symm

theorem formal_exponential_mul (a b : K) :
    formalExponential K a * formalExponential K b = formalExponential K (a + b) :=
  PowerSeries.exp_mul_exp_eq_exp_add a b

theorem formal_exponential_rescale (a b : K) :
    rescale a (formalExponential K b) = formalExponential K (a * b) := by
  simp only [formalExponential, rescale_rescale, mul_comm]

theorem formal_exponential_inverse_product (a : K) :
    formalExponential K a * formalExponential K (-a) = 1 := by
  rw [formal_exponential_mul, add_neg_cancel, formal_exponential_zero]

theorem formal_exponential_coeff_one (a : K) : coeff K 1 (formalExponential K a) = a := by
  simp [formalExponential, coeff_rescale, coeff_exp]

theorem formal_exponential_sub_one_ne_zero (a : K) (ha : a ≠ 0) :
    formalExponential K a - 1 ≠ 0 := by
  intro h
  have hc := congrArg (coeff K 1) h
  apply ha
  simpa [formal_exponential_coeff_one] using hc

theorem rescaled_todd_quotient (a : K) :
    (1 - formalExponential K (-a)) * rescale a (formalTodd K) = C K a * X := by
  have h := congrArg (rescale a) (formal_todd_quotient_identity K)
  simpa only [map_mul, map_sub, map_one, formal_exponential_rescale,
    mul_neg_one, rescale_X] using h

/-- The unit denominator is 2*sinh(X/2)/X. -/
def ahatDenominator : PowerSeries K := formalShift K
  (formalExponential K (1 / 2) - formalExponential K (-(1 / 2)))

def formalAhat : PowerSeries K := (ahatDenominator K)⁻¹

/-- The unit denominator is (exp(2X)-1)/X, with constant coefficient 2. -/
def lDenominator : PowerSeries K := formalShift K (formalExponential K 2 - 1)

/-- X/tanh(X), with the unit quotient interpreted before inversion. -/
def formalL : PowerSeries K :=
  (formalExponential K 2 + 1) * (lDenominator K)⁻¹

theorem ahat_denominator_constant : constantCoeff K (ahatDenominator K) = 1 := by
  norm_num [ahatDenominator, formalShift, formal_exponential_coeff_one]

theorem ahat_denominator_mul_X : ahatDenominator K * X =
    formalExponential K (1 / 2) - formalExponential K (-(1 / 2)) := by
  apply formal_shift_mul_X
  simp [formal_exponential_constant]

theorem formal_ahat_constant : constantCoeff K (formalAhat K) = 1 := by
  simp [formalAhat, constantCoeff_inv, ahat_denominator_constant]

theorem formal_ahat_quotient :
    (formalExponential K (1 / 2) - formalExponential K (-(1 / 2))) *
      formalAhat K = X := by
  rw [← ahat_denominator_mul_X]
  calc
    ahatDenominator K * X * formalAhat K =
        (ahatDenominator K * formalAhat K) * X := by ring
    _ = X := by
      rw [formalAhat, PowerSeries.mul_inv_cancel _ (by simp [ahat_denominator_constant]),
        one_mul]

theorem l_denominator_constant : constantCoeff K (lDenominator K) = 2 := by
  simp [lDenominator, formalShift, formal_exponential_coeff_one]

theorem l_denominator_mul_X : lDenominator K * X = formalExponential K 2 - 1 := by
  apply formal_shift_mul_X
  simp [formal_exponential_constant]

theorem formal_L_constant : constantCoeff K (formalL K) = 1 := by
  norm_num [formalL, constantCoeff_inv, l_denominator_constant, formal_exponential_constant]

theorem formal_L_quotient :
    (formalExponential K 2 - 1) * formalL K = X * (formalExponential K 2 + 1) := by
  rw [← l_denominator_mul_X, formalL]
  calc
    (lDenominator K * X) * ((formalExponential K 2 + 1) * (lDenominator K)⁻¹) =
        (lDenominator K * (lDenominator K)⁻¹) * X * (formalExponential K 2 + 1) := by ring
    _ = X * (formalExponential K 2 + 1) := by
      rw [PowerSeries.mul_inv_cancel _ (by simp [l_denominator_constant]), one_mul]

theorem formal_ahat_to_todd :
    formalExponential K (1 / 2) * formalAhat K = formalTodd K := by
  have he : formalExponential K (-1) * formalExponential K (1 / 2) =
      formalExponential K (-(1 / 2)) := by
    rw [formal_exponential_mul]
    norm_num
  have hq := formal_ahat_quotient K
  have ht := formal_todd_quotient_identity K
  have hn : 1 - formalExponential K (-1) ≠ 0 := by
    intro h
    apply formal_exponential_sub_one_ne_zero K (-1) (by norm_num)
    linear_combination -h
  apply mul_left_cancel₀ hn
  linear_combination hq - ht - formalAhat K * he

theorem formal_todd_to_ahat :
    formalExponential K (-(1 / 2)) * formalTodd K = formalAhat K := by
  rw [← formal_ahat_to_todd]
  rw [← mul_assoc, formal_exponential_mul]
  simp only [neg_add_cancel, formal_exponential_zero, one_mul]

theorem formal_todd_to_L : formalL K = rescale 2 (formalTodd K) - X := by
  have ht := rescaled_todd_quotient K 2
  have hl := formal_L_quotient K
  have he := formal_exponential_inverse_product K 2
  have hn := formal_exponential_sub_one_ne_zero K 2 (by norm_num)
  apply mul_left_cancel₀ hn
  simp only [map_ofNat] at ht
  linear_combination hl - formalExponential K 2 * ht - rescale 2 (formalTodd K) * he

theorem formal_L_to_todd :
    rescale (1 / 2 : K) (formalL K) + C K (1 / 2) * X = formalTodd K := by
  rw [formal_todd_to_L]
  simp [map_sub, rescale_rescale, rescale_X]

end
end Sigma
