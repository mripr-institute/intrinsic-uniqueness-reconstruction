import SigmaRealSeries
import Mathlib.RingTheory.PowerSeries.WellKnown

/-! The actual formal exponential quotient and its Todd coefficient tower.
The proof uses formal differentiation of the quotient identity. Extracting
degree n from the differential identity for exp(kX) T^n cancels the derivative
term and gives the rising-factorial recurrence for every twist. -/

namespace Sigma
noncomputable section
open PowerSeries
open scoped BigOperators

variable (K : Type*) [Field K] [CharZero K]

def formalExponential (k : K) : PowerSeries K := rescale k (PowerSeries.exp K)

def toddDenominator : PowerSeries K :=
  PowerSeries.mk fun n => coeff K (n + 1) (1 - formalExponential K (-1))

/-- X/(1-exp(-X)) means the inverse of its shifted unit denominator. -/
def formalTodd : PowerSeries K := (toddDenominator K)⁻¹

theorem formal_exponential_constant (k : K) :
    constantCoeff K (formalExponential K k) = 1 := by
  simp [formalExponential, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale]

theorem formal_exponential_derivative (k : K) :
    derivative K (formalExponential K k) = C K k * formalExponential K k := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_derivative, formalExponential, coeff_rescale, coeff_exp, coeff_C_mul]
  rw [Nat.factorial_succ]
  simp only [map_div₀, map_one, map_natCast, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hn : (n : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [pow_succ]
  field_simp
  ring

theorem todd_denominator_constant : constantCoeff K (toddDenominator K) = 1 := by
  simp [toddDenominator, formalExponential, coeff_rescale, coeff_exp]

theorem todd_denominator_mul_X :
    toddDenominator K * X = 1 - formalExponential K (-1) := by
  have h := eq_shift_mul_X_add_const (1 - formalExponential K (-1))
  simpa only [map_sub, map_one, formal_exponential_constant, sub_self, map_zero,
    add_zero, toddDenominator] using h.symm

theorem todd_denominator_mul_todd : toddDenominator K * formalTodd K = 1 := by
  apply PowerSeries.mul_inv_cancel
  rw [todd_denominator_constant]
  exact one_ne_zero

theorem formal_todd_constant : constantCoeff K (formalTodd K) = 1 := by
  simp [formalTodd, constantCoeff_inv, todd_denominator_constant]

theorem formal_todd_quotient_identity :
    (1 - formalExponential K (-1)) * formalTodd K = X := by
  rw [← todd_denominator_mul_X]
  calc
    toddDenominator K * X * formalTodd K =
        (toddDenominator K * formalTodd K) * X := by ring
    _ = X := by rw [todd_denominator_mul_todd, one_mul]

theorem formal_todd_riccati :
    X * derivative K (formalTodd K) =
      (1 + X) * formalTodd K - formalTodd K ^ 2 := by
  have hq := formal_todd_quotient_identity K
  have hd := congrArg (derivative K) hq
  rw [Derivation.leibniz, map_sub, Derivation.map_one_eq_zero,
    formal_exponential_derivative, derivative_X] at hd
  simp only [map_neg, map_one, neg_one_mul, sub_neg_eq_add, zero_add,
    smul_eq_mul] at hd
  linear_combination (formalTodd K) * hd +
    (formalTodd K - derivative K (formalTodd K)) * hq

theorem formal_twisted_todd_differential (k : K) (n : ℕ) :
    X * derivative K (formalExponential K k * formalTodd K ^ (n + 1)) =
      C K ((n + 1 : ℕ) : K) * (formalExponential K k * formalTodd K ^ (n + 1)) +
      C K (k + ((n + 1 : ℕ) : K)) * X *
        (formalExponential K k * formalTodd K ^ (n + 1)) -
      C K ((n + 1 : ℕ) : K) *
        (formalExponential K k * formalTodd K ^ (n + 2)) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, formal_exponential_derivative]
  simp only [Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul, map_add, map_natCast]
  have h := formal_todd_riccati K
  simp only [pow_succ] at *
  linear_combination ((n + 1 : ℕ) : PowerSeries K) *
    formalExponential K k * formalTodd K ^ n * h

theorem formal_twisted_todd_coeff_succ (k : K) (n : ℕ) :
    coeff K (n + 1) (formalExponential K k * formalTodd K ^ (n + 2)) =
      (k + ((n + 1 : ℕ) : K)) / ((n + 1 : ℕ) : K) *
        coeff K n (formalExponential K k * formalTodd K ^ (n + 1)) := by
  have h := congrArg (coeff K (n + 1)) (formal_twisted_todd_differential K k n)
  rw [coeff_succ_X_mul, coeff_derivative] at h
  simp only [map_sub, map_add, coeff_C_mul, mul_assoc, coeff_succ_X_mul] at h
  rw [← map_add, coeff_C_mul, coeff_succ_X_mul] at h
  have hn : ((n + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast at h hn ⊢
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hn).2
  linear_combination h

theorem formal_twisted_todd_coeff (k : K) (n : ℕ) :
    coeff K n (formalExponential K k * formalTodd K ^ (n + 1)) =
      (∏ j ∈ Finset.range n, (k + (j : K) + 1)) / (n.factorial : K) := by
  induction n with
  | zero => simp [formal_exponential_constant, formal_todd_constant]
  | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by omega, formal_twisted_todd_coeff_succ, ih,
        Finset.prod_range_succ, Nat.factorial_succ]
      push_cast
      have hn : (n : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have hf : (n.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      field_simp
      ring

end
end Sigma
