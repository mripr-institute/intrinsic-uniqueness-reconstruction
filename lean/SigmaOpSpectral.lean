import SigmaOperators
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! Exact analytic spectral series and the Gamma mixing integral.
These are eigenvalue-series theorems; identifying them as traces of the
specified unbounded Laguerre realization is a separate operator theorem.
-/

namespace Sigma
noncomputable section
open MeasureTheory Set

theorem operator_complex_heat_eigenvalue_hasSum {τ : ℂ} (hτ : 0 < τ.re) :
    HasSum (fun n : ℕ => Complex.exp (-τ * n))
      ((1 - Complex.exp (-τ))⁻¹) := by
  have he : ‖Complex.exp (-τ)‖ < 1 := by
    rw [Complex.norm_eq_abs, Complex.abs_exp, Real.exp_lt_one_iff, Complex.neg_re]
    linarith
  convert hasSum_geometric_of_norm_lt_one he using 1
  funext n
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem operator_complex_heat_eigenvalue_summable_iff (τ : ℂ) :
    Summable (fun n : ℕ => Complex.exp (-τ * n)) ↔ 0 < τ.re := by
  have heq : (fun n : ℕ => Complex.exp (-τ * n)) =
      (fun n : ℕ => (Complex.exp (-τ)) ^ n) := by
    funext n
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  rw [heq, summable_geometric_iff_norm_lt_one,
    Complex.norm_eq_abs, Complex.abs_exp, Real.exp_lt_one_iff, Complex.neg_re]
  constructor <;> intro h <;> linarith

theorem operator_complex_zeta_eigenvalue_summable_iff (s : ℂ) :
    Summable (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) ↔ 1 < s.re := by
  have h := (summable_nat_add_iff 1
    (f := fun n : ℕ => 1 / (n : ℂ) ^ s)).trans
    (Complex.summable_one_div_nat_cpow (p := s))
  simpa only [Nat.cast_add, Nat.cast_one] using h

theorem operator_zeta_eigenvalue_hasSum {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) (riemannZeta s) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  exact ((operator_complex_zeta_eigenvalue_summable_iff s).mpr hs).hasSum

theorem operator_shifted_real_eigenvalue_summable_iff (a s : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => 1 / (n + a : ℝ) ^ s) ↔ 1 < s := by
  have he : (fun n : ℕ => 1 / |(n : ℝ) + a| ^ s) =
      (fun n : ℕ => 1 / ((n : ℝ) + a) ^ s) := by
    funext n
    rw [abs_of_pos (by positivity : 0 < (n : ℝ) + a)]
  rw [← he]
  exact Real.summable_one_div_nat_add_rpow a s

theorem operator_first_resolvent_eigenvalues_not_summable (a : ℝ) (ha : 0 < a) :
    ¬ Summable (fun n : ℕ => 1 / (n + a : ℝ)) := by
  have h := operator_shifted_real_eigenvalue_summable_iff a 1 ha
  simpa using h

theorem operator_squared_resolvent_eigenvalues_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => 1 / (n + a : ℝ) ^ (2 : ℕ)) := by
  have h := (operator_shifted_real_eigenvalue_summable_iff a 2 ha).mpr (by norm_num)
  simpa only [Real.rpow_two] using h

/-- The scalar integral in final:O5, for every nonnegative spectral value. -/
theorem operator_gamma_mixing_integral {lam : ℝ} (hlam : 0 ≤ lam) :
    (∫ t : ℝ in Ioi 0, t * Real.exp (-(1 + lam) * t)) =
      (1 / (1 + lam)) ^ (2 : ℕ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 2) (r := 1 + lam) (by norm_num) (by positivity)
  have hg : Real.Gamma 2 = 1 := by
    simp
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    neg_mul, Real.rpow_two, hg, mul_one] using h

theorem operator_gamma_mixing_integer_integral (n : ℕ) :
    (∫ t : ℝ in Ioi 0, t * Real.exp (-(1 + (n : ℝ)) * t)) =
      (1 / (1 + (n : ℝ))) ^ (2 : ℕ) :=
  operator_gamma_mixing_integral (Nat.cast_nonneg n)

end
end Sigma
