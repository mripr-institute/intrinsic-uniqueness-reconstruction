import SigmaProbGamma
import Mathlib.Data.Nat.Choose.Sum

/-! The marked Laguerre coefficients and the triangular probability-moment
recovery in final:O7.  These are the actual finite-sum polynomials of the draft.
-/

namespace Sigma
noncomputable section
open MeasureTheory
open scoped BigOperators

def opLaguerreCoefficient (n k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * ((n + 1).choose (k + 1) : ℝ) / (k.factorial : ℝ)

def opLaguerre (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), opLaguerreCoefficient n k * t ^ k

theorem opLaguerre_first_three (t : ℝ) :
    opLaguerre 0 t = 1 ∧ opLaguerre 1 t = 2 - t ∧
      opLaguerre 2 t = t ^ 2 / 2 - 3 * t + 3 := by
  norm_num [opLaguerre, opLaguerreCoefficient, Finset.sum_range_succ]
  constructor <;> ring

theorem opLaguerre_leading_coefficient (n : ℕ) :
    opLaguerreCoefficient n n = (-1 : ℝ) ^ n / (n.factorial : ℝ) := by
  simp [opLaguerreCoefficient]

theorem opLaguerre_leading_coefficient_ne_zero (n : ℕ) :
    opLaguerreCoefficient n n ≠ 0 := by
  rw [opLaguerre_leading_coefficient]
  exact div_ne_zero (pow_ne_zero n (by norm_num))
    (by exact_mod_cast Nat.factorial_ne_zero n)

theorem opLaguerre_integral (μ : Measure ℝ)
    (hi : ∀ n : ℕ, Integrable (fun t : ℝ => t ^ n) μ) (n : ℕ) :
    (∫ t, opLaguerre n t ∂μ) =
      ∑ k ∈ Finset.range (n + 1), opLaguerreCoefficient n k * (∫ t : ℝ, t ^ k ∂μ) := by
  unfold opLaguerre
  rw [integral_finset_sum]
  · simp only [integral_mul_left]
  · intro k hk
    exact (hi k).const_mul _

theorem opLaguerre_coefficient_factorial (n k : ℕ) :
    opLaguerreCoefficient n k * ((k + 1).factorial : ℝ) =
      (n + 1 : ℝ) * ((-1 : ℝ) ^ k * (n.choose k : ℝ)) := by
  have hc : ((n + 1).choose (k + 1) : ℝ) * (k + 1 : ℝ) =
      (n + 1 : ℝ) * (n.choose k : ℝ) := by
    exact_mod_cast (Nat.succ_mul_choose_eq n k).symm
  have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  unfold opLaguerreCoefficient
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  nlinarith [congrArg (fun x : ℝ => (-1 : ℝ) ^ k * x) hc]

theorem opLaguerre_factorial_sum_zero (n : ℕ) (hn : n ≠ 0) :
    (∑ k ∈ Finset.range (n + 1),
      opLaguerreCoefficient n k * ((k + 1).factorial : ℝ)) = 0 := by
  simp_rw [opLaguerre_coefficient_factorial]
  rw [← Finset.mul_sum]
  have hs : (∑ k ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ k * (n.choose k : ℝ)) = 0 := by
    exact_mod_cast (Int.alternating_sum_range_choose_of_ne hn)
  rw [hs, mul_zero]

/-- The canonical probability satisfies the complete marked orthogonality clause. -/
theorem operator_gamma_laguerre_orthogonality (n : ℕ) (hn : n ≠ 0) :
    (∫ t, opLaguerre n t ∂gammaProbability) = 0 := by
  rw [opLaguerre_integral gammaProbability gamma_probability_monomial_integrable]
  simp_rw [gamma_probability_moments]
  exact opLaguerre_factorial_sum_zero n hn

/-- The forward moment-recovery step in final:O7, for probabilities on all of R.
No density, support, or Gamma moment values are assumed for the candidate. -/
theorem operator_laguerre_orthogonality_recovers_moments (μ : Measure ℝ)
    [IsProbabilityMeasure μ]
    (hi : ∀ n : ℕ, Integrable (fun t : ℝ => t ^ n) μ)
    (hL : ∀ n : ℕ, n ≠ 0 → (∫ t, opLaguerre n t ∂μ) = 0) :
    ∀ n : ℕ, (∫ t : ℝ, t ^ n ∂μ) = ((n + 1).factorial : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simp
      have hμ := hL n hn
      have hγ := opLaguerre_factorial_sum_zero n hn
      rw [opLaguerre_integral μ hi, Finset.sum_range_succ] at hμ
      rw [Finset.sum_range_succ] at hγ
      have hs : (∑ k ∈ Finset.range n,
          opLaguerreCoefficient n k * (∫ t : ℝ, t ^ k ∂μ)) =
          ∑ k ∈ Finset.range n,
            opLaguerreCoefficient n k * ((k + 1).factorial : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ih k (Finset.mem_range.mp hk)]
      rw [hs] at hμ
      apply mul_left_cancel₀ (opLaguerre_leading_coefficient_ne_zero n)
      linarith

theorem operator_laguerre_orthogonality_iff_moments (μ : Measure ℝ)
    [IsProbabilityMeasure μ]
    (hi : ∀ n : ℕ, Integrable (fun t : ℝ => t ^ n) μ) :
    (∀ n : ℕ, n ≠ 0 → (∫ t, opLaguerre n t ∂μ) = 0) ↔
      (∀ n : ℕ, (∫ t : ℝ, t ^ n ∂μ) = ((n + 1).factorial : ℝ)) := by
  constructor
  · exact operator_laguerre_orthogonality_recovers_moments μ hi
  · intro hm n hn
    rw [opLaguerre_integral μ hi]
    simp_rw [hm]
    exact opLaguerre_factorial_sum_zero n hn

end
end Sigma
