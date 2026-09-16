import SigmaRealTreesNormalization
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace Sigma
noncomputable section
open PowerSeries MeasureTheory
open scoped BigOperators

def borelPMF : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal (borelCoefficient n), by
    apply ENNReal.summable.hasSum_iff.mpr
    rw [← ENNReal.ofReal_tsum_of_nonneg borel_coefficient_nonnegative borel_coefficients_summable,
      borel_coefficients_sum_one, ENNReal.ofReal_one]⟩

theorem borel_pmf_apply (n : ℕ) : borelPMF n = ENNReal.ofReal (borelCoefficient n) := rfl

def borelProbability : Measure ℕ := borelPMF.toMeasure

instance borel_probability_isProbability : IsProbabilityMeasure borelProbability :=
  inferInstanceAs (IsProbabilityMeasure borelPMF.toMeasure)

theorem borel_probability_singleton (n : ℕ) :
    borelProbability {n} = ENNReal.ofReal (borelCoefficient n) :=
  borelPMF.toMeasure_apply_singleton n (measurableSet_singleton n)

theorem borel_probability_zero : borelProbability {0} = 0 := by
  rw [borel_probability_singleton, borel_coefficient_zero, ENNReal.ofReal_zero]

theorem borel_probability_positive_singletons (n : ℕ) :
    0 < borelProbability {n + 1} := by
  rw [borel_probability_singleton, ENNReal.ofReal_pos]
  exact borel_coefficient_positive n

theorem borel_probability_identified (μ : Measure ℕ)
    (hμ : ∀ n, μ {n} = ENNReal.ofReal (borelCoefficient n)) : μ = borelProbability := by
  apply Measure.ext_of_singleton
  intro n
  rw [hμ n, borel_probability_singleton]

/-- Independent sampling: the second PMF is fixed and does not depend on the first draw. -/
def independentNatSum (p q : PMF ℕ) : PMF ℕ :=
  p.bind fun a => q.map (fun b => a + b)

theorem translated_nat_pmf (q : PMF ℕ) (a n : ℕ) :
    q.map (fun b => a + b) n = if a ≤ n then q (n - a) else 0 := by
  rw [PMF.map_apply]
  by_cases ha : a ≤ n
  · rw [if_pos ha]
    have htest (b : ℕ) : n = a + b ↔ b = n - a := by omega
    simp_rw [htest]
    rw [tsum_eq_single (n - a)]
    · simp
    · intro b hb
      simp [hb]
  · rw [if_neg ha]
    have htest (b : ℕ) : n ≠ a + b := by omega
    simp only [htest, if_false, tsum_zero]

theorem independent_nat_sum_apply (p q : PMF ℕ) (n : ℕ) :
    independentNatSum p q n = ∑ a ∈ Finset.range (n + 1), p a * q (n - a) := by
  simp only [independentNatSum, PMF.bind_apply, translated_nat_pmf]
  have ht : (∑' a, p a * if a ≤ n then q (n - a) else 0) =
      ∑ a ∈ Finset.range (n + 1), p a * if a ≤ n then q (n - a) else 0 := by
    apply tsum_eq_sum
    intro a ha
    have hn : ¬ a ≤ n := by
      have hh : ¬ a < n + 1 := by simpa only [Finset.mem_range] using ha
      omega
    simp [hn]
  rw [ht]
  apply Finset.sum_congr rfl
  intro a ha
  rw [if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp ha))]

def borelForestPMF : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | k + 1 => independentNatSum (borelForestPMF k) borelPMF

/-- Coefficients identify the law of the explicitly constructed independent sum. -/
theorem borel_forest_pmf_coefficients (k n : ℕ) :
    borelForestPMF k n = ENNReal.ofReal (coeff ℝ n (borelSeries ^ k)) := by
  induction k generalizing n with
  | zero =>
    simp only [borelForestPMF, PMF.pure_apply, pow_zero, coeff_one]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [borelForestPMF, independent_nat_sum_apply, pow_succ, coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => coeff ℝ a (borelSeries ^ k) * coeff ℝ b borelSeries) n]
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro a ha
      rw [ih, borel_pmf_apply, borelCoefficient, ENNReal.ofReal_mul
        (tree_coeff_pow_nonnegative borelSeries borel_coefficient_nonnegative k a)]
    · intro a ha
      exact mul_nonneg (tree_coeff_pow_nonnegative borelSeries borel_coefficient_nonnegative k a)
        (borel_coefficient_nonnegative (n - a))

theorem borel_independent_forest_probabilities (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    borelForestPMF k n = ENNReal.ofReal
      (Real.exp (-(n : ℝ)) * ((k : ℝ) / (n : ℝ) *
        (n : ℝ) ^ (n - k) / ((n - k).factorial : ℝ))) := by
  rw [borel_forest_pmf_coefficients, borel_forest_coefficients n k hk hkn]


theorem borel_independent_forest_below (n k : ℕ) (hn : n < k) :
    borelForestPMF k n = 0 := by
  rw [borel_forest_pmf_coefficients,
    tree_power_coeff_above ℝ borelSeries borel_series_constant n k hn, ENNReal.ofReal_zero]

end
end Sigma
