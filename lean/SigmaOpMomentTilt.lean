import SigmaOpMomentGrowth
import SigmaOpMixing

namespace Sigma
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

/-- The zeroth exact moment itself forces normalization and finiteness. -/
theorem operator_factorial_moments_isProbability (μ : Measure ℝ)
    (hm : OpFactorialMoments μ) : IsProbabilityMeasure μ := by
  have hi : Integrable (fun _ : ℝ => (1 : ℝ)) μ := by
    simpa using operator_factorial_moments_integrable μ hm 0
  have hfin : μ Set.univ < ⊤ := (integrable_const_iff.mp hi).resolve_left one_ne_zero
  have h0 := hm 0
  simp only [pow_zero, integral_const, smul_eq_mul, mul_one, Nat.factorial_one,
    Nat.cast_one] at h0
  exact ⟨(ENNReal.toReal_eq_toReal hfin.ne ENNReal.one_ne_top).mp (by simpa using h0)⟩

theorem op_abs_pow_bound (t : ℝ) (k : ℕ) :
    |t| ^ k ≤ 1 + t ^ (2 * ((k + 1) / 2)) := by
  have he : t ^ (2 * ((k + 1) / 2)) = |t| ^ (2 * ((k + 1) / 2)) := by
    simp only [pow_mul, sq_abs]
  rw [he]
  by_cases ht : |t| ≤ 1
  · have h := pow_le_pow_left₀ (abs_nonneg t) ht k
    simp only [one_pow] at h
    exact h.trans (le_add_of_nonneg_right (by positivity))
  · have h := pow_le_pow_right₀ (le_of_not_ge ht) (show k ≤ 2 * ((k + 1) / 2) by omega)
    linarith

theorem operator_factorial_absolute_moment_bound (μ : Measure ℝ)
    (hm : OpFactorialMoments μ) (k : ℕ) :
    (∫ t : ℝ, |t| ^ k ∂μ) ≤ 1 + ((k + 2).factorial : ℝ) := by
  letI := operator_factorial_moments_isProbability μ hm
  have hi : Integrable (fun t : ℝ => |t| ^ k) μ := by
    simpa only [Real.norm_eq_abs, abs_pow] using
      (operator_factorial_moments_integrable μ hm k).norm
  have he := operator_factorial_moments_integrable μ hm (2 * ((k + 1) / 2))
  have hb := integral_mono hi ((integrable_const (1 : ℝ)).add he) (fun t => op_abs_pow_bound t k)
  simp only [Pi.add_apply] at hb
  rw [integral_add (integrable_const _) he, integral_const] at hb
  simp only [measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul] at hb
  rw [hm] at hb
  have hfac : ((2 * ((k + 1) / 2) + 1).factorial : ℝ) ≤ ((k + 2).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (show 2 * ((k + 1) / 2) + 1 ≤ k + 2 by omega)
  exact hb.trans (add_le_add_left hfac 1)

theorem op_factorial_ratio (n k : ℕ) :
    ((n + k).factorial : ℝ) / (n.factorial : ℝ) =
      (k.factorial : ℝ) * ((n + k).choose k : ℝ) := by
  have hh := congrArg (fun z : ℕ => (z : ℝ))
    (Nat.add_choose_mul_factorial_mul_factorial n k)
  push_cast at hh
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  apply (div_eq_iff hn).mpr
  nlinarith

def opWeightedExpTerm (m : ℕ) (s : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  t ^ m * (s * t) ^ n / (n.factorial : ℝ)

theorem opWeightedExpTerm_integrable (μ : Measure ℝ) (hm : OpFactorialMoments μ)
    (m : ℕ) (s : ℝ) (n : ℕ) : Integrable (opWeightedExpTerm m s n) μ := by
  convert ((operator_factorial_moments_integrable μ hm (m + n)).const_mul
    (s ^ n)).div_const (n.factorial : ℝ) using 1
  funext t
  simp only [opWeightedExpTerm, mul_pow, pow_add]
  ring

theorem opWeightedExpTerm_integral (μ : Measure ℝ) (hm : OpFactorialMoments μ)
    (m : ℕ) (s : ℝ) (n : ℕ) :
    (∫ t, opWeightedExpTerm m s n t ∂μ) =
      ((m + 1).factorial : ℝ) * (((n + (m + 1)).choose (m + 1) : ℝ) * s ^ n) := by
  have he : opWeightedExpTerm m s n =
      fun t => s ^ n * t ^ (n + (m + 1) - 1) / (n.factorial : ℝ) := by
    funext t
    simp only [opWeightedExpTerm, show n + (m + 1) - 1 = m + n by omega,
      pow_add, mul_pow]
    ring
  rw [he, integral_div, integral_mul_left, hm]
  rw [show n + (m + 1) - 1 + 1 = n + (m + 1) by omega]
  rw [mul_div_assoc, op_factorial_ratio]
  ring

theorem opWeightedExpTerm_norm_integral_bound (μ : Measure ℝ)
    (hm : OpFactorialMoments μ) (m : ℕ) (s : ℝ) (n : ℕ) :
    (∫ t, ‖opWeightedExpTerm m s n t‖ ∂μ) ≤
      |s| ^ n / (n.factorial : ℝ) +
      ((m + 2).factorial : ℝ) * (((n + (m + 2)).choose (m + 2) : ℝ) * |s| ^ n) := by
  have he : (fun t => ‖opWeightedExpTerm m s n t‖) =
      fun t => (|s| ^ n / (n.factorial : ℝ)) * |t| ^ (m + n) := by
    funext t
    simp only [opWeightedExpTerm, Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
      show ∀ n : ℕ, |(n : ℝ)| = (n : ℝ) from fun n => abs_of_nonneg (Nat.cast_nonneg n),
      pow_add]
    ring
  rw [he, integral_mul_left]
  calc
    _ ≤ (|s| ^ n / (n.factorial : ℝ)) * (1 + ((m + n + 2).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (operator_factorial_absolute_moment_bound μ hm (m + n))
        (by positivity)
    _ = _ := by
      rw [show m + n + 2 = n + (m + 2) by omega]
      have hh := op_factorial_ratio n (m + 2)
      calc
        _ = |s| ^ n / (n.factorial : ℝ) +
            |s| ^ n * (((n + (m + 2)).factorial : ℝ) / (n.factorial : ℝ)) := by ring
        _ = _ := by rw [hh]; ring

theorem operator_factorial_moments_weighted_local_mgf (μ : Measure ℝ)
    (hm : OpFactorialMoments μ) (m : ℕ) {s : ℝ} (hs : |s| < 1) :
    (∫ t : ℝ, t ^ m * Real.exp (s * t) ∂μ) =
      ((m + 1).factorial : ℝ) / (1 - s) ^ (m + 2) := by
  have hmajor : Summable (fun n : ℕ => |s| ^ n / (n.factorial : ℝ) +
      ((m + 2).factorial : ℝ) * (((n + (m + 2)).choose (m + 2) : ℝ) * |s| ^ n)) := by
    apply Summable.add
    · simpa [opExpTerm] using (opExpTerm_hasSum |s| 1).summable
    · exact (summable_choose_mul_geometric_of_norm_lt_one (m + 2)
        (by simpa using hs : ‖|s|‖ < 1)).mul_left _
  have hnorm : Summable (fun n : ℕ => ∫ t, ‖opWeightedExpTerm m s n t‖ ∂μ) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _))
      (opWeightedExpTerm_norm_integral_bound μ hm m s) hmajor
  have hh := hasSum_integral_of_summable_integral_norm
    (opWeightedExpTerm_integrable μ hm m s) hnorm
  have hsum : ∀ t : ℝ, HasSum (fun n => opWeightedExpTerm m s n t)
      (t ^ m * Real.exp (s * t)) := by
    intro t
    simpa only [opWeightedExpTerm, opExpTerm, mul_div_assoc] using
      (opExpTerm_hasSum s t).mul_left (t ^ m)
  simp_rw [(hsum _).tsum_eq, opWeightedExpTerm_integral μ hm] at hh
  have hg := (hasSum_choose_mul_geometric_of_norm_lt_one (r := s) (m + 1) hs).mul_left
    ((m + 1).factorial : ℝ)
  simpa only [mul_one_div, Nat.add_assoc] using hh.unique hg

end
end Sigma
