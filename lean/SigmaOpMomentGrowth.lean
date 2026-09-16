import SigmaProbGamma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Analytic consequences of the exact factorial moments on the full real line.
These are genuine integrability and integral identities for the candidate measure.
-/

namespace Sigma
noncomputable section
open MeasureTheory Filter
open scoped Topology

def OpFactorialMoments (μ : Measure ℝ) : Prop :=
  ∀ n : ℕ, (∫ t : ℝ, t ^ n ∂μ) = ((n + 1).factorial : ℝ)

theorem operator_factorial_moments_integrable (μ : Measure ℝ)
    (hm : OpFactorialMoments μ) (n : ℕ) : Integrable (fun t : ℝ => t ^ n) μ := by
  apply Integrable.of_integral_ne_zero
  rw [hm n]
  exact_mod_cast Nat.factorial_ne_zero (n + 1)

def opCoshTerm (c : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (c * t) ^ (2 * n) / ((2 * n).factorial : ℝ)

theorem opCoshTerm_nonneg (c t : ℝ) (n : ℕ) : 0 ≤ opCoshTerm c n t := by
  unfold opCoshTerm
  rw [pow_mul]
  positivity

theorem opCoshTerm_integrable (μ : Measure ℝ) (hm : OpFactorialMoments μ)
    (c : ℝ) (n : ℕ) : Integrable (opCoshTerm c n) μ := by
  have hi := ((operator_factorial_moments_integrable μ hm (2 * n)).const_mul
    (c ^ (2 * n))).div_const ((2 * n).factorial : ℝ)
  change Integrable (fun t => (c * t) ^ (2 * n) / ((2 * n).factorial : ℝ)) μ
  simpa only [mul_pow] using hi

theorem opCoshTerm_integral (μ : Measure ℝ) (hm : OpFactorialMoments μ)
    (c : ℝ) (n : ℕ) :
    (∫ t, opCoshTerm c n t ∂μ) = (2 * (n : ℝ) + 1) * c ^ (2 * n) := by
  unfold opCoshTerm
  simp_rw [mul_pow]
  rw [integral_div, integral_mul_left, hm (2 * n), Nat.factorial_succ, Nat.cast_mul]
  have hf : ((2 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * n)
  push_cast
  field_simp
  <;> ring

theorem opCoshMomentSeries_summable {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    Summable (fun n : ℕ => (2 * (n : ℝ) + 1) * c ^ (2 * n)) := by
  have hq : ‖c ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg c)]
    nlinarith
  have hlin := (summable_pow_mul_geometric_of_norm_lt_one 1 hq).mul_left (2 : ℝ)
  have hgeom := summable_geometric_of_norm_lt_one hq
  convert hlin.add hgeom using 1
  funext n
  simp only [pow_one, pow_mul]
  ring

theorem operator_factorial_moments_cosh_integrable (μ : Measure ℝ)
    (hm : OpFactorialMoments μ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    Integrable (fun t : ℝ => Real.cosh (c * t)) μ := by
  have hs := opCoshMomentSeries_summable hc0 hc1
  have hnorm : Summable (fun n : ℕ => ∫ t, ‖opCoshTerm c n t‖ ∂μ) := by
    simp_rw [Real.norm_of_nonneg (opCoshTerm_nonneg _ _ _),
      opCoshTerm_integral μ hm]
    exact hs
  have hh := hasSum_integral_of_summable_integral_norm
    (opCoshTerm_integrable μ hm c) hnorm
  have he : (∫ t, Real.cosh (c * t) ∂μ) =
      ∑' n : ℕ, (2 * (n : ℝ) + 1) * c ^ (2 * n) := by
    have hhh := hh.tsum_eq.symm
    simp_rw [opCoshTerm_integral μ hm] at hhh
    simpa only [opCoshTerm, ← Real.cosh_eq_tsum] using hhh
  apply Integrable.of_integral_ne_zero
  rw [he]
  apply ne_of_gt
  exact tsum_pos hs (fun n => by positivity) 0 (by norm_num)

theorem op_exp_abs_le_twice_cosh (c t : ℝ) :
    Real.exp (c * |t|) ≤ 2 * Real.cosh (c * t) := by
  rw [Real.cosh_eq]
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    linarith [Real.exp_pos (-(c * t))]
  · rw [abs_of_neg (lt_of_not_ge ht), mul_neg]
    linarith [Real.exp_pos (c * t)]

/-- All factorial moments force a genuine two-sided exponential envelope
on every smaller strip; no support assumption is supplied. -/
theorem operator_factorial_moments_exp_abs_integrable (μ : Measure ℝ)
    (hm : OpFactorialMoments μ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    Integrable (fun t : ℝ => Real.exp (c * |t|)) μ := by
  apply ((operator_factorial_moments_cosh_integrable μ hm hc0 hc1).const_mul 2).mono'
  · exact (Real.continuous_exp.comp
      (continuous_const.mul continuous_abs)).measurable.aestronglyMeasurable
  · exact Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact op_exp_abs_le_twice_cosh c t)

def opExpTerm (s : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (s * t) ^ n / (n.factorial : ℝ)

theorem opExpTerm_integrable (μ : Measure ℝ) (hm : OpFactorialMoments μ)
    (s : ℝ) (n : ℕ) : Integrable (opExpTerm s n) μ := by
  have hi := ((operator_factorial_moments_integrable μ hm n).const_mul
    (s ^ n)).div_const (n.factorial : ℝ)
  change Integrable (fun t => (s * t) ^ n / (n.factorial : ℝ)) μ
  simpa only [mul_pow] using hi

theorem opExpTerm_integral (μ : Measure ℝ) (hm : OpFactorialMoments μ)
    (s : ℝ) (n : ℕ) :
    (∫ t, opExpTerm s n t ∂μ) = ((n : ℝ) + 1) * s ^ n := by
  unfold opExpTerm
  simp_rw [mul_pow]
  rw [integral_div, integral_mul_left, hm n, Nat.factorial_succ, Nat.cast_mul]
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  push_cast
  field_simp
  <;> ring

theorem opExpTerm_hasSum (s t : ℝ) :
    HasSum (fun n => opExpTerm s n t) (Real.exp (s * t)) := by
  simpa only [opExpTerm, Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp ℝ (s * t))

theorem opExpTerm_norm_hasSum (s t : ℝ) :
    HasSum (fun n => ‖opExpTerm s n t‖) (Real.exp (|s| * |t|)) := by
  simpa only [opExpTerm, norm_div, norm_pow, Real.norm_eq_abs, abs_mul,
    show ∀ n : ℕ, |(n : ℝ)| = (n : ℝ) from fun n => abs_of_nonneg (Nat.cast_nonneg n)] using opExpTerm_hasSum |s| |t|

/-- Exact local MGF equality follows by a justified interchange of the
candidate's exponential series and its actual measure integral. -/
theorem operator_factorial_moments_local_mgf (μ : Measure ℝ)
    (hm : OpFactorialMoments μ) {s : ℝ} (hs : |s| < 1) :
    (∫ t : ℝ, Real.exp (s * t) ∂μ) = 1 / (1 - s) ^ (2 : ℕ) := by
  have hbound : Integrable (fun t => ∑' n, ‖opExpTerm s n t‖) μ := by
    simp_rw [(opExpTerm_norm_hasSum s _).tsum_eq]
    exact operator_factorial_moments_exp_abs_integrable μ hm (abs_nonneg s) hs
  have hh := hasSum_integral_of_dominated_convergence
    (fun n t => ‖opExpTerm s n t‖)
    (fun n => (opExpTerm_integrable μ hm s n).aestronglyMeasurable)
    (fun n => Eventually.of_forall (fun t => le_refl _))
    (Eventually.of_forall (fun t => (opExpTerm_norm_hasSum s t).summable))
    hbound (Eventually.of_forall (opExpTerm_hasSum s))
  have hg : HasSum (fun n : ℕ => ((n : ℝ) + 1) * s ^ n)
      (1 / (1 - s) ^ (2 : ℕ)) := by
    simpa using hasSum_choose_mul_geometric_of_norm_lt_one (r := s) 1 hs
  have hh' : HasSum (fun n : ℕ => ((n : ℝ) + 1) * s ^ n)
      (∫ t : ℝ, Real.exp (s * t) ∂μ) := by
    simpa only [opExpTerm_integral μ hm] using hh
  exact hh'.unique hg

end
end Sigma
