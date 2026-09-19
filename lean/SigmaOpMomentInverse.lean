import SigmaOpMomentTilt
import SigmaOpLaguerre

namespace Sigma
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

/-- An actual finite positive measure obtained by exponential tilting and dilation. -/
def opTiltScaleMeasure (μ : Measure ℝ) (a : ℝ) : Measure ℝ :=
  Measure.map (fun t => (1 + a) * t)
    (μ.withDensity (fun t =>
      ((Real.toNNReal ((1 + a) ^ 2 * Real.exp (-(a * t))) : ℝ≥0) : ℝ≥0∞)))

theorem opTiltScale_integral (μ : Measure ℝ) (a : ℝ) (f : ℝ → ℝ)
    (hf : Measurable f) :
    (∫ y, f y ∂opTiltScaleMeasure μ a) =
      ∫ t, (1 + a) ^ 2 * Real.exp (-(a * t)) * f ((1 + a) * t) ∂μ := by
  rw [opTiltScaleMeasure, integral_map
    (φ := fun t : ℝ => (1 + a) * t) (by fun_prop) hf.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_smul
    (f := fun t : ℝ => Real.toNNReal ((1 + a) ^ 2 * Real.exp (-(a * t))))
    (by fun_prop)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    dsimp only
    rw [NNReal.smul_def, smul_eq_mul,
      Real.coe_toNNReal _ (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)])

def OpTiltMoments (μ : Measure ℝ) (a : ℝ) : Prop :=
  ∀ m : ℕ, (∫ t : ℝ, t ^ m * Real.exp (-(a * t)) ∂μ) =
    ((m + 1).factorial : ℝ) / (1 + a) ^ (m + 2)

theorem operator_tilt_scale_factorial_moments (μ : Measure ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hm : OpTiltMoments μ a) :
    OpFactorialMoments (opTiltScaleMeasure μ a) := by
  intro m
  rw [opTiltScale_integral μ a (fun t : ℝ => t ^ m) (by fun_prop)]
  have he : (fun t : ℝ => (1 + a) ^ 2 * Real.exp (-(a * t)) * ((1 + a) * t) ^ m) =
      fun t => (1 + a) ^ (m + 2) * (t ^ m * Real.exp (-(a * t))) := by
    funext t
    simp only [mul_pow, pow_add]
    ring
  rw [he, integral_mul_left, hm m]
  have hr : (1 + a) ^ (m + 2) ≠ 0 := pow_ne_zero _ (by linarith)
  exact mul_div_cancel₀ _ hr

theorem opTiltScale_weighted_exp_integral (μ : Measure ℝ) (a s : ℝ) (m : ℕ) :
    (∫ y, y ^ m * Real.exp (s * y) ∂opTiltScaleMeasure μ a) =
      (1 + a) ^ (m + 2) *
        ∫ t, t ^ m * Real.exp (-((a - s * (1 + a)) * t)) ∂μ := by
  rw [opTiltScale_integral μ a (fun y : ℝ => y ^ m * Real.exp (s * y)) (by fun_prop)]
  rw [← integral_mul_left]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    simp only [mul_pow, pow_add]
    have he : -((a - s * (1 + a)) * t) = -(a * t) + s * ((1 + a) * t) := by ring
    rw [he, Real.exp_add]
    ring)

/-- One half-unit extension of the whole tilted moment sequence. -/
theorem operator_tilt_moments_extend (μ : Measure ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hm : OpTiltMoments μ a) : OpTiltMoments μ (a + 1 / 2) := by
  intro m
  let r : ℝ := 1 + a
  let s : ℝ := -(1 / 2) / r
  have hr : 0 < r := by dsimp [r]; linarith
  have hs : |s| < 1 := by
    dsimp [s]
    rw [abs_div, abs_neg, abs_of_pos hr,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    apply (div_lt_one hr).mpr
    dsimp [r]
    norm_num
    linarith
  have hh := operator_factorial_moments_weighted_local_mgf (opTiltScaleMeasure μ a)
    (operator_tilt_scale_factorial_moments μ ha hm) m hs
  rw [opTiltScale_weighted_exp_integral] at hh
  have haeq : a - s * (1 + a) = a + 1 / 2 := by
    dsimp [s, r]
    field_simp
    ring
  rw [haeq] at hh
  have hd : (1 - s) * (1 + a) = 1 + (a + 1 / 2) := by
    dsimp [s, r]
    field_simp
    ring
  have hrn : (1 + a) ^ (m + 2) ≠ 0 := pow_ne_zero _ (by linarith)
  apply (mul_left_cancel₀ hrn)
  rw [hh]
  have hds : 1 - s ≠ 0 := by
    have h := (abs_lt.mp hs).2
    linarith
  rw [← hd, mul_pow]
  field_simp
  ring

/-- All integer Laplace samples are derived from full-line factorial moments
by iterating actual exponential tilts; no support conclusion is assumed. -/
theorem operator_factorial_moments_integer_samples (μ : Measure ℝ)
    (hm : OpFactorialMoments μ) : OpGammaIntegerSamples μ := by
  have htilt : ∀ k : ℕ, OpTiltMoments μ ((k : ℝ) / 2) := by
    intro k
    induction k with
    | zero =>
      intro m
      simpa using hm m
    | succ k ih =>
      have hh := operator_tilt_moments_extend μ (by positivity : 0 ≤ (k : ℝ) / 2) ih
      convert hh using 1 ; push_cast ; ring
  intro n
  have hh := htilt (2 * n) 0
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
    pow_zero, one_mul, Nat.zero_add, Nat.factorial_one, Nat.cast_one, one_div, inv_pow, neg_mul] using hh

/-- Full real-line factorial-moment determinacy for the actual Gamma law. -/
theorem operator_full_line_factorial_moment_unique (μ : Measure ℝ)
    (hm : OpFactorialMoments μ) : μ = gammaProbability := by
  letI := operator_factorial_moments_isProbability μ hm
  exact operator_full_line_mixing_characterization μ
    (operator_factorial_moments_integer_samples μ hm)

/-- The complete marked Laguerre orthogonality inverse on all of the real line. -/
theorem operator_laguerre_orthogonality_unique (μ : Measure ℝ)
    [IsProbabilityMeasure μ]
    (hi : ∀ n : ℕ, Integrable (fun t : ℝ => t ^ n) μ)
    (hL : ∀ n : ℕ, n ≠ 0 → (∫ t, opLaguerre n t ∂μ) = 0) :
    μ = gammaProbability :=
  operator_full_line_factorial_moment_unique μ
    (operator_laguerre_orthogonality_recovers_moments μ hi hL)

theorem operator_laguerre_orthogonality_iff_gamma (μ : Measure ℝ)
    [IsProbabilityMeasure μ]
    (hi : ∀ n : ℕ, Integrable (fun t : ℝ => t ^ n) μ) :
    (∀ n : ℕ, n ≠ 0 → (∫ t, opLaguerre n t ∂μ) = 0) ↔ μ = gammaProbability := by
  constructor
  · exact operator_laguerre_orthogonality_unique μ hi
  · rintro rfl
    exact operator_gamma_laguerre_orthogonality

/-- The exact polynomial-integrability formulation of final:O7. -/
theorem operator_marked_laguerre_characterization (μ : Measure ℝ)
    [IsProbabilityMeasure μ]
    (hi : ∀ P : Polynomial ℝ, Integrable (fun t : ℝ => P.eval t) μ) :
    (∀ n : ℕ, n ≠ 0 → (∫ t, opLaguerre n t ∂μ) = 0) ↔ μ = gammaProbability := by
  apply operator_laguerre_orthogonality_iff_gamma μ
  intro n
  simpa using hi (Polynomial.X ^ n)

theorem operator_marked_laguerre_positive_support (μ : Measure ℝ)
    [IsProbabilityMeasure μ]
    (hi : ∀ n : ℕ, Integrable (fun t : ℝ => t ^ n) μ)
    (hL : ∀ n : ℕ, n ≠ 0 → (∫ t, opLaguerre n t ∂μ) = 0) :
    μ (Set.Iic 0) = 0 :=
  operator_integer_samples_positive_support μ
    (operator_factorial_moments_integer_samples μ
      (operator_laguerre_orthogonality_recovers_moments μ hi hL))

end
end Sigma
