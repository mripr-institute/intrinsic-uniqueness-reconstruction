import SigmaProbCDF
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal

/-- The unanchored family in P3-haar, in its translation coordinate. -/
def shiftedGumbelCDF (b x : ℝ) : ℝ := gumbelCDF (x - b)

theorem shifted_gumbel_max (b x : ℝ) (n : ℕ) (hn : 0 < n) :
    shiftedGumbelCDF b (x + Real.log n) ^ n = shiftedGumbelCDF b x := by
  simpa only [shiftedGumbelCDF, add_sub_right_comm] using gumbel_max_law n hn (x-b)

theorem shifted_gumbel_scale (c x : ℝ) (hc : 0 < c) :
    shiftedGumbelCDF (Real.log c) x = Real.exp (-c * Real.exp (-x)) := by
  unfold shiftedGumbelCDF gumbelCDF
  rw [neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log hc]
  congr 1
  ring

def shiftedGumbelStieltjes (b : ℝ) : StieltjesFunction where
  toFun := shiftedGumbelCDF b
  mono' := fun _ _ h => gumbel_cdf_monotone (sub_le_sub_right h b)
  right_continuous' _ :=
    (gumbel_cdf_continuous.comp (continuous_id.sub continuous_const)).continuousAt.continuousWithinAt

theorem shifted_gumbel_limits (b : ℝ) :
    Tendsto (shiftedGumbelCDF b) atBot (𝓝 0) ∧
    Tendsto (shiftedGumbelCDF b) atTop (𝓝 1) := by
  simpa only [shiftedGumbelCDF, sub_eq_add_neg] using
    And.intro (gumbel_cdf_tendsto_atBot.comp (tendsto_atBot_add_const_right atBot (-b) tendsto_id))
      (gumbel_cdf_tendsto_atTop.comp (tendsto_atTop_add_const_right atTop (-b) tendsto_id))

instance shifted_gumbel_probability (b : ℝ) :
    IsProbabilityMeasure (shiftedGumbelStieltjes b).measure := by
  constructor
  rw [StieltjesFunction.measure_univ _ (shifted_gumbel_limits b).1
    (shifted_gumbel_limits b).2]
  norm_num

theorem shifted_gumbel_cdf (b : ℝ) :
    cdf (shiftedGumbelStieltjes b).measure = shiftedGumbelStieltjes b :=
  cdf_measure_stieltjesFunction _ (shifted_gumbel_limits b).1 (shifted_gumbel_limits b).2

theorem shifted_gumbel_distinct (b : ℝ) (hb : b ≠ 0) :
    (shiftedGumbelStieltjes b).measure ≠ gumbelProbability := by
  intro he
  have hc := congrArg (fun μ : Measure ℝ => cdf μ 0) he
  dsimp only at hc
  rw [shifted_gumbel_cdf, gumbel_probability_cdf] at hc
  change Real.exp (-Real.exp (-(0-b))) = Real.exp (-Real.exp (-0)) at hc
  have h := Real.exp_injective (neg_injective (Real.exp_injective hc))
  exact hb (by linarith)

/-- An explicit small nonzero amplitude; no smallness assumption is deferred. -/
def gumbelFrequency : ℝ := 2 * Real.pi / Real.log 2
def gumbelAmplitude : ℝ := 1 / (4 * (1 + gumbelFrequency))
def gumbelPeriodicFactor (x : ℝ) : ℝ :=
  1 + gumbelAmplitude * Real.sin (gumbelFrequency * x)
def gumbelPeriodicSlope (x : ℝ) : ℝ :=
  gumbelAmplitude * gumbelFrequency * Real.cos (gumbelFrequency * x)
def periodicGumbelCDF (x : ℝ) : ℝ :=
  Real.exp (-Real.exp (-x) * gumbelPeriodicFactor x)

theorem gumbel_frequency_pos : 0 < gumbelFrequency := by
  exact div_pos (mul_pos (by norm_num) Real.pi_pos) (Real.log_pos (by norm_num))

theorem gumbel_amplitude_bounds :
    0 < gumbelAmplitude ∧ gumbelAmplitude ≤ 1/4 ∧
      gumbelAmplitude * gumbelFrequency ≤ 1/4 := by
  have hw := gumbel_frequency_pos
  have hd : 0 < 4 * (1 + gumbelFrequency) := by positivity
  have he : gumbelAmplitude * (4 * (1 + gumbelFrequency)) = 1 := by
    unfold gumbelAmplitude
    exact div_mul_cancel₀ _ hd.ne'
  have hp : 0 < gumbelAmplitude := by unfold gumbelAmplitude; positivity
  exact ⟨hp, by nlinarith [mul_pos hp hw], by nlinarith⟩

theorem gumbel_periodic_bounds (x : ℝ) :
    3/4 ≤ gumbelPeriodicFactor x ∧ gumbelPeriodicFactor x ≤ 5/4 ∧
      gumbelPeriodicSlope x ≤ 1/4 := by
  obtain ⟨he, he1, hew⟩ := gumbel_amplitude_bounds
  have hsin := Real.neg_one_le_sin (gumbelFrequency*x)
  have hsin' := Real.sin_le_one (gumbelFrequency*x)
  have hcos := Real.cos_le_one (gumbelFrequency*x)
  unfold gumbelPeriodicFactor gumbelPeriodicSlope
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hsin he.le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hsin' he.le]
  · exact (mul_le_mul_of_nonneg_left hcos (mul_pos he gumbel_frequency_pos).le).trans
      (by simpa using hew)

theorem gumbel_periodic_derivative (x : ℝ) :
    HasDerivAt gumbelPeriodicFactor (gumbelPeriodicSlope x) x := by
  convert (((hasDerivAt_id x).const_mul gumbelFrequency).sin.const_mul
    gumbelAmplitude).const_add 1 using 1
  simp only [gumbelPeriodicFactor, gumbelPeriodicSlope, mul_one, id_eq]
  ring

theorem periodic_gumbel_derivative (x : ℝ) :
    HasDerivAt periodicGumbelCDF
      (periodicGumbelCDF x * Real.exp (-x) *
        (gumbelPeriodicFactor x - gumbelPeriodicSlope x)) x := by
  convert ((((hasDerivAt_id x).neg.exp).neg.mul
    (gumbel_periodic_derivative x)).exp) using 1
  simp only [periodicGumbelCDF, neg_mul, mul_neg, mul_one, id_eq]
  ring

theorem periodic_gumbel_strictMono : StrictMono periodicGumbelCDF := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(periodic_gumbel_derivative x).deriv]
  have hb := gumbel_periodic_bounds x
  exact mul_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)) (by linarith)

theorem periodic_gumbel_continuous : Continuous periodicGumbelCDF :=
  continuous_iff_continuousAt.mpr fun x => (periodic_gumbel_derivative x).continuousAt

theorem periodic_gumbel_anchor : periodicGumbelCDF 0 = Real.exp (-1) := by
  simp [periodicGumbelCDF, gumbelPeriodicFactor]

theorem gumbel_periodic_period (x : ℝ) :
    gumbelPeriodicFactor (x + Real.log 2) = gumbelPeriodicFactor x := by
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hw : gumbelFrequency * Real.log 2 = 2 * Real.pi := by
    exact div_mul_cancel₀ _ hl
  simp only [gumbelPeriodicFactor, mul_add, hw, Real.sin_add_two_pi]

theorem periodic_gumbel_max_two (x : ℝ) :
    periodicGumbelCDF (x + Real.log 2) ^ 2 = periodicGumbelCDF x := by
  rw [periodicGumbelCDF, ← Real.exp_nat_mul, periodicGumbelCDF, gumbel_periodic_period]
  congr 1
  simp only [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<2)]
  norm_num
  ring

theorem periodic_gumbel_distinct_function : periodicGumbelCDF ≠ gumbelCDF := by
  intro he
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hw : gumbelFrequency * (Real.log 2 / 4) = Real.pi / 2 := by
    unfold gumbelFrequency
    field_simp
    ring
  have hv := congrFun he (Real.log 2 / 4)
  simp only [periodicGumbelCDF, gumbelCDF, gumbelPeriodicFactor, hw,
    Real.sin_pi_div_two, mul_one] at hv
  have hv' := Real.exp_injective hv
  have hp := gumbel_amplitude_bounds.1
  nlinarith [Real.exp_pos (-(Real.log 2 / 4))]

theorem periodic_gumbel_limits :
    Tendsto periodicGumbelCDF atBot (𝓝 0) ∧
    Tendsto periodicGumbelCDF atTop (𝓝 1) := by
  have hbot : Tendsto (fun x : ℝ => Real.exp (-x)) atBot atTop :=
    Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop
  have htop : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hb : Tendsto (fun x => Real.exp (-x) * gumbelPeriodicFactor x) atBot atTop := by
    apply tendsto_atTop_mono _ (hbot.const_mul_atTop (by norm_num : (0:ℝ)<3/4))
    intro x
    nlinarith [mul_le_mul_of_nonneg_left (gumbel_periodic_bounds x).1 (Real.exp_pos (-x)).le]
  have ht : Tendsto (fun x => Real.exp (-x) * gumbelPeriodicFactor x) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun x => mul_nonneg (Real.exp_pos _).le (by have h := (gumbel_periodic_bounds x).1; linarith))
      (fun x => mul_le_mul_of_nonneg_left (gumbel_periodic_bounds x).2.1 (Real.exp_pos _).le)
    simpa using htop.mul_const (5/4:ℝ)
  constructor
  · change Tendsto (fun x => Real.exp (-Real.exp (-x) * gumbelPeriodicFactor x)) atBot (𝓝 0)
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hb)
  · change Tendsto (fun x => Real.exp (-Real.exp (-x) * gumbelPeriodicFactor x)) atTop (𝓝 1)
    simpa only [Function.comp_def, neg_mul, neg_zero, Real.exp_zero] using
      (Real.continuous_exp.tendsto (-0)).comp ht.neg

def periodicGumbelStieltjes : StieltjesFunction where
  toFun := periodicGumbelCDF
  mono' := periodic_gumbel_strictMono.monotone
  right_continuous' _ := periodic_gumbel_continuous.continuousAt.continuousWithinAt

instance periodic_gumbel_probability : IsProbabilityMeasure periodicGumbelStieltjes.measure := by
  constructor
  rw [StieltjesFunction.measure_univ _ periodic_gumbel_limits.1 periodic_gumbel_limits.2]
  norm_num

theorem periodic_gumbel_cdf : cdf periodicGumbelStieltjes.measure = periodicGumbelStieltjes :=
  cdf_measure_stieltjesFunction _ periodic_gumbel_limits.1 periodic_gumbel_limits.2

/-- Both max observations without the anchor fail to identify a probability. -/
theorem gumbel_without_anchor_counterexample :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ ≠ gumbelProbability ∧
      (∀ x, cdf μ (x + Real.log 2)^2 = cdf μ x) ∧
      (∀ x, cdf μ (x + Real.log 3)^3 = cdf μ x) := by
  refine ⟨(shiftedGumbelStieltjes 1).measure, inferInstance,
    shifted_gumbel_distinct 1 (by norm_num), ?_, ?_⟩
  · intro x
    rw [shifted_gumbel_cdf]
    exact shifted_gumbel_max 1 x 2 (by norm_num)
  · intro x
    rw [shifted_gumbel_cdf]
    exact shifted_gumbel_max 1 x 3 (by norm_num)

/-- The anchor and base-two observation still fail to identify a probability. -/
theorem gumbel_base_two_counterexample :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ ≠ gumbelProbability ∧
      cdf μ 0 = Real.exp (-1) ∧
      (∀ x, cdf μ (x + Real.log 2)^2 = cdf μ x) := by
  refine ⟨periodicGumbelStieltjes.measure, inferInstance, ?_, ?_, ?_⟩
  · intro he
    apply periodic_gumbel_distinct_function
    have hc := congrArg cdf he
    rw [periodic_gumbel_cdf, gumbel_probability_cdf] at hc
    exact congrArg (fun F : StieltjesFunction => (F : ℝ → ℝ)) hc
  · rw [periodic_gumbel_cdf]
    exact periodic_gumbel_anchor
  · intro x
    rw [periodic_gumbel_cdf]
    exact periodic_gumbel_max_two x

end
end Sigma
