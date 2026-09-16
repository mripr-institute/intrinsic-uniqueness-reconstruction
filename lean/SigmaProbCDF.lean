import SigmaProbGumbel
import Mathlib.Probability.CDF
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal

def gumbelStieltjes : StieltjesFunction where
  toFun := gumbelCDF
  mono' := gumbel_cdf_monotone
  right_continuous' x := gumbel_cdf_continuous.continuousAt.continuousWithinAt

def gumbelProbability : Measure ℝ := gumbelStieltjes.measure

instance gumbel_probability_is_probability : IsProbabilityMeasure gumbelProbability := by
  constructor
  rw [gumbelProbability, StieltjesFunction.measure_univ _
    gumbel_cdf_tendsto_atBot gumbel_cdf_tendsto_atTop]
  norm_num

theorem gumbel_probability_cdf : cdf gumbelProbability = gumbelStieltjes :=
  cdf_measure_stieltjesFunction gumbelStieltjes gumbel_cdf_tendsto_atBot
    gumbel_cdf_tendsto_atTop

theorem gumbel_probability_Iic (x : ℝ) :
    gumbelProbability (Iic x) = ENNReal.ofReal (gumbelCDF x) := by
  rw [← ofReal_cdf gumbelProbability, gumbel_probability_cdf]
  rfl

/-- The P3 max observations identify an actual arbitrary Borel probability. -/
theorem gumbel_two_max_probability_unique (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h2 : ∀ x, (cdf μ (x + Real.log 2)) ^ 2 = cdf μ x)
    (h3 : ∀ x, (cdf μ (x + Real.log 3)) ^ 3 = cdf μ x)
    (h0 : cdf μ 0 = Real.exp (-1)) : μ = gumbelProbability := by
  have he := gumbel_two_max_laws_unique (cdf μ) (monotone_cdf μ) h2 h3 h0
  have hc : cdf μ = gumbelStieltjes := by
    ext x
    exact congrFun he x
  rw [← measure_cdf μ, hc]
  rfl

theorem gumbel_density_continuous : Continuous gumbelDensity := by
  exact (continuous_id.neg.sub continuous_id.neg.rexp).rexp

theorem gumbel_density_interval_integral (a b : ℝ) :
    (∫ t : ℝ in a..b, gumbelDensity t) = gumbelCDF b - gumbelCDF a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => gumbel_cdf_derivative t) (gumbel_density_continuous.intervalIntegrable a b)

theorem gumbel_density_integrable : Integrable gumbelDensity := by
  apply integrable_of_intervalIntegral_norm_bounded (a := fun t : ℝ => -t)
    (b := fun t : ℝ => t) (l := atTop) 1
  · intro t
    exact (gumbel_density_continuous.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  · exact tendsto_neg_atTop_atBot
  · exact tendsto_id
  · apply Eventually.of_forall
    intro t
    have he : (fun x : ℝ => ‖gumbelDensity x‖) = gumbelDensity := by
      funext x
      exact Real.norm_of_nonneg (Real.exp_pos _).le
    rw [he, gumbel_density_interval_integral]
    have h0 := gumbel_cdf_positive (-t)
    have h1 := gumbel_cdf_lt_one t
    linarith

theorem gumbel_density_Iic_integral (x : ℝ) :
    (∫ t : ℝ in Iic x, gumbelDensity t) = gumbelCDF x := by
  simpa using integral_Iic_of_hasDerivAt_of_tendsto'
    (fun t _ => gumbel_cdf_derivative t) gumbel_density_integrable.integrableOn
    gumbel_cdf_tendsto_atBot

theorem gumbel_probability_density :
    gumbelProbability = volume.withDensity (fun t => ENNReal.ofReal (gumbelDensity t)) := by
  apply Measure.ext_of_Iic
  intro x
  rw [gumbel_probability_Iic, withDensity_apply _ measurableSet_Iic,
    ← ofReal_integral_eq_lintegral_ofReal gumbel_density_integrable.integrableOn
      (Eventually.of_forall fun t => (Real.exp_pos _).le), gumbel_density_Iic_integral]

end
end Sigma
