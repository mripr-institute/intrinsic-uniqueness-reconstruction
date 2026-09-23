import SigmaProbCantorMeasure
import SigmaProbSingularCDF
import SigmaProbSingularSurvival

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

/-- A concrete singular function: the shifted CDF of the constructed atomless
probability on the actual null Cantor set. No singular-function existence or
almost-everywhere derivative property is a hypothesis. -/
theorem continuous_singular_function_exists :
    ∃ C : ℝ → ℝ, Continuous C ∧ Monotone C ∧
      (∀ x ≤ 1, C x = 0) ∧ (∀ x ≥ 2, C x = 1) ∧
      (∀ᵐ x ∂volume, HasDerivAt C 0 x) := by
  refine ⟨singularShiftedCDF cantorSingularProbability,
    singular_shifted_cdf_continuous _, singular_shifted_cdf_monotone _, ?_, ?_,
    singular_shifted_cdf_derivative_zero_ae _ cantor_singular_probability_supported⟩
  · intro x hx
    exact singular_shifted_cdf_zero _ cantor_singular_probability_supported hx
  · intro x hx
    exact singular_shifted_cdf_one _ cantor_singular_probability_supported hx

/-- Removing local absolute continuity from the a.e. hazard formulation admits
a genuinely different atomless probability, even with the exact survival anchor,
strict decrease, positive finite survival, and the correct limit at infinity. -/
theorem gamma_hazard_regularity_counterexample :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ NoAtoms μ ∧
      (∀ᵐ t ∂μ, 0 < t) ∧ Continuous (lifetimeSurvival μ) ∧
      Antitone (lifetimeSurvival μ) ∧ StrictAntiOn (lifetimeSurvival μ) (Ici 0) ∧
      (∀ x : ℝ, 0 < lifetimeSurvival μ x) ∧ lifetimeSurvival μ 0 = 1 ∧
      Tendsto (lifetimeSurvival μ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
        HasDerivAt (lifetimeSurvival μ) (-gammaHazard x*lifetimeSurvival μ x) x) ∧
      (∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
        HasDerivAt (fun t => Real.log (lifetimeSurvival μ t)) (-gammaHazard x) x) ∧
      μ ≠ gammaProbability ∧
      ¬ LocallyIntegralAbsolutelyContinuousPositive (lifetimeSurvival μ) := by
  obtain ⟨C, hc, hm, hl, hr, hd⟩ := continuous_singular_function_exists
  exact singular_survival_native_counterexample C hc hm hl hr hd

end
end Sigma
