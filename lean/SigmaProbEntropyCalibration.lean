import SigmaProbEuler
import SigmaProbEntropyIntegral

namespace Sigma
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

theorem gamma_density_calibrated :
    CalibratedGammaDensity SigmaPresentations.density (1-Real.eulerMascheroniConstant) := by
  constructor
  · exact (continuous_id.mul continuous_id.neg.rexp).measurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (SigmaPresentations.density_pos ht).le
  · exact intrinsic_density_integral_one
  · simpa only [pow_one] using intrinsic_gamma_integral 1
  · exact (gamma_density_integrability Real.log).mp gamma_probability_log_integrable
  · rw [← gamma_probability_integral, gamma_probability_expected_log]

theorem gamma_extended_entropy_value :
    calibratedExtendedEntropy (1+Real.eulerMascheroniConstant) SigmaPresentations.density =
      ((1+Real.eulerMascheroniConstant : ℝ) : EReal) := by
  apply (calibrated_extended_entropy_equality_iff _ _
    gamma_density_calibrated.measurable gamma_density_calibrated.nonnegative).mpr
  exact EventuallyEq.rfl

theorem calibrated_gamma_maximum_entropy (f : ℝ → ℝ)
    (h : CalibratedGammaDensity f (1-Real.eulerMascheroniConstant)) :
    calibratedExtendedEntropy (1+Real.eulerMascheroniConstant) f ≤
      ((1+Real.eulerMascheroniConstant : ℝ) : EReal) ∧
    (calibratedExtendedEntropy (1+Real.eulerMascheroniConstant) f =
      ((1+Real.eulerMascheroniConstant : ℝ) : EReal) ↔
      f =ᵐ[volume.restrict (Ioi 0)] SigmaPresentations.density) :=
  ⟨calibrated_extended_entropy_bound _ _,
    calibrated_extended_entropy_equality_iff _ _ h.measurable h.nonnegative⟩

theorem calibrated_gamma_finite_entropy (f : ℝ → ℝ)
    (h : CalibratedGammaDensity f (1-Real.eulerMascheroniConstant))
    (hi : IntegrableOn (fun t : ℝ => f t*Real.log (f t)) (Ioi 0)) :
    calibratedExtendedEntropy (1+Real.eulerMascheroniConstant) f =
      ((-(∫ t : ℝ in Ioi 0, f t*Real.log (f t)) : ℝ) : EReal) := by
  have he : 2-(1-Real.eulerMascheroniConstant) = 1+Real.eulerMascheroniConstant := by ring
  simpa only [he] using h.finite_entropy_formula hi

theorem gamma_density_entropy_integrable :
    IntegrableOn (fun t : ℝ => SigmaPresentations.density t*Real.log (SigmaPresentations.density t)) (Ioi 0) :=
  gamma_density_calibrated.cross_integrable

theorem gamma_density_entropy_integral :
    -(∫ t : ℝ in Ioi 0, SigmaPresentations.density t*Real.log (SigmaPresentations.density t)) =
      1+Real.eulerMascheroniConstant := by
  rw [gamma_density_calibrated.cross_entropy]
  ring

end
end Sigma
