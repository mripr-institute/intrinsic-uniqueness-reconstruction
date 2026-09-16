import SigmaProbGammaTransforms

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

def gammaDeficitProbability : Measure ℝ :=
  Measure.map SigmaBase.potential gammaProbability

theorem intrinsic_potential_measurable : Measurable SigmaBase.potential := by
  exact (measurable_id.sub_const 1).sub Real.measurable_log

instance gamma_deficit_probability_is_probability : IsProbabilityMeasure gammaDeficitProbability :=
  MeasureTheory.isProbabilityMeasure_map intrinsic_potential_measurable.aemeasurable

theorem gamma_deficit_nonnegative : ∀ᵐ v ∂gammaDeficitProbability, 0 ≤ v := by
  rw [gammaDeficitProbability]
  apply (ae_map_iff intrinsic_potential_measurable.aemeasurable measurableSet_Ici).mpr
  filter_upwards [operator_integer_samples_ae_pos gammaProbability
    operator_gamma_probability_integer_samples] with t ht
  exact intrinsic_potential_two_branch.nonnegative ht

theorem gamma_deficit_mgf (s : ℝ) (hs : s < 1) :
    (∫ v : ℝ, Real.exp (s*v) ∂gammaDeficitProbability) =
      Real.exp (-s) * (1/(1-s)) ^ (2-s) * Real.Gamma (2-s) := by
  have hmeas : AEStronglyMeasurable (fun v : ℝ => Real.exp (s*v))
      (Measure.map SigmaBase.potential gammaProbability) :=
    ((continuous_const.mul continuous_id).rexp.aestronglyMeasurable)
  rw [gammaDeficitProbability, integral_map intrinsic_potential_measurable.aemeasurable
    hmeas,
    gamma_probability_integral]
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2-s) (r := 1-s)
    (by linarith) (by linarith)
  have he : (∫ t : ℝ in Ioi 0, SigmaPresentations.density t * Real.exp (s*SigmaBase.potential t)) =
      Real.exp (-s) * ∫ t : ℝ in Ioi 0, t ^ ((2-s)-1) * Real.exp (-((1-s)*t)) := by
    rw [← integral_mul_left]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    unfold SigmaPresentations.density SigmaBase.potential
    rw [Real.rpow_def_of_pos ht, ← Real.exp_log ht]
    simp only [Real.log_exp]
    simp_rw [← Real.exp_add]
    congr 1
    ring
  rw [he, hi]
  ring

theorem gamma_deficit_exponential_integrable (s : ℝ) (hs : s < 1) :
    Integrable (fun v : ℝ => Real.exp (s*v)) gammaDeficitProbability := by
  apply Integrable.of_integral_ne_zero
  rw [gamma_deficit_mgf s hs]
  have hg : 0 < Real.Gamma (2-s) := Real.Gamma_pos_of_pos (by linarith)
  exact mul_ne_zero (mul_ne_zero (Real.exp_ne_zero _) (Real.rpow_pos_of_pos
    (one_div_pos.mpr (sub_pos.mpr hs)) _).ne') hg.ne'

end
end Sigma
