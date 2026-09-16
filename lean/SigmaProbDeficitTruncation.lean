import SigmaProbDeficitCDF
import Mathlib.Probability.ConditionalProbability

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal

instance gammaProbability_noAtoms : NoAtoms gammaProbability := ⟨gamma_probability_no_atom⟩

def upperIncompleteGamma (q x : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi x, u^(q-1)*Real.exp (-u)

theorem gamma_probability_tail_integral (a : ℝ) (ha : 0 ≤ a) (f : ℝ → ℝ) :
    (∫ t : ℝ in Ioi a, f t ∂gammaProbability) =
      ∫ t : ℝ in Ioi a, SigmaPresentations.density t*f t := by
  rw [← integral_indicator measurableSet_Ioi,gamma_probability_integral]
  have he : (fun t => SigmaPresentations.density t*(Ioi a).indicator f t) =
      (Ioi a).indicator (fun t => SigmaPresentations.density t*f t) := by
    funext t
    by_cases ht : t∈Ioi a <;> simp [ht]
  rw [he,integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi ha)]

theorem scaled_upper_gamma_integral (q r a : ℝ) (hr : 0 < r) (ha : 0 ≤ a) :
    (∫ t : ℝ in Ioi a, t^(q-1)*Real.exp (-(r*t))) =
      (1/r)^q*upperIncompleteGamma q (r*a) := by
  have he : (∫ t : ℝ in Ioi a, (r*t)^(q-1)*Real.exp (-(r*t))) =
      r^(q-1)*(∫ t : ℝ in Ioi a, t^(q-1)*Real.exp (-(r*t))) := by
    rw [← integral_mul_left]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [Real.mul_rpow hr.le (ha.trans ht.le)]
    ring
  have hi := integral_comp_mul_left_Ioi (fun u:ℝ => u^(q-1)*Real.exp (-u)) a hr
  change (∫ t : ℝ in Ioi a, (r*t)^(q-1)*Real.exp (-(r*t))) =
    r⁻¹*upperIncompleteGamma q (r*a) at hi
  rw [he] at hi
  have hp : r^(q-1) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have hex : r^(q-1)*(1/r)^q = r⁻¹ := by
    rw [one_div,Real.inv_rpow hr.le,Real.rpow_sub hr,Real.rpow_one]
    field_simp [(Real.rpow_pos_of_pos hr q).ne',hr.ne']
    ring
  apply (mul_left_cancel₀ hp)
  rw [hi,← mul_assoc,hex]

theorem gamma_deficit_truncated_numerator (a s : ℝ) (ha : 0 < a) (hs : s < 1) :
    (∫ t : ℝ in Ici a, Real.exp (s*SigmaBase.potential t) ∂gammaProbability) =
      Real.exp (-s)*(1/(1-s))^(2-s)*upperIncompleteGamma (2-s) ((1-s)*a) := by
  rw [integral_Ici_eq_integral_Ioi,gamma_probability_tail_integral a ha.le]
  have he : (∫ t : ℝ in Ioi a, SigmaPresentations.density t*Real.exp (s*SigmaBase.potential t)) =
      Real.exp (-s)*(∫ t : ℝ in Ioi a, t^((2-s)-1)*Real.exp (-((1-s)*t))) := by
    rw [← integral_mul_left]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have htp : 0 < t := ha.trans ht
    dsimp only
    unfold SigmaPresentations.density SigmaBase.potential
    rw [Real.rpow_def_of_pos htp,← Real.exp_log htp]
    simp only [Real.log_exp]
    simp_rw [← Real.exp_add]
    congr 1
    ring
  rw [he,scaled_upper_gamma_integral _ _ _ (by linarith) ha.le]
  ring

theorem gamma_tail_condition_probability (a : ℝ) (ha : 0 < a) :
    IsProbabilityMeasure (ProbabilityTheory.cond gammaProbability (Ici a)) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure
  rw [← measure_congr (Ioi_ae_eq_Ici' (gamma_probability_no_atom a)),gamma_probability_tail a ha.le]
  exact (ENNReal.ofReal_pos.mpr (gamma_survival_positive ha.le)).ne'

theorem gamma_deficit_conditional_transform (a s : ℝ) (ha : 0 < a) (hs : s < 1) :
    (∫ t : ℝ, Real.exp (s*SigmaBase.potential t)
      ∂ProbabilityTheory.cond gammaProbability (Ici a)) =
      Real.exp (-s)*upperIncompleteGamma (2-s) ((1-s)*a) /
        (gammaSurvival a*(1-s)^(2-s)) := by
  rw [ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv,
    ← measure_congr (Ioi_ae_eq_Ici' (gamma_probability_no_atom a)),gamma_probability_tail a ha.le,
    ENNReal.toReal_ofReal (gamma_survival_positive ha.le).le,
    gamma_deficit_truncated_numerator a s ha hs,smul_eq_mul]
  rw [one_div,Real.inv_rpow (by linarith : 0 ≤ 1-s)]
  ring


theorem gamma_deficit_conditional_exponential_integrable (a s : ℝ)
    (ha : 0 < a) (hs : s < 1) :
    Integrable (fun t : ℝ => Real.exp (s*SigmaBase.potential t))
      (ProbabilityTheory.cond gammaProbability (Ici a)) := by
  have hm : Measurable (fun v : ℝ => Real.exp (s*v)) :=
    Real.measurable_exp.comp (measurable_const.mul measurable_id)
  have hi := gamma_deficit_exponential_integrable s hs
  rw [gammaDeficitProbability,integrable_map_measure hm.aestronglyMeasurable
    intrinsic_potential_measurable.aemeasurable] at hi
  apply hi.restrict.smul_measure
  apply ENNReal.inv_ne_top.mpr
  rw [← measure_congr (Ioi_ae_eq_Ici' (gamma_probability_no_atom a)),
    gamma_probability_tail a ha.le]
  exact (ENNReal.ofReal_pos.mpr (gamma_survival_positive ha.le)).ne'

end
end Sigma
