import SigmaProbMomentUnique

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

theorem gamma_density_integrability (f : ℝ → ℝ) :
    Integrable f gammaProbability ↔
      IntegrableOn (fun t => SigmaPresentations.density t*f t) (Ioi (0 : ℝ)) := by
  change Integrable f (volume.withDensity
    (fun t => ((Real.toNNReal (ProbabilityTheory.gammaPDFReal 2 1 t) : ℝ≥0) : ℝ≥0∞))) ↔ _
  rw [integrable_withDensity_iff_integrable_smul
    ((ProbabilityTheory.measurable_gammaPDFReal 2 1).real_toNNReal)]
  have hfun : (fun t => Real.toNNReal (ProbabilityTheory.gammaPDFReal 2 1 t) • f t) =
      (Ici (0 : ℝ)).indicator (fun t => SigmaPresentations.density t*f t) := by
    funext t
    rw [NNReal.smul_def, smul_eq_mul,
      Real.coe_toNNReal _ (ProbabilityTheory.gammaPDFReal_nonneg (by norm_num) (by norm_num) t),
      gamma_pdf_intrinsic]
    by_cases ht : 0 ≤ t
    · simp [ht]
    · simp [ht]
  rw [hfun, integrable_indicator_iff measurableSet_Ici]
  exact integrableOn_Ici_iff_integrableOn_Ioi

theorem gamma_deficit_mgf_not_integrable_at_one :
    ¬ Integrable (fun v : ℝ => Real.exp v) gammaDeficitProbability := by
  intro hi
  have hm : Measurable (fun v : ℝ => Real.exp v) := Real.measurable_exp
  rw [gammaDeficitProbability, integrable_map_measure hm.aestronglyMeasurable
    intrinsic_potential_measurable.aemeasurable] at hi
  have hd := (gamma_density_integrability _).mp hi
  have he : (fun t => SigmaPresentations.density t*Real.exp (SigmaBase.potential t)) =ᵐ[
      volume.restrict (Ioi (0 : ℝ))] (fun _ => Real.exp (-1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    unfold SigmaPresentations.density SigmaBase.potential
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_log ht, ← Real.exp_add]
    congr 1
    simp only [Real.log_exp]
    ring
  have hh : IntegrableOn (fun _ : ℝ => Real.exp (-1)) (Ioi (0 : ℝ)) := hd.congr he
  simp only [integrableOn_const, Real.exp_ne_zero, Real.volume_Ioi, lt_self_iff_false,
    or_self] at hh

theorem gamma_deficit_mgf_not_integrable (s : ℝ) (hs : 1 ≤ s) :
    ¬ Integrable (fun v : ℝ => Real.exp (s*v)) gammaDeficitProbability := by
  intro hi
  apply gamma_deficit_mgf_not_integrable_at_one
  apply hi.mono' Real.continuous_exp.aestronglyMeasurable
  filter_upwards [gamma_deficit_nonnegative] with v hv
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (by nlinarith)

theorem gamma_deficit_mgf_integrable_iff (s : ℝ) :
    Integrable (fun v : ℝ => Real.exp (s*v)) gammaDeficitProbability ↔ s < 1 := by
  constructor
  · intro hi
    by_contra hs
    exact gamma_deficit_mgf_not_integrable s (le_of_not_gt hs) hi
  · exact gamma_deficit_exponential_integrable s

end
end Sigma
