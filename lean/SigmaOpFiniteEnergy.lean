import SigmaOpFormDomainCriterion
import Mathlib.Analysis.Calculus.FDeriv.Measurable

namespace Sigma
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal ENNReal

theorem gamma_integrable_iff_positive_density (f : ℝ → ℝ) :
    Integrable f gammaProbability ↔
      IntegrableOn (fun t => SigmaPresentations.density t * f t) (Ioi 0) volume := by
  change Integrable f (volume.withDensity
    (fun t => ((Real.toNNReal (gammaPDFReal 2 1 t):ℝ≥0):ℝ≥0∞))) ↔ _
  rw [integrable_withDensity_iff_integrable_smul
    ((measurable_gammaPDFReal 2 1).real_toNNReal)]
  have he : (fun t => Real.toNNReal (gammaPDFReal 2 1 t) • f t) =
      (Ici (0:ℝ)).indicator (fun t => SigmaPresentations.density t * f t) := by
    funext t
    rw [NNReal.smul_def, smul_eq_mul,
      Real.coe_toNNReal _ (gammaPDFReal_nonneg (by norm_num) (by norm_num) t), gamma_pdf_intrinsic]
    by_cases ht : 0 ≤ t <;> simp [ht]
  rw [he, integrable_indicator_iff measurableSet_Ici]
  exact integrableOn_Ici_iff_integrableOn_Ioi

/-- The finite literal weighted derivative energy is exactly the L2 condition
on sqrt(t) F'(t). Measurability of the classical derivative is proved by Mathlib
for every function, so no regularity is silently added to this equivalence. -/
theorem weighted_derivative_mem_l2_iff_energy (F : ℝ → ℂ) :
    Memℒp (weightedTestDerivative F) 2 gammaProbability ↔
      IntegrableOn (fun t => steinFlux t * ‖deriv F t‖^2) (Ioi 0) volume := by
  have hm : AEStronglyMeasurable (weightedTestDerivative F) gammaProbability :=
    ((Complex.continuous_ofReal.comp Real.continuous_sqrt).measurable.mul
      (measurable_deriv F)).aestronglyMeasurable
  rw [memℒp_two_iff_integrable_sq_norm hm, gamma_integrable_iff_positive_density]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [weightedTestDerivative, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt (le_of_lt ht), steinFlux, SigmaPresentations.density]
  ring

def finiteEnergyGradient (F : ℝ → ℂ)
    (hF : IntegrableOn (fun t => steinFlux t * ‖deriv F t‖^2) (Ioi 0) volume) :
    LaguerreWeightedHilbert :=
  ((weighted_derivative_mem_l2_iff_energy F).mpr hF).toLp (weightedTestDerivative F)

theorem finite_energy_gradient_coe (F : ℝ → ℂ)
    (hF : IntegrableOn (fun t => steinFlux t * ‖deriv F t‖^2) (Ioi 0) volume) :
    (finiteEnergyGradient F hF : ℝ → ℂ) =ᵐ[gammaProbability] weightedTestDerivative F :=
  Memℒp.coeFn_toLp _

theorem finite_energy_gradient_norm_sq (F : ℝ → ℂ)
    (hF : IntegrableOn (fun t => steinFlux t * ‖deriv F t‖^2) (Ioi 0) volume) :
    ‖finiteEnergyGradient F hF‖^2 =
      ∫ t : ℝ in Ioi 0, steinFlux t * ‖deriv F t‖^2 := by
  rw [laguerre_l2_norm_sq_of_ae _ _ (finite_energy_gradient_coe F hF),
    gamma_probability_integral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [weightedTestDerivative, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt (le_of_lt ht), steinFlux, SigmaPresentations.density]
  ring

end
end Sigma
