import SigmaProbCharacteristic
import Mathlib.Probability.Distributions.Gamma

namespace Sigma
noncomputable section
open Filter MeasureTheory Set ProbabilityTheory
open scoped Topology ENNReal NNReal

def gammaProbability : Measure ℝ := gammaMeasure 2 1

theorem gamma_pdf_intrinsic (t : ℝ) :
    gammaPDFReal 2 1 t = if 0 ≤ t then SigmaPresentations.density t else 0 := by
  have hg : Real.Gamma 2 = 1 := by
    simp
  norm_num [gammaPDFReal, hg, SigmaPresentations.density]

instance gamma_probability_is_probability : IsProbabilityMeasure gammaProbability :=
  isProbabilityMeasureGamma (by norm_num) (by norm_num)

theorem gamma_probability_normalized : gammaProbability Set.univ = 1 := by
  exact measure_univ

theorem gamma_probability_no_atom (x : ℝ) : gammaProbability {x} = 0 := by
  apply withDensity_absolutelyContinuous volume (gammaPDF 2 1)
  exact measure_singleton x

theorem gamma_probability_negative_ray : gammaProbability (Iio 0) = 0 := by
  rw [gammaProbability, gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos (by norm_num)

theorem intrinsic_gamma_integral (n : ℕ) :
    (∫ t : ℝ in Ioi 0, t ^ n * SigmaPresentations.density t) = (n + 1).factorial := by
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (n : ℝ) + 2) (r := 1) (by positivity) (by norm_num)
  have hg : Real.Gamma ((n : ℝ) + 2) = ((n + 1).factorial : ℝ) := by
    convert Real.Gamma_nat_eq_factorial (n + 1) using 1 ; push_cast ; ring
  rw [one_div_one, Real.one_rpow, one_mul, hg] at hi
  convert hi using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have he : (n : ℝ) + 2 - 1 = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [he, Real.rpow_natCast]
  simp [SigmaPresentations.density, pow_succ, mul_assoc]

theorem intrinsic_density_integral_one :
    (∫ t : ℝ in Ioi 0, SigmaPresentations.density t) = 1 := by
  simpa using intrinsic_gamma_integral 0

theorem intrinsic_density_laplace {s : ℝ} (hs : -1 < s) :
    (∫ t : ℝ in Ioi 0, Real.exp (-(s * t)) * SigmaPresentations.density t) =
      (1 + s)⁻¹ ^ 2 := by
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := 2) (r := 1 + s) (by norm_num) (by linarith)
  have hg : Real.Gamma 2 = 1 := by
    simp
  norm_num [hg, Real.rpow_two] at hi
  rw [inv_pow, ← hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [SigmaPresentations.density]
  rw [← mul_assoc, mul_comm (Real.exp _) t, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem gamma_probability_integral (f : ℝ → ℝ) :
    (∫ t, f t ∂gammaProbability) =
      ∫ t : ℝ in Ioi 0, SigmaPresentations.density t * f t := by
  change (∫ t, f t ∂volume.withDensity
    (fun t => ((Real.toNNReal (gammaPDFReal 2 1 t) : ℝ≥0) : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul
    ((measurable_gammaPDFReal 2 1).real_toNNReal)]
  have hfun : (fun t => Real.toNNReal (gammaPDFReal 2 1 t) • f t) =
      (Ici (0 : ℝ)).indicator (fun t => SigmaPresentations.density t * f t) := by
    funext t
    rw [NNReal.smul_def, smul_eq_mul,
      Real.coe_toNNReal _ (gammaPDFReal_nonneg (by norm_num) (by norm_num) t),
      gamma_pdf_intrinsic]
    by_cases ht : 0 ≤ t
    · simp [ht]
    · simp [ht]
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

theorem gamma_probability_moments (n : ℕ) :
    (∫ t : ℝ, t ^ n ∂gammaProbability) = ((n + 1).factorial : ℝ) := by
  rw [gamma_probability_integral]
  simpa only [mul_comm] using intrinsic_gamma_integral n

theorem gamma_probability_monomial_integrable (n : ℕ) :
    Integrable (fun t : ℝ => t ^ n) gammaProbability := by
  by_contra h
  have he := gamma_probability_moments n
  rw [integral_undef h] at he
  have hp : (0 : ℝ) < (n + 1).factorial := by positivity
  linarith

theorem intrinsic_density_integrable : IntegrableOn SigmaPresentations.density (Ioi (0 : ℝ)) := by
  by_contra h
  have he := intrinsic_density_integral_one
  rw [integral_undef h] at he
  norm_num at he

theorem gamma_probability_laplace {s : ℝ} (hs : -1 < s) :
    (∫ t : ℝ, Real.exp (-(s * t)) ∂gammaProbability) = (1 + s)⁻¹ ^ 2 := by
  rw [gamma_probability_integral]
  simpa only [mul_comm] using intrinsic_density_laplace hs

end
end Sigma
