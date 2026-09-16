import SigmaProbRelativeEntropy
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal NNReal

theorem gaussian_integral (v : ℝ≥0) (hv : 0 < v) (f : ℝ → ℝ) :
    (∫ t, f t ∂gaussianReal 0 v) = ∫ t : ℝ, gaussianPDFReal 0 v t*f t := by
  rw [gaussianReal_of_var_ne_zero _ hv.ne']
  change (∫ t, f t ∂volume.withDensity
    (fun t => ((Real.toNNReal (gaussianPDFReal 0 v t) : ℝ≥0) : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul (measurable_gaussianPDFReal 0 v).real_toNNReal]
  apply integral_congr_ae
  filter_upwards with t
  rw [NNReal.smul_def,smul_eq_mul,Real.coe_toNNReal _ (gaussianPDFReal_nonneg _ _ _)]

theorem gaussian_kernel_second_moment (b : ℝ) (hb : 0 < b) :
    (∫ t : ℝ, t^2*Real.exp (-b*t^2)) =
      (1/(2*b))*(∫ t : ℝ, Real.exp (-b*t^2)) := by
  have h₀ : Integrable (fun t:ℝ => Real.exp (-b*t^2)) := integrable_exp_neg_mul_sq hb
  have h₁ : Integrable (fun t:ℝ => t*Real.exp (-b*t^2)) := integrable_mul_exp_neg_mul_sq hb
  have h₂ : Integrable (fun t:ℝ => t^2*Real.exp (-b*t^2)) := by
    simpa only [Real.rpow_two] using integrable_rpow_mul_exp_neg_mul_sq hb (show (-1:ℝ)<2 by norm_num)
  have hd (t:ℝ) : HasDerivAt (fun t:ℝ => t*Real.exp (-b*t^2))
      (Real.exp (-b*t^2)-(2*b)*(t^2*Real.exp (-b*t^2))) t := by
    convert (hasDerivAt_id t).mul ((((hasDerivAt_id t).pow 2).const_mul (-b)).exp) using 1 <;>
      simp only [id_eq] <;> ring
  have hi := integral_eq_zero_of_hasDerivAt_of_integrable hd (h₀.sub (h₂.const_mul (2*b))) h₁
  rw [integral_sub h₀ (h₂.const_mul (2*b)),integral_mul_left] at hi
  have hn : 2*b ≠ 0 := by positivity
  apply (mul_left_cancel₀ hn)
  rw [← mul_assoc,mul_one_div_cancel hn,one_mul]
  linarith


theorem gaussian_zero_second_moment (v : ℝ≥0) (hv : 0 < v) :
    (∫ t:ℝ, t^2 ∂gaussianReal 0 v) = (v:ℝ) := by
  let b : ℝ := 1/(2*(v:ℝ))
  let K : ℝ := (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹
  have hb : 0 < b := by dsimp [b]; positivity
  have he : gaussianPDFReal 0 v = (fun t:ℝ => K*Real.exp (-b*t^2)) := by
    funext t
    simp only [gaussianPDFReal,sub_zero,K,b]
    congr 2
    ring
  have hn : K*(∫ t:ℝ, Real.exp (-b*t^2)) = 1 := by
    rw [← integral_mul_left,← he]
    exact integral_gaussianPDFReal_eq_one 0 hv.ne'
  have hm := gaussian_kernel_second_moment b hb
  have hr : 1/(2*b) = (v:ℝ) := by
    dsimp [b]
    field_simp
  rw [gaussian_integral v hv,he]
  have hi : (∫ t:ℝ, (K*Real.exp (-b*t^2))*t^2) =
      K*(∫ t:ℝ, t^2*Real.exp (-b*t^2)) := by
    rw [← integral_mul_left]
    congr 1
    funext t
    ring
  rw [hi,hm,hr]
  calc K*((v:ℝ)*(∫ t:ℝ, Real.exp (-b*t^2))) =
      (v:ℝ)*(K*(∫ t:ℝ, Real.exp (-b*t^2))) := by ring
    _ = (v:ℝ) := by rw [hn,mul_one]

theorem gaussian_zero_square_integrable (v : ℝ≥0) (hv : 0 < v) :
    Integrable (fun t:ℝ => t^2) (gaussianReal 0 v) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussian_zero_second_moment v hv]
  exact (show (0:ℝ)<v from hv).ne'

theorem gaussian_zero_log_density (v : ℝ≥0) (hv : 0 < v) (t : ℝ) :
    Real.log (gaussianPDFReal 0 v t) =
      -(Real.log 2+Real.log Real.pi+Real.log (v:ℝ))/2-t^2/(2*(v:ℝ)) := by
  unfold gaussianPDFReal
  have hp : 0 < 2*Real.pi*(v:ℝ) := by positivity
  rw [sub_zero,Real.log_mul (inv_ne_zero (Real.sqrt_pos.mpr hp).ne') (Real.exp_ne_zero _),
    Real.log_inv,Real.log_sqrt hp.le,Real.log_exp,
    Real.log_mul (mul_pos (by norm_num) Real.pi_pos).ne' (show (0:ℝ)<v from hv).ne',
    Real.log_mul (by norm_num : (2:ℝ)≠0) Real.pi_ne_zero]
  ring

theorem gaussian_zero_log_likelihood (a b : ℝ≥0) (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    Real.log (gaussianPDFReal 0 a t/gaussianPDFReal 0 b t) =
      (1/2)*Real.log ((b:ℝ)/(a:ℝ))+(1/2)*((1/(b:ℝ))-(1/(a:ℝ)))*t^2 := by
  rw [Real.log_div (gaussianPDFReal_pos _ _ _ ha.ne').ne'
    (gaussianPDFReal_pos _ _ _ hb.ne').ne',
    gaussian_zero_log_density a ha,gaussian_zero_log_density b hb,
    Real.log_div (show (0:ℝ)<b from hb).ne' (show (0:ℝ)<a from ha).ne']
  ring

theorem gaussian_zero_log_rn_derivative (a b : ℝ≥0) (ha : 0 < a) (hb : 0 < b) :
    (fun t => Real.log (((gaussianReal 0 a).rnDeriv (gaussianReal 0 b) t).toReal)) =ᵐ[
      gaussianReal 0 a] (fun t => (1/2)*Real.log ((b:ℝ)/(a:ℝ))+
        (1/2)*((1/(b:ℝ))-(1/(a:ℝ)))*t^2) := by
  have hh := rn_derivative_positive_densities volume (gaussianPDFReal 0 a) (gaussianPDFReal 0 b)
    (measurable_gaussianPDFReal _ _) (measurable_gaussianPDFReal _ _)
    (ae_of_all _ (gaussianPDFReal_nonneg _ _))
    (ae_of_all _ (fun t => gaussianPDFReal_pos _ _ _ hb.ne'))
  have hma := gaussianReal_of_var_ne_zero 0 ha.ne'
  have hmb := gaussianReal_of_var_ne_zero 0 hb.ne'
  simp only [gaussianPDF_def] at hma hmb
  rw [← hma,← hmb] at hh
  filter_upwards [hh] with t ht
  rw [ht,gaussian_zero_log_likelihood a b ha hb]

theorem gaussian_relative_entropy_integrable (a b : ℝ≥0) (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun t => Real.log (((gaussianReal 0 a).rnDeriv (gaussianReal 0 b) t).toReal))
      (gaussianReal 0 a) := by
  apply ((integrable_const ((1/2)*Real.log ((b:ℝ)/(a:ℝ)))).add
    ((gaussian_zero_square_integrable a ha).const_mul ((1/2)*((1/(b:ℝ))-(1/(a:ℝ)))))).congr
  exact (gaussian_zero_log_rn_derivative a b ha hb).symm

theorem gaussian_relative_entropy (a b : ℝ≥0) (ha : 0 < a) (hb : 0 < b) :
    2*finiteRelativeEntropy (gaussianReal 0 a) (gaussianReal 0 b) =
      SigmaBase.potential ((a:ℝ)/(b:ℝ)) := by
  rw [finiteRelativeEntropy,integral_congr_ae (gaussian_zero_log_rn_derivative a b ha hb),
    integral_add (integrable_const _) ((gaussian_zero_square_integrable a ha).const_mul _),
    integral_const,integral_mul_left,gaussian_zero_second_moment a ha]
  simp only [measure_univ,ENNReal.one_toReal,one_smul]
  unfold SigmaBase.potential
  rw [Real.log_div (show (0:ℝ)<b from hb).ne' (show (0:ℝ)<a from ha).ne',
    Real.log_div (show (0:ℝ)<a from ha).ne' (show (0:ℝ)<b from hb).ne']
  field_simp
  ring

theorem gaussian_mutual_absolute_continuity (a b : ℝ≥0) (ha : 0 < a) (hb : 0 < b) :
    gaussianReal 0 a ≪ gaussianReal 0 b ∧ gaussianReal 0 b ≪ gaussianReal 0 a := by
  rw [gaussianReal_of_var_ne_zero 0 ha.ne',gaussianReal_of_var_ne_zero 0 hb.ne']
  simp only [gaussianPDF_def]
  constructor
  · exact positive_density_absolute_continuity _ _ _ (measurable_gaussianPDFReal _ _)
      (ae_of_all _ (fun _ => gaussianPDFReal_pos _ _ _ hb.ne'))
  · exact positive_density_absolute_continuity _ _ _ (measurable_gaussianPDFReal _ _)
      (ae_of_all _ (fun _ => gaussianPDFReal_pos _ _ _ ha.ne'))

end
end Sigma
