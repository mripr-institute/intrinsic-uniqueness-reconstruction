import SigmaProbRelativeEntropy

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal NNReal

def rateExpProbability (r : ℝ) : Measure ℝ := gammaMeasure 1 r

theorem rate_exp_is_probability (r : ℝ) (hr : 0 < r) :
    IsProbabilityMeasure (rateExpProbability r) :=
  isProbabilityMeasureGamma (by norm_num) hr

theorem rate_exp_density (r : ℝ) :
    rateExpProbability r = (volume.restrict (Ioi (0:ℝ))).withDensity
      (fun t => ENNReal.ofReal (r*Real.exp (-(r*t)))) := by
  change volume.withDensity (gammaPDF 1 r) = _
  have he : gammaPDF 1 r = (Ici (0:ℝ)).indicator
      (fun t => ENNReal.ofReal (r*Real.exp (-(r*t)))) := by
    funext t
    by_cases ht : 0 ≤ t <;> simp [gammaPDF,gammaPDFReal,ht]
  rw [he,withDensity_indicator measurableSet_Ici,← restrict_Ioi_eq_restrict_Ici]

theorem rate_exp_integral (r : ℝ) (hr : 0 < r) (f : ℝ → ℝ) :
    (∫ t, f t ∂rateExpProbability r) =
      ∫ t : ℝ in Ioi 0, r*Real.exp (-(r*t))*f t := by
  rw [rate_exp_density]
  change (∫ t, f t ∂(volume.restrict (Ioi (0:ℝ))).withDensity
    (fun t => ((Real.toNNReal (r*Real.exp (-(r*t))) : ℝ≥0) : ℝ≥0∞))) = _
  have hm : Measurable (fun t : ℝ => r*Real.exp (-(r*t))) := by fun_prop
  rw [integral_withDensity_eq_integral_smul hm.real_toNNReal]
  apply integral_congr_ae
  filter_upwards with t
  rw [NNReal.smul_def,smul_eq_mul,Real.coe_toNNReal _ (mul_pos hr (Real.exp_pos _)).le]

theorem rate_exp_mean (r : ℝ) (hr : 0 < r) :
    (∫ t : ℝ, t ∂rateExpProbability r) = 1/r := by
  rw [rate_exp_integral r hr]
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := r) (by norm_num) hr
  norm_num [Real.rpow_two] at hi
  have he : (∫ t : ℝ in Ioi 0, r*Real.exp (-(r*t))*t) =
      r*(∫ t : ℝ in Ioi 0, t*Real.exp (-(r*t))) := by
    rw [← integral_mul_left]
    congr 1
    funext t
    ring
  rw [he,hi]
  field_simp
  ring

theorem rate_exp_identity_integrable (r : ℝ) (hr : 0 < r) :
    Integrable (fun t : ℝ => t) (rateExpProbability r) := by
  apply Integrable.of_integral_ne_zero
  rw [rate_exp_mean r hr]
  exact (one_div_pos.mpr hr).ne'

theorem rate_exp_log_likelihood (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    Real.log ((a*Real.exp (-(a*t)))/(b*Real.exp (-(b*t)))) =
      Real.log (a/b)+(b-a)*t := by
  rw [Real.log_div (mul_pos ha (Real.exp_pos _)).ne' (mul_pos hb (Real.exp_pos _)).ne',
    Real.log_mul ha.ne' (Real.exp_ne_zero _),Real.log_mul hb.ne' (Real.exp_ne_zero _),
    Real.log_exp,Real.log_exp,Real.log_div ha.ne' hb.ne']
  ring

theorem rate_exp_log_rn_derivative (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (fun t => Real.log (((rateExpProbability a).rnDeriv (rateExpProbability b) t).toReal)) =ᵐ[
      rateExpProbability a] (fun t => Real.log (a/b)+(b-a)*t) := by
  have hh := rn_derivative_positive_densities (volume.restrict (Ioi (0:ℝ)))
    (fun t => a*Real.exp (-(a*t))) (fun t => b*Real.exp (-(b*t)))
    (by fun_prop) (by fun_prop)
    (ae_of_all _ (fun t => (mul_pos ha (Real.exp_pos _)).le))
    (ae_of_all _ (fun t => mul_pos hb (Real.exp_pos _)))
  rw [← rate_exp_density a,← rate_exp_density b] at hh
  filter_upwards [hh] with t ht
  rw [ht,rate_exp_log_likelihood a b ha hb]

theorem exponential_relative_entropy_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun t => Real.log (((rateExpProbability a).rnDeriv (rateExpProbability b) t).toReal))
      (rateExpProbability a) := by
  letI := rate_exp_is_probability a ha
  apply ((integrable_const (Real.log (a/b))).add
    ((rate_exp_identity_integrable a ha).const_mul (b-a))).congr
  exact (rate_exp_log_rn_derivative a b ha hb).symm

theorem exponential_relative_entropy (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    finiteRelativeEntropy (rateExpProbability a) (rateExpProbability b) =
      SigmaBase.potential (b/a) := by
  letI := rate_exp_is_probability a ha
  rw [finiteRelativeEntropy,integral_congr_ae (rate_exp_log_rn_derivative a b ha hb),
    integral_add (integrable_const _) ((rate_exp_identity_integrable a ha).const_mul _),
    integral_const,integral_mul_left,rate_exp_mean a ha]
  simp only [measure_univ,ENNReal.one_toReal,one_smul]
  unfold SigmaBase.potential
  rw [Real.log_div ha.ne' hb.ne',Real.log_div hb.ne' ha.ne']
  field_simp
  ring

theorem exponential_mutual_absolute_continuity (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    rateExpProbability a ≪ rateExpProbability b ∧ rateExpProbability b ≪ rateExpProbability a := by
  simp only [rate_exp_density]
  constructor
  · exact positive_density_absolute_continuity _ _ _ (by fun_prop)
      (ae_of_all _ (fun _ => mul_pos hb (Real.exp_pos _)))
  · exact positive_density_absolute_continuity _ _ _ (by fun_prop)
      (ae_of_all _ (fun _ => mul_pos ha (Real.exp_pos _)))

end
end Sigma
