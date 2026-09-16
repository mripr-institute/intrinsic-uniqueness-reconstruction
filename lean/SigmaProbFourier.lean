import SigmaProbWeights

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal NNReal

theorem unit_exp_complex_integral (f : ℝ → ℂ) :
    (∫ t, f t ∂unitExpProbability) =
      ∫ t : ℝ in Ioi 0, (Real.exp (-t) : ℂ) * f t := by
  change (∫ t, f t ∂volume.withDensity
    (fun t => ((Real.toNNReal (gammaPDFReal 1 1 t) : ℝ≥0) : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul
    ((measurable_gammaPDFReal 1 1).real_toNNReal)]
  have hfun : (fun t => Real.toNNReal (gammaPDFReal 1 1 t) • f t) =
      (Ici (0 : ℝ)).indicator (fun t => (Real.exp (-t) : ℂ) * f t) := by
    funext t
    rw [NNReal.smul_def, Complex.real_smul,
      Real.coe_toNNReal _ (gammaPDFReal_nonneg (by norm_num) (by norm_num) t), unit_exp_pdf]
    by_cases ht : 0 ≤ t <;> simp [ht]
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

theorem positive_rate_complex_exponential_integral (a : ℂ) (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, Complex.exp (-a * (t : ℂ))) = a⁻¹ := by
  have ha0 : a ≠ 0 := by intro he; simp [he] at ha
  have hr : (∫ t : ℝ in Ioi 0, Real.exp (-(a.re*t))) = (1/a.re) := by
    simpa using Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := a.re)
      (by norm_num) ha
  have hir : IntegrableOn (fun t : ℝ => Real.exp (-(a.re*t))) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hr]
    exact one_div_ne_zero ha.ne'
  have hic : IntegrableOn (fun t : ℝ => Complex.exp (-a*(t : ℂ))) (Ioi 0) := by
    apply hir.mono' ((continuous_const.mul Complex.continuous_ofReal).cexp.aestronglyMeasurable)
    filter_upwards with t
    simp [Complex.norm_eq_abs, Complex.abs_exp, Complex.mul_re]
  have hz : Tendsto (fun t : ℝ => Complex.exp (-a*(t : ℂ))) atTop (𝓝 0) := by
    apply Complex.tendsto_exp_nhds_zero_iff.mpr
    simpa only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, neg_mul] using
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop ha))
  have hl := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hic tendsto_id
  have ht : Tendsto (fun b : ℝ => ∫ t : ℝ in (0 : ℝ)..b,
      Complex.exp (-a*(t : ℂ))) atTop (𝓝 a⁻¹) := by
    simp_rw [integral_exp_mul_complex (neg_ne_zero.mpr ha0)]
    convert (hz.sub_const 1).div_const (-a) using 1 <;> simp
  exact tendsto_nhds_unique hl ht

theorem unit_exp_characteristic (x : ℝ) :
    probabilityCharacteristic unitExpProbability x = (1-Complex.I*(x : ℂ))⁻¹ := by
  rw [probabilityCharacteristic, unit_exp_complex_integral]
  have ha : 0 < (1-Complex.I*(x : ℂ)).re := by simp
  rw [← positive_rate_complex_exponential_integral _ ha]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem independent_exponential_pair_gamma :
    independentAffineSum unitExpProbability unitExpProbability 1 = gammaProbability := by
  apply operator_full_line_mixing_characterization
  intro n
  have he := independent_affine_sum_laplace unitExpProbability unitExpProbability 1 (n : ℝ)
  rw [one_mul, unit_exp_laplace n (Nat.cast_nonneg n)] at he
  change (∫ t : ℝ, Real.exp (-(n : ℝ)*t) ∂independentAffineSum
    unitExpProbability unitExpProbability 1) = _
  convert he using 1
  · apply integral_congr_ae
    filter_upwards with t
    congr 1
    ring
  · ring

theorem gamma_probability_characteristic (x : ℝ) :
    probabilityCharacteristic gammaProbability x = gammaCharacteristic x := by
  rw [← independent_exponential_pair_gamma, independent_affine_sum_characteristic,
    one_mul, unit_exp_characteristic]
  unfold gammaCharacteristic
  ring

theorem probability_characteristic_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    Integrable (fun t : ℝ => Complex.exp (((x*t : ℝ) : ℂ)*Complex.I)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
      continuous_const).cexp.aestronglyMeasurable)
  filter_upwards with t
  change ‖Complex.exp (((x*t : ℝ) : ℂ)*Complex.I)‖ ≤ 1
  rw [Complex.norm_eq_abs, Complex.abs_exp_ofReal_mul_I]

theorem atom_exp_mixture_characteristic (c x : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    probabilityCharacteristic (atomExpMixture c) x =
      (1-Complex.I*((c*x : ℝ) : ℂ))/(1-Complex.I*(x : ℂ)) := by
  have hi := probability_characteristic_integrable unitExpProbability x
  have hd := probability_characteristic_integrable (Measure.dirac (0 : ℝ)) x
  unfold atomExpMixture probabilityCharacteristic
  rw [integral_add_measure (hd.smul_measure ENNReal.ofReal_ne_top)
    (hi.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure]
  simp only [ENNReal.toReal_ofReal hc0, ENNReal.toReal_ofReal (sub_nonneg.mpr hc1),
    Complex.real_smul, integral_dirac, mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one]
  change (c : ℂ) + ((1-c : ℝ) : ℂ)*probabilityCharacteristic unitExpProbability x = _
  rw [unit_exp_characteristic]
  push_cast
  field_simp [characteristic_denominator_ne_zero x]
  ring

theorem gamma_residual_characteristic (c x : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    probabilityCharacteristic (gammaResidualProbability c) x = residualCharacteristic c x := by
  letI := atom_exp_mixture_probability c hc0 hc1
  rw [gammaResidualProbability, independent_affine_sum_characteristic, one_mul,
    atom_exp_mixture_characteristic c x hc0 hc1]
  unfold residualCharacteristic
  ring

theorem canonical_decomposition_characteristic_equation (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hlaw : independentAffineSum μ (gammaResidualProbability c) c = μ) :
    ∀ x, probabilityCharacteristic μ x = probabilityCharacteristic μ (c*x) *
      residualCharacteristic c x := by
  letI := gamma_residual_probability c hc0 hc1
  intro x
  calc
    probabilityCharacteristic μ x =
        probabilityCharacteristic (independentAffineSum μ (gammaResidualProbability c) c) x := by
      rw [hlaw]
    _ = _ := by rw [independent_affine_sum_characteristic,
      gamma_residual_characteristic c x hc0 hc1]

theorem gamma_characteristic_equation (c x : ℝ) :
    probabilityCharacteristic gammaProbability x =
      probabilityCharacteristic gammaProbability (c*x) * residualCharacteristic c x := by
  rw [gamma_probability_characteristic, gamma_probability_characteristic]
  exact gamma_characteristic_link c x

end
end Sigma
