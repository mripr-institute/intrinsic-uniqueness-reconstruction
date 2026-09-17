import SigmaProbWeights

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

theorem normalized_weight_ae (μ : Measure ℝ) (w : ℝ → ℝ≥0∞)
    {p : ℝ → Prop} (h : ∀ᵐ t ∂μ, p t) : ∀ᵐ t ∂normalizedWeight μ w, p t :=
  Measure.ae_smul_measure ((withDensity_absolutelyContinuous μ w).ae_le h) _

/-- The real normalization in the manuscript is the same normalization as the
nonnegative-integral construction, with finiteness explicit. -/
theorem normalized_real_weight (μ : Measure ℝ) (w : ℝ → ℝ)
    (hi : Integrable w μ) (hn : ∀ᵐ t ∂μ, 0 ≤ w t) (hm : 0 < ∫ t, w t ∂μ) :
    normalizedWeight μ (fun t => ENNReal.ofReal (w t)) =
      ENNReal.ofReal (1 / ∫ t, w t ∂μ) • μ.withDensity (fun t => ENNReal.ofReal (w t)) := by
  rw [normalizedWeight, ← ofReal_integral_eq_lintegral_ofReal hi hn,
    ← ENNReal.ofReal_inv_of_pos hm, one_div]

theorem size_bias_real_normalizer (μ : Measure ℝ) (hpos : ∀ᵐ t ∂μ, 0 < t)
    (hm : 0 < ∫ t : ℝ, t ∂μ) :
    (∫⁻ t, sizeBiasWeight t ∂μ) = ENNReal.ofReal (∫ t : ℝ, t ∂μ) := by
  exact (ofReal_integral_eq_lintegral_ofReal (Integrable.of_integral_ne_zero hm.ne')
    (hpos.mono fun _ ht => ht.le)).symm

theorem reciprocal_size_bias_real_normalizer (μ : Measure ℝ)
    (hpos : ∀ᵐ t ∂μ, 0 < t) (hc : 0 < ∫ t : ℝ, t⁻¹ ∂μ) :
    (∫⁻ t, (sizeBiasWeight t)⁻¹ ∂μ) = ENNReal.ofReal (∫ t : ℝ, t⁻¹ ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal (Integrable.of_integral_ne_zero hc.ne')
    (hpos.mono fun t ht => (inv_pos.mpr ht).le)]
  apply lintegral_congr_ae
  filter_upwards [hpos] with t ht
  exact (ENNReal.ofReal_inv_of_pos ht).symm

theorem positive_size_bias_reciprocal_mean_real (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ t ∂μ, 0 < t) (hm : 0 < ∫ t : ℝ, t ∂μ) :
    (∫ t : ℝ, t⁻¹ ∂normalizedWeight μ sizeBiasWeight) = 1 / ∫ t : ℝ, t ∂μ := by
  have hp := normalized_weight_ae μ sizeBiasWeight hpos
  rw [integral_eq_lintegral_of_nonneg_ae
    (hp.mono fun t ht => (inv_pos.mpr ht).le) measurable_inv.aestronglyMeasurable]
  have he : (fun t : ℝ => ENNReal.ofReal t⁻¹) =ᵐ[normalizedWeight μ sizeBiasWeight]
      (fun t => (sizeBiasWeight t)⁻¹) := by
    filter_upwards [hp] with t ht
    exact ENNReal.ofReal_inv_of_pos ht
  rw [lintegral_congr_ae he, positive_size_bias_reciprocal_mean μ hpos,
    size_bias_real_normalizer μ hpos hm, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hm.le, one_div]

/-- Every positive observed law with finite positive reciprocal mean has the
positive size-bias inverse, whose actual mean is the reciprocal normalizer. -/
theorem positive_size_bias_inverse_exists (β : Measure ℝ) [IsProbabilityMeasure β]
    (hpos : ∀ᵐ t ∂β, 0 < t) (hc : 0 < ∫ t : ℝ, t⁻¹ ∂β) :
    let μ := normalizedWeight β (fun t => (sizeBiasWeight t)⁻¹)
    IsProbabilityMeasure μ ∧ (∀ᵐ t ∂μ, 0 < t) ∧
      (∫ t : ℝ, t ∂μ) = 1 / (∫ t : ℝ, t⁻¹ ∂β) ∧
      normalizedWeight μ sizeBiasWeight = β := by
  let w : ℝ → ℝ≥0∞ := fun t => (sizeBiasWeight t)⁻¹
  have hw : Measurable w := measurable_id.ennreal_ofReal.inv
  have hw0 : ∀ᵐ t ∂β, w t ≠ 0 := by
    filter_upwards with t
    exact ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hwT : ∀ᵐ t ∂β, w t ≠ ∞ := by
    filter_upwards [hpos] with t ht
    exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr ht).ne'
  have hn : (∫⁻ t, w t ∂β) = ENNReal.ofReal (∫ t : ℝ, t⁻¹ ∂β) :=
    reciprocal_size_bias_real_normalizer β hpos hc
  have hn0 : (∫⁻ t, w t ∂β) ≠ 0 := by rw [hn]; exact (ENNReal.ofReal_pos.mpr hc).ne'
  have hnT : (∫⁻ t, w t ∂β) ≠ ∞ := by rw [hn]; exact ENNReal.ofReal_ne_top
  have hp := normalized_weight_ae β w hpos
  refine ⟨normalized_weight_is_probability β w hn0 hnT, hp, ?_, ?_⟩
  · rw [integral_eq_lintegral_of_nonneg_ae (hp.mono fun _ ht => ht.le)
      measurable_id.aestronglyMeasurable]
    have hr := normalized_weight_reciprocal_mass β w hw hw0 hwT
    simp only [w, inv_inv] at hr
    change (∫⁻ t, sizeBiasWeight t ∂normalizedWeight β w).toReal = _
    rw [hr, hn, ENNReal.toReal_inv, ENNReal.toReal_ofReal hc.le, one_div]
  · simpa only [w, inv_inv] using normalized_weight_inverse β w hw hw0 hwT hn0 hnT

theorem positive_size_bias_inverse_real (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ t ∂μ, 0 < t) (hm : 0 < ∫ t : ℝ, t ∂μ) :
    normalizedWeight (normalizedWeight μ sizeBiasWeight) (fun t => (sizeBiasWeight t)⁻¹) = μ := by
  apply positive_size_bias_inverse μ hpos
  · rw [size_bias_real_normalizer μ hpos hm]
    exact (ENNReal.ofReal_pos.mpr hm).ne'
  · rw [size_bias_real_normalizer μ hpos hm]
    exact ENNReal.ofReal_ne_top

/-- The reciprocal real normalizer of a marked exponential tilt. -/
theorem marked_tilt_reciprocal_normalizer_real (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (θ : ℝ) (hm : 0 < ∫ t : ℝ, Real.exp (θ*t) ∂μ) :
    (∫ t : ℝ, Real.exp (-θ*t) ∂normalizedWeight μ (exponentialWeight θ)) =
      1 / (∫ t : ℝ, Real.exp (θ*t) ∂μ) := by
  have he := normalized_weight_reciprocal_mass μ (exponentialWeight θ)
    (exponential_weight_measurable θ)
    (Eventually.of_forall fun t => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
    (Eventually.of_forall fun t => ENNReal.ofReal_ne_top)
  simp only [exponential_weight_inverse] at he
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun t => (Real.exp_pos _).le)
    ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-θ*t))).aestronglyMeasurable)]
  change (∫⁻ t, exponentialWeight (-θ) t ∂normalizedWeight μ (exponentialWeight θ)).toReal = _
  rw [he]
  have hn : (∫⁻ t, exponentialWeight θ t ∂μ) =
      ENNReal.ofReal (∫ t : ℝ, Real.exp (θ*t) ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (Integrable.of_integral_ne_zero hm.ne')
      (Eventually.of_forall fun t => (Real.exp_pos _).le)).symm
  rw [hn, ENNReal.toReal_inv, ENNReal.toReal_ofReal hm.le, one_div]

/-- The displayed real-integral inverse of a marked tilt. -/
theorem marked_exponential_tilt_inverse_real (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (θ : ℝ) (hm : 0 < ∫ t : ℝ, Real.exp (θ*t) ∂μ) :
    let β := normalizedWeight μ (exponentialWeight θ)
    μ = ENNReal.ofReal (1 / ∫ t : ℝ, Real.exp (-θ*t) ∂β) •
      β.withDensity (exponentialWeight (-θ)) := by
  have hn : (∫⁻ t, exponentialWeight θ t ∂μ) =
      ENNReal.ofReal (∫ t : ℝ, Real.exp (θ*t) ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (Integrable.of_integral_ne_zero hm.ne')
      (Eventually.of_forall fun t => (Real.exp_pos _).le)).symm
  have hback : 0 < ∫ t : ℝ, Real.exp (-θ*t) ∂normalizedWeight μ (exponentialWeight θ) := by
    rw [marked_tilt_reciprocal_normalizer_real μ θ hm]
    exact one_div_pos.mpr hm
  have he := marked_exponential_tilt_inverse μ θ
    (by rw [hn]; exact (ENNReal.ofReal_pos.mpr hm).ne')
    (by rw [hn]; exact ENNReal.ofReal_ne_top)
  exact he.symm.trans (normalized_real_weight _ _ (Integrable.of_integral_ne_zero hback.ne')
    (Eventually.of_forall fun t => (Real.exp_pos _).le) hback)

end
end Sigma
