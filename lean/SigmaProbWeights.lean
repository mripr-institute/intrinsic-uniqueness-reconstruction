import SigmaProbResidual

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- A probability tilt is normalization after multiplication by a nonnegative
measurable weight. The normalizer is the actual integral. -/
def normalizedWeight (μ : Measure ℝ) (w : ℝ → ℝ≥0∞) : Measure ℝ :=
  (∫⁻ t, w t ∂μ)⁻¹ • μ.withDensity w

theorem normalized_weight_is_probability (μ : Measure ℝ) (w : ℝ → ℝ≥0∞)
    (hc0 : (∫⁻ t, w t ∂μ) ≠ 0) (hcT : (∫⁻ t, w t ∂μ) ≠ ∞) :
    IsProbabilityMeasure (normalizedWeight μ w) := by
  constructor
  rw [normalizedWeight, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hc0 hcT

theorem normalized_weight_reciprocal (μ : Measure ℝ) (w : ℝ → ℝ≥0∞)
    (hw : Measurable w) (hw0 : ∀ᵐ t ∂μ, w t ≠ 0) (hwT : ∀ᵐ t ∂μ, w t ≠ ∞) :
    (normalizedWeight μ w).withDensity (fun t => (w t)⁻¹) =
      (∫⁻ t, w t ∂μ)⁻¹ • μ := by
  rw [normalizedWeight, withDensity_smul_measure, withDensity_inv_same hw hw0 hwT]

theorem normalized_weight_reciprocal_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    (hw0 : ∀ᵐ t ∂μ, w t ≠ 0) (hwT : ∀ᵐ t ∂μ, w t ≠ ∞) :
    (∫⁻ t, (w t)⁻¹ ∂normalizedWeight μ w) = (∫⁻ t, w t ∂μ)⁻¹ := by
  have he := congrArg (fun ν : Measure ℝ => ν univ)
    (normalized_weight_reciprocal μ w hw hw0 hwT)
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] using he

theorem normalized_weight_inverse (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    (hw0 : ∀ᵐ t ∂μ, w t ≠ 0) (hwT : ∀ᵐ t ∂μ, w t ≠ ∞)
    (hc0 : (∫⁻ t, w t ∂μ) ≠ 0) (hcT : (∫⁻ t, w t ∂μ) ≠ ∞) :
    normalizedWeight (normalizedWeight μ w) (fun t => (w t)⁻¹) = μ := by
  change (∫⁻ t, (w t)⁻¹ ∂normalizedWeight μ w)⁻¹ •
    (normalizedWeight μ w).withDensity (fun t => (w t)⁻¹) = μ
  rw [normalized_weight_reciprocal_mass μ w hw hw0 hwT,
    normalized_weight_reciprocal μ w hw hw0 hwT, inv_inv, smul_smul,
    ENNReal.mul_inv_cancel hc0 hcT, one_smul]

def exponentialWeight (θ : ℝ) (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (θ*t))

theorem exponential_weight_measurable (θ : ℝ) : Measurable (exponentialWeight θ) := by
  exact ((continuous_const.mul continuous_id).rexp.measurable).ennreal_ofReal

theorem exponential_weight_inverse (θ t : ℝ) :
    (exponentialWeight θ t)⁻¹ = exponentialWeight (-θ) t := by
  unfold exponentialWeight
  rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
  congr 2
  ring

theorem marked_exponential_tilt_inverse (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (θ : ℝ) (hc0 : (∫⁻ t, exponentialWeight θ t ∂μ) ≠ 0)
    (hcT : (∫⁻ t, exponentialWeight θ t ∂μ) ≠ ∞) :
    normalizedWeight (normalizedWeight μ (exponentialWeight θ)) (exponentialWeight (-θ)) = μ := by
  have he := normalized_weight_inverse μ (exponentialWeight θ)
    (exponential_weight_measurable θ)
    (Eventually.of_forall fun t => ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
    (Eventually.of_forall fun t => ENNReal.ofReal_ne_top) hc0 hcT
  simpa only [exponential_weight_inverse] using he

theorem marked_exponential_tilt_identifies (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (θ : ℝ)
    (hμ0 : (∫⁻ t, exponentialWeight θ t ∂μ) ≠ 0)
    (hμT : (∫⁻ t, exponentialWeight θ t ∂μ) ≠ ∞)
    (hν0 : (∫⁻ t, exponentialWeight θ t ∂ν) ≠ 0)
    (hνT : (∫⁻ t, exponentialWeight θ t ∂ν) ≠ ∞)
    (he : normalizedWeight μ (exponentialWeight θ) =
      normalizedWeight ν (exponentialWeight θ)) : μ = ν := by
  calc
    μ = normalizedWeight (normalizedWeight μ (exponentialWeight θ))
      (exponentialWeight (-θ)) := (marked_exponential_tilt_inverse μ θ hμ0 hμT).symm
    _ = normalizedWeight (normalizedWeight ν (exponentialWeight θ))
      (exponentialWeight (-θ)) := by rw [he]
    _ = ν := marked_exponential_tilt_inverse ν θ hν0 hνT

def sizeBiasWeight (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal t

theorem positive_size_bias_inverse (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ t ∂μ, 0 < t)
    (hc0 : (∫⁻ t, sizeBiasWeight t ∂μ) ≠ 0)
    (hcT : (∫⁻ t, sizeBiasWeight t ∂μ) ≠ ∞) :
    normalizedWeight (normalizedWeight μ sizeBiasWeight) (fun t => (sizeBiasWeight t)⁻¹) = μ := by
  apply normalized_weight_inverse μ sizeBiasWeight measurable_id.ennreal_ofReal
    _ (Eventually.of_forall fun t => ENNReal.ofReal_ne_top) hc0 hcT
  filter_upwards [hpos] with t ht
  exact ne_of_gt (ENNReal.ofReal_pos.mpr ht)

theorem positive_size_bias_reciprocal_mean (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ t ∂μ, 0 < t) :
    (∫⁻ t, (sizeBiasWeight t)⁻¹ ∂normalizedWeight μ sizeBiasWeight) =
      (∫⁻ t, sizeBiasWeight t ∂μ)⁻¹ := by
  apply normalized_weight_reciprocal_mass μ sizeBiasWeight measurable_id.ennreal_ofReal
    _ (Eventually.of_forall fun t => ENNReal.ofReal_ne_top)
  filter_upwards [hpos] with t ht
  exact ne_of_gt (ENNReal.ofReal_pos.mpr ht)

theorem unit_exp_weighted_by_coordinate :
    unitExpProbability.withDensity sizeBiasWeight = gammaProbability := by
  change (volume.withDensity (ProbabilityTheory.gammaPDF 1 1)).withDensity sizeBiasWeight =
    volume.withDensity (ProbabilityTheory.gammaPDF 2 1)
  have hw : Measurable sizeBiasWeight := measurable_id.ennreal_ofReal
  have hg : Measurable (ProbabilityTheory.gammaPDF 1 1) :=
    (ProbabilityTheory.measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [← withDensity_mul volume hg hw]
  apply withDensity_congr_ae
  filter_upwards with t
  simp only [Pi.mul_apply, ProbabilityTheory.gammaPDF, unit_exp_pdf, gamma_pdf_intrinsic,
    sizeBiasWeight]
  by_cases ht : 0 ≤ t
  · simp only [if_pos ht, SigmaPresentations.density]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
  · simp only [if_neg ht, ENNReal.ofReal_zero, zero_mul]

theorem unit_exp_coordinate_mean : (∫⁻ t, sizeBiasWeight t ∂unitExpProbability) = 1 := by
  have he := congrArg (fun ν : Measure ℝ => ν univ) unit_exp_weighted_by_coordinate
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    gamma_probability_normalized] using he

theorem unit_exp_size_bias_gamma : normalizedWeight unitExpProbability sizeBiasWeight =
    gammaProbability := by
  rw [normalizedWeight, unit_exp_coordinate_mean, inv_one, one_smul,
    unit_exp_weighted_by_coordinate]

theorem unit_exp_positive : ∀ᵐ t ∂unitExpProbability, 0 < t := by
  rw [ae_iff]
  have he : {a : ℝ | ¬ 0 < a} = Iio 0 ∪ {0} := by ext a; simp [le_iff_lt_or_eq]
  rw [he]
  exact measure_union_null unit_exp_negative_ray (unit_exp_no_atom 0)

theorem gamma_positive_size_bias_inverse :
    normalizedWeight gammaProbability (fun t => (sizeBiasWeight t)⁻¹) = unitExpProbability := by
  rw [← unit_exp_size_bias_gamma]
  exact positive_size_bias_inverse unitExpProbability unit_exp_positive
    (by rw [unit_exp_coordinate_mean]; norm_num)
    (by rw [unit_exp_coordinate_mean]; norm_num)

theorem gamma_size_bias_identifies_positive_exponential (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hpos : ∀ᵐ t ∂μ, 0 < t)
    (hc0 : (∫⁻ t, sizeBiasWeight t ∂μ) ≠ 0)
    (hcT : (∫⁻ t, sizeBiasWeight t ∂μ) ≠ ∞)
    (hlaw : normalizedWeight μ sizeBiasWeight = gammaProbability) :
    μ = unitExpProbability := by
  have hi := positive_size_bias_inverse μ hpos hc0 hcT
  rw [hlaw, gamma_positive_size_bias_inverse] at hi
  exact hi.symm

end
end Sigma
