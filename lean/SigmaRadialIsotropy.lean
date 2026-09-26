import SigmaRadialQuaternion

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Quaternion

/-- The normalized-Gaussian quaternion orbit average. -/
def radialQuaternionAverage (f : ℍ → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ q, f (Real.sqrt (2*t) • radialQuaternionDirection q) ∂radialQuaternionGaussian

theorem radial_quaternion_average_measurable (f : ℍ → ℝ≥0∞) (hf : Measurable f) :
    Measurable (radialQuaternionAverage f) := by
  apply Measurable.lintegral_prod_right
  exact hf.comp ((Real.continuous_sqrt.measurable.comp (measurable_const.mul measurable_fst)).smul
    (radial_quaternion_direction_measurable.comp measurable_snd))

theorem radial_quaternion_orbit_average (f : ℍ → ℝ≥0∞) (hf : Measurable f) (x : ℍ) :
    (∫⁻ q, f (radialQuaternionDirection q * x) ∂radialQuaternionGaussian) =
      radialQuaternionAverage f (‖x‖^2/2) := by
  have hs : Real.sqrt (2*(‖x‖^2/2)) = ‖x‖ := by
    rw [show 2*(‖x‖^2/2) = ‖x‖^2 by ring, Real.sqrt_sq (norm_nonneg x)]
  rw [radialQuaternionAverage, hs]
  by_cases hx : x=0
  · simp [hx]
  let u := radialQuaternionDirection x
  have hu : ‖u‖ = 1 := radial_quaternion_direction_norm x hx
  have hm := radial_quaternion_gaussian_isometry (radialQuaternionRight u hu)
  have he := lintegral_map (μ := radialQuaternionGaussian)
    (hf.comp (show Measurable (fun q => ‖x‖ • radialQuaternionDirection q) from
      measurable_const.smul radial_quaternion_direction_measurable))
    (radialQuaternionRight u hu).continuous.measurable
  rw [hm] at he
  simp only [Function.comp_apply] at he
  rw [he]
  apply lintegral_congr
  intro q
  change f (radialQuaternionDirection q*x) =
    f (‖x‖ • radialQuaternionDirection (q*u))
  rw [radial_quaternion_direction_right q u hu, ← mul_smul_comm,
    radial_quaternion_direction_reconstruct]

/-- For an invariant law, averaging unit-quaternion rotations leaves every
nonnegative Borel integral unchanged and makes it depend only on energy. -/
theorem radial_quaternion_isotropic_integral (μ : Measure ℍ) [IsProbabilityMeasure μ]
    (hμ : ∀ U : ℍ ≃ₗᵢ[ℝ] ℍ, μ.map U = μ)
    (f : ℍ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) = ∫⁻ t, radialQuaternionAverage f t ∂μ.map (fun q => ‖q‖^2/2) := by
  rw [lintegral_map (radial_quaternion_average_measurable f hf) (by fun_prop)]
  have hi : (∫⁻ q, ∫⁻ x, f (radialQuaternionDirection q*x) ∂μ ∂radialQuaternionGaussian) =
      ∫⁻ x, f x ∂μ := by
    calc
      _ = ∫⁻ _q, (∫⁻ x, f x ∂μ) ∂radialQuaternionGaussian := by
        apply lintegral_congr_ae
        filter_upwards [radial_quaternion_gaussian_nonzero] with q hq
        have he := lintegral_map (μ := μ) hf
          (radialQuaternionLeft _ (radial_quaternion_direction_norm q hq)).continuous.measurable
        rw [hμ] at he
        exact he.symm
      _ = _ := by simp
  rw [← hi, lintegral_lintegral_swap]
  · apply lintegral_congr
    intro x
    exact radial_quaternion_orbit_average f hf x
  · exact (hf.comp ((radial_quaternion_direction_measurable.comp measurable_fst).mul
      measurable_snd)).aemeasurable

/-- An orthogonally invariant quaternion law is identified by the complete
radial-energy distribution. -/
theorem radial_quaternion_isotropic_unique (μ : Measure ℍ) [IsProbabilityMeasure μ]
    (hμ : ∀ U : ℍ ≃ₗᵢ[ℝ] ℍ, μ.map U = μ)
    (hE : μ.map (fun q => ‖q‖^2/2) = gammaProbability) : μ = radialQuaternionGaussian := by
  have hi (f : ℍ → ℝ≥0∞) (hf : Measurable f) :
      (∫⁻ x, f x ∂μ) = ∫⁻ x, f x ∂radialQuaternionGaussian := by
    rw [radial_quaternion_isotropic_integral μ hμ f hf, hE,
      radial_quaternion_isotropic_integral radialQuaternionGaussian
        radial_quaternion_gaussian_isometry f hf, radial_quaternion_gaussian_energy]
  ext s hs
  simpa only [lintegral_indicator hs, lintegral_one, Measure.restrict_apply_univ] using
    hi (s.indicator (fun _ => 1)) (measurable_const.indicator hs)

/-- Within the actual isotropic four-dimensional context, the radial energy
law uniquely identifies the standard Gaussian. -/
theorem radial_four_isotropic_unique (μ : Measure (EuclideanSpace ℝ (Fin 4)))
    [IsProbabilityMeasure μ]
    (hμ : ∀ U : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4), μ.map U = μ)
    (hE : μ.map radialFourEnergy = gammaProbability) : μ = radialFourGaussian := by
  let e := Quaternion.linearIsometryEquivTuple
  let ν := μ.map e.symm
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_map e.symm.continuous.measurable.aemeasurable
  have hν : ∀ U : ℍ ≃ₗᵢ[ℝ] ℍ, ν.map U = ν := by
    intro U
    have h := congrArg (fun ρ : Measure (EuclideanSpace ℝ (Fin 4)) => ρ.map e.symm)
      (hμ ((e.symm.trans U).trans e))
    dsimp only at h
    rw [Measure.map_map e.symm.continuous.measurable
      ((e.symm.trans U).trans e).continuous.measurable] at h
    change (μ.map e.symm).map U = _
    rw [Measure.map_map U.continuous.measurable e.symm.continuous.measurable]
    convert h using 2
  have hνE : ν.map (fun q => ‖q‖^2/2) = gammaProbability := by
    change (μ.map e.symm).map _ = _
    rw [Measure.map_map (by fun_prop) e.symm.continuous.measurable]
    convert hE using 1
    congr 1
    funext x
    simp only [Function.comp_apply, LinearIsometryEquiv.norm_map, radialFourEnergy]
  have h := congrArg (fun ρ : Measure ℍ => ρ.map e)
    (radial_quaternion_isotropic_unique ν hν hνE)
  simpa only [ν, radialQuaternionGaussian, Measure.map_map e.continuous.measurable
    e.symm.continuous.measurable, LinearIsometryEquiv.symm_apply_apply,
    Function.comp_def, LinearIsometryEquiv.apply_symm_apply, Measure.map_id'] using h

theorem radial_four_isotropic_energy_iff (μ : Measure (EuclideanSpace ℝ (Fin 4)))
    [IsProbabilityMeasure μ]
    (hμ : ∀ U : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4), μ.map U = μ) :
    μ.map radialFourEnergy = gammaProbability ↔ μ = radialFourGaussian :=
  ⟨radial_four_isotropic_unique μ hμ, fun h => h.symm ▸ radial_four_gaussian_energy⟩

end
end Sigma
