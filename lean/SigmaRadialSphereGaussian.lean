import SigmaRadialSpherePolar
import SigmaRadialGaussian
import Mathlib.Probability.Independence.Basic

namespace Sigma
noncomputable section
open MeasureTheory Measure ProbabilityTheory Set Metric
open scoped ENNReal NNReal

def radialFourGaussianProfile (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt (2 * Real.pi)) ^ (-4 : ℤ) * Real.exp (-(r^2/2)))

theorem radial_four_gaussian_profile_measurable : Measurable radialFourGaussianProfile := by
  unfold radialFourGaussianProfile
  fun_prop

def radialFourGaussianRadius : Measure (Ioi (0 : ℝ)) :=
  radialFourRadiusMeasure radialFourGaussianProfile

instance radial_four_gaussian_radius_sfinite : SFinite radialFourGaussianRadius := by
  unfold radialFourGaussianRadius radialFourRadiusMeasure
  letI := SigmaFinite.withDensity_of_ne_top' (μ := Measure.volumeIoiPow 3)
    (fun r : Ioi (0 : ℝ) => show radialFourGaussianProfile r.val ≠ ∞ from ENNReal.ofReal_ne_top)
  infer_instance

/-- Actual angular/radial product disintegration of the four-dimensional
standard Gaussian, with normalized geometric surface measure. -/
theorem radial_four_gaussian_polar :
    (radialFourUniformSphere.prod radialFourGaussianRadius).map radialFourPolarLift =
      radialFourGaussian := by
  rw [radialFourGaussianRadius, radial_four_normalized_density _
    radial_four_gaussian_profile_measurable (fun _ => ENNReal.ofReal_ne_top),
    radial_four_gaussian_density]
  rfl

instance radial_four_gaussian_radius_probability : IsProbabilityMeasure radialFourGaussianRadius := by
  constructor
  have h := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 4)) => μ univ)
    radial_four_gaussian_polar
  dsimp only at h
  rw [Measure.map_apply radial_four_polar_lift_measurable MeasurableSet.univ,
    preimage_univ, ← Set.univ_prod_univ, Measure.prod_prod,
    measure_univ (μ := radialFourUniformSphere), one_mul,
    measure_univ (μ := radialFourGaussian)] at h
  exact h

def radialPositiveEnergy (r : Ioi (0 : ℝ)) : ℝ := r.val^2/2

theorem radial_positive_energy_measurable : Measurable radialPositiveEnergy := by
  unfold radialPositiveEnergy
  fun_prop

theorem radial_four_gaussian_radius_energy :
    radialFourGaussianRadius.map radialPositiveEnergy = gammaProbability := by
  have h := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 4)) => μ.map radialFourEnergy)
    radial_four_gaussian_polar
  dsimp only at h
  rw [Measure.map_map radial_four_energy_continuous.measurable radial_four_polar_lift_measurable,
    radial_four_gaussian_energy] at h
  have he : radialFourEnergy ∘ radialFourPolarLift = radialPositiveEnergy ∘ Prod.snd := by
    funext p
    simp only [Function.comp_apply, radialFourEnergy, radial_four_polar_lift_norm,
      radialPositiveEnergy]
  rw [he, ← Measure.map_map radial_positive_energy_measurable measurable_snd,
    Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h

def radialFourUniformLift (p : RadialFourSphere × ℝ) : EuclideanSpace ℝ (Fin 4) :=
  Real.sqrt (2*p.2) • p.1.val

theorem radial_four_uniform_lift_measurable : Measurable radialFourUniformLift := by
  unfold radialFourUniformLift
  fun_prop

/-- Independent Gamma radial energy and a genuine uniform point on S³
reconstruct the complete Gaussian vector law. -/
theorem radial_four_uniform_gamma_lift :
    (radialFourUniformSphere.prod gammaProbability).map radialFourUniformLift =
      radialFourGaussian := by
  rw [← radial_four_gaussian_radius_energy]
  have hp := Measure.map_prod_map radialFourUniformSphere radialFourGaussianRadius
    measurable_id radial_positive_energy_measurable
  simp only [Measure.map_id] at hp
  rw [hp, Measure.map_map radial_four_uniform_lift_measurable
    (measurable_id.prod_map radial_positive_energy_measurable)]
  have he : radialFourUniformLift ∘ Prod.map id radialPositiveEnergy = radialFourPolarLift := by
    funext p
    change Real.sqrt (2*(p.2.val^2/2)) • p.1.val = p.2.val • p.1.val
    rw [show 2*(p.2.val^2/2) = p.2.val^2 by ring, Real.sqrt_sq p.2.property.le]
  rw [he, radial_four_gaussian_polar]

/-- The converse also applies to supplied independent variables on any native
probability space, retaining the angular law and independence assumptions. -/
theorem radial_four_independent_uniform_inverse {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → ℝ) (A : Ω → RadialFourSphere)
    (hT : Measurable T) (hA : Measurable A) (hi : IndepFun A T P)
    (hTL : P.map T = gammaProbability) (hAL : P.map A = radialFourUniformSphere) :
    P.map (fun ω => Real.sqrt (2*T ω) • (A ω).val) = radialFourGaussian := by
  have h := (indepFun_iff_map_prod_eq_prod_map_map hA.aemeasurable hT.aemeasurable).mp hi
  rw [hAL,hTL] at h
  rw [← radial_four_uniform_gamma_lift, ← h,
    Measure.map_map radial_four_uniform_lift_measurable (hA.prod_mk hT)]
  rfl

end
end Sigma
