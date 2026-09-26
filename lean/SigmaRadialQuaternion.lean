import SigmaRadialGaussian
import Mathlib.Analysis.Quaternion

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Quaternion

instance radialQuaternionMeasurableSpace : MeasurableSpace ℍ := borel ℍ
instance radialQuaternionBorelSpace : BorelSpace ℍ := ⟨rfl⟩

/-- Left multiplication by a unit-norm quaternion is a real orthogonal map. -/
def radialQuaternionLeft (u : ℍ) (hu : ‖u‖ = 1) : ℍ ≃ₗᵢ[ℝ] ℍ :=
  { LinearMap.mulLeft ℝ u with
    toFun := fun x => u*x
    invFun := fun x => u⁻¹*x
    left_inv := fun x => by
      have h : u ≠ 0 := by intro h; simp [h] at hu
      simp [← mul_assoc, h]
    right_inv := fun x => by
      have h : u ≠ 0 := by intro h; simp [h] at hu
      simp [← mul_assoc, h]
    norm_map' := fun x => by simp [norm_mul, hu] }

/-- Right multiplication by a unit-norm quaternion is also orthogonal. -/
def radialQuaternionRight (u : ℍ) (hu : ‖u‖ = 1) : ℍ ≃ₗᵢ[ℝ] ℍ :=
  { LinearMap.mulRight ℝ u with
    toFun := fun x => x*u
    invFun := fun x => x*u⁻¹
    left_inv := fun x => by
      have h : u ≠ 0 := by intro h; simp [h] at hu
      simp [mul_assoc, h]
    right_inv := fun x => by
      have h : u ≠ 0 := by intro h; simp [h] at hu
      simp [mul_assoc, h]
    norm_map' := fun x => by simp [norm_mul, hu] }

def radialQuaternionGaussian : Measure ℍ :=
  radialFourGaussian.map Quaternion.linearIsometryEquivTuple.symm

instance radial_quaternion_gaussian_probability : IsProbabilityMeasure radialQuaternionGaussian :=
  isProbabilityMeasure_map Quaternion.linearIsometryEquivTuple.symm.continuous.measurable.aemeasurable

theorem radial_quaternion_gaussian_isometry (U : ℍ ≃ₗᵢ[ℝ] ℍ) :
    radialQuaternionGaussian.map U = radialQuaternionGaussian := by
  let e := Quaternion.linearIsometryEquivTuple
  have h := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 4)) => μ.map e.symm)
    (radial_four_gaussian_orthogonal ((e.symm.trans U).trans e))
  simp only [Measure.map_map e.symm.continuous.measurable
    ((e.symm.trans U).trans e).continuous.measurable] at h
  rw [radialQuaternionGaussian, Measure.map_map U.continuous.measurable
    e.symm.continuous.measurable]
  convert h using 2

theorem radial_quaternion_gaussian_energy :
    radialQuaternionGaussian.map (fun q => ‖q‖^2/2) = gammaProbability := by
  rw [radialQuaternionGaussian, Measure.map_map (by fun_prop)
    Quaternion.linearIsometryEquivTuple.symm.continuous.measurable]
  convert radial_four_gaussian_energy using 1
  congr 1
  funext x
  simp only [radialFourEnergy, Function.comp_apply, LinearIsometryEquiv.norm_map]

theorem radial_quaternion_gaussian_nonzero : ∀ᵐ q ∂radialQuaternionGaussian, q ≠ 0 := by
  have h := operator_integer_samples_ae_pos gammaProbability operator_gamma_probability_integer_samples
  rw [← radial_quaternion_gaussian_energy] at h
  have h' := (ae_map_iff (by fun_prop : Measurable (fun q : ℍ => ‖q‖^2/2)).aemeasurable
    measurableSet_Ioi).mp h
  filter_upwards [h'] with q hq
  intro he
  simp [he] at hq

/-- Normalization is assigned zero at zero, a Gaussian-null event. -/
def radialQuaternionDirection (q : ℍ) : ℍ := ‖q‖⁻¹ • q

theorem radial_quaternion_direction_measurable : Measurable radialQuaternionDirection :=
  measurable_id.norm.inv.smul measurable_id

theorem radial_quaternion_direction_norm (q : ℍ) (hq : q ≠ 0) :
    ‖radialQuaternionDirection q‖ = 1 := norm_smul_inv_norm hq

theorem radial_quaternion_direction_right (q u : ℍ) (hu : ‖u‖ = 1) :
    radialQuaternionDirection (q*u) = radialQuaternionDirection q * u := by
  simp [radialQuaternionDirection, norm_mul, hu, smul_mul_assoc]

theorem radial_quaternion_direction_reconstruct (q : ℍ) :
    ‖q‖ • radialQuaternionDirection q = q := by
  by_cases hq : q=0
  · simp [hq, radialQuaternionDirection]
  · simp [radialQuaternionDirection, smul_smul, norm_ne_zero_iff.mpr hq]

end
end Sigma
