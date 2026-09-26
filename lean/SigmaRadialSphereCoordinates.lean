import SigmaRadialSphereGaussian
import SigmaRadialOUNormalization

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

def radialFourUnitVector : EuclideanSpace ℝ (Fin 4) := EuclideanSpace.single 0 1

theorem radial_four_unit_vector_norm : ‖radialFourUnitVector‖ = 1 := by
  simp [radialFourUnitVector, EuclideanSpace.norm_single]

/-- The actual direction, with a designated unit vector at the null origin. -/
def radialFourDirection (z : EuclideanSpace ℝ (Fin 4)) : RadialFourSphere :=
  ⟨radialOUNormalize radialFourUnitVector z,
    mem_sphere_zero_iff_norm.mpr (radial_ou_normalize_norm _ _ radial_four_unit_vector_norm)⟩

theorem radial_four_direction_measurable : Measurable radialFourDirection :=
  (radial_ou_normalize_measurable radialFourUnitVector).subtype_mk

theorem radial_four_direction_lift (a : RadialFourSphere) (t : ℝ) (ht : 0<t) :
    radialFourDirection (radialFourUniformLift (a,t)) = a := by
  have ha : ‖(a : EuclideanSpace ℝ (Fin 4))‖ = 1 := mem_sphere_zero_iff_norm.mp a.property
  have hs : 0 < Real.sqrt (2*t) := Real.sqrt_pos.mpr (by positivity)
  have hn : ‖radialFourUniformLift (a,t)‖ = Real.sqrt (2*t) := by
    simp only [radialFourUniformLift, norm_smul, Real.norm_eq_abs, abs_of_pos hs, ha, mul_one]
  apply Subtype.ext
  change radialOUNormalize radialFourUnitVector (radialFourUniformLift (a,t)) = a.val
  rw [radialOUNormalize, if_neg (norm_ne_zero_iff.mp (hn ▸ hs.ne')), hn]
  simp only [radialFourUniformLift, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

theorem radial_four_energy_uniform_lift (a : RadialFourSphere) (t : ℝ) (ht : 0 ≤ t) :
    radialFourEnergy (radialFourUniformLift (a,t)) = t := by
  rw [radialFourEnergy, radialFourUniformLift, norm_smul,
    mem_sphere_zero_iff_norm.mp a.property, mul_one, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity)]
  ring

/-- The Gaussian's actual direction and energy have the product law. Hence the
independent uniform direction is intrinsic to the isotropic realization. -/
theorem radial_four_gaussian_direction_energy :
    radialFourGaussian.map (fun z => (radialFourDirection z, radialFourEnergy z)) =
      radialFourUniformSphere.prod gammaProbability := by
  rw [← radial_four_uniform_gamma_lift,
    Measure.map_map (radial_four_direction_measurable.prod_mk
      radial_four_energy_continuous.measurable) radial_four_uniform_lift_measurable]
  calc
    _ = (radialFourUniformSphere.prod gammaProbability).map id := by
      apply Measure.map_congr
      have hp : ∀ᵐ p ∂radialFourUniformSphere.prod gammaProbability, 0 < p.2 := by
        apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_snd)).mpr
        exact Filter.Eventually.of_forall fun _ => operator_integer_samples_ae_pos
          gammaProbability operator_gamma_probability_integer_samples
      filter_upwards [hp] with p hp
      exact Prod.ext (radial_four_direction_lift p.1 p.2 hp)
        (radial_four_energy_uniform_lift p.1 p.2 hp.le)
    _ = _ := Measure.map_id

theorem radial_four_gaussian_direction_uniform :
    radialFourGaussian.map radialFourDirection = radialFourUniformSphere := by
  have h := congrArg (fun μ : Measure (RadialFourSphere × ℝ) => μ.map Prod.fst)
    radial_four_gaussian_direction_energy
  dsimp only at h
  rw [Measure.map_map measurable_fst (radial_four_direction_measurable.prod_mk
    radial_four_energy_continuous.measurable), Measure.map_fst_prod,
    measure_univ, one_smul] at h
  exact h

theorem radial_four_gaussian_direction_energy_independent :
    IndepFun radialFourDirection radialFourEnergy radialFourGaussian := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    radial_four_direction_measurable.aemeasurable
    radial_four_energy_continuous.measurable.aemeasurable).mpr
  rw [radial_four_gaussian_direction_uniform, radial_four_gaussian_energy,
    radial_four_gaussian_direction_energy]

end
end Sigma
