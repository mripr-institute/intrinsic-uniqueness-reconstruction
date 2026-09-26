import SigmaMatrixGaussianMoments
import SigmaRealRadialBoundary
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

/-- The standard four-dimensional Gaussian, transported from its four independent
standard normal coordinates to the actual Euclidean space. -/
def radialFourGaussian : Measure (EuclideanSpace ℝ (Fin 4)) :=
  (standardMatrixGaussianMeasure (Fin 4)).map (EuclideanSpace.measurableEquiv (Fin 4)).symm

instance radial_four_gaussian_probability : IsProbabilityMeasure radialFourGaussian :=
  isProbabilityMeasure_map (EuclideanSpace.measurableEquiv (Fin 4)).symm.measurable.aemeasurable

theorem radial_four_energy_coordinates (x : EuclideanSpace ℝ (Fin 4)) :
    radialFourEnergy x = (∑ i, x i ^ 2) / 2 := by
  simp only [radialFourEnergy, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]

theorem radial_four_gaussian_density :
    radialFourGaussian = volume.withDensity (fun x =>
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi)) ^ (-4 : ℤ) *
        Real.exp (-radialFourEnergy x))) := by
  rw [radialFourGaussian, standardMatrixGaussianMeasure,
    measurable_equiv_map_with_density _ _ _
      standard_matrix_gaussian_pdf_continuous.measurable.ennreal_ofReal,
    (MeasurePreserving.symm (EuclideanSpace.measurableEquiv (Fin 4))
      (EuclideanSpace.volume_preserving_measurableEquiv (Fin 4))).map_eq]
  congr 1
  funext x
  rw [standard_matrix_gaussian_pdf_formula, radial_four_energy_coordinates]
  norm_num only [Fintype.card_fin]
  simp only [MeasurableEquiv.symm_symm, EuclideanSpace.coe_measurableEquiv, neg_div]
  rfl

/-- Orthogonal invariance of the actual four-dimensional Gaussian measure. -/
theorem radial_four_gaussian_orthogonal (U : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin 4)) : radialFourGaussian.map U = radialFourGaussian := by
  rw [radial_four_gaussian_density]
  change (volume.withDensity _).map U.toHomeomorph.toMeasurableEquiv = _
  rw [measurable_equiv_map_with_density _ U.toHomeomorph.toMeasurableEquiv _
      (by exact (continuous_const.mul
        (Real.continuous_exp.comp radial_four_energy_continuous.neg)).measurable.ennreal_ofReal)]
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 4))).map
      U.toHomeomorph.toMeasurableEquiv = volume := U.measurePreserving.map_eq
  rw [hvol]
  congr 1
  funext x
  simp [radialFourEnergy]

/-- One coordinate's quadratic Laplace transform, obtained from the Gaussian
integral, with no chi-square distribution premise. -/
theorem gaussian_square_laplace (s : ℝ) (hs : 0 ≤ s) :
    (∫ x : ℝ, Real.exp (-s * (x ^ 2 / 2)) ∂gaussianReal 0 1) =
      (Real.sqrt (1 + s))⁻¹ := by
  rw [gaussian_integral 1 (by norm_num)]
  have he : (fun x : ℝ => gaussianPDFReal 0 1 x * Real.exp (-s * (x ^ 2 / 2))) =
      (fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((1+s)/2) * x^2)) := by
    funext x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, one_div]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he, integral_mul_left, integral_gaussian]
  rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
  have hh : (2 * Real.pi)⁻¹ * (Real.pi / ((1+s)/2)) = (1+s)⁻¹ := by
    have hp := Real.pi_pos.ne'
    have hsp : 1+s ≠ 0 := by positivity
    field_simp
    simp_all [mul_comm]
  rw [hh, Real.sqrt_inv]

/-- The literal radial energy of a standard four-dimensional Gaussian has the
paper's Gamma(2,1) density. -/
theorem radial_four_gaussian_energy :
    radialFourGaussian.map radialFourEnergy = gammaProbability := by
  apply operator_full_line_mixing_characterization
  intro n
  rw [integral_map radial_four_energy_continuous.measurable.aemeasurable
      ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-(n:ℝ)*t))).measurable.aestronglyMeasurable),
    radialFourGaussian, integral_map
      (EuclideanSpace.measurableEquiv (Fin 4)).symm.measurable.aemeasurable
      (show AEStronglyMeasurable (fun x => Real.exp (-(n:ℝ)*radialFourEnergy x)) _ from
        (Real.continuous_exp.comp (continuous_const.mul radial_four_energy_continuous)).measurable.aestronglyMeasurable)]
  have he : (fun x : Fin 4 → ℝ => Real.exp (-(n:ℝ) *
      radialFourEnergy ((EuclideanSpace.measurableEquiv (Fin 4)).symm x))) =
      (fun x => ∏ i, Real.exp (-(n:ℝ) * (x i ^ 2 / 2))) := by
    funext x
    rw [radial_four_energy_coordinates, ← Real.exp_sum]
    congr 1
    simp only [Finset.sum_div, Finset.mul_sum]
    rfl
  rw [he, standard_matrix_gaussian_product_integral
    (fun (_ : Fin 4) (t : ℝ) => Real.exp (-(n:ℝ) * (t^2/2)))]
  simp only [gaussian_square_laplace (n:ℝ) (Nat.cast_nonneg n),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_div]
  rw [inv_pow, show (Real.sqrt (1+(n:ℝ)))^4 = (1+(n:ℝ))^2 by
    rw [show (4:ℕ)=2*2 by norm_num, pow_mul, Real.sq_sqrt (by positivity)], inv_pow]

end
end Sigma
