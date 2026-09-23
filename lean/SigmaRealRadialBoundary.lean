import SigmaOpMixing
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace

/-- The literal radial energy on the paper's four-dimensional Euclidean space. -/
def radialFourEnergy (z : EuclideanSpace ℝ (Fin 4)) : ℝ := ‖z‖ ^ 2 / 2

def radialFourPositiveLift (t : ℝ) : EuclideanSpace ℝ (Fin 4) :=
  Real.sqrt (2*t) • EuclideanSpace.single 0 1

def radialFourNegativeLift (t : ℝ) : EuclideanSpace ℝ (Fin 4) :=
  -radialFourPositiveLift t

theorem radial_four_positive_lift_continuous : Continuous radialFourPositiveLift := by
  unfold radialFourPositiveLift
  fun_prop

theorem radial_four_negative_lift_continuous : Continuous radialFourNegativeLift :=
  radial_four_positive_lift_continuous.neg

theorem radial_four_energy_continuous : Continuous radialFourEnergy := by
  unfold radialFourEnergy
  fun_prop

theorem radial_four_positive_lift_energy (t : ℝ) (ht : 0 ≤ t) :
    radialFourEnergy (radialFourPositiveLift t) = t := by
  simp only [radialFourEnergy, radialFourPositiveLift, norm_smul,
    EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [Real.sq_sqrt (by positivity)]
  ring

theorem radial_four_negative_lift_energy (t : ℝ) (ht : 0 ≤ t) :
    radialFourEnergy (radialFourNegativeLift t) = t := by
  simpa only [radialFourEnergy, radialFourNegativeLift, norm_neg] using
    radial_four_positive_lift_energy t ht

def radialFourPositiveLaw : Measure (EuclideanSpace ℝ (Fin 4)) :=
  gammaProbability.map radialFourPositiveLift

def radialFourNegativeLaw : Measure (EuclideanSpace ℝ (Fin 4)) :=
  gammaProbability.map radialFourNegativeLift

instance radial_four_positive_law_probability : IsProbabilityMeasure radialFourPositiveLaw :=
  isProbabilityMeasure_map radial_four_positive_lift_continuous.measurable.aemeasurable

instance radial_four_negative_law_probability : IsProbabilityMeasure radialFourNegativeLaw :=
  isProbabilityMeasure_map radial_four_negative_lift_continuous.measurable.aemeasurable

theorem radial_four_positive_law_energy :
    radialFourPositiveLaw.map radialFourEnergy = gammaProbability := by
  rw [radialFourPositiveLaw, Measure.map_map radial_four_energy_continuous.measurable
    radial_four_positive_lift_continuous.measurable]
  calc
    gammaProbability.map (radialFourEnergy ∘ radialFourPositiveLift) =
        gammaProbability.map id := by
      apply Measure.map_congr
      filter_upwards [operator_integer_samples_ae_pos gammaProbability
        operator_gamma_probability_integer_samples] with t ht
      exact radial_four_positive_lift_energy t ht.le
    _ = gammaProbability := Measure.map_id

theorem radial_four_negative_law_energy :
    radialFourNegativeLaw.map radialFourEnergy = gammaProbability := by
  rw [radialFourNegativeLaw, Measure.map_map radial_four_energy_continuous.measurable
    radial_four_negative_lift_continuous.measurable]
  calc
    gammaProbability.map (radialFourEnergy ∘ radialFourNegativeLift) =
        gammaProbability.map id := by
      apply Measure.map_congr
      filter_upwards [operator_integer_samples_ae_pos gammaProbability
        operator_gamma_probability_integer_samples] with t ht
      exact radial_four_negative_lift_energy t ht.le
    _ = gammaProbability := Measure.map_id

def radialFourPositiveHalfspace : Set (EuclideanSpace ℝ (Fin 4)) :=
  {z | 0 < ⟪EuclideanSpace.single 0 1, z⟫_ℝ}

theorem radial_four_halfspace_measurable : MeasurableSet radialFourPositiveHalfspace := by
  exact measurableSet_lt measurable_const (continuous_const.inner continuous_id).measurable

theorem radial_four_positive_law_halfspace :
    radialFourPositiveLaw radialFourPositiveHalfspace = 1 := by
  rw [radialFourPositiveLaw, Measure.map_apply
    radial_four_positive_lift_continuous.measurable radial_four_halfspace_measurable]
  have h : ∀ᵐ t ∂gammaProbability,
      t ∈ radialFourPositiveLift ⁻¹' radialFourPositiveHalfspace := by
    filter_upwards [operator_integer_samples_ae_pos gammaProbability
      operator_gamma_probability_integer_samples] with t ht
    simp only [mem_preimage, radialFourPositiveHalfspace, mem_setOf_eq,
      radialFourPositiveLift, inner_smul_right, EuclideanSpace.inner_single_left]
    simpa using Real.sqrt_pos.2 (by positivity : 0 < 2*t)
  exact (measure_congr (h.mono fun _ ht => propext (iff_true_intro ht))).trans (measure_univ)

theorem radial_four_negative_law_halfspace :
    radialFourNegativeLaw radialFourPositiveHalfspace = 0 := by
  rw [radialFourNegativeLaw, Measure.map_apply
    radial_four_negative_lift_continuous.measurable radial_four_halfspace_measurable]
  have he : radialFourNegativeLift ⁻¹' radialFourPositiveHalfspace = ∅ := by
    ext t
    simp [radialFourNegativeLift, radialFourPositiveLift, radialFourPositiveHalfspace,
      inner_smul_right, EuclideanSpace.inner_single_left, Real.sqrt_nonneg]
  rw [he, measure_empty]

theorem radial_four_laws_distinct : radialFourPositiveLaw ≠ radialFourNegativeLaw := by
  intro h
  have hh := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 4)) =>
    μ radialFourPositiveHalfspace) h
  change radialFourPositiveLaw radialFourPositiveHalfspace =
    radialFourNegativeLaw radialFourPositiveHalfspace at hh
  rw [radial_four_positive_law_halfspace, radial_four_negative_law_halfspace] at hh
  exact one_ne_zero hh

/-- The actual Gamma energy law does not identify a vector law, without any
isotropy assumption. This is the deletion-boundary clause of final:R1 only. -/
theorem gamma_radial_energy_does_not_identify_vector_law :
    ∃ μ ν : Measure (EuclideanSpace ℝ (Fin 4)),
      IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧ μ ≠ ν ∧
      μ.map radialFourEnergy = gammaProbability ∧
      ν.map radialFourEnergy = gammaProbability :=
  ⟨radialFourPositiveLaw, radialFourNegativeLaw, inferInstance, inferInstance,
    radial_four_laws_distinct, radial_four_positive_law_energy,
    radial_four_negative_law_energy⟩

end
end Sigma
