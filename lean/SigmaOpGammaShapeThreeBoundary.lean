import SigmaOpGammaShapeThreeClosure
import SigmaOpGammaShapeThreeEvolution
import SigmaOpGammaShapeThreeSpectrum
import SigmaOpGammaShapeThreeInvariants
import SigmaOpLimitPoint

namespace Sigma
noncomputable section
open MeasureTheory Set
set_option maxHeartbeats 800000

theorem gamma_shape_three_resolvent_compact (a : ℝ) (ha : 0 < a) :
    IsCompactOperator (gammaShapeThreeResolvent a ha) := by
  exact ((laguerre_resolvent_compact a ha).comp_clm
    gammaShapeUnitary.symm.toLinearIsometry.toContinuousLinearMap).continuous_comp
      gammaShapeUnitary.continuous

theorem gamma_shape_three_canonical_spectrum :
    unboundedOperatorSpectrum gammaShapeThreeCanonicalOperator =
      Set.range (fun n : ℕ => (n : ℂ)) := by
  rw [gamma_shape_three_canonical_eq_spectral]
  exact gamma_shape_three_full_spectrum_exact

theorem gamma_shape_unitary_canonical_domain_iff (x : LaguerreWeightedHilbert) :
    gammaShapeUnitary x ∈ gammaShapeThreeCanonicalOperator.domain ↔
      x ∈ laguerreCanonicalOperator.domain := by
  rw [gamma_shape_three_canonical_eq_spectral]
  exact gamma_shape_unitary_spectral_domain_iff x

theorem gamma_shape_unitary_canonical_action (x : laguerreCanonicalOperator.domain) :
    gammaShapeUnitary (laguerreCanonicalOperator x) =
      gammaShapeThreeCanonicalOperator ⟨gammaShapeUnitary x.val,
        (gamma_shape_unitary_canonical_domain_iff x.val).mpr x.property⟩ := by
  have he : gammaShapeThreeCanonicalOperator
      ⟨gammaShapeUnitary x.val,
        (gamma_shape_unitary_canonical_domain_iff x.val).mpr x.property⟩ =
      gammaShapeThreeSpectralOperator ⟨gammaShapeUnitary x.val,
        (gamma_shape_unitary_spectral_domain_iff x.val).mpr x.property⟩ :=
    gamma_shape_three_canonical_eq_spectral.le.2 rfl
  rw [he]
  exact gamma_shape_unitary_spectral_action x

theorem gamma_shape_three_canonical_heat_evolution :
    OpContractionEvolution gammaShapeThreeCanonicalOperator gammaShapeThreeHeat := by
  rw [gamma_shape_three_canonical_eq_spectral]
  exact gamma_shape_three_heat_evolution

/-- The generic mixing inverse is the same actual shift inverse used in the
spectral trace and determinant results. -/
theorem gamma_shape_three_native_resolvent_eq :
    gammaShapeThreeResolventOne = gammaShapeThreeResolvent 1 (by norm_num) := by
  apply ContinuousLinearMap.ext
  intro x
  have hR := gamma_shape_three_resolvent 1 (by norm_num)
  have hN := op_nonnegative_shift_resolvent gammaShapeThreeSpectralOperator
    gamma_shape_three_spectral_selfAdjoint gamma_shape_three_spectral_nonnegative
  have he := hN.left_inverse ⟨gammaShapeThreeResolvent 1 (by norm_num) x, hR.image_mem x⟩
  change opNonnegativeResolvent gammaShapeThreeSpectralOperator
    gamma_shape_three_spectral_selfAdjoint gamma_shape_three_spectral_nonnegative
    (gammaShapeThreeSpectralOperator ⟨gammaShapeThreeResolvent 1 (by norm_num) x,
      hR.image_mem x⟩ + (1 : ℂ) • gammaShapeThreeResolvent 1 (by norm_num) x) =
      gammaShapeThreeResolvent 1 (by norm_num) x at he
  have hright := hR.right_inverse x
  change gammaShapeThreeSpectralOperator ⟨gammaShapeThreeResolvent 1 (by norm_num) x,
    hR.image_mem x⟩ + (1 : ℂ) • gammaShapeThreeResolvent 1 (by norm_num) x = x at hright
  rw [hright] at he
  exact he

theorem gamma_shape_three_common_mixing_iff (μ : ComplexMeasure OpNonnegativeRay) :
    (∀ x : GammaShapeThreeWeightedHilbert,
      complexStrongIntegral μ (fun s => gammaShapeThreeHeat s.val x) =
        gammaShapeThreeSquaredResolvent 1 (by norm_num) x) ↔
      μ = nonnegativeGammaComplexMeasure := by
  rw [← gamma_shape_three_complex_mixing_iff]
  simp only [gamma_shape_three_native_resolvent_eq, gammaShapeThreeSquaredResolvent,
    ContinuousLinearMap.comp_apply]

theorem gamma_shape_two_native_resolvent_eq :
    opNonnegativeResolvent laguerreCanonicalOperator laguerre_canonical_selfAdjoint
      laguerre_canonical_nonnegative = laguerreResolvent 1 (by norm_num) := by
  apply ContinuousLinearMap.ext
  intro x
  have hR := laguerre_canonical_positive_shift_resolvent 1 (by norm_num)
  have hN := op_nonnegative_shift_resolvent laguerreCanonicalOperator
    laguerre_canonical_selfAdjoint laguerre_canonical_nonnegative
  have he := hN.left_inverse ⟨laguerreResolvent 1 (by norm_num) x, hR.image_mem x⟩
  change opNonnegativeResolvent laguerreCanonicalOperator laguerre_canonical_selfAdjoint
    laguerre_canonical_nonnegative
    (laguerreCanonicalOperator ⟨laguerreResolvent 1 (by norm_num) x, hR.image_mem x⟩ +
      (1 : ℂ) • laguerreResolvent 1 (by norm_num) x) = laguerreResolvent 1 (by norm_num) x at he
  have hright := hR.right_inverse x
  change laguerreCanonicalOperator ⟨laguerreResolvent 1 (by norm_num) x, hR.image_mem x⟩ +
    (1 : ℂ) • laguerreResolvent 1 (by norm_num) x = x at hright
  rw [hright] at he
  exact he

theorem gamma_shape_two_heat_on_ray (s : OpNonnegativeRay) :
    opNonnegativeHeat laguerreCanonicalOperator laguerre_canonical_selfAdjoint
      laguerre_canonical_nonnegative s.val = laguerreHeatOperator s.val s.property :=
  laguerre_canonical_heat_eq s.val s.property

theorem gamma_shape_two_common_mixing_iff (μ : ComplexMeasure OpNonnegativeRay) :
    (∀ x : LaguerreWeightedHilbert,
      complexStrongIntegral μ (fun s => laguerreHeatOperator s.val s.property x) =
        laguerreSquaredResolvent 1 (by norm_num) x) ↔
      μ = nonnegativeGammaComplexMeasure := by
  have h := gamma_shape_two_complex_mixing_iff μ
  simpa only [gamma_shape_two_heat_on_ray, gamma_shape_two_native_resolvent_eq,
    laguerreSquaredResolvent, ContinuousLinearMap.comp_apply] using h

theorem gamma_shapes_two_three_common_mixing (μ : ComplexMeasure OpNonnegativeRay) :
    ((∀ x : LaguerreWeightedHilbert,
      complexStrongIntegral μ (fun s => laguerreHeatOperator s.val s.property x) =
        laguerreSquaredResolvent 1 (by norm_num) x) ∧
     (∀ x : GammaShapeThreeWeightedHilbert,
      complexStrongIntegral μ (fun s => gammaShapeThreeHeat s.val x) =
        gammaShapeThreeSquaredResolvent 1 (by norm_num) x)) ↔
      μ = nonnegativeGammaComplexMeasure := by
  rw [gamma_shape_two_common_mixing_iff, gamma_shape_three_common_mixing_iff, and_self]

/-- The linked native differential closures retain the complete marked
spectrum and the constant, while their actual invariant coordinate laws differ.
The trace and determinant agreements are proved in the imported invariant module. -/
theorem gamma_shapes_two_three_native_boundary :
    IsSelfAdjoint laguerreCanonicalOperator ∧
    IsSelfAdjoint gammaShapeThreeCanonicalOperator ∧
    (∀ x : LaguerreWeightedHilbert,
      gammaShapeUnitary x ∈ gammaShapeThreeCanonicalOperator.domain ↔
        x ∈ laguerreCanonicalOperator.domain) ∧
    (∀ x : laguerreCanonicalOperator.domain,
      gammaShapeUnitary (laguerreCanonicalOperator x) =
        gammaShapeThreeCanonicalOperator ⟨gammaShapeUnitary x.val,
          (gamma_shape_unitary_canonical_domain_iff x.val).mpr x.property⟩) ∧
    gammaShapeUnitary (laguerreHilbertBasis 0) = gammaShapeThreeHilbertBasis 0 ∧
    unboundedOperatorSpectrum laguerreCanonicalOperator =
      unboundedOperatorSpectrum gammaShapeThreeCanonicalOperator ∧
    gammaShapeThreeProbability ≠ gammaProbability ∧
    (∫ t : ℝ, t ∂gammaProbability) = 2 ∧
    (∫ t : ℝ, t ∂gammaShapeThreeProbability) = 3 := by
  refine ⟨laguerre_canonical_selfAdjoint, ?_, gamma_shape_unitary_canonical_domain_iff,
    gamma_shape_unitary_canonical_action, gamma_shape_unitary_basis 0, ?_,
    gamma_shape_three_coordinate_law_ne_shape_two, gamma_probability_mean,
    gamma_shape_three_mean⟩
  · rw [gamma_shape_three_canonical_eq_spectral]
    exact gamma_shape_three_spectral_selfAdjoint
  · rw [laguerre_canonical_spectrum_exact, gamma_shape_three_canonical_spectrum]

end
end Sigma
