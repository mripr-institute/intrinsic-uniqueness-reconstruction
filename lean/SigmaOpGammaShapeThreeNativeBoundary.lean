import SigmaOpGammaShapeThreeClosure
import SigmaOpGammaShapeThreeEvolution
import SigmaOpGammaShapeThreeSpectrum
import SigmaOpLimitPoint

namespace Sigma
noncomputable section
open MeasureTheory Set

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

/-- The native differential closures have the same marked spectrum and fix the
constant, although their invariant coordinate laws and means differ. -/
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
