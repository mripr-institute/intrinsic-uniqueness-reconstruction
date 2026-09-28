import SigmaOpGammaShapeThreeBoundary
import SigmaOpGammaAlternativeRecipe

namespace Sigma
noncomputable section
open MeasureTheory Set

/-- The two native weighted-Hilbert carrier types are retained rather than
being replaced with scalar spectral data. Each packet includes its actual
partially defined operator, distinguished constant and coordinate law. -/
inductive NativeGammaStationaryRealization where
  | shapeTwo (A : LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert)
      (one : LaguerreWeightedHilbert) (coordinateLaw : Measure ℝ)
  | shapeThree (A : GammaShapeThreeWeightedHilbert →ₗ.[ℂ] GammaShapeThreeWeightedHilbert)
      (one : GammaShapeThreeWeightedHilbert) (coordinateLaw : Measure ℝ)

def gammaTwoStationaryRealization : NativeGammaStationaryRealization :=
  .shapeTwo laguerreCanonicalOperator (laguerreHilbertBasis 0) gammaProbability

def gammaThreeStationaryRealization : NativeGammaStationaryRealization :=
  .shapeThree gammaShapeThreeCanonicalOperator (gammaShapeThreeHilbertBasis 0)
    gammaShapeThreeProbability

def stationaryRealizationSpectrum : NativeGammaStationaryRealization → Set ℂ
  | .shapeTwo A _ _ => unboundedOperatorSpectrum A
  | .shapeThree A _ _ => unboundedOperatorSpectrum A

def stationaryCoordinateLaw : NativeGammaStationaryRealization → Measure ℝ
  | .shapeTwo _ _ p => p
  | .shapeThree _ _ p => p

theorem gamma_two_stationary_spectrum :
    stationaryRealizationSpectrum gammaTwoStationaryRealization =
      Set.range (fun n : ℕ => (n : ℂ)) :=
  laguerre_canonical_spectrum_exact

theorem gamma_three_stationary_spectrum :
    stationaryRealizationSpectrum gammaThreeStationaryRealization =
      Set.range (fun n : ℕ => (n : ℂ)) :=
  gamma_shape_three_canonical_spectrum

/-- The fixed exponent-two recipe chooses the actual Gamma-two native
realization on the integer-spectrum class. -/
def canonicalJSelection
    (_ : {S : Set ℂ // S = Set.range (fun n : ℕ => (n : ℂ))}) :
    NativeGammaStationaryRealization := gammaTwoStationaryRealization

theorem canonical_j_selection_spectrum
    (S : {X : Set ℂ // X = Set.range (fun n : ℕ => (n : ℂ))}) :
    stationaryRealizationSpectrum (canonicalJSelection S) = S.val := by
  change unboundedOperatorSpectrum laguerreCanonicalOperator = S.val
  rw [laguerre_canonical_spectrum_exact, S.property]

theorem canonical_j_selection_mixing
    (_ : {S : Set ℂ // S = Set.range (fun n : ℕ => (n : ℂ))}) :
    ∀ x : LaguerreWeightedHilbert,
      complexStrongIntegral nonnegativeGammaComplexMeasure
        (fun s => laguerreHeatOperator s.val s.property x) =
          laguerreSquaredResolvent 1 (by norm_num) x :=
  (gamma_shape_two_common_mixing_iff nonnegativeGammaComplexMeasure).mpr rfl

theorem canonical_j_selection_not_left_inverse :
    canonicalJSelection ⟨stationaryRealizationSpectrum gammaThreeStationaryRealization,
      gamma_three_stationary_spectrum⟩ ≠ gammaThreeStationaryRealization := by
  intro heq
  exact gamma_shape_three_coordinate_law_ne_shape_two
    (congrArg stationaryCoordinateLaw heq).symm

theorem canonical_j_selection_gamma_three_formula :
    canonicalJSelection ⟨stationaryRealizationSpectrum gammaThreeStationaryRealization,
      gamma_three_stationary_spectrum⟩ = gammaTwoStationaryRealization ∧
    canonicalJSelection ⟨stationaryRealizationSpectrum gammaThreeStationaryRealization,
      gamma_three_stationary_spectrum⟩ ≠ gammaThreeStationaryRealization :=
  ⟨rfl, canonical_j_selection_not_left_inverse⟩

end
end Sigma
