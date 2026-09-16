import SigmaRealCharacteristicBaseChange
import SigmaRealCharacteristicTower
import Mathlib.RingTheory.Localization.Away.Basic

namespace Sigma
noncomputable section
open PowerSeries

/-- The actual polynomial parameter ring with 1+y inverted. -/
abbrev CharacteristicParameterRing :=
  Localization.Away (1 + (Polynomial.X : Polynomial ℚ))

instance characteristicParameterAlgebra : Algebra ℚ CharacteristicParameterRing :=
  ((algebraMap (Polynomial ℚ) CharacteristicParameterRing).comp
    (algebraMap ℚ (Polynomial ℚ))).toAlgebra

def localizedCharacteristicParameter : CharacteristicParameterRing :=
  algebraMap (Polynomial ℚ) CharacteristicParameterRing Polynomial.X

theorem localized_characteristic_parameter_unit :
    IsUnit (1 + localizedCharacteristicParameter) := by
  simpa only [map_add, map_one, localizedCharacteristicParameter] using
    (IsLocalization.Away.algebraMap_isUnit (S := CharacteristicParameterRing)
      (1 + (Polynomial.X : Polynomial ℚ)))

/-- The inverse substitution really is defined in Q[y,(1+y)^(-1)]. -/
theorem formal_chi_polynomial_localization_reconstruction :
    ∃ r : CharacteristicParameterRing,
      (1 + localizedCharacteristicParameter) * r = 1 ∧
      r * (1 + localizedCharacteristicParameter) = 1 ∧
      rescale r (formalChiOver CharacteristicParameterRing localizedCharacteristicParameter) +
        C CharacteristicParameterRing (localizedCharacteristicParameter * r) * X =
          (formalToddUnitOver CharacteristicParameterRing : PowerSeries CharacteristicParameterRing) :=
  formal_chi_over_recovers_todd CharacteristicParameterRing _ localized_characteristic_parameter_unit

end
end Sigma
