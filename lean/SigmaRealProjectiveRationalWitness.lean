import SigmaRealProjectiveKTheory
import SigmaRealProjectiveCechComputation
import Mathlib.RingTheory.PowerSeries.Basic

namespace Sigma
noncomputable section
open FiniteComplexBundle

/-- Evaluation of a scalar characteristic series in degrees zero and two
of the three-chart Čech complex. Every higher positive even degree of that
ordered complex is zero. -/
def realProjectiveCechCharacteristicValue (c : RealProjectiveCechH2 ℚ)
    (f : PowerSeries ℚ) : ℚ × RealProjectiveCechH2 ℚ :=
  (PowerSeries.coeff ℚ 0 f, PowerSeries.coeff ℚ 1 f • c)

theorem real_projective_cech_characteristic_series_equal (f : PowerSeries ℚ) :
    realProjectiveCechCharacteristicValue realProjectiveRationalFirstChern f =
      realProjectiveCechCharacteristicValue 0 f := by
  rw [real_projective_rational_first_chern_zero]

/-- A concrete fixed-base witness with native K⁰ classes and the computed
rational Čech characteristic image. The comparison with a separately
specified ordinary-cohomology theory is not assumed or claimed here. -/
theorem real_projective_native_k0_cech_characteristic_witness :
    kClass realProjectiveKLine ≠
      kClass (FiniteComplexBundle.trivial (B := RealProjectivePlane) 1) ∧
    realProjectiveCechChernCharacter = (1, 0) ∧
    ∀ f : PowerSeries ℚ,
      realProjectiveCechCharacteristicValue realProjectiveRationalFirstChern f =
        realProjectiveCechCharacteristicValue 0 f :=
  ⟨real_projective_complex_k0_class_ne_one,
    real_projective_cech_chern_character_one,
    real_projective_cech_characteristic_series_equal⟩

/-- Keeping an arbitrary complete scalar series, together with these
rational characteristic data, cannot recover the integral K⁰ class even
on the two actual line bundles over this one fixed base. -/
theorem real_projective_scalar_cech_data_no_k0_decoder (f : PowerSeries ℚ) :
    ¬ ∃ decode : PowerSeries ℚ × (ℚ × RealProjectiveCechH2 ℚ) →
        FiniteComplexBundle.K0 RealProjectivePlane,
      decode (f, realProjectiveCechChernCharacter) = kClass realProjectiveKLine ∧
      decode (f, (1, 0)) =
        kClass (FiniteComplexBundle.trivial (B := RealProjectivePlane) 1) := by
  rintro ⟨decode, hL, h1⟩
  apply real_projective_complex_k0_class_ne_one
  rw [real_projective_cech_chern_character_one] at hL
  exact hL.symm.trans h1

end
end Sigma
