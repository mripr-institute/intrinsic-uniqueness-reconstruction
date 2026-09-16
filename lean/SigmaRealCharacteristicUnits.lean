import SigmaRealCharacteristicChi

namespace Sigma
noncomputable section
open PowerSeries

section Rings
variable (A : Type*) [CommRing A]

def unitChiForward (u : Aˣ) (T : PowerSeries A) : PowerSeries A :=
  rescale (u : A) T - C A ((u : A) - 1) * X

def unitChiBackward (u : Aˣ) (Q : PowerSeries A) : PowerSeries A :=
  rescale (↑u⁻¹ : A) Q + C A (((u : A) - 1) * (↑u⁻¹ : A)) * X

theorem unit_chi_left_inverse (u : Aˣ) (T : PowerSeries A) :
    unitChiBackward A u (unitChiForward A u T) = T := by
  apply PowerSeries.ext
  intro n
  simp only [unitChiBackward, unitChiForward, coeff_rescale,
    (coeff A n).map_add, (coeff A n).map_sub, coeff_C_mul, coeff_X]
  rw [mul_sub, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  split_ifs with hn
  · subst n
    simp only [pow_one, mul_one]
    ring
  · simp

theorem unit_chi_right_inverse (u : Aˣ) (Q : PowerSeries A) :
    unitChiForward A u (unitChiBackward A u Q) = Q := by
  apply PowerSeries.ext
  intro n
  simp only [unitChiBackward, unitChiForward, coeff_rescale,
    (coeff A n).map_add, (coeff A n).map_sub, coeff_C_mul, coeff_X]
  rw [mul_add, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
  split_ifs with hn
  · subst n
    simp only [pow_one, mul_one]
    have h := u.val_inv
    change (u : A) * (↑u⁻¹ : A) = 1 at h
    linear_combination ((u : A) - 1) * h
  · simp

def characteristicChiUnitEquiv (u : Aˣ) : PowerSeries A ≃ PowerSeries A where
  toFun := unitChiForward A u
  invFun := unitChiBackward A u
  left_inv := unit_chi_left_inverse A u
  right_inv := unit_chi_right_inverse A u

/-- This is the exact marked parameter condition over a general coefficient
ring. In a Q-algebra it specializes to the manuscript's unit-localized formula. -/
theorem characteristic_chi_recovery_of_unit (y : A) (u : Aˣ) (hu : (u : A) = 1 + y)
    (T : PowerSeries A) :
    rescale (↑u⁻¹ : A) (rescale (1 + y) T - C A y * X) +
      C A (y * (↑u⁻¹ : A)) * X = T := by
  have hy : (u : A) - 1 = y := by rw [hu]; ring
  simpa [unitChiForward, unitChiBackward, hu, add_sub_cancel_left] using
    unit_chi_left_inverse A u T

theorem characteristic_chi_recovery_unit_condition (y : A) (hy : IsUnit (1 + y))
    (T : PowerSeries A) :
    ∃ r : A, (1 + y) * r = 1 ∧ r * (1 + y) = 1 ∧
      rescale r (rescale (1 + y) T - C A y * X) + C A (y * r) * X = T := by
  obtain ⟨u, hu⟩ := hy
  refine ⟨(↑u⁻¹ : A), ?_, ?_, characteristic_chi_recovery_of_unit A y u hu T⟩
  · rw [← hu]
    exact u.val_inv
  · rw [← hu]
    exact u.inv_val

end Rings

section Fields
variable (K : Type*) [Field K] [CharZero K]

theorem normalized_series_inverse_involution (F : PowerSeries K)
    (hF : constantCoeff K F = 1) : F⁻¹⁻¹ = F := by
  apply (PowerSeries.inv_eq_iff_mul_eq_one ?_).2
  · exact PowerSeries.mul_inv_cancel F (by rw [hF]; exact one_ne_zero)
  · simp [constantCoeff_inv, hF]

theorem standard_characteristic_inverse_reconstruction (y : K) :
    (formalTodd K)⁻¹⁻¹ = formalTodd K ∧
    (formalAhat K)⁻¹⁻¹ = formalAhat K ∧
    (formalL K)⁻¹⁻¹ = formalL K ∧
    (formalChi K y)⁻¹⁻¹ = formalChi K y := by
  exact ⟨normalized_series_inverse_involution K _ (formal_todd_constant K),
    normalized_series_inverse_involution K _ (formal_ahat_constant K),
    normalized_series_inverse_involution K _ (formal_L_constant K),
    normalized_series_inverse_involution K _ (formal_chi_constant K y)⟩

end Fields
end
end Sigma
