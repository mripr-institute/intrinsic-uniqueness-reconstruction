import SigmaRealCharacteristicRoot

namespace Sigma
noncomputable section
open PowerSeries

variable (K : Type*) [Field K] [CharZero K]

def characteristicToddToChi (y : K) (T : PowerSeries K) : PowerSeries K :=
  rescale (1 + y) T - C K y * X

def characteristicChiToTodd (y : K) (Q : PowerSeries K) : PowerSeries K :=
  rescale (1 + y)⁻¹ Q + C K (y / (1 + y)) * X

/-- The normalized chi_y series, including its meaningful degenerate y=-1 value. -/
def formalChi (y : K) : PowerSeries K := characteristicToddToChi K y (formalTodd K)

def chiDenominator (y : K) : PowerSeries K :=
  formalShift K (1 - formalExponential K (-(1 + y)))

theorem formal_chi_constant (y : K) : constantCoeff K (formalChi K y) = 1 := by
  rw [formalChi, characteristicToddToChi, map_sub, map_mul, constantCoeff_X,
    mul_zero, sub_zero, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale]
  simp [coeff_zero_eq_constantCoeff_apply, formal_todd_constant]

theorem chi_denominator_constant (y : K) :
    constantCoeff K (chiDenominator K y) = 1 + y := by
  simp [chiDenominator, formalShift, formal_exponential_coeff_one]

theorem chi_denominator_mul_X (y : K) :
    chiDenominator K y * X = 1 - formalExponential K (-(1 + y)) := by
  apply formal_shift_mul_X
  simp [formal_exponential_constant]

theorem formal_chi_quotient_product (y : K) :
    (1 - formalExponential K (-(1 + y))) * formalChi K y =
      X * (1 + C K y * formalExponential K (-(1 + y))) := by
  have h := rescaled_todd_quotient K (1 + y)
  simp only [map_add, map_one] at h
  dsimp [formalChi, characteristicToddToChi]
  linear_combination h

/-- The standard exponential quotient, with its exact necessary unit condition. -/
theorem formal_chi_standard_quotient (y : K) (hy : y ≠ -1) :
    formalChi K y = (1 + C K y * formalExponential K (-(1 + y))) *
      (chiDenominator K y)⁻¹ := by
  have ha : 1 + y ≠ 0 := by
    intro h
    apply hy
    linear_combination h
  apply (PowerSeries.eq_mul_inv_iff_mul_eq (by rwa [chi_denominator_constant])).2
  have h := formal_chi_quotient_product K y
  rw [← chi_denominator_mul_X] at h
  apply mul_left_cancel₀ (PowerSeries.X_ne_zero : (X : PowerSeries K) ≠ 0)
  linear_combination h

omit [CharZero K] in
theorem characteristic_chi_Todd_inverse (y : K) (hy : y ≠ -1) (T : PowerSeries K) :
    characteristicChiToTodd K y (characteristicToddToChi K y T) = T := by
  have ha : 1 + y ≠ 0 := by intro h; apply hy; linear_combination h
  apply PowerSeries.ext
  intro n
  simp only [characteristicChiToTodd, characteristicToddToChi, map_add, map_sub,
    coeff_rescale, coeff_C_mul, coeff_X]
  rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ ha, one_pow, one_mul]
  split_ifs with hn
  · subst n
    simp
    field_simp
  · simp

omit [CharZero K] in
theorem characteristic_Todd_chi_inverse (y : K) (hy : y ≠ -1) (Q : PowerSeries K) :
    characteristicToddToChi K y (characteristicChiToTodd K y Q) = Q := by
  have ha : 1 + y ≠ 0 := by intro h; apply hy; linear_combination h
  apply PowerSeries.ext
  intro n
  simp only [characteristicChiToTodd, characteristicToddToChi, map_add, map_sub,
    coeff_rescale, coeff_C_mul, coeff_X]
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ ha, one_pow, one_mul]
  split_ifs with hn
  · subst n
    simp
    field_simp
  · simp

def characteristicChiEquiv (y : K) (hy : y ≠ -1) : PowerSeries K ≃ PowerSeries K where
  toFun := characteristicToddToChi K y
  invFun := characteristicChiToTodd K y
  left_inv := characteristic_chi_Todd_inverse K y hy
  right_inv := characteristic_Todd_chi_inverse K y hy

theorem formal_chi_recovers_todd (y : K) (hy : y ≠ -1) :
    rescale (1 + y)⁻¹ (formalChi K y) + C K (y / (1 + y)) * X = formalTodd K :=
  characteristic_chi_Todd_inverse K y hy (formalTodd K)

omit [CharZero K] in
theorem characteristic_chi_minus_one (T : PowerSeries K) (hT : constantCoeff K T = 1) :
    characteristicToddToChi K (-1) T = 1 + X := by
  simp [characteristicToddToChi, rescale_zero_apply, hT]

theorem formal_chi_minus_one_standard : formalChi K (-1) = 1 + X :=
  characteristic_chi_minus_one K (formalTodd K) (formal_todd_constant K)

theorem characteristic_chi_minus_one_noninjective :
    ∃ F G : PowerSeries K, constantCoeff K F = 1 ∧ constantCoeff K G = 1 ∧
      F ≠ G ∧ characteristicToddToChi K (-1) F = characteristicToddToChi K (-1) G := by
  refine ⟨1, 1 + X, by simp, by simp, ?_, ?_⟩
  · intro h
    have hc := congrArg (coeff K 1) h
    simp at hc
  · rw [characteristic_chi_minus_one K _ (by simp),
      characteristic_chi_minus_one K _ (by simp)]

end
end Sigma
