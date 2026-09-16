import SigmaRealCharacteristicUnits

namespace Sigma
noncomputable section
open PowerSeries

variable (A : Type*) [CommRing A] [Algebra ℚ A]

def mappedNormalizedSeriesUnit (F : PowerSeries ℚ) (hF : constantCoeff ℚ F = 1) :
    (PowerSeries A)ˣ where
  val := PowerSeries.map (algebraMap ℚ A) F
  inv := PowerSeries.map (algebraMap ℚ A) F⁻¹
  val_inv := by
    rw [← map_mul, PowerSeries.mul_inv_cancel F (by rw [hF]; exact one_ne_zero), map_one]
  inv_val := by
    rw [← map_mul, PowerSeries.inv_mul_cancel F (by rw [hF]; exact one_ne_zero), map_one]

def formalAhatUnitOver : (PowerSeries A)ˣ :=
  mappedNormalizedSeriesUnit A (formalAhat ℚ) (formal_ahat_constant ℚ)

def formalLUnitOver : (PowerSeries A)ˣ :=
  mappedNormalizedSeriesUnit A (formalL ℚ) (formal_L_constant ℚ)

def formalAhatSquareRootOver : PowerSeries A :=
  PowerSeries.map (algebraMap ℚ A) (formalAhatSquareRoot ℚ)

theorem rational_series_map_rescale (a : ℚ) (F : PowerSeries ℚ) :
    PowerSeries.map (algebraMap ℚ A) (rescale a F) =
      rescale (algebraMap ℚ A a) (PowerSeries.map (algebraMap ℚ A) F) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_map, coeff_rescale, map_mul, map_pow]

theorem rational_series_map_constant (F : PowerSeries ℚ) :
    constantCoeff A (PowerSeries.map (algebraMap ℚ A) F) =
      algebraMap ℚ A (constantCoeff ℚ F) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]

theorem formal_ahat_over_constant : constantCoeff A (formalAhatUnitOver A : PowerSeries A) = 1 := by
  change constantCoeff A (PowerSeries.map (algebraMap ℚ A) (formalAhat ℚ)) = 1
  rw [rational_series_map_constant, formal_ahat_constant, map_one]

theorem formal_L_over_constant : constantCoeff A (formalLUnitOver A : PowerSeries A) = 1 := by
  change constantCoeff A (PowerSeries.map (algebraMap ℚ A) (formalL ℚ)) = 1
  rw [rational_series_map_constant, formal_L_constant, map_one]

/-- Genuine hyperbolic-sine quotient after base change, not just an abstract unit. -/
theorem formal_ahat_over_quotient :
    (formalExponentialOver A (algebraMap ℚ A (1 / 2)) -
      formalExponentialOver A (-(algebraMap ℚ A (1 / 2)))) *
        (formalAhatUnitOver A : PowerSeries A) = X := by
  have h := congrArg (PowerSeries.map (algebraMap ℚ A)) (formal_ahat_quotient ℚ)
  simpa only [map_mul, map_sub, formal_exponential_over_map, map_neg, PowerSeries.map_X,
    formalAhatUnitOver, mappedNormalizedSeriesUnit] using h

theorem formal_L_over_quotient :
    (formalExponentialOver A 2 - 1) * (formalLUnitOver A : PowerSeries A) =
      X * (formalExponentialOver A 2 + 1) := by
  have h := congrArg (PowerSeries.map (algebraMap ℚ A)) (formal_L_quotient ℚ)
  simpa only [map_mul, map_add, map_sub, formal_exponential_over_map, map_ofNat, map_one,
    PowerSeries.map_X, formalLUnitOver, mappedNormalizedSeriesUnit] using h

theorem formal_ahat_over_to_todd :
    formalExponentialOver A (algebraMap ℚ A (1 / 2)) *
      (formalAhatUnitOver A : PowerSeries A) = (formalToddUnitOver A : PowerSeries A) := by
  have h := congrArg (PowerSeries.map (algebraMap ℚ A)) (formal_ahat_to_todd ℚ)
  simpa only [map_mul, formal_exponential_over_map, formalAhatUnitOver, formalToddUnitOver,
    mappedNormalizedSeriesUnit] using h

theorem formal_todd_over_to_L : (formalLUnitOver A : PowerSeries A) =
    rescale 2 (formalToddUnitOver A : PowerSeries A) - X := by
  have h := congrArg (PowerSeries.map (algebraMap ℚ A)) (formal_todd_to_L ℚ)
  simpa only [map_sub, rational_series_map_rescale, map_ofNat, PowerSeries.map_X,
    formalLUnitOver, formalToddUnitOver, mappedNormalizedSeriesUnit] using h

theorem formal_L_over_to_todd :
    rescale (algebraMap ℚ A (1 / 2)) (formalLUnitOver A : PowerSeries A) +
      C A (algebraMap ℚ A (1 / 2)) * X = (formalToddUnitOver A : PowerSeries A) := by
  have h := congrArg (PowerSeries.map (algebraMap ℚ A)) (formal_L_to_todd ℚ)
  simpa only [map_add, map_mul, rational_series_map_rescale, PowerSeries.map_C,
    PowerSeries.map_X, formalLUnitOver, formalToddUnitOver, mappedNormalizedSeriesUnit] using h

theorem formal_ahat_over_square_root_constant : constantCoeff A (formalAhatSquareRootOver A) = 2 := by
  rw [formalAhatSquareRootOver, rational_series_map_constant, formal_ahat_square_root_constant]
  simp only [map_ofNat]

theorem formal_ahat_over_square_root_equation :
    formalAhatSquareRootOver A ^ 2 =
      (X * (↑(formalAhatUnitOver A)⁻¹ : PowerSeries A)) ^ 2 + 4 := by
  have h := congrArg (PowerSeries.map (algebraMap ℚ A)) (formal_ahat_square_root_equation ℚ)
  simpa only [map_add, map_mul, map_pow, map_ofNat, PowerSeries.map_X,
    formalAhatSquareRootOver, formalAhatUnitOver, mappedNormalizedSeriesUnit,
    Units.val_inv_eq_inv_val] using h

theorem normalized_square_root_unique_over_Q_algebra (S R B : PowerSeries A)
    (hS : constantCoeff A S = 2) (hR : constantCoeff A R = 2)
    (hsq : S ^ 2 = B) (hrq : R ^ 2 = B) : S = R := by
  have hp : (S - R) * (S + R) = 0 := by linear_combination hsq - hrq
  have hu : IsUnit (S + R) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    have h4 : IsUnit (4 : ℚ) := isUnit_iff_ne_zero.mpr (by norm_num)
    have hm := h4.map (algebraMap ℚ A)
    have hm' : IsUnit (4 : A) := by simpa only [map_ofNat] using hm
    convert hm' using 1
    simp [hS, hR]
    ring
  apply sub_eq_zero.mp
  apply hu.mul_right_cancel
  simpa using hp

theorem formal_ahat_over_square_root_exists_unique :
    ∃! S : PowerSeries A, constantCoeff A S = 2 ∧
      S ^ 2 = (X * (↑(formalAhatUnitOver A)⁻¹ : PowerSeries A)) ^ 2 + 4 := by
  refine ⟨formalAhatSquareRootOver A,
    ⟨formal_ahat_over_square_root_constant A, formal_ahat_over_square_root_equation A⟩, ?_⟩
  intro S hS
  exact normalized_square_root_unique_over_Q_algebra A S (formalAhatSquareRootOver A) _
    hS.1 (formal_ahat_over_square_root_constant A) hS.2 (formal_ahat_over_square_root_equation A)

theorem formal_ahat_over_square_root_recovers_todd :
    (C A (algebraMap ℚ A (1 / 2)) *
      (X * (↑(formalAhatUnitOver A)⁻¹ : PowerSeries A) + formalAhatSquareRootOver A)) *
      (formalAhatUnitOver A : PowerSeries A) = (formalToddUnitOver A : PowerSeries A) := by
  have h := congrArg (PowerSeries.map (algebraMap ℚ A)) (formal_ahat_square_root_recovers_todd ℚ)
  simpa only [map_add, map_mul, PowerSeries.map_C, PowerSeries.map_X,
    formalAhatSquareRootOver, formalAhatUnitOver, formalToddUnitOver, mappedNormalizedSeriesUnit,
    Units.val_inv_eq_inv_val] using h

def formalChiOver (y : A) : PowerSeries A :=
  rescale (1 + y) (formalToddUnitOver A : PowerSeries A) - C A y * X

theorem formal_chi_over_constant (y : A) : constantCoeff A (formalChiOver A y) = 1 := by
  rw [formalChiOver, map_sub, map_mul, constantCoeff_X, mul_zero, sub_zero,
    ← coeff_zero_eq_constantCoeff_apply, coeff_rescale]
  simp [coeff_zero_eq_constantCoeff_apply, formal_todd_over_constant]

def formalChiUnitOver (y : A) : (PowerSeries A)ˣ where
  val := formalChiOver A y
  inv := PowerSeries.invOfUnit (formalChiOver A y) 1
  val_inv := PowerSeries.mul_invOfUnit _ _ (formal_chi_over_constant A y)
  inv_val := PowerSeries.invOfUnit_mul _ _ (formal_chi_over_constant A y)

theorem formal_exponential_over_rescale (a b : A) :
    rescale a (formalExponentialOver A b) = formalExponentialOver A (a * b) := by
  simp only [formalExponentialOver, rescale_rescale, mul_comm]

theorem rescaled_todd_over_quotient (a : A) :
    (1 - formalExponentialOver A (-a)) *
      rescale a (formalToddUnitOver A : PowerSeries A) = C A a * X := by
  have h := congrArg (rescale a) (formal_todd_over_quotient_identity A)
  simpa only [map_mul, map_sub, map_one, formal_exponential_over_rescale,
    mul_neg_one, rescale_X] using h

theorem formal_chi_over_quotient_product (y : A) :
    (1 - formalExponentialOver A (-(1 + y))) * formalChiOver A y =
      X * (1 + C A y * formalExponentialOver A (-(1 + y))) := by
  have h := rescaled_todd_over_quotient A (1 + y)
  simp only [map_add, map_one] at h
  dsimp [formalChiOver]
  linear_combination h

theorem formal_chi_over_recovers_todd (y : A) (hy : IsUnit (1 + y)) :
    ∃ r : A, (1 + y) * r = 1 ∧ r * (1 + y) = 1 ∧
      rescale r (formalChiOver A y) + C A (y * r) * X =
        (formalToddUnitOver A : PowerSeries A) :=
  characteristic_chi_recovery_unit_condition A y hy (formalToddUnitOver A)

theorem formal_chi_over_minus_one : formalChiOver A (-1) = 1 + X := by
  simp [formalChiOver, rescale_zero_apply, formal_todd_over_constant]

def formalToddExponentialDenominatorUnitOver : (PowerSeries A)ˣ :=
  mappedNormalizedSeriesUnit A (formalTodd ℚ - X) (by simp [formal_todd_constant])

def formalLExponentialDenominatorUnitOver : (PowerSeries A)ˣ :=
  mappedNormalizedSeriesUnit A (formalL ℚ - X) (by simp [formal_L_constant])

theorem formal_todd_over_exponential_denominator :
    (formalToddExponentialDenominatorUnitOver A : PowerSeries A) =
      (formalToddUnitOver A : PowerSeries A) - X := by
  change PowerSeries.map (algebraMap ℚ A) (formalTodd ℚ - X) = _
  simp only [map_sub, PowerSeries.map_X, formalToddUnitOver]

theorem formal_L_over_exponential_denominator :
    (formalLExponentialDenominatorUnitOver A : PowerSeries A) =
      (formalLUnitOver A : PowerSeries A) - X := by
  change PowerSeries.map (algebraMap ℚ A) (formalL ℚ - X) = _
  simp only [map_sub, PowerSeries.map_X, formalLUnitOver, mappedNormalizedSeriesUnit]

theorem formal_todd_over_recovers_exponential :
    (formalToddUnitOver A : PowerSeries A) *
      (↑(formalToddExponentialDenominatorUnitOver A)⁻¹ : PowerSeries A) =
        formalExponentialOver A 1 := by
  have h := congrArg (PowerSeries.map (algebraMap ℚ A)) (formal_todd_recovers_exponential ℚ)
  simpa only [map_mul, formal_exponential_over_map, map_one, formalToddUnitOver,
    formalToddExponentialDenominatorUnitOver, mappedNormalizedSeriesUnit,
    Units.val_inv_eq_inv_val] using h

theorem formal_L_over_recovers_exponential :
    ((formalLUnitOver A : PowerSeries A) + X) *
      (↑(formalLExponentialDenominatorUnitOver A)⁻¹ : PowerSeries A) =
        formalExponentialOver A 2 := by
  have h := congrArg (PowerSeries.map (algebraMap ℚ A)) (formal_L_recovers_exponential ℚ)
  simpa only [map_mul, map_add, PowerSeries.map_X, formal_exponential_over_map, map_ofNat,
    formalLUnitOver, formalLExponentialDenominatorUnitOver, mappedNormalizedSeriesUnit,
    Units.val_inv_eq_inv_val] using h

theorem standard_characteristic_units_inverse_reconstruction (y : A) :
    (formalToddUnitOver A)⁻¹⁻¹ = formalToddUnitOver A ∧
    (formalAhatUnitOver A)⁻¹⁻¹ = formalAhatUnitOver A ∧
    (formalLUnitOver A)⁻¹⁻¹ = formalLUnitOver A ∧
    (formalChiUnitOver A y)⁻¹⁻¹ = formalChiUnitOver A y := by
  simp

end
end Sigma
