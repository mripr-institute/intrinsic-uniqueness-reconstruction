import SigmaRealToddPolynomial

namespace Sigma
noncomputable section
open PowerSeries
open scoped BigOperators

variable (A : Type*) [CommRing A] [Algebra ℚ A]

def formalExponentialOver (k : A) : PowerSeries A := rescale k (PowerSeries.exp A)

/-- Base change of the proved rational Todd unit to an arbitrary Q-algebra. -/
def formalToddUnitOver : (PowerSeries A)ˣ where
  val := PowerSeries.map (algebraMap ℚ A) (formalTodd ℚ)
  inv := PowerSeries.map (algebraMap ℚ A) (toddDenominator ℚ)
  val_inv := by
    rw [← map_mul, mul_comm, todd_denominator_mul_todd, map_one]
  inv_val := by
    rw [← map_mul, todd_denominator_mul_todd, map_one]

theorem formal_exponential_over_map (k : ℚ) :
    PowerSeries.map (algebraMap ℚ A) (formalExponential ℚ k) =
      formalExponentialOver A (algebraMap ℚ A k) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_map, formalExponential, formalExponentialOver, coeff_rescale, coeff_exp]
  change algebraMap ℚ A (k ^ n * (1 / (n.factorial : ℚ))) = _
  rw [map_mul, map_pow]

theorem formal_todd_over_constant :
    constantCoeff A (formalToddUnitOver A : PowerSeries A) = 1 := by
  change constantCoeff A (PowerSeries.map (algebraMap ℚ A) (formalTodd ℚ)) = 1
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
    formal_todd_constant, map_one]

/-- The inverse unit is exactly (1-exp(-X))/X, expressed without inverting X. -/
theorem formal_todd_over_denominator :
    (↑(formalToddUnitOver A)⁻¹ : PowerSeries A) * X =
      1 - formalExponentialOver A (-1) := by
  have h := congrArg (PowerSeries.map (algebraMap ℚ A)) (todd_denominator_mul_X ℚ)
  rw [map_mul, map_sub, map_one, formal_exponential_over_map, map_neg, map_one] at h
  simpa only [PowerSeries.map_X, formalToddUnitOver, Units.val_inv_eq_inv_val] using h

theorem formal_todd_over_quotient_identity :
    (1 - formalExponentialOver A (-1)) * (formalToddUnitOver A : PowerSeries A) = X := by
  rw [← formal_todd_over_denominator]
  calc
    (↑(formalToddUnitOver A)⁻¹ : PowerSeries A) * X *
        (formalToddUnitOver A : PowerSeries A) =
        ((↑(formalToddUnitOver A)⁻¹ : PowerSeries A) *
          (formalToddUnitOver A : PowerSeries A)) * X := by ring
    _ = X := by simp

theorem todd_twist_polynomial_eval_algebra (n : ℕ) (k : A) :
    (toddTwistPolynomial n).eval₂ (algebraMap ℚ A) k =
      coeff A n (formalExponentialOver A k *
        (formalToddUnitOver A : PowerSeries A) ^ (n + 1)) := by
  rw [coeff_mul]
  simp only [toddTwistPolynomial, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    formalExponentialOver, coeff_rescale, coeff_exp]
  apply Finset.sum_congr rfl
  intro p hp
  change algebraMap ℚ A (_ / _) * k ^ p.1 =
    k ^ p.1 * algebraMap ℚ A (1 / (p.1.factorial : ℚ)) *
      coeff A p.2 ((PowerSeries.map (algebraMap ℚ A) (formalTodd ℚ)) ^ (n + 1))
  rw [← map_pow, coeff_map, div_eq_mul_inv, map_mul, one_div]
  ring

/-- The complete twist identity survives arbitrary commutative Q-algebra base
change, including algebras with zero divisors. The factorial inverse is rational. -/
theorem formal_twisted_todd_coeff_over_Q_algebra (n : ℕ) (k : A) :
    coeff A n (formalExponentialOver A k *
      (formalToddUnitOver A : PowerSeries A) ^ (n + 1)) =
      algebraMap ℚ A ((n.factorial : ℚ)⁻¹) *
        ∏ j ∈ Finset.range n, (k + (j : A) + 1) := by
  rw [← todd_twist_polynomial_eval_algebra, todd_twist_polynomial_identity]
  simp only [toddBinomialPolynomial, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_finset_prod, Polynomial.eval₂_add, Polynomial.eval₂_X,
    map_add, map_natCast, map_one, Polynomial.eval₂_natCast, Polynomial.eval₂_one]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  ring

theorem formal_todd_tower_over_Q_algebra (n : ℕ) :
    coeff A n ((formalToddUnitOver A : PowerSeries A) ^ (n + 1)) = 1 := by
  change coeff A n ((PowerSeries.map (algebraMap ℚ A) (formalTodd ℚ)) ^ (n + 1)) = 1
  rw [← map_pow, coeff_map, formal_todd_tower, map_one]

omit [Algebra ℚ A] in
theorem power_difference_over_Q_algebra (F G : PowerSeries A)
    (hF : constantCoeff A F = 1) (hG : constantCoeff A G = 1)
    (n k : ℕ) (hlow : ∀ m < n, coeff A m F = coeff A m G) :
    coeff A n (F ^ k - G ^ k) =
      (k : A) * (coeff A n F - coeff A n G) := by
  have hdvd : (X : PowerSeries A) ^ n ∣ F - G := by
    apply X_pow_dvd_iff.mpr
    intro m hm
    simp [hlow m hm]
  obtain ⟨D, hD⟩ := hdvd
  have hc : coeff A n (F - G) = constantCoeff A D := by
    rw [hD]
    simpa using coeff_X_pow_mul D n 0
  let S : PowerSeries A := ∑ i ∈ Finset.range k, F ^ i * G ^ (k - 1 - i)
  have hS : constantCoeff A S = (k : A) := by simp [S, hF, hG]
  calc
    coeff A n (F ^ k - G ^ k) = coeff A n (X ^ n * (D * S)) := by
      congr 1
      rw [← (Commute.all F G).mul_geom_sum₂ k, hD]
      simp only [S]
      ring
    _ = constantCoeff A (D * S) := by simpa using coeff_X_pow_mul (D * S) n 0
    _ = (k : A) * (coeff A n F - coeff A n G) := by
      rw [map_mul, hS, ← hc, map_sub]
      ring

theorem todd_tower_unique_over_Q_algebra (F G : PowerSeries A)
    (hF : constantCoeff A F = 1) (hG : constantCoeff A G = 1)
    (hFtower : ∀ n > 0, coeff A n (F ^ (n + 1)) = 1)
    (hGtower : ∀ n > 0, coeff A n (G ^ (n + 1)) = 1) : F = G := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa using hF.trans hG.symm
    · have hd := power_difference_over_Q_algebra A F G hF hG n (n + 1) ih
      rw [map_sub, hFtower n (Nat.pos_of_ne_zero hn),
        hGtower n (Nat.pos_of_ne_zero hn), sub_self] at hd
      have hk : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have hinv : algebraMap ℚ A (((n + 1 : ℕ) : ℚ)⁻¹) * ((n + 1 : ℕ) : A) = 1 := by
        rw [← map_natCast (algebraMap ℚ A), ← map_mul, inv_mul_cancel₀ hk, map_one]
      apply sub_eq_zero.mp
      calc
        coeff A n F - coeff A n G =
            1 * (coeff A n F - coeff A n G) := (one_mul _).symm
        _ = algebraMap ℚ A (((n + 1 : ℕ) : ℚ)⁻¹) *
            (((n + 1 : ℕ) : A) * (coeff A n F - coeff A n G)) := by rw [← mul_assoc, hinv]
        _ = 0 := by rw [← hd, mul_zero]

theorem todd_tower_iff_exponential_quotient_over_Q_algebra (F : PowerSeries A) :
    (constantCoeff A F = 1 ∧ ∀ n > 0, coeff A n (F ^ (n + 1)) = 1) ↔
      F = (formalToddUnitOver A : PowerSeries A) := by
  constructor
  · rintro ⟨hF, ht⟩
    exact todd_tower_unique_over_Q_algebra A F (formalToddUnitOver A)
      hF (formal_todd_over_constant A) ht (fun n _ => formal_todd_tower_over_Q_algebra A n)
  · rintro rfl
    exact ⟨formal_todd_over_constant A, fun n _ => formal_todd_tower_over_Q_algebra A n⟩

end
end Sigma
