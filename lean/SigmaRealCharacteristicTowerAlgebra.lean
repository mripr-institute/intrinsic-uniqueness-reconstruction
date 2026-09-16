import SigmaRealCharacteristicTower
import SigmaRealCharacteristicBaseChange

namespace Sigma
noncomputable section
open PowerSeries

variable (A : Type*) [CommRing A] [Algebra ℚ A]

def algebraTowerCoefficient (a : ℕ → A) (n : ℕ) : A :=
  if _hn : n = 0 then 1 else
    algebraMap ℚ A (((n + 1 : ℕ) : ℚ)⁻¹) *
      (a n - coeff A n ((PowerSeries.mk fun j =>
        if _hj : j < n then algebraTowerCoefficient a j else 0) ^ (n + 1)))
termination_by n

def algebraTowerSolution (a : ℕ → A) : PowerSeries A :=
  PowerSeries.mk (algebraTowerCoefficient A a)

theorem algebra_tower_coefficient_zero (a : ℕ → A) : algebraTowerCoefficient A a 0 = 1 := by
  rw [algebraTowerCoefficient]
  simp

theorem algebra_tower_solution_constant (a : ℕ → A) :
    constantCoeff A (algebraTowerSolution A a) = 1 := by
  simpa [algebraTowerSolution] using algebra_tower_coefficient_zero A a

theorem rational_successor_inverse (n : ℕ) :
    ((n + 1 : ℕ) : A) * algebraMap ℚ A (((n + 1 : ℕ) : ℚ)⁻¹) = 1 := by
  have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [← map_natCast (algebraMap ℚ A), ← map_mul, mul_inv_cancel₀ hn, map_one]

theorem algebra_tower_solution_observation (a : ℕ → A) (n : ℕ) (hn : 0 < n) :
    coeff A n (algebraTowerSolution A a ^ (n + 1)) = a n := by
  let G : PowerSeries A := PowerSeries.mk fun j =>
    if j < n then algebraTowerCoefficient A a j else 0
  have hG : constantCoeff A G = 1 := by simp [G, hn, algebra_tower_coefficient_zero]
  have hlo : ∀ j < n, coeff A j (algebraTowerSolution A a) = coeff A j G := by
    intro j hj
    simp [algebraTowerSolution, G, hj]
  have hd := power_difference_over_Q_algebra A
    (algebraTowerSolution A a) G (algebra_tower_solution_constant A a) hG n (n + 1) hlo
  have hGn : coeff A n G = 0 := by simp [G]
  rw [map_sub, hGn, sub_zero] at hd
  have hcn : coeff A n (algebraTowerSolution A a) =
      algebraMap ℚ A (((n + 1 : ℕ) : ℚ)⁻¹) * (a n - coeff A n (G ^ (n + 1))) := by
    simp only [algebraTowerSolution, coeff_mk]
    rw [algebraTowerCoefficient, dif_neg (Nat.ne_of_gt hn)]
    simp only [dite_eq_ite]
  rw [hcn, ← mul_assoc, rational_successor_inverse, one_mul] at hd
  linear_combination hd

theorem normalized_algebra_tower_observations_injective (F G : PowerSeries A)
    (hF : constantCoeff A F = 1) (hG : constantCoeff A G = 1)
    (hobs : ∀ n > 0, coeff A n (F ^ (n + 1)) = coeff A n (G ^ (n + 1))) : F = G := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa using hF.trans hG.symm
    · have hd := power_difference_over_Q_algebra A F G hF hG n (n + 1) ih
      rw [map_sub, hobs n (Nat.pos_of_ne_zero hn), sub_self] at hd
      have he := congrArg (algebraMap ℚ A (((n + 1 : ℕ) : ℚ)⁻¹) * ·) hd.symm
      have hi : algebraMap ℚ A (((n + 1 : ℕ) : ℚ)⁻¹) * ((n + 1 : ℕ) : A) = 1 :=
        (mul_comm _ _).trans (rational_successor_inverse A n)
      dsimp only at he
      rw [← mul_assoc, hi, one_mul, mul_zero] at he
      exact sub_eq_zero.mp he

theorem complete_algebra_tower_exists_unique (a : ℕ → A) :
    ∃! F : PowerSeries A, constantCoeff A F = 1 ∧
      ∀ n > 0, coeff A n (F ^ (n + 1)) = a n := by
  refine ⟨algebraTowerSolution A a,
    ⟨algebra_tower_solution_constant A a, fun n hn => algebra_tower_solution_observation A a n hn⟩,
    ?_⟩
  intro F hF
  apply normalized_algebra_tower_observations_injective A F (algebraTowerSolution A a)
    hF.1 (algebra_tower_solution_constant A a)
  intro n hn
  rw [hF.2 n hn, algebra_tower_solution_observation A _ n hn]

def unnormalizedToddOver (a : Aˣ) : PowerSeries A :=
  C A (a : A) * algebraTowerSolution A (fun n => (↑a⁻¹ : A) ^ (n + 1))

theorem unnormalized_todd_over_constant (a : Aˣ) :
    constantCoeff A (unnormalizedToddOver A a) = (a : A) := by
  simp [unnormalizedToddOver, algebra_tower_solution_constant]

theorem unnormalized_todd_over_observation (a : Aˣ) (n : ℕ) (hn : 0 < n) :
    coeff A n (unnormalizedToddOver A a ^ (n + 1)) = 1 := by
  rw [unnormalizedToddOver, mul_pow, ← map_pow, coeff_C_mul,
    algebra_tower_solution_observation A _ n hn, ← mul_pow, Units.mul_inv, one_pow]

theorem unnormalized_todd_family_over_Q_algebra_exists_unique (a : Aˣ) :
    ∃! F : PowerSeries A, constantCoeff A F = (a : A) ∧
      ∀ n > 0, coeff A n (F ^ (n + 1)) = 1 := by
  refine ⟨unnormalizedToddOver A a,
    ⟨unnormalized_todd_over_constant A a, fun n hn => unnormalized_todd_over_observation A a n hn⟩,
    ?_⟩
  intro F hF
  have hn (G : PowerSeries A) (hG : constantCoeff A G = (a : A)) :
      constantCoeff A (C A (↑a⁻¹ : A) * G) = 1 := by simp [hG]
  have he : C A (↑a⁻¹ : A) * F = C A (↑a⁻¹ : A) * unnormalizedToddOver A a := by
    apply normalized_algebra_tower_observations_injective A _ _ (hn F hF.1)
      (hn _ (unnormalized_todd_over_constant A a))
    intro n hnp
    rw [mul_pow, mul_pow, ← map_pow, coeff_C_mul, coeff_C_mul,
      hF.2 n hnp, unnormalized_todd_over_observation A a n hnp]
  have hh := congrArg (C A (a : A) * ·) he
  simpa only [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul] using hh

theorem unnormalized_todd_over_parameter_injective : Function.Injective (unnormalizedToddOver A) := by
  intro a b h
  apply Units.ext
  have hc := congrArg (constantCoeff A) h
  simpa only [unnormalized_todd_over_constant] using hc

end
end Sigma
