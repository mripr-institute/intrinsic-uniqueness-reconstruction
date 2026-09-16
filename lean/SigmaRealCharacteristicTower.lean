import SigmaRealCharacteristicUnits

namespace Sigma
noncomputable section
open PowerSeries

variable (K : Type*) [Field K] [CharZero K]

def fieldTowerCoefficient (a : ℕ → K) (n : ℕ) : K :=
  if hn : n = 0 then 1 else
    (a n - coeff K n ((PowerSeries.mk fun j =>
      if _hj : j < n then fieldTowerCoefficient a j else 0) ^ (n + 1))) / (n + 1)
termination_by n

def fieldTowerSolution (a : ℕ → K) : PowerSeries K :=
  PowerSeries.mk (fieldTowerCoefficient K a)

omit [CharZero K] in
theorem field_tower_coefficient_zero (a : ℕ → K) : fieldTowerCoefficient K a 0 = 1 := by
  rw [fieldTowerCoefficient]
  simp

omit [CharZero K] in
theorem field_tower_solution_constant (a : ℕ → K) :
    constantCoeff K (fieldTowerSolution K a) = 1 := by
  simpa [fieldTowerSolution] using field_tower_coefficient_zero K a

theorem field_tower_solution_observation (a : ℕ → K) (n : ℕ) (hn : 0 < n) :
    coeff K n (fieldTowerSolution K a ^ (n + 1)) = a n := by
  let G : PowerSeries K := PowerSeries.mk fun j =>
    if j < n then fieldTowerCoefficient K a j else 0
  have hG : constantCoeff K G = 1 := by simp [G, hn, field_tower_coefficient_zero]
  have hlo : ∀ j < n, coeff K j (fieldTowerSolution K a) = coeff K j G := by
    intro j hj
    simp [fieldTowerSolution, G, hj]
  have hd := characteristic_zero_power_difference K
    (fieldTowerSolution K a) G (field_tower_solution_constant K a) hG n (n + 1) hlo
  have hGn : coeff K n G = 0 := by simp [G]
  rw [map_sub, hGn, sub_zero] at hd
  have hcn : coeff K n (fieldTowerSolution K a) =
      (a n - coeff K n (G ^ (n + 1))) / (n + 1) := by
    simp only [fieldTowerSolution, coeff_mk]
    rw [fieldTowerCoefficient, dif_neg (Nat.ne_of_gt hn)]
    simp only [dite_eq_ite]
  rw [hcn] at hd
  have hden : (n : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast at hd
  have hcancel : ((n : K) + 1) *
      ((a n - coeff K n (G ^ (n + 1))) / ((n : K) + 1)) =
      a n - coeff K n (G ^ (n + 1)) := by field_simp
  rw [hcancel] at hd
  linear_combination hd

theorem normalized_field_tower_observations_injective (F G : PowerSeries K)
    (hF : constantCoeff K F = 1) (hG : constantCoeff K G = 1)
    (hobs : ∀ n > 0, coeff K n (F ^ (n + 1)) = coeff K n (G ^ (n + 1))) : F = G := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa using hF.trans hG.symm
    · have hd := characteristic_zero_power_difference K F G hF hG n (n + 1) ih
      rw [map_sub, hobs n (Nat.pos_of_ne_zero hn), sub_self] at hd
      have hk : ((n + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      exact sub_eq_zero.mp ((mul_eq_zero.mp hd.symm).resolve_left hk)

theorem complete_field_tower_exists_unique (a : ℕ → K) :
    ∃! F : PowerSeries K, constantCoeff K F = 1 ∧
      ∀ n > 0, coeff K n (F ^ (n + 1)) = a n := by
  refine ⟨fieldTowerSolution K a,
    ⟨field_tower_solution_constant K a, fun n hn => field_tower_solution_observation K a n hn⟩,
    ?_⟩
  intro F hF
  apply normalized_field_tower_observations_injective K F (fieldTowerSolution K a)
    hF.1 (field_tower_solution_constant K a)
  intro n hn
  rw [hF.2 n hn, field_tower_solution_observation K a n hn]

def unnormalizedTodd (a : K) : PowerSeries K :=
  C K a * fieldTowerSolution K (fun n => (a ^ (n + 1))⁻¹)

omit [CharZero K] in
theorem unnormalized_todd_constant (a : K) : constantCoeff K (unnormalizedTodd K a) = a := by
  simp [unnormalizedTodd, field_tower_solution_constant]

theorem unnormalized_todd_observation (a : K) (ha : a ≠ 0) (n : ℕ) (hn : 0 < n) :
    coeff K n (unnormalizedTodd K a ^ (n + 1)) = 1 := by
  rw [unnormalizedTodd, mul_pow, ← map_pow, coeff_C_mul, field_tower_solution_observation K _ n hn]
  exact mul_inv_cancel₀ (pow_ne_zero _ ha)

theorem unnormalized_todd_family_exists_unique (a : K) (ha : a ≠ 0) :
    ∃! F : PowerSeries K, constantCoeff K F = a ∧
      ∀ n > 0, coeff K n (F ^ (n + 1)) = 1 := by
  refine ⟨unnormalizedTodd K a,
    ⟨unnormalized_todd_constant K a, fun n hn => unnormalized_todd_observation K a ha n hn⟩,
    ?_⟩
  intro F hF
  have hn (G : PowerSeries K) (hG : constantCoeff K G = a) :
      constantCoeff K (C K a⁻¹ * G) = 1 := by simp [hG, ha]
  have he : C K a⁻¹ * F = C K a⁻¹ * unnormalizedTodd K a := by
    apply normalized_field_tower_observations_injective K _ _ (hn F hF.1)
      (hn _ (unnormalized_todd_constant K a))
    intro n hnp
    rw [mul_pow, mul_pow, ← map_pow, coeff_C_mul, coeff_C_mul,
      hF.2 n hnp, unnormalized_todd_observation K a ha n hnp]
  have hc : C K a⁻¹ ≠ 0 := by
    intro h
    have he := congrArg (constantCoeff K) h
    simp only [constantCoeff_C, map_zero] at he
    exact (inv_ne_zero ha) he
  exact mul_left_cancel₀ hc he

omit [CharZero K] in
theorem unnormalized_todd_parameter_injective : Function.Injective (unnormalizedTodd K) := by
  intro a b h
  have hc := congrArg (constantCoeff K) h
  simpa only [unnormalized_todd_constant] using hc

end
end Sigma
