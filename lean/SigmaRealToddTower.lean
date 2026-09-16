import SigmaRealTodd

namespace Sigma
noncomputable section
open PowerSeries
open scoped BigOperators

variable (K : Type*) [Field K] [CharZero K]

theorem formal_exponential_zero : formalExponential K 0 = 1 := by
  simp [formalExponential, rescale_zero_apply]

theorem formal_todd_exponential_recovery_product :
    formalExponential K 1 * (formalTodd K - X) = formalTodd K := by
  have hq := formal_todd_quotient_identity K
  have he : formalExponential K 1 * formalExponential K (-1) = 1 := by
    simpa [formalExponential] using
      (PowerSeries.exp_mul_exp_eq_exp_add (1 : K) (-1))
  linear_combination formalExponential K 1 * hq + formalTodd K * he

theorem formal_todd_recovers_exponential :
    formalTodd K * (formalTodd K - X)⁻¹ = formalExponential K 1 := by
  symm
  apply (PowerSeries.eq_mul_inv_iff_mul_eq ?_).2
  · exact formal_todd_exponential_recovery_product K
  · simp [formal_todd_constant]

theorem formal_todd_tower (n : ℕ) : coeff K n (formalTodd K ^ (n + 1)) = 1 := by
  induction n with
  | zero => simpa using formal_todd_constant K
  | succ n ih =>
      have h := formal_twisted_todd_coeff_succ K 0 n
      have hn : ((n + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      simp only [formal_exponential_zero, one_mul, zero_add, div_self hn] at h
      simpa only [one_mul] using h.trans ih

omit [CharZero K] in
theorem characteristic_zero_power_difference (F G : PowerSeries K)
    (hF : constantCoeff K F = 1) (hG : constantCoeff K G = 1)
    (n k : ℕ) (hlow : ∀ m < n, coeff K m F = coeff K m G) :
    coeff K n (F ^ k - G ^ k) =
      (k : K) * (coeff K n F - coeff K n G) := by
  have hdvd : (X : PowerSeries K) ^ n ∣ F - G := by
    apply X_pow_dvd_iff.mpr
    intro m hm
    simp [hlow m hm]
  obtain ⟨D, hD⟩ := hdvd
  have hc : coeff K n (F - G) = constantCoeff K D := by
    rw [hD]
    simpa using coeff_X_pow_mul D n 0
  let S : PowerSeries K := ∑ i ∈ Finset.range k, F ^ i * G ^ (k - 1 - i)
  have hS : constantCoeff K S = (k : K) := by simp [S, hF, hG]
  calc
    coeff K n (F ^ k - G ^ k) = coeff K n (X ^ n * (D * S)) := by
      congr 1
      rw [← (Commute.all F G).mul_geom_sum₂ k, hD]
      simp only [S]
      ring
    _ = constantCoeff K (D * S) := by simpa using coeff_X_pow_mul (D * S) n 0
    _ = (k : K) * (coeff K n F - coeff K n G) := by
      rw [map_mul, hS, ← hc, map_sub]
      ring

theorem formal_todd_tower_unique (F G : PowerSeries K)
    (hF : constantCoeff K F = 1) (hG : constantCoeff K G = 1)
    (hFtower : ∀ n > 0, coeff K n (F ^ (n + 1)) = 1)
    (hGtower : ∀ n > 0, coeff K n (G ^ (n + 1)) = 1) : F = G := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa using hF.trans hG.symm
    · have hd := characteristic_zero_power_difference K F G hF hG n (n + 1) ih
      rw [map_sub, hFtower n (Nat.pos_of_ne_zero hn),
        hGtower n (Nat.pos_of_ne_zero hn), sub_self] at hd
      have hk : ((n + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      exact sub_eq_zero.mp ((mul_eq_zero.mp hd.symm).resolve_left hk)

theorem normalized_todd_tower_iff_exponential_quotient (F : PowerSeries K) :
    (constantCoeff K F = 1 ∧ ∀ n > 0, coeff K n (F ^ (n + 1)) = 1) ↔
      F = formalTodd K := by
  constructor
  · rintro ⟨hF, ht⟩
    exact formal_todd_tower_unique K F (formalTodd K) hF (formal_todd_constant K)
      ht (fun n _ => formal_todd_tower K n)
  · rintro rfl
    exact ⟨formal_todd_constant K, fun n _ => formal_todd_tower K n⟩

theorem all_degree_todd_tower_iff_exponential_quotient (F : PowerSeries K) :
    (∀ n : ℕ, coeff K n (F ^ (n + 1)) = 1) ↔ F = formalTodd K := by
  constructor
  · intro h
    apply (normalized_todd_tower_iff_exponential_quotient K F).1
    exact ⟨by simpa using h 0, fun n _ => h n⟩
  · rintro rfl
    exact formal_todd_tower K

theorem exponential_quotient_todd_exists_unique :
    ∃! F : PowerSeries K, constantCoeff K F = 1 ∧
      ∀ n > 0, coeff K n (F ^ (n + 1)) = 1 := by
  refine ⟨formalTodd K, ⟨formal_todd_constant K, fun n _ => formal_todd_tower K n⟩, ?_⟩
  intro F hF
  exact (normalized_todd_tower_iff_exponential_quotient K F).1 hF

theorem recursive_todd_equals_exponential_quotient :
    towerSolution (fun _ => 1) = formalTodd ℚ := by
  apply (normalized_todd_tower_iff_exponential_quotient ℚ _).1
  exact ⟨towerSolution_constant _, fun n hn => towerSolution_observation _ n hn⟩

theorem formal_todd_omitted_degree (N : ℕ) (hN : 0 < N) :
    ∃ G : PowerSeries K, constantCoeff K G = 1 ∧ G ≠ formalTodd K ∧
      ∀ n > 0, n ≠ N → coeff K n (G ^ (n + 1)) = 1 := by
  obtain ⟨F, G, hF, hG, hne, hFt, hGt⟩ := omitted_todd_degree N hN
  let φ : PowerSeries ℚ →+* PowerSeries K := PowerSeries.map (algebraMap ℚ K)
  have hφ (P : PowerSeries ℚ) (n : ℕ) :
      coeff K n (φ P) = algebraMap ℚ K (coeff ℚ n P) := coeff_map _ _ _
  have hφ0 (P : PowerSeries ℚ) :
      constantCoeff K (φ P) = algebraMap ℚ K (constantCoeff ℚ P) := by
    simpa only [coeff_zero_eq_constantCoeff_apply] using hφ P 0
  have hφinj : Function.Injective φ := by
    intro A B h
    apply PowerSeries.ext
    intro n
    apply (algebraMap ℚ K).injective
    have he := congrArg (coeff K n) h
    simpa only [hφ] using he
  have hf : φ F = formalTodd K := by
    apply (normalized_todd_tower_iff_exponential_quotient K _).1
    refine ⟨by rw [hφ0, hF, map_one], ?_⟩
    intro n hn
    rw [← map_pow, hφ, hFt n hn, map_one]
  refine ⟨φ G, by rw [hφ0, hG, map_one], ?_, ?_⟩
  · intro hg
    exact hne (hφinj (hf.trans hg.symm))
  · intro n hn hnN
    rw [← map_pow, hφ, hGt n hn hnN, map_one]

theorem formal_twisted_todd_coeff_nat (k n : ℕ) :
    coeff K n (formalExponential K (k : K) * formalTodd K ^ (n + 1)) =
      ((n + k).choose n : K) := by
  rw [formal_twisted_todd_coeff]
  have hp : ∀ n : ℕ, (∏ j ∈ Finset.range n, ((k : K) + (j : K) + 1)) =
      ((k + 1).ascFactorial n : K) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.prod_range_succ, ih, Nat.ascFactorial_succ]
        push_cast
        ring
  rw [hp, Nat.ascFactorial_eq_factorial_mul_choose]
  push_cast
  have hf : (n.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [Nat.add_comm k n]
  field_simp

end
end Sigma
