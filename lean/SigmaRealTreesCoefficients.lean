import SigmaRealTreesFixedPoint

namespace Sigma
noncomputable section
open PowerSeries

variable (K : Type*) [Field K] [CharZero K]

omit [CharZero K] in
theorem tree_euler_coefficient (F : PowerSeries K) (n : ℕ) :
    coeff K n (X * derivative K F) = (n : K) * coeff K n F := by
  cases n with
  | zero => simp
  | succ n => simp [Nat.add_comm, coeff_derivative, mul_comm]

omit [CharZero K] in
theorem rooted_power_diagonal (n : ℕ) : coeff K n (rootedSeries K ^ n) = 1 := by
  have he : rootedSeries K ^ n = X ^ n * treeExp K (rootedSeries K) ^ n := by
    calc
      rootedSeries K ^ n = (X * treeExp K (rootedSeries K)) ^ n :=
        congrArg (fun F => F ^ n) (rooted_series_fixed_point K)
      _ = X ^ n * treeExp K (rootedSeries K) ^ n := mul_pow _ _ _
  rw [he]
  simpa [tree_exp_constant] using coeff_X_pow_mul (treeExp K (rootedSeries K) ^ n) n 0

theorem rooted_power_differential (k : ℕ) :
    X * (1 - rootedSeries K) * derivative K (rootedSeries K ^ (k + 1)) =
      C K ((k + 1 : ℕ) : K) * rootedSeries K ^ (k + 1) := by
  rw [Derivation.leibniz_pow]
  simp only [Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul, map_natCast]
  have hd := rooted_series_differential K
  simp only [pow_succ]
  linear_combination ((k + 1 : ℕ) : PowerSeries K) * rootedSeries K ^ k * hd

omit [CharZero K] in
theorem rooted_adjacent_power_derivative (k : ℕ) :
    C K ((k + 2 : ℕ) : K) * rootedSeries K * derivative K (rootedSeries K ^ (k + 1)) =
      C K ((k + 1 : ℕ) : K) * derivative K (rootedSeries K ^ (k + 2)) := by
  rw [Derivation.leibniz_pow, Derivation.leibniz_pow]
  simp only [Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega,
    smul_eq_mul, nsmul_eq_mul, map_natCast, pow_succ]
  ring

theorem rooted_power_coefficient_recurrence (n k : ℕ) :
    ((k + 2 : ℕ) : K) * ((n : K) - ((k + 1 : ℕ) : K)) *
        coeff K n (rootedSeries K ^ (k + 1)) =
      (n : K) * ((k + 1 : ℕ) : K) * coeff K n (rootedSeries K ^ (k + 2)) := by
  have hp := rooted_power_differential K k
  have ha := rooted_adjacent_power_derivative K k
  have hh :
      C K ((k + 2 : ℕ) : K) * (X * derivative K (rootedSeries K ^ (k + 1))) -
        C K ((k + 1 : ℕ) : K) * (X * derivative K (rootedSeries K ^ (k + 2))) =
      C K (((k + 2 : ℕ) : K) * ((k + 1 : ℕ) : K)) * rootedSeries K ^ (k + 1) := by
    rw [map_mul]
    linear_combination C K ((k + 2 : ℕ) : K) * hp + X * ha
  have hc := congrArg (coeff K n) hh
  simp only [map_sub, coeff_C_mul, tree_euler_coefficient] at hc
  linear_combination hc

theorem rooted_power_coefficient_step (n k : ℕ) (hk : 0 < k) :
    ((k + 1 : ℕ) : K) * ((n : K) - (k : K)) * coeff K n (rootedSeries K ^ k) =
      (n : K) * (k : K) * coeff K n (rootedSeries K ^ (k + 1)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  exact rooted_power_coefficient_recurrence K n j

/-- The complete Lagrange coefficient formula is derived from the actual fixed
point, using its differential identity and descending powers. -/
theorem rooted_power_coefficient_gap (k d : ℕ) (hk : 0 < k) :
    coeff K (k + d) (rootedSeries K ^ k) =
      (k : K) / ((k + d : ℕ) : K) * ((k + d : ℕ) : K) ^ d / (d.factorial : K) := by
  induction d generalizing k with
  | zero =>
    simp only [Nat.add_zero, rooted_power_diagonal, pow_zero, Nat.factorial_zero, Nat.cast_one,
      mul_one, div_one]
    have hkn : (k : K) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
    exact (div_self hkn).symm
  | succ d ih =>
    have hn : ((k + (d + 1) : ℕ) : K) ≠ 0 := by exact_mod_cast (by omega : k + (d + 1) ≠ 0)
    have hk1 : ((k + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hd1 : ((d + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
    have hf : (d.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
    have hrec := rooted_power_coefficient_step K (k + (d + 1)) k hk
    have hindex : k + (d + 1) = (k + 1) + d := by omega
    have hnext := ih (k + 1) (by omega)
    rw [← hindex] at hnext
    rw [hnext] at hrec
    have hsub : (((k + (d + 1) : ℕ) : K) - (k : K)) = ((d + 1 : ℕ) : K) := by push_cast; ring
    rw [hsub] at hrec
    apply (mul_left_cancel₀ (mul_ne_zero hk1 hd1))
    rw [hrec, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    field_simp only [hn, hk1, hd1, hf]
    ring_nf
    have hd1' : ((1 + d : ℕ) : K) ≠ 0 := by exact_mod_cast (by omega : 1 + d ≠ 0)
    simp only [mul_assoc, mul_inv_cancel₀ hd1', mul_one]

theorem rooted_power_coefficients (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    coeff K n (rootedSeries K ^ k) =
      (k : K) / (n : K) * (n : K) ^ (n - k) / ((n - k).factorial : K) := by
  simpa only [Nat.add_sub_of_le hkn] using rooted_power_coefficient_gap K k (n - k) hk

theorem rooted_series_coefficients (n : ℕ) :
    coeff K (n + 1) (rootedSeries K) =
      ((n + 1 : ℕ) : K) ^ n / ((n + 1).factorial : K) := by
  have h := rooted_power_coefficient_gap K 1 n (by omega)
  rw [pow_one, Nat.add_comm 1 n, Nat.cast_one] at h
  rw [h, Nat.factorial_succ, Nat.cast_mul]
  ring

end
end Sigma
