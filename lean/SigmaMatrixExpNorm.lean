import SigmaMatrixGeodesic

namespace Sigma
noncomputable section
open scoped Matrix ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
set_option maxHeartbeats 1000000

/-- A uniform exponential bound for the Frobenius matrix algebra. -/
theorem matrix_norm_exp_le_exp_norm (A : Matrix n n ℝ) :
    ‖NormedSpace.exp ℝ A‖ ≤ ‖(1 : Matrix n n ℝ)‖ + Real.exp ‖A‖ := by
  have hsM : Summable (fun k : ℕ => ‖((Nat.factorial k : ℝ)⁻¹) • A ^ k‖) :=
    NormedSpace.norm_expSeries_summable' A
  have hsR : Summable (fun k : ℕ => ((Nat.factorial k : ℝ)⁻¹) * ‖A‖ ^ k) := by
    simpa only [smul_eq_mul] using
      (NormedSpace.expSeries_summable' (𝕂 := ℝ) (‖A‖))
  have hterm (k : ℕ) :
      ‖((Nat.factorial (k+1) : ℝ)⁻¹) • A ^ (k+1)‖ ≤
        ((Nat.factorial (k+1) : ℝ)⁻¹) * ‖A‖ ^ (k+1) := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
    exact mul_le_mul_of_nonneg_left (norm_pow_le' A (Nat.succ_pos k))
      (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hsMt : Summable (fun k : ℕ => ‖((Nat.factorial (k+1) : ℝ)⁻¹) • A ^ (k+1)‖) :=
    (summable_nat_add_iff 1).mpr hsM
  have hsRt : Summable (fun k : ℕ => ((Nat.factorial (k+1) : ℝ)⁻¹) * ‖A‖ ^ (k+1)) :=
    (summable_nat_add_iff 1).mpr hsR
  have htail : (∑' k : ℕ, ‖((Nat.factorial (k+1) : ℝ)⁻¹) • A ^ (k+1)‖) ≤
      ∑' k : ℕ, ((Nat.factorial (k+1) : ℝ)⁻¹) * ‖A‖ ^ (k+1) :=
    tsum_le_tsum hterm hsMt hsRt
  have hreal : (∑' k : ℕ, ((Nat.factorial k : ℝ)⁻¹) * ‖A‖ ^ k) =
      Real.exp ‖A‖ := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum]
    simp only [smul_eq_mul]
  calc
    ‖NormedSpace.exp ℝ A‖ = ‖∑' k : ℕ, ((Nat.factorial k : ℝ)⁻¹) • A ^ k‖ := by
      rw [NormedSpace.exp_eq_tsum]
    _ ≤ ∑' k : ℕ, ‖((Nat.factorial k : ℝ)⁻¹) • A ^ k‖ := norm_tsum_le_tsum_norm hsM
    _ = ‖(1 : Matrix n n ℝ)‖ +
        ∑' k : ℕ, ‖((Nat.factorial (k+1) : ℝ)⁻¹) • A ^ (k+1)‖ := by
      rw [tsum_eq_zero_add hsM]
      simp
    _ ≤ ‖(1 : Matrix n n ℝ)‖ +
        ∑' k : ℕ, ((Nat.factorial (k+1) : ℝ)⁻¹) * ‖A‖ ^ (k+1) :=
      add_le_add_left htail _
    _ ≤ ‖(1 : Matrix n n ℝ)‖ + Real.exp ‖A‖ := by
      rw [← hreal, tsum_eq_zero_add hsR]
      simp

end
end Sigma
