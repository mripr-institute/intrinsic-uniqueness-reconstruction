import SigmaMatrixDiagonalDistances
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace Sigma
noncomputable section
open scoped Matrix Topology ComplexOrder BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

theorem sinh_strict_superlinear {c x : ℝ} (hc : 1 < c) (hx : 0 < x) :
    c * Real.sinh x < Real.sinh (c*x) := by
  have hconv : StrictConvexOn ℝ (Set.Ici 0) Real.sinh := by
    apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ici _) Real.continuous_sinh.continuousOn
    simpa only [Real.deriv_sinh, interior_Ici] using
      Real.cosh_strictMonoOn.mono (Set.Ioi_subset_Ici_self (a := (0:ℝ)))
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hi : 0 < c⁻¹ := inv_pos.mpr hcpos
  have hi1 : c⁻¹ < 1 := (inv_lt_one₀ hcpos).mpr hc
  have h : Real.sinh ((1-c⁻¹)*0+c⁻¹*(c*x)) <
      (1-c⁻¹)*Real.sinh 0+c⁻¹*Real.sinh (c*x) :=
    hconv.2 (show (0:ℝ) ∈ Set.Ici 0 by norm_num)
    (show c*x ∈ Set.Ici 0 from (mul_pos hcpos hx).le) (ne_of_lt (mul_pos hcpos hx))
    (sub_pos.mpr hi1) hi (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.sinh_zero] at h
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcpos), one_mul] at h
  have hh := (mul_lt_mul_left hcpos).mpr h
  rwa [← mul_assoc c c⁻¹, mul_inv_cancel₀ (ne_of_gt hcpos), one_mul] at hh

theorem matrix_diagonal_exp_inverse (w : n → ℝ) :
    (Matrix.diagonal (fun i => Real.exp (w i)))⁻¹ =
      Matrix.diagonal (fun i => Real.exp (-(w i))) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero]
  · simp [Matrix.diagonal_apply_ne _ hij, hij]

theorem matrix_identity_symmetrization_trace (Y : Matrix n n ℝ) :
    matrixDivergence 1 Y + matrixDivergence Y 1 =
      Matrix.trace Y + Matrix.trace Y⁻¹ - 2*(Fintype.card n : ℝ) := by
  unfold matrixDivergence
  rw [Matrix.mul_one, inv_one, Matrix.one_mul,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.log_inv]
  ring

theorem matrix_diagonal_exp_symmetrization (w : n → ℝ) :
    matrixDivergence 1 (Matrix.diagonal (fun i => Real.exp (w i))) +
      matrixDivergence (Matrix.diagonal (fun i => Real.exp (w i))) 1 =
        4 * ∑ i, Real.sinh (w i / 2)^2 := by
  rw [matrix_identity_symmetrization_trace, matrix_diagonal_exp_inverse,
    Matrix.trace_diagonal, Matrix.trace_diagonal]
  have he (i : n) : Real.exp (w i) + Real.exp (-w i) - 2 = 4*Real.sinh (w i / 2)^2 := by
    have h := positive_eigenvalue_hyperbolic_symmetrization (Real.exp_pos (w i))
    rwa [Real.log_exp, ← Real.exp_neg] at h
  calc
    _ = ∑ i, (Real.exp (w i)+Real.exp (-w i)-2) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      ring
    _ = ∑ i, 4*Real.sinh (w i / 2)^2 := Finset.sum_congr rfl fun i _ => he i
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem matrix_single_log_symmetrization (i : n) (r : ℝ) :
    matrixDivergence 1 (matrixSingleLogEndpoint i r) + matrixDivergence (matrixSingleLogEndpoint i r) 1 =
      4*Real.sinh (r/2)^2 := by
  unfold matrixSingleLogEndpoint
  rw [matrix_diagonal_exp_symmetrization]
  simp [ite_div, apply_ite, ite_pow]

theorem matrix_isotropic_log_symmetrization (r : ℝ) :
    matrixDivergence 1 (matrixIsotropicLogEndpoint (n := n) r) +
      matrixDivergence (matrixIsotropicLogEndpoint (n := n) r) 1 =
        4*(Fintype.card n : ℝ)*Real.sinh (r/2)^2 := by
  unfold matrixIsotropicLogEndpoint
  rw [matrix_diagonal_exp_symmetrization]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Actual SPD matrices of every rank at least two, with equal genuine
piecewise-path distance and unequal symmetrized Bregman divergences. -/
theorem matrix_equal_distance_divergence_counterexample (hn : 2 ≤ Fintype.card n) :
    ∃ X Y Z : Matrix n n ℝ, X.PosDef ∧ Y.PosDef ∧ Z.PosDef ∧
      matrixPiecewiseHessianDistance X Y = matrixPiecewiseHessianDistance X Z ∧
      matrixDivergence X Y + matrixDivergence Y X ≠ matrixDivergence X Z + matrixDivergence Z X := by
  haveI : Nonempty n := Fintype.card_pos_iff.mp (by omega)
  let i : n := Classical.choice inferInstance
  let c : ℝ := Real.sqrt (Fintype.card n : ℝ)
  have hN : (2:ℝ) ≤ Fintype.card n := by exact_mod_cast hn
  have hc2 : c^2 = (Fintype.card n : ℝ) := Real.sq_sqrt (by positivity)
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc1 : 1 < c := by nlinarith
  refine ⟨1, matrixSingleLogEndpoint i c, matrixIsotropicLogEndpoint (n := n) 1,
    Matrix.PosDef.one, Matrix.PosDef.diagonal (fun _ => Real.exp_pos _),
    Matrix.PosDef.diagonal (fun _ => Real.exp_pos _), ?_, ?_⟩
  · rw [matrix_single_log_distance, matrix_isotropic_log_distance, abs_of_nonneg hc0]
    simp [c]
  · rw [matrix_single_log_symmetrization, matrix_isotropic_log_symmetrization]
    have hs := sinh_strict_superlinear hc1 (by norm_num : (0:ℝ) < 1/2)
    rw [show c*((1:ℝ)/2) = c/2 by ring] at hs
    have hh : 0 < Real.sinh ((1:ℝ)/2) := Real.sinh_pos_iff.mpr (by norm_num)
    have hp : 0 ≤ c*Real.sinh ((1:ℝ)/2) := mul_nonneg hc0 hh.le
    have hsquare : (c*Real.sinh ((1:ℝ)/2))^2 < Real.sinh (c/2)^2 := by
      nlinarith
    rw [mul_pow, hc2] at hsquare
    nlinarith

theorem matrix_symmetrized_divergence_not_distance_function (hn : 2 ≤ Fintype.card n) :
    ¬ ∃ F : ℝ → ℝ, ∀ X Y : Matrix n n ℝ, X.PosDef → Y.PosDef →
      matrixDivergence X Y + matrixDivergence Y X = F (matrixPiecewiseHessianDistance X Y) := by
  rintro ⟨F, hF⟩
  obtain ⟨X, Y, Z, hX, hY, hZ, hd, hne⟩ := matrix_equal_distance_divergence_counterexample (n := n) hn
  apply hne
  rw [hF X Y hX hY, hF X Z hX hZ, hd]

end
end Sigma
