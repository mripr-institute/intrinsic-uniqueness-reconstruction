import SigmaMatrixGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Sigma
noncomputable section
open scoped BigOperators Matrix ComplexOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The genuine relative positive-definite matrix X^(-1/2) Y X^(-1/2). -/
def matrixRelativeSPD (X Y : Matrix n n ℝ) (hX : X.PosDef) : Matrix n n ℝ :=
  hX.inv.posSemidef.sqrt*Y*hX.inv.posSemidef.sqrt

theorem matrix_relative_spd_positive (X Y : Matrix n n ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    (matrixRelativeSPD X Y hX).PosDef := by
  have hp := positive_definite_congruence Y hX.inv.posSemidef.sqrt hY
    (sqrt_positive_definite_isUnit X⁻¹ hX.inv)
  rwa [hX.inv.posSemidef.posSemidef_sqrt.isHermitian.eq] at hp

theorem matrix_inverse_sqrt_whitens (X : Matrix n n ℝ) (hX : X.PosDef) :
    matrixCongruence hX.inv.posSemidef.sqrt X = 1 := by
  let Q := hX.inv.posSemidef.sqrt
  have hQ : IsUnit Q := sqrt_positive_definite_isUnit X⁻¹ hX.inv
  have hQd := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have hsq : Q*Q = X⁻¹ := hX.inv.posSemidef.sqrt_mul_self
  have hQQ : Qᵀ = Q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hX.inv.posSemidef.posSemidef_sqrt.isHermitian.eq
  have hXd : IsUnit X.det := isUnit_iff_ne_zero.mpr hX.det_pos.ne'
  have hXX : X = Q⁻¹*Q⁻¹ := by
    rw [← Matrix.mul_inv_rev, hsq, Matrix.nonsing_inv_nonsing_inv X hXd]
  change Q*X*Qᵀ = 1
  rw [hQQ, hXX, ← Matrix.mul_assoc Q Q⁻¹, Matrix.mul_nonsing_inv Q hQd,
    Matrix.one_mul, Matrix.nonsing_inv_mul Q hQd]

theorem matrix_symmetrization_relative (X Y : Matrix n n ℝ)
    (hX : X.PosDef) :
    matrixDivergence X Y+matrixDivergence Y X =
      matrixPotential (matrixRelativeSPD X Y hX)+
        matrixPotential (matrixRelativeSPD X Y hX)⁻¹ := by
  let Q := hX.inv.posSemidef.sqrt
  have hQ : IsUnit Q := sqrt_positive_definite_isUnit X⁻¹ hX.inv
  have hQh : Qᵀ = Q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hX.inv.posSemidef.posSemidef_sqrt.isHermitian.eq
  have hYQ : matrixCongruence Q Y = matrixRelativeSPD X Y hX := by
    change Q*Y*Qᵀ = Q*Y*Q
    rw [hQh]
  rw [← matrixDivergence_congruence X Y Q hQ,
    ← matrixDivergence_congruence Y X Q hQ,
    matrix_inverse_sqrt_whitens X hX, hYQ]
  simp only [matrixDivergence, Matrix.mul_one, inv_one, Matrix.one_mul,
    matrixPotential]
  ring

theorem matrix_trace_inverse_eigenvalues (A : Matrix n n ℝ) (hA : A.PosDef) :
    Matrix.trace A⁻¹ = ∑ i, (hA.isHermitian.eigenvalues i)⁻¹ := by
  let U := (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)
  have hU : U⁻¹ = Star.star U := Matrix.inv_eq_left_inv
    (unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary)
  have hUs : (Star.star U)⁻¹ = U := Matrix.inv_eq_left_inv
    (unitary.coe_mul_star_self hA.isHermitian.eigenvectorUnitary)
  have hs : A = U*Matrix.diagonal hA.isHermitian.eigenvalues*Star.star U := by
    simpa only [RCLike.ofReal_real_eq_id, Function.comp_def, id_eq] using hA.isHermitian.spectral_theorem
  have hdiag : (Matrix.diagonal hA.isHermitian.eigenvalues)⁻¹ =
      Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    have he : (fun i => (hA.isHermitian.eigenvalues i)⁻¹*hA.isHermitian.eigenvalues i) =
        (fun _ : n => (1:ℝ)) := by
      funext i
      exact inv_mul_cancel₀ (hA.eigenvalues_pos i).ne'
    rw [he, Matrix.diagonal_one]
  conv_lhs => rw [hs]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hUs, hU,
    ← Matrix.mul_assoc, Matrix.trace_mul_cycle, unitary.coe_star_mul_self, Matrix.one_mul,
    hdiag, Matrix.trace_diagonal]

theorem positive_eigenvalue_hyperbolic_symmetrization {t : ℝ} (ht : 0 < t) :
    t+t⁻¹-2 = 4*Real.sinh (Real.log t/2)^2 := by
  have hc : 2*Real.cosh (Real.log t) = t+t⁻¹ := by
    rw [Real.cosh_eq, Real.exp_log ht, Real.exp_neg, Real.exp_log ht]
    ring
  have hh := Real.cosh_two_mul (Real.log t/2)
  rw [show 2*(Real.log t/2) = Real.log t by ring, Real.cosh_sq] at hh
  linarith

theorem matrix_potential_symmetrization_spectral (A : Matrix n n ℝ) (hA : A.PosDef) :
    matrixPotential A+matrixPotential A⁻¹ =
      4*∑ i, Real.sinh (Real.log (hA.isHermitian.eigenvalues i)/2)^2 := by
  unfold matrixPotential
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.log_inv,
    matrix_trace_eq_eigenvalue_sum A hA.isHermitian, matrix_trace_inverse_eigenvalues A hA]
  have he : (∑ i, hA.isHermitian.eigenvalues i)+
      (∑ i, (hA.isHermitian.eigenvalues i)⁻¹)-2*Fintype.card n =
      ∑ i, (hA.isHermitian.eigenvalues i+(hA.isHermitian.eigenvalues i)⁻¹-2) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  calc
    _ = (∑ i, hA.isHermitian.eigenvalues i)+
        (∑ i, (hA.isHermitian.eigenvalues i)⁻¹)-2*Fintype.card n := by ring
    _ = _ := he
    _ = ∑ i, 4*Real.sinh (Real.log (hA.isHermitian.eigenvalues i)/2)^2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact positive_eigenvalue_hyperbolic_symmetrization (hA.eigenvalues_pos i)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The exact M3 symmetrization formula, on native SPD matrices and their
actual relative-matrix eigenvalues. -/
theorem matrix_divergence_relative_symmetrization (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    matrixDivergence X Y+matrixDivergence Y X =
      4*∑ i, Real.sinh
        (Real.log ((matrix_relative_spd_positive X Y hX hY).isHermitian.eigenvalues i)/2)^2 := by
  rw [matrix_symmetrization_relative X Y hX]
  exact matrix_potential_symmetrization_spectral _ (matrix_relative_spd_positive X Y hX hY)

end
end Sigma
