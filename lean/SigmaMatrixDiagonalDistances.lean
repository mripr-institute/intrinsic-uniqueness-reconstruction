import SigmaMatrixPathBounds

namespace Sigma
noncomputable section
open scoped Matrix Topology ComplexOrder BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

def matrixDiagonalExpPath (w : n → ℝ) : ℝ → Matrix n n ℝ :=
  matrixExponentialCurve 1 (Matrix.diagonal w) Matrix.PosDef.one

omit [Fintype n] in
theorem matrix_diagonal_symmetric (w : n → ℝ) : (Matrix.diagonal w).IsSymm :=
  Matrix.diagonal_transpose w

theorem matrix_diagonal_exp_path_formula (w : n → ℝ) (s : ℝ) :
    matrixDiagonalExpPath w s = Matrix.diagonal (fun i => Real.exp (s*w i)) := by
  have hs : (Matrix.PosDef.one : (1 : Matrix n n ℝ).PosDef).posSemidef.sqrt = 1 := by
    symm
    apply (Matrix.PosSemidef.one : (1 : Matrix n n ℝ).PosSemidef).eq_sqrt_of_sq_eq
    simp
  unfold matrixDiagonalExpPath matrixExponentialCurve
  rw [hs, Matrix.one_mul, Matrix.mul_one]
  have hd : s • Matrix.diagonal w = Matrix.diagonal (fun i => s*w i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, hij]
  rw [hd, matrix_exp_diagonal_real]

theorem matrix_diagonal_exp_path_admissible (w : n → ℝ) :
    MatrixPiecewiseAdmissiblePath 1 (Matrix.diagonal (fun i => Real.exp (w i)))
      (matrixDiagonalExpPath w) := by
  have hd (s : ℝ) := matrix_exponential_curve_hasDerivAt 1 (Matrix.diagonal w) Matrix.PosDef.one s
  have hv : Continuous (matrixExponentialCurveVelocity 1 (Matrix.diagonal w) Matrix.PosDef.one) :=
    continuous_iff_continuousAt.mpr fun s =>
      (matrix_exponential_velocity_hasDerivAt 1 (Matrix.diagonal w) Matrix.PosDef.one s).continuousAt
  refine ⟨?_, ?_, ?_, ?_, 1, (fun j => (j:ℝ)),
    (fun _ => matrixExponentialCurveVelocity 1 (Matrix.diagonal w) Matrix.PosDef.one),
    by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · rw [matrix_diagonal_exp_path_formula]
    simp
  · rw [matrix_diagonal_exp_path_formula]
    simp
  · exact fun s _ => (hd s).continuousAt.continuousWithinAt
  · intro s _
    exact matrix_exponential_curve_positive 1 (Matrix.diagonal w) Matrix.PosDef.one
      (matrix_diagonal_symmetric w) s
  · intro j hj
    interval_cases j <;> norm_num
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    norm_num
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    exact ⟨hv.continuousOn, fun s _ => hd s⟩

theorem matrix_diagonal_frobenius_norm (w : n → ℝ) :
    ‖Matrix.diagonal w‖ = Real.sqrt (∑ i, (w i)^2) := by
  have he : Matrix.trace (Matrix.diagonal w * Matrix.diagonal w) = ∑ i, (w i)^2 := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    simp only [pow_two]
  rw [← he, ← matrix_symmetric_frobenius_norm_square _ (matrix_diagonal_symmetric w),
    Real.sqrt_sq (norm_nonneg _)]

theorem matrix_diagonal_exp_path_length (w : n → ℝ) :
    matrixHessianPathLength (matrixDiagonalExpPath w) = Real.sqrt (∑ i, (w i)^2) := by
  unfold matrixHessianPathLength matrixDiagonalExpPath
  simp_rw [matrix_exponential_curve_constant_speed 1 (Matrix.diagonal w) Matrix.PosDef.one
    (matrix_diagonal_symmetric w)]
  simp only [intervalIntegral.integral_const, sub_zero, one_smul]
  exact matrix_diagonal_frobenius_norm w

def matrixSingleLogEndpoint (i : n) (r : ℝ) : Matrix n n ℝ :=
  Matrix.diagonal (fun j => Real.exp (if j = i then r else 0))

theorem matrix_single_log_distance (i : n) (r : ℝ) :
    matrixPiecewiseHessianDistance 1 (matrixSingleLogEndpoint i r) = |r| := by
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨matrixDiagonalExpPath (fun j => if j = i then r else 0),
      matrix_diagonal_exp_path_admissible _, ?_⟩
    rw [matrix_diagonal_exp_path_length]
    simp [Real.sqrt_sq_eq_abs]
  · rintro L ⟨γ, hγ, rfl⟩
    have h := matrix_piecewise_diagonal_log_length_bound 1 (matrixSingleLogEndpoint i r) γ hγ i
    simpa [matrixSingleLogEndpoint] using h

def matrixIsotropicLogEndpoint (r : ℝ) : Matrix n n ℝ :=
  Matrix.diagonal (fun _ => Real.exp r)

theorem matrix_isotropic_logdet (r : ℝ) :
    Real.log (matrixIsotropicLogEndpoint (n := n) r).det = (Fintype.card n : ℝ)*r := by
  unfold matrixIsotropicLogEndpoint
  rw [Matrix.det_diagonal]
  have he : (∏ _i : n, Real.exp r) = Real.exp ((Fintype.card n : ℝ)*r) := by
    rw [← Real.exp_sum]
    simp
  rw [he, Real.log_exp]

theorem matrix_isotropic_log_distance [Nonempty n] (r : ℝ) :
    matrixPiecewiseHessianDistance 1 (matrixIsotropicLogEndpoint (n := n) r) =
      Real.sqrt (Fintype.card n : ℝ) * |r| := by
  have hn : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : 0 < Real.sqrt (Fintype.card n : ℝ) := Real.sqrt_pos.mpr hn
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨matrixDiagonalExpPath (fun _ => r), matrix_diagonal_exp_path_admissible _, ?_⟩
    rw [matrix_diagonal_exp_path_length]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Real.sqrt_mul hn.le, Real.sqrt_sq_eq_abs]
  · rintro L ⟨γ, hγ, rfl⟩
    have h := matrix_piecewise_logdet_length_bound 1 (matrixIsotropicLogEndpoint (n := n) r) γ hγ
    rw [matrix_isotropic_logdet, Matrix.det_one, Real.log_one, sub_zero, abs_mul, abs_of_pos hn] at h
    apply (mul_le_mul_left hs).mp
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt hn.le]
    exact h

end
end Sigma
