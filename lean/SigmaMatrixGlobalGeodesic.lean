import SigmaMatrixPathBounds

/-!
This isolated module records the exact spectral length of the canonical SPD
path.  It does not assert that arbitrary paths are no shorter: that requires
the matrix-log differential contraction discussed in final:M3.
-/

namespace Sigma
noncomputable section
open scoped BigOperators Matrix ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

/-- The Frobenius norm of the actual spectral logarithm is exactly the
Euclidean norm of the logarithms of the positive eigenvalues. -/
theorem matrix_spd_log_norm_sq_eigenvalues (A : Matrix n n ℝ) (hA : A.PosDef) :
    ‖matrixSPDLog A hA‖^2 = ∑ i, (Real.log (hA.isHermitian.eigenvalues i))^2 := by
  let U := (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)
  let D := Matrix.diagonal (fun i => Real.log (hA.isHermitian.eigenvalues i))
  have hU : Uᵀ*U = 1 := by
    exact unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary
  have hUh : U*Uᵀ = 1 := by
    exact unitary.coe_mul_star_self hA.isHermitian.eigenvectorUnitary
  have hK : (matrixSPDLog A hA).IsSymm := matrix_spd_log_symmetric A hA
  have hspectral : matrixSPDLog A hA = U*D*Uᵀ := by
    rfl
  rw [matrix_symmetric_frobenius_norm_square _ hK, hspectral]
  rw [show (U*D*Uᵀ)*(U*D*Uᵀ) = U*(D*D)*Uᵀ by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]]
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  simp only [pow_two]

/-- The canonical geodesic has the paper's spectral/Frobenius length formula.
This is a candidate-path upper bound on the intrinsic distance; no minimality
claim for arbitrary paths is made here. -/
theorem matrix_spd_geodesic_length_sq_eigenvalues
    (X Y : Matrix n n ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    (matrixHessianPathLength (matrixSPDGeodesic X Y hX hY))^2 =
      ∑ i, (Real.log ((matrix_relative_spd_positive X Y hX hY).isHermitian.eigenvalues i))^2 := by
  rw [matrix_spd_geodesic_length, matrix_spd_log_norm_sq_eigenvalues]

/-- The canonical higher-rank SPD curve belongs to the paper's actual
finite-piece admissible path class. Together with its exact length formula,
this supplies a genuine competitor (and hence the variational upper bound),
without asserting global minimality. -/
theorem matrix_spd_geodesic_admissible
    (X Y : Matrix n n ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    MatrixPiecewiseAdmissiblePath X Y (matrixSPDGeodesic X Y hX hY) := by
  let K := matrixSPDLog (matrixRelativeSPD X Y hX)
    (matrix_relative_spd_positive X Y hX hY)
  have hc : Continuous (matrixExponentialCurve X K hX) :=
    continuous_iff_continuousAt.mpr (fun s =>
      (matrix_exponential_curve_hasDerivAt X K hX s).continuousAt)
  have hv : Continuous (fun s => matrixExponentialCurveVelocity X K hX s) :=
    continuous_iff_continuousAt.mpr (fun s =>
      (matrix_exponential_velocity_hasDerivAt X K hX s).continuousAt)
  refine ⟨matrix_spd_geodesic_zero X Y hX hY,
    matrix_spd_geodesic_one X Y hX hY, ?_,
    (fun s _ => matrix_spd_geodesic_positive X Y hX hY s), ?_⟩
  · change ContinuousOn (matrixExponentialCurve X K hX) (Set.Icc (0:ℝ) 1)
    exact hc.continuousOn
  · refine ⟨1, (fun j => (j : ℝ)),
      (fun _ s => matrixExponentialCurveVelocity X K hX s), by norm_num,
      by norm_num, by norm_num, ?_, ?_, ?_⟩
    · intro j hj
      have hj' : j = 0 ∨ j = 1 := by omega
      rcases hj' with rfl | rfl <;> norm_num
    · intro j hj
      have hj' : j = 0 := by omega
      subst j
      norm_num
    · intro j hj
      constructor
      · simpa using hv.continuousOn
      · intro s _
        have hj' : j = 0 := by omega
        subst j
        change HasDerivAt (matrixExponentialCurve X K hX)
          (matrixExponentialCurveVelocity X K hX s) s
        exact matrix_exponential_curve_hasDerivAt X K hX s

theorem matrix_spd_geodesic_is_admissible_with_exact_length
    (X Y : Matrix n n ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    MatrixPiecewiseAdmissiblePath X Y (matrixSPDGeodesic X Y hX hY) ∧
      matrixHessianPathLength (matrixSPDGeodesic X Y hX hY) =
        ‖matrixSPDLog (matrixRelativeSPD X Y hX)
          (matrix_relative_spd_positive X Y hX hY)‖ :=
  ⟨matrix_spd_geodesic_admissible X Y hX hY,
    matrix_spd_geodesic_length X Y hX hY⟩

end
end Sigma
