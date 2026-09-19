import SigmaMatrixSymmetrization
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace Sigma
noncomputable section
open scoped BigOperators Matrix ComplexOrder Topology
variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

theorem matrix_exp_diagonal_real (v : n → ℝ) :
    NormedSpace.exp ℝ (Matrix.diagonal v) = Matrix.diagonal (fun i => Real.exp (v i)) := by
  rw [Matrix.exp_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  rw [Pi.coe_exp, ← Real.exp_eq_exp_ℝ]

/-- The symmetric logarithm obtained by applying the real logarithm to the
actual spectral resolution of a native positive-definite matrix. -/
def matrixSPDLog (A : Matrix n n ℝ) (hA : A.PosDef) : Matrix n n ℝ :=
  (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)*
    Matrix.diagonal (fun i => Real.log (hA.isHermitian.eigenvalues i))*
      Star.star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)

theorem matrix_spd_log_symmetric (A : Matrix n n ℝ) (hA : A.PosDef) :
    (matrixSPDLog A hA).IsSymm := by
  have hh := Matrix.isHermitian_conjTranspose_mul_mul
    (Star.star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ))
    (Matrix.isHermitian_diagonal (fun i => Real.log (hA.isHermitian.eigenvalues i)))
  simpa only [Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, matrixSPDLog] using hh

theorem matrix_exp_spd_log (A : Matrix n n ℝ) (hA : A.PosDef) :
    NormedSpace.exp ℝ (matrixSPDLog A hA) = A := by
  let U := (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)
  have hU : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr
    (Matrix.UnitaryGroup.det_isUnit hA.isHermitian.eigenvectorUnitary)
  have hi : U⁻¹ = Star.star U := Matrix.inv_eq_left_inv
    (unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary)
  change NormedSpace.exp ℝ (U*Matrix.diagonal (fun i => Real.log (hA.isHermitian.eigenvalues i))*
    Star.star U) = A
  rw [← hi, Matrix.exp_conj ℝ _ _ hU, matrix_exp_diagonal_real, hi]
  have he : (fun i => Real.exp (Real.log (hA.isHermitian.eigenvalues i))) =
      hA.isHermitian.eigenvalues := by
    funext i
    exact Real.exp_log (hA.eigenvalues_pos i)
  rw [he]
  simpa only [RCLike.ofReal_real_eq_id, Function.comp_def, id_eq] using hA.isHermitian.spectral_theorem.symm

theorem matrix_exp_symmetric_positive (K : Matrix n n ℝ) (hK : K.IsSymm) :
    (NormedSpace.exp ℝ K).PosDef := by
  have hH : K.IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hK
  let U := (hH.eigenvectorUnitary : Matrix n n ℝ)
  have hU : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr
    (Matrix.UnitaryGroup.det_isUnit hH.eigenvectorUnitary)
  have hi : U⁻¹ = Star.star U := Matrix.inv_eq_left_inv
    (unitary.coe_star_mul_self hH.eigenvectorUnitary)
  have hs : K = U*Matrix.diagonal hH.eigenvalues*Star.star U := by
    simpa only [RCLike.ofReal_real_eq_id, Function.comp_def, id_eq] using hH.spectral_theorem
  rw [hs, ← hi, Matrix.exp_conj ℝ _ _ hU, matrix_exp_diagonal_real]
  have hp := positive_definite_congruence (Matrix.diagonal (fun i => Real.exp (hH.eigenvalues i)))
    (Star.star U) (Matrix.PosDef.diagonal (fun i => Real.exp_pos _))
    (by
      rw [← hi]
      exact (Matrix.isUnit_iff_isUnit_det _).mpr
        (Matrix.isUnit_nonsing_inv_det U ((Matrix.isUnit_iff_isUnit_det U).mp hU)))
  have hstar : (Star.star U)ᴴ = U := Matrix.conjTranspose_conjTranspose U
  rwa [hstar, ← hi] at hp

/-- The explicit affine-invariant exponential curve, with a symmetric tangent
logarithm and the genuine SPD square root at its basepoint. -/
def matrixExponentialCurve (X K : Matrix n n ℝ) (hX : X.PosDef) (s : ℝ) : Matrix n n ℝ :=
  hX.posSemidef.sqrt*NormedSpace.exp ℝ (s • K)*hX.posSemidef.sqrt

theorem matrix_exponential_curve_positive (X K : Matrix n n ℝ)
    (hX : X.PosDef) (hK : K.IsSymm) (s : ℝ) : (matrixExponentialCurve X K hX s).PosDef := by
  have hs : (s • K).IsSymm := by
    change (s • K)ᵀ = s • K
    rw [Matrix.transpose_smul, hK]
  have hp := positive_definite_congruence (NormedSpace.exp ℝ (s • K)) hX.posSemidef.sqrt
    (matrix_exp_symmetric_positive _ hs) (sqrt_positive_definite_isUnit X hX)
  rwa [hX.posSemidef.posSemidef_sqrt.isHermitian.eq] at hp

def matrixExponentialCurveVelocity (X K : Matrix n n ℝ) (hX : X.PosDef) (s : ℝ) : Matrix n n ℝ :=
  hX.posSemidef.sqrt*(NormedSpace.exp ℝ (s • K)*K)*hX.posSemidef.sqrt

def matrixExponentialCurveAcceleration (X K : Matrix n n ℝ) (hX : X.PosDef) (s : ℝ) : Matrix n n ℝ :=
  hX.posSemidef.sqrt*(NormedSpace.exp ℝ (s • K)*K*K)*hX.posSemidef.sqrt

theorem matrix_exponential_curve_hasDerivAt (X K : Matrix n n ℝ) (hX : X.PosDef) (s : ℝ) :
    HasDerivAt (matrixExponentialCurve X K hX) (matrixExponentialCurveVelocity X K hX s) s :=
  ((hasDerivAt_exp_smul_const K s).const_mul hX.posSemidef.sqrt).mul_const
    hX.posSemidef.sqrt

theorem matrix_exponential_velocity_hasDerivAt (X K : Matrix n n ℝ) (hX : X.PosDef) (s : ℝ) :
    HasDerivAt (matrixExponentialCurveVelocity X K hX)
      (matrixExponentialCurveAcceleration X K hX s) s :=
  (((hasDerivAt_exp_smul_const K s).mul_const K).const_mul hX.posSemidef.sqrt).mul_const
    hX.posSemidef.sqrt

theorem matrix_exponential_curve_metric_square (X K : Matrix n n ℝ) (hX : X.PosDef) (s : ℝ) :
    precisionMetric (matrixExponentialCurve X K hX s)⁻¹
      (matrixExponentialCurveVelocity X K hX s) (matrixExponentialCurveVelocity X K hX s) =
        Matrix.trace (K*K) := by
  let Q := hX.posSemidef.sqrt
  let E := NormedSpace.exp ℝ (s • K)
  have hQ : IsUnit Q := sqrt_positive_definite_isUnit X hX
  have hQh : Qᵀ = Q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hX.posSemidef.posSemidef_sqrt.isHermitian.eq
  have hE : IsUnit E.det := (Matrix.isUnit_iff_isUnit_det E).mp (Matrix.isUnit_exp ℝ (s • K))
  change precisionMetric (Q*E*Q)⁻¹ (Q*(E*K)*Q) (Q*(E*K)*Q) = _
  have he := hessianMetric_congruence E (E*K) (E*K) Q hQ
  simp only [matrixCongruence, hQh] at he
  rw [he]
  unfold precisionMetric
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul E hE, Matrix.one_mul]
  rw [Matrix.mul_assoc K E⁻¹ E, Matrix.nonsing_inv_mul E hE, Matrix.mul_one]

theorem matrix_symmetric_frobenius_norm_square (K : Matrix n n ℝ) (hK : K.IsSymm) :
    ‖K‖^2 = Matrix.trace (K*K) := by
  rw [symmetric_trace_square K hK, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun j _ => Real.rpow_nonneg (norm_nonneg _) _)))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]

theorem matrix_exponential_curve_geodesic_equation (X K : Matrix n n ℝ)
    (hX : X.PosDef) (s : ℝ) :
    matrixExponentialCurveAcceleration X K hX s =
      matrixExponentialCurveVelocity X K hX s*(matrixExponentialCurve X K hX s)⁻¹*
        matrixExponentialCurveVelocity X K hX s := by
  let Q := hX.posSemidef.sqrt
  let E := NormedSpace.exp ℝ (s • K)
  have hQd := (Matrix.isUnit_iff_isUnit_det Q).mp (sqrt_positive_definite_isUnit X hX)
  have hEd := (Matrix.isUnit_iff_isUnit_det E).mp (Matrix.isUnit_exp ℝ (s • K))
  change Q*(E*K*K)*Q = (Q*(E*K)*Q)*(Q*E*Q)⁻¹*(Q*(E*K)*Q)
  symm
  calc
    _ = Q*E*K*(Q*Q⁻¹)*E⁻¹*(Q⁻¹*Q)*E*K*Q := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
    _ = Q*E*K*E⁻¹*E*K*Q := by
      rw [Matrix.mul_nonsing_inv Q hQd, Matrix.nonsing_inv_mul Q hQd]
      simp only [Matrix.mul_one]
    _ = Q*E*K*(E⁻¹*E)*K*Q := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.nonsing_inv_mul E hEd]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem matrix_sqrt_inverse (X : Matrix n n ℝ) (hX : X.PosDef) :
    (hX.posSemidef.sqrt)⁻¹ = hX.inv.posSemidef.sqrt := by
  apply hX.posSemidef.posSemidef_sqrt.inv.eq_sqrt_of_sq_eq hX.inv.posSemidef
  rw [pow_two, ← Matrix.mul_inv_rev, hX.posSemidef.sqrt_mul_self]

theorem matrix_relative_spd_reconstruct (X Y : Matrix n n ℝ) (hX : X.PosDef) :
    hX.posSemidef.sqrt*matrixRelativeSPD X Y hX*hX.posSemidef.sqrt = Y := by
  let Q := hX.posSemidef.sqrt
  have hQd := (Matrix.isUnit_iff_isUnit_det Q).mp (sqrt_positive_definite_isUnit X hX)
  rw [matrixRelativeSPD, ← matrix_sqrt_inverse X hX]
  change Q*(Q⁻¹*Y*Q⁻¹)*Q = Y
  calc
    _ = (Q*Q⁻¹)*Y*(Q⁻¹*Q) := by simp only [Matrix.mul_assoc]
    _ = Y := by rw [Matrix.mul_nonsing_inv Q hQd, Matrix.nonsing_inv_mul Q hQd]; simp

def matrixSPDGeodesic (X Y : Matrix n n ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    ℝ → Matrix n n ℝ :=
  matrixExponentialCurve X (matrixSPDLog (matrixRelativeSPD X Y hX)
    (matrix_relative_spd_positive X Y hX hY)) hX

theorem matrix_spd_geodesic_positive (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) (s : ℝ) : (matrixSPDGeodesic X Y hX hY s).PosDef :=
  matrix_exponential_curve_positive X _ hX (matrix_spd_log_symmetric _ _) s

theorem matrix_spd_geodesic_zero (X Y : Matrix n n ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    matrixSPDGeodesic X Y hX hY 0 = X := by
  simp only [matrixSPDGeodesic, matrixExponentialCurve, zero_smul, NormedSpace.exp_zero,
    Matrix.mul_one, hX.posSemidef.sqrt_mul_self]

theorem matrix_spd_geodesic_one (X Y : Matrix n n ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    matrixSPDGeodesic X Y hX hY 1 = Y := by
  simp only [matrixSPDGeodesic, matrixExponentialCurve, one_smul, matrix_exp_spd_log]
  exact matrix_relative_spd_reconstruct X Y hX

/-- Actual Hessian speed, using the native derivative of a matrix-valued path. -/
def matrixHessianSpeed (γ : ℝ → Matrix n n ℝ) (s : ℝ) : ℝ :=
  Real.sqrt (precisionMetric (γ s)⁻¹ (deriv γ s) (deriv γ s))

def matrixHessianPathLength (γ : ℝ → Matrix n n ℝ) : ℝ :=
  ∫ s : ℝ in (0:ℝ)..1, matrixHessianSpeed γ s

theorem matrix_exponential_curve_constant_speed (X K : Matrix n n ℝ)
    (hX : X.PosDef) (hK : K.IsSymm) (s : ℝ) :
    matrixHessianSpeed (matrixExponentialCurve X K hX) s = ‖K‖ := by
  rw [matrixHessianSpeed, (matrix_exponential_curve_hasDerivAt X K hX s).deriv,
    matrix_exponential_curve_metric_square X K hX s,
    ← matrix_symmetric_frobenius_norm_square K hK, Real.sqrt_sq (norm_nonneg K)]

theorem matrix_spd_geodesic_length (X Y : Matrix n n ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    matrixHessianPathLength (matrixSPDGeodesic X Y hX hY) =
      ‖matrixSPDLog (matrixRelativeSPD X Y hX) (matrix_relative_spd_positive X Y hX hY)‖ := by
  unfold matrixHessianPathLength matrixSPDGeodesic
  simp_rw [matrix_exponential_curve_constant_speed X _ hX (matrix_spd_log_symmetric _ _)]
  simp

theorem matrix_exponential_curve_deriv (X K : Matrix n n ℝ) (hX : X.PosDef) :
    deriv (matrixExponentialCurve X K hX) = matrixExponentialCurveVelocity X K hX := by
  funext s
  exact (matrix_exponential_curve_hasDerivAt X K hX s).deriv

theorem matrix_exponential_curve_continuous_deriv (X K : Matrix n n ℝ) (hX : X.PosDef) :
    Continuous (deriv (matrixExponentialCurve X K hX)) := by
  rw [matrix_exponential_curve_deriv]
  exact continuous_iff_continuousAt.mpr fun s =>
    (matrix_exponential_velocity_hasDerivAt X K hX s).continuousAt

/-- The geodesic equation expressed with native first and second derivatives,
not merely with names for the proposed velocity and acceleration. -/
theorem matrix_exponential_curve_native_geodesic_equation
    (X K : Matrix n n ℝ) (hX : X.PosDef) (s : ℝ) :
    deriv (deriv (matrixExponentialCurve X K hX)) s =
      deriv (matrixExponentialCurve X K hX) s * (matrixExponentialCurve X K hX s)⁻¹ *
        deriv (matrixExponentialCurve X K hX) s := by
  rw [matrix_exponential_curve_deriv,
    (matrix_exponential_velocity_hasDerivAt X K hX s).deriv]
  exact matrix_exponential_curve_geodesic_equation X K hX s

end
end Sigma
