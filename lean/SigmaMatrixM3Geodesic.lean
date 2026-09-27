import SigmaMatrixM3Distance

namespace Sigma
noncomputable section
open scoped Matrix Topology
variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

private theorem matrix_exp_smul_mul (K : Matrix n n ℝ) (a b : ℝ) :
    NormedSpace.exp ℝ (a • K) * NormedSpace.exp ℝ (b • K) =
      NormedSpace.exp ℝ ((a+b) • K) := by
  rw [add_smul]
  exact (NormedSpace.exp_add_of_commute ((Commute.refl K).smul_left a |>.smul_right b)).symm

private theorem matrix_exp_smul_symmetric (K : Matrix n n ℝ) (hK : K.IsSymm) (a : ℝ) :
    (NormedSpace.exp ℝ (a • K)).IsSymm := by
  change (NormedSpace.exp ℝ (a • K))ᵀ = NormedSpace.exp ℝ (a • K)
  rw [← Matrix.exp_transpose, Matrix.transpose_smul, hK]

private theorem matrix_relative_identity (Y : Matrix n n ℝ) :
    matrixRelativeSPD 1 Y Matrix.PosDef.one = Y := by
  have hs : (Matrix.PosDef.one : (1 : Matrix n n ℝ).PosDef).inv.posSemidef.sqrt = 1 := by
    symm
    exact Matrix.PosSemidef.one.eq_sqrt_of_sq_eq _ (by simp)
  simp [matrixRelativeSPD, hs]

/-- The variational Hessian distance along a symmetric matrix exponential is
exactly its constant-speed parameter distance, for every pair of real times. -/
theorem matrix_exponential_metric_geodesic
    (K : Matrix n n ℝ) (hK : K.IsSymm) (s t : ℝ) :
    matrixPiecewiseHessianDistance
      (NormedSpace.exp ℝ (s • K)) (NormedSpace.exp ℝ (t • K)) = |t-s| * ‖K‖ := by
  let C := NormedSpace.exp ℝ ((-s/2) • K)
  have hC : IsUnit C := Matrix.isUnit_exp ℝ _
  have hCs : Cᵀ = C := matrix_exp_smul_symmetric K hK (-s/2)
  have hs : matrixCongruence C (NormedSpace.exp ℝ (s • K)) = 1 := by
    dsimp [matrixCongruence]
    rw [hCs]
    change NormedSpace.exp ℝ ((-s/2) • K) * NormedSpace.exp ℝ (s • K) *
      NormedSpace.exp ℝ ((-s/2) • K) = 1
    rw [matrix_exp_smul_mul, matrix_exp_smul_mul]
    have hz : -s/2+s+(-s/2) = 0 := by ring
    rw [hz, zero_smul, NormedSpace.exp_zero]
  have ht : matrixCongruence C (NormedSpace.exp ℝ (t • K)) =
      NormedSpace.exp ℝ ((t-s) • K) := by
    dsimp [matrixCongruence]
    rw [hCs]
    change NormedSpace.exp ℝ ((-s/2) • K) * NormedSpace.exp ℝ (t • K) *
      NormedSpace.exp ℝ ((-s/2) • K) = _
    rw [matrix_exp_smul_mul, matrix_exp_smul_mul]
    congr 2
    ring
  have hsym : ((t-s) • K).IsSymm := by
    change ((t-s) • K)ᵀ = (t-s) • K
    rw [Matrix.transpose_smul, hK]
  have hpos := matrix_exp_symmetric_positive ((t-s) • K) hsym
  rw [← matrix_congruence_piecewise_distance_eq C hC, hs, ht,
    matrix_piecewise_hessian_distance_eq_spd_log_norm 1 _ Matrix.PosDef.one hpos]
  have hself : IsSelfAdjoint ((t-s) • K) := by
    simpa only [IsSelfAdjoint, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hsym
  rw [matrix_spd_log_eq_cfc_log, matrix_relative_identity,
    CFC.log_exp _ hself, norm_smul, Real.norm_eq_abs]

/-- The paper's canonical curve is a metric geodesic for the actual
piecewise-C¹ variational Hessian distance, including equal endpoints. -/
theorem matrix_spd_geodesic_metric_distance
    (X Y : Matrix n n ℝ) (hX : X.PosDef) (hY : Y.PosDef) (s t : ℝ) :
    matrixPiecewiseHessianDistance (matrixSPDGeodesic X Y hX hY s)
      (matrixSPDGeodesic X Y hX hY t) =
        |t-s| * matrixPiecewiseHessianDistance X Y := by
  let K := matrixSPDLog (matrixRelativeSPD X Y hX)
    (matrix_relative_spd_positive X Y hX hY)
  let Q := hX.posSemidef.sqrt
  have hQ : IsUnit Q := sqrt_positive_definite_isUnit X hX
  have hQt : Qᵀ = Q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hX.posSemidef.posSemidef_sqrt.isHermitian.eq
  have hcurve (r : ℝ) : matrixSPDGeodesic X Y hX hY r =
      matrixCongruence Q (NormedSpace.exp ℝ (r • K)) := by
    simp only [matrixSPDGeodesic, matrixExponentialCurve, matrixCongruence, hQt, K, Q]
  rw [hcurve s, hcurve t, matrix_congruence_piecewise_distance_eq Q hQ,
    matrix_exponential_metric_geodesic K (matrix_spd_log_symmetric _ _),
    matrix_piecewise_hessian_distance_eq_spd_log_norm X Y hX hY]

end
end Sigma
