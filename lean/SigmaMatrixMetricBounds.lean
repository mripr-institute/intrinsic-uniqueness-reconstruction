import SigmaMatrixGeodesic
import Mathlib.Algebra.QuadraticDiscriminant

namespace Sigma
noncomputable section
open scoped Matrix Topology ComplexOrder BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

omit [DecidableEq n] in
theorem precisionMetric_add_left (P U V W : Matrix n n ℝ) :
    precisionMetric P (U+V) W = precisionMetric P U W + precisionMetric P V W := by
  simp [precisionMetric, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]

omit [DecidableEq n] in
theorem precisionMetric_add_right (P U V W : Matrix n n ℝ) :
    precisionMetric P U (V+W) = precisionMetric P U V + precisionMetric P U W := by
  simp [precisionMetric, Matrix.mul_add, Matrix.trace_add]

theorem precisionMetric_smul_left (P U V : Matrix n n ℝ) (t : ℝ) :
    precisionMetric P (t • U) V = t * precisionMetric P U V := by
  simp [precisionMetric, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]

theorem precisionMetric_smul_right (P U V : Matrix n n ℝ) (t : ℝ) :
    precisionMetric P U (t • V) = t * precisionMetric P U V := by
  simp [precisionMetric, Matrix.mul_smul, Matrix.trace_smul]

/-- Cauchy--Schwarz for the actual Hessian bilinear form on symmetric
matrix tangent vectors, obtained from positivity of its quadratic form. -/
theorem precisionMetric_cauchy_schwarz_sq (P U V : Matrix n n ℝ)
    (hP : P.PosDef) (hU : U.IsSymm) (hV : V.IsSymm) :
    (precisionMetric P U V)^2 ≤ precisionMetric P U U * precisionMetric P V V := by
  have hh (t : ℝ) : 0 ≤ precisionMetric P V V * (t*t) +
      (2 * precisionMetric P U V)*t + precisionMetric P U U := by
    have hsym : (U+t • V).IsSymm := by
      change (U+t • V)ᵀ = U+t • V
      rw [Matrix.transpose_add, Matrix.transpose_smul, hU, hV]
    have hp := precisionMetric_nonnegative P (U+t • V) hP hsym
    rw [precisionMetric_add_left, precisionMetric_add_right, precisionMetric_add_right,
      precisionMetric_smul_right, precisionMetric_smul_left,
      precisionMetric_smul_left, precisionMetric_smul_right,
      precisionMetric_symmetric P V U] at hp
    nlinarith
  have hd := discrim_le_zero hh
  unfold discrim at hd
  nlinarith

theorem precisionMetric_cauchy_schwarz (P U V : Matrix n n ℝ)
    (hP : P.PosDef) (hU : U.IsSymm) (hV : V.IsSymm) :
    |precisionMetric P U V| ≤
      Real.sqrt (precisionMetric P U U) * Real.sqrt (precisionMetric P V V) := by
  have hsq := precisionMetric_cauchy_schwarz_sq P U V hP hU hV
  have he : (Real.sqrt (precisionMetric P U U) * Real.sqrt (precisionMetric P V V))^2 =
      precisionMetric P U U * precisionMetric P V V := by
    rw [mul_pow, Real.sq_sqrt (precisionMetric_nonnegative P U hP hU),
      Real.sq_sqrt (precisionMetric_nonnegative P V hP hV)]
  have hnn := mul_nonneg (Real.sqrt_nonneg (precisionMetric P U U))
    (Real.sqrt_nonneg (precisionMetric P V V))
  nlinarith [sq_abs (precisionMetric P U V), abs_nonneg (precisionMetric P U V)]

theorem precisionMetric_radial_pairing (X U : Matrix n n ℝ) (hX : X.PosDef) :
    precisionMetric X⁻¹ U X = Matrix.trace (X⁻¹*U) := by
  unfold precisionMetric
  rw [Matrix.mul_assoc (X⁻¹*U) X⁻¹ X,
    Matrix.nonsing_inv_mul X (isUnit_iff_ne_zero.mpr (ne_of_gt hX.det_pos)), Matrix.mul_one]

theorem precisionMetric_radial_square (X : Matrix n n ℝ) (hX : X.PosDef) :
    precisionMetric X⁻¹ X X = Fintype.card n := by
  rw [precisionMetric_radial_pairing X X hX,
    Matrix.nonsing_inv_mul X (isUnit_iff_ne_zero.mpr (ne_of_gt hX.det_pos)), Matrix.trace_one]

/-- The differential of log determinant has metric dual norm sqrt(rank).
This is a native all-rank pointwise bound, not a spectral distance premise. -/
theorem matrix_logdet_velocity_bound (X U : Matrix n n ℝ)
    (hX : X.PosDef) (hU : U.IsSymm) :
    |Matrix.trace (X⁻¹*U)| ≤
      Real.sqrt (Fintype.card n : ℝ) * Real.sqrt (precisionMetric X⁻¹ U U) := by
  have hs : X.IsSymm := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hX.isHermitian.eq
  have h := precisionMetric_cauchy_schwarz X⁻¹ U X hX.inv hU hs
  rw [precisionMetric_radial_pairing X U hX, precisionMetric_radial_square X hX] at h
  simpa only [mul_comm] using h

def matrixCoordinateGradient (X : Matrix n n ℝ) (i : n) : Matrix n n ℝ :=
  X * Matrix.stdBasisMatrix i i 1 * X

theorem matrixCoordinateGradient_symmetric (X : Matrix n n ℝ) (hX : X.IsSymm) (i : n) :
    (matrixCoordinateGradient X i).IsSymm := by
  have hi : (Matrix.stdBasisMatrix i i (1:ℝ))ᵀ = Matrix.stdBasisMatrix i i 1 := by
    ext j k
    simp only [Matrix.transpose_apply, Matrix.stdBasisMatrix, Matrix.of_apply, and_comm]
  change (X * Matrix.stdBasisMatrix i i 1 * X)ᵀ = X * Matrix.stdBasisMatrix i i 1 * X
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hX, hi, Matrix.mul_assoc]

theorem matrix_trace_mul_coordinate (U : Matrix n n ℝ) (i : n) :
    Matrix.trace (U * Matrix.stdBasisMatrix i i 1) = U i i := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.stdBasisMatrix, ite_and]

theorem precisionMetric_coordinate_pairing (X U : Matrix n n ℝ) (hX : X.PosDef) (i : n) :
    precisionMetric X⁻¹ U (matrixCoordinateGradient X i) = U i i := by
  have hXd : IsUnit X.det := isUnit_iff_ne_zero.mpr (ne_of_gt hX.det_pos)
  unfold precisionMetric matrixCoordinateGradient
  calc
    _ = Matrix.trace (X⁻¹*U*(X⁻¹*X)*Matrix.stdBasisMatrix i i 1*X) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (X⁻¹*U*Matrix.stdBasisMatrix i i 1*X) := by
      rw [Matrix.nonsing_inv_mul X hXd, Matrix.mul_one]
    _ = Matrix.trace (X*(X⁻¹*U*Matrix.stdBasisMatrix i i 1)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (U*Matrix.stdBasisMatrix i i 1) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv X hXd, Matrix.one_mul]
    _ = U i i := matrix_trace_mul_coordinate U i

theorem precisionMetric_coordinate_square (X : Matrix n n ℝ) (hX : X.PosDef) (i : n) :
    precisionMetric X⁻¹ (matrixCoordinateGradient X i) (matrixCoordinateGradient X i) =
      (X i i)^2 := by
  rw [precisionMetric_coordinate_pairing X _ hX i]
  simp [matrixCoordinateGradient, Matrix.mul_apply, Matrix.stdBasisMatrix, ite_and, pow_two]

theorem matrix_posDef_diagonal_entry (X : Matrix n n ℝ) (hX : X.PosDef) (i : n) :
    0 < X i i := by
  have hn : (Pi.single i (1:ℝ) : n → ℝ) ≠ 0 := by
    intro he
    have hh := congrFun he i
    simp at hh
  simpa using hX.2 (Pi.single i (1:ℝ)) hn

/-- Every positive diagonal coordinate is 1-Lipschitz infinitesimally in
logarithmic coordinates for the full SPD metric, not only for diagonal paths. -/
theorem matrix_diagonal_log_velocity_bound (X U : Matrix n n ℝ)
    (hX : X.PosDef) (hU : U.IsSymm) (i : n) :
    |U i i / X i i| ≤ Real.sqrt (precisionMetric X⁻¹ U U) := by
  have hxs : X.IsSymm := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hX.isHermitian.eq
  have h := precisionMetric_cauchy_schwarz X⁻¹ U (matrixCoordinateGradient X i)
    hX.inv hU (matrixCoordinateGradient_symmetric X hxs i)
  rw [precisionMetric_coordinate_pairing X U hX i, precisionMetric_coordinate_square X hX i,
    Real.sqrt_sq (matrix_posDef_diagonal_entry X hX i).le] at h
  rw [abs_div, abs_of_pos (matrix_posDef_diagonal_entry X hX i)]
  exact (div_le_iff₀ (matrix_posDef_diagonal_entry X hX i)).mpr h

def matrixEntryCLM (i j : n) : Matrix n n ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => X i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def matrixTransposeCLM : Matrix n n ℝ →L[ℝ] Matrix n n ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.transpose
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem matrix_spd_path_velocity_symmetric
    {γ : ℝ → Matrix n n ℝ} {U : Matrix n n ℝ} {a b s : ℝ}
    (hp : ∀ t ∈ Set.Icc a b, (γ t).PosDef) (hs : s ∈ Set.Ioo a b)
    (hd : HasDerivAt γ U s) : U.IsSymm := by
  have he : (fun t => (γ t)ᵀ) =ᶠ[nhds s] γ := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hp t ⟨ht.1.le, ht.2.le⟩).isHermitian.eq
  have hdt : HasDerivAt (fun t => (γ t)ᵀ) Uᵀ s :=
    (matrixTransposeCLM (n := n)).hasFDerivAt.comp_hasDerivAt s hd
  exact (hdt.congr_of_eventuallyEq he.symm).unique hd

theorem matrix_logdet_path_hasDerivAt {γ : ℝ → Matrix n n ℝ} {U : Matrix n n ℝ} {s : ℝ}
    (hp : (γ s).PosDef) (hd : HasDerivAt γ U s) :
    HasDerivAt (fun t => Real.log (γ t).det) (Matrix.trace ((γ s)⁻¹*U)) s := by
  have hh := ((matrix_det_differentiable (γ s)).hasFDerivAt.comp_hasDerivAt s hd).log
    (ne_of_gt hp.det_pos)
  convert hh using 1
  rw [matrix_det_fderiv (γ s) U (isUnit_iff_ne_zero.mpr (ne_of_gt hp.det_pos))]
  exact (mul_div_cancel_left₀ _ (ne_of_gt hp.det_pos)).symm

theorem matrix_diagonal_log_path_hasDerivAt {γ : ℝ → Matrix n n ℝ}
    {U : Matrix n n ℝ} {s : ℝ} (hp : (γ s).PosDef) (hd : HasDerivAt γ U s) (i : n) :
    HasDerivAt (fun t => Real.log (γ t i i)) (U i i / γ s i i) s :=
  ((matrixEntryCLM i i).hasFDerivAt.comp_hasDerivAt s hd).log
    (ne_of_gt (matrix_posDef_diagonal_entry (γ s) hp i))

end
end Sigma
