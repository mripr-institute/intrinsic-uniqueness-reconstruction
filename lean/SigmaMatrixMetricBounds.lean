import SigmaMatrixGeodesic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace Sigma
noncomputable section
open scoped Matrix Topology ComplexOrder BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

private theorem abs_le_abs_sinh (x : ℝ) : |x| ≤ |Real.sinh x| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, abs_of_nonneg (Real.sinh_nonneg_iff.mpr hx)]
    exact Real.self_le_sinh_iff.mpr hx
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hn : 0 ≤ -x := by linarith
    rw [abs_of_nonpos hx', abs_of_nonpos (Real.sinh_nonpos_iff.mpr hx')]
    have h := Real.self_le_sinh_iff.mpr hn
    rw [Real.sinh_neg] at h
    linarith

/-- Scalar divided differences of the logarithm are contractions in the
relative Frobenius metric. This is the pointwise estimate needed for the
higher-rank path-length argument. -/
theorem real_log_divided_difference_bound (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (Real.log y - Real.log x)^2 * (x * y) ≤ (y - x)^2 := by
  let a := Real.log x
  let b := Real.log y
  let u := (b - a) / 2
  let m := (a + b) / 2
  have hxa : Real.exp a = x := Real.exp_log hx
  have hyb : Real.exp b = y := Real.exp_log hy
  have hum : Real.log y - Real.log x = 2 * u := by
    dsimp [u, a, b]
    ring
  have hxy : x * y = (Real.exp m)^2 := by
    rw [← hxa, ← hyb, ← Real.exp_add]
    have hm : a + b = m + m := by dsimp [m]; ring
    rw [hm, Real.exp_add]
    ring
  have hexp_sinh : Real.exp u - Real.exp (-u) = 2 * Real.sinh u := by
    calc
      _ = (Real.cosh u + Real.sinh u) - (Real.cosh u - Real.sinh u) := by
        rw [Real.cosh_add_sinh, Real.cosh_sub_sinh]
      _ = _ := by ring
  have hdiff : y - x = 2 * Real.exp m * Real.sinh u := by
    rw [← hxa, ← hyb]
    have hplus : m + u = b := by dsimp [m, u]; ring
    have hminus : m - u = a := by dsimp [m, u]; ring
    calc
      _ = Real.exp (m + u) - Real.exp (m - u) := by rw [hplus, hminus]
      _ = Real.exp m * (Real.exp u - Real.exp (-u)) := by
        rw [show m - u = m + (-u) by ring]
        rw [Real.exp_add, Real.exp_add]
        ring
      _ = 2 * Real.exp m * Real.sinh u := by rw [hexp_sinh]; ring
  have hu : u^2 ≤ (Real.sinh u)^2 := by
    have h := abs_le_abs_sinh u
    calc
      u^2 = |u|^2 := (sq_abs u).symm
      _ ≤ |Real.sinh u|^2 := by
        simpa only [pow_two] using mul_self_le_mul_self (abs_nonneg u) h
      _ = (Real.sinh u)^2 := sq_abs _
  rw [hum]
  calc
    _ = 4 * (Real.exp m)^2 * u^2 := by rw [hxy]; ring
    _ ≤ 4 * (Real.exp m)^2 * (Real.sinh u)^2 :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = (y - x)^2 := by rw [hdiff]; ring

/-- The continuous divided difference of `log`, with its diagonal value. -/
def realLogDividedDifference (x y : ℝ) : ℝ :=
  if x = y then x⁻¹ else (Real.log y - Real.log x) / (y - x)

/-- In logarithmic spectral coordinates, the derivative multiplier is bounded
by one after the relative-metric normalization. -/
theorem real_log_divided_difference_relative_bound (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) :
    (realLogDividedDifference x y)^2 * (x * y) ≤ 1 := by
  by_cases hxy : x = y
  · subst y
    simp [realLogDividedDifference]
    have hxne : x ≠ 0 := ne_of_gt hx
    field_simp [hxne]
    have hpos : 0 < x^2 := pow_pos hx 2
    rw [div_le_iff₀ hpos]
    nlinarith
  · simp only [realLogDividedDifference, if_neg hxy]
    have h := real_log_divided_difference_bound x y hx hy
    have hden : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    rw [div_pow]
    calc
      ((Real.log y - Real.log x)^2 / (y - x)^2) * (x * y) =
          ((Real.log y - Real.log x)^2 * (x * y)) / (y - x)^2 := by ring
      _ ≤ 1 := (div_le_one₀ (sq_pos_of_ne_zero hden)).2 h

theorem real_log_divided_difference_sq_bound (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) :
    (realLogDividedDifference x y)^2 ≤ 1 / (x * y) := by
  rw [le_div_iff₀ (mul_pos hx hy)]
  exact real_log_divided_difference_relative_bound x y hx hy

omit [DecidableEq n] in
theorem real_log_divided_difference_matrix_coefficient_bound
    (a : n → ℝ) (U : Matrix n n ℝ) (ha : ∀ i, 0 < a i) :
    ∑ i, ∑ j, (realLogDividedDifference (a i) (a j) * U i j)^2 ≤
      ∑ i, ∑ j, (U i j)^2 / (a i * a j) := by
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  rw [mul_pow]
  calc
    _ ≤ (1 / (a i * a j)) * (U i j)^2 :=
      mul_le_mul_of_nonneg_right
        (real_log_divided_difference_sq_bound (a i) (a j) (ha i) (ha j))
        (sq_nonneg (U i j))
    _ = (U i j)^2 / (a i * a j) := by ring

theorem precisionMetric_diagonal_formula (d : n → ℝ) (W : Matrix n n ℝ)
    (hd : ∀ i, d i ≠ 0) (hW : W.IsSymm) :
    precisionMetric (Matrix.diagonal d)⁻¹ W W =
      ∑ i, ∑ j, (W i j)^2 / (d i * d j) := by
  have hinv : (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    have hfun : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : ℝ) := by
      funext i
      exact inv_mul_cancel₀ (hd i)
    rw [hfun, Matrix.diagonal_one]
  have hWcoords : ∀ i j, W j i = W i j := by
    intro i j
    have hs : Wᵀ = W := by simpa [Matrix.IsSymm] using hW
    have hh := congrArg (fun M : Matrix n n ℝ => M i j) hs
    simpa only [Matrix.transpose_apply] using hh
  unfold precisionMetric
  rw [hinv]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
    hW, div_eq_mul_inv]
  simp_rw [hWcoords]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem matrix_log_divided_difference_diagonal_metric_bound
    (a : n → ℝ) (W : Matrix n n ℝ) (ha : ∀ i, 0 < a i) (hW : W.IsSymm) :
    ∑ i, ∑ j, (realLogDividedDifference (a i) (a j) * W i j)^2 ≤
      precisionMetric (Matrix.diagonal a)⁻¹ W W := by
  calc
    _ ≤ ∑ i, ∑ j, (W i j)^2 / (a i * a j) :=
      real_log_divided_difference_matrix_coefficient_bound a W ha
    _ = precisionMetric (Matrix.diagonal a)⁻¹ W W := by
      symm
      apply precisionMetric_diagonal_formula
      · exact fun i => (ha i).ne'
      · exact hW

theorem matrix_log_spectral_directional_bound
    (V A U : Matrix n n ℝ) (a : n → ℝ)
    (hV : IsUnit V) (hVVt : V * Vᵀ = 1)
    (hA : matrixCongruence V (Matrix.diagonal a) = A)
    (ha : ∀ i, 0 < a i) (hU : U.IsSymm) :
    let W := Vᵀ * U * V
    ∑ i, ∑ j, (realLogDividedDifference (a i) (a j) * W i j)^2 ≤
      precisionMetric A⁻¹ U U := by
  dsimp
  let W := Vᵀ * U * V
  have hW : W.IsSymm := by
    change Wᵀ = W
    dsimp [W]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hU]
    simp [Matrix.mul_assoc]
  have hback : matrixCongruence V W = U := by
    unfold matrixCongruence
    dsimp [W]
    calc
      V * (Vᵀ * U * V) * Vᵀ = (V * Vᵀ) * U * (V * Vᵀ) := by
        simp only [Matrix.mul_assoc]
      _ = U := by rw [hVVt]; simp
  have hmetric := hessianMetric_congruence (Matrix.diagonal a) W W V hV
  rw [hA, hback] at hmetric
  calc
    _ ≤ precisionMetric (Matrix.diagonal a)⁻¹ W W :=
      matrix_log_divided_difference_diagonal_metric_bound a W ha hW
    _ = precisionMetric A⁻¹ U U := hmetric.symm

/-- For a native SPD matrix, the spectral divided-difference operator for its
logarithm is contractive in the actual Hessian metric. This is the pointwise
matrix estimate used in the path-length lower bound. -/
theorem matrix_spd_log_spectral_directional_bound
    (A U : Matrix n n ℝ) (hA : A.PosDef) (hU : U.IsSymm) :
    let V := (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)
    let a := hA.isHermitian.eigenvalues
    let W := Vᵀ * U * V
    ∑ i, ∑ j, (realLogDividedDifference (a i) (a j) * W i j)^2 ≤
      precisionMetric A⁻¹ U U := by
  dsimp
  let V := (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)
  let a := hA.isHermitian.eigenvalues
  let W := Vᵀ * U * V
  have hV : IsUnit V := (Matrix.isUnit_iff_isUnit_det V).mpr
    (Matrix.UnitaryGroup.det_isUnit hA.isHermitian.eigenvectorUnitary)
  have hVVt : V * Vᵀ = 1 :=
    unitary.coe_mul_star_self hA.isHermitian.eigenvectorUnitary
  have hAcong : matrixCongruence V (Matrix.diagonal a) = A := by
    unfold matrixCongruence
    have hs := hA.isHermitian.spectral_theorem
    simpa only [RCLike.ofReal_real_eq_id, Function.comp_def, id_eq,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hs.symm
  have ha : ∀ i, 0 < a i := hA.eigenvalues_pos
  exact matrix_log_spectral_directional_bound V A U a hV hVVt hAcong ha hU

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
