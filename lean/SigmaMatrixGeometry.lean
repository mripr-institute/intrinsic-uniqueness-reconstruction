import SigmaMatrixCalculus

namespace Sigma
noncomputable section
open scoped BigOperators Matrix ComplexOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem symmetric_trace_square_eq_zero (U : Matrix n n ℝ) (hU : U.IsSymm) :
    Matrix.trace (U*U) = 0 ↔ U = 0 := by
  rw [symmetric_trace_square U hU]
  constructor
  · intro hz
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) => Finset.sum_nonneg (fun j _ => sq_nonneg (U i j)))).mp hz
    ext i j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => sq_nonneg (U i j))).mp (hi i (Finset.mem_univ i))
    exact pow_eq_zero (hj j (Finset.mem_univ j))
  · rintro rfl
    simp

theorem precisionMetric_eq_zero_iff (P U : Matrix n n ℝ)
    (hP : P.PosDef) (hU : U.IsSymm) : precisionMetric P U U = 0 ↔ U = 0 := by
  let Q := hP.posSemidef.sqrt
  have hsq : Q*Q = P := hP.posSemidef.sqrt_mul_self
  have hQ : Q.IsSymm := by
    ext i j
    simpa using hP.posSemidef.posSemidef_sqrt.isHermitian.apply i j
  have hA : (Q*U*Q).IsSymm := by
    change (Q*U*Q)ᵀ = Q*U*Q
    change Qᵀ = Q at hQ
    change Uᵀ = U at hU
    simp only [Matrix.transpose_mul, hQ, hU, Matrix.mul_assoc]
  have ht : Matrix.trace ((Q*U*Q)*(Q*U*Q)) = precisionMetric P U U := by
    calc
      _ = Matrix.trace (Q*(U*Q*Q*U)*Q) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Q*Q*(U*Q*Q*U)) := Matrix.trace_mul_cycle _ _ _
      _ = Matrix.trace ((Q*Q)*U*(Q*Q)*U) := by simp only [Matrix.mul_assoc]
      _ = precisionMetric P U U := by rw [hsq]; rfl
  rw [← ht, symmetric_trace_square_eq_zero _ hA]
  constructor
  · intro hz
    have hQd := (Matrix.isUnit_iff_isUnit_det Q).mp (sqrt_positive_definite_isUnit P hP)
    have he := congrArg (fun Z : Matrix n n ℝ => Q⁻¹*Z*Q⁻¹) hz
    dsimp only at he
    have hc : Q⁻¹*(Q*U*Q)*Q⁻¹ = U := by
      calc
        _ = (Q⁻¹*Q)*U*(Q*Q⁻¹) := by simp only [Matrix.mul_assoc]
        _ = U := by rw [Matrix.nonsing_inv_mul Q hQd, Matrix.mul_nonsing_inv Q hQd]; simp
    simpa [hc] using he
  · rintro rfl
    simp

theorem precisionMetric_positive (P U : Matrix n n ℝ)
    (hP : P.PosDef) (hU : U.IsSymm) (hU0 : U ≠ 0) : 0 < precisionMetric P U U := by
  exact lt_of_le_of_ne (precisionMetric_nonnegative P U hP hU)
    (fun h => hU0 ((precisionMetric_eq_zero_iff P U hP hU).mp h.symm))

theorem hessianMetric_congruence (X U V C : Matrix n n ℝ) (hC : IsUnit C) :
    precisionMetric (matrixCongruence C X)⁻¹ (matrixCongruence C U) (matrixCongruence C V) =
      precisionMetric X⁻¹ U V := by
  have hCt : IsUnit Cᵀ.det := by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det C).mp hC
  unfold precisionMetric
  rw [Matrix.mul_assoc ((matrixCongruence C X)⁻¹*matrixCongruence C U)
    (matrixCongruence C X)⁻¹ (matrixCongruence C V)]
  change Matrix.trace (((matrixCongruence C X)⁻¹*matrixCongruence C U)*
    ((matrixCongruence C X)⁻¹*matrixCongruence C V)) = _
  rw [matrix_relative_congruence U X C hC, matrix_relative_congruence V X C hC]
  have he : ((Cᵀ)⁻¹*(X⁻¹*U)*Cᵀ)*((Cᵀ)⁻¹*(X⁻¹*V)*Cᵀ) =
      (Cᵀ)⁻¹*((X⁻¹*U)*(X⁻¹*V))*Cᵀ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Cᵀ (Cᵀ)⁻¹, Matrix.mul_nonsing_inv Cᵀ hCt, Matrix.one_mul]
  rw [he, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv Cᵀ hCt, Matrix.one_mul]
  simp only [Matrix.mul_assoc]

theorem hessianMetric_inversion (X U V : Matrix n n ℝ) (hX : IsUnit X.det) :
    precisionMetric (X⁻¹)⁻¹ (-(X⁻¹*U*X⁻¹)) (-(X⁻¹*V*X⁻¹)) =
      precisionMetric X⁻¹ U V := by
  rw [Matrix.nonsing_inv_nonsing_inv X hX]
  unfold precisionMetric
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc X X⁻¹, Matrix.mul_nonsing_inv X hX, Matrix.one_mul,
    ← Matrix.mul_assoc X⁻¹ X, Matrix.nonsing_inv_mul X hX, Matrix.one_mul]
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (U*(X⁻¹*V)) X⁻¹

theorem matrixPotential_block_additivity {m : Type*} [Fintype m] [DecidableEq m]
    (X : Matrix n n ℝ) (Y : Matrix m m ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    matrixPotential (Matrix.fromBlocks X 0 0 Y) = matrixPotential X + matrixPotential Y := by
  have ht : Matrix.trace (Matrix.fromBlocks X 0 0 Y) = Matrix.trace X + Matrix.trace Y := by
    simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]
  unfold matrixPotential
  rw [ht, Matrix.det_fromBlocks_zero₂₁, Real.log_mul (ne_of_gt hX.det_pos) (ne_of_gt hY.det_pos)]
  simp only [Fintype.card_sum, Nat.cast_add]
  ring

theorem matrixPotential_orthogonal_congruence (X Q : Matrix n n ℝ)
    (hQ : Qᵀ*Q = 1) : matrixPotential (Q*X*Qᵀ) = matrixPotential X := by
  have ht : Matrix.trace (Q*X*Qᵀ) = Matrix.trace X := by
    rw [Matrix.trace_mul_cycle, hQ, Matrix.one_mul]
  have hdet := congrArg Matrix.det hQ
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  have hd : (Q*X*Qᵀ).det = X.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    calc
      _ = X.det*(Q.det*Q.det) := by ring
      _ = X.det := by rw [hdet, mul_one]
  simp only [matrixPotential, ht, hd]

/-- A nonnegative, block-additive perturbation which detects the chosen basis. -/
def matrixOffDiagonalPenalty (X : Matrix n n ℝ) : ℝ :=
  ∑ i, ∑ j, if i=j then 0 else (X i j)^2

theorem matrix_off_diagonal_penalty_nonnegative (X : Matrix n n ℝ) :
    0 ≤ matrixOffDiagonalPenalty X := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> positivity

theorem matrix_off_diagonal_penalty_blocks {m : Type*} [Fintype m] [DecidableEq m]
    (X : Matrix n n ℝ) (Y : Matrix m m ℝ) :
    matrixOffDiagonalPenalty (Matrix.fromBlocks X 0 0 Y) =
      matrixOffDiagonalPenalty X + matrixOffDiagonalPenalty Y := by
  simp [matrixOffDiagonalPenalty, Fintype.sum_sum_type, Matrix.fromBlocks]

def matrixBasisDependentLift (X : Matrix n n ℝ) : ℝ :=
  matrixPotential X + matrixOffDiagonalPenalty X

theorem matrix_basis_lift_nonnegative (X : Matrix n n ℝ) (hX : X.PosDef) :
    0 ≤ matrixBasisDependentLift X :=
  add_nonneg (matrixPotential_nonnegative X hX) (matrix_off_diagonal_penalty_nonnegative X)

theorem matrix_basis_lift_seed (t : ℝ) :
    matrixBasisDependentLift (Matrix.diagonal (fun _ : Fin 1 => t)) = SigmaBase.potential t := by
  simp [matrixBasisDependentLift, matrixOffDiagonalPenalty, matrixPotential,
    Matrix.trace, Matrix.diag, Matrix.det_diagonal, SigmaBase.potential]
  ring

theorem matrix_basis_lift_blocks {m : Type*} [Fintype m] [DecidableEq m]
    (X : Matrix n n ℝ) (Y : Matrix m m ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    matrixBasisDependentLift (Matrix.fromBlocks X 0 0 Y) =
      matrixBasisDependentLift X + matrixBasisDependentLift Y := by
  rw [matrixBasisDependentLift, matrixPotential_block_additivity X Y hX hY,
    matrix_off_diagonal_penalty_blocks]
  unfold matrixBasisDependentLift
  ring

/-- Dropping scalar recursion leaves a rank-dependent nonnegative freedom. -/
def matrixRankShiftLift (X : Matrix n n ℝ) : ℝ :=
  matrixPotential X + if Fintype.card n = 1 then 0 else 1

theorem matrix_rank_shift_nonnegative (X : Matrix n n ℝ) (hX : X.PosDef) :
    0 ≤ matrixRankShiftLift X := by
  unfold matrixRankShiftLift
  split_ifs <;> linarith [matrixPotential_nonnegative X hX]

theorem matrix_rank_shift_seed (t : ℝ) :
    matrixRankShiftLift (Matrix.diagonal (fun _ : Fin 1 => t)) = SigmaBase.potential t := by
  simp [matrixRankShiftLift, matrixPotential, Matrix.trace, Matrix.diag,
    Matrix.det_diagonal, SigmaBase.potential]
  ring

theorem matrix_rank_shift_invariant (X Q : Matrix n n ℝ) (hQ : Qᵀ*Q = 1) :
    matrixRankShiftLift (Q*X*Qᵀ) = matrixRankShiftLift X := by
  simp only [matrixRankShiftLift, matrixPotential_orthogonal_congruence X Q hQ]

theorem matrix_rank_shift_recursion_failure :
    matrixRankShiftLift (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0
      (1 : Matrix (Fin 1) (Fin 1) ℝ)) ≠
      matrixRankShiftLift (1 : Matrix (Fin 1) (Fin 1) ℝ) + SigmaBase.potential 1 := by
  have he : Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0
      (1 : Matrix (Fin 1) (Fin 1) ℝ) = 1 := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.one_apply]
  rw [he]
  norm_num [matrixRankShiftLift, matrixPotential, Matrix.trace_one, SigmaBase.potential]

theorem matrix_basis_lift_invariance_failure :
    ∃ X Q : Matrix (Fin 2) (Fin 2) ℝ, X.PosDef ∧ Qᵀ*Q = 1 ∧
      matrixBasisDependentLift (Q*X*Qᵀ) ≠ matrixBasisDependentLift X := by
  let X : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![2,1]
  let Q : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    if i=0 then (if j=0 then 3/5 else -4/5) else (if j=0 then 4/5 else 3/5)
  have hX : X.PosDef := Matrix.PosDef.diagonal (by intro i; fin_cases i <;> norm_num)
  have hQ : Qᵀ*Q = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Q, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  refine ⟨X, Q, hX, hQ, ?_⟩
  have h0 : matrixOffDiagonalPenalty X = 0 := by
    norm_num [matrixOffDiagonalPenalty, X, Fin.sum_univ_two]
  have h1 : matrixOffDiagonalPenalty (Q*X*Qᵀ) = 288/625 := by
    norm_num [matrixOffDiagonalPenalty, Q, X, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.diagonal_apply, Fin.sum_univ_two]
  rw [matrixBasisDependentLift, matrixBasisDependentLift,
    matrixPotential_orthogonal_congruence X Q hQ, h0, h1]
  norm_num

omit [DecidableEq n] in
theorem positive_definite_positive_smul (X : Matrix n n ℝ) (hX : X.PosDef)
    {c : ℝ} (hc : 0 < c) : (c • X).PosDef := by
  refine ⟨?_, ?_⟩
  · change (c • X)ᴴ = c • X
    rw [Matrix.conjTranspose_smul, star_trivial, hX.isHermitian.eq]
  · intro x hx
    rw [Matrix.smul_mulVec_assoc, Matrix.dotProduct_smul]
    exact mul_pos hc (hX.2 x hx)

theorem positive_definite_trace_positive [Nonempty n] (X : Matrix n n ℝ) (hX : X.PosDef) :
    0 < Matrix.trace X := by
  rw [matrix_trace_eq_eigenvalue_sum X hX.isHermitian]
  exact Finset.sum_pos (fun i _ => hX.eigenvalues_pos i) Finset.univ_nonempty

theorem spd_determinant_arithmetic_mean_bound [Nonempty n]
    (X : Matrix n n ℝ) (hX : X.PosDef) :
    X.det ≤ (Matrix.trace X / Fintype.card n)^Fintype.card n := by
  let a : ℝ := Matrix.trace X / Fintype.card n
  have hn : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  have ha : 0 < a := div_pos (positive_definite_trace_positive X hX) hn
  have hY := positive_definite_positive_smul X hX (inv_pos.mpr ha)
  have ht : Matrix.trace (a⁻¹ • X) = Fintype.card n := by
    rw [Matrix.trace_smul]
    change a⁻¹ * Matrix.trace X = Fintype.card n
    dsimp [a]
    field_simp [(positive_definite_trace_positive X hX).ne']
  have hd := spd_determinant_exponential_bound (a⁻¹ • X) hY
  rw [ht, sub_self, Real.exp_zero, Matrix.det_smul, inv_pow] at hd
  have hh := mul_le_mul_of_nonneg_left hd (pow_pos ha (Fintype.card n)).le
  simpa [mul_assoc, (pow_ne_zero (Fintype.card n) ha.ne')] using hh

theorem spd_determinant_arithmetic_mean_equality [Nonempty n]
    (X : Matrix n n ℝ) (hX : X.PosDef) :
    X.det = (Matrix.trace X / Fintype.card n)^Fintype.card n ↔
      X = (Matrix.trace X / Fintype.card n) • (1 : Matrix n n ℝ) := by
  let a : ℝ := Matrix.trace X / Fintype.card n
  have hn : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  have ha : 0 < a := div_pos (positive_definite_trace_positive X hX) hn
  have hY := positive_definite_positive_smul X hX (inv_pos.mpr ha)
  have ht : Matrix.trace (a⁻¹ • X) = Fintype.card n := by
    rw [Matrix.trace_smul]
    change a⁻¹ * Matrix.trace X = Fintype.card n
    dsimp [a]
    field_simp [(positive_definite_trace_positive X hX).ne']
  have he := spd_determinant_exponential_equality (a⁻¹ • X) hY
  rw [ht, sub_self, Real.exp_zero, Matrix.det_smul, inv_pow] at he
  change X.det = a^Fintype.card n ↔ X = a • (1 : Matrix n n ℝ)
  constructor
  · intro hd
    have hy : a⁻¹ • X = 1 := he.mp (by rw [hd]; exact inv_mul_cancel₀ (pow_ne_zero _ ha.ne'))
    have hh := congrArg (fun Y : Matrix n n ℝ => a • Y) hy
    simpa [smul_smul, ha.ne'] using hh
  · intro hx
    rw [hx, Matrix.det_smul, Matrix.det_one, mul_one]

omit [DecidableEq n] in
theorem positive_definite_convex : Convex ℝ {X : Matrix n n ℝ | X.PosDef} := by
  intro X hX Y hY a b ha hb hab
  by_cases ha0 : a=0
  · have hb1 : b=1 := by linarith
    simpa [ha0, hb1] using hY
  by_cases hb0 : b=0
  · have ha1 : a=1 := by linarith
    simpa [hb0, ha1] using hX
  exact (positive_definite_positive_smul X hX (lt_of_le_of_ne ha (Ne.symm ha0))).add
    (positive_definite_positive_smul Y hY (lt_of_le_of_ne hb (Ne.symm hb0)))

theorem matrix_logdet_strictConcave :
    StrictConcaveOn ℝ {X : Matrix n n ℝ | X.PosDef} (fun X => Real.log X.det) := by
  refine ⟨positive_definite_convex, ?_⟩
  intro X hX Y hY hXY a b ha hb hab
  let Z := a • X+b • Y
  have hZ : Z.PosDef := (positive_definite_positive_smul X hX ha).add
    (positive_definite_positive_smul Y hY hb)
  have hXZ : X ≠ Z := by
    intro he
    have hh : b • (X-Y) = 0 := by
      calc
        b • (X-Y) = (a+b) • X-(a • X+b • Y) := by module
        _ = X-(a • X+b • Y) := by rw [hab, one_smul]
        _ = 0 := sub_eq_zero.mpr he
    exact hXY (sub_eq_zero.mp ((smul_eq_zero.mp hh).resolve_left hb.ne'))
  have hpos : 0 < matrixDivergence X Z :=
    lt_of_le_of_ne (matrixDivergence_nonnegative X Z hX hZ)
      (fun hz => hXZ ((matrixDivergence_eq_zero_iff X Z hX hZ).mp hz.symm))
  have hnonneg := matrixDivergence_nonnegative Y Z hY hZ
  have hid : a*matrixDivergence X Z+b*matrixDivergence Y Z =
      Real.log Z.det-a*Real.log X.det-b*Real.log Y.det := by
    rw [← matrix_bregman_formula X Z hX hZ, ← matrix_bregman_formula Y Z hY hZ]
    have ht : a*Matrix.trace ((1-Z⁻¹)*(X-Z))+b*Matrix.trace ((1-Z⁻¹)*(Y-Z))=0 := by
      change a • Matrix.trace ((1-Z⁻¹)*(X-Z))+b • Matrix.trace ((1-Z⁻¹)*(Y-Z))=0
      rw [← Matrix.trace_smul, ← Matrix.trace_smul, ← Matrix.trace_add]
      have he : a • ((1-Z⁻¹)*(X-Z))+b • ((1-Z⁻¹)*(Y-Z))=0 := by
        rw [← Matrix.mul_smul, ← Matrix.mul_smul, ← Matrix.mul_add]
        have hv : a • (X-Z)+b • (Y-Z)=0 := by
          calc
            _ = (a • X+b • Y)-(a+b) • Z := by module
            _ = 0 := by rw [hab, one_smul]; exact sub_self Z
        rw [hv, Matrix.mul_zero]
      rw [he, Matrix.trace_zero]
    have htrace : Matrix.trace Z=a*Matrix.trace X+b*Matrix.trace Y := by
      simp [Z, Matrix.trace_add, Matrix.trace_smul]
    unfold matrixBregman matrixPotential
    rw [htrace]
    linear_combination -ht - (a*Matrix.trace X+b*Matrix.trace Y-Real.log Z.det)*hab
  have hh := add_pos_of_pos_of_nonneg (mul_pos ha hpos) (mul_nonneg hb.le hnonneg)
  rw [hid] at hh
  change a*Real.log X.det+b*Real.log Y.det < Real.log Z.det
  linarith

end
end Sigma
