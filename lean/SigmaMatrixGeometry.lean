import SigmaMatrixCalculus

namespace Sigma
noncomputable section
open scoped BigOperators Matrix
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

end
end Sigma
