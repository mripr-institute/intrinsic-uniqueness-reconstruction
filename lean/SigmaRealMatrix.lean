import SigmaPresentations
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

namespace Sigma
noncomputable section
open scoped BigOperators ComplexOrder Matrix
set_option maxHeartbeats 800000

variable {n : Type*} [Fintype n] [DecidableEq n]

def matrixPotential (X : Matrix n n ℝ) : ℝ :=
  Matrix.trace X - Real.log X.det - Fintype.card n

theorem matrix_trace_eq_eigenvalue_sum (X : Matrix n n ℝ) (hX : X.IsHermitian) :
    Matrix.trace X = ∑ i, hX.eigenvalues i := by
  conv_lhs => rw [hX.spectral_theorem]
  rw [Matrix.trace_mul_cycle, unitary.coe_star_mul_self, Matrix.one_mul]
  simp [Matrix.trace_diagonal]

theorem matrixPotential_spectral (X : Matrix n n ℝ) (hX : X.PosDef) :
    matrixPotential X = ∑ i, SigmaBase.potential (hX.1.eigenvalues i) := by
  unfold matrixPotential
  rw [matrix_trace_eq_eigenvalue_sum X hX.1, hX.1.det_eq_prod_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Real.log_prod Finset.univ _ (fun i _ => ne_of_gt (hX.eigenvalues_pos i))]
  simp only [SigmaBase.potential, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

theorem matrixPotential_nonnegative (X : Matrix n n ℝ) (hX : X.PosDef) :
    0 ≤ matrixPotential X := by
  rw [matrixPotential_spectral X hX]
  apply Finset.sum_nonneg
  intro i hi
  have h := Real.log_le_sub_one_of_pos (hX.eigenvalues_pos i)
  unfold SigmaBase.potential
  linarith

theorem matrixPotential_eq_zero_iff (X : Matrix n n ℝ) (hX : X.PosDef) :
    matrixPotential X = 0 ↔ X = 1 := by
  constructor
  · intro h
    have hz : ∀ i, SigmaBase.potential (hX.1.eigenvalues i) = 0 := by
      intro i
      have hh := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ Finset.univ) =>
          show 0 ≤ SigmaBase.potential (hX.1.eigenvalues j) by
            have hj := Real.log_le_sub_one_of_pos (hX.eigenvalues_pos j)
            unfold SigmaBase.potential
            linarith)).mp ((matrixPotential_spectral X hX).symm.trans h)
      exact hh i (Finset.mem_univ _)
    have he : hX.1.eigenvalues = fun _ => 1 := by
      funext i
      by_contra hi
      have hh := Real.log_lt_sub_one_of_pos (hX.eigenvalues_pos i) hi
      have hz' := hz i
      unfold SigmaBase.potential at hz'
      linarith
    rw [hX.1.spectral_theorem, he]
    simp
  · rintro rfl
    simp [matrixPotential]

theorem spd_determinant_exponential_bound (X : Matrix n n ℝ) (hX : X.PosDef) :
    X.det ≤ Real.exp (Matrix.trace X - Fintype.card n) := by
  have h := matrixPotential_nonnegative X hX
  have hd := hX.det_pos
  have hlog : Real.log X.det ≤ Matrix.trace X - Fintype.card n := by
    unfold matrixPotential at h
    linarith
  simpa [Real.exp_log hd] using Real.exp_le_exp.mpr hlog

theorem spd_determinant_exponential_equality (X : Matrix n n ℝ) (hX : X.PosDef) :
    X.det = Real.exp (Matrix.trace X - Fintype.card n) ↔ X = 1 := by
  rw [← matrixPotential_eq_zero_iff X hX]
  constructor
  · intro h
    have hh := congrArg Real.log h
    rw [Real.log_exp] at hh
    unfold matrixPotential
    linarith
  · intro h
    have hh : Real.log X.det = Matrix.trace X - Fintype.card n := by
      unfold matrixPotential at h
      linarith
    simpa [Real.exp_log hX.det_pos] using congrArg Real.exp hh

/-- A zero-dimensional extension is included only for clean scalar-block recursion.
The positive-dimensional family has the same seed and recursion as M1. -/
theorem spd_scalar_block_lift_unique
    (F : (k : ℕ) → Matrix (Fin k) (Fin k) ℝ → ℝ)
    (hzero : F 0 0 = 0)
    (hrec : ∀ k (d : Fin k → ℝ), (∀ i, 0 < d i) → ∀ t > 0,
      F (k + 1) (Matrix.diagonal (Fin.cons t d)) =
        SigmaBase.potential t + F k (Matrix.diagonal d))
    (hinv : ∀ k (X : Matrix (Fin k) (Fin k) ℝ), X.PosDef →
      ∀ Q : Matrix.unitaryGroup (Fin k) ℝ,
      F k ((Q : Matrix _ _ _) * X * star (Q : Matrix _ _ _)) = F k X)
    (k : ℕ) (X : Matrix (Fin k) (Fin k) ℝ) (hX : X.PosDef) :
    F k X = matrixPotential X := by
  have hdiag : ∀ k (d : Fin k → ℝ), (∀ i, 0 < d i) →
      F k (Matrix.diagonal d) = ∑ i, SigmaBase.potential (d i) := by
    intro k
    induction k with
    | zero =>
      intro d hd
      have he : Matrix.diagonal d = 0 := Subsingleton.elim _ _
      simp [he, hzero]
    | succ k ih =>
      intro d hd
      have hh := hrec k (Fin.tail d) (fun i => hd i.succ) (d 0) (hd 0)
      rw [Fin.cons_self_tail, ih (Fin.tail d) (fun i => hd i.succ)] at hh
      simpa [Fin.sum_univ_succ, Fin.tail] using hh
  rw [matrixPotential_spectral X hX]
  have hs := hX.1.spectral_theorem
  have he : (RCLike.ofReal ∘ hX.1.eigenvalues : Fin k → ℝ) = hX.1.eigenvalues := by
    funext i
    simp
  rw [he] at hs
  calc
    F k X = F k ((hX.1.eigenvectorUnitary : Matrix _ _ _) *
      Matrix.diagonal hX.1.eigenvalues * star (hX.1.eigenvectorUnitary : Matrix _ _ _)) :=
      congrArg (F k) hs
    _ = F k (Matrix.diagonal hX.1.eigenvalues) :=
      hinv k _ (Matrix.PosDef.diagonal hX.eigenvalues_pos) hX.1.eigenvectorUnitary
    _ = ∑ i, SigmaBase.potential (hX.1.eigenvalues i) :=
      hdiag k hX.1.eigenvalues hX.eigenvalues_pos

/-- Exact positive-rank interface of M1: no zero-dimensional value is assumed.
Here F k is the family member in rank k+1. -/
theorem spd_positive_rank_lift_unique
    (F : (k : ℕ) → Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ → ℝ)
    (hseed : ∀ t > 0,
      F 0 (Matrix.diagonal (fun _ : Fin 1 => t)) = SigmaBase.potential t)
    (hrec : ∀ k (d : Fin (k + 1) → ℝ), (∀ i, 0 < d i) → ∀ t > 0,
      F (k + 1) (Matrix.diagonal (Fin.cons t d)) =
        SigmaBase.potential t + F k (Matrix.diagonal d))
    (hinv : ∀ k (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ), X.PosDef →
      ∀ Q : Matrix.unitaryGroup (Fin (k + 1)) ℝ,
      F k ((Q : Matrix _ _ _) * X * star (Q : Matrix _ _ _)) = F k X)
    (k : ℕ) (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (hX : X.PosDef) :
    F k X = matrixPotential X := by
  let G : (m : ℕ) → Matrix (Fin m) (Fin m) ℝ → ℝ
    | 0, _ => 0
    | m + 1, A => F m A
  have hGrec : ∀ m (d : Fin m → ℝ), (∀ i, 0 < d i) → ∀ t > 0,
      G (m + 1) (Matrix.diagonal (Fin.cons t d)) =
        SigmaBase.potential t + G m (Matrix.diagonal d) := by
    intro m d hd t ht
    cases m with
    | zero =>
      have he : Fin.cons t d = (fun _ : Fin 1 => t) := by
        funext i
        fin_cases i
        rfl
      simpa [G, he] using hseed t ht
    | succ m => exact hrec m d hd t ht
  have hGinv : ∀ m (A : Matrix (Fin m) (Fin m) ℝ), A.PosDef →
      ∀ Q : Matrix.unitaryGroup (Fin m) ℝ,
      G m ((Q : Matrix _ _ _) * A * star (Q : Matrix _ _ _)) = G m A := by
    intro m A hA Q
    cases m with
    | zero => rfl
    | succ m => exact hinv m A hA Q
  exact spd_scalar_block_lift_unique G rfl hGrec hGinv (k + 1) X hX

def matrixDivergence (X Y : Matrix n n ℝ) : ℝ :=
  Matrix.trace (Y⁻¹ * X) - Real.log (Y⁻¹ * X).det - Fintype.card n

def matrixBregman (X Y : Matrix n n ℝ) : ℝ :=
  matrixPotential X - matrixPotential Y - Matrix.trace ((1 - Y⁻¹) * (X - Y))

theorem matrix_bregman_formula (X Y : Matrix n n ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    matrixBregman X Y = matrixDivergence X Y := by
  have hx : X.det ≠ 0 := ne_of_gt hX.det_pos
  have hy : Y.det ≠ 0 := ne_of_gt hY.det_pos
  have hinv : Y⁻¹ * Y = 1 := Matrix.nonsing_inv_mul Y (isUnit_iff_ne_zero.mpr hy)
  unfold matrixBregman matrixPotential matrixDivergence
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv,
    Real.log_mul (inv_ne_zero hy) hx, Real.log_inv]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.trace_sub,
    hinv, Matrix.trace_one]
  ring

theorem matrix_precision_reversal (X Y : Matrix n n ℝ)
    (hY : Y.PosDef) :
    matrixDivergence X⁻¹ Y⁻¹ = matrixDivergence Y X := by
  have hy : IsUnit Y.det := isUnit_iff_ne_zero.mpr (ne_of_gt hY.det_pos)
  unfold matrixDivergence
  rw [Matrix.nonsing_inv_nonsing_inv Y hy, Matrix.trace_mul_comm,
    Matrix.det_mul, Matrix.det_mul]
  congr 2
  ring

def precisionMetric (P U V : Matrix n n ℝ) : ℝ := Matrix.trace (P * U * P * V)

omit [DecidableEq n] in
theorem precisionMetric_symmetric (P U V : Matrix n n ℝ) :
    precisionMetric P U V = precisionMetric P V U := by
  unfold precisionMetric
  simpa [Matrix.mul_assoc] using Matrix.trace_mul_comm (P * U) (P * V)

omit [DecidableEq n] in
theorem symmetric_trace_square (U : Matrix n n ℝ) (hU : U.IsSymm) :
    Matrix.trace (U * U) = ∑ i, ∑ j, (U i j) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have he : U j i = U i j := congrFun (congrFun hU i) j
  rw [he]
  ring

omit [DecidableEq n] in
theorem symmetric_trace_square_nonnegative (U : Matrix n n ℝ) (hU : U.IsSymm) :
    0 ≤ Matrix.trace (U * U) := by
  rw [symmetric_trace_square U hU]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem positive_definite_congruence (X C : Matrix n n ℝ)
    (hX : X.PosDef) (hC : IsUnit C) : (Cᴴ * X * C).PosDef := by
  refine ⟨Matrix.isHermitian_conjTranspose_mul_mul C hX.1, ?_⟩
  intro x hx
  have hn : C *ᵥ x ≠ 0 := by
    intro h
    apply hx
    apply Matrix.mulVec_injective_iff_isUnit.mpr hC
    simpa using h
  simpa only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
    using hX.2 (C *ᵥ x) hn

theorem sqrt_positive_definite_isUnit (X : Matrix n n ℝ) (hX : X.PosDef) :
    IsUnit hX.posSemidef.sqrt := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  intro h
  have hh := congrArg Matrix.det hX.posSemidef.sqrt_mul_self
  rw [Matrix.det_mul, h, zero_mul] at hh
  exact (ne_of_gt hX.det_pos) hh.symm

theorem matrixDivergence_relative_potential (X Y : Matrix n n ℝ)
    (hY : Y.PosDef) :
    matrixDivergence X Y =
      matrixPotential (hY.inv.posSemidef.sqrt * X * hY.inv.posSemidef.sqrt) := by
  let Q := hY.inv.posSemidef.sqrt
  have hsq : Q * Q = Y⁻¹ := hY.inv.posSemidef.sqrt_mul_self
  have ht : Matrix.trace (Y⁻¹ * X) = Matrix.trace (Q * X * Q) := by
    rw [Matrix.trace_mul_cycle, hsq]
  have hd : (Y⁻¹ * X).det = (Q * X * Q).det := by
    rw [← hsq]
    simp only [Matrix.det_mul]
    ring
  unfold matrixDivergence matrixPotential
  rw [ht, hd]

theorem matrixDivergence_nonnegative (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) : 0 ≤ matrixDivergence X Y := by
  rw [matrixDivergence_relative_potential X Y hY]
  apply matrixPotential_nonnegative
  have h := positive_definite_congruence X hY.inv.posSemidef.sqrt hX
    (sqrt_positive_definite_isUnit Y⁻¹ hY.inv)
  rwa [hY.inv.posSemidef.posSemidef_sqrt.isHermitian.eq] at h

theorem matrixDivergence_self (X : Matrix n n ℝ) (hX : X.PosDef) :
    matrixDivergence X X = 0 := by
  unfold matrixDivergence
  rw [Matrix.nonsing_inv_mul X (isUnit_iff_ne_zero.mpr (ne_of_gt hX.det_pos))]
  simp

theorem matrixDivergence_eq_zero_iff (X Y : Matrix n n ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) : matrixDivergence X Y = 0 ↔ X = Y := by
  constructor
  · intro h
    let Q := hY.inv.posSemidef.sqrt
    have hQu : IsUnit Q := sqrt_positive_definite_isUnit Y⁻¹ hY.inv
    have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQu
    have hA := positive_definite_congruence X Q hX hQu
    have hQh : Qᴴ = Q := hY.inv.posSemidef.posSemidef_sqrt.isHermitian.eq
    rw [hQh] at hA
    rw [matrixDivergence_relative_potential X Y hY] at h
    have hAeq : Q * X * Q = 1 := (matrixPotential_eq_zero_iff _ hA).mp h
    have hh := congrArg (fun Z : Matrix n n ℝ => Q⁻¹ * Z * Q⁻¹) hAeq
    dsimp only at hh
    have hleft : Q⁻¹ * (Q * X * Q) * Q⁻¹ = X := by
      calc
        _ = (Q⁻¹ * Q) * X * (Q * Q⁻¹) := by simp only [Matrix.mul_assoc]
        _ = X := by rw [Matrix.nonsing_inv_mul Q hQd,
          Matrix.mul_nonsing_inv Q hQd]; simp
    rw [hleft, Matrix.mul_one] at hh
    have hsq : Q * Q = Y⁻¹ := hY.inv.posSemidef.sqrt_mul_self
    rw [← Matrix.mul_inv_rev, hsq,
      Matrix.nonsing_inv_nonsing_inv Y
        (isUnit_iff_ne_zero.mpr (ne_of_gt hY.det_pos))] at hh
    exact hh
  · intro h
    subst X
    exact matrixDivergence_self _ hY

theorem precisionMetric_nonnegative (P U : Matrix n n ℝ)
    (hP : P.PosDef) (hU : U.IsSymm) : 0 ≤ precisionMetric P U U := by
  let Q := hP.posSemidef.sqrt
  have hsq : Q * Q = P := hP.posSemidef.sqrt_mul_self
  have hQ : Q.IsSymm := by
    ext i j
    simpa using hP.posSemidef.posSemidef_sqrt.isHermitian.apply i j
  have hA : (Q * U * Q).IsSymm := by
    change (Q * U * Q)ᵀ = Q * U * Q
    change Qᵀ = Q at hQ
    change Uᵀ = U at hU
    simp only [Matrix.transpose_mul, hQ, hU, Matrix.mul_assoc]
  have ht : Matrix.trace ((Q * U * Q) * (Q * U * Q)) = precisionMetric P U U := by
    calc
      _ = Matrix.trace (Q * (U * Q * Q * U) * Q) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Q * Q * (U * Q * Q * U)) := Matrix.trace_mul_cycle _ _ _
      _ = Matrix.trace ((Q * Q) * U * (Q * Q) * U) := by simp only [Matrix.mul_assoc]
      _ = precisionMetric P U U := by rw [hsq]; rfl
  rw [← ht]
  exact symmetric_trace_square_nonnegative _ hA

theorem matrixPotential_similarity (A C : Matrix n n ℝ) (hC : IsUnit C) :
    matrixPotential (C⁻¹ * A * C) = matrixPotential A := by
  have hd := (Matrix.isUnit_iff_isUnit_det C).mp hC
  have ht : Matrix.trace (C⁻¹ * A * C) = Matrix.trace A := by
    rw [Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv C hd, Matrix.one_mul]
  have hdet : (C⁻¹ * A * C).det = A.det := by
    have hc := congrArg Matrix.det (Matrix.nonsing_inv_mul C hd)
    rw [Matrix.det_mul, Matrix.det_one] at hc
    simp only [Matrix.det_mul]
    calc
      _ = A.det * (C⁻¹.det * C.det) := by ring
      _ = A.det := by rw [hc, mul_one]
  simp only [matrixPotential, ht, hdet]

def matrixCongruence (C X : Matrix n n ℝ) : Matrix n n ℝ := C * X * Cᵀ

theorem matrix_relative_congruence (X Y C : Matrix n n ℝ) (hC : IsUnit C) :
    (matrixCongruence C Y)⁻¹ * matrixCongruence C X =
      (Cᵀ)⁻¹ * (Y⁻¹ * X) * Cᵀ := by
  have hd := (Matrix.isUnit_iff_isUnit_det C).mp hC
  unfold matrixCongruence
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc C⁻¹ C, Matrix.nonsing_inv_mul C hd, Matrix.one_mul]

theorem matrixDivergence_congruence (X Y C : Matrix n n ℝ) (hC : IsUnit C) :
    matrixDivergence (matrixCongruence C X) (matrixCongruence C Y) =
      matrixDivergence X Y := by
  have hCt : IsUnit Cᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det C).mp hC
  change matrixPotential ((matrixCongruence C Y)⁻¹ * matrixCongruence C X) =
    matrixPotential (Y⁻¹ * X)
  rw [matrix_relative_congruence X Y C hC, matrixPotential_similarity _ _ hCt]

end
end Sigma
