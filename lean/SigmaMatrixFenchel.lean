import SigmaMatrixGeometry
import Mathlib.Topology.Instances.EReal

namespace Sigma
noncomputable section
open scoped Matrix ComplexOrder
variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Classical.propDecidable

def extendedMatrixPotential (X : Matrix n n ℝ) : EReal := by
  classical
  exact if X.PosDef then (matrixPotential X : EReal) else ⊤

/-- Literal extended-real conjugacy, with all primal matrices in the supremum.
Outside the positive-definite cone the primal function is infinity. -/
def matrixFenchelConjugate (Θ : Matrix n n ℝ) : EReal :=
  ⨆ X : Matrix n n ℝ, (Matrix.trace (Θ*X) : ℝ) - extendedMatrixPotential X

theorem matrix_fenchel_gap_identity (Θ X : Matrix n n ℝ)
    (hΘ : (1-Θ).PosDef) (hX : X.PosDef) :
    Matrix.trace (Θ*X)-matrixPotential X =
      -Real.log (1-Θ).det-matrixDivergence X (1-Θ)⁻¹ := by
  have hdet : IsUnit (1-Θ).det := isUnit_iff_ne_zero.mpr hΘ.det_pos.ne'
  unfold matrixDivergence matrixPotential
  rw [Matrix.nonsing_inv_nonsing_inv _ hdet, Matrix.det_mul,
    Real.log_mul hΘ.det_pos.ne' hX.det_pos.ne', Matrix.sub_mul,
    Matrix.one_mul, Matrix.trace_sub]
  ring

theorem matrix_fenchel_upper_bound (Θ X : Matrix n n ℝ)
    (hΘ : (1-Θ).PosDef) (hX : X.PosDef) :
    Matrix.trace (Θ*X)-matrixPotential X ≤ -Real.log (1-Θ).det := by
  rw [matrix_fenchel_gap_identity Θ X hΘ hX]
  linarith [matrixDivergence_nonnegative X (1-Θ)⁻¹ hX hΘ.inv]

theorem matrix_fenchel_equality_iff (Θ X : Matrix n n ℝ)
    (hΘ : (1-Θ).PosDef) (hX : X.PosDef) :
    Matrix.trace (Θ*X)-matrixPotential X = -Real.log (1-Θ).det ↔ X=(1-Θ)⁻¹ := by
  rw [matrix_fenchel_gap_identity Θ X hΘ hX]
  constructor
  · intro hh
    exact (matrixDivergence_eq_zero_iff X (1-Θ)⁻¹ hX hΘ.inv).mp (by linarith)
  · intro hh
    rw [hh, matrixDivergence_self _ hΘ.inv, sub_zero]

theorem matrix_fenchel_conjugate_finite (Θ : Matrix n n ℝ) (hΘ : (1-Θ).PosDef) :
    matrixFenchelConjugate Θ = (-Real.log (1-Θ).det : ℝ) := by
  apply le_antisymm
  · apply iSup_le
    intro X
    by_cases hX : X.PosDef
    · simpa only [extendedMatrixPotential, if_pos hX, ← EReal.coe_sub, EReal.coe_le_coe_iff]
        using matrix_fenchel_upper_bound Θ X hΘ hX
    · simp [extendedMatrixPotential, hX]
  · apply le_iSup_of_le (1-Θ)⁻¹
    rw [extendedMatrixPotential, if_pos hΘ.inv, ← EReal.coe_sub,
      (matrix_fenchel_equality_iff Θ (1-Θ)⁻¹ hΘ hΘ.inv).mpr rfl]

theorem matrix_legendre_coordinate_inverse (X : Matrix n n ℝ) (hX : X.PosDef) :
    (1-(1-X⁻¹)).PosDef ∧ (1-(1-X⁻¹))⁻¹=X := by
  have he : (1 : Matrix n n ℝ)-(1-X⁻¹)=X⁻¹ := by abel
  rw [he]
  exact ⟨hX.inv, Matrix.nonsing_inv_nonsing_inv X (isUnit_iff_ne_zero.mpr hX.det_pos.ne')⟩

theorem matrix_legendre_inverse_coordinate (Θ : Matrix n n ℝ) (hΘ : (1-Θ).PosDef) :
    (1-Θ)⁻¹.PosDef ∧ 1-((1-Θ)⁻¹)⁻¹=Θ := by
  refine ⟨hΘ.inv, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hΘ.det_pos.ne')]
  abel

theorem unitary_conjugate_positive_definite (D : Matrix n n ℝ) (hD : D.PosDef)
    (U : Matrix.unitaryGroup n ℝ) :
    ((U : Matrix n n ℝ)*D*star (U : Matrix n n ℝ)).PosDef := by
  have hu : IsUnit (star (U : Matrix n n ℝ)) := (unitary.toUnits (star U)).isUnit
  have hh := positive_definite_congruence D (star (U : Matrix n n ℝ)) hD hu
  change (star (star (U : Matrix n n ℝ))*D*star (U : Matrix n n ℝ)).PosDef at hh
  simpa only [star_star] using hh

theorem hermitian_nonpositive_eigenvalue (B : Matrix n n ℝ) (hB : B.IsHermitian)
    (hn : ¬B.PosDef) : ∃ i, hB.eigenvalues i ≤ 0 := by
  by_contra h
  push_neg at h
  have hd : (Matrix.diagonal hB.eigenvalues).PosDef := Matrix.PosDef.diagonal h
  have hp := unitary_conjugate_positive_definite _ hd hB.eigenvectorUnitary
  apply hn
  convert hp using 1
  simpa only [RCLike.ofReal_real_eq_id, Function.comp_id, Function.id_comp] using hB.spectral_theorem

/-- A concrete SPD spectral ray exposes every nonpositive dual eigenvalue,
including the zero-eigenvalue boundary. -/
theorem matrix_fenchel_unbounded (Θ : Matrix n n ℝ) (hΘ : Θ.IsHermitian)
    (hn : ¬(1-Θ).PosDef) (M : ℝ) :
    ∃ X : Matrix n n ℝ, X.PosDef ∧ M < Matrix.trace (Θ*X)-matrixPotential X := by
  let B := (1 : Matrix n n ℝ)-Θ
  have hB : B.IsHermitian := Matrix.isHermitian_one.sub hΘ
  obtain ⟨j, hj⟩ := hermitian_nonpositive_eigenvalue B hB hn
  let U := hB.eigenvectorUnitary
  let S : ℝ := ∑ i ∈ Finset.univ.erase j, hB.eigenvalues i
  let r : ℝ := Real.exp (M+S+1)
  have hr : 0 < r := Real.exp_pos _
  let d : n → ℝ := fun i => if i=j then r else 1
  let D := Matrix.diagonal d
  let X : Matrix n n ℝ := (U : Matrix n n ℝ)*D*star (U : Matrix n n ℝ)
  have hD : D.PosDef := Matrix.PosDef.diagonal (by intro i; dsimp [d]; split_ifs <;> positivity)
  have hX : X.PosDef := unitary_conjugate_positive_definite D hD U
  have hd : X.det=r := by
    have hh := congrArg Matrix.det (unitary.coe_mul_star_self U)
    rw [Matrix.det_mul, Matrix.det_one] at hh
    rw [unitary.coe_star] at hh
    have hdet : X.det=D.det := by
      dsimp [X]
      rw [Matrix.det_mul, Matrix.det_mul]
      calc
        _ = D.det*((U : Matrix n n ℝ).det*(star (U : Matrix n n ℝ)).det) := by ring
        _ = D.det := by rw [hh, mul_one]
    rw [hdet, Matrix.det_diagonal]
    simp [d]
  have ht : Matrix.trace (B*X) = hB.eigenvalues j*r+S := by
    have he : star (U : Matrix n n ℝ)*B*(U : Matrix n n ℝ) = Matrix.diagonal hB.eigenvalues := by
      simpa only [RCLike.ofReal_real_eq_id, Function.comp_id, Function.id_comp] using hB.star_mul_self_mul_eq_diagonal
    calc
      _ = Matrix.trace ((star (U : Matrix n n ℝ)*B*(U : Matrix n n ℝ))*D) := by
        dsimp [X]
        rw [← Matrix.mul_assoc B, Matrix.trace_mul_cycle]
        simp only [Matrix.mul_assoc]
      _ = ∑ i, hB.eigenvalues i*d i := by rw [he]; simp [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
      _ = hB.eigenvalues j*r+S := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
        simp only [d, ↓reduceIte]
        have hh : ∑ i ∈ Finset.univ.erase j, hB.eigenvalues i*(if i=j then r else 1) = S := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [(Finset.mem_erase.mp hi).1]
        rw [hh]
        ring
  refine ⟨X, hX, ?_⟩
  have htrace : Matrix.trace (Θ*X)-Matrix.trace X = -(hB.eigenvalues j*r+S) := by
    dsimp [B] at ht
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub] at ht
    linarith
  unfold matrixPotential
  rw [hd]
  change M < Matrix.trace (Θ*X)-(Matrix.trace X-Real.log (Real.exp (M+S+1))-Fintype.card n)
  rw [Real.log_exp]
  have hb : hB.eigenvalues j*r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hj hr.le
  have hc : (0 : ℝ) ≤ Fintype.card n := Nat.cast_nonneg _
  linarith

theorem matrix_fenchel_conjugate_infinite (Θ : Matrix n n ℝ) (hΘ : Θ.IsHermitian)
    (hn : ¬(1-Θ).PosDef) : matrixFenchelConjugate Θ = ⊤ := by
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro M
  obtain ⟨X, hX, hM⟩ := matrix_fenchel_unbounded Θ hΘ hn M
  apply lt_of_lt_of_le _ (le_iSup (fun X : Matrix n n ℝ =>
    (Matrix.trace (Θ*X) : ℝ)-extendedMatrixPotential X) X)
  simpa only [extendedMatrixPotential, if_pos hX, ← EReal.coe_sub, EReal.coe_lt_coe_iff] using hM

theorem matrix_fenchel_conjugate_formula (Θ : Matrix n n ℝ) (hΘ : Θ.IsHermitian) :
    matrixFenchelConjugate Θ =
      if (1-Θ).PosDef then ((-Real.log (1-Θ).det : ℝ) : EReal) else ⊤ := by
  classical
  split_ifs with h
  · exact matrix_fenchel_conjugate_finite Θ h
  · exact matrix_fenchel_conjugate_infinite Θ hΘ h

end
end Sigma
