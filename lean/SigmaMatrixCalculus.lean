import SigmaRealMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Matrix

namespace Sigma
noncomputable section
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
open scoped Topology

theorem matrix_det_differentiable : Differentiable ℝ (Matrix.det : Matrix n n ℝ → ℝ) := by
  intro X
  have he : (Matrix.det : Matrix n n ℝ → ℝ) = fun X =>
      ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, X (σ i) i := by
    funext X
    exact Matrix.det_apply' X
  rw [he]
  apply DifferentiableAt.sum
  intro σ hσ
  apply DifferentiableAt.const_mul
  apply HasFDerivAt.differentiableAt
  apply HasFDerivAt.finset_prod
  intro i hi
  let ev : Matrix n n ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun X => X (σ i) i
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hd : Differentiable ℝ (fun X : Matrix n n ℝ => X (σ i) i) :=
    ev.toContinuousLinearMap.differentiable
  exact (hd X).hasFDerivAt

theorem matrix_det_identity_direction (U : Matrix n n ℝ) :
    HasDerivAt (fun t : ℝ => (1+t • U).det) (Matrix.trace U) 0 := by
  let Q : Polynomial ℝ := (Matrix.det ((1 : Matrix n n (Polynomial ℝ)) +
    (Polynomial.X : Polynomial ℝ) • U.map Polynomial.C)).divX.divX
  have he : (fun t : ℝ => (1+t • U).det) =
      fun t : ℝ => 1+Matrix.trace U*t+Q.eval t*t^2 := by
    funext t
    exact Matrix.det_one_add_smul t U
  rw [he]
  have hd := (((hasDerivAt_id (0 : ℝ)).const_mul (Matrix.trace U)).const_add 1).add
    ((Q.hasDerivAt 0).mul ((hasDerivAt_id (0 : ℝ)).pow 2))
  simpa using hd

theorem matrix_det_direction (X U : Matrix n n ℝ) (hX : IsUnit X.det) :
    HasDerivAt (fun t : ℝ => (X+t • U).det) (X.det*Matrix.trace (X⁻¹*U)) 0 := by
  have he : (fun t : ℝ => (X+t • U).det) =
      fun t : ℝ => X.det*(1+t • (X⁻¹*U)).det := by
    funext t
    rw [← Matrix.det_mul]
    congr 1
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv X hX, Matrix.one_mul]
  rw [he]
  exact (matrix_det_identity_direction (X⁻¹*U)).const_mul X.det

/-- Jacobi's formula for the actual Frechet derivative, obtained from the native determinant. -/
theorem matrix_det_fderiv (X U : Matrix n n ℝ) (hX : IsUnit X.det) :
    fderiv ℝ Matrix.det X U = X.det*Matrix.trace (X⁻¹*U) := by
  have hd : HasFDerivAt (Matrix.det : Matrix n n ℝ → ℝ) (fderiv ℝ Matrix.det X)
      (X+(0 : ℝ) • U) := by simpa using (matrix_det_differentiable X).hasFDerivAt
  have hl := hd.comp_hasDerivAt (f := fun t : ℝ => X+t • U) 0
    (((hasDerivAt_id (0 : ℝ)).smul_const U).const_add X)
  have he := hl.unique (matrix_det_direction X U hX)
  simpa using he

def matrixTraceCLM : Matrix n n ℝ →L[ℝ] ℝ :=
  (Matrix.traceLinearMap n ℝ ℝ).toContinuousLinearMap

theorem matrixPotential_differentiableAt (X : Matrix n n ℝ) (hX : X.PosDef) :
    DifferentiableAt ℝ matrixPotential X := by
  exact ((matrixTraceCLM (n := n)).differentiableAt.sub
    ((matrix_det_differentiable X).log (ne_of_gt hX.det_pos))).sub_const (Fintype.card n : ℝ)

theorem matrixPotential_fderiv (X U : Matrix n n ℝ) (hX : X.PosDef) :
    fderiv ℝ matrixPotential X U = Matrix.trace ((1-X⁻¹)*U) := by
  have hd := ((matrixTraceCLM (n := n)).hasFDerivAt.sub
    ((matrix_det_differentiable X).hasFDerivAt.log (ne_of_gt hX.det_pos))).sub_const
    (Fintype.card n : ℝ)
  have he : fderiv ℝ matrixPotential X =
      matrixTraceCLM - (X.det)⁻¹ • fderiv ℝ Matrix.det X := hd.fderiv
  rw [he]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [matrix_det_fderiv X U (isUnit_iff_ne_zero.mpr (ne_of_gt hX.det_pos))]
  change Matrix.trace U - X.det⁻¹*(X.det*Matrix.trace (X⁻¹*U)) = Matrix.trace ((1-X⁻¹)*U)
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, ← mul_assoc,
    inv_mul_cancel₀ (ne_of_gt hX.det_pos), one_mul]

theorem matrix_inverse_hasFDerivAt (X : Matrix n n ℝ) (hX : IsUnit X.det) :
    HasFDerivAt (fun A : Matrix n n ℝ => A⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℝ) X⁻¹ X⁻¹) X := by
  rcases (Matrix.isUnit_iff_isUnit_det X).mpr hX with ⟨u, rfl⟩
  simpa only [Matrix.nonsing_inv_eq_ring_inverse, Ring.inverse_unit] using
    (hasFDerivAt_ring_inverse (𝕜 := ℝ) u)

def matrixGradient (X : Matrix n n ℝ) : Matrix n n ℝ := 1-X⁻¹

theorem matrixGradient_hasFDerivAt (X : Matrix n n ℝ) (hX : X.PosDef) :
    HasFDerivAt matrixGradient
      (ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℝ) X⁻¹ X⁻¹) X := by
  simpa only [neg_neg] using
    (matrix_inverse_hasFDerivAt X (isUnit_iff_ne_zero.mpr (ne_of_gt hX.det_pos))).const_sub 1

theorem matrixGradient_fderiv (X U : Matrix n n ℝ) (hX : X.PosDef) :
    fderiv ℝ matrixGradient X U = X⁻¹*U*X⁻¹ := by
  rw [(matrixGradient_hasFDerivAt X hX).fderiv]
  rfl

theorem matrix_hessian_metric (X U V : Matrix n n ℝ) (hX : X.PosDef) :
    Matrix.trace ((fderiv ℝ matrixGradient X U)*V) = precisionMetric X⁻¹ U V := by
  rw [matrixGradient_fderiv X U hX]
  rfl

theorem matrix_actual_bregman (X Y : Matrix n n ℝ) (hX : X.PosDef) (hY : Y.PosDef) :
    matrixPotential X - matrixPotential Y - fderiv ℝ matrixPotential Y (X-Y) =
      matrixDivergence X Y := by
  rw [matrixPotential_fderiv Y (X-Y) hY]
  exact matrix_bregman_formula X Y hX hY

theorem matrixPotential_fderiv_of_det_ne_zero (X U : Matrix n n ℝ) (hX : X.det ≠ 0) :
    fderiv ℝ matrixPotential X U = Matrix.trace ((1-X⁻¹)*U) := by
  have hd := ((matrixTraceCLM (n := n)).hasFDerivAt.sub
    ((matrix_det_differentiable X).hasFDerivAt.log hX)).sub_const (Fintype.card n : ℝ)
  have he : fderiv ℝ matrixPotential X =
      matrixTraceCLM - (X.det)⁻¹ • fderiv ℝ Matrix.det X := hd.fderiv
  rw [he]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [matrix_det_fderiv X U (isUnit_iff_ne_zero.mpr hX)]
  change Matrix.trace U - X.det⁻¹*(X.det*Matrix.trace (X⁻¹*U)) = Matrix.trace ((1-X⁻¹)*U)
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, ← mul_assoc,
    inv_mul_cancel₀ hX, one_mul]

def matrixTraceRightCLM (U : Matrix n n ℝ) : Matrix n n ℝ →L[ℝ] ℝ :=
  matrixTraceCLM.comp (ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℝ) 1 U)

theorem matrixPotential_second_fderiv (X U V : Matrix n n ℝ) (hX : X.PosDef) :
    fderiv ℝ (fun Y : Matrix n n ℝ => fderiv ℝ matrixPotential Y U) X V =
      Matrix.trace (X⁻¹*V*X⁻¹*U) := by
  have hd := (matrixTraceRightCLM U).hasFDerivAt.comp X (matrixGradient_hasFDerivAt X hX)
  have he : (fun Y : Matrix n n ℝ => fderiv ℝ matrixPotential Y U) =ᶠ[𝓝 X]
      (fun Y : Matrix n n ℝ => matrixTraceRightCLM U (matrixGradient Y)) := by
    have hn := (matrix_det_differentiable X).continuousAt
      (eventually_ne_nhds (ne_of_gt hX.det_pos))
    filter_upwards [hn] with Y hY
    rw [matrixPotential_fderiv_of_det_ne_zero Y U hY]
    simp [matrixTraceRightCLM, matrixTraceCLM, matrixGradient,
      ContinuousLinearMap.mulLeftRight_apply]
  rw [(hd.congr_of_eventuallyEq he).fderiv]
  simp [matrixTraceRightCLM, matrixTraceCLM, ContinuousLinearMap.mulLeftRight_apply]

end
end Sigma
