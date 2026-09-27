import SigmaMatrixGlobalMinimality
import SigmaMatrixExpDuhamel
import SigmaMatrixExpFrechet
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace Sigma
noncomputable section
open MeasureTheory
open scoped Matrix Topology

variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

/-- The exponential divided difference, including its diagonal value. -/
def realExpDividedDifference (x y : ℝ) : ℝ :=
  if x = y then Real.exp x else (Real.exp y - Real.exp x) / (y - x)

theorem real_exp_divided_difference_integral (x y : ℝ) :
    (∫ r : ℝ in (0:ℝ)..1, Real.exp ((1-r)*x+r*y)) =
      realExpDividedDifference x y := by
  by_cases h : x = y
  · subst y
    have he : (fun r : ℝ => Real.exp ((1-r)*x+r*x)) = fun _ => Real.exp x := by
      funext r
      congr 1
      ring
    rw [he]
    simp [realExpDividedDifference]
  · have hne : y-x ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    let f : ℝ → ℝ := fun r => Real.exp ((1-r)*x+r*y) / (y-x)
    have hd (r : ℝ) : HasDerivAt f (Real.exp ((1-r)*x+r*y)) r := by
      have ha : HasDerivAt (fun r : ℝ => (1-r)*x+r*y) (y-x) r := by
        convert (((hasDerivAt_const r (1:ℝ)).sub (hasDerivAt_id r)).mul_const x).add
          ((hasDerivAt_id r).mul_const y) using 1
        ring
      convert ha.exp.div_const (y-x) using 1
      simp [f, hne]
    have hc : Continuous f := continuous_iff_continuousAt.mpr fun r => (hd r).continuousAt
    have hi : IntervalIntegrable (fun r : ℝ => Real.exp ((1-r)*x+r*y)) volume 0 1 := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1)
      hc.continuousOn (fun r _ => hd r) hi]
    simp [f, realExpDividedDifference, h, sub_div]

theorem real_exp_log_divided_difference_mul (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    realExpDividedDifference (Real.log a) (Real.log b) *
      realLogDividedDifference a b = 1 := by
  by_cases h : a = b
  · subst b
    simp [realExpDividedDifference, realLogDividedDifference, Real.exp_log ha, ha.ne']
  · have hl : Real.log a ≠ Real.log b := fun hh => h (Real.log_injOn_pos ha hb hh)
    have hab : b-a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have hlab : Real.log b-Real.log a ≠ 0 := sub_ne_zero.mpr (Ne.symm hl)
    simp only [realExpDividedDifference, realLogDividedDifference, if_neg hl, if_neg h,
      Real.exp_log ha, Real.exp_log hb]
    field_simp

/-- A spectral coordinate multiplier is an actual continuous linear map on
the Frobenius matrix space; continuity follows from finite dimension. -/
def matrixSpectralMultiplier (V : Matrix n n ℝ) (c : n → n → ℝ) :
    Matrix n n ℝ →L[ℝ] Matrix n n ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun U => V * (Matrix.of fun i j => c i j * (Vᵀ * U * V) i j) * Vᵀ
    map_add' := by
      intro U W
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, mul_add]
      rw [show (Matrix.of fun i j => c i j * (Vᵀ * U * V) i j +
        c i j * (Vᵀ * W * V) i j) =
          (Matrix.of fun i j => c i j * (Vᵀ * U * V) i j) +
          (Matrix.of fun i j => c i j * (Vᵀ * W * V) i j) by rfl]
      change V * ((Matrix.of fun i j => c i j * (Vᵀ * U * V) i j) +
        (Matrix.of fun i j => c i j * (Vᵀ * W * V) i j)) * Vᵀ = _
      rw [Matrix.mul_add, Matrix.add_mul]
    map_smul' := by
      intro r U
      simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
        smul_eq_mul]
      have he : (Matrix.of fun i j => c i j * (r * (Vᵀ * U * V) i j)) =
          r • (Matrix.of fun i j => c i j * (Vᵀ * U * V) i j) := by
        ext i j
        simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      rw [he, Matrix.mul_smul, Matrix.smul_mul] }

omit [DecidableEq n] in
@[simp] theorem matrix_spectral_multiplier_apply (V : Matrix n n ℝ)
    (c : n → n → ℝ) (U : Matrix n n ℝ) :
    matrixSpectralMultiplier V c U =
      V * (Matrix.of fun i j => c i j * (Vᵀ * U * V) i j) * Vᵀ := rfl

theorem matrix_spectral_multiplier_comp (V : Matrix n n ℝ)
    (hV : Vᵀ * V = 1) (hV' : V * Vᵀ = 1)
    (c d : n → n → ℝ) (hcd : ∀ i j, c i j * d i j = 1)
    (U : Matrix n n ℝ) :
    matrixSpectralMultiplier V c (matrixSpectralMultiplier V d U) = U := by
  simp only [matrix_spectral_multiplier_apply]
  have he (T : Matrix n n ℝ) : Vᵀ * (V * T * Vᵀ) * V = T := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᵀ V, hV]
    simp only [Matrix.one_mul]
    simp
  rw [he]
  have hc : (Matrix.of fun i j => c i j * (Matrix.of fun i j =>
      d i j * (Vᵀ * U * V) i j) i j) = Vᵀ * U * V := by
    ext i j
    simp only [Matrix.of_apply, ← mul_assoc, hcd, one_mul]
  rw [hc]
  simp only [← Matrix.mul_assoc]
  rw [hV', Matrix.one_mul]
  rw [Matrix.mul_assoc U V Vᵀ, hV', Matrix.mul_one]

theorem matrix_exp_differential_diagonal (z : n → ℝ) (U : Matrix n n ℝ) :
    matrixExpDifferential (Matrix.diagonal z) U =
      Matrix.of (fun i j => realExpDividedDifference (z i) (z j) * U i j) := by
  rw [matrix_exp_differential_apply]
  have hi : IntervalIntegrable (fun r : ℝ =>
      NormedSpace.exp ℝ ((1-r) • Matrix.diagonal z) * U *
      NormedSpace.exp ℝ (r • Matrix.diagonal z)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact ((NormedSpace.exp_continuous.comp
      ((continuous_const.sub continuous_id).smul continuous_const)).mul continuous_const).mul
      (NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const))
  ext i j
  change matrixEntryCLM i j (∫ r : ℝ in (0:ℝ)..1,
    NormedSpace.exp ℝ ((1-r) • Matrix.diagonal z) * U *
      NormedSpace.exp ℝ (r • Matrix.diagonal z)) = _
  rw [← (matrixEntryCLM i j).intervalIntegral_comp_comm hi]
  have he (r : ℝ) : matrixEntryCLM i j
      (NormedSpace.exp ℝ ((1-r) • Matrix.diagonal z) * U *
        NormedSpace.exp ℝ (r • Matrix.diagonal z)) =
      Real.exp ((1-r)*z i+r*z j) * U i j := by
    have hs (r : ℝ) : r • Matrix.diagonal z = Matrix.diagonal (fun i => r*z i) := by
      rw [← Matrix.diagonal_smul]
      rfl
    rw [hs, hs, matrix_exp_diagonal_real, matrix_exp_diagonal_real]
    change ((Matrix.diagonal fun i => Real.exp ((1-r)*z i)) * U *
      (Matrix.diagonal fun i => Real.exp (r*z i))) i j = _
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [Real.exp_add]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_mul_const, real_exp_divided_difference_integral]
  rfl

theorem matrix_exp_differential_congruence (V Z U : Matrix n n ℝ)
    (hV : Vᵀ * V = 1) (hV' : V * Vᵀ = 1) :
    matrixExpDifferential (V * Z * Vᵀ) U =
      V * matrixExpDifferential Z (Vᵀ * U * V) * Vᵀ := by
  have hdet : V.det * (Vᵀ).det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hV'
  have hu : IsUnit V := (Matrix.isUnit_iff_isUnit_det V).mpr
    (isUnit_of_mul_eq_one V.det (Vᵀ).det hdet)
  have hinv : V⁻¹ = Vᵀ := Matrix.inv_eq_left_inv hV
  let W := Vᵀ * U * V
  have he : V * W * Vᵀ = U := by
    dsimp [W]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V Vᵀ, hV']
    simp only [Matrix.one_mul]
    simp
  have hd : HasDerivAt (fun t : ℝ => Z+t • W) W 0 := by
    simpa using (hasDerivAt_const (0:ℝ) Z).add ((hasDerivAt_id (0:ℝ)).smul_const W)
  have he1 : HasDerivAt (fun t : ℝ => NormedSpace.exp ℝ (Z+t • W))
      (matrixExpDifferential Z W) 0 := by
    have hh := matrix_exp_hasFDerivAt Z
    have hh' : HasFDerivAt (NormedSpace.exp ℝ) (matrixExpDifferential Z) (Z+(0:ℝ) • W) := by
      simpa using hh
    exact hh'.comp_hasDerivAt 0 hd
  have hc := matrix_congruence_hasDerivAt V he1
  have hf : (fun t : ℝ => matrixCongruence V (NormedSpace.exp ℝ (Z+t • W))) =
      (fun t : ℝ => NormedSpace.exp ℝ (V*Z*Vᵀ+t • U)) := by
    funext t
    unfold matrixCongruence
    rw [← hinv, ← Matrix.exp_conj ℝ _ _ hu, hinv]
    congr 1
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, he]
  rw [hf] at hc
  have hd' : HasDerivAt (fun t : ℝ => V*Z*Vᵀ+t • U) U 0 := by
    simpa using (hasDerivAt_const (0:ℝ) (V*Z*Vᵀ)).add ((hasDerivAt_id (0:ℝ)).smul_const U)
  have hh : HasFDerivAt (NormedSpace.exp ℝ) (matrixExpDifferential (V*Z*Vᵀ))
      (V*Z*Vᵀ+(0:ℝ) • U) := by
    simpa using matrix_exp_hasFDerivAt (V*Z*Vᵀ)
  exact (hh.comp_hasDerivAt 0 hd').unique hc

theorem matrix_exp_differential_spd_log (A : Matrix n n ℝ) (hA : A.PosDef) :
    matrixExpDifferential (matrixSPDLog A hA) =
      matrixSpectralMultiplier
        (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)
        (fun i j => realExpDividedDifference
          (Real.log (hA.isHermitian.eigenvalues i))
          (Real.log (hA.isHermitian.eigenvalues j))) := by
  apply ContinuousLinearMap.ext
  intro U
  change matrixExpDifferential
    ((hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal (fun i => Real.log (hA.isHermitian.eigenvalues i)) *
      (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)ᵀ) U = _
  have hV : (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)ᵀ *
      (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary
  have hV' : (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) *
      (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)ᵀ = 1 :=
    unitary.coe_mul_star_self hA.isHermitian.eigenvectorUnitary
  rw [matrix_exp_differential_congruence
    (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ) _ U hV hV',
    matrix_exp_differential_diagonal]
  rfl

/-- The exponential differential at the actual symmetric SPD logarithm is
invertible, and its inverse is precisely the logarithmic divided difference. -/
def matrixExpSPDLogEquiv (A : Matrix n n ℝ) (hA : A.PosDef) :
    Matrix n n ℝ ≃L[ℝ] Matrix n n ℝ := by
  let V := (hA.isHermitian.eigenvectorUnitary : Matrix n n ℝ)
  let a := hA.isHermitian.eigenvalues
  let D := matrixSpectralMultiplier V (fun i j =>
    realExpDividedDifference (Real.log (a i)) (Real.log (a j)))
  let L := matrixSpectralMultiplier V (fun i j => realLogDividedDifference (a i) (a j))
  have hV : Vᵀ * V = 1 := unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary
  have hV' : V * Vᵀ = 1 := unitary.coe_mul_star_self hA.isHermitian.eigenvectorUnitary
  have hDL (U : Matrix n n ℝ) : D (L U) = U :=
    matrix_spectral_multiplier_comp V hV hV' _ _
      (fun i j => real_exp_log_divided_difference_mul _ _ (hA.eigenvalues_pos i)
        (hA.eigenvalues_pos j)) U
  have hLD (U : Matrix n n ℝ) : L (D U) = U :=
    matrix_spectral_multiplier_comp V hV hV'
      (fun i j => realLogDividedDifference (a i) (a j))
      (fun i j => realExpDividedDifference (Real.log (a i)) (Real.log (a j)))
      (fun i j => (mul_comm _ _).trans
        (real_exp_log_divided_difference_mul _ _ (hA.eigenvalues_pos i)
          (hA.eigenvalues_pos j))) U
  exact {
    toLinearEquiv := {
      toLinearMap := D.toLinearMap
      invFun := L
      left_inv := hLD
      right_inv := hDL }
    continuous_toFun := D.continuous
    continuous_invFun := L.continuous }

theorem matrix_exp_spd_log_equiv_coe (A : Matrix n n ℝ) (hA : A.PosDef) :
    (matrixExpSPDLogEquiv A hA : Matrix n n ℝ →L[ℝ] Matrix n n ℝ) =
      matrixExpDifferential (matrixSPDLog A hA) :=
  (matrix_exp_differential_spd_log A hA).symm

theorem matrix_exp_spd_log_equiv_symm_apply (A U : Matrix n n ℝ) (hA : A.PosDef) :
    (matrixExpSPDLogEquiv A hA).symm U = matrixSPDLogSpectralDifferential A U hA := rfl

end
end Sigma
