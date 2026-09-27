import SigmaMatrixExpDuhamel
import SigmaMatrixExpNorm
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Analysis.Normed.Ring.Units

namespace Sigma
noncomputable section
open MeasureTheory NormedSpace Filter
open scoped Matrix Topology

variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

/-- The actual Fréchet differential of the noncommutative matrix exponential. -/
def matrixExpDifferential (Z : Matrix n n ℝ) : Matrix n n ℝ →L[ℝ] Matrix n n ℝ :=
  fderiv ℝ (NormedSpace.exp ℝ) Z

theorem matrix_exp_hasStrictFDerivAt (Z : Matrix n n ℝ) :
    HasStrictFDerivAt (NormedSpace.exp ℝ) (matrixExpDifferential Z) Z :=
  (NormedSpace.exp_analytic Z).hasStrictFDerivAt

theorem matrix_exp_hasFDerivAt (Z : Matrix n n ℝ) :
    HasFDerivAt (NormedSpace.exp ℝ) (matrixExpDifferential Z) Z :=
  (matrix_exp_hasStrictFDerivAt Z).hasFDerivAt

theorem matrix_exp_differential_continuous :
    Continuous (matrixExpDifferential : Matrix n n ℝ → Matrix n n ℝ →L[ℝ] Matrix n n ℝ) := by
  exact continuous_iff_continuousAt.mpr fun Z => (NormedSpace.exp_analytic Z).fderiv.continuousAt

/-- An invertible exponential differential has a continuous inverse along any continuous
curve. The pointwise equivalences need not be supplied with a continuity hypothesis. -/
theorem matrix_exp_inverse_differential_continuousOn
    {α : Type*} [TopologicalSpace α] (Z : α → Matrix n n ℝ)
    (e : α → (Matrix n n ℝ ≃L[ℝ] Matrix n n ℝ)) (S : Set α)
    (hZ : ContinuousOn Z S)
    (he : ∀ s ∈ S, (e s : Matrix n n ℝ →L[ℝ] Matrix n n ℝ) =
      matrixExpDifferential (Z s)) :
    ContinuousOn (fun s => ((e s).symm : Matrix n n ℝ →L[ℝ] Matrix n n ℝ)) S := by
  have hInv : ContinuousOn (fun s => Ring.inverse (matrixExpDifferential (Z s))) S := by
    intro s hs
    have hEq : ((e s).toUnit : Matrix n n ℝ →L[ℝ] Matrix n n ℝ) =
        matrixExpDifferential (Z s) := he s hs
    have hi := NormedRing.inverse_continuousAt (e s).toUnit
    rw [hEq] at hi
    exact hi.comp_continuousWithinAt (f := fun t => matrixExpDifferential (Z t))
      (x := s) (matrix_exp_differential_continuous.comp_continuousOn hZ s hs)
  apply hInv.congr
  intro s hs
  dsimp only
  rw [← he s hs, ContinuousLinearMap.ring_inverse_equiv,
    ContinuousLinearMap.inverse_equiv]

private theorem matrix_exp_duhamel_parametric_continuous (Z U : Matrix n n ℝ) :
    Continuous (fun t : ℝ => ∫ r : ℝ in (0:ℝ)..1,
      NormedSpace.exp ℝ ((1-r) • Z) * U * NormedSpace.exp ℝ (r • (Z+t • U))) := by
  have hf : Continuous (Function.uncurry (fun (t r : ℝ) =>
      NormedSpace.exp ℝ ((1-r) • Z) * U * NormedSpace.exp ℝ (r • (Z+t • U)))) := by
    exact (((NormedSpace.exp_continuous.comp
      ((continuous_const.sub continuous_snd).smul continuous_const)).mul continuous_const).mul
      (NormedSpace.exp_continuous.comp
        (continuous_snd.smul (continuous_const.add (continuous_fst.smul continuous_const)))))
  have h := continuous_parametric_integral_of_continuous (μ := volume) hf
    (isCompact_Icc (a := (0:ℝ)) (b := 1))
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc] using h

/-- The Duhamel integral is the genuine Fréchet differential, without any commutativity
assumption on the perturbation. -/
theorem matrix_exp_differential_apply (Z U : Matrix n n ℝ) :
    matrixExpDifferential Z U = ∫ r : ℝ in (0:ℝ)..1,
      NormedSpace.exp ℝ ((1-r) • Z) * U * NormedSpace.exp ℝ (r • Z) := by
  let F : ℝ → Matrix n n ℝ := fun t => ∫ r : ℝ in (0:ℝ)..1,
    NormedSpace.exp ℝ ((1-r) • Z) * U * NormedSpace.exp ℝ (r • (Z+t • U))
  have hF : Continuous F := matrix_exp_duhamel_parametric_continuous Z U
  have hline : HasDerivAt (fun t : ℝ => Z+t • U) U 0 := by
    simpa using (hasDerivAt_const (0:ℝ) Z).add ((hasDerivAt_id (0:ℝ)).smul_const U)
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp ℝ (Z+t • U))
      (matrixExpDifferential Z U) 0 := by
    have hexp : HasFDerivAt (NormedSpace.exp ℝ) (matrixExpDifferential Z) (Z+(0:ℝ) • U) := by
      simpa using matrix_exp_hasFDerivAt Z
    exact hexp.comp_hasDerivAt 0 hline
  have hquot : (fun t : ℝ => t⁻¹ •
      (NormedSpace.exp ℝ (Z+t • U)-NormedSpace.exp ℝ Z)) =ᶠ[𝓝[≠] (0:ℝ)] F := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht
    rw [matrix_exp_duhamel_integral]
    have hscalar : (∫ r : ℝ in (0:ℝ)..1, matrixExpDuhamelIntegrand Z (t • U) r) = t • F t := by
      rw [← intervalIntegral.integral_smul]
      congr 1
      funext r
      dsimp [matrixExpDuhamelIntegrand, matrixExpDuhamelLeft, matrixExpDuhamelRight]
      simp only [mul_smul_comm, smul_mul_assoc]
    rw [hscalar, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  have hlim : Tendsto (fun t : ℝ => t⁻¹ •
      (NormedSpace.exp ℝ (Z+t • U)-NormedSpace.exp ℝ Z))
      (𝓝[≠] (0:ℝ)) (𝓝 (F 0)) :=
    (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hquot.symm
  have hlim' : Tendsto (fun t : ℝ => t⁻¹ •
      (NormedSpace.exp ℝ (Z+t • U)-NormedSpace.exp ℝ Z))
      (𝓝[≠] (0:ℝ)) (𝓝 (matrixExpDifferential Z U)) := by
    simpa using hd.tendsto_slope_zero
  have heq := tendsto_nhds_unique hlim' hlim
  simpa [F] using heq

end
end Sigma
