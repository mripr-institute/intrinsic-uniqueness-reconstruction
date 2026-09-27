import SigmaOpNonnegativeResolvent
import SigmaOpResolventHeat
import SigmaOpCFCEigen
import SigmaOpMixingStrong
import Mathlib.Analysis.InnerProductSpace.StarOrder

namespace Sigma
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem op_nonnegative_resolvent_spectrum (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) :
    spectrum ℝ (opNonnegativeResolvent B hsa hB) ⊆ Icc (0 : ℝ) 1 := by
  nontriviality H
  intro r hr
  exact ⟨spectrum_nonneg_of_nonneg (op_nonnegative_resolvent_nonneg B hsa hB) hr,
    (Real.le_norm_self r).trans ((spectrum.norm_le_norm_of_mem hr).trans
      (op_nonnegative_resolvent_norm B hsa hB))⟩

/-- The exponential functional calculus of an arbitrary nonnegative native
self-adjoint operator, constructed through its actual shift resolvent. -/
def opNonnegativeHeat (B : H →ₗ.[ℂ] H) (hsa : IsSelfAdjoint B)
    (hB : OpNonnegative B) : ℝ → H →L[ℂ] H :=
  resolventHeatOperator (opNonnegativeResolvent B hsa hB)

/-- The actual norm operator integral; it also supplies every strong integral. -/
theorem op_nonnegative_operator_gamma_mixing (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) :
    (∫ t : ℝ in Ioi 0, (t * Real.exp (-t)) • opNonnegativeHeat B hsa hB t) =
      opNonnegativeResolvent B hsa hB ^ 2 :=
  resolvent_heat_operator_gamma_integral _ (op_nonnegative_resolvent_selfAdjoint B hsa hB)
    (op_nonnegative_resolvent_spectrum B hsa hB)

theorem op_nonnegative_strong_gamma_mixing (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) (x : H) :
    (∫ t : ℝ in Ioi 0, (t * Real.exp (-t)) • opNonnegativeHeat B hsa hB t x) =
      opNonnegativeResolvent B hsa hB (opNonnegativeResolvent B hsa hB x) :=
  resolvent_heat_strong_gamma_integral _ (op_nonnegative_resolvent_selfAdjoint B hsa hB)
    (op_nonnegative_resolvent_spectrum B hsa hB) x

theorem op_nonnegative_heat_integer_eigenvector (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) (n : ℕ) (x : B.domain)
    (hx : B x = (n : ℂ) • x.val) (t : ℝ) (ht : 0 ≤ t) :
    opNonnegativeHeat B hsa hB t x.val = Real.exp (-(n : ℝ) * t) • x.val := by
  have hR := op_resolvent_integer_eigenvector_action B _
    (op_nonnegative_shift_resolvent B hsa hB) n x hx
  unfold opNonnegativeHeat resolventHeatOperator
  by_cases htpos : 0 < t
  · rw [if_pos htpos]
    have he := op_cfc_eigenvector_action (opNonnegativeResolvent B hsa hB)
      (op_nonnegative_resolvent_selfAdjoint B hsa hB) (1 / (1 + (n : ℝ))) x.val hR
      (resolventHeatScalar t) (resolvent_heat_scalar_continuous t).continuousOn
    have hp : 0 < (1 / (1 + (n : ℝ))) := by positivity
    rw [he, resolvent_heat_scalar_eq htpos hp]
    have hi : (1 / (1 + (n : ℝ)))⁻¹ - 1 = (n : ℝ) := by
      simp only [one_div, inv_inv]; ring
    rw [hi, show -t * (n : ℝ) = -(n : ℝ) * t by ring]
    exact algebraMap_smul ℂ (Real.exp (-(n : ℝ) * t)) x.val
  · have hz : t = 0 := le_antisymm (not_lt.mp htpos) ht
    simp [hz]

/-- Applying the actual operator equation to a nonzero integer eigenvector
extracts its scalar sample, with no completeness or multiplicity hypothesis. -/
theorem op_nonnegative_complex_mixing_integer_sample (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B)
    (μ : ComplexMeasure OpNonnegativeRay) (n : ℕ) (x : B.domain)
    (hx : B x = (n : ℂ) • x.val) (hx0 : x.val ≠ 0)
    (hmix : complexStrongIntegral μ (fun s => opNonnegativeHeat B hsa hB s.val x.val) =
      opNonnegativeResolvent B hsa hB (opNonnegativeResolvent B hsa hB x.val)) :
    complexRealIntegral μ (nonnegativeLaplaceTest n) =
      (((1 / (1 + (n : ℝ))) ^ 2 : ℝ) : ℂ) := by
  have he : (fun s : OpNonnegativeRay => opNonnegativeHeat B hsa hB s.val x.val) =
      fun s => nonnegativeLaplaceTest n s • x.val := by
    funext s
    exact op_nonnegative_heat_integer_eigenvector B hsa hB n x hx s.val s.property
  rw [he, complex_strong_integral_real_test] at hmix
  have hR := op_resolvent_integer_eigenvector_action B _
    (op_nonnegative_shift_resolvent B hsa hB) n x hx
  rw [hR, _root_.map_smul, hR, smul_smul] at hmix
  apply smul_left_injective ℂ hx0
  convert hmix using 1
  push_cast
  simp only [pow_two]

theorem op_nonnegative_complex_mixing_unique (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B)
    (μ : ComplexMeasure OpNonnegativeRay)
    (heigen : ∀ n : ℕ, ∃ x : B.domain, x.val ≠ 0 ∧ B x = (n : ℂ) • x.val)
    (hmix : ∀ x : H, complexStrongIntegral μ
      (fun s => opNonnegativeHeat B hsa hB s.val x) =
        opNonnegativeResolvent B hsa hB (opNonnegativeResolvent B hsa hB x)) :
    μ = nonnegativeGammaComplexMeasure := by
  apply operator_complex_gamma_mixing_characterization
  intro n
  obtain ⟨x,hx0,hx⟩ := heigen n
  exact op_nonnegative_complex_mixing_integer_sample B hsa hB μ n x hx hx0 (hmix x.val)

omit [CompleteSpace H] in
/-- The literal Gamma density conversion holds for genuine vector Bochner
integrals, not just scalar tests. -/
theorem gamma_probability_strong_integral (f : ℝ → H) :
    (∫ t, f t ∂gammaProbability) =
      ∫ t : ℝ in Ioi 0, (t * Real.exp (-t)) • f t := by
  change (∫ t, f t ∂volume.withDensity
    (fun t => ((Real.toNNReal (gammaPDFReal 2 1 t) : ℝ≥0) : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul
    ((measurable_gammaPDFReal 2 1).real_toNNReal)]
  have hfun : (fun t => Real.toNNReal (gammaPDFReal 2 1 t) • f t) =
      (Ici (0 : ℝ)).indicator (fun t => (t * Real.exp (-t)) • f t) := by
    funext t
    rw [NNReal.smul_def,
      Real.coe_toNNReal _ (gammaPDFReal_nonneg (by norm_num) (by norm_num) t),
      gamma_pdf_intrinsic]
    by_cases ht : 0 ≤ t
    · simp [ht, SigmaPresentations.density]
    · simp [ht]
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

theorem op_nonnegative_gamma_probability_mixing (B : H →ₗ.[ℂ] H)
    (hsa : IsSelfAdjoint B) (hB : OpNonnegative B) (x : H) :
    (∫ t, opNonnegativeHeat B hsa hB t x ∂gammaProbability) =
      opNonnegativeResolvent B hsa hB (opNonnegativeResolvent B hsa hB x) := by
  rw [gamma_probability_strong_integral]
  exact op_nonnegative_strong_gamma_mixing B hsa hB x

omit [CompleteSpace H] in
theorem signed_strong_integral_positive {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → H) :
    (∫ s, f s ∂μ.toSignedMeasure.toJordanDecomposition.posPart) -
      (∫ s, f s ∂μ.toSignedMeasure.toJordanDecomposition.negPart) = ∫ s, f s ∂μ := by
  let j : JordanDecomposition α := ⟨μ,0,Measure.MutuallySingular.zero_right⟩
  have hj : j.toSignedMeasure = μ.toSignedMeasure := by
    simp [j,JordanDecomposition.toSignedMeasure]
  have he : μ.toSignedMeasure.toJordanDecomposition = j := by
    rw [← hj,j.toJordanDecomposition_toSignedMeasure]
  simp [he,j]

omit [CompleteSpace H] in
theorem nonnegative_gamma_complex_strong_integral (f : OpNonnegativeRay → H) :
    complexStrongIntegral nonnegativeGammaComplexMeasure f =
      ∫ s, f s ∂nonnegativeGammaMixingMeasure := by
  unfold complexStrongIntegral nonnegativeGammaComplexMeasure
  change signedStrongIntegral nonnegativeGammaMixingMeasure.toSignedMeasure f +
    Complex.I • signedStrongIntegral (0 : SignedMeasure OpNonnegativeRay) f = _
  simpa [signedStrongIntegral, SignedMeasure.toJordanDecomposition_zero] using
    signed_strong_integral_positive nonnegativeGammaMixingMeasure f

end
end Sigma
