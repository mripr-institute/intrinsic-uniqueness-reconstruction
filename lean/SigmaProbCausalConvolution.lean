import SigmaProbSurvival
import Mathlib.MeasureTheory.Integral.SetIntegral

namespace Sigma
noncomputable section
open MeasureTheory Set

/-- The causal unit-rate exponential kernel on the full real line. -/
def causalUnitExponential (t : ℝ) : ℝ :=
  if 0 ≤ t then Real.exp (-t) else 0

/-- The causal Gamma(2,1) Green kernel, including its zero extension to negative time. -/
def causalGammaGreen (t : ℝ) : ℝ :=
  if 0 ≤ t then t * Real.exp (-t) else 0

/-- The ordinary whole-line convolution of two causal unit-exponential kernels. -/
def causalUnitExponentialConvolution (t : ℝ) : ℝ :=
  ∫ s : ℝ, causalUnitExponential s * causalUnitExponential (t-s)

theorem causal_unit_exponential_convolution_eq_gamma_green (t : ℝ) :
    causalUnitExponentialConvolution t = causalGammaGreen t := by
  by_cases ht : 0 ≤ t
  · have hpoint (s : ℝ) :
        causalUnitExponential s * causalUnitExponential (t-s) =
          (Set.indicator (Icc 0 t) (fun s : ℝ => Real.exp (-s) * Real.exp (-(t-s))) s) := by
      by_cases hs : s ∈ Icc (0 : ℝ) t
      · have hs0 : 0 ≤ s := hs.1
        have hst : 0 ≤ t-s := by linarith [hs.2]
        simp [causalUnitExponential, hs0, hst, Set.indicator_of_mem hs]
      · have hzero : ¬ (0 ≤ s ∧ s ≤ t) := by simpa [mem_Icc] using hs
        have hprod : ¬ (0 ≤ s ∧ 0 ≤ t-s) := by
          intro h
          exact hzero ⟨h.1, by linarith [h.2]⟩
        simp only [causalUnitExponential]
        rw [Set.indicator_of_not_mem hs]
        by_cases hs0 : 0 ≤ s <;> by_cases hst : 0 ≤ t-s <;>
          simp_all
    rw [causalUnitExponentialConvolution, show
      (fun s : ℝ => causalUnitExponential s * causalUnitExponential (t-s)) =
        Set.indicator (Icc 0 t) (fun s : ℝ => Real.exp (-s) * Real.exp (-(t-s))) by
          funext s; exact hpoint s]
    rw [integral_indicator measurableSet_Icc]
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht]
    rw [exponential_pair_convolution]
    simp [causalGammaGreen, ht, SigmaPresentations.density]
  · have hzero (s : ℝ) :
        causalUnitExponential s * causalUnitExponential (t-s) = 0 := by
      by_cases hs : 0 ≤ s
      · have hst : ¬ 0 ≤ t-s := by intro h; exact ht (by linarith)
        simp [causalUnitExponential, hs, hst]
      · simp [causalUnitExponential, hs]
    rw [causalUnitExponentialConvolution, show
      (fun s : ℝ => causalUnitExponential s * causalUnitExponential (t-s)) =
        fun _ : ℝ => 0 by funext s; exact hzero s]
    simp [causalGammaGreen, ht]

end
end Sigma
