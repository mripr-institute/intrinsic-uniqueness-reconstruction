import SigmaOperators
import SigmaProbGamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The native full-line smooth compact-test equation of final:O1. -/
def WeakGammaStein (μ : Measure ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
    (∫ t : ℝ, t * deriv f t + (2-t)*f t ∂μ) = 0

def steinFlux (t : ℝ) : ℝ := t^2 * Real.exp (-t)

def steinKernelFamily (C t : ℝ) : ℝ := t + C * Real.exp t / t

theorem stein_test_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    Integrable (fun t => t * deriv f t + (2-t)*f t) μ := by
  have hc : Continuous (fun t => t * deriv f t + (2-t)*f t) := (continuous_id.mul (hf.continuous_deriv (by simp))).add
    ((continuous_const.sub continuous_id).mul hf.continuous)
  exact hc.integrable_of_hasCompactSupport (hs.deriv.mul_left.add hs.mul_left)

theorem steinFlux_contDiff : ContDiff ℝ ∞ steinFlux :=
  (contDiff_id.pow 2).mul (contDiff_id.neg.exp)

theorem steinFlux_hasDerivAt (t : ℝ) :
    HasDerivAt steinFlux ((2-t)*SigmaPresentations.density t) t := by
  convert operator_pearson_flux_derivative t using 1
  funext x
  simp [steinFlux, SigmaPresentations.density]
  ring

theorem stein_flux_test_derivative (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    deriv (fun t => steinFlux t * f t) t =
      SigmaPresentations.density t * (t * deriv f t + (2-t)*f t) := by
  rw [((steinFlux_hasDerivAt t).mul ((hf.differentiable (by simp) t).hasDerivAt)).deriv]
  unfold steinFlux SigmaPresentations.density
  ring

theorem gamma_probability_weak_stein : WeakGammaStein gammaProbability := by
  intro f hf hs
  rw [gamma_probability_integral]
  have hh := HasCompactSupport.integral_Ioi_deriv_eq
    ((steinFlux_contDiff.mul hf).of_le (by simp)) hs.mul_left (0 : ℝ)
  have he : (fun t => deriv (fun t => steinFlux t * f t) t) =
      (fun t => SigmaPresentations.density t * (t * deriv f t + (2-t)*f t)) := by
    funext t
    exact stein_flux_test_derivative f hf t
  rw [he] at hh
  simpa [steinFlux] using hh

/-- The forward measure implication with the same full-line test class. -/
theorem weak_stein_of_eq_gamma (μ : Measure ℝ) (hμ : μ = gammaProbability) : WeakGammaStein μ := by
  rw [hμ]
  exact gamma_probability_weak_stein

theorem steinKernelFamily_flux (C : ℝ) {t : ℝ} (ht : 0 < t) :
    steinKernelFamily C t * SigmaPresentations.density t = steinFlux t + C := by
  unfold steinKernelFamily SigmaPresentations.density steinFlux
  have he : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  calc
    _ = t^2 * Real.exp (-t) + C * (Real.exp t * Real.exp (-t)) := by
      field_simp
      ring
    _ = _ := by rw [he]; ring

theorem steinFlux_integrable : IntegrableOn steinFlux (Ioi (0 : ℝ)) := by
  have hh := gamma_probability_monomial_integrable 1
  have he : (∫ t : ℝ in Ioi 0, steinFlux t) = 2 := by
    simpa [steinFlux, SigmaPresentations.density, pow_two, mul_assoc] using intrinsic_gamma_integral 1
  by_contra hn
  rw [integral_undef hn] at he
  norm_num at he

theorem steinFlux_integral : (∫ t : ℝ in Ioi 0, steinFlux t) = 2 := by
  simpa [steinFlux, SigmaPresentations.density, pow_two, mul_assoc] using intrinsic_gamma_integral 1

theorem steinFlux_tendsto_zero_atTop : Tendsto steinFlux atTop (𝓝 0) :=
  Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2

theorem steinFlux_tendsto_zero_at_zero : Tendsto steinFlux (𝓝[>] 0) (𝓝 0) := by
  have hh := steinFlux_contDiff.continuous.continuousAt.tendsto.mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  simpa [steinFlux] using hh

end
end Sigma
