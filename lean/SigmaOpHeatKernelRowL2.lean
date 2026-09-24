import SigmaOpHeatKernelHilbert

namespace Sigma
noncomputable section
open MeasureTheory
open scoped ENNReal

/-- Every positive spatial row of the Hille--Hardy kernel lies in the complex
Gamma-weighted Hilbert space, with no exceptional set of starting points. -/
theorem laguerre_heat_kernel_row_mem_l2 {τ x : ℝ} (hτ : 0 < τ)
    (hx : 0 < x) :
    Memℒp (fun y : ℝ => (laguerreHeatKernel τ x y : ℂ)) 2 gammaProbability := by
  let r := Real.exp (-τ)
  let c := Real.sqrt r / (1+Real.sqrt r)
  let D := ((1-r)⁻¹)^2
  have hr : 0 < r ∧ r < 1 := by
    constructor
    · exact Real.exp_pos _
    · rw [Real.exp_lt_one_iff]; linarith
  have hs : Real.sqrt r < 1 := by
    nlinarith [Real.sq_sqrt hr.1.le, Real.sqrt_nonneg r]
  have hc : c < 1/2 := by
    dsimp [c]
    rw [div_lt_iff₀ (by positivity : 0 < 1+Real.sqrt r)]
    nlinarith
  have hβ : -1 < -(2*c) := by linarith
  have hExpInt : Integrable (fun y : ℝ => Real.exp ((2*c)*y))
      gammaProbability := by
    apply Integrable.of_integral_ne_zero
    have h := gamma_probability_laplace (s := -(2*c)) hβ
    simpa only [neg_mul, neg_neg] using
      (show (∫ y : ℝ, Real.exp ((2*c)*y) ∂gammaProbability) ≠ 0 by
        rw [show (fun y : ℝ => Real.exp ((2*c)*y)) =
          (fun y : ℝ => Real.exp (-(-(2*c)*y))) by funext y; congr 1; ring,
          h]
        have hden : 0 < 1 + -(2*c) := by linarith
        positivity)
  have hboundInt : Integrable
      (fun y : ℝ => (D * Real.exp (c*x))^2 * Real.exp ((2*c)*y))
      gammaProbability := hExpInt.const_mul _
  have hp : ∀ᵐ y : ℝ ∂gammaProbability, 0 < y := by
    have hn : ∀ᵐ y : ℝ ∂gammaProbability, 0 ≤ y := by
      simpa only [ae_iff, not_le] using gamma_probability_negative_ray
    have hne : ∀ᵐ y : ℝ ∂gammaProbability, y ≠ 0 := by
      rw [ae_iff]
      simpa only [not_ne_iff, Set.setOf_eq_eq_singleton] using
        gamma_probability_no_atom 0
    filter_upwards [hn, hne] with y hy hyn
    exact lt_of_le_of_ne hy (Ne.symm hyn)
  have hm : Measurable (fun y : ℝ => laguerreHeatKernel τ x y) := by
    have hpair : Measurable (fun y : ℝ => (x, y)) := by fun_prop
    exact (laguerre_heat_kernel_measurable τ).comp hpair
  have hmc : Measurable (fun y : ℝ => (laguerreHeatKernel τ x y : ℂ)) :=
    Complex.measurable_ofReal.comp hm
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => (laguerreHeatKernel τ x y : ℂ)) gammaProbability :=
    hmc.aestronglyMeasurable
  apply (memℒp_two_iff_integrable_sq_norm hmeas).mpr
  apply Integrable.mono' hboundInt
  · exact (hmc.norm.pow_const 2).aestronglyMeasurable
  · filter_upwards [hp] with y hy
    have hKpos : 0 ≤ laguerreHeatKernel τ x y := by
      rw [laguerreHeatKernel, if_pos hy]
      exact (laguerre_heat_kernel_closed_pos hτ hx hy).le
    have hKbound : laguerreHeatKernel τ x y ≤
        D * Real.exp (c*(x+y)) := by
      rw [laguerreHeatKernel, if_pos hy]
      simpa only [D, c, r] using
        laguerre_heat_kernel_closed_growth_bound hτ hx hy
    rw [Real.norm_of_nonneg (sq_nonneg (‖(laguerreHeatKernel τ x y : ℂ)‖)),
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hsq : (laguerreHeatKernel τ x y)^2 ≤
        (D * Real.exp (c*(x+y)))^2 := by gcongr
    calc
      (laguerreHeatKernel τ x y)^2 ≤
          (D * Real.exp (c*(x+y)))^2 := hsq
      _ = (D * Real.exp (c*x))^2 * Real.exp ((2*c)*y) := by
        calc
          (D * Real.exp (c*(x+y)))^2 =
              (D * Real.exp (c*x))^2 * (Real.exp (c*y))^2 := by
            rw [show c*(x+y) = c*x+c*y by ring, Real.exp_add]
            ring
          _ = (D * Real.exp (c*x))^2 * Real.exp ((2*c)*y) := by
            congr 1
            rw [pow_two, ← Real.exp_add]
            congr 1
            ring

/-- The L² row vector represented by the actual Hille--Hardy kernel formula. -/
def laguerreHeatKernelRow (τ x : ℝ) (hτ : 0 < τ) (hx : 0 < x) :
    LaguerreWeightedHilbert :=
  (laguerre_heat_kernel_row_mem_l2 hτ hx).toLp

theorem laguerre_heat_kernel_row_coe_ae {τ x : ℝ} (hτ : 0 < τ)
    (hx : 0 < x) :
    (laguerreHeatKernelRow τ x hτ hx : ℝ → ℂ) =ᵐ[gammaProbability]
      fun y => (laguerreHeatKernel τ x y : ℂ) :=
  (laguerre_heat_kernel_row_mem_l2 hτ hx).coeFn_toLp

end
end Sigma
