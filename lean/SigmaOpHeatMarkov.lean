import SigmaOpHeatKernelAction
import SigmaOpHeatResolvent

/-!
The conservative-semigroup clause of paper `final:O3-form`.
The input and output are the actual complex Gamma-weighted L² classes.
Positivity means that a representative is real and nonnegative almost
everywhere. The kernel identification proves positivity; the zeroth
Laguerre coefficient proves conservation of the probability integral.
-/

namespace Sigma
noncomputable section
open MeasureTheory Filter

/-- The normalized zeroth Laguerre mode is the constant function one. -/
theorem laguerre_basis_zero_coe :
    (laguerreHilbertBasis 0 : ℝ → ℂ) =ᵐ[gammaProbability] fun _ => 1 := by
  rw [laguerre_hilbert_basis_apply, normalizedLaguerreL2Vector]
  simp only [Nat.cast_zero, zero_add, Real.sqrt_one, Complex.ofReal_one,
    inv_one, one_smul]
  filter_upwards [(op_laguerre_complex_mem_l2 0).coeFn_toLp] with t ht
  simpa only [(opLaguerre_first_three t).1, Complex.ofReal_one] using ht

/-- The zeroth Fourier coefficient is exactly the probability integral. -/
theorem laguerre_coefficient_zero_integral (f : LaguerreWeightedHilbert) :
    laguerreHilbertBasis.repr f 0 = ∫ t : ℝ, f t ∂gammaProbability := by
  rw [HilbertBasis.repr_apply_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [laguerre_basis_zero_coe] with t ht
  simp [ht, RCLike.inner_apply]

/-- Every weighted L² input is integrable for the invariant probability. -/
theorem laguerre_l2_integrable (f : LaguerreWeightedHilbert) :
    Integrable (fun t : ℝ => f t) gammaProbability := by
  simpa only [show ∀ t, opLaguerre 0 t = 1 from fun t => (opLaguerre_first_three t).1,
    Complex.ofReal_one, one_mul] using
    laguerre_l2_product_integrable 0 f

/-- The actual heat semigroup preserves the constant vector, including time zero. -/
theorem laguerre_heat_preserves_one (τ : ℝ) (hτ : 0 ≤ τ) :
    laguerreHeatOperator τ hτ (laguerreHilbertBasis 0) = laguerreHilbertBasis 0 := by
  simpa using laguerre_heat_basis_action τ hτ 0

/-- The probability integral is invariant on all of the weighted L² space. -/
theorem laguerre_heat_preserves_integral (τ : ℝ) (hτ : 0 ≤ τ)
    (f : LaguerreWeightedHilbert) :
    (∫ t : ℝ, (laguerreHeatOperator τ hτ f : ℝ → ℂ) t ∂gammaProbability) =
      ∫ t : ℝ, f t ∂gammaProbability := by
  rw [← laguerre_coefficient_zero_integral, laguerre_heat_coordinate,
    laguerre_coefficient_zero_integral]
  simp

/-- Each kernel row multiplied by an arbitrary L² input is integrable. -/
theorem laguerre_heat_kernel_product_integrable {τ x : ℝ} (hτ : 0 < τ)
    (hx : 0 < x) (f : LaguerreWeightedHilbert) :
    Integrable (fun y : ℝ => (laguerreHeatKernel τ x y : ℂ) * f y)
      gammaProbability := by
  apply (L2.integrable_inner (𝕜 := ℂ) (laguerreHeatKernelRow τ x hτ hx) f).congr
  filter_upwards [laguerre_heat_kernel_row_coe_ae hτ hx] with y hy
  simp [hy, RCLike.inner_apply]

/-- The positive kernel preserves real nonnegative inputs under its actual
integral action at every positive spatial point. -/
theorem laguerre_heat_kernel_integral_nonnegative {τ x : ℝ} (hτ : 0 < τ)
    (hx : 0 < x) (f : LaguerreWeightedHilbert)
    (hf : ∀ᵐ y ∂gammaProbability, 0 ≤ (f y).re ∧ (f y).im = 0) :
    0 ≤ (∫ y : ℝ, (laguerreHeatKernel τ x y : ℂ) * f y ∂gammaProbability).re ∧
      (∫ y : ℝ, (laguerreHeatKernel τ x y : ℂ) * f y ∂gammaProbability).im = 0 := by
  have hi := laguerre_heat_kernel_product_integrable hτ hx f
  have hp := operator_integer_samples_ae_pos gammaProbability
    operator_gamma_probability_integer_samples
  constructor
  · have he := Complex.reCLM.integral_comp_comm hi
    change (∫ y : ℝ, ((laguerreHeatKernel τ x y : ℂ) * f y).re
      ∂gammaProbability) =
      (∫ y : ℝ, (laguerreHeatKernel τ x y : ℂ) * f y ∂gammaProbability).re at he
    rw [← he]
    apply integral_nonneg_of_ae
    filter_upwards [hf, hp] with y hy hyp
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using
      mul_nonneg (laguerre_heat_kernel_pos hτ hx hyp).le hy.1
  · have he := Complex.imCLM.integral_comp_comm hi
    change (∫ y : ℝ, ((laguerreHeatKernel τ x y : ℂ) * f y).im
      ∂gammaProbability) =
      (∫ y : ℝ, (laguerreHeatKernel τ x y : ℂ) * f y ∂gammaProbability).im at he
    rw [← he]
    apply integral_eq_zero_of_ae
    filter_upwards [hf] with y hy
    simp [Complex.mul_im, hy.2]

/-- Positivity preservation for the native semigroup on complex weighted L²,
with reality as well as nonnegativity retained, at every nonnegative time. -/
theorem laguerre_heat_preserves_nonnegative (τ : ℝ) (hτ : 0 ≤ τ)
    (f : LaguerreWeightedHilbert)
    (hf : ∀ᵐ y ∂gammaProbability, 0 ≤ (f y).re ∧ (f y).im = 0) :
    ∀ᵐ x ∂gammaProbability,
      0 ≤ ((laguerreHeatOperator τ hτ f : ℝ → ℂ) x).re ∧
        ((laguerreHeatOperator τ hτ f : ℝ → ℂ) x).im = 0 := by
  rcases eq_or_lt_of_le hτ with hzero | hpos
  · subst τ
    simpa only [laguerre_heat_zero, ContinuousLinearMap.id_apply] using hf
  · have hp := operator_integer_samples_ae_pos gammaProbability
      operator_gamma_probability_integer_samples
    filter_upwards [hp, laguerre_heat_kernel_integral_eq_operator hpos f]
      with x hx he
    rw [← he]
    exact laguerre_heat_kernel_integral_nonnegative hpos hx f hf

end
end Sigma
