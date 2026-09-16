import SigmaProbFourier

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal NNReal

def complexLaplace (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-z*(t : ℂ)) ∂μ

theorem unit_exp_complex_laplace (z : ℂ) (hz : -1 < z.re) :
    complexLaplace unitExpProbability z = (1+z)⁻¹ := by
  rw [complexLaplace, unit_exp_complex_integral]
  have ha : 0 < (1+z).re := by simp; linarith
  rw [← positive_rate_complex_exponential_integral _ ha]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem independent_sum_complex_laplace (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (z : ℂ) :
    complexLaplace (independentAffineSum μ ν 1) z =
      complexLaplace μ z * complexLaplace ν z := by
  unfold complexLaplace independentAffineSum
  rw [integral_map (by fun_prop : Measurable (fun p : ℝ×ℝ => 1*p.1+p.2)).aemeasurable
    ((continuous_const.mul Complex.continuous_ofReal).cexp.aestronglyMeasurable)]
  have he : (fun p : ℝ×ℝ => Complex.exp (-z*((1*p.1+p.2 : ℝ) : ℂ))) =
      fun p : ℝ×ℝ => Complex.exp (-z*(p.1 : ℂ))*Complex.exp (-z*(p.2 : ℂ)) := by
    funext p
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  exact integral_prod_mul (fun t : ℝ => Complex.exp (-z*(t : ℂ)))
    (fun t : ℝ => Complex.exp (-z*(t : ℂ)))

theorem gamma_complex_laplace (z : ℂ) (hz : -1 < z.re) :
    complexLaplace gammaProbability z = (1+z)⁻¹ ^ 2 := by
  rw [← independent_exponential_pair_gamma, independent_sum_complex_laplace,
    unit_exp_complex_laplace z hz]
  ring

theorem gamma_probability_complex_integral (f : ℝ → ℂ) :
    (∫ t, f t ∂gammaProbability) =
      ∫ t : ℝ in Ioi 0, (SigmaPresentations.density t : ℂ) * f t := by
  change (∫ t, f t ∂volume.withDensity
    (fun t => ((Real.toNNReal (gammaPDFReal 2 1 t) : ℝ≥0) : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul
    ((measurable_gammaPDFReal 2 1).real_toNNReal)]
  have hfun : (fun t => Real.toNNReal (gammaPDFReal 2 1 t) • f t) =
      (Ici (0 : ℝ)).indicator (fun t => (SigmaPresentations.density t : ℂ) * f t) := by
    funext t
    rw [NNReal.smul_def, Complex.real_smul,
      Real.coe_toNNReal _ (gammaPDFReal_nonneg (by norm_num) (by norm_num) t),
      gamma_pdf_intrinsic]
    by_cases ht : 0 ≤ t <;> simp [ht]
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

theorem gamma_complex_mellin (z : ℂ) (hz : -1 < z.re) :
    (∫ t : ℝ, (t : ℂ) ^ (z-1) ∂gammaProbability) = Complex.Gamma (z+1) := by
  rw [gamma_probability_complex_integral]
  have hz1 : 0 < (z+1).re := by simp; linarith
  have hi := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := z+1) (r := 1)
    hz1 (by norm_num)
  simp only [add_sub_cancel_right, Complex.ofReal_one, one_div_one, Complex.one_cpow,
    one_mul] at hi
  rw [← hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have hp : (t : ℂ) * (t : ℂ) ^ (z-1) = (t : ℂ) ^ z := by
    nth_rw 1 [← Complex.cpow_one (t : ℂ)]
    rw [← Complex.cpow_add _ _ ht0]
    congr 1
    ring
  simp only [SigmaPresentations.density, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]
  rw [mul_assoc, mul_comm (Complex.exp _) _, ← mul_assoc, hp]

theorem gamma_probability_mean : (∫ t : ℝ, t ∂gammaProbability) = 2 := by
  simpa using gamma_probability_moments 1

theorem gamma_probability_variance :
    (∫ t : ℝ, (t-2)^2 ∂gammaProbability) = 2 := by
  have h1 : Integrable (fun t : ℝ => t) gammaProbability := by
    simpa using gamma_probability_monomial_integrable 1
  have h2 := gamma_probability_monomial_integrable 2
  have he : (fun t : ℝ => (t-2)^2) = fun t => t^2 - 4*t + 4 := by funext t; ring
  have hs : Integrable (fun t : ℝ => t^2 - 4*t) gammaProbability := h2.sub (h1.const_mul 4)
  rw [he, integral_add hs (integrable_const (4 : ℝ)),
    integral_sub h2 (show Integrable (fun t : ℝ => 4*t) gammaProbability from h1.const_mul 4),
    integral_mul_left, gamma_probability_moments 2, gamma_probability_mean]
  norm_num [Nat.factorial]

end
end Sigma
