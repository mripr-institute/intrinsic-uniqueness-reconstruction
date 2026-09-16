import SigmaProbGammaTransforms

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

def gammaLevyDensity (x : ℝ) : ℝ := 2*Real.exp (-x)/x
def gammaLaplaceExponent (s : ℝ) : ℝ := 2*Real.log (1+s)

theorem exponential_rate_tail_integral (x : ℝ) (hx : 0 < x) :
    (∫ s : ℝ in Ioi 1, Real.exp (-(s*x))) = Real.exp (-x)/x := by
  let F : ℝ → ℝ := fun s => -Real.exp (-(s*x))/x
  have hd : ∀ s ∈ Ici (1 : ℝ), HasDerivAt F (Real.exp (-(s*x))) s := by
    intro s hs
    have he := (((hasDerivAt_id s).mul_const x).neg.exp.neg).div_const x
    convert he using 1
    field_simp
  have ht : Tendsto F atTop (𝓝 0) := by
    have he : Tendsto (fun s : ℝ => Real.exp (-(s*x))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_id.atTop_mul_const hx))
    simpa [F] using he.neg.div_const x
  have hi := integrableOn_Ioi_deriv_of_nonneg' hd (fun s hs => (Real.exp_pos _).le) ht
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht
  simpa [F, neg_div] using he

theorem gamma_levy_complete_monotone_representation (x : ℝ) (hx : 0 < x) :
    gammaLevyDensity x = 2 * ∫ s : ℝ in Ioi 1, Real.exp (-(s*x)) := by
  rw [exponential_rate_tail_integral x hx]
  unfold gammaLevyDensity
  ring

theorem log_complete_bernstein_integral (l : ℝ) (hl : 0 ≤ l) :
    (∫ s : ℝ in Ioi 1, l/(s*(s+l))) = Real.log (1+l) := by
  let F : ℝ → ℝ := fun s => Real.log s - Real.log (s+l)
  have hd : ∀ s ∈ Ici (1 : ℝ), HasDerivAt F (l/(s*(s+l))) s := by
    intro s hs
    change 1 ≤ s at hs
    have hs0 : s ≠ 0 := ne_of_gt (by linarith)
    have hsl : s+l ≠ 0 := ne_of_gt (by linarith)
    convert (Real.hasDerivAt_log hs0).sub
      (((hasDerivAt_id s).add_const l).log hsl) using 1
    field_simp
  have hlim : Tendsto (fun s : ℝ => (1+l/s)⁻¹) atTop (𝓝 1) := by
    have hh : Tendsto (fun s : ℝ => 1+l/s) atTop (𝓝 1) := by
      simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := (1 : ℝ))).add
        ((tendsto_inv_atTop_zero).const_mul l)
    simpa using hh.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have ht : Tendsto F atTop (𝓝 0) := by
    have he := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hlim
    apply (show Tendsto (fun s : ℝ => Real.log ((1+l/s)⁻¹)) atTop (𝓝 0) by
      simpa only [Function.comp_apply, Real.log_one] using he).congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hs0 : s ≠ 0 := ne_of_gt (by linarith)
    have hsl : s+l ≠ 0 := ne_of_gt (by linarith)
    have heq : (1+l/s)⁻¹ = s/(s+l) := by field_simp
    rw [heq, Real.log_div hs0 hsl]
  have hi := integrableOn_Ioi_deriv_of_nonneg' hd (fun s hs => by
    have hs0 : 0 < s := by linarith [mem_Ioi.mp hs]
    exact div_nonneg hl (mul_pos hs0 (by linarith)).le) ht
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht
  simpa [F] using he

theorem gamma_exponent_derivative (l : ℝ) (hl : 0 ≤ l) :
    HasDerivAt gammaLaplaceExponent (2/(1+l)) l := by
  convert (((hasDerivAt_id l).const_add 1).log
    (ne_of_gt (by positivity : 0 < 1+l))).const_mul 2 using 1 <;>
      simp [gammaLaplaceExponent, div_eq_mul_inv]

end
end Sigma
