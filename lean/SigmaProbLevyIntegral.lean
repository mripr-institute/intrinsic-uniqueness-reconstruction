import SigmaProbLevy
import Mathlib.MeasureTheory.Integral.Prod

namespace Sigma
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

theorem positive_rate_exponential_integral (r : ℝ) (hr : 0 < r) :
    (∫ x : ℝ in Ioi 0, Real.exp (-(r*x))) = 1/r := by
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := r)
    (by norm_num) hr
  simpa using hi

theorem positive_rate_exponential_integrable (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => Real.exp (-(r*x))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [positive_rate_exponential_integral r hr]
  exact (one_div_pos.mpr hr).ne'

theorem levy_kernel_parameter_integral (l x : ℝ) (hl : 0 ≤ l) (hx : 0 < x) :
    (∫ u : ℝ in Icc 0 l, 2*Real.exp (-((1+u)*x))) =
      (1-Real.exp (-(l*x)))*gammaLevyDensity x := by
  let F : ℝ → ℝ := fun u => -2/x*Real.exp (-((1+u)*x))
  have hd (u : ℝ) : HasDerivAt F (2*Real.exp (-((1+u)*x))) u := by
    have hh := (((((hasDerivAt_id u).const_add 1).mul_const x).neg.exp).const_mul (-2/x))
    convert hh using 1
    field_simp
    ring
  have hm : Continuous (fun u : ℝ => 2*Real.exp (-((1+u)*x))) := by fun_prop
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hl]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) (hm.intervalIntegrable 0 l)]
  simp only [F, add_zero, one_mul]
  have he : -((1+l)*x) = -x+(-(l*x)) := by ring
  rw [he, Real.exp_add, gammaLevyDensity]
  ring

theorem levy_kernel_space_integral (u : ℝ) (hu : 0 ≤ u) :
    (∫ x : ℝ in Ioi 0, 2*Real.exp (-((1+u)*x))) = 2/(1+u) := by
  rw [integral_mul_left, positive_rate_exponential_integral (1+u) (by positivity)]
  ring

theorem levy_kernel_integrable (l : ℝ) :
    Integrable (fun z : ℝ×ℝ => 2*Real.exp (-((1+z.1)*z.2)))
      ((volume.restrict (Icc 0 l)).prod (volume.restrict (Ioi 0))) := by
  have hconst : Integrable (fun _ : ℝ => (2 : ℝ)) (volume.restrict (Icc 0 l)) :=
    integrable_const 2
  have hexp : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) := by
    simpa using positive_rate_exponential_integrable 1 (by norm_num)
  have hm : Continuous (fun z : ℝ×ℝ => 2*Real.exp (-((1+z.1)*z.2))) := by fun_prop
  have hb : Continuous (fun z : ℝ×ℝ => 2*Real.exp (-z.2)) := by fun_prop
  apply (hconst.prod_mul hexp).mono' hm.aestronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae (isClosed_le hm.norm hb).measurableSet).mpr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.exp (-((1+u)*x)))]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  nlinarith [hu.1, mem_Ioi.mp hx]

theorem gamma_levy_exponent_integral (l : ℝ) (hl : 0 ≤ l) :
    (∫ x : ℝ in Ioi 0, (1-Real.exp (-(l*x)))*gammaLevyDensity x) =
      gammaLaplaceExponent l := by
  have he : (∫ x : ℝ in Ioi 0, (1-Real.exp (-(l*x)))*gammaLevyDensity x) =
      ∫ x : ℝ in Ioi 0, ∫ u : ℝ in Icc 0 l, 2*Real.exp (-((1+u)*x)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact (levy_kernel_parameter_integral l x hl hx).symm
  rw [he, ← integral_integral_swap (levy_kernel_integrable l)]
  have he2 : (∫ u : ℝ in Icc 0 l, ∫ x : ℝ in Ioi 0,
      2*Real.exp (-((1+u)*x))) = ∫ u : ℝ in Icc 0 l, 2/(1+u) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    exact levy_kernel_space_integral u hu.1
  rw [he2, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hl]
  have hd : ∀ u ∈ uIcc (0 : ℝ) l, HasDerivAt gammaLaplaceExponent (2/(1+u)) u := by
    intro u hu
    rw [uIcc_of_le hl] at hu
    exact gamma_exponent_derivative u hu.1
  have hi : IntervalIntegrable (fun u : ℝ => 2/(1+u)) volume 0 l := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (continuous_const.add continuous_id).continuousOn
    intro u hu
    rw [uIcc_of_le hl] at hu
    change 1+u ≠ 0
    linarith [hu.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp [gammaLaplaceExponent]

theorem gamma_levy_exponent_integrable (l : ℝ) (hl : 0 ≤ l) :
    IntegrableOn (fun x : ℝ => (1-Real.exp (-(l*x)))*gammaLevyDensity x) (Ioi 0) := by
  apply (levy_kernel_integrable l).integral_prod_right.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact levy_kernel_parameter_integral l x hl hx

end
end Sigma
