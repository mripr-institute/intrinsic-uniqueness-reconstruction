import SigmaProbCumulants
import SigmaProbDeficitDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace Sigma
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

theorem harmonic_real_sum (n : ℕ) :
    (∑ m ∈ Finset.range n, (1+(m : ℝ))⁻¹) = (harmonic n : ℝ) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_congr rfl
  intro m hm
  push_cast
  ring

theorem log_gamma_sequence_support (x : ℝ) (hx : 0 < x) (n : ℕ) :
    Real.BohrMollerup.logGammaSeq 1 n + (x-1)*
      (Real.log n-(harmonic (n+1) : ℝ)) ≤ Real.BohrMollerup.logGammaSeq x n := by
  have hterm (m : ℕ) : Real.log (x+m) ≤ Real.log (1+(m : ℝ)) +
      (x-1)/(1+(m : ℝ)) := by
    have hm : 0 < (1+(m : ℝ)) := by positivity
    have hxm : 0 < x+(m : ℝ) := by positivity
    have h := Real.log_le_sub_one_of_pos (div_pos hxm hm)
    rw [Real.log_div hxm.ne' hm.ne'] at h
    have he : (x+(m : ℝ))/(1+(m : ℝ))-1 = (x-1)/(1+(m : ℝ)) := by
      field_simp
    rw [he] at h
    linarith
  have hh := Finset.sum_le_sum (s := Finset.range (n+1)) (fun m _ => hterm m)
  rw [Finset.sum_add_distrib] at hh
  have he : (∑ m ∈ Finset.range (n+1), (x-1)/(1+(m : ℝ))) =
      (x-1)*(harmonic (n+1) : ℝ) := by
    simp only [div_eq_mul_inv, ← Finset.mul_sum, harmonic_real_sum]
  rw [he] at hh
  unfold Real.BohrMollerup.logGammaSeq
  nlinarith

theorem harmonic_log_slope_tendsto :
    Tendsto (fun n : ℕ => Real.log n-(harmonic (n+1) : ℝ)) atTop
      (𝓝 (-Real.eulerMascheroniConstant)) := by
  have hi : Tendsto (fun n : ℕ => ((n : ℝ)+1)⁻¹) atTop (𝓝 0) :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
      (tendsto_const_nhds (x := (1 : ℝ)))).inv_tendsto_atTop
  have he : (fun n : ℕ => Real.log n-(harmonic (n+1) : ℝ)) =
      fun n => -((harmonic n : ℝ)-Real.log n)-((n : ℝ)+1)⁻¹ := by
    funext n
    rw [harmonic_succ]
    push_cast
    ring
  rw [he]
  simpa using Real.tendsto_harmonic_sub_log.neg.sub hi

theorem log_gamma_euler_support (x : ℝ) (hx : 0 < x) :
    (x-1)*(-Real.eulerMascheroniConstant) ≤ Real.log (Real.Gamma x) := by
  have hleft := (Real.BohrMollerup.tendsto_log_gamma (by norm_num : (0 : ℝ)<1)).add
    (harmonic_log_slope_tendsto.const_mul (x-1))
  have hright := Real.BohrMollerup.tendsto_log_gamma hx
  have h := le_of_tendsto_of_tendsto hleft hright
    (Eventually.of_forall (log_gamma_sequence_support x hx))
  simpa only [Real.Gamma_one, Real.log_one, zero_add] using h

theorem gamma_derivative_one_euler :
    HasDerivAt Real.Gamma (-Real.eulerMascheroniConstant) 1 := by
  have hg : DifferentiableAt ℝ Real.Gamma 1 :=
    Real.differentiableAt_Gamma (fun m => by
      have hm : (0 : ℝ) ≤ m := by positivity
      linarith)
  have hd := (hg.hasDerivAt.log (by simp : Real.Gamma 1 ≠ 0)).add
    (((hasDerivAt_id (1 : ℝ)).sub_const 1).mul_const Real.eulerMascheroniConstant)
  have hmin : IsLocalMin (fun x : ℝ => Real.log (Real.Gamma x)+
      (x-1)*Real.eulerMascheroniConstant) 1 := by
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ)<1)] with x hx
    have hh := log_gamma_euler_support x hx
    simp only [Real.Gamma_one, Real.log_one, sub_self, zero_mul, add_zero]
    nlinarith
  have he := hmin.hasDerivAt_eq_zero hd
  simp only [Real.Gamma_one, div_one, mul_one] at he
  have heq : deriv Real.Gamma 1 = -Real.eulerMascheroniConstant := by linarith
  simpa only [heq] using hg.hasDerivAt

theorem gamma_derivative_two_euler :
    HasDerivAt Real.Gamma (1-Real.eulerMascheroniConstant) 2 := by
  have hg2 : DifferentiableAt ℝ Real.Gamma 2 :=
    Real.differentiableAt_Gamma (fun m => by
      have hm : (0 : ℝ) ≤ m := by positivity
      linarith)
  have hg2a : HasDerivAt Real.Gamma (deriv Real.Gamma 2) ((1 : ℝ)+1) := by
    simpa only [show (1 : ℝ)+1=2 by norm_num] using hg2.hasDerivAt
  have hshift := hg2a.comp (h := fun x : ℝ => x+1) 1
    ((hasDerivAt_id (1 : ℝ)).add_const 1)
  have hprod := (hasDerivAt_id (1 : ℝ)).mul gamma_derivative_one_euler
  have he : (fun x : ℝ => Real.Gamma (x+1)) =ᶠ[𝓝 1] (fun x => x*Real.Gamma x) := by
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ)<1)] with x hx
    exact Real.Gamma_add_one hx.ne'
  have hval := hshift.unique (hprod.congr_of_eventuallyEq he)
  simp only [id_eq, one_mul, mul_one, Real.Gamma_one] at hval
  have hval' : deriv Real.Gamma 2 = 1-Real.eulerMascheroniConstant := by linarith
  simpa only [hval'] using hg2.hasDerivAt

theorem gamma_logarithmic_integral_euler :
    (∫ t : ℝ in Ioi 0, t*(Real.log t*Real.exp (-t))) =
      1-Real.eulerMascheroniConstant := by
  have hc := Complex.hasDerivAt_GammaIntegral (s := (2 : ℂ)) (by norm_num)
  have heval : (∫ t : ℝ in Ioi 0,
      (t : ℂ)^((2 : ℂ)-1)*(Real.log t*Real.exp (-t))) =
      Complex.ofReal (∫ t : ℝ in Ioi 0, t*(Real.log t*Real.exp (-t))) := by
    have hfun : (fun t : ℝ => (t : ℂ)^((2 : ℂ)-1)*(Real.log t*Real.exp (-t))) =
        (fun t : ℝ => Complex.ofReal (t*(Real.log t*Real.exp (-t)))) := by
      funext t
      norm_num
    rw [hfun]
    exact (@RCLike.ofRealLI ℂ _).integral_comp_comm _
  rw [heval] at hc
  have hr := hc.real_of_complex
  have he : Real.Gamma =ᶠ[𝓝 (2 : ℝ)]
      (fun x : ℝ => (Complex.GammaIntegral (x : ℂ)).re) := by
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ)<2)] with x hx
    exact congrArg Complex.re (Complex.Gamma_eq_integral (by simpa using hx))
  have hh := hr.congr_of_eventuallyEq he
  exact hh.unique gamma_derivative_two_euler

theorem gamma_probability_expected_log :
    (∫ t : ℝ, Real.log t ∂gammaProbability) = 1-Real.eulerMascheroniConstant := by
  rw [gamma_probability_integral]
  have he : (fun t : ℝ => SigmaPresentations.density t*Real.log t) =
      (fun t : ℝ => t*(Real.log t*Real.exp (-t))) := by
    funext t
    unfold SigmaPresentations.density
    ring
  rw [he, gamma_logarithmic_integral_euler]

theorem gamma_probability_log_integrable : Integrable Real.log gammaProbability := by
  apply Integrable.of_integral_ne_zero
  rw [gamma_probability_expected_log]
  have h := Real.eulerMascheroniConstant_lt_two_thirds
  linarith

end
end Sigma
