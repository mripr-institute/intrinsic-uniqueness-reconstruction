import SigmaProbEuler

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem gamma_derivative_recurrence (s d : ℝ) (hs : 0 < s)
    (hd : HasDerivAt Real.Gamma d s) :
    HasDerivAt Real.Gamma (Real.Gamma s+s*d) (s+1) := by
  have hg : DifferentiableAt ℝ Real.Gamma (s+1) :=
    Real.differentiableAt_Gamma (fun m => by
      have hm : (0 : ℝ) ≤ m := by positivity
      linarith)
  have hshift := hg.hasDerivAt.comp (h := fun x : ℝ => x+1) s
    ((hasDerivAt_id s).add_const 1)
  have hprod := (hasDerivAt_id s).mul hd
  have he : (fun x : ℝ => Real.Gamma (x+1)) =ᶠ[𝓝 s] (fun x => x*Real.Gamma x) := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with x hx
    exact Real.Gamma_add_one hx.ne'
  have hval := hshift.unique (hprod.congr_of_eventuallyEq he)
  simp only [one_mul,mul_one,id_eq] at hval
  simpa only [hval] using hg.hasDerivAt

theorem gamma_log_moment_of_gamma_derivative (n : ℕ) (d : ℝ)
    (hd : HasDerivAt Real.Gamma d ((n : ℝ)+2)) :
    (∫ t : ℝ, t^n*Real.log t ∂gammaProbability) = d := by
  have hc := Complex.hasDerivAt_GammaIntegral (s := (n : ℂ)+2) (by
    norm_num
    positivity)
  have heval : (∫ t : ℝ in Ioi 0,
      (t : ℂ)^((n : ℂ)+2-1)*(Real.log t*Real.exp (-t))) =
      Complex.ofReal (∫ t : ℝ in Ioi 0, t^(n+1)*(Real.log t*Real.exp (-t))) := by
    have hfun : (fun t : ℝ => (t : ℂ)^((n : ℂ)+2-1)*(Real.log t*Real.exp (-t))) =
        (fun t : ℝ => Complex.ofReal (t^(n+1)*(Real.log t*Real.exp (-t)))) := by
      funext t
      have hn : (n : ℂ)+2-1 = ((n+1 : ℕ) : ℂ) := by push_cast; ring
      rw [hn,Complex.cpow_natCast]
      push_cast
      rfl
    rw [hfun]
    exact (@RCLike.ofRealLI ℂ _).integral_comp_comm _
  rw [heval] at hc
  have hc' : HasDerivAt Complex.GammaIntegral
      (Complex.ofReal (∫ t : ℝ in Ioi 0, t^(n+1)*(Real.log t*Real.exp (-t))))
      (Complex.ofReal ((n : ℝ)+2)) := by simpa using hc
  have hr := hc'.real_of_complex
  have he : Real.Gamma =ᶠ[𝓝 ((n : ℝ)+2)]
      (fun x : ℝ => (Complex.GammaIntegral (x : ℂ)).re) := by
    filter_upwards [isOpen_Ioi.mem_nhds (by positivity : (0 : ℝ)<(n : ℝ)+2)] with x hx
    exact congrArg Complex.re (Complex.Gamma_eq_integral (by simpa using hx))
  have hr' : HasDerivAt Real.Gamma
      (∫ t : ℝ in Ioi 0, t^(n+1)*(Real.log t*Real.exp (-t))) ((n : ℝ)+2) := by
    simpa using hr.congr_of_eventuallyEq he
  have hv := hr'.unique hd
  rw [gamma_probability_integral]
  have hfun : (fun t : ℝ => SigmaPresentations.density t*(t^n*Real.log t)) =
      (fun t : ℝ => t^(n+1)*(Real.log t*Real.exp (-t))) := by
    funext t
    simp only [SigmaPresentations.density,pow_succ]
    ring
  rw [hfun,hv]

theorem gamma_log_moment_one :
    (∫ t : ℝ, t*Real.log t ∂gammaProbability) = 3-2*Real.eulerMascheroniConstant := by
  have hd := gamma_derivative_recurrence 2 (1-Real.eulerMascheroniConstant) (by norm_num)
    gamma_derivative_two_euler
  have he : HasDerivAt Real.Gamma (3-2*Real.eulerMascheroniConstant) 3 := by
    convert hd using 1 <;> norm_num [Real.Gamma_two]; ring
  simpa using gamma_log_moment_of_gamma_derivative 1 _ (by convert he using 1; norm_num)

theorem gamma_log_moment_two :
    (∫ t : ℝ, t^2*Real.log t ∂gammaProbability) = 11-6*Real.eulerMascheroniConstant := by
  have hd2 := gamma_derivative_recurrence 2 (1-Real.eulerMascheroniConstant) (by norm_num)
    gamma_derivative_two_euler
  have hd3 := gamma_derivative_recurrence 3 (3-2*Real.eulerMascheroniConstant) (by norm_num)
    (by convert hd2 using 1 <;> norm_num [Real.Gamma_two]; ring)
  have he : HasDerivAt Real.Gamma (11-6*Real.eulerMascheroniConstant) 4 := by
    convert hd3 using 1 <;> norm_num [Real.Gamma_nat_eq_factorial,Nat.factorial]; ring
  simpa using gamma_log_moment_of_gamma_derivative 2 _ (by convert he using 1; norm_num)

theorem gamma_log_moment_three :
    (∫ t : ℝ, t^3*Real.log t ∂gammaProbability) = 50-24*Real.eulerMascheroniConstant := by
  have hd2 := gamma_derivative_recurrence 2 (1-Real.eulerMascheroniConstant) (by norm_num)
    gamma_derivative_two_euler
  have hd3 := gamma_derivative_recurrence 3 (3-2*Real.eulerMascheroniConstant) (by norm_num)
    (by convert hd2 using 1 <;> norm_num [Real.Gamma_two]; ring)
  have hd4 := gamma_derivative_recurrence 4 (11-6*Real.eulerMascheroniConstant) (by norm_num)
    (by convert hd3 using 1 <;> norm_num [Real.Gamma_nat_eq_factorial,Nat.factorial]; ring)
  have he : HasDerivAt Real.Gamma (50-24*Real.eulerMascheroniConstant) 5 := by
    convert hd4 using 1 <;> norm_num [Real.Gamma_nat_eq_factorial,Nat.factorial]; ring
  simpa using gamma_log_moment_of_gamma_derivative 3 _ (by convert he using 1; norm_num)

end
end Sigma
