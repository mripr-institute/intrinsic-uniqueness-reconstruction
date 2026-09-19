import SigmaProbZetaSeries

namespace Sigma
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

theorem deficit_cgf_log_gamma (s : ℝ) (hs : s<1) :
    Real.log (∫ v : ℝ, Real.exp (s*v) ∂gammaDeficitProbability)=
      Real.log (Real.Gamma (1-s))-s-(1-s)*Real.log (1-s) := by
  have hp : 0<1-s := by linarith
  have hgp : 0<Real.Gamma (1-s) := Real.Gamma_pos_of_pos hp
  rw [gamma_deficit_mgf s hs]
  rw [Real.log_mul (mul_ne_zero (Real.exp_ne_zero _) (Real.rpow_pos_of_pos
      (one_div_pos.mpr hp) _).ne') (Real.Gamma_pos_of_pos (by linarith : 0<2-s)).ne',
    Real.log_mul (Real.exp_ne_zero _) (Real.rpow_pos_of_pos (one_div_pos.mpr hp) _).ne',
    Real.log_exp, Real.log_rpow (one_div_pos.mpr hp)]
  have hg : Real.Gamma (2-s)=(1-s)*Real.Gamma (1-s) := by
    convert Real.Gamma_add_one hp.ne' using 1
    congr 1
    ring
  rw [hg,Real.log_mul hp.ne' hgp.ne',Real.log_div one_ne_zero hp.ne',Real.log_one]
  ring

theorem deficit_cgf_correction_series (s : ℝ) (hs : |s|<1) :
    HasSum (fun n : ℕ => s^(n+2)/(((n:ℝ)+1)*((n:ℝ)+2)))
      (s+(1-s)*Real.log (1-s)) := by
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one hs).mul_left s
  have ht := euler_log_gamma_term_series s hs 0
  have hh := h.sub ht
  convert hh using 1
  · funext n
    simp only [eulerLogGammaDoubleTerm,Nat.cast_zero,zero_add,div_one]
    have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
    have hn2 : (n:ℝ)+2 ≠ 0 := by positivity
    rw [pow_succ s (n+1)]
    field_simp
    ring
  · simp only [eulerLogGammaTerm,Nat.cast_zero,zero_add,div_one]
    ring

/-- The explicit deficit cumulant-generating series, with no unproved
analytic-series assumption. The zeta coefficients are identified with the
native Riemann zeta function by `natural_zeta_riemann`. -/
theorem deficit_cgf_zeta_series (s : ℝ) (hs : |s|<1) :
    HasSum (fun n : ℕ =>
      (naturalZeta (n+2)-1/((n:ℝ)+1))*s^(n+2)/((n:ℝ)+2))
      (Real.log (∫ v : ℝ, Real.exp (s*v) ∂gammaDeficitProbability)-
        Real.eulerMascheroniConstant*s) := by
  have h := (log_gamma_zeta_series s hs).sub (deficit_cgf_correction_series s hs)
  convert h using 1
  · funext n
    have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
    have hn2 : (n:ℝ)+2 ≠ 0 := by positivity
    field_simp
    ring
  · rw [deficit_cgf_log_gamma s (lt_of_le_of_lt (le_abs_self s) hs)]
    ring

end
end Sigma
