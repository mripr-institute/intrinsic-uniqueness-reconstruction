import SigmaProbWeights
import SigmaProbGammaShift
import SigmaProbCumulants

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal NNReal

/-- Exponential weighting changes the rate of the actual Gamma measure. -/
theorem gamma_rate_exponential_weight (b θ : ℝ) (hθ : θ < b) :
    (gammaMeasure 2 b).withDensity (exponentialWeight θ) =
      ENNReal.ofReal (b^2 / (b-θ)^2) • gammaMeasure 2 (b-θ) := by
  change (volume.withDensity (fun t => ENNReal.ofReal (gammaPDFReal 2 b t))).withDensity
    (exponentialWeight θ) = ENNReal.ofReal (b^2/(b-θ)^2) •
      volume.withDensity (fun t => ENNReal.ofReal (gammaPDFReal 2 (b-θ) t))
  rw [← withDensity_mul volume
    (measurable_gammaPDFReal 2 b).ennreal_ofReal (exponential_weight_measurable θ),
    ← withDensity_smul _ (measurable_gammaPDFReal 2 (b-θ)).ennreal_ofReal]
  apply withDensity_congr_ae
  filter_upwards with t
  change ENNReal.ofReal (gammaPDFReal 2 b t) * ENNReal.ofReal (Real.exp (θ*t)) =
    ENNReal.ofReal (b^2/(b-θ)^2) * ENNReal.ofReal (gammaPDFReal 2 (b-θ) t)
  by_cases ht : 0 ≤ t
  · rw [gamma_shape_two_density b t ht, gamma_shape_two_density (b-θ) t ht,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_assoc (b^2*t), ← Real.exp_add]
    have he : -(b*t)+θ*t = -((b-θ)*t) := by ring
    rw [he]
    field_simp [ne_of_gt (sub_pos.mpr hθ)]
    ring
  · simp [gammaPDFReal, ht]

theorem gamma_rate_tilt_normalizer (b θ : ℝ) (hθ : θ < b) :
    (∫⁻ t, exponentialWeight θ t ∂gammaMeasure 2 b) =
      ENNReal.ofReal (b^2/(b-θ)^2) := by
  haveI : IsProbabilityMeasure (gammaMeasure 2 (b-θ)) :=
    isProbabilityMeasureGamma (by norm_num) (by linarith)
  have he := congrArg (fun μ : Measure ℝ => μ univ) (gamma_rate_exponential_weight b θ hθ)
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] using he

theorem gamma_rate_tilt_normalizer_infinite (b θ : ℝ) (hb : 0 < b) (hθ : b ≤ θ) :
    (∫⁻ t, exponentialWeight θ t ∂gammaMeasure 2 b) = ∞ := by
  change (∫⁻ t, exponentialWeight θ t ∂volume.withDensity
    (fun t => ENNReal.ofReal (gammaPDFReal 2 b t))) = ∞
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (measurable_gammaPDFReal 2 b).ennreal_ofReal (exponential_weight_measurable θ)]
  have hl : (∫⁻ t : ℝ in Ioi 1, ENNReal.ofReal (b^2)) ≤
      ∫⁻ t : ℝ, ENNReal.ofReal (gammaPDFReal 2 b t) * exponentialWeight θ t := by
    calc
      _ ≤ ∫⁻ t : ℝ in Ioi 1, ENNReal.ofReal (gammaPDFReal 2 b t) * exponentialWeight θ t := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        change (1 : ℝ) < t at ht
        rw [exponentialWeight, gamma_shape_two_density b t (by linarith : 0 ≤ t),
          ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [mul_assoc (b^2*t), ← Real.exp_add]
        have hp : 1 ≤ Real.exp (-(b*t)+θ*t) := Real.one_le_exp_iff.mpr (by nlinarith)
        calc
          b^2 = b^2*1 := by ring
          _ ≤ b^2*(t*Real.exp (-(b*t)+θ*t)) :=
            mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le ht.le hp) (sq_nonneg b)
          _ = _ := by ring
      _ ≤ _ := setLIntegral_le_lintegral _ _
  have hc : ENNReal.ofReal (b^2) ≠ 0 := (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hb)).ne'
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioi,
    ENNReal.mul_top hc] at hl
  exact top_le_iff.mp hl

theorem gamma_rate_tilt_admissible_iff (b θ : ℝ) (hb : 0 < b) :
    (∫⁻ t, exponentialWeight θ t ∂gammaMeasure 2 b) ≠ ∞ ↔ θ < b := by
  constructor
  · intro hfin
    by_contra hθ
    exact hfin (gamma_rate_tilt_normalizer_infinite b θ hb (le_of_not_gt hθ))
  · intro hθ
    rw [gamma_rate_tilt_normalizer b θ hθ]
    exact ENNReal.ofReal_ne_top

theorem gamma_rate_marked_tilt (b θ : ℝ) (hb : 0 < b) (hθ : θ < b) :
    normalizedWeight (gammaMeasure 2 b) (exponentialWeight θ) = gammaMeasure 2 (b-θ) := by
  have hc : 0 < b^2/(b-θ)^2 := div_pos (sq_pos_of_pos hb) (sq_pos_of_pos (by linarith))
  rw [normalizedWeight, gamma_rate_tilt_normalizer b θ hθ,
    gamma_rate_exponential_weight b θ hθ, smul_smul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top, one_smul]

/-- With the tilt mark forgotten, every positive input rate can give the same
fixed positive output rate. -/
theorem gamma_unmarked_tilt_rate_ambiguity (b r : ℝ) (hb : 0 < b) (hr : 0 < r) :
    normalizedWeight (gammaMeasure 2 b) (exponentialWeight (b-r)) = gammaMeasure 2 r := by
  simpa using gamma_rate_marked_tilt b (b-r) hb (by linarith)

theorem gamma_rate_mgf (b s : ℝ) (hs : s < b) :
    (∫ t : ℝ, Real.exp (s*t) ∂gammaMeasure 2 b) = b^2/(b-s)^2 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun t => (Real.exp_pos _).le)
    ((by fun_prop : Continuous (fun t : ℝ => Real.exp (s*t))).aestronglyMeasurable)]
  change (∫⁻ t, exponentialWeight s t ∂gammaMeasure 2 b).toReal = _
  rw [gamma_rate_tilt_normalizer b s hs, ENNReal.toReal_ofReal (by positivity)]

theorem gamma_rate_cgf (b s : ℝ) (hb : 0 < b) (hs : s < b) :
    probabilityCGF (gammaMeasure 2 b) s = 2*(Real.log b - Real.log (b-s)) := by
  rw [probabilityCGF, gamma_rate_mgf b s hs,
    Real.log_div (pow_ne_zero _ hb.ne') (pow_ne_zero _ (show b-s ≠ 0 by linarith)),
    Real.log_pow, Real.log_pow]
  ring

def gammaRateCGFDerivative (b : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  2*(n.factorial : ℝ)*(1/(b-s))^(n+1)

theorem gamma_rate_cgf_first_derivative (b s : ℝ) (hb : 0 < b) (hs : s < b) :
    HasDerivAt (probabilityCGF (gammaMeasure 2 b)) (gammaRateCGFDerivative b 0 s) s := by
  have hd := (((((hasDerivAt_const s b).sub (hasDerivAt_id s)).log
    (by linarith : b-s ≠ 0)).const_sub (Real.log b)).const_mul 2)
  have he : probabilityCGF (gammaMeasure 2 b) =ᶠ[𝓝 s]
      (fun u => 2*(Real.log b - Real.log (b-u))) := by
    filter_upwards [isOpen_Iio.mem_nhds hs] with u hu
    exact gamma_rate_cgf b u hb hu
  apply HasDerivAt.congr_of_eventuallyEq _ he
  convert hd using 1
  simp [gammaRateCGFDerivative]
  ring

theorem gamma_rate_cgf_derivative_step (b : ℝ) (n : ℕ) (s : ℝ) (hs : s < b) :
    HasDerivAt (gammaRateCGFDerivative b n) (gammaRateCGFDerivative b (n+1) s) s := by
  have hd := (((hasDerivAt_const s (1 : ℝ)).div
    ((hasDerivAt_const s b).sub (hasDerivAt_id s))
    (by linarith : b-s ≠ 0)).pow (n+1)).const_mul (2*(n.factorial : ℝ))
  convert hd using 1
  simp only [gammaRateCGFDerivative, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, mul_zero, zero_sub, zero_sub, sub_neg_eq_add, zero_add, mul_one,
    Nat.add_sub_cancel]
  rw [pow_succ, pow_succ]
  field_simp
  ring

theorem gamma_rate_cgf_iterated_derivative (b : ℝ) (hb : 0 < b) (n : ℕ) :
    ∀ s : ℝ, s < b → iteratedDeriv (n+1) (probabilityCGF (gammaMeasure 2 b)) s =
      gammaRateCGFDerivative b n s := by
  induction n with
  | zero =>
    intro s hs
    simpa [iteratedDeriv_succ] using (gamma_rate_cgf_first_derivative b s hb hs).deriv
  | succ n ih =>
    intro s hs
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv (n+1) (probabilityCGF (gammaMeasure 2 b)) =ᶠ[𝓝 s]
        gammaRateCGFDerivative b n := by
      filter_upwards [isOpen_Iio.mem_nhds hs] with u hu
      exact ih u hu
    exact ((gamma_rate_cgf_derivative_step b n s hs).congr_of_eventuallyEq he).deriv

theorem gamma_rate_cumulants (b : ℝ) (hb : 0 < b) (n : ℕ) :
    probabilityCumulant (gammaMeasure 2 b) (n+1) = 2*(n.factorial : ℝ)/b^(n+1) := by
  rw [probabilityCumulant, gamma_rate_cgf_iterated_derivative b hb n 0 hb]
  simp [gammaRateCGFDerivative, div_pow, div_eq_mul_inv]

theorem gamma_tilt_cumulants (θ : ℝ) (hθ : θ < 1) (n : ℕ) :
    probabilityCumulant (normalizedWeight (gammaMeasure 2 1) (exponentialWeight θ)) (n+1) =
      2*(n.factorial : ℝ)/(1-θ)^(n+1) := by
  rw [gamma_rate_marked_tilt 1 θ (by norm_num) hθ]
  exact gamma_rate_cumulants (1-θ) (by linarith) n

theorem gamma_rate_real_integral (b : ℝ) (hb : 0 < b) (f : ℝ → ℝ) :
    (∫ t, f t ∂gammaMeasure 2 b) =
      ∫ t : ℝ in Ioi 0, (b^2*t*Real.exp (-(b*t))) * f t := by
  change (∫ t, f t ∂volume.withDensity
    (fun t => ((Real.toNNReal (gammaPDFReal 2 b t) : ℝ≥0) : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul ((measurable_gammaPDFReal 2 b).real_toNNReal)]
  have he : (fun t => Real.toNNReal (gammaPDFReal 2 b t) • f t) =
      (Ici (0 : ℝ)).indicator (fun t => (b^2*t*Real.exp (-(b*t))) * f t) := by
    funext t
    rw [NNReal.smul_def, smul_eq_mul,
      Real.coe_toNNReal _ (gammaPDFReal_nonneg (by norm_num) hb t)]
    by_cases ht : 0 ≤ t
    · simp [ht, gamma_shape_two_density b t ht]
    · simp [ht, gammaPDFReal]
  rw [he, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

theorem gamma_rate_moments (b : ℝ) (hb : 0 < b) (n : ℕ) :
    (∫ t : ℝ, t^n ∂gammaMeasure 2 b) = ((n+1).factorial : ℝ) / b^n := by
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (n : ℝ)+2) (r := b) (by positivity) hb
  have hg : Real.Gamma ((n : ℝ)+2) = ((n+1).factorial : ℝ) := by
    convert Real.Gamma_nat_eq_factorial (n+1) using 1
    push_cast
    ring
  have he1 : (n : ℝ)+2-1 = ((n+1 : ℕ) : ℝ) := by push_cast; ring
  have he2 : (n : ℝ)+2 = ((n+2 : ℕ) : ℝ) := by push_cast; ring
  rw [he1, hg] at hi
  simp only [Real.rpow_natCast] at hi
  rw [he2] at hi
  simp only [Real.rpow_natCast] at hi
  calc
    _ = b^2 * ∫ t : ℝ in Ioi 0, t^(n+1)*Real.exp (-(b*t)) := by
      rw [gamma_rate_real_integral b hb, ← integral_mul_left]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      simp only [pow_succ]
      ring
    _ = _ := by
      rw [hi, pow_add, div_pow, one_pow]
      field_simp [hb.ne']
      ring

theorem gamma_rate_monomial_integrable (b : ℝ) (hb : 0 < b) (n : ℕ) :
    Integrable (fun t : ℝ => t^n) (gammaMeasure 2 b) := by
  apply Integrable.of_integral_ne_zero
  rw [gamma_rate_moments b hb n]
  exact div_ne_zero (by positivity) (pow_ne_zero _ hb.ne')

theorem gamma_rate_mean (b : ℝ) (hb : 0 < b) :
    (∫ t : ℝ, t ∂gammaMeasure 2 b) = 2/b := by
  simpa using gamma_rate_moments b hb 1

theorem gamma_rate_variance (b : ℝ) (hb : 0 < b) :
    (∫ t : ℝ, (t-2/b)^2 ∂gammaMeasure 2 b) = 2/b^2 := by
  haveI : IsProbabilityMeasure (gammaMeasure 2 b) := isProbabilityMeasureGamma (by norm_num) hb
  have h1 : Integrable (fun t : ℝ => t) (gammaMeasure 2 b) := by
    simpa using gamma_rate_monomial_integrable b hb 1
  have h2 := gamma_rate_monomial_integrable b hb 2
  have he : (fun t : ℝ => (t-2/b)^2) = fun t => t^2 - (4/b)*t + 4/b^2 := by
    funext t
    ring
  have hs : Integrable (fun t : ℝ => t^2 - (4/b)*t) (gammaMeasure 2 b) :=
    h2.sub (h1.const_mul (4/b))
  rw [he, integral_add hs (integrable_const (4/b^2 : ℝ)),
    integral_sub h2 (h1.const_mul (4/b)), integral_mul_left,
    gamma_rate_moments b hb 2, gamma_rate_mean b hb]
  simp only [integral_const, measure_univ, smul_eq_mul]
  norm_num [Nat.factorial]
  ring

theorem gamma_rates_distinct (b r : ℝ) (hb : 0 < b) (hr : 0 < r) (hne : b ≠ r) :
    gammaMeasure 2 b ≠ gammaMeasure 2 r := by
  intro he
  have hm := congrArg (fun μ : Measure ℝ => ∫ t : ℝ, t ∂μ) he
  dsimp only at hm
  rw [gamma_rate_mean b hb, gamma_rate_mean r hr] at hm
  have hh := (div_eq_div_iff hb.ne' hr.ne').mp hm
  apply hne
  linarith

/-- The marked Gamma tilt has the mean and variance displayed in Proposition 3.16. -/
theorem gamma_tilt_mean_variance (θ : ℝ) (hθ : θ < 1) :
    (∫ t : ℝ, t ∂normalizedWeight (gammaMeasure 2 1) (exponentialWeight θ)) = 2/(1-θ) ∧
    (∫ t : ℝ, (t-2/(1-θ))^2 ∂normalizedWeight (gammaMeasure 2 1) (exponentialWeight θ)) =
      2/(1-θ)^2 := by
  rw [gamma_rate_marked_tilt 1 θ (by norm_num) hθ]
  exact ⟨gamma_rate_mean _ (by linarith), gamma_rate_variance _ (by linarith)⟩

/-- Two distinct positive rates give the same observed law after distinct
unretained tilt marks. -/
theorem gamma_unmarked_tilt_counterexample (b c r : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hr : 0 < r) (hne : b ≠ c) :
    gammaMeasure 2 b ≠ gammaMeasure 2 c ∧
      normalizedWeight (gammaMeasure 2 b) (exponentialWeight (b-r)) =
        normalizedWeight (gammaMeasure 2 c) (exponentialWeight (c-r)) := by
  exact ⟨gamma_rates_distinct b c hb hc hne,
    (gamma_unmarked_tilt_rate_ambiguity b r hb hr).trans
      (gamma_unmarked_tilt_rate_ambiguity c r hc hr).symm⟩

end
end Sigma
