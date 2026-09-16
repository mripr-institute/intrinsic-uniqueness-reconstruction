import SigmaProbRelativeEntropy

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal NNReal

theorem poisson_factorial_second_hasSum (r : ℝ≥0) :
    HasSum (fun n : ℕ => (n:ℝ)*((n:ℝ)-1)*(poissonPMF r n).toReal) ((r:ℝ)^2) := by
  have hrec (n : ℕ) : ((n+2:ℕ):ℝ)*(((n+2:ℕ):ℝ)-1)*(poissonPMF r (n+2)).toReal =
      (r:ℝ)^2*(poissonPMF r n).toReal := by
    have h₁ := poisson_general_recurrence r (n+1)
    have h₂ := poisson_general_recurrence r n
    push_cast at h₁ h₂ ⊢
    nlinarith [congrArg (fun x:ℝ => ((n:ℝ)+1)*x) h₁,
      congrArg (fun x:ℝ => (r:ℝ)*x) h₂]
  have hs : HasSum (fun n:ℕ => ((n+2:ℕ):ℝ)*(((n+2:ℕ):ℝ)-1)*
      (poissonPMF r (n+2)).toReal) ((r:ℝ)^2) := by
    simpa only [hrec,mul_one] using (pmf_real_mass (poissonPMF r)).mul_left ((r:ℝ)^2)
  have hh := (hasSum_nat_add_iff
    (f := fun n:ℕ => (n:ℝ)*((n:ℝ)-1)*(poissonPMF r n).toReal) (g := (r:ℝ)^2) 2).mp hs
  simpa [Finset.sum_range_succ] using hh

theorem poisson_second_moment_hasSum (r : ℝ≥0) :
    HasSum (fun n : ℕ => (n:ℝ)^2*(poissonPMF r n).toReal) ((r:ℝ)^2+r) := by
  convert (poisson_factorial_second_hasSum r).add (poisson_general_mean_hasSum r) using 1
  funext n
  ring

theorem poisson_square_integrable (r : ℝ≥0) :
    Integrable (fun n:ℕ => (n:ℝ)^2) (poissonMeasure r) := by
  apply pmf_integrable_of_summable
  convert (poisson_second_moment_hasSum r).summable using 1
  funext n
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (n:ℝ))]

theorem poisson_general_second_moment (r : ℝ≥0) :
    (∫ n:ℕ, (n:ℝ)^2 ∂poissonMeasure r) = (r:ℝ)^2+r := by
  rw [poissonMeasure,PMF.integral_eq_tsum _ _ (poisson_square_integrable r)]
  simpa only [smul_eq_mul,mul_comm] using (poisson_second_moment_hasSum r).tsum_eq

theorem poisson_centered_square_integrable (r : ℝ≥0) :
    Integrable (fun n:ℕ => ((n:ℝ)-(r:ℝ))^2) (poissonMeasure r) := by
  convert ((poisson_square_integrable r).sub
    ((poisson_general_identity_integrable r).const_mul (2*(r:ℝ)))).add
    (integrable_const ((r:ℝ)^2)) using 1
  funext n
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

theorem poisson_general_variance (r : ℝ≥0) :
    (∫ n:ℕ, ((n:ℝ)-(r:ℝ))^2 ∂poissonMeasure r) = (r:ℝ) := by
  have he : (fun n:ℕ => ((n:ℝ)-(r:ℝ))^2) =
      (fun n:ℕ => ((n:ℝ)^2-2*(r:ℝ)*(n:ℝ))+(r:ℝ)^2) := by
    funext n; ring
  have hd : Integrable (fun n:ℕ => (n:ℝ)^2-2*(r:ℝ)*(n:ℝ)) (poissonMeasure r) :=
    (poisson_square_integrable r).sub ((poisson_general_identity_integrable r).const_mul (2*(r:ℝ)))
  rw [he,integral_add hd (integrable_const _),
    integral_sub (poisson_square_integrable r)
      ((poisson_general_identity_integrable r).const_mul (2*(r:ℝ))),
    integral_mul_left,poisson_general_second_moment,poisson_general_mean,integral_const]
  simp
  ring

def poissonNaturalRate (u : ℝ) : ℝ≥0 := ⟨Real.exp u,(Real.exp_pos u).le⟩

theorem poisson_natural_log_mass (u : ℝ) (n : ℕ) :
    Real.log (poissonPMFReal (poissonNaturalRate u) n) =
      -Real.exp u+(n:ℝ)*u-Real.log (n.factorial:ℝ) := by
  unfold poissonPMFReal poissonNaturalRate
  simp only [NNReal.coe_mk]
  rw [Real.log_div (mul_pos (Real.exp_pos _) (pow_pos (Real.exp_pos _) _)).ne' (by positivity),
    Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ (Real.exp_ne_zero _)),
    Real.log_exp,Real.log_pow,Real.log_exp]

theorem poisson_natural_score (u : ℝ) (n : ℕ) :
    HasDerivAt (fun v => Real.log (poissonPMFReal (poissonNaturalRate v) n))
      ((n:ℝ)-Real.exp u) u := by
  have hd := (((Real.hasDerivAt_exp u).neg).add
    ((hasDerivAt_id u).const_mul (n:ℝ))).sub_const (Real.log (n.factorial:ℝ))
  convert hd.congr_of_eventuallyEq (Eventually.of_forall (fun v => poisson_natural_log_mass v n)) using 1
  ring

theorem poisson_natural_fisher_information (u : ℝ) :
    (∫ n:ℕ, (deriv (fun v => Real.log (poissonPMFReal (poissonNaturalRate v) n)) u)^2
      ∂poissonMeasure (poissonNaturalRate u)) = Real.exp u := by
  simp_rw [(poisson_natural_score u _).deriv]
  exact poisson_general_variance (poissonNaturalRate u)

def poissonExponentialTilt (u : ℝ) : Measure ℕ :=
  (∫⁻ n:ℕ, ENNReal.ofReal (Real.exp ((n:ℝ)*u)) ∂poissonMeasure 1)⁻¹ •
    (poissonMeasure 1).withDensity (fun n => ENNReal.ofReal (Real.exp ((n:ℝ)*u)))

theorem poisson_tilt_normalizer (u : ℝ) :
    (∫⁻ n:ℕ, ENNReal.ofReal (Real.exp ((n:ℝ)*u)) ∂poissonMeasure 1) =
      ENNReal.ofReal (Real.exp (Real.exp u-1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (poisson_exponential_integrable u)]
  · rw [poisson_probability_mgf]
  · exact ae_of_all _ (fun _ => (Real.exp_pos _).le)

theorem poisson_exponential_tilt_law (u : ℝ) :
    poissonExponentialTilt u = poissonMeasure (poissonNaturalRate u) := by
  apply Measure.ext_of_singleton
  intro n
  rw [poissonExponentialTilt,poisson_tilt_normalizer,Measure.smul_apply,
    withDensity_apply _ (measurableSet_singleton _),lintegral_singleton]
  simp only [poissonMeasure,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),smul_eq_mul]
  change (ENNReal.ofReal (Real.exp (Real.exp u-1)))⁻¹*
    (ENNReal.ofReal (Real.exp ((n:ℝ)*u))*ENNReal.ofReal (poissonPMFReal 1 n)) =
      ENNReal.ofReal (poissonPMFReal (poissonNaturalRate u) n)
  rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.exp_pos _).le)]
  congr 1
  unfold poissonPMFReal poissonNaturalRate
  simp only [NNReal.coe_mk,NNReal.coe_one,one_pow,mul_one]
  rw [← Real.exp_nat_mul,← Real.exp_neg,← Real.exp_add]
  field_simp
  simp_rw [← Real.exp_add]
  congr 1
  ring

end
end Sigma
