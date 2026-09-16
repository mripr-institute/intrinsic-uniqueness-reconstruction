import SigmaProbLogMoments
import SigmaProbEntropyCalibration

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

def entropyPerturbationCoefficient (n : ℕ) : ℝ :=
  if n=0 then -12 else if n=1 then 24 else if n=2 then -10 else 1

def entropyPerturbationPolynomial (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 4, entropyPerturbationCoefficient n*t^n

def entropyPerturbationWeight (t : ℝ) := 1+entropyPerturbationPolynomial t/2024

def entropyCounterdensity (t : ℝ) := SigmaPresentations.density t*entropyPerturbationWeight t

theorem entropy_perturbation_polynomial_formula (t : ℝ) :
    entropyPerturbationPolynomial t = t^3-10*t^2+24*t-12 := by
  norm_num [entropyPerturbationPolynomial,entropyPerturbationCoefficient,Finset.sum_range_succ]
  ring

theorem entropy_perturbation_polynomial_lower_bound (t : ℝ) (ht : 0 ≤ t) :
    -1012 ≤ entropyPerturbationPolynomial t := by
  rw [entropy_perturbation_polynomial_formula]
  rcases le_or_gt t 10 with h | h
  · have ht2 : t^2 ≤ 100 := by nlinarith
    have ht3 : 0 ≤ t^3 := pow_nonneg ht _
    nlinarith
  · have hh : 0 ≤ t^2*(t-10) := mul_nonneg (sq_nonneg t) (by linarith)
    nlinarith

theorem entropy_perturbation_weight_positive (t : ℝ) (ht : 0 ≤ t) :
    0 < entropyPerturbationWeight t := by
  have hh := entropy_perturbation_polynomial_lower_bound t ht
  unfold entropyPerturbationWeight
  linarith

theorem entropy_perturbation_monomial_integrable (m : ℕ) :
    Integrable (fun t : ℝ => entropyPerturbationPolynomial t*t^m) gammaProbability := by
  have he : (fun t : ℝ => entropyPerturbationPolynomial t*t^m) =
      fun t => ∑ n ∈ Finset.range 4, entropyPerturbationCoefficient n*t^(n+m) := by
    funext t
    simp only [entropyPerturbationPolynomial,Finset.sum_mul,pow_add]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [he]
  exact integrable_finset_sum _ (fun n _ => (gamma_probability_monomial_integrable (n+m)).const_mul _)

theorem entropy_perturbation_monomial_integral (m : ℕ) :
    (∫ t : ℝ, entropyPerturbationPolynomial t*t^m ∂gammaProbability) =
      ∑ n ∈ Finset.range 4, entropyPerturbationCoefficient n*((n+m+1).factorial : ℝ) := by
  have he : (fun t : ℝ => entropyPerturbationPolynomial t*t^m) =
      fun t => ∑ n ∈ Finset.range 4, entropyPerturbationCoefficient n*t^(n+m) := by
    funext t
    simp only [entropyPerturbationPolynomial,Finset.sum_mul,pow_add]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [he,integral_finset_sum _ (fun n _ => (gamma_probability_monomial_integrable (n+m)).const_mul _)]
  simp only [integral_mul_left,gamma_probability_moments]

theorem entropy_perturbation_mass_zero :
    (∫ t : ℝ, entropyPerturbationPolynomial t ∂gammaProbability) = 0 := by
  have hh := entropy_perturbation_monomial_integral 0
  norm_num [entropyPerturbationCoefficient,Finset.sum_range_succ,Nat.factorial] at hh
  exact hh

theorem entropy_perturbation_first_zero :
    (∫ t : ℝ, entropyPerturbationPolynomial t*t ∂gammaProbability) = 0 := by
  have hh := entropy_perturbation_monomial_integral 1
  norm_num [entropyPerturbationCoefficient,Finset.sum_range_succ,Nat.factorial] at hh
  exact hh

def smallGammaLogMoment (n : ℕ) : ℝ :=
  if n=0 then 1-Real.eulerMascheroniConstant else
  if n=1 then 3-2*Real.eulerMascheroniConstant else
  if n=2 then 11-6*Real.eulerMascheroniConstant else 50-24*Real.eulerMascheroniConstant

theorem gamma_small_log_moment (n : ℕ) (hn : n < 4) :
    (∫ t : ℝ, t^n*Real.log t ∂gammaProbability) = smallGammaLogMoment n := by
  interval_cases n
  · simpa [smallGammaLogMoment] using gamma_probability_expected_log
  · simpa [smallGammaLogMoment] using gamma_log_moment_one
  · simpa [smallGammaLogMoment] using gamma_log_moment_two
  · simpa [smallGammaLogMoment] using gamma_log_moment_three

theorem gamma_small_log_moment_integrable (n : ℕ) (hn : n < 4) :
    Integrable (fun t : ℝ => t^n*Real.log t) gammaProbability := by
  apply Integrable.of_integral_ne_zero
  rw [gamma_small_log_moment n hn]
  have hh := Real.eulerMascheroniConstant_lt_two_thirds
  interval_cases n <;> norm_num [smallGammaLogMoment] <;> linarith

theorem entropy_perturbation_log_expansion :
    (fun t : ℝ => entropyPerturbationPolynomial t*Real.log t) =
      fun t => ∑ n ∈ Finset.range 4, entropyPerturbationCoefficient n*(t^n*Real.log t) := by
  funext t
  simp only [entropyPerturbationPolynomial,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem entropy_perturbation_log_integrable :
    Integrable (fun t : ℝ => entropyPerturbationPolynomial t*Real.log t) gammaProbability := by
  rw [entropy_perturbation_log_expansion]
  exact integrable_finset_sum _ (fun n hn =>
    (gamma_small_log_moment_integrable n (Finset.mem_range.mp hn)).const_mul _)

theorem entropy_perturbation_log_zero :
    (∫ t : ℝ, entropyPerturbationPolynomial t*Real.log t ∂gammaProbability) = 0 := by
  rw [entropy_perturbation_log_expansion,integral_finset_sum _ (fun n hn =>
    (gamma_small_log_moment_integrable n (Finset.mem_range.mp hn)).const_mul _)]
  simp only [integral_mul_left]
  have he : (∑ n ∈ Finset.range 4, entropyPerturbationCoefficient n*
      (∫ t : ℝ, t^n*Real.log t ∂gammaProbability)) =
      ∑ n ∈ Finset.range 4, entropyPerturbationCoefficient n*smallGammaLogMoment n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [gamma_small_log_moment n (Finset.mem_range.mp hn)]
  rw [he]
  norm_num [entropyPerturbationCoefficient,smallGammaLogMoment,Finset.sum_range_succ]
  ring

theorem entropy_weight_integrable (f : ℝ → ℝ) (hf : Integrable f gammaProbability)
    (hq : Integrable (fun t => entropyPerturbationPolynomial t*f t) gammaProbability) :
    Integrable (fun t => entropyPerturbationWeight t*f t) gammaProbability := by
  apply (hf.add (hq.div_const 2024)).congr
  filter_upwards with t
  dsimp only [Pi.add_apply]
  unfold entropyPerturbationWeight
  ring

theorem entropy_weight_integral (f : ℝ → ℝ) (hf : Integrable f gammaProbability)
    (hq : Integrable (fun t => entropyPerturbationPolynomial t*f t) gammaProbability) :
    (∫ t : ℝ, entropyPerturbationWeight t*f t ∂gammaProbability) =
      (∫ t : ℝ, f t ∂gammaProbability)+
      (∫ t : ℝ, entropyPerturbationPolynomial t*f t ∂gammaProbability)/2024 := by
  have he : (fun t => entropyPerturbationWeight t*f t) =
      (fun t => f t+(entropyPerturbationPolynomial t*f t)/2024) := by
    funext t
    unfold entropyPerturbationWeight
    ring
  rw [he,integral_add hf (hq.div_const 2024),integral_div]

theorem entropy_counterdensity_integral (f : ℝ → ℝ) :
    (∫ t : ℝ in Ioi 0, entropyCounterdensity t*f t) =
      ∫ t : ℝ, entropyPerturbationWeight t*f t ∂gammaProbability := by
  rw [gamma_probability_integral]
  apply integral_congr_ae
  filter_upwards with t
  unfold entropyCounterdensity
  ring

theorem entropy_counterdensity_integrable (f : ℝ → ℝ)
    (hi : Integrable (fun t => entropyPerturbationWeight t*f t) gammaProbability) :
    IntegrableOn (fun t => entropyCounterdensity t*f t) (Ioi (0 : ℝ)) := by
  apply ((gamma_density_integrability _).mp hi).congr
  filter_upwards with t
  unfold entropyCounterdensity
  ring

theorem entropy_counterdensity_contDiff : ContDiff ℝ ⊤ entropyCounterdensity := by
  have he : entropyCounterdensity = fun t : ℝ => t*Real.exp (-t)*
      (1+(t^3-10*t^2+24*t-12)/2024) := by
    funext t
    rw [entropyCounterdensity,entropyPerturbationWeight,entropy_perturbation_polynomial_formula]
    rfl
  rw [he]
  simp only [div_eq_mul_inv]
  fun_prop

theorem entropy_counterdensity_positive (t : ℝ) (ht : 0 < t) :
    0 < entropyCounterdensity t :=
  mul_pos (SigmaPresentations.density_pos ht) (entropy_perturbation_weight_positive t ht.le)

theorem entropy_counterdensity_calibrated :
    CalibratedGammaDensity entropyCounterdensity (1-Real.eulerMascheroniConstant) := by
  have hq0 : Integrable (fun t => entropyPerturbationPolynomial t*(1 : ℝ)) gammaProbability := by
    simpa using entropy_perturbation_monomial_integrable 0
  have hq1 : Integrable (fun t : ℝ => entropyPerturbationPolynomial t*t) gammaProbability := by
    simpa using entropy_perturbation_monomial_integrable 1
  have hi1 : Integrable (fun t : ℝ => t) gammaProbability := by
    simpa using gamma_probability_monomial_integrable 1
  constructor
  · exact entropy_counterdensity_contDiff.continuous.measurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (entropy_counterdensity_positive t ht).le
  · have he := entropy_counterdensity_integral (fun _ => (1 : ℝ))
    rw [entropy_weight_integral _ (integrable_const _) hq0] at he
    simpa [entropy_perturbation_mass_zero] using he
  · have he := entropy_counterdensity_integral (fun t : ℝ => t)
    rw [entropy_weight_integral _ hi1 hq1,entropy_perturbation_first_zero] at he
    have hm : (∫ t : ℝ, t ∂gammaProbability) = 2 := gamma_probability_mean
    rw [hm] at he
    simpa [mul_comm] using he
  · exact entropy_counterdensity_integrable Real.log
      (entropy_weight_integrable Real.log gamma_probability_log_integrable entropy_perturbation_log_integrable)
  · rw [entropy_counterdensity_integral,
      entropy_weight_integral Real.log gamma_probability_log_integrable entropy_perturbation_log_integrable,
      entropy_perturbation_log_zero,gamma_probability_expected_log]
    ring

theorem entropy_counterdensity_not_ae_gamma :
    ¬ entropyCounterdensity =ᵐ[volume.restrict (Ioi (0 : ℝ))] SigmaPresentations.density := by
  intro he
  have hp : Continuous SigmaPresentations.density := by unfold SigmaPresentations.density; fun_prop
  have hh := Measure.eqOn_open_of_ae_eq he isOpen_Ioi entropy_counterdensity_contDiff.continuous.continuousOn
    hp.continuousOn
  have h1 := hh (show (1 : ℝ) ∈ Ioi 0 by norm_num)
  norm_num [entropyCounterdensity,entropyPerturbationWeight,entropy_perturbation_polynomial_formula] at h1
  have hp1 := SigmaPresentations.density_pos (by norm_num : (0 : ℝ)<1)
  nlinarith

/-- An explicit smooth positive density retains mass, mean, and logarithmic mean
but is not the entropy maximizer. -/
theorem calibrated_moments_do_not_identify_gamma :
    ∃ f : ℝ → ℝ, ContDiff ℝ ⊤ f ∧ (∀ t > 0, 0 < f t) ∧
      CalibratedGammaDensity f (1-Real.eulerMascheroniConstant) ∧
      ¬ f =ᵐ[volume.restrict (Ioi (0 : ℝ))] SigmaPresentations.density :=
  ⟨entropyCounterdensity,entropy_counterdensity_contDiff,entropy_counterdensity_positive,
    entropy_counterdensity_calibrated,entropy_counterdensity_not_ae_gamma⟩


theorem entropy_counterdensity_strict_entropy :
    calibratedExtendedEntropy (1+Real.eulerMascheroniConstant) entropyCounterdensity <
      ((1+Real.eulerMascheroniConstant : ℝ) : EReal) := by
  have hh := calibrated_gamma_maximum_entropy entropyCounterdensity entropy_counterdensity_calibrated
  exact lt_of_le_of_ne hh.1 (fun he => entropy_counterdensity_not_ae_gamma (hh.2.mp he))

end
end Sigma
