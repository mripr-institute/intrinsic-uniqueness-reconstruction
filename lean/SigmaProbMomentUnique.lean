import SigmaProbMGFUnique
import SigmaOpMomentGrowth
import SigmaProbDeficitTransform

namespace Sigma
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

theorem exponential_series_integral (μ : Measure ℝ) (s : ℝ)
    (hi : Integrable (fun t : ℝ => Real.exp (|s| * |t|)) μ) :
    HasSum (fun n : ℕ => ∫ t : ℝ, opExpTerm s n t ∂μ)
      (∫ t : ℝ, Real.exp (s*t) ∂μ) := by
  apply hasSum_integral_of_dominated_convergence (fun n t => ‖opExpTerm s n t‖)
  · intro n
    exact (by unfold opExpTerm; fun_prop : Continuous (opExpTerm s n)).aestronglyMeasurable
  · intro n
    exact Eventually.of_forall (fun t => le_refl _)
  · exact Eventually.of_forall (fun t => (opExpTerm_norm_hasSum s t).summable)
  · simpa only [(opExpTerm_norm_hasSum s _).tsum_eq] using hi
  · exact Eventually.of_forall (opExpTerm_hasSum s)

theorem exp_terms_equal_of_moments (μ ν : Measure ℝ)
    (hm : ∀ n : ℕ, (∫ t : ℝ, t^n ∂μ) = ∫ t : ℝ, t^n ∂ν) (s : ℝ) (n : ℕ) :
    (∫ t : ℝ, opExpTerm s n t ∂μ) = ∫ t : ℝ, opExpTerm s n t ∂ν := by
  simp only [opExpTerm, mul_pow, integral_div, integral_mul_left, hm n]

theorem cosh_envelope_integrable (μ : Measure ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hi : Integrable (fun t : ℝ => Real.exp (c*|t|)) μ) :
    Integrable (fun t : ℝ => Real.cosh (c*t)) μ := by
  apply hi.mono' ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
  filter_upwards with t
  change ‖Real.cosh (c*t)‖ ≤ Real.exp (c*|t|)
  rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _), Real.cosh_eq]
  have h1 : Real.exp (c*t) ≤ Real.exp (c*|t|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _) hc)
  have h2 : Real.exp (-(c*t)) ≤ Real.exp (c*|t|) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (neg_le_abs t) hc
    nlinarith
  linarith

theorem cosh_series_integral (μ : Measure ℝ) (c : ℝ)
    (hi : Integrable (fun t : ℝ => Real.cosh (c*t)) μ) :
    HasSum (fun n : ℕ => ∫ t : ℝ, opCoshTerm c n t ∂μ)
      (∫ t : ℝ, Real.cosh (c*t) ∂μ) := by
  have hsum (t : ℝ) : HasSum (fun n => opCoshTerm c n t) (Real.cosh (c*t)) :=
    Real.hasSum_cosh (c*t)
  apply hasSum_integral_of_dominated_convergence (fun n t => opCoshTerm c n t)
  · intro n
    exact (by unfold opCoshTerm; fun_prop : Continuous (opCoshTerm c n)).aestronglyMeasurable
  · intro n
    exact Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg (opCoshTerm_nonneg _ _ _)]
  · exact Eventually.of_forall (fun t => (hsum t).summable)
  · simpa only [(hsum _).tsum_eq] using hi
  · exact Eventually.of_forall hsum

/-- A target exponential moment and matching finite ordinary moments force a
candidate exponential envelope on the full real line. -/
theorem moments_force_exponential_envelope (μ ν : Measure ℝ)
    [IsProbabilityMeasure ν] (c : ℝ) (hc : 0 ≤ c)
    (hν : Integrable (fun t : ℝ => Real.exp (c*|t|)) ν)
    (hi : ∀ n : ℕ, Integrable (fun t : ℝ => t^n) μ)
    (hm : ∀ n : ℕ, (∫ t : ℝ, t^n ∂μ) = ∫ t : ℝ, t^n ∂ν) :
    Integrable (fun t : ℝ => Real.exp (c*|t|)) μ := by
  have hvcosh := cosh_envelope_integrable ν c hc hν
  have hsν := cosh_series_integral ν c hvcosh
  have he (n : ℕ) : (∫ t, opCoshTerm c n t ∂μ) = ∫ t, opCoshTerm c n t ∂ν := by
    simp only [opCoshTerm, mul_pow, integral_div, integral_mul_left, hm (2*n)]
  have hnorm : Summable (fun n : ℕ => ∫ t, ‖opCoshTerm c n t‖ ∂μ) := by
    simp_rw [Real.norm_of_nonneg (opCoshTerm_nonneg _ _ _), he]
    exact hsν.summable
  have hic (n : ℕ) : Integrable (opCoshTerm c n) μ := by
    change Integrable (fun t => (c*t)^(2*n)/((2*n).factorial : ℝ)) μ
    simpa only [mul_pow] using
      ((hi (2*n)).const_mul (c^(2*n))).div_const ((2*n).factorial : ℝ)
  have hh := hasSum_integral_of_summable_integral_norm hic hnorm
  have heq : (∫ t, Real.cosh (c*t) ∂μ) = ∫ t, Real.cosh (c*t) ∂ν := by
    have hhh := hh.tsum_eq.symm
    simp_rw [he] at hhh
    simpa only [opCoshTerm, ← Real.cosh_eq_tsum] using hhh.trans hsν.tsum_eq
  have hp : 0 < ∫ t : ℝ, Real.cosh (c*t) ∂ν := by
    rw [integral_pos_iff_support_of_nonneg (fun t => (Real.cosh_pos _).le) hvcosh]
    have hsupp : Function.support (fun t : ℝ => Real.cosh (c*t)) = univ := by
      ext t
      simp [Function.mem_support, (Real.cosh_pos (c*t)).ne']
    simp [hsupp]
  have hμcosh : Integrable (fun t : ℝ => Real.cosh (c*t)) μ :=
    Integrable.of_integral_ne_zero (heq.trans_ne hp.ne')
  apply (hμcosh.const_mul 2).mono'
    ((continuous_const.mul continuous_id.abs).rexp.aestronglyMeasurable)
  filter_upwards with t
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact op_exp_abs_le_twice_cosh c t

/-- Full-real-line moment determinacy with a single exponential envelope on the
specified target.  No exponential integrability or support is assumed for μ. -/
theorem probability_moment_unique_of_target_exponential (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (c : ℝ) (hc : 0 < c)
    (hν : Integrable (fun t : ℝ => Real.exp (c*|t|)) ν)
    (hi : ∀ n : ℕ, Integrable (fun t : ℝ => t^n) μ)
    (hm : ∀ n : ℕ, (∫ t : ℝ, t^n ∂μ) = ∫ t : ℝ, t^n ∂ν) : μ = ν := by
  have hμ := moments_force_exponential_envelope μ ν c hc.le hν hi hm
  have envelope (ρ : Measure ℝ) (hρ : Integrable (fun t : ℝ => Real.exp (c*|t|)) ρ)
      (s : ℝ) (hs : |s| < c) : Integrable (fun t : ℝ => Real.exp (|s| * |t|)) ρ := by
    apply hρ.mono' ((continuous_const.mul continuous_id.abs).rexp.aestronglyMeasurable)
    filter_upwards with t
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs.le (abs_nonneg _))
  have expint (ρ : Measure ℝ) (hρ : Integrable (fun t : ℝ => Real.exp (c*|t|)) ρ)
      (s : ℝ) (hs : |s| < c) : Integrable (fun t : ℝ => Real.exp (s*t)) ρ := by
    apply (envelope ρ hρ s hs).mono'
      ((continuous_const.mul continuous_id).rexp.aestronglyMeasurable)
    filter_upwards with t
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    simpa only [abs_mul] using le_abs_self (s*t)
  apply finite_measure_local_mgf_unique μ ν c hc (expint μ hμ) (expint ν hν)
  intro s hs
  have hsm := exponential_series_integral μ s (envelope μ hμ s hs)
  have hsn := exponential_series_integral ν s (envelope ν hν s hs)
  simp_rw [exp_terms_equal_of_moments μ ν hm] at hsm
  exact hsm.unique hsn

/-- Moment identification of the actual Gamma deficit law.  The candidate needs
only its finite moments, not an additional exponential-moment hypothesis. -/
theorem gamma_deficit_moments_identify_real_line_probability (μ : Measure ℝ)
    [IsProbabilityMeasure μ]
    (hi : ∀ n : ℕ, Integrable (fun t : ℝ => t^n) μ)
    (hm : ∀ n : ℕ, (∫ t : ℝ, t^n ∂μ) = ∫ t : ℝ, t^n ∂gammaDeficitProbability) :
    μ = gammaDeficitProbability := by
  apply probability_moment_unique_of_target_exponential μ gammaDeficitProbability
    (1/2) (by norm_num) _ hi hm
  apply (gamma_deficit_exponential_integrable (1/2) (by norm_num)).congr
  filter_upwards [gamma_deficit_nonnegative] with t ht
  rw [abs_of_nonneg ht]

/-- The standard algebraic moment-cumulant recurrence, including its marked
order.  It does not require an a priori convergent candidate MGF. -/
def AlgebraicCumulantRecurrence (μ : Measure ℝ) (κ : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, (∫ t : ℝ, t^(n+1) ∂μ) =
    ∑ j ∈ Finset.range (n+1), (Nat.choose n j : ℝ)*κ (j+1)*(∫ t : ℝ, t^(n-j) ∂μ)

theorem probability_moments_eq_of_algebraic_cumulants (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (κ : ℕ → ℝ)
    (hμ : AlgebraicCumulantRecurrence μ κ) (hν : AlgebraicCumulantRecurrence ν κ) :
    ∀ n : ℕ, (∫ t : ℝ, t^n ∂μ) = ∫ t : ℝ, t^n ∂ν := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [hμ n, hν n]
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih (n-j) (by omega)]

/-- Once the target cumulant values are calibrated, the recurrence and target
exponential envelope give the deficit inverse with no candidate MGF premise. -/
theorem gamma_deficit_algebraic_cumulants_identify (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (κ : ℕ → ℝ)
    (hi : ∀ n : ℕ, Integrable (fun t : ℝ => t^n) μ)
    (hμ : AlgebraicCumulantRecurrence μ κ)
    (hγ : AlgebraicCumulantRecurrence gammaDeficitProbability κ) :
    μ = gammaDeficitProbability := by
  apply gamma_deficit_moments_identify_real_line_probability μ hi
  exact probability_moments_eq_of_algebraic_cumulants μ gammaDeficitProbability κ hμ hγ

end
end Sigma
