import SigmaOpLaguerreOrthogonal
import SigmaProbMomentUnique

namespace Sigma
noncomputable section
open MeasureTheory Filter Polynomial
open scoped Topology ENNReal NNReal

theorem finite_measure_moments_unique_of_exponential_envelopes (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : ℝ) (hc : 0 < c)
    (hμ : Integrable (fun t : ℝ => Real.exp (c * |t|)) μ)
    (hν : Integrable (fun t : ℝ => Real.exp (c * |t|)) ν)
    (hm : ∀ n : ℕ, (∫ t : ℝ, t^n ∂μ) = ∫ t : ℝ, t^n ∂ν) : μ = ν := by
  have envelope (ρ : Measure ℝ) (hρ : Integrable (fun t : ℝ => Real.exp (c*|t|)) ρ)
      (s : ℝ) (hs : |s| < c) : Integrable (fun t : ℝ => Real.exp (|s| * |t|)) ρ := by
    apply hρ.mono' ((continuous_const.mul continuous_id.abs).rexp.aestronglyMeasurable)
    filter_upwards with t
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs.le (abs_nonneg _))
  have expint (ρ : Measure ℝ) (hρ : Integrable (fun t : ℝ => Real.exp (c*|t|)) ρ)
      (s : ℝ) (hs : |s| < c) : Integrable (fun t : ℝ => Real.exp (s*t)) ρ := by
    apply (envelope ρ hρ s hs).mono' ((continuous_const.mul continuous_id).rexp.aestronglyMeasurable)
    filter_upwards with t
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    simpa only [abs_mul] using le_abs_self (s*t)
  apply finite_measure_local_mgf_unique μ ν c hc (expint μ hμ) (expint ν hν)
  intro s hs
  have h1 := exponential_series_integral μ s (envelope μ hμ s hs)
  have h2 := exponential_series_integral ν s (envelope ν hν s hs)
  simp_rw [exp_terms_equal_of_moments μ ν hm] at h1
  exact h1.unique h2

theorem real_mem_l2_product_integrable {μ : Measure ℝ} {f g : ℝ → ℝ}
    (hf : Memℒp f 2 μ) (hg : Memℒp g 2 μ) : Integrable (fun t => f t * g t) μ := by
  simpa only [Pi.smul_apply, smul_eq_mul] using
    memℒp_one_iff_integrable.mp (hg.smul hf (by
      simp only [div_one, one_div, ENNReal.inv_two_add_inv_two] : (1 : ℝ≥0∞)/1 = 1/2+1/2))

theorem real_nonnegative_density_integral (μ : Measure ℝ) (a f : ℝ → ℝ)
    (ha : Measurable a) (ha0 : ∀ t, 0 ≤ a t) :
    (∫ t, f t ∂μ.withDensity (fun t => ENNReal.ofReal (a t))) =
      ∫ t, a t * f t ∂μ := by
  change (∫ t, f t ∂μ.withDensity (fun t => (Real.toNNReal (a t) : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul ha.real_toNNReal]
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (ha0 _)]

theorem real_nonnegative_density_integrable (μ : Measure ℝ) (a f : ℝ → ℝ)
    (ha : Measurable a) (ha0 : ∀ t, 0 ≤ a t)
    (hi : Integrable (fun t => a t * f t) μ) :
    Integrable f (μ.withDensity (fun t => ENNReal.ofReal (a t))) := by
  apply (integrable_withDensity_iff_integrable_smul' ha.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  simpa only [ENNReal.toReal_ofReal (ha0 _), smul_eq_mul] using hi

/-- A real square-integrable function annihilating all polynomial moments is
zero when the underlying finite measure has a square-integrable exponential
envelope. The signed density is split into two actual finite positive measures. -/
theorem real_mem_l2_zero_of_moments (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Measurable f) (hf2 : Memℒp f 2 μ)
    (hp : ∀ n : ℕ, Memℒp (fun t : ℝ => t^n) 2 μ)
    (c : ℝ) (hc : 0 < c)
    (he : Memℒp (fun t : ℝ => Real.exp (c*|t|)) 2 μ)
    (hm : ∀ n : ℕ, (∫ t : ℝ, f t * t^n ∂μ) = 0) : f =ᵐ[μ] 0 := by
  let a : ℝ → ℝ := fun t => |f t| + f t
  let b : ℝ → ℝ := fun t => |f t| - f t
  have ha : Measurable a := (continuous_abs.measurable.comp hf).add hf
  have hb : Measurable b := (continuous_abs.measurable.comp hf).sub hf
  have ha0 : ∀ t, 0 ≤ a t := fun t => by dsimp [a]; linarith [neg_abs_le (f t)]
  have hb0 : ∀ t, 0 ≤ b t := fun t => sub_nonneg.mpr (le_abs_self (f t))
  have habs : Memℒp (fun t => |f t|) 2 μ := by
    simpa only [Real.norm_eq_abs] using hf2.norm
  have ha2 : Memℒp a 2 μ := habs.add hf2
  have hb2 : Memℒp b 2 μ := habs.sub hf2
  let μa := μ.withDensity (fun t => ENNReal.ofReal (a t))
  let μb := μ.withDensity (fun t => ENNReal.ofReal (b t))
  letI : IsFiniteMeasure μa := isFiniteMeasure_withDensity_ofReal
    (ha2.integrable (by norm_num)).2
  letI : IsFiniteMeasure μb := isFiniteMeasure_withDensity_ofReal
    (hb2.integrable (by norm_num)).2
  have heq : μa = μb := by
    apply finite_measure_moments_unique_of_exponential_envelopes μa μb c hc
    · exact real_nonnegative_density_integrable μ a _ ha ha0
        (real_mem_l2_product_integrable ha2 he)
    · exact real_nonnegative_density_integrable μ b _ hb hb0
        (real_mem_l2_product_integrable hb2 he)
    · intro n
      rw [real_nonnegative_density_integral μ a _ ha ha0,
        real_nonnegative_density_integral μ b _ hb hb0]
      dsimp [a,b]
      simp only [add_mul, sub_mul, integral_add
        (real_mem_l2_product_integrable habs (hp n)) (real_mem_l2_product_integrable hf2 (hp n)),
        integral_sub (real_mem_l2_product_integrable habs (hp n))
          (real_mem_l2_product_integrable hf2 (hp n)), hm n, add_zero, sub_zero]
  have hae := (withDensity_eq_iff_of_sigmaFinite ha.ennreal_ofReal.aemeasurable
    hb.ennreal_ofReal.aemeasurable).mp heq
  filter_upwards [hae] with t ht
  have hr := congrArg ENNReal.toReal ht
  simp only [ENNReal.toReal_ofReal (ha0 t), ENNReal.toReal_ofReal (hb0 t)] at hr
  change f t = 0
  dsimp [a,b] at hr
  linarith

end
end Sigma
