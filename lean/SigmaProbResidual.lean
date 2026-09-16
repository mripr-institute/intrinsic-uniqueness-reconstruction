import SigmaProbContraction

namespace Sigma
noncomputable section
open Filter MeasureTheory Set ProbabilityTheory
open scoped Topology ENNReal NNReal

def unitExpProbability : Measure ℝ := gammaMeasure 1 1

instance unitExpProbability_is_probability : IsProbabilityMeasure unitExpProbability :=
  isProbabilityMeasureGamma (by norm_num) (by norm_num)

theorem unit_exp_pdf (t : ℝ) :
    gammaPDFReal 1 1 t = if 0 ≤ t then Real.exp (-t) else 0 := by
  norm_num [gammaPDFReal]

theorem unit_exp_integral (f : ℝ → ℝ) :
    (∫ t, f t ∂unitExpProbability) = ∫ t : ℝ in Ioi 0, Real.exp (-t) * f t := by
  change (∫ t, f t ∂volume.withDensity
    (fun t => ((Real.toNNReal (gammaPDFReal 1 1 t) : ℝ≥0) : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul
    ((measurable_gammaPDFReal 1 1).real_toNNReal)]
  have hfun : (fun t => Real.toNNReal (gammaPDFReal 1 1 t) • f t) =
      (Ici (0 : ℝ)).indicator (fun t => Real.exp (-t) * f t) := by
    funext t
    rw [NNReal.smul_def, smul_eq_mul,
      Real.coe_toNNReal _ (gammaPDFReal_nonneg (by norm_num) (by norm_num) t), unit_exp_pdf]
    by_cases ht : 0 ≤ t <;> simp [ht]
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

theorem unit_exp_laplace (s : ℝ) (hs : 0 ≤ s) : realLaplace unitExpProbability s = (1+s)⁻¹ := by
  rw [realLaplace, unit_exp_integral]
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 1) (r := 1+s) (by norm_num) (by positivity)
  norm_num at hi
  rw [← hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [← Real.exp_add]
  congr 1
  ring

theorem unit_exp_no_atom (x : ℝ) : unitExpProbability {x} = 0 := by
  apply withDensity_absolutelyContinuous volume (gammaPDF 1 1)
  exact measure_singleton x

theorem unit_exp_negative_ray : unitExpProbability (Iio 0) = 0 := by
  rw [unitExpProbability, gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos (by norm_num)

def atomExpMixture (c : ℝ) : Measure ℝ :=
  ENNReal.ofReal c • Measure.dirac 0 + ENNReal.ofReal (1-c) • unitExpProbability

theorem atom_exp_mixture_probability (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsProbabilityMeasure (atomExpMixture c) := by
  constructor
  have he : ENNReal.ofReal c + ENNReal.ofReal (1-c) = 1 := by
    rw [← ENNReal.ofReal_add hc0 (by linarith)]
    norm_num
  simpa [atomExpMixture] using he

theorem atom_exp_mixture_nonnegative (c : ℝ) : ∀ᵐ x ∂atomExpMixture c, 0 ≤ x := by
  rw [ae_iff]
  simp only [not_le]
  change atomExpMixture c (Iio 0) = 0
  simp [atomExpMixture, unit_exp_negative_ray]

theorem atom_exp_mixture_zero_atom (c : ℝ) : atomExpMixture c {0} = ENNReal.ofReal c := by
  simp [atomExpMixture, unit_exp_no_atom]

theorem atom_exp_mixture_laplace (c s : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hs : 0 ≤ s) :
    realLaplace (atomExpMixture c) s = (1+c*s)/(1+s) := by
  have hi : Integrable (fun t : ℝ => Real.exp (-(s*t))) unitExpProbability := by
    apply Integrable.of_integral_ne_zero
    change realLaplace unitExpProbability s ≠ 0
    rw [unit_exp_laplace s hs]
    positivity
  have hd : Integrable (fun t : ℝ => Real.exp (-(s*t))) (Measure.dirac 0) :=
    by
      apply Integrable.of_integral_ne_zero
      rw [integral_dirac]
      exact Real.exp_ne_zero _
  unfold atomExpMixture realLaplace
  rw [integral_add_measure (hd.smul_measure ENNReal.ofReal_ne_top)
    (hi.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure]
  simp only [ENNReal.toReal_ofReal hc0, ENNReal.toReal_ofReal (sub_nonneg.mpr hc1),
    smul_eq_mul]
  rw [integral_dirac]
  change c * Real.exp (-(s*0)) + (1-c) * realLaplace unitExpProbability s = _
  rw [unit_exp_laplace s hs]
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
  field_simp
  ring

def gammaResidualProbability (c : ℝ) : Measure ℝ :=
  independentAffineSum (atomExpMixture c) (atomExpMixture c) 1

theorem gamma_residual_probability (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsProbabilityMeasure (gammaResidualProbability c) := by
  letI := atom_exp_mixture_probability c hc0 hc1
  unfold gammaResidualProbability
  infer_instance

theorem gamma_residual_laplace (c s : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hs : 0 ≤ s) :
    realLaplace (gammaResidualProbability c) s = gammaResidualLaplace c s := by
  letI := atom_exp_mixture_probability c hc0 hc1
  rw [gammaResidualProbability, independent_affine_sum_laplace, one_mul,
    atom_exp_mixture_laplace c s hc0 hc1 hs]
  unfold gammaResidualLaplace
  ring

theorem gamma_residual_nonnegative (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∀ᵐ x ∂gammaResidualProbability c, 0 ≤ x := by
  letI := atom_exp_mixture_probability c hc0 hc1
  unfold gammaResidualProbability independentAffineSum
  rw [ae_map_iff ((measurable_const.mul measurable_fst).add measurable_snd).aemeasurable
    measurableSet_Ici]
  apply (Measure.ae_prod_iff_ae_ae
    (isClosed_le continuous_const
      ((continuous_const.mul continuous_fst).add continuous_snd)).measurableSet).mpr
  filter_upwards [atom_exp_mixture_nonnegative c] with x hx
  filter_upwards [atom_exp_mixture_nonnegative c] with y hy
  simpa using add_nonneg hx hy

theorem gamma_residual_zero_atom (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    gammaResidualProbability c {0} = ENNReal.ofReal (c ^ 2) := by
  letI := atom_exp_mixture_probability c hc0 hc1
  unfold gammaResidualProbability independentAffineSum
  rw [Measure.map_apply ((measurable_const.mul measurable_fst).add measurable_snd)
    (measurableSet_singleton 0)]
  have hae : (fun z : ℝ × ℝ => 1 * z.1 + z.2) ⁻¹' ({0} : Set ℝ) =ᵐ[
      (atomExpMixture c).prod (atomExpMixture c)] ({0} : Set ℝ) ×ˢ ({0} : Set ℝ) := by
    have hp : ∀ᵐ z : ℝ × ℝ ∂(atomExpMixture c).prod (atomExpMixture c),
        0 ≤ z.1 ∧ 0 ≤ z.2 := by
      apply (Measure.ae_prod_iff_ae_ae
        ((isClosed_le continuous_const continuous_fst).measurableSet.inter
          (isClosed_le continuous_const continuous_snd).measurableSet)).mpr
      filter_upwards [atom_exp_mixture_nonnegative c] with x hx
      filter_upwards [atom_exp_mixture_nonnegative c] with y hy
      exact ⟨hx, hy⟩
    filter_upwards [hp] with z hz
    apply propext
    change 1 * z.1 + z.2 = 0 ↔ z.1 = 0 ∧ z.2 = 0
    constructor
    · intro he
      exact ⟨by linarith [hz.1, hz.2], by linarith [hz.1, hz.2]⟩
    · rintro ⟨he1, he2⟩
      simp [he1, he2]
  rw [measure_congr hae, Measure.prod_prod, atom_exp_mixture_zero_atom]
  rw [pow_two, ENNReal.ofReal_mul hc0]

/-- The actual residual construction gives the real-line identifying clause of P9. -/
theorem canonical_residual_identifies_gamma
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hdecomp : independentAffineSum μ (gammaResidualProbability c) c = μ) :
    μ = gammaProbability := by
  letI := gamma_residual_probability c hc0 hc1.le
  exact independent_gamma_residual_identifies_real_line_law μ (gammaResidualProbability c)
    c hc0 hc1 (gamma_residual_nonnegative c hc0 hc1.le)
    (fun s hs => gamma_residual_laplace c s hc0 hc1.le hs) hdecomp

theorem gamma_canonical_self_decomposition (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    independentAffineSum gammaProbability (gammaResidualProbability c) c = gammaProbability := by
  letI := gamma_residual_probability c hc0 hc1
  apply operator_full_line_mixing_characterization
  intro n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs : -1 < c * (n : ℝ) := by have := mul_nonneg hc0 hn; linarith
  have he := independent_affine_sum_laplace gammaProbability (gammaResidualProbability c) c (n : ℝ)
  rw [gamma_residual_laplace c n hc0 hc1 hn] at he
  unfold realLaplace at he
  rw [gamma_probability_laplace hs] at he
  unfold gammaResidualLaplace at he
  have hne : 1 + c * (n : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hne0 : 1 + (n : ℝ) ≠ 0 := ne_of_gt (by positivity)
  calc
    (∫ t : ℝ, Real.exp (-(n : ℝ) * t) ∂independentAffineSum gammaProbability
      (gammaResidualProbability c) c) =
        ∫ t : ℝ, Real.exp (-((n : ℝ) * t)) ∂independentAffineSum gammaProbability
          (gammaResidualProbability c) c := by
      apply integral_congr_ae
      filter_upwards with t
      congr 1
      ring
    _ = (1 + c * (n : ℝ))⁻¹ ^ 2 *
        ((1 + c * (n : ℝ)) / (1 + (n : ℝ))) ^ 2 := he
    _ = (1 / (1 + (n : ℝ))) ^ 2 := by field_simp [hne, hne0]

theorem gamma_residual_scale_identified (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hc1 : c ≤ 1) (hd1 : d ≤ 1)
    (hlaw : gammaResidualProbability c = gammaResidualProbability d) : c = d := by
  have he := congrArg (fun μ : Measure ℝ => μ {0}) hlaw
  dsimp only at he
  rw [gamma_residual_zero_atom c hc hc1, gamma_residual_zero_atom d hd hd1] at he
  have hr := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_ofReal (sq_nonneg c), ENNReal.toReal_ofReal (sq_nonneg d)] at hr
  nlinarith

end
end Sigma
