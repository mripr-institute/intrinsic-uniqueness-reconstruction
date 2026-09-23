import SigmaProbCompletion
import SigmaProbLevyIntegral
import Mathlib.Probability.Distributions.Poisson

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Iterated native additive convolution, including the zero-fold Dirac law. -/
def convolutionPower (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => (convolutionPower μ n).conv μ

theorem gamma_completion_convolution_power (r : ℝ≥0) (n : ℕ) :
    convolutionPower (gammaCompletion r) n = gammaCompletion ((n : ℝ≥0) * r) := by
  induction n with
  | zero => simp [convolutionPower, gamma_completion_zero]
  | succ n ih =>
    rw [convolutionPower, ih, gamma_completion_native_convolution]
    congr 1
    rw [Nat.cast_succ, add_mul, one_mul]

/-- Every integer convolution root is an actual probability measure on the
nonnegative real line. -/
theorem gamma_probability_infinitely_divisible (n : ℕ) (hn : 0 < n) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      (∀ᵐ x ∂μ, 0 ≤ x) ∧ convolutionPower μ n = gammaProbability := by
  let r : ℝ≥0 := (n : ℝ≥0)⁻¹
  refine ⟨gammaCompletion r, inferInstance, gamma_completion_nonnegative r, ?_⟩
  rw [gamma_completion_convolution_power, ← gamma_completion_one]
  congr 1
  dsimp [r]
  field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)]

theorem convolution_power_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) : IsProbabilityMeasure (convolutionPower μ n) := by
  induction n with
  | zero =>
    change IsProbabilityMeasure (Measure.dirac (0 : ℝ))
    infer_instance
  | succ n ih =>
    change IsProbabilityMeasure ((convolutionPower μ n).conv μ)
    letI := ih
    infer_instance

/-- A Poisson number of independent jumps, expressed as a native mixture of
the corresponding finite convolution laws. -/
def poissonConvolutionLaw (r : ℝ≥0) (π : Measure ℝ) : Measure ℝ :=
  Measure.sum (fun n : ℕ => (poissonPMF r n) • convolutionPower π n)

theorem poisson_convolution_probability (r : ℝ≥0) (π : Measure ℝ)
    [IsProbabilityMeasure π] : IsProbabilityMeasure (poissonConvolutionLaw r π) := by
  constructor
  rw [poissonConvolutionLaw, Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [Measure.smul_apply]
  calc
    (∑' n : ℕ, (poissonPMF r n) * (convolutionPower π n) univ) =
        ∑' n : ℕ, poissonPMF r n := by
          apply tsum_congr
          intro n
          letI := convolution_power_probability π n
          simp
    _ = 1 := (poissonPMF r).tsum_coe

theorem poisson_pmf_real_generating (r : ℝ≥0) (z : ℝ) :
    HasSum (fun n : ℕ => poissonPMFReal r n * z ^ n)
      (Real.exp ((r : ℝ) * (z - 1))) := by
  have h := NormedSpace.expSeries_div_hasSum_exp ℝ ((r : ℝ) * z)
  have h' := h.mul_left (Real.exp (-(r : ℝ)))
  convert h' using 1
  · funext n
    simp [poissonPMFReal, mul_pow]
    ring
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1
    ring

theorem convolution_power_laplace (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (s : ℝ) :
    realLaplace (convolutionPower μ n) s = (realLaplace μ s) ^ n := by
  induction n with
  | zero => simp [convolutionPower, realLaplace]
  | succ n ih =>
    letI := convolution_power_probability μ n
    have h := independent_affine_sum_laplace (convolutionPower μ n) μ 1 s
    simpa only [Measure.conv, independentAffineSum, one_mul, convolutionPower,
      ih, pow_succ] using h

theorem convolution_power_nonnegative (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (n : ℕ) :
    ∀ᵐ x ∂convolutionPower μ n, 0 ≤ x := by
  induction n with
  | zero => simp [convolutionPower]
  | succ n ih =>
    rw [convolutionPower, Measure.conv]
    rw [ae_map_iff (by fun_prop : AEMeasurable (fun z : ℝ × ℝ => z.1 + z.2)
      ((convolutionPower μ n).prod μ)) measurableSet_Ici]
    apply (Measure.ae_prod_iff_ae_ae
      (isClosed_le continuous_const (continuous_fst.add continuous_snd)).measurableSet).mpr
    filter_upwards [ih] with x hx
    filter_upwards [hμ] with y hy
    exact add_nonneg hx hy

theorem poisson_convolution_nonnegative (r : ℝ≥0) (π : Measure ℝ)
    [IsProbabilityMeasure π] (hπ : ∀ᵐ x ∂π, 0 ≤ x) :
    ∀ᵐ x ∂poissonConvolutionLaw r π, 0 ≤ x := by
  rw [poissonConvolutionLaw]
  apply (Measure.ae_sum_iff).mpr
  intro n
  exact Measure.ae_smul_measure (convolution_power_nonnegative π hπ n) _

/-- The native Poisson mixture has the compound-Poisson Laplace formula. -/
theorem poisson_convolution_laplace (r : ℝ≥0) (π : Measure ℝ)
    [IsProbabilityMeasure π] (hπ : ∀ᵐ x ∂π, 0 ≤ x)
    (s : ℝ) (hs : 0 ≤ s) :
    realLaplace (poissonConvolutionLaw r π) s =
      Real.exp ((r : ℝ) * (realLaplace π s - 1)) := by
  letI := poisson_convolution_probability r π
  have hpos := poisson_convolution_nonnegative r π hπ
  have hi := nonnegative_probability_laplace_integrable
    (poissonConvolutionLaw r π) hpos s hs
  unfold realLaplace at hi ⊢
  rw [poissonConvolutionLaw, integral_sum_measure hi]
  simp_rw [integral_smul_measure]
  calc
    (∑' n : ℕ, (poissonPMF r n).toReal •
        ∫ x : ℝ, Real.exp (-(s * x)) ∂convolutionPower π n) =
      ∑' n : ℕ, poissonPMFReal r n * (realLaplace π s) ^ n := by
        apply tsum_congr
        intro n
        rw [← realLaplace, convolution_power_laplace]
        rw [show (poissonPMF r n).toReal = poissonPMFReal r n by
          change (ENNReal.ofReal (poissonPMFReal r n)).toReal = _
          exact ENNReal.toReal_ofReal poissonPMFReal_nonneg]
        simp only [smul_eq_mul]
    _ = _ := (poisson_pmf_real_generating r (realLaplace π s)).tsum_eq

def gammaResidualJumpRate (c : ℝ) : ℝ≥0 :=
  Real.toNNReal (-2 * Real.log c)

def gammaResidualJumpLaw (c : ℝ) : Measure ℝ :=
  ((gammaResidualJumpRate c : ℝ≥0∞)⁻¹) • gammaResidualLevyMeasure c

theorem gamma_residual_jump_rate_pos {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    0 < gammaResidualJumpRate c := by
  rw [gammaResidualJumpRate, Real.toNNReal_pos]
  have hl := Real.log_neg hc0 hc1
  linarith

theorem gamma_residual_jump_law_probability {c : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) :
    IsProbabilityMeasure (gammaResidualJumpLaw c) := by
  constructor
  rw [gammaResidualJumpLaw, Measure.smul_apply,
    gamma_residual_levy_measure_mass hc0 hc1.le]
  have hp := gamma_residual_jump_rate_pos hc0 hc1
  have he : ENNReal.ofReal (-2 * Real.log c) =
      (gammaResidualJumpRate c : ℝ≥0∞) := rfl
  rw [he]
  change ((gammaResidualJumpRate c : ℝ≥0∞)⁻¹) *
    (gammaResidualJumpRate c : ℝ≥0∞) = 1
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hp.ne') ENNReal.coe_ne_top

theorem gamma_residual_jump_law_nonnegative (c : ℝ) :
    ∀ᵐ x ∂gammaResidualJumpLaw c, 0 ≤ x := by
  rw [ae_iff]
  simp only [not_le]
  change gammaResidualJumpLaw c (Iio 0) = 0
  simp [gammaResidualJumpLaw, gammaResidualLevyMeasure,
    Measure.smul_apply, withDensity_apply]
  have he : Iio (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_empty_iff_false, iff_false]
    exact fun h => (lt_asymm h.1 h.2).elim
  rw [he]
  simp

theorem gamma_residual_levy_integral_density {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) (f : ℝ → ℝ) :
    (∫ x : ℝ, f x ∂gammaResidualLevyMeasure c) =
      ∫ x : ℝ in Ioi 0, gammaResidualLevyDensity c x * f x := by
  unfold gammaResidualLevyMeasure
  simp only [ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
    (show Measurable (fun x : ℝ => Real.toNNReal (gammaResidualLevyDensity c x)) by
      unfold gammaResidualLevyDensity
      fun_prop)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (gamma_residual_levy_density_nonnegative hc0 hc1 hx)]

theorem gamma_residual_levy_exponent_integral {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    (∫ x : ℝ in Ioi 0,
      (1 - Real.exp (-(s * x))) * gammaResidualLevyDensity c x) =
      gammaLaplaceExponent s + gammaLaplaceExponent (1 / c - 1) -
        gammaLaplaceExponent (s + (1 / c - 1)) := by
  let a := 1 / c - 1
  have ha : 0 ≤ a := by
    dsimp [a]
    apply sub_nonneg.mpr
    exact (le_div_iff₀ hc0).mpr (by simpa using hc1)
  have he : (fun x : ℝ =>
      (1 - Real.exp (-(s * x))) * gammaResidualLevyDensity c x) =
      (fun x => (1 - Real.exp (-(s * x))) * gammaLevyDensity x) +
        (fun x => (1 - Real.exp (-(a * x))) * gammaLevyDensity x) -
        (fun x => (1 - Real.exp (-((s + a) * x))) * gammaLevyDensity x) := by
    funext x
    rw [gamma_residual_levy_density_factor hc0]
    change (1 - Real.exp (-(s * x))) *
      ((1 - Real.exp (-(a * x))) * gammaLevyDensity x) = _
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [show -((s + a) * x) = -(s * x) + -(a * x) by ring, Real.exp_add]
    ring
  rw [he]
  rw [MeasureTheory.integral_sub'
    ((gamma_levy_exponent_integrable s hs).add
      (gamma_levy_exponent_integrable a ha))
    (gamma_levy_exponent_integrable (s + a) (add_nonneg hs ha)),
    MeasureTheory.integral_add' (gamma_levy_exponent_integrable s hs)
      (gamma_levy_exponent_integrable a ha),
    gamma_levy_exponent_integral s hs,
    gamma_levy_exponent_integral a ha,
    gamma_levy_exponent_integral (s + a) (add_nonneg hs ha)]

theorem gamma_residual_levy_measure_nonnegative (c : ℝ) :
    ∀ᵐ x ∂gammaResidualLevyMeasure c, 0 ≤ x := by
  rw [ae_iff]
  simp only [not_le]
  change gammaResidualLevyMeasure c (Iio 0) = 0
  simp [gammaResidualLevyMeasure, withDensity_apply]
  have he : Iio (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_empty_iff_false, iff_false]
    exact fun h => (lt_asymm h.1 h.2).elim
  rw [he]
  simp

theorem gamma_residual_levy_integral_exp {c : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (s : ℝ) (hs : 0 ≤ s) :
    realLaplace (gammaResidualLevyMeasure c) s =
      -2 * Real.log c -
        (gammaLaplaceExponent s + gammaLaplaceExponent (1 / c - 1) -
          gammaLaplaceExponent (s + (1 / c - 1))) := by
  letI := gamma_residual_levy_measure_finite hc0 hc1.le
  have hpos := gamma_residual_levy_measure_nonnegative c
  have hi : Integrable (fun x : ℝ => Real.exp (-(s*x)))
      (gammaResidualLevyMeasure c) := by
    apply (integrable_const (1 : ℝ)).mono'
      ((continuous_const.mul continuous_id).neg.rexp.aestronglyMeasurable)
    filter_upwards [hpos] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hs hx))
  have hsub := MeasureTheory.integral_sub (integrable_const (1 : ℝ)) hi
  rw [integral_const, smul_eq_mul, mul_one] at hsub
  rw [gamma_residual_levy_integral_density hc0 hc1.le] at hsub
  simp only [mul_comm (gammaResidualLevyDensity c _)] at hsub
  rw [gamma_residual_levy_exponent_integral hc0 hc1.le s hs] at hsub
  rw [gamma_residual_levy_measure_mass hc0 hc1.le,
    ENNReal.toReal_ofReal (by have h := Real.log_neg hc0 hc1; linarith)] at hsub
  unfold realLaplace
  linarith

theorem gamma_residual_jump_laplace {c : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (s : ℝ) (hs : 0 ≤ s) :
    (gammaResidualJumpRate c : ℝ) *
        (realLaplace (gammaResidualJumpLaw c) s - 1) =
      -(gammaLaplaceExponent s + gammaLaplaceExponent (1 / c - 1) -
        gammaLaplaceExponent (s + (1 / c - 1))) := by
  have hr : (gammaResidualJumpRate c : ℝ) = -2 * Real.log c := by
    unfold gammaResidualJumpRate
    exact Real.coe_toNNReal _ (by have h := Real.log_neg hc0 hc1; linarith)
  have hrpos : 0 < (gammaResidualJumpRate c : ℝ) := by
    exact_mod_cast gamma_residual_jump_rate_pos hc0 hc1
  have hl : realLaplace (gammaResidualJumpLaw c) s =
      (gammaResidualJumpRate c : ℝ)⁻¹ *
        realLaplace (gammaResidualLevyMeasure c) s := by
    unfold realLaplace gammaResidualJumpLaw
    rw [integral_smul_measure]
    simp only [smul_eq_mul, ENNReal.toReal_inv, ENNReal.coe_toReal]
  rw [hl, gamma_residual_levy_integral_exp hc0 hc1 s hs, ← hr]
  field_simp [ne_of_gt hrpos]

theorem gamma_residual_levy_exponent_exp {c : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (s : ℝ) (hs : 0 ≤ s) :
    Real.exp (-(gammaLaplaceExponent s +
      gammaLaplaceExponent (1 / c - 1) -
      gammaLaplaceExponent (s + (1 / c - 1)))) =
      gammaResidualLaplace c s := by
  have hp : 0 < 1 + s := by linarith
  have hq : 0 < 1 + (1 / c - 1) := by
    have := one_div_pos.mpr hc0
    linarith
  have ht : 0 < 1 + (s + (1 / c - 1)) := by linarith
  have hexp (u : ℝ) (hu : 0 < u) : Real.exp (2 * Real.log u) = u ^ 2 := by
    rw [show 2 * Real.log u = Real.log u + Real.log u by ring,
      Real.exp_add, Real.exp_log hu]
    ring
  unfold gammaLaplaceExponent gammaResidualLaplace
  rw [neg_sub, Real.exp_sub, Real.exp_add,
    hexp _ ht, hexp _ hp, hexp _ hq]
  have hcne : c ≠ 0 := ne_of_gt hc0
  have hpne : 1 + s ≠ 0 := ne_of_gt hp
  field_simp
  ring

/-- The displayed finite Lévy measure is the jump-intensity measure of
the actual residual probability law. -/
theorem gamma_residual_compound_poisson {c : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) :
    poissonConvolutionLaw (gammaResidualJumpRate c)
      (gammaResidualJumpLaw c) = gammaResidualProbability c := by
  letI := gamma_residual_jump_law_probability hc0 hc1
  letI := poisson_convolution_probability (gammaResidualJumpRate c)
    (gammaResidualJumpLaw c)
  letI := gamma_residual_probability c hc0.le hc1.le
  apply nonnegative_integer_laplace_unique _ _
    (poisson_convolution_nonnegative _ _ (gamma_residual_jump_law_nonnegative c))
    (gamma_residual_nonnegative c hc0.le hc1.le)
  intro n
  rw [poisson_convolution_laplace _ _ (gamma_residual_jump_law_nonnegative c)
      n (Nat.cast_nonneg n),
    gamma_residual_laplace c n hc0.le hc1.le (Nat.cast_nonneg n),
    gamma_residual_jump_laplace hc0 hc1 n (Nat.cast_nonneg n),
    gamma_residual_levy_exponent_exp hc0 hc1 n (Nat.cast_nonneg n)]

/-- Shape four provides a distinct infinitely divisible Gamma law. -/
theorem gamma_shape_four_infinitely_divisible (n : ℕ) (hn : 0 < n) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      (∀ᵐ x ∂μ, 0 ≤ x) ∧ convolutionPower μ n = gammaCompletion 2 := by
  let r : ℝ≥0 := 2 * (n : ℝ≥0)⁻¹
  refine ⟨gammaCompletion r, inferInstance, gamma_completion_nonnegative r, ?_⟩
  rw [gamma_completion_convolution_power]
  congr 1
  dsimp [r]
  field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)]

theorem independent_affine_sum_nonnegative (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hν : ∀ᵐ y ∂ν, 0 ≤ y)
    (c : ℝ) (hc : 0 ≤ c) :
    ∀ᵐ z ∂independentAffineSum μ ν c, 0 ≤ z := by
  unfold independentAffineSum
  rw [ae_map_iff (by fun_prop : AEMeasurable (fun z : ℝ × ℝ => c * z.1 + z.2)
      (μ.prod ν)) measurableSet_Ici]
  apply (Measure.ae_prod_iff_ae_ae
    (isClosed_le continuous_const (continuous_const.mul continuous_fst |>.add continuous_snd)).measurableSet).mpr
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  exact add_nonneg (mul_nonneg hc hx) hy

theorem gamma_shape_four_self_decomposition (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    independentAffineSum (gammaCompletion 2)
      ((gammaResidualProbability c).conv (gammaResidualProbability c)) c =
        gammaCompletion 2 := by
  letI := gamma_residual_probability c hc0 hc1
  letI : IsProbabilityMeasure
      ((gammaResidualProbability c).conv (gammaResidualProbability c)) := inferInstance
  letI : IsProbabilityMeasure
      (independentAffineSum (gammaCompletion 2)
        ((gammaResidualProbability c).conv (gammaResidualProbability c)) c) := inferInstance
  have hrespos : ∀ᵐ x ∂(gammaResidualProbability c).conv
      (gammaResidualProbability c), 0 ≤ x := by
    simpa [Measure.conv, independentAffineSum, one_mul] using
      independent_affine_sum_nonnegative (gammaResidualProbability c)
        (gammaResidualProbability c)
        (gamma_residual_nonnegative c hc0 hc1)
        (gamma_residual_nonnegative c hc0 hc1) 1 (by norm_num)
  apply nonnegative_integer_laplace_unique _ _
  · exact independent_affine_sum_nonnegative _ _
      (gamma_completion_nonnegative 2) hrespos c hc0
  · exact gamma_completion_nonnegative 2
  intro n
  have hγ : gammaCompletion 2 =
      (gammaProbability).conv gammaProbability := by
    rw [← gamma_completion_one, gamma_completion_native_convolution]
    norm_num
  have hbase := congrArg (fun μ : Measure ℝ => realLaplace μ (n : ℝ))
    (gamma_canonical_self_decomposition c hc0 hc1)
  change realLaplace (independentAffineSum gammaProbability
    (gammaResidualProbability c) c) n = realLaplace gammaProbability n at hbase
  rw [independent_affine_sum_laplace] at hbase
  rw [independent_affine_sum_laplace]
  rw [hγ]
  have hγlap : realLaplace (gammaProbability.conv gammaProbability) (c * n) =
      (realLaplace gammaProbability (c * n)) ^ 2 := by
    have h := independent_affine_sum_laplace gammaProbability gammaProbability 1 (c * n)
    simpa [Measure.conv, independentAffineSum, one_mul, pow_two] using h
  have hreslap : realLaplace ((gammaResidualProbability c).conv
      (gammaResidualProbability c)) n =
      (realLaplace (gammaResidualProbability c) n) ^ 2 := by
    have h := independent_affine_sum_laplace (gammaResidualProbability c)
      (gammaResidualProbability c) 1 n
    simpa [Measure.conv, independentAffineSum, one_mul, pow_two] using h
  have hγtarget : realLaplace (gammaProbability.conv gammaProbability) n =
      (realLaplace gammaProbability n) ^ 2 := by
    have h := independent_affine_sum_laplace gammaProbability gammaProbability 1 n
    simpa [Measure.conv, independentAffineSum, one_mul, pow_two] using h
  rw [hγlap, hreslap, hγtarget]
  calc
    (realLaplace gammaProbability (c * n)) ^ 2 *
        (realLaplace (gammaResidualProbability c) n) ^ 2 =
      (realLaplace gammaProbability (c * n) *
        realLaplace (gammaResidualProbability c) n) ^ 2 := by ring
    _ = _ := by rw [hbase]

theorem gamma_shape_four_ne_canonical : gammaCompletion 2 ≠ gammaProbability := by
  intro h
  have he := congrArg (fun μ : Measure ℝ => realLaplace μ 1) h
  change realLaplace (gammaCompletion 2) 1 = realLaplace gammaProbability 1 at he
  rw [← gamma_completion_one, gamma_completion_laplace 2 1 (by norm_num),
    gamma_completion_laplace 1 1 (by norm_num)] at he
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hinj := Real.exp_injective he
  norm_num at hinj

theorem gamma_shape_four_identification : gammaCompletion 2 = gammaMeasure 4 1 := by
  norm_num [gammaCompletion]

theorem gamma_rate_two_integral (f : ℝ → ℝ) :
    (∫ t, f t ∂gammaMeasure 2 2) =
      ∫ t : ℝ in Ioi 0, (4 * t * Real.exp (-(2*t))) * f t := by
  change (∫ t, f t ∂volume.withDensity
    (fun t => ((Real.toNNReal (gammaPDFReal 2 2 t) : ℝ≥0) : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul
    ((measurable_gammaPDFReal 2 2).real_toNNReal)]
  have he : (fun t => Real.toNNReal (gammaPDFReal 2 2 t) • f t) =
      (Ici (0 : ℝ)).indicator (fun t => (4 * t * Real.exp (-(2*t))) * f t) := by
    funext t
    rw [NNReal.smul_def, smul_eq_mul,
      Real.coe_toNNReal _ (gammaPDFReal_nonneg (by norm_num) (by norm_num) t)]
    by_cases ht : 0 ≤ t
    · rw [Set.indicator_of_mem (show t ∈ Ici (0:ℝ) from ht)]
      simp only [gammaPDFReal, if_pos ht]
      norm_num
    · simp [gammaPDFReal, ht]
  rw [he, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

theorem gamma_rate_two_laplace (s : ℝ) (hs : 0 ≤ s) :
    realLaplace (gammaMeasure 2 2) s = (2 / (2+s)) ^ 2 := by
  rw [realLaplace, gamma_rate_two_integral]
  have he : (fun t : ℝ => (4 * t * Real.exp (-(2*t))) * Real.exp (-(s*t))) =
      fun t => 4 * (t * Real.exp (-((2+s)*t))) := by
    funext t
    rw [show -((2+s)*t) = -(2*t) + -(s*t) by ring, Real.exp_add]
    ring
  rw [he, integral_mul_left]
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 2+s)
    (by norm_num) (by linarith : 0 < 2+s)
  have hi' : (∫ t : ℝ in Ioi 0, t * Real.exp (-((2+s)*t))) =
      ((2+s)^2)⁻¹ := by
    simpa [show (2 : ℝ) - 1 = 1 by norm_num,
      Real.rpow_one, div_eq_mul_inv, inv_pow] using hi
  rw [hi']
  field_simp [ne_of_gt (by linarith : 0 < 2+s)]
  ring

theorem realLaplace_map_scale (μ : Measure ℝ) (q s : ℝ) :
    realLaplace (μ.map (fun x => q * x)) s = realLaplace μ (q * s) := by
  unfold realLaplace
  have hmap := integral_map (φ := fun x : ℝ => q * x) (μ := μ)
    (f := fun t : ℝ => Real.exp (-(s * t)))
    (measurable_const.mul measurable_id).aemeasurable
    ((continuous_const.mul continuous_id).neg.rexp.measurable.aestronglyMeasurable)
  rw [hmap]
  have he : (fun x : ℝ => Real.exp (-(s * (q * x)))) =
      (fun x : ℝ => Real.exp (-(q * s * x))) := by
    funext x
    congr 1
    ring
  rw [he]

theorem gamma_rate_two_eq_scaled :
    (gammaProbability.map (fun x => x / 2)) = gammaMeasure 2 2 := by
  letI := gamma_probability_is_probability
  letI : IsProbabilityMeasure (gammaProbability.map (fun x => x / 2)) :=
    isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (gammaMeasure 2 2) :=
    isProbabilityMeasureGamma (by norm_num) (by norm_num)
  apply nonnegative_integer_laplace_unique _ _
  · rw [ae_map_iff (by fun_prop : AEMeasurable (fun x : ℝ => x / 2) gammaProbability)
      measurableSet_Ici]
    filter_upwards [gamma_shape_nonnegative 2] with x hx
    exact div_nonneg hx (by norm_num)
  · rw [ae_iff]
    simp only [not_le]
    change (gammaMeasure 2 2) (Iio 0) = 0
    rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
    exact lintegral_gammaPDF_of_nonpos le_rfl
  intro n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [show (fun x : ℝ => x / 2) = (fun x => (1/2 : ℝ) * x) by funext x; ring,
    realLaplace_map_scale, gamma_rate_two_laplace n hn]
  have hγ := gamma_probability_laplace
    (show -1 < (1/2 : ℝ) * n by
      have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith)
  change realLaplace gammaProbability ((1/2 : ℝ) * n) = _ at hγ
  rw [hγ]
  have hne : 1 + (n : ℝ) * (1/2) ≠ 0 := by positivity
  have hne2 : 2 + (n : ℝ) ≠ 0 := by positivity
  field_simp

theorem map_scale_nonnegative (μ : Measure ℝ) (q : ℝ)
    (hq : 0 ≤ q) (hμ : ∀ᵐ x ∂μ, 0 ≤ x) :
    ∀ᵐ x ∂μ.map (fun x => q * x), 0 ≤ x := by
  rw [ae_map_iff (by fun_prop : AEMeasurable (fun x : ℝ => q * x) μ)
    measurableSet_Ici]
  filter_upwards [hμ] with x hx
  exact mul_nonneg hq hx

theorem gamma_rate_two_infinitely_divisible (n : ℕ) (hn : 0 < n) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      (∀ᵐ x ∂μ, 0 ≤ x) ∧ convolutionPower μ n = gammaMeasure 2 2 := by
  let r : ℝ≥0 := (n : ℝ≥0)⁻¹
  let μ := (gammaCompletion r).map (fun x => (1/2 : ℝ) * x)
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_map (by fun_prop)
  refine ⟨μ, inferInstance,
    map_scale_nonnegative _ _ (by norm_num) (gamma_completion_nonnegative r), ?_⟩
  letI : IsProbabilityMeasure (gammaMeasure 2 2) :=
    isProbabilityMeasureGamma (by norm_num) (by norm_num)
  letI := convolution_power_probability μ n
  apply nonnegative_integer_laplace_unique _ _
  · exact convolution_power_nonnegative μ
      (map_scale_nonnegative _ _ (by norm_num) (gamma_completion_nonnegative r)) n
  · rw [← gamma_rate_two_eq_scaled]
    rw [show (fun x : ℝ => x / 2) = (fun x => (1/2 : ℝ) * x) by
      funext x; ring]
    exact map_scale_nonnegative gammaProbability (1/2 : ℝ)
      (by norm_num) (gamma_shape_nonnegative 2)
  intro k
  rw [convolution_power_laplace, show μ =
      (gammaCompletion r).map (fun x => (1/2 : ℝ) * x) by rfl,
    realLaplace_map_scale, ← gamma_rate_two_eq_scaled,
    show (fun x : ℝ => x / 2) = (fun x => (1/2 : ℝ) * x) by funext x; ring,
    realLaplace_map_scale]
  have hroot : convolutionPower (gammaCompletion r) n = gammaProbability := by
    rw [gamma_completion_convolution_power, ← gamma_completion_one]
    congr 1
    dsimp [r]
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)]
  have he := congrArg (fun ρ : Measure ℝ =>
    realLaplace ρ ((1/2 : ℝ) * k)) hroot
  change realLaplace (convolutionPower (gammaCompletion r) n) ((1/2 : ℝ) * k) =
    realLaplace gammaProbability ((1/2 : ℝ) * k) at he
  rw [convolution_power_laplace] at he
  exact he

theorem gamma_rate_two_self_decomposition (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    independentAffineSum (gammaMeasure 2 2)
      ((gammaResidualProbability c).map (fun x => (1/2 : ℝ) * x)) c =
        gammaMeasure 2 2 := by
  letI := gamma_residual_probability c hc0 hc1
  letI : IsProbabilityMeasure
      ((gammaResidualProbability c).map (fun x => (1/2 : ℝ) * x)) :=
    isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (gammaMeasure 2 2) :=
    isProbabilityMeasureGamma (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure
      (independentAffineSum (gammaMeasure 2 2)
        ((gammaResidualProbability c).map (fun x => (1/2 : ℝ) * x)) c) :=
    inferInstance
  have hratepos : ∀ᵐ x ∂gammaMeasure 2 2, 0 ≤ x := by
    rw [← gamma_rate_two_eq_scaled,
      show (fun x : ℝ => x / 2) = (fun x => (1/2 : ℝ) * x) by funext x; ring]
    exact map_scale_nonnegative _ _ (by norm_num) (gamma_shape_nonnegative 2)
  have hrespos := map_scale_nonnegative (gammaResidualProbability c) (1/2 : ℝ)
    (by norm_num) (gamma_residual_nonnegative c hc0 hc1)
  apply nonnegative_integer_laplace_unique _ _
    (independent_affine_sum_nonnegative _ _ hratepos hrespos c hc0) hratepos
  intro k
  rw [independent_affine_sum_laplace]
  have hbase := congrArg (fun ρ : Measure ℝ =>
    realLaplace ρ ((1/2 : ℝ) * k))
      (gamma_canonical_self_decomposition c hc0 hc1)
  change realLaplace (independentAffineSum gammaProbability
    (gammaResidualProbability c) c) ((1/2 : ℝ) * k) =
    realLaplace gammaProbability ((1/2 : ℝ) * k) at hbase
  rw [independent_affine_sum_laplace] at hbase
  rw [← gamma_rate_two_eq_scaled,
    show (fun x : ℝ => x / 2) = (fun x => (1/2 : ℝ) * x) by funext x; ring,
    realLaplace_map_scale,
    realLaplace_map_scale,
    realLaplace_map_scale]
  convert hbase using 1
  ring_nf

theorem gamma_rate_two_ne_canonical : gammaMeasure 2 2 ≠ gammaProbability := by
  intro h
  have he := congrArg (fun μ : Measure ℝ => realLaplace μ 1) h
  change realLaplace (gammaMeasure 2 2) 1 = realLaplace gammaProbability 1 at he
  rw [gamma_rate_two_laplace 1 (by norm_num)] at he
  have hγ := gamma_probability_laplace (s := 1) (by norm_num)
  change realLaplace gammaProbability 1 = _ at hγ
  rw [hγ] at he
  norm_num at he

theorem gamma_residual_jump_intensity_measure {c : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) :
    (gammaResidualJumpRate c : ℝ≥0∞) • gammaResidualJumpLaw c =
      gammaResidualLevyMeasure c := by
  have hp := gamma_residual_jump_rate_pos hc0 hc1
  unfold gammaResidualJumpLaw
  rw [smul_smul]
  rw [ENNReal.mul_inv_cancel (by exact_mod_cast hp.ne') ENNReal.coe_ne_top]
  exact one_smul _ _

end
end Sigma
