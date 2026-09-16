import SigmaProbLevyIntegral
import SigmaProbSurvival
import SigmaProbMGFUnique
import SigmaOpMoments

namespace Sigma
noncomputable section

open Filter MeasureTheory Set
open scoped Topology ENNReal

/-- The probability Stieltjes transform used in `final:P5-stieltjes`. -/
def probabilityStieltjes (μ : Measure ℝ) (z : ℝ) : ℝ :=
  ∫ t : ℝ, (t + z)⁻¹ ∂μ

/-- The real exponential integral occurring in the explicit Gamma transform. -/
def expIntegralOne (z : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi z, Real.exp (-u) / u

/-- Alternating derivative inequalities on the positive ray. -/
def CompletelyMonotoneOnPositive (f : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∀ x : ℝ, 0 < x →
    0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n f x

/-- A concrete derivative tower on the positive ray. -/
def DerivativeTowerOnPositive (f : ℝ → ℝ) (d : ℕ → ℝ → ℝ) : Prop :=
  d 0 = f ∧ ∀ n : ℕ, ∀ x : ℝ, 0 < x → HasDerivAt (d n) (d (n + 1) x) x

theorem derivativeTower_iteratedDeriv {f : ℝ → ℝ} {d : ℕ → ℝ → ℝ}
    (h : DerivativeTowerOnPositive f d) (n : ℕ) (x : ℝ) (hx : 0 < x) :
    iteratedDeriv n f x = d n x := by
  induction n generalizing x with
  | zero => simp [iteratedDeriv_zero, h.1]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv n f =ᶠ[𝓝 x] d n := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        exact ih y hy
      rw [heq.deriv_eq, (h.2 n x hx).deriv]

def gammaLaplaceFunction (x : ℝ) : ℝ := (1 + x)⁻¹ ^ 2

def gammaLaplaceDerivative (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * ((n + 1).factorial : ℝ) * (1 + x)⁻¹ ^ (n + 2)

theorem gamma_laplace_derivative_tower :
    DerivativeTowerOnPositive gammaLaplaceFunction gammaLaplaceDerivative := by
  constructor
  · funext x
    simp [gammaLaplaceDerivative, gammaLaplaceFunction]
  · intro n x hx
    have hne : 1 + x ≠ 0 := ne_of_gt (by linarith)
    have hinv : HasDerivAt (fun y : ℝ => (1 + y)⁻¹) (-((1 + x)⁻¹ ^ 2)) x := by
      have h := ((hasDerivAt_const x 1).add (hasDerivAt_id x)).inv hne
      convert h using 1 <;> field_simp [hne] <;> ring
    have hp := hinv.pow (n + 2)
    unfold gammaLaplaceDerivative
    convert hp.const_mul ((-1 : ℝ) ^ n * ((n + 1).factorial : ℝ)) using 1
    · rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        show n + 1 + 2 = n + 3 by omega,
        show n + 2 - 1 = n + 1 by omega,
        Nat.factorial_succ]
      push_cast
      rw [show n + 3 = (n + 1) + 2 by omega, pow_add, pow_succ]
      ring

theorem gamma_laplace_completely_monotone :
    CompletelyMonotoneOnPositive gammaLaplaceFunction := by
  intro n x hx
  rw [derivativeTower_iteratedDeriv gamma_laplace_derivative_tower n x hx]
  unfold gammaLaplaceDerivative
  have hpos : 0 < (1 + x)⁻¹ := inv_pos.mpr (by linarith)
  rw [show (-1 : ℝ) ^ n *
      ((-1 : ℝ) ^ n * ((n + 1).factorial : ℝ) * (1 + x)⁻¹ ^ (n + 2)) =
      (((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n)) *
        (((n + 1).factorial : ℝ) * (1 + x)⁻¹ ^ (n + 2)) by ring]
  exact mul_nonneg (mul_self_nonneg _)
    (mul_nonneg (by positivity) (pow_nonneg hpos.le _))

theorem intrinsic_density_derivative (x : ℝ) :
    HasDerivAt SigmaPresentations.density ((1 - x) * Real.exp (-x)) x := by
  unfold SigmaPresentations.density
  convert (hasDerivAt_id x).mul (((hasDerivAt_id x).neg).exp) using 1 <;>
    simp only [id_eq] <;> ring

theorem intrinsic_density_not_completely_monotone :
    ¬ CompletelyMonotoneOnPositive SigmaPresentations.density := by
  intro h
  have hh := h 1 (1 / 2 : ℝ) (by norm_num)
  rw [iteratedDeriv_one, (intrinsic_density_derivative (1 / 2 : ℝ)).deriv] at hh
  norm_num at hh
  nlinarith [Real.exp_pos (-(1 / 2 : ℝ))]

theorem gamma_survival_second_derivative (x : ℝ) :
    iteratedDeriv 2 gammaSurvival x = (x - 1) * Real.exp (-x) := by
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  have hfirst : deriv gammaSurvival = fun y => -SigmaPresentations.density y := by
    funext y
    exact (gamma_survival_derivative y).deriv
  rw [hfirst]
  have hd := (intrinsic_density_derivative x).neg
  convert hd.deriv using 1 <;> ring

theorem gamma_survival_not_completely_monotone :
    ¬ CompletelyMonotoneOnPositive gammaSurvival := by
  intro h
  have hh := h 2 (1 / 2 : ℝ) (by norm_num)
  rw [gamma_survival_second_derivative] at hh
  norm_num at hh
  nlinarith [Real.exp_pos (-(1 / 2 : ℝ))]

theorem expIntegralOne_shift (z : ℝ) :
    expIntegralOne z = Real.exp (-z) *
      ∫ t : ℝ in Ioi 0, Real.exp (-t) / (t + z) := by
  have htranslate := (measurePreserving_add_right volume z).setIntegral_image_emb
    (Homeomorph.addRight z).isClosedEmbedding.measurableEmbedding
    (fun u : ℝ => Real.exp (-u) / u) (Ioi (0 : ℝ))
  have himage : (fun t : ℝ => t + z) '' Ioi 0 = Ioi z := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact by simpa using add_lt_add_right ht z
    · intro hu
      refine ⟨u - z, ?_, by ring⟩
      simpa using sub_pos.mpr hu
  rw [himage] at htranslate
  rw [expIntegralOne, htranslate, ← integral_mul_left]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change Real.exp (-(t + z)) / (t + z) =
    Real.exp (-z) * (Real.exp (-t) / (t + z))
  rw [show -(t + z) = -z + -t by ring, Real.exp_add]
  ring

theorem gamma_stieltjes_integral_formula (z : ℝ) (hz : 0 < z) :
    probabilityStieltjes gammaProbability z =
      1 - z * Real.exp z * expIntegralOne z := by
  rw [probabilityStieltjes, gamma_probability_integral]
  have h_exp : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
    simpa using positive_rate_exponential_integrable 1 (by norm_num)
  have h_quot : IntegrableOn (fun t : ℝ => Real.exp (-t) / (t + z)) (Ioi 0) := by
    apply (h_exp.const_mul (1 / z)).mono'
    · exact (((Real.continuous_exp.comp continuous_neg).measurable.div
        (continuous_id.add continuous_const).measurable).aestronglyMeasurable)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := mem_Ioi.mp ht
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos (add_pos ht hz)]
      have hden : z ≤ t + z := by linarith
      have hinv : (t + z)⁻¹ ≤ z⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hz hden
      rw [div_eq_mul_inv, one_div]
      calc
        Real.exp (-t) * (t + z)⁻¹ ≤ Real.exp (-t) * z⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le
        _ = z⁻¹ * Real.exp (-t) := mul_comm _ _
  have hsplit :
      (∫ t : ℝ in Ioi 0, SigmaPresentations.density t * (t + z)⁻¹) =
        (∫ t : ℝ in Ioi 0, Real.exp (-t)) -
          z * ∫ t : ℝ in Ioi 0, Real.exp (-t) / (t + z) := by
    rw [← integral_mul_left, ← integral_sub h_exp (h_quot.const_mul z)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [SigmaPresentations.density]
    have hn : t + z ≠ 0 := (add_pos ht hz).ne'
    field_simp
    ring
  rw [hsplit]
  have hexp : (∫ t : ℝ in Ioi 0, Real.exp (-t)) = 1 := by
    simpa using positive_rate_exponential_integral 1 (by norm_num)
  rw [hexp]
  rw [expIntegralOne_shift z]
  have he : Real.exp z * Real.exp (-z) = 1 := by rw [← Real.exp_add]; simp
  rw [mul_assoc z (Real.exp z) _, ← mul_assoc (Real.exp z) (Real.exp (-z)),
    he, one_mul]

/-- The classical Stieltjes representation, allowing an infinite representing
measure with the required integrable reciprocal weight. -/
def HasStieltjesRepresentation (f : ℝ → ℝ) : Prop :=
  ∃ (a b : ℝ) (ρ : Measure ℝ), 0 ≤ a ∧ 0 ≤ b ∧
    (∀ᵐ t ∂ρ, 0 ≤ t) ∧ Integrable (fun t : ℝ => (1 + t)⁻¹) ρ ∧
    ∀ x : ℝ, 0 < x → f x = a / x + b + ∫ t : ℝ, (x + t)⁻¹ ∂ρ

theorem stieltjes_kernel_integrable_ge_one (ρ : Measure ℝ)
    (hρ : ∀ᵐ t ∂ρ, 0 ≤ t)
    (hi : Integrable (fun t : ℝ => (1 + t)⁻¹) ρ)
    {x : ℝ} (hx : 1 ≤ x) : Integrable (fun t : ℝ => (x + t)⁻¹) ρ := by
  apply hi.mono' ((measurable_const.add measurable_id).inv.aestronglyMeasurable)
  filter_upwards [hρ] with t ht
  change ‖(x + t)⁻¹‖ ≤ (1 + t)⁻¹
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (by linarith))]
  exact inv_anti₀ (by linarith) (by linarith)

theorem stieltjes_scaled_mono_ge_one {f : ℝ → ℝ}
    (h : HasStieltjesRepresentation f) {x y : ℝ}
    (hx : 1 ≤ x) (hxy : x ≤ y) : x * f x ≤ y * f y := by
  obtain ⟨a, b, ρ, ha, hb, hρ, hi, hf⟩ := h
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := hx0.trans_le hxy
  have hix := stieltjes_kernel_integrable_ge_one ρ hρ hi hx
  have hiy := stieltjes_kernel_integrable_ge_one ρ hρ hi (hx.trans hxy)
  have hint : x * (∫ t : ℝ, (x + t)⁻¹ ∂ρ) ≤
      y * (∫ t : ℝ, (y + t)⁻¹ ∂ρ) := by
    rw [← integral_mul_left, ← integral_mul_left]
    apply integral_mono_ae (hix.const_mul x) (hiy.const_mul y)
    filter_upwards [hρ] with t ht
    have hxt : 0 < x + t := by linarith
    have hyt : 0 < y + t := by linarith
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ hxt hyt]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) ht]
  rw [hf x hx0, hf y hy0]
  have hxa : x * (a / x) = a := by field_simp
  have hya : y * (a / y) = a := by field_simp
  nlinarith [mul_le_mul_of_nonneg_right hxy hb]

theorem gamma_laplace_not_stieltjes :
    ¬ HasStieltjesRepresentation gammaLaplaceFunction := by
  intro h
  have hm := stieltjes_scaled_mono_ge_one h (x := 1) (y := 2)
    (by norm_num) (by norm_num)
  norm_num [gammaLaplaceFunction] at hm

/-- Reciprocal moments of a finite measure supported on the nonnegative ray. -/
def stieltjesReciprocalMoment (μ : Measure ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∫ t : ℝ, (t + x)⁻¹ ^ n ∂μ

theorem stieltjes_reciprocal_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => (t + x)⁻¹ ^ n) μ := by
  apply (integrable_const (x⁻¹ ^ n)).mono'
    ((measurable_id.add_const x).inv.pow_const n).aestronglyMeasurable
  filter_upwards [hμ] with t ht
  change ‖(t + x)⁻¹ ^ n‖ ≤ x⁻¹ ^ n
  rw [Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr (by linarith)) _)]
  exact pow_le_pow_left₀ (inv_nonneg.mpr (by linarith))
    (inv_anti₀ hx (by linarith)) n

theorem stieltjes_reciprocal_derivative (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (stieltjesReciprocalMoment μ (n + 1))
      (-((n + 1 : ℕ) : ℝ) * stieltjesReciprocalMoment μ (n + 2) x) x := by
  have hnear {y : ℝ} (hy : y ∈ Metric.ball x (x / 2)) : x / 2 < y := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
    linarith [hy.1]
  have hd (t y : ℝ) (ht : 0 ≤ t) (hy : 0 < y) :
      HasDerivAt (fun z : ℝ => (t + z)⁻¹ ^ (n + 1))
        (-((n + 1 : ℕ) : ℝ) * (t + y)⁻¹ ^ (n + 2)) y := by
    have hne : t + y ≠ 0 := (add_pos_of_nonneg_of_pos ht hy).ne'
    have hinv : HasDerivAt (fun z : ℝ => (t + z)⁻¹) (-(t + y)⁻¹ ^ 2) y := by
      convert ((hasDerivAt_id y).const_add t).inv hne using 1
      simp only [id_eq, one_div, div_eq_mul_inv, inv_pow]
      ring
    convert hinv.pow (n + 1) using 1
    simp only [Nat.add_sub_cancel, pow_succ]
    ring
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (x₀ := x) (ε := x / 2)
    (F := fun y t : ℝ => (t + y)⁻¹ ^ (n + 1))
    (F' := fun y t : ℝ => -((n + 1 : ℕ) : ℝ) * (t + y)⁻¹ ^ (n + 2))
    (bound := fun _ : ℝ => ((n + 1 : ℕ) : ℝ) * (x / 2)⁻¹ ^ (n + 2))
    (by positivity)
    (Eventually.of_forall fun y =>
      ((measurable_id.add_const y).inv.pow_const (n + 1)).aestronglyMeasurable)
    (stieltjes_reciprocal_integrable μ hμ (n + 1) hx)
    ((measurable_const.mul ((measurable_id.add_const x).inv.pow_const (n + 2))).aestronglyMeasurable)
    ?_ (integrable_const _) ?_
  · simpa only [stieltjesReciprocalMoment, integral_mul_left] using hi.2
  · filter_upwards [hμ] with t ht
    intro y hy
    have hy' := hnear hy
    have hty : 0 < t + y := by linarith
    rw [norm_mul, norm_neg, Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hty.le) _)]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact pow_le_pow_left₀ (inv_nonneg.mpr hty.le)
      (inv_anti₀ (by positivity) (by linarith)) _
  · filter_upwards [hμ] with t ht
    intro y hy
    exact hd t y ht (by have := hnear hy; linarith)


/-- Equality on an open set determines every positive reciprocal moment there. -/
theorem stieltjes_local_eq_reciprocal_moments (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    {U : Set ℝ} (hU : IsOpen U) (hpos : U ⊆ Ioi 0)
    (heq : EqOn (probabilityStieltjes μ) (probabilityStieltjes ν) U) :
    ∀ n : ℕ, EqOn (stieltjesReciprocalMoment μ (n + 1))
      (stieltjesReciprocalMoment ν (n + 1)) U := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simpa only [stieltjesReciprocalMoment, probabilityStieltjes, zero_add, pow_one] using heq hx
  | succ n ih =>
      intro x hx
      have he : stieltjesReciprocalMoment μ (n + 1) =ᶠ[𝓝 x]
          stieltjesReciprocalMoment ν (n + 1) :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds hx, ih⟩
      have hd := he.deriv_eq
      rw [(stieltjes_reciprocal_derivative μ hμ n (hpos hx)).deriv,
        (stieltjes_reciprocal_derivative ν hν n (hpos hx)).deriv] at hd
      have hn : -((n + 1 : ℕ) : ℝ) ≠ 0 := neg_ne_zero.mpr (by positivity)
      exact mul_left_cancel₀ hn hd


/-- Compact coordinate for the reciprocal-moment inverse. -/
def stieltjesCompactCoordinate (x : ℝ) (hx : 0 < x) (t : ℝ) : OpUnitInterval :=
  ⟨x / (max t 0 + x), by positivity,
    (div_le_one (by positivity)).mpr (by have := le_max_right t 0; linarith)⟩

theorem stieltjes_compact_continuous (x : ℝ) (hx : 0 < x) :
    Continuous (stieltjesCompactCoordinate x hx) :=
  (continuous_const.div ((continuous_id.max continuous_const).add continuous_const)
    (fun t => (show 0 < max t 0 + x by positivity).ne')).subtype_mk _

def stieltjesCompactDecode (x : ℝ) (q : OpUnitInterval) : ℝ := x / (q : ℝ) - x

theorem stieltjes_compact_decode (x : ℝ) (hx : 0 < x) (t : ℝ) (ht : 0 ≤ t) :
    stieltjesCompactDecode x (stieltjesCompactCoordinate x hx t) = t := by
  simp only [stieltjesCompactDecode, stieltjesCompactCoordinate, max_eq_left ht]
  field_simp

def stieltjesWeight (x t : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((t + x)⁻¹)

theorem stieltjes_weight_measurable (x : ℝ) : Measurable (stieltjesWeight x) :=
  (measurable_id.add_const x).inv.ennreal_ofReal

theorem stieltjes_weight_finite (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) {x : ℝ} (hx : 0 < x) :
    IsFiniteMeasure (μ.withDensity (stieltjesWeight x)) := by
  have hi : Integrable (fun t : ℝ => (t + x)⁻¹) μ := by
    simpa using stieltjes_reciprocal_integrable μ hμ 1 hx
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  exact (hasFiniteIntegral_iff_ofReal (by
    filter_upwards [hμ] with t ht
    exact inv_nonneg.mpr (by linarith))).mp hi.2

theorem stieltjes_weight_reciprocal (μ : Measure ℝ)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) {x : ℝ} (hx : 0 < x) :
    (μ.withDensity (stieltjesWeight x)).withDensity
      (fun t => (stieltjesWeight x t)⁻¹) = μ := by
  apply withDensity_inv_same (stieltjes_weight_measurable x) _ (ae_of_all _ fun _ => ENNReal.ofReal_ne_top)
  filter_upwards [hμ] with t ht
  exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr (by linarith))).ne'

theorem stieltjes_weighted_compact_moment (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (∫ q : OpUnitInterval, (q : ℝ) ^ n ∂
      (μ.withDensity (stieltjesWeight x)).map (stieltjesCompactCoordinate x hx)) =
      x ^ n * stieltjesReciprocalMoment μ (n + 1) x := by
  rw [integral_map (stieltjes_compact_continuous x hx).measurable.aemeasurable
    (continuous_subtype_val.pow n).aestronglyMeasurable]
  change (∫ t : ℝ, _ ∂μ.withDensity
    (fun t => (Real.toNNReal ((t + x)⁻¹) : ℝ≥0∞))) = _
  have hw : Measurable (fun t : ℝ => Real.toNNReal ((t + x)⁻¹)) :=
    (measurable_id.add_const x).inv.real_toNNReal
  rw [integral_withDensity_eq_integral_smul hw]
  unfold stieltjesReciprocalMoment
  rw [← integral_mul_left]
  apply integral_congr_ae
  filter_upwards [hμ] with t ht
  simp only [NNReal.smul_def, smul_eq_mul, stieltjesCompactCoordinate, max_eq_left ht,
    Real.coe_toNNReal _ (inv_nonneg.mpr (by linarith : 0 ≤ t + x))]
  rw [div_eq_mul_inv, mul_pow, pow_succ]
  ring

theorem stieltjes_compact_map_injective (μ ν : Measure ℝ)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    {x : ℝ} (hx : 0 < x)
    (he : μ.map (stieltjesCompactCoordinate x hx) =
      ν.map (stieltjesCompactCoordinate x hx)) : μ = ν := by
  have hm : Measurable (stieltjesCompactDecode x) :=
    (measurable_const.div measurable_subtype_coe).sub_const x
  have hback (ρ : Measure ℝ) (hρ : ∀ᵐ t ∂ρ, 0 ≤ t) :
      (ρ.map (stieltjesCompactCoordinate x hx)).map (stieltjesCompactDecode x) = ρ := by
    rw [Measure.map_map hm (stieltjes_compact_continuous x hx).measurable]
    calc
      _ = ρ.map id := by
        apply Measure.map_congr
        filter_upwards [hρ] with t ht
        exact stieltjes_compact_decode x hx t ht
      _ = ρ := Measure.map_id
  have hb := congrArg (fun ρ => ρ.map (stieltjesCompactDecode x)) he
  dsimp only at hb
  rwa [hback μ hμ, hback ν hν] at hb

/-- All positive reciprocal moments at one positive coordinate identify the measure. -/
theorem stieltjes_reciprocal_moments_unique (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    {x : ℝ} (hx : 0 < x)
    (he : ∀ n : ℕ, stieltjesReciprocalMoment μ (n + 1) x =
      stieltjesReciprocalMoment ν (n + 1) x) : μ = ν := by
  letI := stieltjes_weight_finite μ hμ hx
  letI := stieltjes_weight_finite ν hν hx
  have hcompact : (μ.withDensity (stieltjesWeight x)).map (stieltjesCompactCoordinate x hx) =
      (ν.withDensity (stieltjesWeight x)).map (stieltjesCompactCoordinate x hx) := by
    apply operator_hausdorff_moment_unique
    intro n
    rw [stieltjes_weighted_compact_moment μ hμ hx n,
      stieltjes_weighted_compact_moment ν hν hx n, he n]
  have hweighted := stieltjes_compact_map_injective
    (μ.withDensity (stieltjesWeight x)) (ν.withDensity (stieltjesWeight x))
    ((withDensity_absolutelyContinuous _ _) hμ)
    ((withDensity_absolutelyContinuous _ _) hν) hx hcompact
  have hback := congrArg (fun ρ : Measure ℝ =>
    ρ.withDensity (fun t => (stieltjesWeight x t)⁻¹)) hweighted
  dsimp only at hback
  rwa [stieltjes_weight_reciprocal μ hμ hx, stieltjes_weight_reciprocal ν hν hx] at hback

theorem probability_stieltjes_unique_on_open_set (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty) (hpos : U ⊆ Ioi 0)
    (he : EqOn (probabilityStieltjes μ) (probabilityStieltjes ν) U) : μ = ν := by
  obtain ⟨x, hx⟩ := hne
  exact stieltjes_reciprocal_moments_unique μ ν hμ hν (hpos hx)
    (fun n => stieltjes_local_eq_reciprocal_moments μ ν hμ hν hU hpos he n hx)

theorem probability_stieltjes_unique (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    (he : ∀ x : ℝ, 0 < x → probabilityStieltjes μ x = probabilityStieltjes ν x) :
    μ = ν :=
  probability_stieltjes_unique_on_open_set μ ν hμ hν isOpen_Ioi
    ⟨1, by norm_num⟩ (Subset.refl _) (fun _ hx => he _ hx)


theorem probability_stieltjes_unique_on_interval (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (he : ∀ x ∈ Ioo a b, probabilityStieltjes μ x = probabilityStieltjes ν x) :
    μ = ν :=
  probability_stieltjes_unique_on_open_set μ ν hμ hν isOpen_Ioo
    (nonempty_Ioo.mpr hab) (fun _ hx => ha.trans_lt hx.1) he

theorem gamma_laplace_smooth :
    ContDiffOn ℝ ⊤ gammaLaplaceFunction (Ioi 0) := by
  apply ContDiffOn.pow
  apply ContDiffOn.inv
  · exact contDiffOn_const.add contDiffOn_id
  · intro x hx
    exact (show 0 < 1 + x by have := mem_Ioi.mp hx; linarith).ne'


/-- The Gamma target inverse on any nonempty open set of positive parameters. -/
theorem gamma_stieltjes_identifies (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) {U : Set ℝ} (hU : IsOpen U)
    (hne : U.Nonempty) (hpos : U ⊆ Ioi 0)
    (he : EqOn (probabilityStieltjes μ) (probabilityStieltjes gammaProbability) U) :
    μ = gammaProbability := by
  have hg : ∀ᵐ t ∂gammaProbability, 0 ≤ t := by
    simpa only [ae_iff, not_le] using gamma_probability_negative_ray
  exact probability_stieltjes_unique_on_open_set μ gammaProbability hμ hg hU hne hpos he

end
end Sigma
