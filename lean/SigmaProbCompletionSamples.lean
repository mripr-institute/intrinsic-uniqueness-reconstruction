import SigmaProbCompletion
import SigmaProbLevyIntegral

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

def exponentialTilt (μ : Measure ℝ) (a : ℝ) : Measure ℝ :=
  μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-(a*x))))

theorem exponential_tilt_finite (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (a : ℝ) (ha : 0 ≤ a) : IsFiniteMeasure (exponentialTilt μ a) := by
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  apply lt_of_le_of_lt (show (∫⁻ x, ENNReal.ofReal (Real.exp (-(a*x))) ∂μ) ≤
      ∫⁻ _ : ℝ, (1:ℝ≥0∞) ∂μ from ?_) (by simp)
  apply lintegral_mono_ae
  filter_upwards [hμ] with x hx
  exact ENNReal.ofReal_le_one.mpr
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ha hx)))

theorem exponential_tilt_nonnegative (μ : Measure ℝ)
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (a : ℝ) : ∀ᵐ x ∂exponentialTilt μ a, 0 ≤ x :=
  (withDensity_absolutelyContinuous μ _).ae_le hμ

theorem exponential_tilt_laplace (μ : Measure ℝ) (a s : ℝ) :
    realLaplace (exponentialTilt μ a) s = realLaplace μ (a+s) := by
  rw [realLaplace, exponentialTilt]
  change (∫ x, Real.exp (-(s*x)) ∂μ.withDensity
    (fun x => ((Real.toNNReal (Real.exp (-(a*x))) : ℝ≥0) : ℝ≥0∞))) = _
  have hm : Measurable (fun x : ℝ => Real.toNNReal (Real.exp (-(a*x)))) := by fun_prop
  rw [integral_withDensity_eq_integral_smul hm]
  apply integral_congr_ae
  filter_upwards with x
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.exp_pos _).le,
    ← Real.exp_add]
  congr 1
  ring

theorem exponential_tilt_injective (a : ℝ) : Function.Injective (fun μ : Measure ℝ => exponentialTilt μ a) := by
  intro μ ν he
  change exponentialTilt μ a = exponentialTilt ν a at he
  have hb (ρ : Measure ℝ) :
      (exponentialTilt ρ a).withDensity (fun x => (ENNReal.ofReal (Real.exp (-(a*x))))⁻¹) = ρ := by
    exact withDensity_inv_same (((measurable_const.mul measurable_id).neg.exp).ennreal_ofReal)
      (ae_of_all _ (fun x => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'))
      (ae_of_all _ (fun x => ENNReal.ofReal_ne_top))
  rw [← hb μ, he, hb ν]

/-- Every integer tail of a nonnegative finite measure's Laplace transform
determines the full measure; no zeroth sample is required. -/
theorem nonnegative_integer_tail_laplace_unique (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hν : ∀ᵐ x ∂ν, 0 ≤ x) (N : ℕ)
    (he : ∀ n : ℕ, N ≤ n → realLaplace μ n = realLaplace ν n) : μ = ν := by
  letI := exponential_tilt_finite μ hμ N (Nat.cast_nonneg N)
  letI := exponential_tilt_finite ν hν N (Nat.cast_nonneg N)
  apply exponential_tilt_injective N
  apply nonnegative_integer_laplace_unique _ _ (exponential_tilt_nonnegative μ hμ N)
    (exponential_tilt_nonnegative ν hν N)
  intro n
  rw [exponential_tilt_laplace, exponential_tilt_laplace, ← Nat.cast_add]
  exact he (N+n) (Nat.le_add_right N n)

/-- The ordinary Lévy--Khintchine representation category specified in O6. -/
structure BernsteinRepresentation where
  killing : ℝ
  drift : ℝ
  killing_nonnegative : 0 ≤ killing
  drift_nonnegative : 0 ≤ drift
  levy : Measure ℝ
  levy_positive_support : ∀ᵐ x ∂levy, 0 < x
  levy_integrable : Integrable (fun x => min 1 x) levy

def BernsteinRepresentation.exponent (B : BernsteinRepresentation) (l : ℝ) : ℝ :=
  B.killing+B.drift*l+∫ x, 1-Real.exp (-(l*x)) ∂B.levy

theorem levy_exponent_kernel_bound (l x : ℝ) (hl : 0 ≤ l) (hx : 0 ≤ x) :
    ‖1-Real.exp (-(l*x))‖ ≤ max 1 l*min 1 x := by
  have hn : 0 ≤ 1-Real.exp (-(l*x)) := by
    have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hl hx)); linarith
  have hb : 1-Real.exp (-(l*x)) ≤ l*x := by
    have := Real.add_one_le_exp (-(l*x)); linarith
  have h1 : 1-Real.exp (-(l*x)) ≤ 1 := by linarith [Real.exp_pos (-(l*x))]
  rw [Real.norm_of_nonneg hn]
  by_cases hx1 : x ≤ 1
  · rw [min_eq_right hx1]
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_right 1 l) hx)
  · rw [min_eq_left (le_of_not_ge hx1), mul_one]
    exact h1.trans (le_max_left 1 l)

theorem BernsteinRepresentation.kernel_integrable (B : BernsteinRepresentation)
    (l : ℝ) (hl : 0 ≤ l) : Integrable (fun x => 1-Real.exp (-(l*x))) B.levy := by
  apply (B.levy_integrable.const_mul (max 1 l)).mono'
    ((measurable_const.sub (measurable_const.mul measurable_id).neg.exp).aestronglyMeasurable)
  filter_upwards [B.levy_positive_support] with x hx
  exact levy_exponent_kernel_bound l x hl hx.le

def BernsteinRepresentation.incrementMeasure (B : BernsteinRepresentation) : Measure ℝ :=
  ENNReal.ofReal B.drift • Measure.dirac 0 +
    B.levy.withDensity (fun x => ENNReal.ofReal (1-Real.exp (-x)))

theorem BernsteinRepresentation.weighted_levy_finite (B : BernsteinRepresentation) :
    IsFiniteMeasure (B.levy.withDensity (fun x => ENNReal.ofReal (1-Real.exp (-x)))) := by
  apply isFiniteMeasure_withDensity
  have hi : Integrable (fun x => 1-Real.exp (-x)) B.levy := by
    simpa using B.kernel_integrable 1 (by norm_num)
  apply (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable ?_).mpr hi
  filter_upwards [B.levy_positive_support] with x hx
  change 0 ≤ 1-Real.exp (-x)
  have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.le)
  linarith

instance BernsteinRepresentation.increment_finite (B : BernsteinRepresentation) :
    IsFiniteMeasure B.incrementMeasure := by
  letI := B.weighted_levy_finite
  haveI : IsFiniteMeasure (ENNReal.ofReal B.drift • Measure.dirac (0:ℝ)) :=
    ⟨by simp⟩
  unfold incrementMeasure
  infer_instance

theorem BernsteinRepresentation.increment_nonnegative (B : BernsteinRepresentation) :
    ∀ᵐ x ∂B.incrementMeasure, 0 ≤ x := by
  rw [incrementMeasure, ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure (by simp) _
  · exact (withDensity_absolutelyContinuous B.levy _).ae_le
      (B.levy_positive_support.mono (fun x hx => hx.le))

theorem BernsteinRepresentation.weighted_levy_integral (B : BernsteinRepresentation) (f : ℝ → ℝ) :
    (∫ x, f x ∂B.levy.withDensity (fun x => ENNReal.ofReal (1-Real.exp (-x)))) =
      ∫ x, (1-Real.exp (-x))*f x ∂B.levy := by
  change (∫ x, f x ∂B.levy.withDensity
    (fun x => ((Real.toNNReal (1-Real.exp (-x)) : ℝ≥0) : ℝ≥0∞))) = _
  have hm : Measurable (fun x : ℝ => Real.toNNReal (1-Real.exp (-x))) := by fun_prop
  rw [integral_withDensity_eq_integral_smul hm]
  apply integral_congr_ae
  filter_upwards [B.levy_positive_support] with x hx
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal]
  have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.le)
  linarith

theorem BernsteinRepresentation.increment_laplace (B : BernsteinRepresentation)
    (l : ℝ) (hl : 0 ≤ l) :
    realLaplace B.incrementMeasure l = B.exponent (l+1)-B.exponent l := by
  let W := B.levy.withDensity (fun x => ENNReal.ofReal (1-Real.exp (-x)))
  letI : IsFiniteMeasure W := B.weighted_levy_finite
  have hW : ∀ᵐ x ∂W, 0 ≤ x :=
    (withDensity_absolutelyContinuous B.levy _).ae_le
      (B.levy_positive_support.mono fun x hx => hx.le)
  have hi : Integrable (fun x => Real.exp (-(l*x))) W := by
    apply (integrable_const (1:ℝ)).mono'
      ((continuous_const.mul continuous_id).neg.rexp.aestronglyMeasurable)
    filter_upwards [hW] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hl hx))
  have hid : Integrable (fun x : ℝ => Real.exp (-(l*x)))
      (ENNReal.ofReal B.drift • Measure.dirac 0) := by
    apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
    exact (integrable_const (Real.exp (-(l*0)))).congr
      (ae_eq_dirac (fun x : ℝ => Real.exp (-(l*x)))).symm
  change (∫ x, Real.exp (-(l*x)) ∂((ENNReal.ofReal B.drift • Measure.dirac 0)+W)) = _
  rw [integral_add_measure hid hi, integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal B.drift_nonnegative]
  simp only [mul_zero, neg_zero, Real.exp_zero, smul_eq_mul, mul_one]
  rw [show W = B.levy.withDensity (fun x => ENNReal.ofReal (1-Real.exp (-x))) from rfl,
    B.weighted_levy_integral]
  have he : (fun x : ℝ => (1-Real.exp (-x))*Real.exp (-(l*x))) =
      fun x => (1-Real.exp (-((l+1)*x)))-(1-Real.exp (-(l*x))) := by
    funext x
    rw [show -((l+1)*x) = -x + -(l*x) by ring, Real.exp_add]
    ring
  rw [he, integral_sub (B.kernel_integrable (l+1) (by positivity)) (B.kernel_integrable l hl)]
  simp only [exponent]
  ring

theorem BernsteinRepresentation.integer_tail_increment_unique (B C : BernsteinRepresentation)
    (N : ℕ) (he : ∀ n : ℕ, N ≤ n → B.exponent n = C.exponent n) :
    B.incrementMeasure = C.incrementMeasure := by
  apply nonnegative_integer_tail_laplace_unique _ _ B.increment_nonnegative C.increment_nonnegative N
  intro n hn
  rw [B.increment_laplace n (Nat.cast_nonneg n), C.increment_laplace n (Nat.cast_nonneg n),
    ← Nat.cast_one, ← Nat.cast_add, he (n+1) (by omega), he n hn]

theorem BernsteinRepresentation.increment_restrict_positive (B : BernsteinRepresentation) :
    B.incrementMeasure.restrict (Ioi 0) =
      B.levy.withDensity (fun x => ENNReal.ofReal (1-Real.exp (-x))) := by
  rw [incrementMeasure, Measure.restrict_add, Measure.restrict_smul,
    show (Measure.dirac (0:ℝ)).restrict (Ioi 0) = 0 from
      Measure.restrict_eq_zero.mpr (by simp), smul_zero, zero_add]
  exact Measure.restrict_eq_self_of_ae_mem
    ((withDensity_absolutelyContinuous B.levy _).ae_le B.levy_positive_support)

theorem BernsteinRepresentation.levy_eq_of_increment_eq (B C : BernsteinRepresentation)
    (he : B.incrementMeasure = C.incrementMeasure) : B.levy = C.levy := by
  have hh := congrArg (fun ρ : Measure ℝ => ρ.restrict (Ioi 0)) he
  dsimp only at hh
  rw [B.increment_restrict_positive, C.increment_restrict_positive] at hh
  have hb (A : BernsteinRepresentation) :
      (A.levy.withDensity (fun x => ENNReal.ofReal (1-Real.exp (-x)))).withDensity
        (fun x => (ENNReal.ofReal (1-Real.exp (-x)))⁻¹) = A.levy := by
    apply withDensity_inv_same (by fun_prop)
    · filter_upwards [A.levy_positive_support] with x hx
      apply (ENNReal.ofReal_pos.mpr _).ne'
      have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)
      linarith
    · exact ae_of_all _ (fun _ => ENNReal.ofReal_ne_top)
  rw [← hb B, hh, hb C]

theorem BernsteinRepresentation.increment_zero_mass (B : BernsteinRepresentation) :
    B.incrementMeasure {0} = ENNReal.ofReal B.drift := by
  have hz : B.levy {0} = 0 := measure_mono_null
    (show {0} ⊆ {x : ℝ | ¬0 < x} by intro x hx; obtain rfl := Set.mem_singleton_iff.mp hx; simp)
    (ae_iff.mp B.levy_positive_support)
  have hw : B.levy.withDensity (fun x => ENNReal.ofReal (1-Real.exp (-x))) {0} = 0 :=
    (withDensity_absolutelyContinuous B.levy _) hz
  simp [incrementMeasure, hw, Measure.add_apply, Measure.smul_apply]

theorem BernsteinRepresentation.integer_tail_data_unique (B C : BernsteinRepresentation)
    (N : ℕ) (he : ∀ n : ℕ, N ≤ n → B.exponent n = C.exponent n) :
    B.killing = C.killing ∧ B.drift = C.drift ∧ B.levy = C.levy := by
  have hh := B.integer_tail_increment_unique C N he
  have hL := B.levy_eq_of_increment_eq C hh
  have hd : B.drift = C.drift := by
    have hmass := congrArg (fun ρ : Measure ℝ => ρ {0}) hh
    dsimp only at hmass
    rw [B.increment_zero_mass, C.increment_zero_mass] at hmass
    simpa only [ENNReal.toReal_ofReal B.drift_nonnegative,
      ENNReal.toReal_ofReal C.drift_nonnegative] using congrArg ENNReal.toReal hmass
  refine ⟨?_, hd, hL⟩
  have hk := he N le_rfl
  simp only [exponent, hd, hL] at hk
  linarith

theorem BernsteinRepresentation.integer_tail_unique (B C : BernsteinRepresentation)
    (N : ℕ) (he : ∀ n : ℕ, N ≤ n → B.exponent n = C.exponent n) :
    B.exponent = C.exponent := by
  obtain ⟨hk, hd, hL⟩ := B.integer_tail_data_unique C N he
  funext l
  simp only [exponent, hk, hd, hL]

/-- The actual positive Gamma Lévy measure; its total mass need not be finite. -/
def gammaCompletionLevyMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal (gammaLevyDensity x))

theorem gamma_completion_levy_positive_support :
    ∀ᵐ x ∂gammaCompletionLevyMeasure, 0 < x :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)

theorem gamma_completion_levy_density_nonnegative {x : ℝ} (hx : 0 < x) :
    0 ≤ gammaLevyDensity x := by unfold gammaLevyDensity; positivity

theorem gamma_completion_levy_integrability :
    Integrable (fun x => min 1 x) gammaCompletionLevyMeasure := by
  unfold gammaCompletionLevyMeasure
  apply (integrable_withDensity_iff_integrable_smul'
    (show Measurable (fun x => ENNReal.ofReal (gammaLevyDensity x)) by
      unfold gammaLevyDensity; fun_prop) (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mpr
  have hi : IntegrableOn (fun x : ℝ => 2*Real.exp (-x)) (Ioi 0) := by
    simpa only [one_mul] using (positive_rate_exponential_integrable 1 (by norm_num)).const_mul 2
  have hm : Measurable (fun x => (ENNReal.ofReal (gammaLevyDensity x)).toReal • min 1 x) := by
    simp only [smul_eq_mul]
    unfold gammaLevyDensity
    fun_prop
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  rw [smul_eq_mul, ENNReal.toReal_ofReal (gamma_completion_levy_density_nonnegative hx0),
    Real.norm_of_nonneg (mul_nonneg (gamma_completion_levy_density_nonnegative hx0)
      (le_min (by norm_num) hx0.le)), gammaLevyDensity]
  calc
    2*Real.exp (-x)/x*min 1 x ≤ 2*Real.exp (-x)/x*x :=
      mul_le_mul_of_nonneg_left (min_le_right 1 x) (by positivity)
    _ = _ := div_mul_cancel₀ _ hx0.ne'

def gammaBernsteinRepresentation : BernsteinRepresentation where
  killing := 0
  drift := 0
  killing_nonnegative := le_rfl
  drift_nonnegative := le_rfl
  levy := gammaCompletionLevyMeasure
  levy_positive_support := gamma_completion_levy_positive_support
  levy_integrable := gamma_completion_levy_integrability

theorem gamma_bernstein_representation_exponent (l : ℝ) (hl : 0 ≤ l) :
    gammaBernsteinRepresentation.exponent l = gammaLaplaceExponent l := by
  simp only [BernsteinRepresentation.exponent, gammaBernsteinRepresentation, zero_mul, zero_add]
  unfold gammaCompletionLevyMeasure
  change (∫ x, 1-Real.exp (-(l*x)) ∂(volume.restrict (Ioi 0)).withDensity
    (fun x => ((Real.toNNReal (gammaLevyDensity x) : ℝ≥0) : ℝ≥0∞))) = _
  have hm : Measurable (fun x => Real.toNNReal (gammaLevyDensity x)) := by
    unfold gammaLevyDensity; fun_prop
  rw [integral_withDensity_eq_integral_smul hm]
  rw [← gamma_levy_exponent_integral l hl]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (gamma_completion_levy_density_nonnegative hx), mul_comm]

/-- Every complete integer tail identifies the entire Gamma exponent and all
three actual Lévy--Khintchine data, without a supplied value at zero. -/
theorem gamma_bernstein_integer_tail_unique (B : BernsteinRepresentation) (N : ℕ)
    (he : ∀ n : ℕ, N ≤ n → B.exponent n = 2*Real.log (1+(n:ℝ))) :
    (∀ l : ℝ, 0 ≤ l → B.exponent l = 2*Real.log (1+l)) ∧
      B.killing = 0 ∧ B.drift = 0 ∧ B.levy = gammaCompletionLevyMeasure := by
  have hs (n : ℕ) (hn : N ≤ n) : B.exponent n = gammaBernsteinRepresentation.exponent n := by
    rw [he n hn, gamma_bernstein_representation_exponent n (Nat.cast_nonneg n)]
    rfl
  have hd := B.integer_tail_data_unique gammaBernsteinRepresentation N hs
  refine ⟨?_, hd⟩
  intro l hl
  rw [congrFun (B.integer_tail_unique gammaBernsteinRepresentation N hs) l,
    gamma_bernstein_representation_exponent l hl]
  rfl

/-- Membership in the usual Bernstein representation category explicitly used
in O6; values outside the nonnegative ray are not prescribed. -/
def HasBernsteinRepresentation (f : ℝ → ℝ) : Prop :=
  ∃ B : BernsteinRepresentation, ∀ l : ℝ, 0 ≤ l → f l = B.exponent l

theorem bernstein_function_integer_tail_unique (f g : ℝ → ℝ)
    (hf : HasBernsteinRepresentation f) (hg : HasBernsteinRepresentation g)
    (N : ℕ) (he : ∀ n : ℕ, N ≤ n → f n = g n) :
    ∀ l : ℝ, 0 ≤ l → f l = g l := by
  obtain ⟨B,hB⟩ := hf
  obtain ⟨C,hC⟩ := hg
  have hs (n : ℕ) (hn : N ≤ n) : B.exponent n = C.exponent n := by
    rw [← hB n (Nat.cast_nonneg n), ← hC n (Nat.cast_nonneg n), he n hn]
  intro l hl
  rw [hB l hl, hC l hl, B.integer_tail_unique C N hs]

theorem gamma_laplace_exponent_has_bernstein_representation :
    HasBernsteinRepresentation gammaLaplaceExponent :=
  ⟨gammaBernsteinRepresentation, fun l hl => (gamma_bernstein_representation_exponent l hl).symm⟩

/-- P8-samples in the representation category of O6, in fact valid also for
N=0 and at the endpoint l=0. No value of f at zero is assumed. -/
theorem gamma_bernstein_function_integer_tail_unique (f : ℝ → ℝ)
    (hf : HasBernsteinRepresentation f) (N : ℕ)
    (he : ∀ n : ℕ, N ≤ n → f n = 2*Real.log (1+(n:ℝ))) :
    ∀ l : ℝ, 0 ≤ l → f l = 2*Real.log (1+l) := by
  exact bernstein_function_integer_tail_unique f gammaLaplaceExponent hf
    gamma_laplace_exponent_has_bernstein_representation N he

/-- The paper's smooth nonnegative perturbation, invisible on the marked
nonnegative integer spectrum. -/
def smoothIntegerInvisibleExponent (l : ℝ) : ℝ :=
  gammaLaplaceExponent l + Real.sin (Real.pi * l) ^ 2

theorem smooth_integer_invisible_exponent_boundary :
    ContDiffOn ℝ ⊤ smoothIntegerInvisibleExponent (Set.Ici 0) ∧
    (∀ l : ℝ, 0 ≤ l → 0 ≤ smoothIntegerInvisibleExponent l) ∧
    (∀ n : ℕ, smoothIntegerInvisibleExponent n = gammaLaplaceExponent n) ∧
    smoothIntegerInvisibleExponent (1 / 2) ≠ gammaLaplaceExponent (1 / 2) ∧
    ¬ HasBernsteinRepresentation smoothIntegerInvisibleExponent := by
  have hsmooth : ContDiffOn ℝ ⊤ gammaLaplaceExponent (Set.Ici 0) := by
    intro l hl
    apply ContDiffAt.contDiffWithinAt
    unfold gammaLaplaceExponent
    exact contDiffAt_const.mul ((contDiffAt_const.add contDiffAt_id).log (by
      dsimp only [id_eq]
      exact ne_of_gt (by have hl0 : 0 ≤ l := hl; linarith)))
  have hsin : ContDiff ℝ ⊤ (fun l : ℝ => Real.sin (Real.pi * l) ^ 2) :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).pow 2
  have hsamples : ∀ n : ℕ,
      smoothIntegerInvisibleExponent n = gammaLaplaceExponent n := by
    intro n
    have hpi : Real.pi * (n : ℝ) = ((n : ℤ) : ℝ) * Real.pi := by
      push_cast
      ring
    simp [smoothIntegerInvisibleExponent, hpi]
  have hhalf : smoothIntegerInvisibleExponent (1 / 2) ≠
      gammaLaplaceExponent (1 / 2) := by
    rw [smoothIntegerInvisibleExponent,
      show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring,
      Real.sin_pi_div_two]
    norm_num
  refine ⟨hsmooth.add hsin.contDiffOn, ?_, hsamples, hhalf, ?_⟩
  · intro l hl
    unfold smoothIntegerInvisibleExponent gammaLaplaceExponent
    have hlog : 0 ≤ Real.log (1 + l) := Real.log_nonneg (by linarith)
    positivity
  · intro hbernstein
    have he := bernstein_function_integer_tail_unique smoothIntegerInvisibleExponent
      gammaLaplaceExponent hbernstein gamma_laplace_exponent_has_bernstein_representation
      0 (fun n _ => hsamples n) (1 / 2) (by norm_num)
    exact hhalf he

end
end Sigma
