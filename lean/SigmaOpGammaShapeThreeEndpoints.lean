import SigmaOpGammaShapeThree
import SigmaOpZeroEnergy
import Mathlib.Analysis.SpecialFunctions.Integrals

namespace Sigma
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal ENNReal
set_option maxHeartbeats 800000

def gammaShapeThreeDensity (t : ℝ) : ℝ := t^2 * Real.exp (-t) / 2

def gammaShapeThreeFlux (t : ℝ) : ℝ := t^3 * Real.exp (-t) / 2

def gammaShapeThreeDivergenceExpression (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  -(gammaShapeThreeDensity t : ℂ)⁻¹ *
    deriv (fun s => (gammaShapeThreeFlux s : ℂ) * deriv F s) t

theorem gamma_shape_three_flux_hasDerivAt (t : ℝ) :
    HasDerivAt gammaShapeThreeFlux ((3-t)*gammaShapeThreeDensity t) t := by
  have hd := (((hasDerivAt_id t).pow 3).mul
    (((hasDerivAt_id t).neg).exp)).div_const 2
  convert hd using 1
  dsimp [gammaShapeThreeFlux,gammaShapeThreeDensity]
  ring

/-- The literal divergence-form expression is exactly the paper's
`-t f'' -(3-t) f'` on smooth functions. -/
theorem gamma_shape_three_divergence_eq_classical (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) {t : ℝ} (ht : 0 < t) :
    gammaShapeThreeDivergenceExpression f t =
      -(t : ℂ)*deriv (deriv f) t - (3-(t : ℂ))*deriv f t := by
  have hfd := (contDiff_infty_iff_deriv.mp hf).2
  have hd : HasDerivAt (fun s => (gammaShapeThreeFlux s : ℂ)*deriv f s)
      ((((3-t)*gammaShapeThreeDensity t : ℝ) : ℂ)*deriv f t +
        (gammaShapeThreeFlux t : ℂ)*deriv (deriv f) t) t := by
    simpa only [Function.comp_apply] using
      (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
        (gamma_shape_three_flux_hasDerivAt t)).mul
        ((hfd.differentiable (by simp) t).hasDerivAt)
  have hp : (gammaShapeThreeDensity t : ℂ) ≠ 0 := by
    have hreal : 0 < gammaShapeThreeDensity t := by dsimp [gammaShapeThreeDensity]; positivity
    exact_mod_cast hreal.ne'
  simp only [gammaShapeThreeDivergenceExpression,hd.deriv,Function.comp_apply]
  have hflux : gammaShapeThreeFlux t = t*gammaShapeThreeDensity t := by
    dsimp [gammaShapeThreeFlux,gammaShapeThreeDensity]
    ring
  rw [hflux]
  push_cast
  field_simp
  ring

/-- The actual second zero-energy solution, with unit divergence-form flux. -/
def gammaShapeThreeSecondZeroSolution (t : ℝ) : ℂ :=
  ∫ s in (1:ℝ)..t, (gammaShapeThreeFlux s : ℂ)⁻¹

theorem gamma_shape_three_flux_contDiff : ContDiff ℝ ∞ gammaShapeThreeFlux := by
  exact ((contDiff_id.pow 3).mul contDiff_id.neg.exp).div_const 2

theorem gamma_shape_three_flux_ne_zero {t : ℝ} (ht : 0 < t) :
    (gammaShapeThreeFlux t : ℂ) ≠ 0 := by
  have hp : 0 < gammaShapeThreeFlux t := by dsimp [gammaShapeThreeFlux]; positivity
  exact_mod_cast hp.ne'

theorem gamma_shape_three_inverse_flux_continuousOn :
    ContinuousOn (fun t => (gammaShapeThreeFlux t : ℂ)⁻¹) (Ioi 0) :=
  (Complex.continuous_ofReal.comp gamma_shape_three_flux_contDiff.continuous).continuousOn.inv₀
    (fun _ ht => gamma_shape_three_flux_ne_zero ht)

theorem gamma_shape_three_second_zero_locally_ac :
    PositiveRayLocallyAbsolutelyContinuous gammaShapeThreeSecondZeroSolution := by
  intro l r hl ε hε
  exact positive_primitive_absolute_continuity _
    (gamma_shape_three_inverse_flux_continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (by norm_num) hl ε hε

theorem gamma_shape_three_second_zero_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt gammaShapeThreeSecondZeroSolution (gammaShapeThreeFlux t : ℂ)⁻¹ t := by
  apply gamma_shape_three_second_zero_locally_ac.hasDerivAt_of_ae_continuous
    gamma_shape_three_inverse_flux_continuousOn _ ht
  exact positive_primitive_hasDerivAt_ae _
    (gamma_shape_three_inverse_flux_continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (by norm_num)

theorem gamma_shape_three_second_zero_flux {t : ℝ} (ht : 0 < t) :
    (gammaShapeThreeFlux t : ℂ) * deriv gammaShapeThreeSecondZeroSolution t = 1 := by
  rw [(gamma_shape_three_second_zero_hasDerivAt ht).deriv,
    mul_inv_cancel₀ (gamma_shape_three_flux_ne_zero ht)]

theorem gamma_shape_three_second_zero_flux_locally_ac :
    PositiveRayLocallyAbsolutelyContinuous
      (fun t => (gammaShapeThreeFlux t : ℂ) * deriv gammaShapeThreeSecondZeroSolution t) :=
  (smooth_positive_locally_ac (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (1:ℂ)))).congr
    (fun _ ht => gamma_shape_three_second_zero_flux ht)

theorem gamma_shape_three_second_zero_divergence {t : ℝ} (ht : 0 < t) :
    gammaShapeThreeDivergenceExpression gammaShapeThreeSecondZeroSolution t = 0 := by
  have he : (fun t => (gammaShapeThreeFlux t : ℂ) * deriv gammaShapeThreeSecondZeroSolution t)
      =ᶠ[𝓝 t] (fun _ => (1:ℂ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact gamma_shape_three_second_zero_flux hs
  simp only [gammaShapeThreeDivergenceExpression, he.deriv_eq,
    (hasDerivAt_const t (1:ℂ)).deriv, mul_zero]

/-- Every locally regular zero-energy solution is a combination of the two
literal divergence-form solutions; no endpoint condition is assumed. -/
theorem gamma_shape_three_zero_solution_fundamental_system (F : ℝ → ℂ)
    (hF : PositiveRayLocallyAbsolutelyContinuous F)
    (hQ : PositiveRayLocallyAbsolutelyContinuous
      (fun t => (gammaShapeThreeFlux t : ℂ) * deriv F t))
    (hz : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), gammaShapeThreeDivergenceExpression F t = 0) :
    ∃ a b : ℂ, EqOn F (fun t => a+b*gammaShapeThreeSecondZeroSolution t) (Ioi 0) := by
  let Q : ℝ → ℂ := fun t => (gammaShapeThreeFlux t : ℂ)*deriv F t
  have hQd : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), HasDerivAt Q 0 t := by
    filter_upwards [hQ.ae_differentiableAt,hz,ae_restrict_mem measurableSet_Ioi] with t ht hzt hp
    change 0 < t at hp
    have hp0 : (gammaShapeThreeDensity t : ℂ) ≠ 0 := by
      have he : 0 < gammaShapeThreeDensity t := by dsimp [gammaShapeThreeDensity]; positivity
      exact_mod_cast he.ne'
    have hd : deriv Q t=0 := by
      change -(gammaShapeThreeDensity t : ℂ)⁻¹*deriv Q t=0 at hzt
      exact (mul_eq_zero.mp hzt).resolve_left (neg_ne_zero.mpr (inv_ne_zero hp0))
    exact hd ▸ ht.hasDerivAt
  have hconst {t : ℝ} (ht : 0 < t) : Q t=Q 1 := by
    have he := hQ.integral_eq_sub (g := fun _ => 0)
      (continuous_const.continuousOn.locallyIntegrableOn measurableSet_Ioi) hQd
      (by norm_num : (0:ℝ)<1) ht
    rw [intervalIntegral.integral_zero] at he
    exact sub_eq_zero.mp he.symm
  let D : ℝ → ℂ := fun t => F t-Q 1*gammaShapeThreeSecondZeroSolution t
  have hD : PositiveRayLocallyAbsolutelyContinuous D := hF.sub
    ((smooth_positive_locally_ac (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => Q 1))).mul
      gamma_shape_three_second_zero_locally_ac)
  have hDd : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), HasDerivAt D 0 t := by
    filter_upwards [hF.ae_differentiableAt,ae_restrict_mem measurableSet_Ioi] with t ht hp
    have he : deriv F t-Q 1*(gammaShapeThreeFlux t : ℂ)⁻¹=0 := by
      rw [← hconst hp]
      dsimp [Q]
      field_simp [gamma_shape_three_flux_ne_zero hp]
    simpa only [he] using ht.hasDerivAt.sub
      ((gamma_shape_three_second_zero_hasDerivAt hp).const_mul (Q 1))
  refine ⟨F 1,Q 1,?_⟩
  intro t ht
  have he := hD.integral_eq_sub (g := fun _ => 0)
    (continuous_const.continuousOn.locallyIntegrableOn measurableSet_Ioi) hDd
    (by norm_num : (0:ℝ)<1) ht
  simp only [intervalIntegral.integral_zero,D,gammaShapeThreeSecondZeroSolution,
    intervalIntegral.integral_same,mul_zero,sub_zero] at he
  change F t=F 1+Q 1*gammaShapeThreeSecondZeroSolution t
  dsimp [gammaShapeThreeSecondZeroSolution]
  linear_combination -he

theorem gamma_shape_three_integrable_iff_density_on {S : Set ℝ}
    (hS : MeasurableSet S) (hp : S ⊆ Ioi 0) (f : ℝ → ℝ) :
    Integrable f (gammaShapeThreeProbability.restrict S) ↔
      IntegrableOn (fun t => gammaShapeThreeDensity t * f t) S volume := by
  change Integrable f ((volume.withDensity
    (fun t => ((Real.toNNReal (gammaPDFReal 3 1 t):ℝ≥0):ℝ≥0∞))).restrict S) ↔ _
  rw [restrict_withDensity hS,
    integrable_withDensity_iff_integrable_smul ((measurable_gammaPDFReal 3 1).real_toNNReal)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem hS] with t ht
  rw [NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (gammaPDFReal_nonneg (by norm_num) (by norm_num) t),
    gamma_shape_three_pdf, if_pos (le_of_lt (hp ht))]
  rfl

theorem gamma_shape_three_second_zero_real (t : ℝ) :
    gammaShapeThreeSecondZeroSolution t =
      Complex.ofReal (∫ s in (1:ℝ)..t, (gammaShapeThreeFlux s)⁻¹) := by
  simp only [gammaShapeThreeSecondZeroSolution, ← Complex.ofReal_inv,
    intervalIntegral.integral_ofReal]

private theorem inverse_flux_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun s => (gammaShapeThreeFlux s)⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ((gamma_shape_three_flux_contDiff.continuous.continuousOn).inv₀
    (fun t ht => by
      have hp : 0 < gammaShapeThreeFlux t := by
        dsimp [gammaShapeThreeFlux]
        have ht0 : 0 < t := ht
        positivity
      exact hp.ne')).mono
  intro t ht
  exact (lt_min ha hb).trans_le ht.1

private theorem inverse_flux_nonneg {s : ℝ} (hs : 0 < s) :
    0 ≤ (gammaShapeThreeFlux s)⁻¹ := by
  dsimp [gammaShapeThreeFlux]
  positivity

private theorem inverse_flux_eq {s : ℝ} :
    (gammaShapeThreeFlux s)⁻¹ = 2 * Real.exp s / s^3 := by
  dsimp [gammaShapeThreeFlux]
  rw [inv_div, div_eq_mul_inv, mul_inv_rev, ← Real.exp_neg, neg_neg]
  ring

/-- A concrete lower bound for the second solution in every sufficiently
small positive neighborhood, avoiding any appeal to unformalized asymptotics. -/
theorem gamma_shape_three_second_zero_zero_bound {t : ℝ} (ht : 0 < t) (hsmall : t ≤ 1/2) :
    1/(4*t^2) ≤ ‖gammaShapeThreeSecondZeroSolution t‖ := by
  have h2t : 0 < 2*t := by positivity
  have h2t1 : 2*t ≤ 1 := by linarith
  have hlow : 1/(4*t^2) ≤ ∫ s in t..2*t, (gammaShapeThreeFlux s)⁻¹ := by
    have hh := intervalIntegral.integral_mono_on (by linarith : t ≤ 2*t)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 1/(4*t^3)) volume t (2*t))
      (inverse_flux_intervalIntegrable ht h2t) (fun s hs => ?_)
    · simpa only [intervalIntegral.integral_const, smul_eq_mul] using hh
        |> fun h => by convert h using 1; field_simp; ring
    · rw [inverse_flux_eq]
      have hs0 : 0 < s := ht.trans_le hs.1
      have hexp : 1 ≤ Real.exp s := (Real.one_le_exp_iff).mpr hs0.le
      have hpow : s^3 ≤ 8*t^3 := by
        have h := pow_le_pow_left₀ hs0.le hs.2 3
        nlinarith
      apply (div_le_div_iff₀ (by positivity : 0 < 4*t^3) (by positivity : 0 < s^3)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hexp (by positivity : 0 ≤ 8*t^3)]
  have hmono := intervalIntegral.integral_mono_interval (le_refl t)
    (by linarith : t ≤ 2*t) h2t1
    ((ae_restrict_mem measurableSet_Ioc).mono
      (fun s hs => inverse_flux_nonneg (ht.trans hs.1)))
    (inverse_flux_intervalIntegrable ht (by norm_num : (0:ℝ)<1))
  rw [gamma_shape_three_second_zero_real, Complex.norm_real, Real.norm_eq_abs,
    intervalIntegral.integral_symm, abs_neg]
  exact (hlow.trans hmono).trans (le_abs_self _)

theorem gamma_shape_three_second_zero_infinity_bound {t : ℝ} (ht : 2 ≤ t) :
    2 * Real.exp (t-1) / t^3 ≤ ‖gammaShapeThreeSecondZeroSolution t‖ := by
  have ht0 : 0 < t := by linarith
  have htm : 0 < t-1 := by linarith
  have hlow : 2 * Real.exp (t-1) / t^3 ≤
      ∫ s in (t-1)..t, (gammaShapeThreeFlux s)⁻¹ := by
    have hh := intervalIntegral.integral_mono_on (by linarith : t-1 ≤ t)
      (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ => 2 * Real.exp (t-1) / t^3) volume (t-1) t)
      (inverse_flux_intervalIntegrable htm ht0) (fun s hs => ?_)
    · simpa only [intervalIntegral.integral_const, smul_eq_mul,
        show t-(t-1)=1 by ring, one_mul] using hh
    · rw [inverse_flux_eq]
      have hs0 : 0 < s := htm.trans_le hs.1
      exact div_le_div₀ (by positivity) (by gcongr; exact hs.1)
        (by positivity) (pow_le_pow_left₀ hs0.le hs.2 3)
  have hmono := intervalIntegral.integral_mono_interval (by linarith : 1 ≤ t-1)
    (by linarith : t-1 ≤ t) (le_refl t)
    ((ae_restrict_mem measurableSet_Ioc).mono
      (fun s hs => inverse_flux_nonneg (lt_trans zero_lt_one hs.1)))
    (inverse_flux_intervalIntegrable (by norm_num : (0:ℝ)<1) ht0)
  rw [gamma_shape_three_second_zero_real, Complex.norm_real, Real.norm_eq_abs]
  exact (hlow.trans hmono).trans (le_abs_self _)

theorem gamma_shape_three_second_zero_weighted_zero_bound {t : ℝ}
    (ht : 0 < t) (hsmall : t ≤ 1/2) :
    Real.exp (-1) / (32*t^2) ≤
      gammaShapeThreeDensity t * ‖gammaShapeThreeSecondZeroSolution t‖^2 := by
  have hsq := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1/(4*t^2))
    (gamma_shape_three_second_zero_zero_bound ht hsmall) 2
  have hexp : Real.exp (-1) ≤ Real.exp (-t) := by gcongr; linarith
  have hd : 0 ≤ gammaShapeThreeDensity t := by dsimp [gammaShapeThreeDensity]; positivity
  calc
    _ = (t^2 * Real.exp (-1) / 2) * (1/(4*t^2))^2 := by field_simp; ring
    _ ≤ gammaShapeThreeDensity t * (1/(4*t^2))^2 := by
      dsimp [gammaShapeThreeDensity]
      gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq hd

theorem gamma_shape_three_second_zero_weighted_infinity_bound {t : ℝ}
    (ht : 2 ≤ t) :
    Real.exp (-2) / 12 ≤
      gammaShapeThreeDensity t * ‖gammaShapeThreeSecondZeroSolution t‖^2 := by
  have ht0 : 0 < t := by linarith
  have hsq := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2*Real.exp (t-1)/t^3)
    (gamma_shape_three_second_zero_infinity_bound ht) 2
  have hd : 0 ≤ gammaShapeThreeDensity t := by dsimp [gammaShapeThreeDensity]; positivity
  have hfactor : gammaShapeThreeDensity t * (2*Real.exp (t-1)/t^3)^2 =
      2*Real.exp (-2)*Real.exp t/t^4 := by
    dsimp [gammaShapeThreeDensity]
    have he : Real.exp (-t) * Real.exp (t-1)^2 = Real.exp (-2)*Real.exp t := by
      rw [sq, ←Real.exp_add, ←Real.exp_add, ←Real.exp_add]
      congr 1
      ring
    field_simp
    nlinarith [he]
  have he := Real.pow_div_factorial_le_exp t ht0.le 4
  norm_num [Nat.factorial] at he
  calc
    _ ≤ 2*Real.exp (-2)*Real.exp t/t^4 := by
      apply (le_div_iff₀ (by positivity : 0 < t^4)).mpr
      nlinarith [mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2*Real.exp (-2))]
    _ = gammaShapeThreeDensity t * (2*Real.exp (t-1)/t^3)^2 := hfactor.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq hd

/-- The second actual solution is not weighted square integrable on any
neighborhood of zero for the paper's Gamma-three probability. -/
theorem gamma_shape_three_second_zero_not_l2_at_zero (r : ℝ) (hr : 0 < r) :
    ¬Memℒp gammaShapeThreeSecondZeroSolution 2
      (gammaShapeThreeProbability.restrict (Ioo 0 r)) := by
  intro hi
  have his := (memℒp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mp hi
  have hw := (gamma_shape_three_integrable_iff_density_on measurableSet_Ioo
    Ioo_subset_Ioi_self _).mp his
  let b : ℝ := min r (1/2)
  have hb : 0 < b := lt_min hr (by norm_num)
  have hwb : IntegrableOn
      (fun t => gammaShapeThreeDensity t * ‖gammaShapeThreeSecondZeroSolution t‖^2)
      (Ioo 0 b) volume :=
    hw.mono_set (Ioo_subset_Ioo le_rfl (min_le_left r (1/2)))
  have hinv : IntegrableOn (fun t : ℝ => (t^2)⁻¹) (Ioo 0 b) volume := by
    apply (hwb.const_mul (32 / Real.exp (-1))).mono'
    · exact ((measurable_id.pow_const 2).inv).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : 0 < t := ht.1
      have hs : t ≤ 1/2 := (le_of_lt ht.2).trans (min_le_right _ _)
      have h := gamma_shape_three_second_zero_weighted_zero_bound ht.1 hs
      rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (t^2)⁻¹)]
      have he : 0 < Real.exp (-1) := Real.exp_pos _
      calc
        (t^2)⁻¹ = (32/Real.exp (-1)) * (Real.exp (-1)/(32*t^2)) := by
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
  have hrpow : IntegrableOn (fun t : ℝ => t^(-2 : ℝ)) (Ioo 0 b) volume := by
    apply hinv.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.rpow_neg ht.1.le, Real.rpow_two]
  have hbad := (intervalIntegral.integrableOn_Ioo_rpow_iff hb).mp hrpow
  norm_num at hbad

/-- At infinity the weighted square is bounded below by a fixed positive
constant, so it cannot be integrable on any positive tail. -/
theorem gamma_shape_three_second_zero_not_l2_at_infinity (r : ℝ) (hr : 0 < r) :
    ¬Memℒp gammaShapeThreeSecondZeroSolution 2
      (gammaShapeThreeProbability.restrict (Ioi r)) := by
  intro hi
  have his := (memℒp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mp hi
  have hw := (gamma_shape_three_integrable_iff_density_on measurableSet_Ioi
    (fun _ ht => hr.trans ht) _).mp his
  have hwt := hw.mono_set (Ioi_subset_Ioi (le_max_left r 2))
  have hc : IntegrableOn (fun _ : ℝ => Real.exp (-2) / 12) (Ioi (max r 2)) volume := by
    apply hwt.mono' aestronglyMeasurable_const
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < Real.exp (-2)/12)]
    exact gamma_shape_three_second_zero_weighted_infinity_bound
      ((le_max_right r 2).trans ht.le)
  have hbad := integrableOn_const.mp hc
  rcases hbad with hz | hfinite
  · exact (ne_of_gt (by positivity : 0 < Real.exp (-2)/12)) hz
  · simp at hfinite

def GammaShapeThreeZeroEnergySolution (F : ℝ → ℂ) : Prop :=
  PositiveRayLocallyAbsolutelyContinuous F ∧
  PositiveRayLocallyAbsolutelyContinuous (fun t => (gammaShapeThreeFlux t : ℂ)*deriv F t) ∧
  ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), gammaShapeThreeDivergenceExpression F t=0

def GammaShapeThreeSquareIntegrableAtZero (F : ℝ → ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ Memℒp F 2 (gammaShapeThreeProbability.restrict (Ioo 0 r))

def GammaShapeThreeSquareIntegrableAtInfinity (F : ℝ → ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ Memℒp F 2 (gammaShapeThreeProbability.restrict (Ioi r))

/-- The single-parameter Weyl characterization used by the existing Gamma-two
development and by the paper's zero-energy proof. -/
def GammaShapeThreeWeylLimitPoint (endpointL2 : (ℝ → ℂ) → Prop) : Prop :=
  ¬∀ F, GammaShapeThreeZeroEnergySolution F → endpointL2 F

theorem gamma_shape_three_second_zero_is_solution :
    GammaShapeThreeZeroEnergySolution gammaShapeThreeSecondZeroSolution := by
  refine ⟨gamma_shape_three_second_zero_locally_ac,
    gamma_shape_three_second_zero_flux_locally_ac,?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact gamma_shape_three_second_zero_divergence ht

theorem gamma_shape_three_constant_zero_solution (c : ℂ) :
    GammaShapeThreeZeroEnergySolution (fun _ => c) := by
  have hd : deriv (fun _ : ℝ => c) = fun _ => 0 := funext fun t => deriv_const t c
  refine ⟨smooth_positive_locally_ac contDiff_const,?_,?_⟩
  · simpa only [hd,mul_zero] using
      (smooth_positive_locally_ac (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0:ℂ))))
  · filter_upwards with t
    simp only [gammaShapeThreeDivergenceExpression,hd,mul_zero,deriv_const]

theorem gamma_shape_three_constant_square_integrable_at_both_endpoints (c : ℂ) :
    GammaShapeThreeSquareIntegrableAtZero (fun _ => c) ∧
      GammaShapeThreeSquareIntegrableAtInfinity (fun _ => c) :=
  ⟨⟨1,by norm_num,memℒp_const c⟩,⟨1,by norm_num,memℒp_const c⟩⟩

theorem gamma_shape_three_zero_fundamental_independent (a b : ℂ)
    (he : EqOn (fun t => a+b*gammaShapeThreeSecondZeroSolution t) (fun _ => 0) (Ioi 0)) :
    a=0 ∧ b=0 := by
  have hevent : (fun t => a+b*gammaShapeThreeSecondZeroSolution t)
      =ᶠ[𝓝 (1:ℝ)] (fun _ => 0) := by
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0:ℝ)<1)] with t ht
    exact he ht
  have hd := ((gamma_shape_three_second_zero_hasDerivAt
    (by norm_num : (0:ℝ)<1)).const_mul b).const_add a
  have hb : b=0 := by
    have hz := hevent.deriv_eq
    rw [hd.deriv,deriv_const] at hz
    exact (mul_eq_zero.mp hz).resolve_right
      (inv_ne_zero (gamma_shape_three_flux_ne_zero (by norm_num)))
  refine ⟨?_,hb⟩
  simpa only [hb,zero_mul,add_zero] using he (show (1:ℝ) ∈ Ioi 0 by norm_num)

private theorem gamma_shape_three_zero_solution_l2_forces_constant (F : ℝ → ℂ)
    (hF : GammaShapeThreeZeroEnergySolution F) {S : Set ℝ} (hS : MeasurableSet S)
    (hp : S ⊆ Ioi 0)
    (hU : ¬Memℒp gammaShapeThreeSecondZeroSolution 2 (gammaShapeThreeProbability.restrict S))
    (hi : Memℒp F 2 (gammaShapeThreeProbability.restrict S)) :
    ∃ a : ℂ, EqOn F (fun _ => a) (Ioi 0) := by
  obtain ⟨a,b,he⟩ := gamma_shape_three_zero_solution_fundamental_system
    F hF.1 hF.2.1 hF.2.2
  have hb : b=0 := by
    by_contra hb
    apply hU
    have hm := (hi.sub (memℒp_const a)).const_mul b⁻¹
    apply hm.ae_eq
    filter_upwards [ae_restrict_mem hS] with t ht
    change b⁻¹*(F t-a)=gammaShapeThreeSecondZeroSolution t
    rw [he (hp ht)]
    field_simp
  exact ⟨a,fun t ht => by simpa only [hb,zero_mul,add_zero] using he ht⟩

theorem gamma_shape_three_zero_solution_l2_at_zero_iff_constant (F : ℝ → ℂ)
    (hF : GammaShapeThreeZeroEnergySolution F) :
    GammaShapeThreeSquareIntegrableAtZero F ↔
      ∃ a : ℂ, EqOn F (fun _ => a) (Ioi 0) := by
  constructor
  · rintro ⟨r,hr,hi⟩
    exact gamma_shape_three_zero_solution_l2_forces_constant F hF measurableSet_Ioo
      Ioo_subset_Ioi_self (gamma_shape_three_second_zero_not_l2_at_zero r hr) hi
  · rintro ⟨a,ha⟩
    refine ⟨1,by norm_num,(memℒp_const a).ae_eq ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (ha ht.1).symm

theorem gamma_shape_three_zero_solution_l2_at_infinity_iff_constant (F : ℝ → ℂ)
    (hF : GammaShapeThreeZeroEnergySolution F) :
    GammaShapeThreeSquareIntegrableAtInfinity F ↔
      ∃ a : ℂ, EqOn F (fun _ => a) (Ioi 0) := by
  constructor
  · rintro ⟨r,hr,hi⟩
    exact gamma_shape_three_zero_solution_l2_forces_constant F hF measurableSet_Ioi
      (fun _ ht => hr.trans ht) (gamma_shape_three_second_zero_not_l2_at_infinity r hr) hi
  · rintro ⟨a,ha⟩
    refine ⟨1,by norm_num,(memℒp_const a).ae_eq ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (ha (lt_trans zero_lt_one ht)).symm

/-- Both singular endpoints are limit point, and the constants are exactly the
locally square-integrable zero-energy direction at each endpoint. -/
theorem gamma_shape_three_both_endpoints_limit_point :
    GammaShapeThreeWeylLimitPoint GammaShapeThreeSquareIntegrableAtZero ∧
      GammaShapeThreeWeylLimitPoint GammaShapeThreeSquareIntegrableAtInfinity := by
  constructor
  · intro h
    obtain ⟨r,hr,hi⟩ := h gammaShapeThreeSecondZeroSolution gamma_shape_three_second_zero_is_solution
    exact gamma_shape_three_second_zero_not_l2_at_zero r hr hi
  · intro h
    obtain ⟨r,hr,hi⟩ := h gammaShapeThreeSecondZeroSolution gamma_shape_three_second_zero_is_solution
    exact gamma_shape_three_second_zero_not_l2_at_infinity r hr hi

end
end Sigma
