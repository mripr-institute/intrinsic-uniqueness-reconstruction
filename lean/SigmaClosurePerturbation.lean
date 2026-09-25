import SigmaCore
import SigmaZeroAnalytic
import Mathlib.Analysis.Convex.Deriv

/-! The analytic perturbations used in the intrinsic deletion test of Theorem 9.4.
The mass-preserving parameter selection is a separate remaining obligation.
-/

namespace Sigma.Closure
noncomputable section
open Filter Set
open scoped Topology

def perturbation (b t : ℝ) : ℝ := (t - 1) ^ 4 * Real.exp (-b * t)

def perturbationSlope (b t : ℝ) : ℝ :=
  (4 * (t - 1) ^ 3 - b * (t - 1) ^ 4) * Real.exp (-b * t)

def perturbationCurvature (b t : ℝ) : ℝ :=
  (12 * (t - 1) ^ 2 - 8 * b * (t - 1) ^ 3 + b ^ 2 * (t - 1) ^ 4) *
    Real.exp (-b * t)

theorem perturbation_analytic (b t : ℝ) : AnalyticAt ℝ (perturbation b) t := by
  exact (((analyticAt_id.sub analyticAt_const).pow 4).mul
    ((analyticAt_const.mul analyticAt_id).rexp))

theorem perturbation_hasDerivAt (b t : ℝ) :
    HasDerivAt (perturbation b) (perturbationSlope b t) t := by
  have h := (((hasDerivAt_id t).sub_const 1).pow 4).mul
    (((hasDerivAt_id t).const_mul (-b)).exp)
  convert h using 1
  dsimp [perturbation, perturbationSlope]
  ring

theorem perturbationSlope_hasDerivAt (b t : ℝ) :
    HasDerivAt (perturbationSlope b) (perturbationCurvature b t) t := by
  have h := ((((hasDerivAt_id t).sub_const 1).pow 3).const_mul 4 |>.sub
    ((((hasDerivAt_id t).sub_const 1).pow 4).const_mul b)).mul
    (((hasDerivAt_id t).const_mul (-b)).exp)
  convert h using 1
  dsimp [perturbationSlope, perturbationCurvature]
  ring

theorem perturbation_second_deriv (b t : ℝ) :
    deriv (deriv (perturbation b)) t = perturbationCurvature b t := by
  have he : deriv (perturbation b) = perturbationSlope b := by
    funext x
    exact (perturbation_hasDerivAt b x).deriv
  rw [he]
  exact (perturbationSlope_hasDerivAt b t).deriv

theorem perturbation_anchors (b : ℝ) :
    perturbation b 1 = 0 ∧ deriv (perturbation b) 1 = 0 ∧
      deriv (deriv (perturbation b)) 1 = 0 := by
  rw [(perturbation_hasDerivAt b 1).deriv, perturbation_second_deriv]
  simp [perturbation, perturbationSlope, perturbationCurvature]

/-- The two perturbations in the paper are linearly independent already on the positive ray. -/
theorem perturbations_independent (ε δ : ℝ)
    (h : ∀ t > 0, ε * perturbation 1 t + δ * perturbation 2 t = 0) :
    ε = 0 ∧ δ = 0 := by
  have evaluate (t : ℝ) (ht : 0 < t) (hne : t ≠ 1) :
      ε * Real.exp t + δ = 0 := by
    have he := h t ht
    have hexp : Real.exp (-t) = Real.exp t * Real.exp (-2 * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hprod : (t - 1) ^ 4 * Real.exp (-2 * t) *
        (ε * Real.exp t + δ) = 0 := by
      dsimp [perturbation] at he
      simp only [one_mul, neg_mul, neg_one_mul] at he
      rw [← neg_mul 2 t] at he
      rw [hexp] at he
      linear_combination he
    exact (mul_eq_zero.mp hprod).resolve_left
      (mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hne)) (Real.exp_ne_zero _))
  have h2 := evaluate 2 (by norm_num) (by norm_num)
  have h3 := evaluate 3 (by norm_num) (by norm_num)
  have hne : Real.exp (2 : ℝ) ≠ Real.exp 3 := by
    exact ne_of_lt (Real.exp_lt_exp.mpr (by norm_num))
  have hz : ε * (Real.exp 2 - Real.exp 3) = 0 := by nlinarith
  have hε : ε = 0 := (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hne)
  exact ⟨hε, by simpa [hε] using h2⟩

def perturbedIntrinsic (ε δ t : ℝ) : ℝ :=
  I t + ε * perturbation 1 t + δ * perturbation 2 t

theorem perturbed_intrinsic_analytic (ε δ : ℝ) {t : ℝ} (ht : 0 < t) :
    AnalyticAt ℝ (perturbedIntrinsic ε δ) t := by
  have hI : AnalyticAt ℝ I t :=
    (analyticAt_id.sub analyticAt_const).sub (positive_real_log_analytic ht)
  exact (hI.add (analyticAt_const.mul (perturbation_analytic 1 t))).add
    (analyticAt_const.mul (perturbation_analytic 2 t))

theorem perturbed_intrinsic_hasDerivAt (ε δ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (perturbedIntrinsic ε δ)
      (1 - 1 / t + ε * perturbationSlope 1 t + δ * perturbationSlope 2 t) t :=
  ((SigmaBase.potential_hasDerivAt ht).add
    ((perturbation_hasDerivAt 1 t).const_mul ε)).add
    ((perturbation_hasDerivAt 2 t).const_mul δ)

theorem perturbed_intrinsic_second_deriv (ε δ : ℝ) {t : ℝ} (ht : 0 < t) :
    deriv (deriv (perturbedIntrinsic ε δ)) t =
      1 / t ^ 2 + ε * perturbationCurvature 1 t + δ * perturbationCurvature 2 t := by
  have hI : HasDerivAt (fun x : ℝ => 1 - 1 / x) (1 / t ^ 2) t := by
    convert (reciprocal_hasDerivAt ht).neg using 1 <;> simp
  have hd := (hI.add ((perturbationSlope_hasDerivAt 1 t).const_mul ε)).add
    ((perturbationSlope_hasDerivAt 2 t).const_mul δ)
  apply HasDerivAt.deriv
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
  exact (perturbed_intrinsic_hasDerivAt ε δ hx).deriv

theorem perturbed_intrinsic_anchors (ε δ : ℝ) :
    perturbedIntrinsic ε δ 1 = 0 ∧ deriv (perturbedIntrinsic ε δ) 1 = 0 ∧
      deriv (deriv (perturbedIntrinsic ε δ)) 1 = 1 := by
  rw [(perturbed_intrinsic_hasDerivAt ε δ (by norm_num : (0 : ℝ) < 1)).deriv,
    perturbed_intrinsic_second_deriv ε δ (by norm_num : (0 : ℝ) < 1)]
  simp [perturbedIntrinsic, I, SigmaBase.potential, perturbation,
    perturbationSlope, perturbationCurvature]

theorem perturbed_intrinsic_identical_iff (ε δ : ℝ) :
    (∀ t > 0, perturbedIntrinsic ε δ t = I t) ↔ ε = 0 ∧ δ = 0 := by
  constructor
  · intro h
    apply perturbations_independent
    intro t ht
    have he := h t ht
    dsimp [perturbedIntrinsic] at he
    linarith
  · rintro ⟨rfl, rfl⟩ t ht
    simp [perturbedIntrinsic]

/-- Exponential decay controls every polynomial term of the perturbation. -/
theorem monomial_exp_decay (b : ℝ) (hb : 0 < b) (n : ℕ) :
    Tendsto (fun t : ℝ => t ^ n * Real.exp (-b * t)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    (tendsto_id.const_mul_atTop hb)
  have hd := h.div_const (b ^ n)
  simpa only [zero_div] using hd.congr' (Eventually.of_forall (fun t => by
    dsimp
    rw [mul_pow]
    field_simp
    ring))

/-- Each perturbation vanishes at the upper endpoint of the positive ray. -/
theorem perturbation_tendsto_atTop (b : ℝ) (hb : 0 < b) :
    Tendsto (perturbation b) atTop (𝓝 0) := by
  have h := (((((monomial_exp_decay b hb 4).add
    ((monomial_exp_decay b hb 3).const_mul (-4))).add
    ((monomial_exp_decay b hb 2).const_mul 6)).add
    ((monomial_exp_decay b hb 1).const_mul (-4))).add
    (monomial_exp_decay b hb 0))
  convert h using 1
  · funext t
    dsimp [perturbation]
    ring
  · ring

/-- At the lower endpoint each perturbation has the finite limit one. -/
theorem perturbation_tendsto_zero_right (b : ℝ) :
    Tendsto (perturbation b) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hc : ContinuousAt (perturbation b) 0 := by
    unfold perturbation
    fun_prop
  have h := hc.tendsto.mono_left
    (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  convert h using 1
  norm_num [perturbation]

/-- The upper-endpoint perturbation of the intrinsic potential vanishes. -/
theorem perturbed_intrinsic_difference_tendsto_atTop (ε δ : ℝ) :
    Tendsto (fun t => perturbedIntrinsic ε δ t - I t) atTop (𝓝 0) := by
  have h := ((perturbation_tendsto_atTop 1 (by norm_num)).const_mul ε).add
    ((perturbation_tendsto_atTop 2 (by norm_num)).const_mul δ)
  convert h using 1
  · funext t
    dsimp [perturbedIntrinsic]
    ring
  · ring

/-- The lower-endpoint perturbation has the finite offset `ε + δ`. -/
theorem perturbed_intrinsic_difference_tendsto_zero_right (ε δ : ℝ) :
    Tendsto (fun t => perturbedIntrinsic ε δ t - I t)
      (𝓝[>] (0 : ℝ)) (𝓝 (ε + δ)) := by
  have h := ((perturbation_tendsto_zero_right 1).const_mul ε).add
    ((perturbation_tendsto_zero_right 2).const_mul δ)
  convert h using 1
  · funext t
    dsimp [perturbedIntrinsic]
    ring
  · ring

/-- The unperturbed calibrated intrinsic potential diverges at zero. -/
private theorem intrinsic_tendsto_zero_right :
    Tendsto I (𝓝[>] (0 : ℝ)) atTop := by
  have hc : ContinuousAt (fun t : ℝ => t - 1) 0 := by fun_prop
  have hfin : Tendsto (fun t : ℝ => t - 1) (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
    simpa using hc.tendsto.mono_left
      (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hlog : Tendsto (fun t : ℝ => -Real.log t) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsWithin_zero_right
  exact hfin.add_atTop hlog

/-- The unperturbed calibrated intrinsic potential diverges at infinity. -/
private theorem intrinsic_tendsto_atTop : Tendsto I atTop atTop := by
  have hratio : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hfac : Tendsto (fun t : ℝ => 1 - Real.log t / t) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hratio
  have hprod : Tendsto (fun t : ℝ => t * (1 - Real.log t / t)) atTop atTop :=
    tendsto_id.atTop_mul (by norm_num : (0 : ℝ) < 1) hfac
  have hshift := tendsto_atTop_add_const_right atTop (-1) hprod
  apply hshift.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  dsimp [I, SigmaBase.potential]
  field_simp [ht.ne']
  ring

/-- Every two-parameter perturbation retains divergence at both endpoints. -/
theorem perturbed_intrinsic_endpoint_divergence (ε δ : ℝ) :
    Tendsto (perturbedIntrinsic ε δ) (𝓝[>] (0 : ℝ)) atTop ∧
      Tendsto (perturbedIntrinsic ε δ) atTop atTop := by
  constructor
  · have h := (perturbed_intrinsic_difference_tendsto_zero_right ε δ).add_atTop
      intrinsic_tendsto_zero_right
    convert h using 1
    funext t
    ring
  · have h := (perturbed_intrinsic_difference_tendsto_atTop ε δ).add_atTop
      intrinsic_tendsto_atTop
    convert h using 1
    funext t
    ring

theorem perturbation_weighted_curvature_decay (b : ℝ) (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ 2 * perturbationCurvature b t) atTop (𝓝 0) := by
  have h := (((((monomial_exp_decay b hb 6).const_mul (b ^ 2)).add
    ((monomial_exp_decay b hb 5).const_mul (-4*b^2-8*b))).add
    ((monomial_exp_decay b hb 4).const_mul (6*b^2+24*b+12))).add
    ((monomial_exp_decay b hb 3).const_mul (-4*b^2-24*b-24))).add
    ((monomial_exp_decay b hb 2).const_mul (b^2+8*b+12))
  convert h using 1
  · funext t
    dsimp [perturbationCurvature]
    ring
  · ring

/-- A continuous decaying real function is bounded on the entire closed positive ray. -/
theorem positive_ray_bound_of_decay (f : ℝ → ℝ) (hc : Continuous f)
    (hl : Tendsto f atTop (𝓝 0)) : ∃ C > 0, ∀ t ≥ 0, |f t| ≤ C := by
  have he : ∀ᶠ t : ℝ in atTop, |f t| < 1 := by
    exact hl.abs.eventually (gt_mem_nhds (by norm_num : |(0 : ℝ)| < 1))
  obtain ⟨R, hR⟩ := eventually_atTop.mp he
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) (max R 0))).bddAbove_image
    hc.abs.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro t ht
  by_cases htr : t ≤ max R 0
  · exact (hC (mem_image_of_mem _ ⟨ht, htr⟩)).trans (le_max_left _ _)
  · exact (hR t (le_trans (le_max_left _ _) (le_of_not_ge htr))).le.trans
      (le_max_right _ _)

theorem perturbation_weighted_curvature_bound (b : ℝ) (hb : 0 < b) :
    ∃ C > 0, ∀ t ≥ 0, |t ^ 2 * perturbationCurvature b t| ≤ C := by
  apply positive_ray_bound_of_decay
  · unfold perturbationCurvature
    fun_prop
  · exact perturbation_weighted_curvature_decay b hb

/-- A uniform neighborhood preserves strict convexity, in addition to all three anchors.
Mass normalization requires a separate proof. -/
theorem perturbed_intrinsic_strictConvex_near_zero :
    ∃ η > 0, ∀ ε δ : ℝ, |ε| < η → |δ| < η →
      StrictConvexOn ℝ (Ioi 0) (perturbedIntrinsic ε δ) := by
  obtain ⟨Cg, hCg, hg⟩ := perturbation_weighted_curvature_bound 1 (by norm_num)
  obtain ⟨Ch, hCh, hh⟩ := perturbation_weighted_curvature_bound 2 (by norm_num)
  let η := 1 / (2 * (Cg + Ch))
  have hsum : 0 < Cg + Ch := add_pos hCg hCh
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η, hη, ?_⟩
  intro ε δ hε hδ
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi (0 : ℝ))
    (fun t ht => (perturbed_intrinsic_analytic ε δ ht).continuousAt.continuousWithinAt)
  intro t ht
  change 0 < deriv (deriv (perturbedIntrinsic ε δ)) t
  rw [perturbed_intrinsic_second_deriv ε δ ht]
  have hg' := hg t ht.le
  have hh' := hh t ht.le
  have he : |ε * (t ^ 2 * perturbationCurvature 1 t)| < η * Cg := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hg' (abs_nonneg ε)).trans_lt
      (mul_lt_mul_of_pos_right hε hCg)
  have hd : |δ * (t ^ 2 * perturbationCurvature 2 t)| < η * Ch := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hh' (abs_nonneg δ)).trans_lt
      (mul_lt_mul_of_pos_right hδ hCh)
  have hs : η * Cg + η * Ch = 1 / 2 := by
    dsimp [η]
    field_simp
    ring
  have hlowg := neg_abs_le (ε * (t ^ 2 * perturbationCurvature 1 t))
  have hlowh := neg_abs_le (δ * (t ^ 2 * perturbationCurvature 2 t))
  have hpos : 0 < 1 + ε * (t ^ 2 * perturbationCurvature 1 t) +
      δ * (t ^ 2 * perturbationCurvature 2 t) := by linarith
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have hid : t ^ 2 * (1 / t ^ 2 + ε * perturbationCurvature 1 t +
      δ * perturbationCurvature 2 t) =
      1 + ε * (t ^ 2 * perturbationCurvature 1 t) +
      δ * (t ^ 2 * perturbationCurvature 2 t) := by
    field_simp
    ring
  exact (mul_pos_iff.mp (hid.symm ▸ hpos)).resolve_right (by
    intro h
    exact (not_lt_of_gt ht2) h.1) |>.2

end
end Sigma.Closure
