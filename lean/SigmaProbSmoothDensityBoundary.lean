import SigmaSmoothGerm
import SigmaRealTreesInverse
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

def continuationBump : ContDiffBump (5/2 : ℝ) :=
  ⟨1/8, 1/4, by norm_num, by norm_num⟩

def continuationPerturbation : ℝ → ℝ := deriv continuationBump

theorem continuation_bump_support : tsupport continuationBump ⊆ Ioo (2 : ℝ) 3 := by
  rw [continuationBump.tsupport_eq]
  intro t ht
  simp only [Metric.mem_closedBall, Real.dist_eq, continuationBump] at ht
  have hh := abs_le.mp ht
  constructor <;> linarith

theorem continuation_perturbation_smooth : ContDiff ℝ ∞ continuationPerturbation :=
  (contDiff_infty_iff_deriv.mp continuationBump.contDiff).2

theorem continuation_perturbation_compact : HasCompactSupport continuationPerturbation :=
  continuationBump.hasCompactSupport.deriv

theorem continuation_perturbation_support :
    tsupport continuationPerturbation ⊆ Ioo (2 : ℝ) 3 :=
  (closure_minimal support_deriv_subset (isClosed_tsupport _)).trans continuation_bump_support

theorem continuation_perturbation_zero {t : ℝ} (ht : t ∉ Ioo (2 : ℝ) 3) :
    continuationPerturbation t = 0 :=
  image_eq_zero_of_nmem_tsupport (fun hh => ht (continuation_perturbation_support hh))

theorem continuation_perturbation_deriv_zero {t : ℝ} (ht : t ∉ Ioo (2 : ℝ) 3) :
    deriv continuationPerturbation t = 0 :=
  Function.nmem_support.mp (fun hh => ht (continuation_perturbation_support (support_deriv_subset hh)))

theorem continuation_perturbation_mass_zero :
    (∫ t : ℝ in Ioi 0, continuationPerturbation t) = 0 := by
  rw [continuationPerturbation,
    HasCompactSupport.integral_Ioi_deriv_eq (show ContDiff ℝ 1 continuationBump from continuationBump.contDiff)
      continuationBump.hasCompactSupport]
  have hz : continuationBump (0 : ℝ) = 0 :=
    image_eq_zero_of_nmem_tsupport (fun hh => by
      have := continuation_bump_support hh
      norm_num at this)
  rw [hz, neg_zero]

theorem continuation_perturbation_nonzero : ∃ t ∈ Ioo (2 : ℝ) 3,
    continuationPerturbation t ≠ 0 := by
  have hn : ∃ t : ℝ, continuationPerturbation t ≠ 0 := by
    by_contra hh
    push_neg at hh
    have he := is_const_of_deriv_eq_zero
      ((show ContDiff ℝ 1 continuationBump from continuationBump.contDiff).differentiable le_rfl) hh (5/2 : ℝ) 0
    have hc : continuationBump (5/2 : ℝ) = 1 :=
      continuationBump.one_of_mem_closedBall (by simp [continuationBump])
    have hz : continuationBump (0 : ℝ) = 0 :=
      image_eq_zero_of_nmem_tsupport (fun h => by
        have := continuation_bump_support h
        norm_num at this)
    rw [hc, hz] at he
    norm_num at he
  obtain ⟨t, ht⟩ := hn
  exact ⟨t, continuation_perturbation_support (subset_closure ht), ht⟩

theorem continuation_perturbation_uniform_bounds : ∃ K : ℝ, 0 < K ∧
    (∀ t, |continuationPerturbation t| ≤ K) ∧
    (∀ t, |deriv continuationPerturbation t| ≤ K) := by
  have hc := continuation_perturbation_smooth
  obtain ⟨B, hB⟩ := (continuation_perturbation_compact.abs.isCompact_range hc.continuous.abs).bddAbove
  obtain ⟨D, hD⟩ := (continuation_perturbation_compact.deriv.abs.isCompact_range
    (hc.continuous_deriv (by simp)).abs).bddAbove
  refine ⟨|B|+|D|+1, by positivity, ?_, ?_⟩
  · intro t
    have ht := hB (mem_range_self t)
    change |continuationPerturbation t| ≤ B at ht
    linarith [le_abs_self B, abs_nonneg D]
  · intro t
    have ht := hD (mem_range_self t)
    change |deriv continuationPerturbation t| ≤ D at ht
    linarith [le_abs_self D, abs_nonneg B]

def continuationDensity (ε t : ℝ) : ℝ :=
  SigmaPresentations.density t + ε*continuationPerturbation t

theorem continuation_density_smooth (ε : ℝ) : ContDiff ℝ ∞ (continuationDensity ε) :=
  (contDiff_id.mul contDiff_id.neg.exp).add
    (contDiff_const.mul continuation_perturbation_smooth)

theorem continuation_density_derivative (ε t : ℝ) :
    HasDerivAt (continuationDensity ε)
      ((1-t)*Real.exp (-t)+ε*deriv continuationPerturbation t) t := by
  have hp : HasDerivAt SigmaPresentations.density ((1-t)*Real.exp (-t)) t := by
    convert (hasDerivAt_id t).mul ((hasDerivAt_id t).neg.exp) using 1
    simp only [SigmaPresentations.density, id_eq]
    ring
  exact hp.add (((continuation_perturbation_smooth.differentiable (by simp)) t).hasDerivAt.const_mul ε)

theorem continuation_density_outside (ε : ℝ) {t : ℝ} (ht : t ∉ Ioo (2 : ℝ) 3) :
    continuationDensity ε t = SigmaPresentations.density t := by
  simp only [continuationDensity, continuation_perturbation_zero ht, mul_zero, add_zero]

theorem continuation_density_normalized (ε : ℝ) :
    IntegrableOn (continuationDensity ε) (Ioi 0) volume ∧
      (∫ t : ℝ in Ioi 0, continuationDensity ε t) = 1 := by
  have hi : Integrable continuationPerturbation volume :=
    continuation_perturbation_smooth.continuous.integrable_of_hasCompactSupport
    continuation_perturbation_compact
  refine ⟨intrinsic_density_integrable.add (hi.integrableOn.const_mul ε), ?_⟩
  dsimp only [continuationDensity]
  rw [integral_add intrinsic_density_integrable
    (hi.integrableOn.const_mul ε), integral_mul_left, continuation_perturbation_mass_zero,
    intrinsic_density_integral_one, mul_zero, add_zero]

theorem continuation_density_positive_and_shape : ∃ ε : ℝ, 0 < ε ∧
    (∀ t > 0, 0 < continuationDensity ε t) ∧
    StrictMonoOn (continuationDensity ε) (Icc 0 1) ∧
    StrictAntiOn (continuationDensity ε) (Ici 1) := by
  obtain ⟨K, hK, hb, hdb⟩ := continuation_perturbation_uniform_bounds
  let ε := Real.exp (-3)/(2*K)
  have he : 0 < ε := by dsimp [ε]; positivity
  have heK : ε*K = Real.exp (-3)/2 := by dsimp [ε]; field_simp; ring
  have hsmall (t : ℝ) : |ε*continuationPerturbation t| ≤ Real.exp (-3)/2 := by
    rw [abs_mul, abs_of_pos he, ← heK]
    exact mul_le_mul_of_nonneg_left (hb t) he.le
  have hdsmall (t : ℝ) : |ε*deriv continuationPerturbation t| ≤ Real.exp (-3)/2 := by
    rw [abs_mul, abs_of_pos he, ← heK]
    exact mul_le_mul_of_nonneg_left (hdb t) he.le
  have hdneg (t : ℝ) (ht : 1 < t) : deriv (continuationDensity ε) t < 0 := by
    rw [(continuation_density_derivative ε t).deriv]
    by_cases htin : t ∈ Ioo (2 : ℝ) 3
    · have hexp : Real.exp (-3) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith [htin.2])
      have hp : (1-t)*Real.exp (-t) ≤ -Real.exp (-3) := by
        have hh := mul_le_mul_of_nonneg_right (show 1-t ≤ -1 by linarith [htin.1])
          (Real.exp_pos (-t)).le
        nlinarith
      have hh := (le_abs_self (ε*deriv continuationPerturbation t)).trans (hdsmall t)
      linarith [Real.exp_pos (-3)]
    · rw [continuation_perturbation_deriv_zero htin, mul_zero, add_zero]
      exact mul_neg_of_neg_of_pos (sub_neg.mpr ht) (Real.exp_pos _)
  refine ⟨ε, he, ?_, ?_, ?_⟩
  · intro t ht
    by_cases htin : t ∈ Ioo (2 : ℝ) 3
    · have hexp : Real.exp (-3) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith [htin.2])
      have hp : 2*Real.exp (-3) ≤ SigmaPresentations.density t := by
        exact mul_le_mul (by linarith [htin.1]) hexp (Real.exp_pos _).le (by linarith [htin.1])
      have hh := neg_abs_le (ε*continuationPerturbation t)
      have hb' := hsmall t
      dsimp [continuationDensity]
      linarith [Real.exp_pos (-3)]
    · rw [continuation_density_outside ε htin]
      exact SigmaPresentations.density_pos ht
  · apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
      (continuation_density_smooth ε).continuous.continuousOn
    intro t ht
    rw [interior_Icc] at ht
    rw [(continuation_density_derivative ε t).deriv,
      continuation_perturbation_deriv_zero (by intro h; linarith [h.1, ht.2]),
      mul_zero, add_zero]
    exact mul_pos (sub_pos.mpr ht.2) (Real.exp_pos _)
  · apply strictAntiOn_of_deriv_neg (convex_Ici 1)
      (continuation_density_smooth ε).continuous.continuousOn
    intro t ht
    rw [interior_Ici] at ht
    exact hdneg t ht

theorem continuation_density_same_germ (ε : ℝ) :
    continuationDensity ε =ᶠ[𝓝 (0 : ℝ)] SigmaPresentations.density := by
  filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 2 by norm_num)] with t ht
  exact continuation_density_outside ε (by intro h; exact (not_lt_of_ge h.1.le) ht)

theorem continuation_density_inverse_germ (ε : ℝ) :
    (fun z => continuationDensity ε (rootedAnalyticSeries.sum z)) =ᶠ[𝓝 (0 : ℝ)] id ∧
    (fun t => rootedAnalyticSeries.sum (continuationDensity ε t)) =ᶠ[𝓝 (0 : ℝ)] id := by
  have hr0 : rootedAnalyticSeries.sum 0 = 0 := by
    rw [rooted_generating_scaled_borel, zero_mul, borel_generating_zero]
  have hr : Tendsto rootedAnalyticSeries.sum (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hc := (rooted_generating_analytic 0 (by simpa using Real.exp_pos (-1))).continuousAt
    change Tendsto rootedAnalyticSeries.sum (𝓝 (0 : ℝ)) (𝓝 (rootedAnalyticSeries.sum 0)) at hc
    rwa [hr0] at hc
  constructor
  · filter_upwards [(continuation_density_same_germ ε).comp_tendsto hr,
      rooted_inverse_analytic_germs.1] with z hz hi
    exact hz.trans hi
  · filter_upwards [continuation_density_same_germ ε,
      rooted_inverse_analytic_germs.2] with t ht hi
    rw [ht]
    exact hi

theorem continuation_density_endpoints (ε : ℝ) :
    Tendsto (continuationDensity ε) (𝓝 (0 : ℝ)) (𝓝 0) ∧
    Tendsto (continuationDensity ε) atTop (𝓝 0) := by
  constructor
  · have hp : Tendsto SigmaPresentations.density (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa [SigmaPresentations.density] using
        (continuous_id.mul continuous_id.neg.rexp).tendsto (0 : ℝ)
    exact hp.congr' (continuation_density_same_germ ε).symm
  · have hp : Tendsto SigmaPresentations.density atTop (𝓝 0) := by
      simpa only [pow_one] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    apply hp.congr'
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with t ht
    exact (continuation_density_outside ε (by intro h; linarith [h.2])).symm

theorem continuation_density_distinct (ε : ℝ) (hε : ε ≠ 0) :
    ¬ continuationDensity ε =ᵐ[volume.restrict (Ioi (0 : ℝ))] SigmaPresentations.density := by
  intro he
  have hp : Continuous SigmaPresentations.density := continuous_id.mul continuous_id.neg.rexp
  have hh := Measure.eqOn_open_of_ae_eq he isOpen_Ioi
    (continuation_density_smooth ε).continuous.continuousOn hp.continuousOn
  obtain ⟨t, ht, hn⟩ := continuation_perturbation_nonzero
  have hv := hh (show t ∈ Ioi 0 by change 0 < t; linarith [ht.1])
  have hz : ε*continuationPerturbation t = 0 := by
    change SigmaPresentations.density t + ε*continuationPerturbation t = _ at hv
    linarith
  exact (mul_ne_zero hε hn) hz

/-- A literal smooth normalized positive density with the complete canonical
inverse germ and shape, but a different probability density. -/
theorem smooth_inverse_germ_density_boundary :
    ∃ q : ℝ → ℝ, ContDiff ℝ ∞ q ∧
      (∀ t > 0, 0 < q t) ∧ IntegrableOn q (Ioi 0) volume ∧
      (∫ t : ℝ in Ioi 0, q t) = 1 ∧
      (∀ t, t ∉ Ioo (2 : ℝ) 3 → q t = SigmaPresentations.density t) ∧
      HasCompactSupport (fun t => q t-SigmaPresentations.density t) ∧
      StrictMonoOn q (Icc 0 1) ∧ StrictAntiOn q (Ici 1) ∧
      q 1 = Real.exp (-1) ∧
      (∀ t > 0, t ≠ 1 → q t < q 1) ∧
      Tendsto q (𝓝 (0 : ℝ)) (𝓝 0) ∧ Tendsto q atTop (𝓝 0) ∧
      (fun z => q (rootedAnalyticSeries.sum z)) =ᶠ[𝓝 (0 : ℝ)] id ∧
      (fun t => rootedAnalyticSeries.sum (q t)) =ᶠ[𝓝 (0 : ℝ)] id ∧
      ¬ q =ᵐ[volume.restrict (Ioi (0 : ℝ))] SigmaPresentations.density := by
  obtain ⟨ε, he, hpos, hmono, hanti⟩ := continuation_density_positive_and_shape
  obtain ⟨hi, hm⟩ := continuation_density_normalized ε
  obtain ⟨h0, htop⟩ := continuation_density_endpoints ε
  obtain ⟨hgi, hig⟩ := continuation_density_inverse_germ ε
  refine ⟨continuationDensity ε, continuation_density_smooth ε, hpos, hi, hm,
    fun _ ht => continuation_density_outside ε ht, ?_, hmono, hanti, ?_, ?_,
    h0, htop, hgi, hig, continuation_density_distinct ε he.ne'⟩
  · convert (show HasCompactSupport (fun t => ε*continuationPerturbation t) from
      continuation_perturbation_compact.mul_left) using 1
    funext t
    simp only [continuationDensity, add_sub_cancel_left]
  · rw [continuation_density_outside ε (by norm_num)]
    simp [SigmaPresentations.density]
  · intro t ht hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hmono ⟨ht.le, hlt.le⟩ (by norm_num) hlt
    · exact hanti (by norm_num) hgt.le hgt

end
end Sigma
