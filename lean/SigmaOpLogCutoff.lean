import SigmaSteinCutoff
import Mathlib.Analysis.SpecialFunctions.Integrals

namespace Sigma
noncomputable section
open Set Filter MeasureTheory Real
open scoped Topology ContDiff

/-- A logarithmically stretched smooth cutoff at the critical lower endpoint. -/
def operatorLogCutoff (R t : ℝ) : ℝ :=
  if 0 < t then smoothTransition ((Real.log t + 2*R)/R) else 0

theorem operator_log_cutoff_zero {R t : ℝ} (hR : 0 < R)
    (ht : t ≤ Real.exp (-2*R)) : operatorLogCutoff R t = 0 := by
  unfold operatorLogCutoff
  split_ifs with hp
  · apply smoothTransition.zero_of_nonpos
    apply div_nonpos_of_nonpos_of_nonneg _ hR.le
    have hl : Real.log t ≤ -2*R := (Real.log_le_iff_le_exp hp).mpr ht
    linarith
  · rfl

theorem operator_log_cutoff_one {R t : ℝ} (hR : 0 < R)
    (ht : Real.exp (-R) ≤ t) : operatorLogCutoff R t = 1 := by
  have hp : 0 < t := (Real.exp_pos _).trans_le ht
  rw [operatorLogCutoff, if_pos hp]
  apply smoothTransition.one_of_one_le
  apply (le_div_iff₀ hR).mpr
  have hl : -R ≤ Real.log t := (Real.le_log_iff_exp_le hp).mpr ht
  linarith

theorem operator_log_cutoff_bounds (R t : ℝ) :
    0 ≤ operatorLogCutoff R t ∧ operatorLogCutoff R t ≤ 1 := by
  unfold operatorLogCutoff
  split_ifs
  · exact ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  · norm_num

theorem operator_log_cutoff_contDiff {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (operatorLogCutoff R) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : 0 < t
  · have he : operatorLogCutoff R =ᶠ[𝓝 t]
        (fun u => smoothTransition ((Real.log u + 2*R)/R)) := by
      filter_upwards [eventually_gt_nhds ht] with u hu
      simp only [operatorLogCutoff, if_pos hu]
    apply ContDiffAt.congr_of_eventuallyEq _ he
    exact smoothTransition.contDiffAt.comp t
      (((Real.contDiffAt_log.mpr ht.ne').add contDiffAt_const).div_const R)
  · have hlt : t < Real.exp (-2*R) := lt_of_le_of_lt (le_of_not_gt ht) (Real.exp_pos _)
    have he : operatorLogCutoff R =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds hlt] with u hu
      exact operator_log_cutoff_zero hR hu.le
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem operator_log_cutoff_hasDerivAt {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    HasDerivAt (operatorLogCutoff R)
      (deriv smoothTransition ((Real.log t + 2*R)/R) / (R*t)) t := by
  have he : operatorLogCutoff R =ᶠ[𝓝 t]
      (fun u => smoothTransition ((Real.log u + 2*R)/R)) := by
    filter_upwards [eventually_gt_nhds ht] with u hu
    simp only [operatorLogCutoff, if_pos hu]
  have h := (smoothTransition.contDiff.differentiable (by simp : (1 : ℕ∞) ≤ ∞)).differentiableAt.hasDerivAt.comp t
    (((Real.hasDerivAt_log ht.ne').add_const (2*R)).div_const R)
  convert h.congr_of_eventuallyEq he using 1
  dsimp
  field_simp
  exact Or.inl (mul_comm _ _)

theorem operator_log_cutoff_deriv {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    deriv (operatorLogCutoff R) t =
      deriv smoothTransition ((Real.log t + 2*R)/R) / (R*t) :=
  (operator_log_cutoff_hasDerivAt hR ht).deriv

theorem smooth_transition_deriv_compact_support :
    HasCompactSupport (deriv smoothTransition) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  intro t ht
  by_contra hm
  have hz : deriv smoothTransition t = 0 := by
    rcases not_and_or.mp hm with hn | hn
    · have ht0 : t < 0 := lt_of_not_ge hn
      have he : smoothTransition =ᶠ[𝓝 t] (fun _ => 0) := by
        filter_upwards [eventually_lt_nhds ht0] with u hu
        exact smoothTransition.zero_of_nonpos hu.le
      exact he.deriv_eq.trans (deriv_const _ _)
    · have ht1 : 1 < t := lt_of_not_ge hn
      have he : smoothTransition =ᶠ[𝓝 t] (fun _ => 1) := by
        filter_upwards [eventually_gt_nhds ht1] with u hu
        exact smoothTransition.one_of_one_le hu.le
      exact he.deriv_eq.trans (deriv_const _ _)
  exact ht hz

theorem smooth_transition_derivatives_bounded : ∃ C > 0,
    (∀ t : ℝ, |deriv smoothTransition t| ≤ C) ∧
    (∀ t : ℝ, |deriv (deriv smoothTransition) t| ≤ C) := by
  have hd : ContDiff ℝ ∞ (deriv smoothTransition) :=
    (contDiff_infty_iff_deriv.mp smoothTransition.contDiff).2
  obtain ⟨B, hB⟩ :=
    (smooth_transition_deriv_compact_support.abs.isCompact_range hd.continuous.abs).bddAbove
  obtain ⟨D, hD⟩ :=
    (smooth_transition_deriv_compact_support.deriv.abs.isCompact_range
      (hd.continuous_deriv (by simp)).abs).bddAbove
  refine ⟨|B| + |D| + 1, by positivity, ?_, ?_⟩
  · intro t
    exact (hB (mem_range_self t)).trans (by linarith [le_abs_self B, abs_nonneg D])
  · intro t
    exact (hD (mem_range_self t)).trans (by linarith [le_abs_self D, abs_nonneg B])

theorem operator_log_cutoff_second_deriv {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    deriv (deriv (operatorLogCutoff R)) t =
      deriv (deriv smoothTransition) ((Real.log t + 2*R)/R) / (R^2*t^2) -
        deriv smoothTransition ((Real.log t + 2*R)/R) / (R*t^2) := by
  have hd : ContDiff ℝ ∞ (deriv smoothTransition) :=
    (contDiff_infty_iff_deriv.mp smoothTransition.contDiff).2
  have he : deriv (operatorLogCutoff R) =ᶠ[𝓝 t]
      (fun u => deriv smoothTransition ((Real.log u + 2*R)/R) / (R*u)) := by
    filter_upwards [eventually_gt_nhds ht] with u hu
    exact operator_log_cutoff_deriv hR hu
  have hn := (hd.differentiable (by simp)).differentiableAt.hasDerivAt.comp t
    (((Real.hasDerivAt_log ht.ne').add_const (2*R)).div_const R)
  have hb := (hasDerivAt_id t).const_mul R
  have h := (hn.div hb (mul_ne_zero hR.ne' ht.ne')).congr_of_eventuallyEq he
  rw [h.deriv]
  dsimp
  field_simp
  ring

theorem operator_log_cutoff_deriv_bound {R t C : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hC : ∀ u : ℝ, |deriv smoothTransition u| ≤ C) :
    |deriv (operatorLogCutoff R) t| ≤ C/(R*t) := by
  rw [operator_log_cutoff_deriv hR ht, abs_div, abs_of_pos (mul_pos hR ht)]
  exact div_le_div_of_nonneg_right (hC _) (mul_pos hR ht).le

theorem operator_log_cutoff_second_deriv_bound {R t C : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hC : ∀ u : ℝ, |deriv smoothTransition u| ≤ C)
    (hC₂ : ∀ u : ℝ, |deriv (deriv smoothTransition) u| ≤ C) :
    |deriv (deriv (operatorLogCutoff R)) t| ≤ C/(R^2*t^2) + C/(R*t^2) := by
  rw [operator_log_cutoff_second_deriv hR ht]
  apply (abs_sub _ _).trans
  rw [abs_div, abs_div, abs_of_pos (by positivity : 0 < R^2*t^2),
    abs_of_pos (by positivity : 0 < R*t^2)]
  exact add_le_add
    (div_le_div_of_nonneg_right (hC₂ _) (by positivity))
    (div_le_div_of_nonneg_right (hC _) (by positivity))

def operatorLogCutoffGraphError (R t : ℝ) : ℝ :=
  t * Real.exp (-t) *
    (t * deriv (deriv (operatorLogCutoff R)) t + (2-t)*deriv (operatorLogCutoff R) t)^2

theorem operator_log_cutoff_graph_error_continuous {R : ℝ} (hR : 0 < R) :
    Continuous (operatorLogCutoffGraphError R) := by
  have hd := (contDiff_infty_iff_deriv.mp (operator_log_cutoff_contDiff hR)).2
  unfold operatorLogCutoffGraphError
  exact (continuous_id.mul (continuous_id.neg.rexp)).mul
    (((continuous_id.mul (hd.continuous_deriv (by simp))).add
      ((continuous_const.sub continuous_id).mul hd.continuous)).pow 2)

theorem operator_log_cutoff_graph_error_support {R : ℝ} (hR : 0 < R) :
    Function.support (operatorLogCutoffGraphError R) ⊆
      Icc (Real.exp (-2*R)) (Real.exp (-R)) := by
  intro t ht
  by_contra hm
  have he : ∃ c : ℝ, operatorLogCutoff R =ᶠ[𝓝 t] (fun _ => c) := by
    rcases not_and_or.mp hm with hn | hn
    · refine ⟨0, ?_⟩
      filter_upwards [eventually_lt_nhds (lt_of_not_ge hn)] with u hu
      exact operator_log_cutoff_zero hR hu.le
    · refine ⟨1, ?_⟩
      filter_upwards [eventually_gt_nhds (lt_of_not_ge hn)] with u hu
      exact operator_log_cutoff_one hR hu.le
  obtain ⟨c, hc⟩ := he
  have hd : deriv (operatorLogCutoff R) t = 0 := hc.deriv_eq.trans (deriv_const _ _)
  have hdd : deriv (deriv (operatorLogCutoff R)) t = 0 := by
    rw [hc.deriv.deriv_eq]
    have he : deriv (fun _ : ℝ => c) = fun _ : ℝ => 0 := by funext u; exact deriv_const _ _
    rw [he, deriv_const]
  exact ht (by simp only [operatorLogCutoffGraphError, hd, hdd, mul_zero, add_zero, zero_pow
    (by decide : 2 ≠ 0)])

theorem operator_log_cutoff_graph_error_integrable {R : ℝ} (hR : 0 < R) :
    Integrable (operatorLogCutoffGraphError R) :=
  (operator_log_cutoff_graph_error_continuous hR).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (operator_log_cutoff_graph_error_support hR))

theorem operator_log_cutoff_graph_error_bound {R t C : ℝ} (hR : 1 ≤ R)
    (ht : 0 < t) (ht1 : t ≤ 1) (hC0 : 0 ≤ C)
    (hC : ∀ u : ℝ, |deriv smoothTransition u| ≤ C)
    (hC₂ : ∀ u : ℝ, |deriv (deriv smoothTransition) u| ≤ C) :
    operatorLogCutoffGraphError R t ≤ (16*C^2/R^2)/t := by
  have hRp : 0 < R := by linarith
  have hd := operator_log_cutoff_deriv_bound hRp ht hC
  have hdd := operator_log_cutoff_second_deriv_bound hRp ht hC hC₂
  have ha : |t * deriv (deriv (operatorLogCutoff R)) t +
      (2-t)*deriv (operatorLogCutoff R) t| ≤ 4*C/(R*t) := by
    calc
      _ ≤ |t * deriv (deriv (operatorLogCutoff R)) t| +
          |(2-t)*deriv (operatorLogCutoff R) t| := abs_add _ _
      _ = t * |deriv (deriv (operatorLogCutoff R)) t| +
          (2-t)*|deriv (operatorLogCutoff R) t| := by
        rw [abs_mul, abs_mul, abs_of_pos ht, abs_of_nonneg (by linarith : 0 ≤ 2-t)]
      _ ≤ t*(C/(R^2*t^2)+C/(R*t^2)) + 2*(C/(R*t)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hdd ht.le)
          (mul_le_mul (by linarith) hd (abs_nonneg _) (by norm_num))
      _ = (C+3*C*R)/(R^2*t) := by field_simp; ring
      _ ≤ 4*C/(R*t) := by
        apply (div_le_div_iff₀ (by positivity : 0 < R^2*t) (by positivity : 0 < R*t)).mpr
        have hCR : C ≤ C*R := by nlinarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hCR) (show 0 ≤ R*t by positivity)]
  have hs : (t * deriv (deriv (operatorLogCutoff R)) t +
      (2-t)*deriv (operatorLogCutoff R) t)^2 ≤ (4*C/(R*t))^2 :=
    (sq_le_sq).mpr (by simpa only [abs_of_nonneg (by positivity : 0 ≤ 4*C/(R*t))] using ha)
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  calc
    operatorLogCutoffGraphError R t ≤ t * (4*C/(R*t))^2 := by
      unfold operatorLogCutoffGraphError
      exact mul_le_mul (by nlinarith) hs (sq_nonneg _) ht.le
    _ = (16*C^2/R^2)/t := by field_simp; ring

theorem operator_log_cutoff_graph_error_integral_bound {R C : ℝ} (hR : 1 ≤ R)
    (hC0 : 0 ≤ C) (hC : ∀ u : ℝ, |deriv smoothTransition u| ≤ C)
    (hC₂ : ∀ u : ℝ, |deriv (deriv smoothTransition) u| ≤ C) :
    (∫ t : ℝ in Ioi 0, operatorLogCutoffGraphError R t) ≤ 16*C^2/R := by
  have hRp : 0 < R := by linarith
  have hab : Real.exp (-2*R) ≤ Real.exp (-R) := Real.exp_le_exp.mpr (by linarith)
  have hsub : Icc (Real.exp (-2*R)) (Real.exp (-R)) ⊆ Ioi (0 : ℝ) := by
    intro t ht
    exact (Real.exp_pos _).trans_le ht.1
  have heq : (∫ t : ℝ in Ioi 0, operatorLogCutoffGraphError R t) =
      ∫ t : ℝ in Icc (Real.exp (-2*R)) (Real.exp (-R)),
        operatorLogCutoffGraphError R t := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi hsub
    intro t ht
    by_contra hn
    exact ht.2 (operator_log_cutoff_graph_error_support hRp hn)
  rw [heq]
  have hg : ContinuousOn (fun t : ℝ => (16*C^2/R^2)/t)
      (Icc (Real.exp (-2*R)) (Real.exp (-R))) := by
    exact continuousOn_const.div continuousOn_id
      (fun t ht => ne_of_gt ((Real.exp_pos _).trans_le ht.1))
  calc
    _ ≤ ∫ t : ℝ in Icc (Real.exp (-2*R)) (Real.exp (-R)), (16*C^2/R^2)/t := by
      apply setIntegral_mono_on
        (operator_log_cutoff_graph_error_integrable hRp).integrableOn
        hg.integrableOn_Icc measurableSet_Icc
      intro t ht
      exact operator_log_cutoff_graph_error_bound hR
        ((Real.exp_pos _).trans_le ht.1)
        (ht.2.trans (Real.exp_le_one_iff.mpr (by linarith))) hC0 hC hC₂
    _ = 16*C^2/R := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
      simp_rw [div_eq_mul_inv]
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (Real.exp_pos _) (Real.exp_pos _)]
      rw [← Real.exp_sub, Real.log_exp]
      field_simp
      ring

/-- The critical logarithmic cutoff error tends to zero in the actual
Gamma-weighted squared graph norm. -/
theorem operator_log_cutoff_graph_error_tendsto :
    Tendsto (fun R : ℝ => ∫ t : ℝ in Ioi 0, operatorLogCutoffGraphError R t)
      atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC, hC₂⟩ := smooth_transition_derivatives_bounded
  have hlo : ∀ R : ℝ, 0 ≤ ∫ t : ℝ in Ioi 0, operatorLogCutoffGraphError R t := by
    intro R
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    exact mul_nonneg (mul_nonneg ht.le (Real.exp_pos _).le) (sq_nonneg _)
  have hhi : ∀ᶠ R : ℝ in atTop,
      (∫ t : ℝ in Ioi 0, operatorLogCutoffGraphError R t) ≤ 16*C^2/R := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact operator_log_cutoff_graph_error_integral_bound hR hC0.le hC hC₂
  apply squeeze_zero' (Eventually.of_forall hlo) hhi
  simpa only [div_eq_mul_inv, mul_zero] using
    (tendsto_const_nhds.mul (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)))

theorem operator_log_cutoff_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto (fun R : ℝ => operatorLogCutoff R t) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (max 1 (-Real.log t))] with R hR
  have hRp : 0 < R := by have := (le_max_left (1 : ℝ) (-Real.log t)).trans hR; linarith
  have hl : -R ≤ Real.log t := by have := (le_max_right (1 : ℝ) (-Real.log t)).trans hR; linarith
  exact (operator_log_cutoff_one hRp ((Real.le_log_iff_exp_le ht).mp hl)).symm

end
end Sigma
