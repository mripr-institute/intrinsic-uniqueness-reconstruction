import SigmaOpZeroEnergy

namespace Sigma
noncomputable section
open Set Filter MeasureTheory Real
open scoped Topology ContDiff ENNReal

def endpointTransition (a b t : ℝ) : ℂ := smoothTransition ((t-a)/(b-a))

theorem endpoint_transition_contDiff (a b : ℝ) : ContDiff ℝ ∞ (endpointTransition a b) :=
  Complex.ofRealCLM.contDiff.comp (smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _))

theorem endpoint_transition_zero {a b t : ℝ} (hab : a < b) (ht : t ≤ a) :
    endpointTransition a b t = 0 := by
  rw [endpointTransition,smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr ht) (sub_pos.mpr hab).le),Complex.ofReal_zero]

theorem endpoint_transition_one {a b t : ℝ} (hab : a < b) (ht : b ≤ t) :
    endpointTransition a b t = 1 := by
  rw [endpointTransition,smoothTransition.one_of_one_le
    ((one_le_div (sub_pos.mpr hab)).mpr (sub_le_sub_right ht a)),Complex.ofReal_one]

theorem endpoint_transition_norm_le (a b t : ℝ) : ‖endpointTransition a b t‖ ≤ 1 := by
  simpa only [endpointTransition,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (smoothTransition.nonneg _)] using smoothTransition.le_one ((t-a)/(b-a))

theorem endpoint_transition_complement_norm_le (a b t : ℝ) : ‖1-endpointTransition a b t‖ ≤ 1 := by
  rw [endpointTransition,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (smoothTransition.le_one _))]
  linarith [smoothTransition.nonneg ((t-a)/(b-a))]

theorem constant_tails_derivative_tsupport (χ : ℝ → ℂ) (a b : ℝ) (c d : ℂ)
    (hl : ∀ t ≤ a, χ t=c) (hr : ∀ t, b ≤ t → χ t=d) :
    tsupport (deriv χ) ⊆ Icc a b := by
  apply closure_minimal ?_ isClosed_Icc
  intro t ht
  by_contra hn
  have he : ∃ k : ℂ, χ =ᶠ[𝓝 t] (fun _ => k) := by
    rcases not_and_or.mp hn with h | h
    · refine ⟨c,?_⟩
      filter_upwards [eventually_lt_nhds (lt_of_not_ge h)] with s hs
      exact hl s hs.le
    · refine ⟨d,?_⟩
      filter_upwards [eventually_gt_nhds (lt_of_not_ge h)] with s hs
      exact hr s hs.le
  obtain ⟨k,hk⟩ := he
  exact ht (hk.deriv_eq.trans (deriv_const t k))

theorem endpoint_transition_derivative_support {a b : ℝ} (hab : a < b) :
    tsupport (deriv (endpointTransition a b)) ⊆ Icc a b :=
  constant_tails_derivative_tsupport _ a b 0 1
    (fun _ ht => endpoint_transition_zero hab ht) (fun _ ht => endpoint_transition_one hab ht)

theorem endpoint_transition_complement_derivative_support {a b : ℝ} (hab : a < b) :
    tsupport (deriv (fun t => 1-endpointTransition a b t)) ⊆ Icc a b :=
  constant_tails_derivative_tsupport _ a b 1 0
    (fun _ ht => by rw [endpoint_transition_zero hab ht,sub_zero])
    (fun _ ht => by rw [endpoint_transition_one hab ht,sub_self])

theorem gamma_local_l2_cutoff (U χ : ℝ → ℂ) {S : Set ℝ} (hS : MeasurableSet S)
    (hU : Memℒp U 2 (gammaProbability.restrict S))
    (hχ : Continuous χ) (hb : ∀ t, ‖χ t‖ ≤ 1)
    (hs : ∀ t, 0 < t → t ∉ S → χ t=0) :
    Memℒp (fun t => χ t*U t) 2 gammaProbability := by
  have hi : Memℒp (S.indicator U) 2 gammaProbability := (memℒp_indicator_iff_restrict hS).mpr hU
  have hc : Memℒp χ ∞ gammaProbability := Memℒp.of_bound hχ.aestronglyMeasurable 1
    (Eventually.of_forall hb)
  have hm := hc.smul_of_top_left hi
  apply hm.ae_eq
  apply gamma_ae_iff_positive_volume_ae.mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  by_cases hs' : t ∈ S
  · simp [hs',smul_eq_mul,mul_comm]
  · simp [hs',hs t ht hs',smul_eq_mul]

end
end Sigma
