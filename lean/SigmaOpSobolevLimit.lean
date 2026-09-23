import SigmaOpSobolevPrimitive
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal NNReal

theorem positive_locally_integrable_interval (g : ℝ → ℂ)
    (hg : LocallyIntegrableOn g (Ioi 0) volume) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable g volume a b := by
  apply IntegrableOn.intervalIntegrable
  apply hg.integrableOn_compact_subset _ isCompact_uIcc
  intro t ht
  exact (lt_min ha hb).trans_le ht.1

/-- A local `L¹` limit of derivatives and an a.e. pointwise limit of the
functions produce an actual integral representative. No regularity property
of the limiting representative is imposed as a hypothesis. -/
theorem positive_sobolev_limit_integral_representative
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hpos : ∀ᵐ t ∂μ, 0 < t)
    (f : ℕ → ℝ → ℂ) (hf : ∀ k, ContDiff ℝ ∞ (f k)) (F G : ℝ → ℂ)
    (hG : LocallyIntegrableOn G (Ioi 0) volume)
    (hF : ∀ᵐ t ∂μ, Tendsto (fun k => f k t) atTop (𝓝 (F t)))
    (hd : ∀ a b : ℝ, 0 < a → 0 < b →
      Tendsto (fun k => ∫ t : ℝ in uIcc a b, ‖deriv (f k) t-G t‖) atTop (𝓝 0)) :
    ∃ a : ℝ, 0 < a ∧
      (∀ t : ℝ, 0 < t → Tendsto (fun k => f k t) atTop
        (𝓝 (F a + ∫ u in a..t, G u))) ∧
      (fun t => F a + ∫ u in a..t, G u) =ᵐ[μ] F := by
  obtain ⟨a, ha, hfa⟩ := (hpos.and hF).exists
  have hg (t : ℝ) (ht : 0 < t) : IntervalIntegrable G volume a t :=
    positive_locally_integrable_interval G hG ha ht
  have hlim (t : ℝ) (ht : 0 < t) :
      Tendsto (fun k => ∫ u in a..t, deriv (f k) u) atTop (𝓝 (∫ u in a..t, G u)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hder (k : ℕ) : IntervalIntegrable (deriv (f k)) volume a t :=
      ((hf k).continuous_deriv (by simp)).intervalIntegrable a t
    apply squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) (hd a t ha ht)
    rw [← intervalIntegral.integral_sub (hder k) (hg t ht)]
    exact (intervalIntegral.norm_integral_le_integral_norm_Ioc).trans_eq
      (integral_Icc_eq_integral_Ioc.symm)
  have hall (t : ℝ) (ht : 0 < t) :
      Tendsto (fun k => f k t) atTop (𝓝 (F a + ∫ u in a..t, G u)) := by
    have hh := hfa.add (hlim t ht)
    convert hh using 1
    funext k
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun u _ => (hf k).differentiable (by simp) u)
      (((hf k).continuous_deriv (by simp)).intervalIntegrable a t)]
    abel
  refine ⟨a, ha, hall, ?_⟩
  filter_upwards [hpos, hF] with t ht hft
  exact tendsto_nhds_unique (hall t ht) hft

/-- Explicit local absolute continuity of the representative on every compact
interval strictly inside the positive ray. -/
theorem positive_primitive_absolute_continuity (g : ℝ → ℂ)
    (hg : LocallyIntegrableOn g (Ioi 0) volume) {a l r : ℝ} (ha : 0 < a) (hl : 0 < l)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ (m : ℕ) (u v : Fin m → ℝ),
      (∀ i, l ≤ u i ∧ u i ≤ v i ∧ v i ≤ r) →
      (Set.univ.PairwiseDisjoint (fun i => Ioc (u i) (v i))) →
      (∑ i, ENNReal.ofReal (v i-u i)) < δ →
      (∑ i, (‖(∫ t in a..v i, g t) - ∫ t in a..u i, g t‖₊ : ℝ≥0∞)) < ε := by
  let g₀ := (Icc l r).indicator g
  have hg₀ : Integrable g₀ volume := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact hg.integrableOn_compact_subset (fun t ht => hl.trans_le ht.1) isCompact_Icc
  obtain ⟨δ, hδ, hd⟩ := integrable_primitive_absolute_continuity g₀ hg₀ a ε hε
  refine ⟨δ, hδ, ?_⟩
  intro m u v huv hdis hlen
  have he (i : Fin m) :
      (∫ t in a..v i, g t) - ∫ t in a..u i, g t =
        (∫ t in a..v i, g₀ t) - ∫ t in a..u i, g₀ t := by
    have hui : 0 < u i := hl.trans_le (huv i).1
    have hvi : 0 < v i := hui.trans_le (huv i).2.1
    rw [intervalIntegral.integral_interval_sub_left
      (positive_locally_integrable_interval g hg ha hvi)
      (positive_locally_integrable_interval g hg ha hui),
      intervalIntegral.integral_interval_sub_left hg₀.intervalIntegrable hg₀.intervalIntegrable]
    apply intervalIntegral.integral_congr
    intro t ht
    have htt : t ∈ Icc l r :=
      (uIcc_subset_Icc ⟨(huv i).1, (huv i).2.1.trans (huv i).2.2⟩
        ⟨(huv i).1.trans (huv i).2.1, (huv i).2.2⟩) ht
    exact (indicator_of_mem htt g).symm
  simp_rw [he]
  exact hd m u v (fun i => (huv i).2.1) hdis hlen

theorem positive_primitive_hasDerivAt_ae_interval (g : ℝ → ℂ)
    (hg : LocallyIntegrableOn g (Ioi 0) volume) {a l r : ℝ} (ha : 0 < a) (hl : 0 < l) :
    ∀ᵐ x : ℝ ∂volume.restrict (Ioo l r),
      HasDerivAt (fun t => ∫ u in a..t, g u) (g x) x := by
  let g₀ := (Icc l r).indicator g
  have hg₀ : Integrable g₀ volume := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact hg.integrableOn_compact_subset (fun t ht => hl.trans_le ht.1) isCompact_Icc
  have hder := locally_integrable_primitive_hasDerivAt_ae g₀ hg₀.locallyIntegrable a
  filter_upwards [ae_restrict_of_ae hder, ae_restrict_mem measurableSet_Ioo] with x hx hxr
  have hxp : 0 < x := hl.trans hxr.1
  have he : (fun t => ∫ u in a..t, g u) =ᶠ[𝓝 x]
      (fun t => (∫ u in a..x, g u) + ((∫ u in a..t, g₀ u) - ∫ u in a..x, g₀ u)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hxr] with t ht
    have htp : 0 < t := hl.trans ht.1
    have hEq : (∫ u in a..t, g u) - ∫ u in a..x, g u =
        (∫ u in a..t, g₀ u) - ∫ u in a..x, g₀ u := by
      rw [intervalIntegral.integral_interval_sub_left
        (positive_locally_integrable_interval g hg ha htp)
        (positive_locally_integrable_interval g hg ha hxp),
        intervalIntegral.integral_interval_sub_left hg₀.intervalIntegrable hg₀.intervalIntegrable]
      apply intervalIntegral.integral_congr
      intro u hu
      exact (indicator_of_mem
        ((uIcc_subset_Icc ⟨hxr.1.le, hxr.2.le⟩ ⟨ht.1.le, ht.2.le⟩) hu) g).symm
    exact eq_add_of_sub_eq' hEq
  have hh := ((hx.sub_const (∫ u in a..x, g₀ u)).const_add (∫ u in a..x, g u)).congr_of_eventuallyEq he
  simpa only [g₀, indicator_of_mem (show x ∈ Icc l r from ⟨hxr.1.le, hxr.2.le⟩)] using hh

theorem positive_primitive_hasDerivAt_ae (g : ℝ → ℂ)
    (hg : LocallyIntegrableOn g (Ioi 0) volume) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0),
      HasDerivAt (fun t => ∫ u in a..t, g u) (g x) x := by
  have hi (n : ℕ) : ∀ᵐ x : ℝ,
      x ∈ Ioo (1/(n+1 : ℝ)) (n+1 : ℝ) →
        HasDerivAt (fun t => ∫ u in a..t, g u) (g x) x :=
    (ae_restrict_iff' measurableSet_Ioo).mp
      (positive_primitive_hasDerivAt_ae_interval g hg ha (by positivity))
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [ae_all_iff.mpr hi] with x hx
  intro hxp
  obtain ⟨n, hn⟩ := exists_nat_gt (max x x⁻¹)
  apply hx n
  constructor
  · apply (div_lt_iff₀ (by positivity : 0 < (n+1 : ℝ))).mpr
    have hi : x⁻¹ < (n : ℝ) := (le_max_right _ _).trans_lt hn
    have hm := mul_lt_mul_of_pos_left hi hxp
    rw [mul_inv_cancel₀ hxp.ne'] at hm
    nlinarith
  · have ht : x < (n : ℝ) := (le_max_left _ _).trans_lt hn
    linarith

/-- Local Sobolev limits have a representative with the actual a.e.
derivative and the literal local absolute-continuity condition. -/
theorem positive_sobolev_limit_regular_representative
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hpos : ∀ᵐ t ∂μ, 0 < t)
    (f : ℕ → ℝ → ℂ) (hf : ∀ k, ContDiff ℝ ∞ (f k)) (F G : ℝ → ℂ)
    (hG : LocallyIntegrableOn G (Ioi 0) volume)
    (hF : ∀ᵐ t ∂μ, Tendsto (fun k => f k t) atTop (𝓝 (F t)))
    (hd : ∀ a b : ℝ, 0 < a → 0 < b →
      Tendsto (fun k => ∫ t : ℝ in uIcc a b, ‖deriv (f k) t-G t‖) atTop (𝓝 0)) :
    ∃ H : ℝ → ℂ, H =ᵐ[μ] F ∧
      (∀ᵐ t ∂volume.restrict (Ioi 0), HasDerivAt H (G t) t) ∧
      (∀ l r : ℝ, 0 < l → ∀ ε : ℝ≥0∞, ε ≠ 0 →
        ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ (m : ℕ) (u v : Fin m → ℝ),
          (∀ i, l ≤ u i ∧ u i ≤ v i ∧ v i ≤ r) →
          (Set.univ.PairwiseDisjoint (fun i => Ioc (u i) (v i))) →
          (∑ i, ENNReal.ofReal (v i-u i)) < δ →
          (∑ i, (‖H (v i)-H (u i)‖₊ : ℝ≥0∞)) < ε) := by
  obtain ⟨a, ha, _, hrep⟩ :=
    positive_sobolev_limit_integral_representative μ hpos f hf F G hG hF hd
  refine ⟨fun t => F a + ∫ u in a..t, G u, hrep, ?_, ?_⟩
  · filter_upwards [positive_primitive_hasDerivAt_ae G hG ha] with t ht
    exact ht.const_add (F a)
  · intro l r hl ε hε
    obtain ⟨δ, hδ, hh⟩ := positive_primitive_absolute_continuity G hG ha hl ε hε (r := r)
    refine ⟨δ, hδ, ?_⟩
    intro m u v huv hdis hlen
    simpa only [add_sub_add_left_eq_sub] using hh m u v huv hdis hlen

end
end Sigma
