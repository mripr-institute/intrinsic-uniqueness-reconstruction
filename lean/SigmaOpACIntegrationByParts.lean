import SigmaOpACProduct

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem complex_local_test_product_integrable (u w : ℝ → ℂ)
    (hu : LocallyIntegrableOn u (Ioi 0) volume)
    (hw : Continuous w) (hs : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) :
    Integrable (fun t => u t * w t) := by
  have hi : Integrable ((tsupport w).indicator u) := by
    rw [integrable_indicator_iff hs.measurableSet]
    exact hu.integrableOn_compact_subset hp hs
  have hh := hi.smul_of_top_left (hw.memℒp_top_of_hasCompactSupport hs volume)
  apply hh.congr
  filter_upwards with t
  by_cases ht : t ∈ tsupport w
  · simp [ht, smul_eq_mul]
  · simp [ht, image_eq_zero_of_nmem_tsupport ht, smul_eq_mul]

/-- Integration by parts against genuine compact interior tests, requiring only
literal local absolute continuity and a locally integrable a.e. derivative. -/
theorem PositiveRayLocallyAbsolutelyContinuous.compact_integration_by_parts
    {F g : ℝ → ℂ} (hF : PositiveRayLocallyAbsolutelyContinuous F)
    (hg : LocallyIntegrableOn g (Ioi 0) volume)
    (hder : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), HasDerivAt F (g t) t)
    (w : ℝ → ℂ) (hw : ContDiff ℝ ∞ w) (hs : HasCompactSupport w)
    (hp : tsupport w ⊆ Ioi 0) :
    (∫ t : ℝ, g t * w t) + (∫ t : ℝ, F t * deriv w t) = 0 := by
  have hdw : ContDiff ℝ ∞ (deriv w) := (contDiff_infty_iff_deriv.mp hw).2
  have hsp : tsupport (deriv w) ⊆ tsupport w := closure_minimal support_deriv_subset isClosed_closure
  have hFl : LocallyIntegrableOn F (Ioi 0) volume :=
    hF.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hgw := complex_local_test_product_integrable g w hg hw.continuous hs hp
  have hFw := complex_local_test_product_integrable F (deriv w) hFl hdw.continuous hs.deriv (hsp.trans hp)
  let D : ℝ → ℂ := fun t => g t*w t+F t*deriv w t
  have hD : LocallyIntegrableOn D (Ioi 0) volume :=
    (hg.mul_continuousOn hw.continuous.continuousOn isOpen_Ioi.isLocallyClosed).add
      ((hF.continuousOn.mul hdw.continuous.continuousOn).locallyIntegrableOn measurableSet_Ioi)
  have hDp : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), HasDerivAt (fun t => F t*w t) (D t) t := by
    filter_upwards [hder] with t ht
    exact ht.mul ((hw.differentiable (by simp) t).hasDerivAt)
  have hDs : Function.support D ⊆ tsupport w := by
    intro t ht
    by_contra hn
    have hd : deriv w t = 0 := image_eq_zero_of_nmem_tsupport (fun hh => hn (hsp hh))
    exact ht (by simp [D,image_eq_zero_of_nmem_tsupport hn,hd])
  by_cases hne : (tsupport w).Nonempty
  · obtain ⟨m,hm,hmin⟩ := hs.exists_isMinOn hne continuous_id.continuousOn
    obtain ⟨M,hM,hmax⟩ := hs.exists_isMaxOn hne continuous_id.continuousOn
    have hm0 : 0 < m := hp hm
    let a := m/2
    let b := M+1
    have ha : 0 < a := by dsimp [a]; linarith
    have hmM : m ≤ M := hmin hM
    have hb : 0 < b := by dsimp [b]; linarith
    have hbounds : ∀ t ∈ tsupport w, a < t ∧ t < b := by
      intro t ht
      have hmt : m ≤ t := hmin ht
      have htM : t ≤ M := hmax ht
      dsimp [a,b]
      constructor <;> linarith
    have hwa : w a = 0 := image_eq_zero_of_nmem_tsupport (fun h => (lt_irrefl a) (hbounds a h).1)
    have hwb : w b = 0 := image_eq_zero_of_nmem_tsupport (fun h => (lt_irrefl b) (hbounds b h).2)
    have he := (hF.mul (smooth_positive_locally_ac hw)).integral_eq_sub hD hDp ha hb
    rw [hwa,hwb,mul_zero,mul_zero,sub_self] at he
    rw [intervalIntegral.integral_eq_integral_of_support_subset
      (fun t ht => ⟨(hbounds t (hDs ht)).1,(hbounds t (hDs ht)).2.le⟩)] at he
    simpa only [D,integral_add hgw hFw] using he
  · have hwz : w = 0 := tsupport_eq_empty_iff.mp (Set.not_nonempty_iff_eq_empty.mp hne)
    simp only [hwz, Pi.zero_apply, mul_zero, integral_zero, zero_add]
    have hz : deriv (0 : ℝ → ℂ) = 0 := funext fun t => (hasDerivAt_const t (0 : ℂ)).deriv
    simp [hz]

end
end Sigma
