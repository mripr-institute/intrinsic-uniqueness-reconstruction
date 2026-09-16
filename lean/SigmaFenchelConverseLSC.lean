import SigmaFenchelConverseLocal

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology

theorem fenchel_lower_semicontinuous_at_identifies (F : ℝ → EReal)
    (hc : fullFenchelConjugate F = intrinsicConjugateTarget)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (hl : LowerSemicontinuousWithinAt F (Ioi 0) t₀) :
    F t₀ = (I t₀ : EReal) := by
  apply le_antisymm
  · by_contra hn
    have hg : (I t₀ : EReal) < F t₀ := lt_of_not_ge hn
    obtain ⟨r, hrI, hrF⟩ := EReal.exists_between_coe_real hg
    have hIr : I t₀ < r := EReal.coe_lt_coe_iff.mp hrI
    have hnb := hl (r : EReal) hrF
    have hnb' : {t | (r : EReal) < F t} ∈ 𝓝 t₀ := by
      rwa [nhdsWithin_eq_nhds.mpr (isOpen_Ioi.mem_nhds ht₀)] at hnb
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnb'
    obtain ⟨t, v, ht, hdist, hv, hvlt⟩ :=
      fenchel_candidate_local_contact F hc ht₀ hδ (sub_pos.mpr hIr)
    have hrv := hball (show t ∈ Metric.ball t₀ δ by simpa [Real.dist_eq] using hdist)
    change (r : EReal) < F t at hrv
    rw [hv, EReal.coe_lt_coe_iff] at hrv
    linarith
  · simpa only [extendedIntrinsic, if_pos ht₀] using fenchel_candidate_lower_bound F hc t₀

theorem fenchel_lower_semicontinuous_identifies (F : ℝ → EReal)
    (hc : fullFenchelConjugate F = intrinsicConjugateTarget)
    (hl : LowerSemicontinuousOn F (Ioi 0)) : F = extendedIntrinsic := by
  funext t₀
  by_cases ht₀ : 0 < t₀
  · simpa only [extendedIntrinsic, if_pos ht₀] using
      fenchel_lower_semicontinuous_at_identifies F hc ht₀ (hl t₀ ht₀)
  · rw [fenchel_candidate_off_positive F hc (le_of_not_gt ht₀)]
    simp [extendedIntrinsic, ht₀]

theorem extended_intrinsic_continuousOn : ContinuousOn extendedIntrinsic (Ioi 0) := by
  have hi : ContinuousOn I (Ioi 0) := fun t ht =>
    (SigmaBase.potential_hasDerivAt ht).continuousAt.continuousWithinAt
  have hc := continuous_coe_real_ereal.comp_continuousOn hi
  apply hc.congr
  intro t ht
  change 0 < t at ht
  simp [extendedIntrinsic, ht]

theorem extended_intrinsic_lower_semicontinuousOn :
    LowerSemicontinuousOn extendedIntrinsic (Ioi 0) := extended_intrinsic_continuousOn.lowerSemicontinuousOn

end
end Sigma
