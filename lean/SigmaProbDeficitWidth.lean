import SigmaProbDeficit

namespace Sigma
noncomputable section
open MeasureTheory Set
open scoped ENNReal

/-- Sublevel masses determine a measure even when its total mass is infinite. -/
theorem measure_eq_of_finite_Iic_eq (μ ν : Measure ℝ)
    (hfinite : ∀ v, μ (Iic v) ≠ ∞)
    (heq : ∀ v, μ (Iic v) = ν (Iic v)) : μ = ν := by
  apply Measure.ext_of_Ioc' μ ν
  · intro a b _
    exact ne_top_of_le_ne_top (hfinite b) (measure_mono Ioc_subset_Iic_self)
  · intro a b hab
    rw [← Iic_diff_Iic,
      measure_diff (Iic_subset_Iic.2 hab.le) nullMeasurableSet_Iic (hfinite a),
      measure_diff (Iic_subset_Iic.2 hab.le) nullMeasurableSet_Iic
        (by rw [← heq a]; exact hfinite a), heq a, heq b]

theorem TwoBranchPotential.level_measure_Iic {J : ℝ → ℝ}
    (hJ : TwoBranchPotential J) (v a b : ℝ)
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hb1 : 1 ≤ b) (ha : J a = v) (hb : J b = v) :
    Measure.map J (volume.restrict (Ioi 0)) (Iic v) = ENNReal.ofReal (b-a) := by
  rw [Measure.map_apply hJ.measurable measurableSet_Iic,
    Measure.restrict_apply (hJ.measurable measurableSet_Iic),
    hJ.sublevel_interval a b v ha0 ha1 hb1 ha hb, Real.volume_Icc]

theorem TwoBranchPotential.level_measure_Iic_negative {J : ℝ → ℝ}
    (hJ : TwoBranchPotential J) (v : ℝ) (hv : v < 0) :
    Measure.map J (volume.restrict (Ioi 0)) (Iic v) = 0 := by
  rw [Measure.map_apply hJ.measurable measurableSet_Iic,
    Measure.restrict_apply (hJ.measurable measurableSet_Iic)]
  have hempty : J ⁻¹' Iic v ∩ Ioi 0 = ∅ := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro t ht
    have hnonneg := hJ.nonnegative ht.2
    have hle : J t ≤ v := ht.1
    linarith
  rw [hempty, measure_empty]

/-- Equal sublevel widths imply equality of the actual unweighted level measures. -/
theorem equal_widths_level_measure {J K : ℝ → ℝ}
    (hJ : TwoBranchPotential J) (hK : TwoBranchPotential K)
    (hwidth : ∀ v ≥ 0, ∃ a b c d : ℝ,
      (0 < a ∧ a ≤ 1 ∧ 1 ≤ b ∧ J a = v ∧ J b = v) ∧
      (0 < c ∧ c ≤ 1 ∧ 1 ≤ d ∧ K c = v ∧ K d = v) ∧ b-a = d-c) :
    Measure.map J (volume.restrict (Ioi 0)) =
      Measure.map K (volume.restrict (Ioi 0)) := by
  apply measure_eq_of_finite_Iic_eq
  · intro v
    by_cases hv : 0 ≤ v
    · obtain ⟨a, b, ha0, ha1, hb1, ha, hb⟩ := hJ.roots v hv
      rw [hJ.level_measure_Iic v a b ha0 ha1 hb1 ha hb]
      exact ENNReal.ofReal_ne_top
    · rw [hJ.level_measure_Iic_negative v (lt_of_not_ge hv)]
      exact ENNReal.zero_ne_top
  · intro v
    by_cases hv : 0 ≤ v
    · obtain ⟨a, b, c, d, hJr, hKr, hw⟩ := hwidth v hv
      rw [hJ.level_measure_Iic v a b hJr.1 hJr.2.1 hJr.2.2.1 hJr.2.2.2.1 hJr.2.2.2.2,
        hK.level_measure_Iic v c d hKr.1 hKr.2.1 hKr.2.2.1 hKr.2.2.2.1 hKr.2.2.2.2, hw]
    · rw [hJ.level_measure_Iic_negative v (lt_of_not_ge hv),
        hK.level_measure_Iic_negative v (lt_of_not_ge hv)]

/-- Width equality gives equality of linked deficit probability laws, not just CDF formulas. -/
theorem equal_widths_linked_deficit_law {J K : ℝ → ℝ}
    (hJ : TwoBranchPotential J) (hK : TwoBranchPotential K)
    (hwidth : ∀ v ≥ 0, ∃ a b c d : ℝ,
      (0 < a ∧ a ≤ 1 ∧ 1 ≤ b ∧ J a = v ∧ J b = v) ∧
      (0 < c ∧ c ≤ 1 ∧ 1 ≤ d ∧ K c = v ∧ K d = v) ∧ b-a = d-c) :
    Measure.map J ((volume.restrict (Ioi 0)).withDensity (deficitWeight ∘ J)) =
      Measure.map K ((volume.restrict (Ioi 0)).withDensity (deficitWeight ∘ K)) := by
  rw [← map_with_linked_density _ J hJ.measurable _ deficit_weight_measurable,
    ← map_with_linked_density _ K hK.measurable _ deficit_weight_measurable,
    equal_widths_level_measure hJ hK hwidth]

/-- Equality of measurable pushforwards transfers normalization to the original measure. -/
theorem probability_of_map_eq_probability {μ ν : Measure ℝ} {J K : ℝ → ℝ}
    (hJ : Measurable J) (hK : Measurable K) [IsProbabilityMeasure ν]
    (heq : Measure.map J μ = Measure.map K ν) : IsProbabilityMeasure μ := by
  constructor
  have h := congrArg (fun ρ : Measure ℝ => ρ univ) heq
  simpa only [Measure.map_apply hJ MeasurableSet.univ,
    Measure.map_apply hK MeasurableSet.univ, preimage_univ, measure_univ] using h

end
end Sigma
