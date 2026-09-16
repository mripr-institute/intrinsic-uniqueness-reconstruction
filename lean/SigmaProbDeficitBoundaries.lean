import SigmaProbCanonicalPair
import SigmaProbDeficitTransform

namespace Sigma
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal

/-- The upper inverse branch, extended constantly below the deficit range. -/
def canonicalUpperRoot (v : ℝ) : ℝ :=
  if 0 ≤ v then (canonicalDeficitRoots v).2 else 1

theorem canonical_upper_root_spec (v : ℝ) (hv : 0 ≤ v) :
    1 ≤ canonicalUpperRoot v ∧ SigmaBase.potential (canonicalUpperRoot v) = v := by
  simp only [canonicalUpperRoot, if_pos hv]
  exact ⟨(canonical_deficit_roots_spec v hv).2.2.1,
    (canonical_deficit_roots_spec v hv).2.2.2.2⟩

theorem canonical_upper_root_monotone : Monotone canonicalUpperRoot := by
  intro v w hvw
  by_cases hw : 0 ≤ w
  · by_cases hv : 0 ≤ v
    · simp only [canonicalUpperRoot, if_pos hv, if_pos hw]
      have hs := canonical_deficit_roots_spec v hv
      have ht := canonical_deficit_roots_spec w hw
      by_contra hlt
      have hlt' : (canonicalDeficitRoots w).2 < (canonicalDeficitRoots v).2 :=
        lt_of_not_ge hlt
      have hpot := intrinsic_potential_two_branch.right_strict ht.2.2.1
        hs.2.2.1 hlt'
      rw [ht.2.2.2.2, hs.2.2.2.2] at hpot
      linarith
    · have hs := canonical_upper_root_spec w hw
      simp only [canonicalUpperRoot, if_neg hv, if_pos hw]
      exact (canonical_deficit_roots_spec w hw).2.2.1
  · have hw' : w < 0 := lt_of_not_ge hw
    have hv : v < 0 := lt_of_le_of_lt hvw hw'
    have hv' : ¬ 0 ≤ v := not_le_of_gt hv
    simp only [canonicalUpperRoot, if_neg hv', if_neg hw]
    norm_num

theorem canonical_upper_root_measurable : Measurable canonicalUpperRoot :=
  canonical_upper_root_monotone.measurable

def upperBranchProbability : Measure ℝ :=
  Measure.map canonicalUpperRoot gammaDeficitProbability

instance upper_branch_probability_is_probability :
    IsProbabilityMeasure upperBranchProbability := by
  constructor
  rw [upperBranchProbability, Measure.map_apply canonical_upper_root_measurable MeasurableSet.univ,
    preimage_univ, measure_univ]

theorem upper_branch_potential_probability :
    Measure.map SigmaBase.potential upperBranchProbability = gammaDeficitProbability := by
  rw [upperBranchProbability,
    Measure.map_map intrinsic_potential_measurable canonical_upper_root_measurable]
  calc
    Measure.map (SigmaBase.potential ∘ canonicalUpperRoot) gammaDeficitProbability =
        Measure.map id gammaDeficitProbability := by
      apply Measure.map_congr
      filter_upwards [gamma_deficit_nonnegative] with v hv
      exact (canonical_upper_root_spec v hv).2
    _ = gammaDeficitProbability := Measure.map_id

theorem upper_branch_ae_ge_one : ∀ᵐ t ∂upperBranchProbability, 1 ≤ t := by
  rw [upperBranchProbability, ae_map_iff canonical_upper_root_measurable.aemeasurable
    measurableSet_Ici]
  filter_upwards [gamma_deficit_nonnegative] with v hv
  exact canonical_upper_root_spec v hv |>.1

theorem upper_branch_Ici_one : upperBranchProbability (Ici 1) = 1 := by
  have h := (ae_iff_measure_eq measurableSet_Ici.nullMeasurableSet).mp upper_branch_ae_ge_one
  simpa only [measure_univ] using h

theorem gamma_Ici_one : gammaProbability (Ici 1) = ENNReal.ofReal (2 * Real.exp (-1)) := by
  rw [show Ici (1 : ℝ) = Ioi 1 ∪ {1} by ext; simp [le_iff_lt_or_eq],
    measure_union (by simp) (measurableSet_singleton 1), gamma_probability_tail 1 (by norm_num),
    gamma_probability_no_atom]
  simp [gammaSurvival]
  ring

theorem gamma_Ici_one_lt_one : gammaProbability (Ici 1) < 1 := by
  rw [gamma_Ici_one]
  rw [← ENNReal.ofReal_one]
  apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).2
  have he : (2 : ℝ) < Real.exp 1 := by
    have he' := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    norm_num at he'
    exact he'
  have he' := mul_lt_mul_of_pos_right he (Real.exp_pos (-1))
  rw [← Real.exp_add] at he'
  simpa using he'

/-- The law obtained by always taking the upper root has the same deficit law,
but is not the Gamma source law. This is the source-law boundary in P4. -/
theorem upper_branch_source_counterexample :
    Measure.map SigmaBase.potential upperBranchProbability = gammaDeficitProbability ∧
    upperBranchProbability ≠ gammaProbability := by
  refine ⟨upper_branch_potential_probability, ?_⟩
  intro he
  have h := congrArg (fun μ : Measure ℝ => μ (Ici 1)) he
  change upperBranchProbability (Ici 1) = gammaProbability (Ici 1) at h
  rw [upper_branch_Ici_one] at h
  exact (ne_of_lt gamma_Ici_one_lt_one) h.symm

end
end Sigma
