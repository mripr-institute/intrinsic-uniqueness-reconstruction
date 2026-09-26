import SigmaProbGWTree
import SigmaProbTreeConditioning

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology Classical

/-- The concrete iid offspring field on the countable Haar source. -/
def gwOffspring (q : PMF ℕ) (ω : TreeSource) : GWOffspringArray :=
  fun w => natPMFSample q (ω w)

theorem gw_offspring_measurable (q : PMF ℕ) : Measurable (gwOffspring q) :=
  measurable_pi_lambda _ fun w => (nat_pmf_sample_measurable q).comp (measurable_pi_apply w)

theorem gw_offspring_child (q : PMF ℕ) (i : ℕ) (ω : TreeSource) :
    gwChildArray i (gwOffspring q ω) = gwOffspring q (treeChildSource i ω) := rfl

theorem gw_offspring_coordinate_law (q : PMF ℕ) (w : List ℕ) :
    treeSourceProbability.map (fun ω => gwOffspring q ω w) = q.toMeasure := by
  rw [show (fun ω => gwOffspring q ω w) = natPMFSample q ∘ (fun ω : TreeSource => ω w) from rfl,
    ← Measure.map_map (nat_pmf_sample_measurable q) (measurable_pi_apply w),
    treeCoordinate_map, nat_pmf_sample_map]

theorem gw_offspring_independent (q : PMF ℕ) :
    ProbabilityTheory.iIndepFun (fun _ : List ℕ => inferInstance)
      (fun w ω => gwOffspring q ω w) treeSourceProbability :=
  treeCoordinates_independent.comp (fun _ => natPMFSample q)
    (fun _ => nat_pmf_sample_measurable q)

def gwExtinctionProbability (q : PMF ℕ) (d : ℕ) : ℝ≥0∞ :=
  treeSourceProbability {ω | gwExtinctAt d (gwOffspring q ω)}

theorem gw_extinction_event_measurable (q : PMF ℕ) (d : ℕ) :
    MeasurableSet {ω | gwExtinctAt d (gwOffspring q ω)} :=
  (gw_extinct_measurable d).preimage (gw_offspring_measurable q)

theorem gw_extinction_probability_zero (q : PMF ℕ) : gwExtinctionProbability q 0 = 0 := by
  simp [gwExtinctionProbability, gw_extinct_zero]

theorem gw_extinction_probability_le_one (q : PMF ℕ) (d : ℕ) :
    gwExtinctionProbability q d ≤ 1 := prob_le_one

theorem gw_extinction_probability_mono (q : PMF ℕ) : Monotone (gwExtinctionProbability q) := by
  intro d e h
  exact measure_mono (fun ω hω => gw_extinct_mono _ h hω)

theorem gw_extinction_probability_succ (q : PMF ℕ) (d : ℕ) :
    gwExtinctionProbability q (d+1) = ∑' n, q n * (gwExtinctionProbability q d)^n := by
  let f : TreeSource → ℝ≥0∞ := fun ω => if gwExtinctAt d (gwOffspring q ω) then 1 else 0
  have hf : Measurable f := Measurable.ite (gw_extinction_event_measurable q d)
    measurable_const measurable_const
  have hI : (∫⁻ ω, f ω ∂treeSourceProbability) = gwExtinctionProbability q d := by
    change (∫⁻ ω, Set.indicator {ω | gwExtinctAt d (gwOffspring q ω)}
      (fun _ => (1 : ℝ≥0∞)) ω ∂treeSourceProbability) = _
    rw [lintegral_indicator_const (gw_extinction_event_measurable q d), one_mul]
    rfl
  have hprod (ω : TreeSource) :
      (∏ i ∈ Finset.range (treeRootOffspring q ω), f (treeChildSource i ω)) =
        if gwExtinctAt (d+1) (gwOffspring q ω) then 1 else 0 := by
    rw [gw_extinct_succ]
    simp only [f, ← gw_offspring_child]
    by_cases h : ∀ i < (gwOffspring q ω) [], gwExtinctAt d (gwChildArray i (gwOffspring q ω))
    · rw [if_pos h]
      apply Finset.prod_eq_one
      intro i hi
      exact if_pos (h i (Finset.mem_range.mp hi))
    · rw [if_neg h]
      push_neg at h
      obtain ⟨i, hi, hnot⟩ := h
      apply Finset.prod_eq_zero (Finset.mem_range.mpr hi)
      exact if_neg hnot
  have h := tree_offspring_product_lintegral q f hf
  rw [hI] at h
  simp_rw [hprod] at h
  change (∫⁻ ω, Set.indicator {ω | gwExtinctAt (d+1) (gwOffspring q ω)}
    (fun _ => (1 : ℝ≥0∞)) ω ∂treeSourceProbability) = _ at h
  rw [lintegral_indicator_const (gw_extinction_event_measurable q (d+1)), one_mul] at h
  exact h

/-- Extinction is exactly finiteness of the actual retained tree, not an assumed event. -/
theorem gw_finite_probability (q : PMF ℕ) :
    treeSourceProbability {ω | gwTotalSize (gwOffspring q ω) < ∞} =
      ⨆ d, gwExtinctionProbability q d := by
  have he : {ω | gwTotalSize (gwOffspring q ω) < ∞} =
      ⋃ d, {ω | gwExtinctAt d (gwOffspring q ω)} := by
    ext ω
    simp [gw_total_size_finite_iff_extinct]
  rw [he, Directed.measure_iUnion]
  · rfl
  · exact fun d e => ⟨max d e,
    fun ω hω => gw_extinct_mono _ (le_max_left _ _) hω,
    fun ω hω => gw_extinct_mono _ (le_max_right _ _) hω⟩

end
end Sigma
