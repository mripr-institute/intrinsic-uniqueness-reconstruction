import SigmaProbGamma

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- The usual topological support, expressed by positive measure of every open
neighborhood.  This definition uses the ambient marked real coordinate. -/
def topologicalMeasureSupport (μ : Measure ℝ) : Set ℝ :=
  {x | ∀ U : Set ℝ, IsOpen U → x ∈ U → 0 < μ U}

theorem gamma_pdf_function_support :
    Function.support (ProbabilityTheory.gammaPDF 2 1) = Ioi (0 : ℝ) := by
  ext t
  change ProbabilityTheory.gammaPDF 2 1 t ≠ 0 ↔ 0 < t
  rw [ProbabilityTheory.gammaPDF]
  constructor
  · intro h
    by_contra ht
    have hle : t ≤ 0 := le_of_not_gt ht
    rcases hle.eq_or_lt with he | hn
    · subst t
      simp [gamma_pdf_intrinsic, SigmaPresentations.density] at h
    · simp [gamma_pdf_intrinsic, hn.not_le] at h
  · intro ht
    exact (ENNReal.ofReal_pos.mpr
      (ProbabilityTheory.gammaPDFReal_pos (by norm_num) (by norm_num) ht)).ne'

theorem gamma_probability_open_positive_iff (U : Set ℝ) (hU : IsOpen U) :
    0 < gammaProbability U ↔ (Ioi (0 : ℝ) ∩ U).Nonempty := by
  have hm : Measurable (ProbabilityTheory.gammaPDF 2 1) :=
    (ProbabilityTheory.measurable_gammaPDFReal 2 1).ennreal_ofReal
  rw [gammaProbability, ProbabilityTheory.gammaMeasure,
    withDensity_apply _ hU.measurableSet,
    setLintegral_pos_iff hm,
    gamma_pdf_function_support]
  exact (isOpen_Ioi.inter hU).measure_pos_iff volume

theorem gamma_probability_topological_support :
    topologicalMeasureSupport gammaProbability = Ici (0 : ℝ) := by
  have he : topologicalMeasureSupport gammaProbability = closure (Ioi (0 : ℝ)) := by
    ext x
    rw [mem_closure_iff]
    change (∀ U : Set ℝ, IsOpen U → x ∈ U → 0 < gammaProbability U) ↔ _
    constructor
    · intro h U hU hx
      have hn := (gamma_probability_open_positive_iff U hU).mp (h U hU hx)
      simpa only [inter_comm] using hn
    · intro h U hU hx
      apply (gamma_probability_open_positive_iff U hU).mpr
      simpa only [inter_comm] using h U hU hx
  rw [he, closure_Ioi]

end
end Sigma
