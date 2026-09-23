import SigmaRealTreesOffspring
import SigmaRealTreesProbability
import Mathlib.Data.Set.Card

namespace Sigma
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

def criticalLineProbability : Measure Unit := Measure.dirac ()

instance critical_line_probability_isProbability : IsProbabilityMeasure criticalLineProbability :=
  inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))

def criticalLineOffspring (_ : List ℕ) (_ : Unit) : ℕ := 1

theorem critical_line_offspring_measurable (w : List ℕ) :
    Measurable (criticalLineOffspring w) := measurable_const

theorem critical_line_offspring_independent :
    iIndepFun (fun _ : List ℕ => inferInstance) criticalLineOffspring criticalLineProbability := by
  classical
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S sets _
  by_cases h : ∀ w ∈ S, 1 ∈ sets w
  · have hp : ∀ w ∈ S, criticalLineProbability (criticalLineOffspring w ⁻¹' sets w) = 1 := by
      intro w hw
      simp [criticalLineProbability, criticalLineOffspring, h w hw]
    rw [Finset.prod_congr rfl hp, Finset.prod_const_one]
    change (Measure.dirac ()) (⋂ i ∈ S, criticalLineOffspring i ⁻¹' sets i) = 1
    rw [Measure.dirac_apply' _ (Set.to_countable _).measurableSet]
    apply indicator_of_mem
    simpa only [mem_iInter, mem_preimage, criticalLineOffspring] using h
  · push_neg at h
    obtain ⟨w, hw, hn⟩ := h
    have hp : (∏ i ∈ S, criticalLineProbability (criticalLineOffspring i ⁻¹' sets i)) = 0 := by
      apply Finset.prod_eq_zero hw
      simp [criticalLineProbability, criticalLineOffspring, hn]
    rw [hp]
    simp [criticalLineProbability, criticalLineOffspring, show ¬ ∀ i ∈ S, 1 ∈ sets i from
      fun hh => hn (hh w hw)]

theorem critical_line_offspring_law (w : List ℕ) :
    criticalLineProbability.map (criticalLineOffspring w) = Measure.dirac (1 : ℕ) := by
  rw [criticalLineProbability, Measure.map_dirac (critical_line_offspring_measurable w)]
  rfl

theorem critical_line_offspring_mean (w : List ℕ) :
    (∫ ω, (criticalLineOffspring w ω : ℝ) ∂criticalLineProbability) = 1 := by
  simp [criticalLineOffspring]

theorem critical_line_offspring_nonpoisson : PMF.pure (1 : ℕ) ≠ poissonPMF 1 := by
  intro he
  have hh := congrArg (fun p : PMF ℕ => p 0) he
  have hp : 0 < poissonPMF 1 0 :=
    ENNReal.ofReal_pos.mpr (poissonPMFReal_pos (by norm_num))
  have hz : poissonPMF 1 0 = 0 := by simpa using hh.symm
  exact hp.ne' hz

/-- The genuine active-vertex recursion of the offspring array, with the
newest edge label first in its finite word. -/
def criticalLineActive (ω : Unit) : List ℕ → Prop
  | [] => True
  | k::w => criticalLineActive ω w ∧ k < criticalLineOffspring w ω

theorem critical_line_active_iff (ω : Unit) (w : List ℕ) :
    criticalLineActive ω w ↔ ∀ k ∈ w, k = 0 := by
  induction w with
  | nil => simp [criticalLineActive]
  | cons k w ih => simp [criticalLineActive, criticalLineOffspring, ih, Nat.lt_one_iff, and_comm]

theorem critical_line_active_replicate (ω : Unit) (w : List ℕ) :
    criticalLineActive ω w ↔ w = List.replicate w.length 0 := by
  rw [critical_line_active_iff, List.eq_replicate_length]

theorem critical_line_generation (ω : Unit) (n : ℕ) :
    {w : List ℕ | criticalLineActive ω w ∧ w.length = n} = {List.replicate n 0} := by
  ext w
  simp only [mem_setOf_eq, mem_singleton_iff, critical_line_active_replicate]
  constructor
  · rintro ⟨hw, hn⟩
    simpa only [hn] using hw
  · intro hw
    subst w
    simp

theorem critical_line_one_vertex_each_generation (ω : Unit) (n : ℕ) :
    {w : List ℕ | criticalLineActive ω w ∧ w.length = n}.encard = 1 := by
  rw [critical_line_generation]
  simp

theorem critical_line_one_child (ω : Unit) (w : List ℕ) (hw : criticalLineActive ω w) :
    {k : ℕ | criticalLineActive ω (k::w)} = {0} := by
  ext k
  simp [criticalLineActive, criticalLineOffspring, hw, Nat.lt_one_iff]

def criticalLineTotalProgeny (ω : Unit) : ℕ∞ := {w : List ℕ | criticalLineActive ω w}.encard

theorem critical_line_total_progeny_infinite (ω : Unit) : criticalLineTotalProgeny ω = ⊤ := by
  apply Set.Infinite.encard_eq
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => List.replicate n 0)
  · intro m n h
    simpa only [List.length_replicate] using congrArg List.length h
  · intro n
    rw [mem_setOf_eq, critical_line_active_replicate]
    simp

theorem critical_line_total_progeny_measurable : Measurable criticalLineTotalProgeny := by
  have he : criticalLineTotalProgeny = fun _ => (⊤ : ℕ∞) :=
    funext critical_line_total_progeny_infinite
  rw [he]
  exact measurable_const

def criticalLineTotalProgenyLaw : Measure ℕ∞ := criticalLineProbability.map criticalLineTotalProgeny

def extendedBorelTotalProgenyLaw : Measure ℕ∞ := borelProbability.map (fun n : ℕ => (n : ℕ∞))

instance critical_line_total_progeny_isProbability : IsProbabilityMeasure criticalLineTotalProgenyLaw :=
  isProbabilityMeasure_map critical_line_total_progeny_measurable.aemeasurable

instance extended_borel_total_progeny_isProbability : IsProbabilityMeasure extendedBorelTotalProgenyLaw :=
  isProbabilityMeasure_map (measurable_of_countable (fun n : ℕ => (n : ℕ∞))).aemeasurable

theorem critical_line_total_progeny_law : criticalLineTotalProgenyLaw = Measure.dirac ⊤ := by
  rw [criticalLineTotalProgenyLaw, criticalLineProbability,
    Measure.map_dirac critical_line_total_progeny_measurable, critical_line_total_progeny_infinite]

theorem extended_borel_total_progeny_finite : extendedBorelTotalProgenyLaw {⊤} = 0 := by
  rw [extendedBorelTotalProgenyLaw, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : (fun n : ℕ => (n : ℕ∞)) ⁻¹' {⊤} = ∅ := by
    ext n
    simp
  rw [he, measure_empty]

/-- Critical iid offspring alone does not identify the Borel total-size law.
This witness is the degenerate one-child process, not the stronger finite,
almost-surely extinct binary example in the paper's proof. -/
theorem criticality_does_not_identify_borel_total_progeny :
    criticalLineTotalProgenyLaw ≠ extendedBorelTotalProgenyLaw := by
  intro he
  have hh := congrArg (fun μ : Measure ℕ∞ => μ {⊤}) he
  dsimp only at hh
  rw [critical_line_total_progeny_law, Measure.dirac_apply_of_mem (by simp),
    extended_borel_total_progeny_finite] at hh
  exact one_ne_zero hh

theorem critical_iid_galton_watson_boundary :
    iIndepFun (fun _ : List ℕ => inferInstance) criticalLineOffspring criticalLineProbability ∧
      (∀ w, criticalLineProbability.map (criticalLineOffspring w) = Measure.dirac (1 : ℕ)) ∧
      (∀ w, (∫ ω, (criticalLineOffspring w ω : ℝ) ∂criticalLineProbability) = 1) ∧
      (PMF.pure (1 : ℕ) ≠ poissonPMF 1) ∧
      (∀ ω, criticalLineTotalProgeny ω = ⊤) ∧
      criticalLineTotalProgenyLaw ≠ extendedBorelTotalProgenyLaw :=
  ⟨critical_line_offspring_independent, critical_line_offspring_law,
    critical_line_offspring_mean, critical_line_offspring_nonpoisson,
    critical_line_total_progeny_infinite, criticality_does_not_identify_borel_total_progeny⟩

end
end Sigma
