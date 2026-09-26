import SigmaProbOffspringArray
import SigmaProbGWTree
import Mathlib.MeasureTheory.Constructions.Projective

namespace Sigma
noncomputable section
open MeasureTheory Measure Set ProbabilityTheory
open scoped BigOperators

variable {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The actual law of every finite offspring block follows from coordinate
independence and its one-coordinate laws. -/
theorem iid_nat_array_finite_law (q : ι → PMF ℕ) (μ : Measure Ω)
    (X : Ω → ι → ℕ) (hX : ∀ i, Measurable (fun ω => X ω i))
    (hI : iIndepFun (fun _ : ι => inferInstance) (fun i ω => X ω i) μ)
    (hL : ∀ i, μ.map (fun ω => X ω i) = (q i).toMeasure) (S : Finset ι) :
    μ.map (fun ω => S.restrict (X ω)) = Measure.pi (fun i : S => (q i).toMeasure) := by
  classical
  apply Measure.ext_of_singleton
  intro b
  have hm : Measurable (fun ω => S.restrict (X ω)) :=
    measurable_pi_lambda _ fun i => hX i
  rw [Measure.map_apply hm (measurableSet_singleton b)]
  let sets : ι → Set ℕ := fun i => if hi : i ∈ S then {b ⟨i,hi⟩} else univ
  have hsets (i : ι) (hi : i ∈ S) : sets i = {b ⟨i,hi⟩} := by simp [sets,hi]
  have hmeas (i : ι) (_ : i ∈ S) : MeasurableSet (sets i) := MeasurableSet.of_discrete
  have hind := hI.measure_inter_preimage_eq_mul S hmeas
  have he : (fun ω => S.restrict (X ω)) ⁻¹' {b} =
      ⋂ i ∈ S, (fun ω => X ω i) ⁻¹' sets i := by
    ext ω
    simp only [mem_preimage,mem_singleton_iff,mem_iInter]
    constructor
    · intro h i hi
      rw [hsets i hi]
      exact congrFun h ⟨i,hi⟩
    · intro h
      funext i
      have hi := h i i.property
      simpa [hsets] using hi
  rw [he,hind,← Set.univ_pi_singleton b,Measure.pi_pi,← Finset.prod_coe_sort S]
  apply Finset.prod_congr rfl
  intro i hi
  rw [hsets i i.property,← hL i,Measure.map_apply (hX i) (measurableSet_singleton _)]

/-- Equality of independent coordinate laws determines the complete array law,
via uniqueness of its native finite-dimensional projective distributions. -/
theorem iid_nat_array_law_unique (q : ι → PMF ℕ) (μ : Measure Ω) (ν : Measure Ω')
    (X : Ω → ι → ℕ) (Y : Ω' → ι → ℕ)
    (hX : ∀ i, Measurable (fun ω => X ω i)) (hY : ∀ i, Measurable (fun ω => Y ω i))
    (hIX : iIndepFun (fun _ : ι => inferInstance) (fun i ω => X ω i) μ)
    (hIY : iIndepFun (fun _ : ι => inferInstance) (fun i ω => Y ω i) ν)
    (hLX : ∀ i, μ.map (fun ω => X ω i) = (q i).toMeasure)
    (hLY : ∀ i, ν.map (fun ω => Y ω i) = (q i).toMeasure) :
    μ.map X = ν.map Y := by
  have hx : IsProjectiveLimit (μ.map X) (fun S => Measure.pi (fun i : S => (q i).toMeasure)) := by
    intro S
    have hr : Measurable (S.restrict : (ι → ℕ) → (S → ℕ)) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply (i : ι)
    rw [Measure.map_map hr (measurable_pi_lambda _ hX)]
    exact iid_nat_array_finite_law q μ X hX hIX hLX S
  have hy : IsProjectiveLimit (ν.map Y) (fun S => Measure.pi (fun i : S => (q i).toMeasure)) := by
    intro S
    have hr : Measurable (S.restrict : (ι → ℕ) → (S → ℕ)) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply (i : ι)
    rw [Measure.map_map hr (measurable_pi_lambda _ hY)]
    exact iid_nat_array_finite_law q ν Y hY hIY hLY S
  exact hx.unique hy

/-- Every fixed measurable construction has the same law under iid arrays with
the same offspring marginals. This includes the whole tree and its total size. -/
theorem iid_nat_array_observable_law_unique {E : Type*} [MeasurableSpace E]
    (q : ι → PMF ℕ) (μ : Measure Ω) (ν : Measure Ω')
    (X : Ω → ι → ℕ) (Y : Ω' → ι → ℕ)
    (hX : ∀ i, Measurable (fun ω => X ω i)) (hY : ∀ i, Measurable (fun ω => Y ω i))
    (hIX : iIndepFun (fun _ : ι => inferInstance) (fun i ω => X ω i) μ)
    (hIY : iIndepFun (fun _ : ι => inferInstance) (fun i ω => Y ω i) ν)
    (hLX : ∀ i, μ.map (fun ω => X ω i) = (q i).toMeasure)
    (hLY : ∀ i, ν.map (fun ω => Y ω i) = (q i).toMeasure)
    (F : (ι → ℕ) → E) (hF : Measurable F) :
    μ.map (fun ω => F (X ω)) = ν.map (fun ω => F (Y ω)) := by
  change μ.map (F ∘ X) = ν.map (F ∘ Y)
  rw [← Measure.map_map hF (measurable_pi_lambda _ hX),
    ← Measure.map_map hF (measurable_pi_lambda _ hY),
    iid_nat_array_law_unique q μ ν X Y hX hY hIX hIY hLX hLY]

/-- In the fixed rooted-tree construction, the offspring law determines both
the full random tree and its actual (possibly infinite) total-size law. -/
theorem iid_gw_tree_law_unique (q : PMF ℕ) (μ : Measure Ω) (ν : Measure Ω')
    (X : Ω → GWOffspringArray) (Y : Ω' → GWOffspringArray)
    (hX : ∀ w, Measurable (fun ω => X ω w)) (hY : ∀ w, Measurable (fun ω => Y ω w))
    (hIX : iIndepFun (fun _ : List ℕ => inferInstance) (fun w ω => X ω w) μ)
    (hIY : iIndepFun (fun _ : List ℕ => inferInstance) (fun w ω => Y ω w) ν)
    (hLX : ∀ w, μ.map (fun ω => X ω w) = q.toMeasure)
    (hLY : ∀ w, ν.map (fun ω => Y ω w) = q.toMeasure) :
    μ.map (fun ω => gwTree (X ω)) = ν.map (fun ω => gwTree (Y ω)) ∧
    μ.map (fun ω => gwTotalSize (X ω)) = ν.map (fun ω => gwTotalSize (Y ω)) := by
  constructor
  · exact iid_nat_array_observable_law_unique (fun _ => q) μ ν X Y hX hY hIX hIY hLX hLY
      gwTree gw_tree_measurable
  · exact iid_nat_array_observable_law_unique (fun _ => q) μ ν X Y hX hY hIX hIY hLX hLY
      gwTotalSize gw_total_size_measurable

end
end Sigma
