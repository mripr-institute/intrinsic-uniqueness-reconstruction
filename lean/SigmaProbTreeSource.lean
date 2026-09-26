import SigmaProbPoissonClock

set_option synthInstance.maxSize 512

open MeasureTheory Measure Set TopologicalSpace
open scoped ENNReal

namespace Sigma
noncomputable section

/-- Independent randomness at all potential vertices of a rooted tree.
Children are indexed by natural numbers, starting at zero. -/
abbrev TreeSource := List ℕ → AddCircle (1 : ℝ)

def treeSourceProbability : Measure TreeSource := addHaarMeasure ⊤

instance treeSourceProbability_probability : IsProbabilityMeasure treeSourceProbability where
  measure_univ := by
    change addHaarMeasure (⊤ : PositiveCompacts TreeSource) univ = 1
    simpa only [PositiveCompacts.coe_top] using
      (addHaarMeasure_self (K₀ := (⊤ : PositiveCompacts TreeSource)))

instance treeSourceProbability_haar : IsAddHaarMeasure treeSourceProbability :=
  inferInstanceAs (IsAddHaarMeasure (addHaarMeasure (⊤ : PositiveCompacts TreeSource)))

def treeRootSource (ω : TreeSource) : AddCircle (1 : ℝ) := ω []

def treeChildSource (i : ℕ) (ω : TreeSource) : TreeSource := fun w => ω (i :: w)

theorem treeRootSource_continuous : Continuous treeRootSource := continuous_apply []

theorem treeChildSource_continuous (i : ℕ) : Continuous (treeChildSource i) :=
  continuous_pi fun w => continuous_apply (i :: w)

theorem treeRootSource_measurable : Measurable treeRootSource :=
  treeRootSource_continuous.measurable

theorem treeChildSource_measurable (i : ℕ) : Measurable (treeChildSource i) :=
  (treeChildSource_continuous i).measurable

theorem treeRootSource_map : treeSourceProbability.map treeRootSource =
    (volume : Measure (AddCircle (1 : ℝ))) := by
  let f : TreeSource →+ AddCircle (1 : ℝ) :=
    { toFun := treeRootSource, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hs : Function.Surjective f := fun x => ⟨fun _ => x, rfl⟩
  letI : IsAddHaarMeasure (treeSourceProbability.map f) :=
    isAddHaarMeasure_map_of_isFiniteMeasure treeSourceProbability f
      treeRootSource_continuous hs
  letI : IsProbabilityMeasure (treeSourceProbability.map f) :=
    isProbabilityMeasure_map treeRootSource_measurable.aemeasurable
  exact isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem treeChildSource_map (i : ℕ) :
    treeSourceProbability.map (treeChildSource i) = treeSourceProbability := by
  let f : TreeSource →+ TreeSource :=
    { toFun := treeChildSource i, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hs : Function.Surjective f := by
    intro x
    refine ⟨fun w => match w with | [] => 0 | _ :: v => x v, ?_⟩
    rfl
  letI : IsAddHaarMeasure (treeSourceProbability.map f) :=
    isAddHaarMeasure_map_of_isFiniteMeasure treeSourceProbability f
      (treeChildSource_continuous i) hs
  letI : IsProbabilityMeasure (treeSourceProbability.map f) :=
    isProbabilityMeasure_map (treeChildSource_measurable i).aemeasurable
  exact isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem treeCoordinate_map (w : List ℕ) :
    treeSourceProbability.map (fun ω => ω w) =
      (volume : Measure (AddCircle (1 : ℝ))) := by
  let f : TreeSource →+ AddCircle (1 : ℝ) :=
    { toFun := fun ω => ω w, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hc : Continuous f := continuous_apply w
  have hs : Function.Surjective f := fun x => ⟨fun _ => x, rfl⟩
  letI : IsAddHaarMeasure (treeSourceProbability.map f) :=
    isAddHaarMeasure_map_of_isFiniteMeasure treeSourceProbability f hc hs
  letI : IsProbabilityMeasure (treeSourceProbability.map f) :=
    isProbabilityMeasure_map hc.measurable.aemeasurable
  exact isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

def treeCoordinateProjection (S : Finset (List ℕ)) :
    TreeSource →+ (S → AddCircle (1 : ℝ)) where
  toFun ω w := ω w
  map_zero' := rfl
  map_add' _ _ := rfl

theorem treeCoordinateProjection_continuous (S : Finset (List ℕ)) :
    Continuous (treeCoordinateProjection S) := continuous_pi fun w => continuous_apply w.val

theorem treeCoordinateProjection_map (S : Finset (List ℕ)) :
    treeSourceProbability.map (treeCoordinateProjection S) =
      Measure.pi (fun _ : S => (volume : Measure (AddCircle (1 : ℝ)))) := by
  classical
  have hs : Function.Surjective (treeCoordinateProjection S) := by
    intro x
    refine ⟨fun w => if h : w ∈ S then x ⟨w,h⟩ else 0, ?_⟩
    ext w
    simp [treeCoordinateProjection, w.property]
  letI : IsAddHaarMeasure (treeSourceProbability.map (treeCoordinateProjection S)) :=
    isAddHaarMeasure_map_of_isFiniteMeasure treeSourceProbability
      (treeCoordinateProjection S) (treeCoordinateProjection_continuous S) hs
  letI : IsProbabilityMeasure (treeSourceProbability.map (treeCoordinateProjection S)) :=
    isProbabilityMeasure_map (treeCoordinateProjection_continuous S).measurable.aemeasurable
  exact isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem treeCoordinates_independent :
    ProbabilityTheory.iIndepFun (fun _ : List ℕ => inferInstance)
      (fun w (ω : TreeSource) => ω w) treeSourceProbability := by
  rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hs
  have hm : MeasurableSet (Set.univ.pi (fun i : S => sets i)) :=
    MeasurableSet.univ_pi fun i => hs i i.property
  have he : (treeCoordinateProjection S) ⁻¹' (Set.univ.pi fun i : S => sets i) =
      ⋂ i ∈ S, (fun ω : TreeSource => ω i) ⁻¹' sets i := by
    ext ω
    simp [treeCoordinateProjection]
  rw [← he, ← Measure.map_apply (treeCoordinateProjection_continuous S).measurable hm,
    treeCoordinateProjection_map, Measure.pi_pi, ← Finset.prod_coe_sort S]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← treeCoordinate_map i,
    Measure.map_apply (measurable_pi_apply (i : List ℕ)) (hs i i.property)]

def treeChildrenProjection (S : Finset ℕ) : TreeSource →+ (S → TreeSource) where
  toFun ω i := treeChildSource i ω
  map_zero' := rfl
  map_add' _ _ := rfl

theorem treeChildrenProjection_continuous (S : Finset ℕ) :
    Continuous (treeChildrenProjection S) :=
  continuous_pi fun i => treeChildSource_continuous i

theorem treeChildrenProjection_surjective (S : Finset ℕ) :
    Function.Surjective (treeChildrenProjection S) := by
  classical
  intro x
  refine ⟨fun w => match w with
    | [] => 0
    | i :: v => if h : i ∈ S then x ⟨i,h⟩ v else 0, ?_⟩
  ext i w
  simp [treeChildrenProjection, treeChildSource, i.property]

theorem treeChildrenProjection_map (S : Finset ℕ) :
    treeSourceProbability.map (treeChildrenProjection S) =
      Measure.pi (fun _ : S => treeSourceProbability) := by
  letI : IsAddHaarMeasure (treeSourceProbability.map (treeChildrenProjection S)) :=
    isAddHaarMeasure_map_of_isFiniteMeasure treeSourceProbability
      (treeChildrenProjection S) (treeChildrenProjection_continuous S)
      (treeChildrenProjection_surjective S)
  letI : IsProbabilityMeasure (treeSourceProbability.map (treeChildrenProjection S)) :=
    isProbabilityMeasure_map (treeChildrenProjection_continuous S).measurable.aemeasurable
  exact isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- Independence of the entire descendant sources, not just individual
coordinates or a predetermined collection of tree statistics. -/
theorem treeChildSources_independent :
    ProbabilityTheory.iIndepFun (fun _ : ℕ => inferInstance)
      treeChildSource treeSourceProbability := by
  rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hs
  have hm : MeasurableSet (Set.univ.pi (fun i : S => sets i)) :=
    MeasurableSet.univ_pi fun i => hs i i.property
  have he : (treeChildrenProjection S) ⁻¹' (Set.univ.pi fun i : S => sets i) =
      ⋂ i ∈ S, treeChildSource i ⁻¹' sets i := by
    ext ω
    simp [treeChildrenProjection]
  rw [← he, ← Measure.map_apply (treeChildrenProjection_continuous S).measurable hm,
    treeChildrenProjection_map, Measure.pi_pi]
  rw [← Finset.prod_coe_sort S]
  apply Finset.prod_congr rfl
  intro i hi
  nth_rw 1 [← treeChildSource_map i]
  rw [Measure.map_apply (treeChildSource_measurable i) (hs i i.property)]

def treeRootChildrenProjection (S : Finset ℕ) :
    TreeSource →+ (AddCircle (1 : ℝ) × (S → TreeSource)) where
  toFun ω := (treeRootSource ω, treeChildrenProjection S ω)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem treeRootChildrenProjection_continuous (S : Finset ℕ) :
    Continuous (treeRootChildrenProjection S) :=
  treeRootSource_continuous.prod_mk (treeChildrenProjection_continuous S)

theorem treeRootChildrenProjection_surjective (S : Finset ℕ) :
    Function.Surjective (treeRootChildrenProjection S) := by
  classical
  intro x
  refine ⟨fun w => match w with
    | [] => x.1
    | i :: v => if h : i ∈ S then x.2 ⟨i,h⟩ v else 0, ?_⟩
  apply Prod.ext
  · rfl
  · ext i w
    simp [treeRootChildrenProjection, treeChildrenProjection, treeChildSource, i.property]

theorem treeRootChildrenProjection_map (S : Finset ℕ) :
    treeSourceProbability.map (treeRootChildrenProjection S) =
      (volume : Measure (AddCircle (1 : ℝ))).prod
        (Measure.pi (fun _ : S => treeSourceProbability)) := by
  letI : IsAddHaarMeasure (treeSourceProbability.map (treeRootChildrenProjection S)) :=
    isAddHaarMeasure_map_of_isFiniteMeasure treeSourceProbability
      (treeRootChildrenProjection S) (treeRootChildrenProjection_continuous S)
      (treeRootChildrenProjection_surjective S)
  letI : IsProbabilityMeasure (treeSourceProbability.map (treeRootChildrenProjection S)) :=
    isProbabilityMeasure_map (treeRootChildrenProjection_continuous S).measurable.aemeasurable
  exact isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- Root randomness is independent of any finite tuple of whole descendant
sources. Thus measurable functions of those sources may be conditioned on the root. -/
theorem treeRootSource_independent_children (S : Finset ℕ) :
    ProbabilityTheory.IndepFun treeRootSource (treeChildrenProjection S)
      treeSourceProbability := by
  rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    treeRootSource_measurable.aemeasurable
    (treeChildrenProjection_continuous S).measurable.aemeasurable]
  rw [treeRootSource_map, treeChildrenProjection_map]
  exact treeRootChildrenProjection_map S

end
end Sigma
