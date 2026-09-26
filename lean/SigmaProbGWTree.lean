import SigmaRealTreesOffspring
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Constructions.Pi

namespace Sigma
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

/-- Offspring counts indexed by finite words; child indices start at zero. -/
abbrev GWOffspringArray := List ℕ → ℕ

instance gwWordMeasurableSpace : MeasurableSpace (List ℕ) := ⊤
instance gwWordMeasurableSingleton : MeasurableSingletonClass (List ℕ) :=
  ⟨fun _ => MeasurableSet.of_discrete⟩

def gwChildArray (i : ℕ) (a : GWOffspringArray) : GWOffspringArray :=
  fun w => a (i :: w)

/-- A word is retained precisely when every edge is allowed by its parent's count. -/
def gwVertex (a : GWOffspringArray) : List ℕ → Prop
  | [] => True
  | i :: w => i < a [] ∧ gwVertex (gwChildArray i a) w

/-- The actual set of retained vertices in the fixed ordered rooted construction. -/
def gwTree (a : GWOffspringArray) : Set (List ℕ) := {w | gwVertex a w}

/-- All vertices strictly below the specified depth. -/
def gwVerticesBelow (a : GWOffspringArray) : ℕ → Finset (List ℕ)
  | 0 => ∅
  | d + 1 => insert [] ((Finset.range (a [])).biUnion fun i =>
      (gwVerticesBelow (gwChildArray i a) d).image (List.cons i))

/-- Number of vertices strictly below depth d, computed from actual offspring. -/
def gwSizeBelow (a : GWOffspringArray) : ℕ → ℕ
  | 0 => 0
  | d + 1 => 1 + ∑ i ∈ Finset.range (a []), gwSizeBelow (gwChildArray i a) d

theorem gw_vertices_below_mem (a : GWOffspringArray) (d : ℕ) (w : List ℕ) :
    w ∈ gwVerticesBelow a d ↔ gwVertex a w ∧ w.length < d := by
  induction d generalizing a w with
  | zero => simp [gwVerticesBelow]
  | succ d ih =>
    cases w with
    | nil => simp [gwVerticesBelow, gwVertex]
    | cons i w =>
      simp only [gwVerticesBelow, Finset.mem_insert, List.cons_ne_nil, false_or,
        Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, List.cons.injEq]
      simp only [exists_eq_right_right, ih, gwVertex, List.length_cons]
      simp only [Nat.succ_lt_succ_iff]
      aesop

theorem gw_vertices_below_card (a : GWOffspringArray) (d : ℕ) :
    (gwVerticesBelow a d).card = gwSizeBelow a d := by
  induction d generalizing a with
  | zero => rfl
  | succ d ih =>
    have hn : [] ∉ (Finset.range (a [])).biUnion (fun i =>
        (gwVerticesBelow (gwChildArray i a) d).image (List.cons i)) := by simp
    have hd : ∀ i ∈ Finset.range (a []), ∀ j ∈ Finset.range (a []), i ≠ j →
        Disjoint ((gwVerticesBelow (gwChildArray i a) d).image (List.cons i))
          ((gwVerticesBelow (gwChildArray j a) d).image (List.cons j)) := by
      intro i hi j hj hij
      apply Finset.disjoint_left.mpr
      intro w hw hw'
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hw'
      exact hij (List.cons.inj he).1.symm
    simp only [gwVerticesBelow, Finset.card_insert_of_not_mem hn,
      Finset.card_biUnion hd, Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2), ih,
      gwSizeBelow]
    omega

theorem gw_vertices_below_mono (a : GWOffspringArray) : Monotone (gwVerticesBelow a) := by
  intro d e h w hw
  rw [gw_vertices_below_mem] at hw ⊢
  exact ⟨hw.1, lt_of_lt_of_le hw.2 h⟩

theorem gw_size_below_mono (a : GWOffspringArray) : Monotone (gwSizeBelow a) := by
  intro d e h
  rw [← gw_vertices_below_card, ← gw_vertices_below_card]
  exact Finset.card_le_card (gw_vertices_below_mono a h)

theorem gw_tree_eq_union (a : GWOffspringArray) :
    gwTree a = ⋃ d : ℕ, (gwVerticesBelow a d : Set (List ℕ)) := by
  ext w
  simp only [gwTree, mem_setOf_eq, mem_iUnion, Finset.mem_coe, gw_vertices_below_mem]
  exact ⟨fun h => ⟨w.length + 1, h, Nat.lt_succ_self _⟩, fun ⟨d, h, _⟩ => h⟩

/-- Extended total size is the actual counting measure of the retained word set. -/
def gwTotalSize (a : GWOffspringArray) : ℝ≥0∞ := Measure.count (gwTree a)

theorem gw_total_size_eq_iSup (a : GWOffspringArray) :
    gwTotalSize a = ⨆ d : ℕ, (gwSizeBelow a d : ℝ≥0∞) := by
  rw [gwTotalSize, gw_tree_eq_union, Directed.measure_iUnion]
  · simp only [Measure.count_apply_finset, gw_vertices_below_card]
  · exact fun d e => ⟨max d e, gw_vertices_below_mono a (le_max_left _ _),
      gw_vertices_below_mono a (le_max_right _ _)⟩

theorem gw_total_size_finite_iff (a : GWOffspringArray) :
    gwTotalSize a < ∞ ↔ (gwTree a).Finite := Measure.count_apply_lt_top

theorem gw_child_array_measurable (i : ℕ) : Measurable (gwChildArray i) :=
  measurable_pi_lambda _ fun w => measurable_pi_apply (i :: w)

theorem gw_vertex_measurable (w : List ℕ) :
    MeasurableSet {a : GWOffspringArray | gwVertex a w} := by
  induction w with
  | nil => simp [gwVertex]
  | cons i w ih =>
    exact (measurableSet_lt measurable_const (measurable_pi_apply [])).inter
      (ih.preimage (gw_child_array_measurable i))

theorem gw_size_below_measurable (d : ℕ) : Measurable (fun a => gwSizeBelow a d) := by
  induction d with
  | zero => exact measurable_const
  | succ d ih =>
    have hm : Measurable (fun x : GWOffspringArray × ℕ =>
        1 + ∑ i ∈ Finset.range x.2, gwSizeBelow (gwChildArray i x.1) d) := by
      apply measurable_from_prod_countable
      intro n
      change Measurable (fun a => 1 + ∑ i ∈ Finset.range n, gwSizeBelow (gwChildArray i a) d)
      exact measurable_const.add (Finset.measurable_sum _ fun i _ =>
        show Measurable (fun a => gwSizeBelow (gwChildArray i a) d) from
          ih.comp (gw_child_array_measurable i))
    exact hm.comp (measurable_id.prod_mk (measurable_pi_apply []))

theorem gw_total_size_measurable : Measurable gwTotalSize := by
  change Measurable (fun a => gwTotalSize a)
  simp_rw [gw_total_size_eq_iSup]
  exact Measurable.iSup fun d => (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp (gw_size_below_measurable d)

theorem gw_tree_measurable : Measurable gwTree :=
  measurable_set_iff.mpr fun w => measurableSet_setOf.mp (gw_vertex_measurable w)

/-- Extinction by depth d means there are no retained vertices at depth d or later. -/
def gwExtinctAt (d : ℕ) (a : GWOffspringArray) : Prop :=
  ∀ w, gwVertex a w → w.length < d

theorem gw_extinct_zero (a : GWOffspringArray) : ¬ gwExtinctAt 0 a := by
  intro h
  have := h [] trivial
  simp at this

theorem gw_extinct_succ (d : ℕ) (a : GWOffspringArray) :
    gwExtinctAt (d + 1) a ↔ ∀ i < a [], gwExtinctAt d (gwChildArray i a) := by
  constructor
  · intro h i hi w hw
    exact Nat.lt_of_succ_lt_succ (h (i :: w) ⟨hi, hw⟩)
  · intro h w hw
    cases w with
    | nil => exact Nat.zero_lt_succ _
    | cons i w => exact Nat.succ_lt_succ (h i hw.1 w hw.2)

theorem gw_extinct_mono (a : GWOffspringArray) {d e : ℕ} (hde : d ≤ e)
    (h : gwExtinctAt d a) : gwExtinctAt e a :=
  fun w hw => lt_of_lt_of_le (h w hw) hde

theorem gw_extinct_measurable (d : ℕ) :
    MeasurableSet {a : GWOffspringArray | gwExtinctAt d a} := by
  simp only [gwExtinctAt, setOf_forall]
  apply MeasurableSet.iInter
  intro w
  by_cases h : w.length < d
  · simp [h]
  · convert (gw_vertex_measurable w).compl using 1
    ext a
    simp only [mem_setOf_eq, mem_compl_iff, h, imp_false]

theorem gw_extinct_iff_tree_eq (a : GWOffspringArray) (d : ℕ) :
    gwExtinctAt d a ↔ gwTree a = (gwVerticesBelow a d : Set (List ℕ)) := by
  constructor
  · intro h
    ext w
    exact ⟨fun hw => (gw_vertices_below_mem a d w).mpr ⟨hw, h w hw⟩,
      fun hw => ((gw_vertices_below_mem a d w).mp hw).1⟩
  · intro h w hw
    have : w ∈ (gwVerticesBelow a d : Set (List ℕ)) := by rw [← h]; exact hw
    exact ((gw_vertices_below_mem a d w).mp this).2

theorem gw_tree_finite_iff_extinct (a : GWOffspringArray) :
    (gwTree a).Finite ↔ ∃ d, gwExtinctAt d a := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (h.image List.length).bddAbove
    refine ⟨n + 1, fun w hw => Nat.lt_succ_of_le ?_⟩
    exact hn (mem_image_of_mem List.length hw)
  · rintro ⟨d, hd⟩
    rw [(gw_extinct_iff_tree_eq a d).mp hd]
    exact Finset.finite_toSet _

theorem gw_total_size_finite_iff_extinct (a : GWOffspringArray) :
    gwTotalSize a < ∞ ↔ ∃ d, gwExtinctAt d a :=
  (gw_total_size_finite_iff a).trans (gw_tree_finite_iff_extinct a)

theorem gw_total_size_of_extinct {a : GWOffspringArray} {d : ℕ}
    (h : gwExtinctAt d a) : gwTotalSize a = (gwSizeBelow a d : ℝ≥0∞) := by
  rw [gwTotalSize, (gw_extinct_iff_tree_eq a d).mp h,
    Measure.count_apply_finset, gw_vertices_below_card]

/-- Root decomposition of the actual retained-word set. -/
theorem gw_tree_root_decomposition (a : GWOffspringArray) :
    gwTree a = {[]} ∪ ⋃ i ∈ Finset.range (a []), List.cons i '' gwTree (gwChildArray i a) := by
  ext w
  cases w with
  | nil => simp [gwTree, gwVertex]
  | cons i w =>
    simp only [gwTree, gwVertex, mem_setOf_eq, mem_union, mem_singleton_iff,
      List.cons_ne_nil, false_or, mem_iUnion, Finset.mem_range, mem_image, List.cons.injEq]
    aesop

theorem gw_total_size_root_decomposition (a : GWOffspringArray) :
    gwTotalSize a = 1 + ∑ i ∈ Finset.range (a []), gwTotalSize (gwChildArray i a) := by
  have hd : Disjoint ({[]} : Set (List ℕ))
      (⋃ i ∈ Finset.range (a []), List.cons i '' gwTree (gwChildArray i a)) := by
    simp [Set.disjoint_left]
  have hi : (↑(Finset.range (a [])) : Set ℕ).PairwiseDisjoint
      (fun i => List.cons i '' gwTree (gwChildArray i a)) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    rintro w ⟨v, hv, rfl⟩ ⟨u, hu, he⟩
    exact hij (List.cons.inj he).1.symm
  rw [gwTotalSize, gw_tree_root_decomposition, measure_union hd (by measurability),
    Measure.count_singleton, measure_biUnion_finset hi (fun _ _ => .of_discrete)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact Measure.count_injective_image (fun _ _ h => (List.cons.inj h).2) _

end
end Sigma
