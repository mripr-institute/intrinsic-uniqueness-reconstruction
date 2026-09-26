import Mathlib.Analysis.BoxIntegral.Partition.SubboxInduction
import Mathlib.Analysis.BoxIntegral.Partition.Additive
import Mathlib.Analysis.Complex.Basic

namespace Sigma
noncomputable section
open Set Filter BoxIntegral
open scoped Topology

/-- Endpoint increments are additive over genuine one-dimensional partitions,
for an arbitrary function, with no regularity assumption. -/
def realIntervalIncrement {E : Type*} [AddCommGroup E] (F : ℝ → E) :
    Fin 1 →ᵇᵃ[⊤] E :=
  BoxAdditiveMap.ofMapSplitAdd (fun J => F (J.upper 0)-F (J.lower 0)) ⊤ (by
    intro J _ i x hx
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [Box.splitLower_def hx, Box.splitUpper_def hx, Function.update_same,
      ← WithBot.some_eq_coe, Option.elim']
    abel)

/-- A finite tagged real-interval partition subordinate to any positive gauge.
Its telescoping identity is valid for every complex function. -/
theorem exists_real_tagged_partition {a b : ℝ} (hab : a < b)
    (r : ℝ → Ioi (0:ℝ)) :
    ∃ (n : ℕ) (u v ξ : Fin n → ℝ),
      (∀ i, a ≤ u i ∧ u i < v i ∧ v i ≤ b ∧ ξ i ∈ Icc (u i) (v i)) ∧
      univ.PairwiseDisjoint (fun i => Ioc (u i) (v i)) ∧
      (∀ i, Icc (u i) (v i) ⊆ Metric.closedBall (ξ i) (r (ξ i))) ∧
      (∑ i, (v i-u i)) = b-a ∧
      (∀ F : ℝ → ℂ, (∑ i, (F (v i)-F (u i))) = F b-F a) := by
  classical
  let I : Box (Fin 1) := ⟨fun _ => a,fun _ => b,fun _ => hab⟩
  obtain ⟨π,hπ,hH,hr,_,_⟩ := I.exists_taggedPartition_isHenstock_isSubordinate_homothetic
    (fun x => r (x 0))
  let e := (Fintype.equivFin ↑π.boxes).symm
  let J : Fin (Fintype.card ↑π.boxes) → Box (Fin 1) := fun i => (e i).val
  have hJ (i) : J i ∈ π := (e i).property
  have hsum {E : Type} [AddCommMonoid E] (f : Box (Fin 1) → E) :
      (∑ i, f (J i)) = ∑ K ∈ π.boxes, f K := by
    calc
      _ = ∑ k : ↑π.boxes, f k.val := e.sum_comp (fun k => f k.val)
      _ = _ := Finset.sum_attach π.boxes f
  refine ⟨Fintype.card ↑π.boxes,fun i => (J i).lower 0,
    fun i => (J i).upper 0,fun i => π.tag (J i) 0,?_,?_,?_,?_,?_⟩
  · intro i
    exact ⟨π.toPrepartition.lower_le_lower (hJ i) 0, (J i).lower_lt_upper 0,
      π.toPrepartition.upper_le_upper (hJ i) 0, (hH _ (hJ i)).1 0, (hH _ (hJ i)).2 0⟩
  · intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro t hti htj
    have hne : J i ≠ J j := fun he => hij (e.injective (Subtype.ext he))
    have hi : (fun _ : Fin 1 => t) ∈ (J i : Set (Fin 1 → ℝ)) := by
      intro k
      have hk : k = 0 := Subsingleton.elim _ _
      simpa only [hk] using hti
    have hj : (fun _ : Fin 1 => t) ∈ (J j : Set (Fin 1 → ℝ)) := by
      intro k
      have hk : k = 0 := Subsingleton.elim _ _
      simpa only [hk] using htj
    exact Set.disjoint_left.mp
      (π.toPrepartition.disjoint_coe_of_mem (hJ i) (hJ j) hne) hi hj
  · intro i t ht
    have hmem : (fun _ : Fin 1 => t) ∈ Box.Icc (J i) := by
      constructor
      · intro k
        simpa only [show k = 0 from Subsingleton.elim _ _] using ht.1
      · intro k
        simpa only [show k = 0 from Subsingleton.elim _ _] using ht.2
    have hh := hr (J i) (hJ i) hmem
    exact (dist_le_pi_dist (fun _ : Fin 1 => t) (π.tag (J i)) 0).trans hh
  · rw [hsum (fun K => K.upper 0-K.lower 0)]
    exact (realIntervalIncrement (fun t : ℝ => t)).sum_partition_boxes le_top hπ
  · intro F
    rw [hsum (fun K => F (K.upper 0)-F (K.lower 0))]
    exact (realIntervalIncrement F).sum_partition_boxes le_top hπ

end
end Sigma
