import SigmaOpSesquilinearForm
import Mathlib.Analysis.BoundedVariation
import Mathlib.Topology.Compactness.Lindelof

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

/-- On a sufficiently short interior interval, the AC condition bounds the
variation of every finite monotone partition. -/
theorem PositiveRayLocallyAbsolutelyContinuous.small_interval_variation
    {F : ℝ → ℂ} (hF : PositiveRayLocallyAbsolutelyContinuous F)
    {l r : ℝ} (hl : 0 < l) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b : ℝ, l ≤ a → b ≤ r → b-a < d →
      eVariationOn F (Icc a b) ≤ 1 := by
  obtain ⟨δ,hδ,hd⟩ := hF l r hl 1 one_ne_zero
  obtain ⟨d,_,hdpos,hdd⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδ
  have hdp : 0 < d := ENNReal.ofReal_pos.mp hdpos
  refine ⟨d,hdp,fun a b hla hbr hab => ?_⟩
  apply iSup_le
  rintro ⟨n,u,hu,hus⟩
  have hdj : Set.univ.PairwiseDisjoint (fun i : Fin n => Ioc (u i) (u (i+1))) := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro t hti htj
    rcases lt_or_gt_of_ne hij with h | h
    · have hm := hu (show (i : ℕ)+1 ≤ j from h)
      exact (not_lt_of_ge (hti.2.trans hm)) htj.1
    · have hm := hu (show (j : ℕ)+1 ≤ i from h)
      exact (not_lt_of_ge (htj.2.trans hm)) hti.1
  have hs : ∑ i : Fin n, ENNReal.ofReal (u (i+1)-u i) < δ := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sub_nonneg.mpr (hu (Nat.le_succ _))),
      Fin.sum_univ_eq_sum_range (fun i => u (i+1)-u i), Finset.sum_range_sub]
    apply lt_trans _ hdd
    apply (ENNReal.ofReal_lt_ofReal_iff hdp).mpr
    have h0 := (hus 0).1
    have hn := (hus n).2
    linarith
  have hb := hd n (fun i => u i) (fun i => u (i+1))
    (fun i => ⟨hla.trans (hus i).1, hu (Nat.le_succ _), (hus (i+1)).2.trans hbr⟩) hdj hs
  rw [Fin.sum_univ_eq_sum_range (fun i => (‖F (u (i+1))-F (u i)‖₊ : ℝ≥0∞))] at hb
  simpa only [edist_eq_coe_nnnorm_sub] using hb.le

theorem PositiveRayLocallyAbsolutelyContinuous.local_boundedVariation
    {F : ℝ → ℂ} (hF : PositiveRayLocallyAbsolutelyContinuous F)
    {x : ℝ} (hx : 0 < x) :
    ∃ a b : ℝ, 0 < a ∧ a < x ∧ x < b ∧ BoundedVariationOn F (Icc a b) := by
  obtain ⟨d,hd,hvar⟩ := hF.small_interval_variation (l := x/2) (r := x+1) (by positivity)
  let e := min (x/4) (min (1/2) (d/4))
  have he : 0 < e := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hex : e ≤ x/4 := min_le_left _ _
  have he1 : e ≤ 1/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hed : e ≤ d/4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨x-e,x+e,by linarith,by linarith,by linarith,?_⟩
  exact ne_of_lt ((hvar (x-e) (x+e) (by linarith) (by linarith) (by linarith)).trans_lt
    (by simp : (1 : ℝ≥0∞) < ∞))

/-- Almost-everywhere classical differentiability follows from the literal
AC condition, via local bounded variation and a countable interior cover. -/
theorem PositiveRayLocallyAbsolutelyContinuous.ae_differentiableAt
    {F : ℝ → ℂ} (hF : PositiveRayLocallyAbsolutelyContinuous F) :
    ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), DifferentiableAt ℝ F t := by
  choose a b ha hax hxb hvar using fun x : Ioi (0:ℝ) => hF.local_boundedVariation x.property
  have hcover : Ioi (0:ℝ) ⊆ ⋃ x : Ioi (0:ℝ), Ioo (a x) (b x) := by
    intro t ht
    exact mem_iUnion.mpr ⟨⟨t,ht⟩,hax ⟨t,ht⟩,hxb ⟨t,ht⟩⟩
  obtain ⟨c,hc,hccover⟩ := (HereditarilyLindelof_LindelofSets (Ioi (0:ℝ))).elim_countable_subcover
    (fun x : Ioi (0:ℝ) => Ioo (a x) (b x)) (fun _ => isOpen_Ioo) hcover
  have hlocal (x : Ioi (0:ℝ)) : ∀ᵐ t ∂volume,
      t ∈ Ioo (a x) (b x) → DifferentiableAt ℝ F t := by
    have hd := ((hvar x).mono Ioo_subset_Icc_self).locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem
    filter_upwards [hd] with t ht htm
    exact (ht htm).differentiableAt (isOpen_Ioo.mem_nhds htm)
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [(ae_ball_iff hc).mpr (fun x _ => hlocal x)] with t ht htp
  obtain ⟨x,hxc,hxt⟩ := mem_iUnion₂.mp (hccover htp)
  exact ht x hxc hxt

end
end Sigma
