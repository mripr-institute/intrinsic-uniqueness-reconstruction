import SigmaOpLocalACDifferentiability
import SigmaRealTaggedPartition

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

private theorem ac_control_subfamily {F : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    {ε δ : ℝ≥0∞}
    (hctl : ∀ (m : ℕ) (u v : Fin m → ℝ),
      (∀ i, a ≤ u i ∧ u i ≤ v i ∧ v i ≤ b) →
      univ.PairwiseDisjoint (fun i => Ioc (u i) (v i)) →
      (∑ i, ENNReal.ofReal (v i-u i)) < δ →
      (∑ i, (‖F (v i)-F (u i)‖₊ : ℝ≥0∞)) < ε)
    {n : ℕ} (u v : Fin n → ℝ) (s : Finset (Fin n))
    (huv : ∀ i, a ≤ u i ∧ u i ≤ v i ∧ v i ≤ b)
    (hdis : univ.PairwiseDisjoint (fun i => Ioc (u i) (v i)))
    (hlen : (∑ i ∈ s, ENNReal.ofReal (v i-u i)) < δ) :
    (∑ i ∈ s, (‖F (v i)-F (u i)‖₊ : ℝ≥0∞)) < ε := by
  classical
  have h := hctl n (fun i => if i ∈ s then u i else a)
    (fun i => if i ∈ s then v i else a) (by
      intro i
      dsimp only
      split_ifs with hi
      · exact huv i
      · exact ⟨le_rfl,le_rfl,hab⟩) (by
      intro i _ j _ hij
      dsimp only [Function.onFun]
      split_ifs with hi hj
      · exact hdis (mem_univ i) (mem_univ j) hij
      all_goals simp) (by
        have he : (fun i => ENNReal.ofReal ((if i ∈ s then v i else a) -
            if i ∈ s then u i else a)) =
            fun i => if i ∈ s then ENNReal.ofReal (v i-u i) else 0 := by
          funext i
          split_ifs <;> simp
        simpa only [he,Finset.sum_ite_mem,Finset.univ_inter] using hlen)
  have he : (fun i => (‖F (if i ∈ s then v i else a)-F (if i ∈ s then u i else a)‖₊ : ℝ≥0∞)) =
      fun i => if i ∈ s then (‖F (v i)-F (u i)‖₊ : ℝ≥0∞) else 0 := by
    funext i
    split_ifs <;> simp
  simpa only [he,Finset.sum_ite_mem,Finset.univ_inter] using h

private theorem zero_derivative_local_bound {F : ℝ → ℂ} {x c : ℝ}
    (hx : HasDerivAt F 0 x) (hc : 0 < c) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Metric.closedBall x r, ‖F y-F x‖ ≤ c*|y-x| := by
  have h := (hasDerivAt_iff_isLittleO.mp hx).bound hc
  simp only [smul_zero, sub_zero, Real.norm_eq_abs] at h
  obtain ⟨r,hr,hh⟩ := Metric.nhds_basis_closedBall.mem_iff.mp h
  exact ⟨r,hr,hh⟩

/-- Literal local absolute continuity rules out a singular component: an
almost-everywhere zero derivative forces equality at any two positive points.
The proof uses fine tagged partitions; AC controls intervals tagged in a null
exceptional set and the derivative controls all remaining intervals. -/
theorem PositiveRayLocallyAbsolutelyContinuous.eq_of_ae_hasDerivAt_zero
    {F : ℝ → ℂ} (hF : PositiveRayLocallyAbsolutelyContinuous F)
    (hder : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), HasDerivAt F 0 t)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) : F b = F a := by
  classical
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hε2 : 0 < ε/2 := half_pos hε
  obtain ⟨δ,hδ,hctl⟩ := hF a b ha (ENNReal.ofReal (ε/2))
    (ne_of_gt (ENNReal.ofReal_pos.mpr hε2))
  let N := {t : ℝ | t ∈ Icc a b ∧ ¬ HasDerivAt F 0 t}
  have hN : volume N = 0 := by
    have hh := (ae_restrict_iff' measurableSet_Ioi).mp hder
    apply measure_mono_null _ (show volume {t | ¬ (t ∈ Ioi (0:ℝ) → HasDerivAt F 0 t)} = 0
      from hh)
    intro t ht hd
    exact ht.2 (hd (ha.trans_le ht.1.1))
  obtain ⟨U,hNU,hU,hμU⟩ := N.exists_isOpen_lt_of_lt δ (by rw [hN]; exact hδ)
  let c := ε / (2 * (b-a+1))
  have hba : 0 < b-a := sub_pos.mpr hab
  have hc : 0 < c := by dsimp [c]; positivity
  have hr : ∀ x : ℝ, ∃ r : ℝ, 0 < r ∧
      (x ∈ N → Metric.closedBall x r ⊆ U) ∧
      (x ∈ Icc a b → x ∉ N → ∀ y ∈ Metric.closedBall x r, ‖F y-F x‖ ≤ c*|y-x|) := by
    intro x
    by_cases hx : x ∈ N
    · obtain ⟨r,hr,hh⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds (hNU hx))
      exact ⟨r,hr,fun _ => hh,fun _ hn => (hn hx).elim⟩
    · by_cases hxi : x ∈ Icc a b
      · have hd : HasDerivAt F 0 x := by
          by_contra hn
          exact hx ⟨hxi,hn⟩
        obtain ⟨r,hr,hh⟩ := zero_derivative_local_bound hd hc
        exact ⟨r,hr,fun hn => (hx hn).elim,fun _ _ => hh⟩
      · exact ⟨1,zero_lt_one,fun hn => (hx hn).elim,fun hi => (hxi hi).elim⟩
  choose r hrpos hrN hrD using hr
  obtain ⟨n,u,v,ξ,huv,hdis,hsub,hlen,htel⟩ :=
    exists_real_tagged_partition hab (fun x => ⟨r x,hrpos x⟩)
  let s : Finset (Fin n) := Finset.univ.filter (fun i => ξ i ∈ N)
  have hbadlen : (∑ i ∈ s, ENNReal.ofReal (v i-u i)) < δ := by
    have hm : (∑ i ∈ s, ENNReal.ofReal (v i-u i)) =
        volume (⋃ i ∈ s, Ioc (u i) (v i)) := by
      rw [measure_biUnion_finset (fun i _ j _ hij => hdis (mem_univ i) (mem_univ j) hij)
        (fun _ _ => measurableSet_Ioc)]
      simp only [Real.volume_Ioc]
    rw [hm]
    apply lt_of_le_of_lt (measure_mono ?_) hμU
    intro t ht
    obtain ⟨i,his,hti⟩ := mem_iUnion₂.mp ht
    exact hrN (ξ i) (Finset.mem_filter.mp his).2 (hsub i (Ioc_subset_Icc_self hti))
  have hbad := ac_control_subfamily hab.le hctl u v s
    (fun i => ⟨(huv i).1,(huv i).2.1.le,(huv i).2.2.1⟩) hdis hbadlen
  have hbadreal : (∑ i ∈ s, ‖F (v i)-F (u i)‖) < ε/2 := by
    simp_rw [← ENNReal.ofReal_coe_nnreal] at hbad
    change (∑ i ∈ s, ENNReal.ofReal ‖F (v i)-F (u i)‖) < ENNReal.ofReal (ε/2) at hbad
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _),
      ENNReal.ofReal_lt_ofReal_iff hε2] at hbad
    exact hbad
  have hgood : ∀ i ∈ Finset.univ \ s, ‖F (v i)-F (u i)‖ ≤ c*(v i-u i) := by
    intro i hi
    have hn : ξ i ∉ N := by simpa [s] using (Finset.mem_sdiff.mp hi).2
    have hξ : ξ i ∈ Icc a b :=
      ⟨(huv i).1.trans (huv i).2.2.2.1,(huv i).2.2.2.2.trans (huv i).2.2.1⟩
    have hv := hrD (ξ i) hξ hn (v i) (hsub i (right_mem_Icc.mpr (huv i).2.1.le))
    have hu := hrD (ξ i) hξ hn (u i) (hsub i (left_mem_Icc.mpr (huv i).2.1.le))
    rw [abs_of_nonneg (sub_nonneg.mpr (huv i).2.2.2.2)] at hv
    rw [abs_of_nonpos (sub_nonpos.mpr (huv i).2.2.2.1)] at hu
    have ht := norm_sub_le_norm_sub_add_norm_sub (F (v i)) (F (ξ i)) (F (u i))
    rw [norm_sub_rev (F (ξ i)) (F (u i))] at ht
    linarith
  have hgoodsum : (∑ i ∈ Finset.univ \ s, ‖F (v i)-F (u i)‖) ≤ c*(b-a) := by
    calc
      _ ≤ ∑ i ∈ Finset.univ \ s, c*(v i-u i) := Finset.sum_le_sum hgood
      _ ≤ ∑ i : Fin n, c*(v i-u i) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset) (fun i _ _ =>
          mul_nonneg hc.le (sub_nonneg.mpr (huv i).2.1.le))
      _ = _ := by rw [← Finset.mul_sum,hlen]
  have hcε : c*(b-a) < ε/2 := by
    dsimp [c]
    have hb : 0 < b-a+1 := by linarith
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(b-a+1))).mpr
    nlinarith
  have hsum : (∑ i : Fin n, ‖F (v i)-F (u i)‖) < ε := by
    have hh := Finset.sum_sdiff (Finset.subset_univ s) (f := fun i => ‖F (v i)-F (u i)‖)
    linarith
  have hnorm := norm_sum_le Finset.univ (fun i => F (v i)-F (u i))
  rw [htel F] at hnorm
  simpa only [zero_add] using (hnorm.trans hsum.le)

end
end Sigma
