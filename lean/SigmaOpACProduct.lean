import SigmaOpACFundamental

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal NNReal

theorem PositiveRayLocallyAbsolutelyContinuous.congr
    {F G : ℝ → ℂ} (hF : PositiveRayLocallyAbsolutelyContinuous F)
    (he : EqOn G F (Ioi 0)) : PositiveRayLocallyAbsolutelyContinuous G := by
  intro a b ha ε hε
  obtain ⟨δ,hδ,hc⟩ := hF a b ha ε hε
  refine ⟨δ,hδ,fun n u v huv hdis hlen => ?_⟩
  have h := hc n u v huv hdis hlen
  convert h using 2
  rename_i i _
  rw [he (ha.trans_le ((huv i).1.trans (huv i).2.1)),he (ha.trans_le (huv i).1)]

theorem PositiveRayLocallyAbsolutelyContinuous.const_add
    {F : ℝ → ℂ} (hF : PositiveRayLocallyAbsolutelyContinuous F) (c : ℂ) :
    PositiveRayLocallyAbsolutelyContinuous (fun t => c+F t) := by
  intro a b ha ε hε
  obtain ⟨δ,hδ,hc⟩ := hF a b ha ε hε
  refine ⟨δ,hδ,fun n u v huv hdis hlen => ?_⟩
  simpa only [add_sub_add_left_eq_sub] using hc n u v huv hdis hlen

theorem smooth_positive_locally_ac {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) :
    PositiveRayLocallyAbsolutelyContinuous F := by
  have hg : LocallyIntegrableOn (deriv F) (Ioi 0) volume :=
    (hF.continuous_deriv (by simp)).continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hP : PositiveRayLocallyAbsolutelyContinuous (fun t => ∫ s in (1:ℝ)..t, deriv F s) := by
    intro l r hl ε hε
    exact positive_primitive_absolute_continuity (deriv F) hg (by norm_num) hl ε hε
  apply (hP.const_add (F 1)).congr
  intro t _
  dsimp only
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun s _ => hF.differentiable (by simp) s)
    ((hF.continuous_deriv (by simp)).intervalIntegrable 1 t)]
  abel

theorem PositiveRayLocallyAbsolutelyContinuous.conj
    {F : ℝ → ℂ} (hF : PositiveRayLocallyAbsolutelyContinuous F) :
    PositiveRayLocallyAbsolutelyContinuous (fun t => starRingEnd ℂ (F t)) := by
  intro a b ha ε hε
  obtain ⟨δ,hδ,hc⟩ := hF a b ha ε hε
  refine ⟨δ,hδ,fun n u v huv hdis hlen => ?_⟩
  simpa only [← map_sub,RCLike.nnnorm_conj] using hc n u v huv hdis hlen

theorem PositiveRayLocallyAbsolutelyContinuous.mul
    {F G : ℝ → ℂ} (hF : PositiveRayLocallyAbsolutelyContinuous F)
    (hG : PositiveRayLocallyAbsolutelyContinuous G) :
    PositiveRayLocallyAbsolutelyContinuous (fun t => F t*G t) := by
  intro a b ha ε hε
  have hsubset : Icc a b ⊆ Ioi 0 := fun t ht => ha.trans_le ht.1
  obtain ⟨CF,hCF⟩ := (isCompact_Icc : IsCompact (Icc a b)).bddAbove_image
    ((hF.continuousOn.mono hsubset).norm)
  obtain ⟨CG,hCG⟩ := (isCompact_Icc : IsCompact (Icc a b)).bddAbove_image
    ((hG.continuousOn.mono hsubset).norm)
  let K := max 1 (max CF CG)
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hFb (t : ℝ) (ht : t ∈ Icc a b) : ‖F t‖ ≤ K :=
    (hCF (mem_image_of_mem _ ht)).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hGb (t : ℝ) (ht : t ∈ Icc a b) : ‖G t‖ ≤ K :=
    (hCG (mem_image_of_mem _ ht)).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨e,_,hepos,heε⟩ := ENNReal.lt_iff_exists_real_btwn.mp (pos_iff_ne_zero.mpr hε)
  have hep : 0 < e := ENNReal.ofReal_pos.mp hepos
  let q := e/(2*K)
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨δF,hδF,hcF⟩ := hF a b ha (ENNReal.ofReal q) (ne_of_gt (ENNReal.ofReal_pos.mpr hq))
  obtain ⟨δG,hδG,hcG⟩ := hG a b ha (ENNReal.ofReal q) (ne_of_gt (ENNReal.ofReal_pos.mpr hq))
  refine ⟨min δF δG,lt_min hδF hδG,?_⟩
  intro n u v huv hdis hlen
  have hf := hcF n u v huv hdis (hlen.trans_le (min_le_left _ _))
  have hg := hcG n u v huv hdis (hlen.trans_le (min_le_right _ _))
  have sum_lt {H : ℝ → ℂ} (hh : (∑ i, (‖H (v i)-H (u i)‖₊ : ℝ≥0∞)) < ENNReal.ofReal q) :
      (∑ i, ‖H (v i)-H (u i)‖) < q := by
    simp_rw [← ENNReal.ofReal_coe_nnreal] at hh
    change (∑ i, ENNReal.ofReal ‖H (v i)-H (u i)‖) < ENNReal.ofReal q at hh
    rwa [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _),
      ENNReal.ofReal_lt_ofReal_iff hq] at hh
  have hb : (∑ i, ‖F (v i)*G (v i)-F (u i)*G (u i)‖) ≤
      K * (∑ i, ‖F (v i)-F (u i)‖) + K * (∑ i, ‖G (v i)-G (u i)‖) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hiu : u i ∈ Icc a b := ⟨(huv i).1,(huv i).2.1.trans (huv i).2.2⟩
    have hiv : v i ∈ Icc a b := ⟨(huv i).1.trans (huv i).2.1,(huv i).2.2⟩
    calc
      _ = ‖(F (v i)-F (u i))*G (v i)+F (u i)*(G (v i)-G (u i))‖ := by congr 1; ring
      _ ≤ ‖F (v i)-F (u i)‖*‖G (v i)‖ + ‖F (u i)‖*‖G (v i)-G (u i)‖ := by
        simpa only [norm_mul] using norm_add_le
          ((F (v i)-F (u i))*G (v i)) (F (u i)*(G (v i)-G (u i)))
      _ ≤ _ := by
        rw [mul_comm K ‖F (v i)-F (u i)‖]
        exact add_le_add (mul_le_mul_of_nonneg_left (hGb _ hiv) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hFb _ hiu) (norm_nonneg _))
  have heq : K*q+K*q = e := by dsimp [q]; field_simp; ring
  have hlt := hb.trans_lt (add_lt_add
    (mul_lt_mul_of_pos_left (sum_lt hf) hK) (mul_lt_mul_of_pos_left (sum_lt hg) hK))
  rw [heq] at hlt
  simp_rw [← ENNReal.ofReal_coe_nnreal]
  change (∑ i, ENNReal.ofReal ‖F (v i)*G (v i)-F (u i)*G (u i)‖) < ε
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
  exact ((ENNReal.ofReal_lt_ofReal_iff hep).mpr hlt).trans heε

end
end Sigma
