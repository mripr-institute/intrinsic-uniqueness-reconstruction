import SigmaFenchelConverseConvex

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology

/-- The exact single raised-point countermodel from final:C5. -/
def raisedIntrinsic (t : ℝ) : EReal :=
  if t = 2 then ((I 2 + 1 : ℝ) : EReal) else extendedIntrinsic t

theorem raised_intrinsic_dominates : extendedIntrinsic ≤ raisedIntrinsic := by
  intro t
  by_cases ht : t = 2
  · subst t
    simp only [raisedIntrinsic, if_pos rfl, extendedIntrinsic, show (0 : ℝ) < 2 by norm_num, if_true,
      EReal.coe_le_coe_iff]
    linarith
  · simp [raisedIntrinsic, ht]

theorem raised_intrinsic_not_equal : raisedIntrinsic ≠ extendedIntrinsic := by
  intro h
  have hh := congrFun h 2
  simp only [raisedIntrinsic, if_pos rfl, extendedIntrinsic, show (0 : ℝ) < 2 by norm_num, if_true,
    EReal.coe_eq_coe_iff] at hh
  linarith

/-- The one modified objective value is recovered as a limit from punctured neighborhoods. -/
theorem raised_intrinsic_objective_two_le (θ : ℝ) :
    ((θ*2-I 2 : ℝ) : EReal) ≤ fullFenchelConjugate raisedIntrinsic θ := by
  have hc : ContinuousAt (fun t : ℝ => ((θ*t-I t : ℝ) : EReal)) 2 :=
    continuous_coe_real_ereal.continuousAt.comp
      (((hasDerivAt_id (2 : ℝ)).const_mul θ).sub
        (SigmaBase.potential_hasDerivAt (show (0 : ℝ) < 2 by norm_num))).continuousAt
  apply le_of_tendsto (hc.tendsto.mono_left
    (show 𝓝[≠] (2 : ℝ) ≤ 𝓝 2 from nhdsWithin_le_nhds))
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds (show (0 : ℝ) < 2 by norm_num))] with t hne ht
  change t ≠ 2 at hne
  change 0 < t at ht
  have hh := le_iSup (fun t : ℝ => ((θ*t : ℝ) : EReal) - raisedIntrinsic t) t
  simpa only [raisedIntrinsic, if_neg hne, extendedIntrinsic, if_pos ht, ← EReal.coe_sub] using hh

theorem raised_intrinsic_full_conjugate :
    fullFenchelConjugate raisedIntrinsic = intrinsicConjugateTarget := by
  rw [← extended_intrinsic_full_conjugate]
  funext θ
  apply le_antisymm
  · apply iSup_le
    intro t
    exact (EReal.sub_le_sub le_rfl (raised_intrinsic_dominates t)).trans
      (le_iSup (fun t : ℝ => ((θ*t : ℝ) : EReal) - extendedIntrinsic t) t)
  · apply iSup_le
    intro t
    by_cases ht : t = 2
    · subst t
      simpa only [extendedIntrinsic, show (0 : ℝ) < 2 by norm_num, if_true, ← EReal.coe_sub]
        using raised_intrinsic_objective_two_le θ
    · have hh := le_iSup (fun t : ℝ => ((θ*t : ℝ) : EReal) - raisedIntrinsic t) t
      simpa only [raisedIntrinsic, if_neg ht] using hh

theorem raised_intrinsic_not_lower_semicontinuous_at_two :
    ¬ LowerSemicontinuousWithinAt raisedIntrinsic (Ioi 0) 2 := by
  intro hl
  have he := fenchel_lower_semicontinuous_at_identifies raisedIntrinsic
    raised_intrinsic_full_conjugate (show (0 : ℝ) < 2 by norm_num) hl
  simp only [raisedIntrinsic, if_pos rfl, if_true, EReal.coe_eq_coe_iff] at he
  linarith

theorem raised_intrinsic_not_lower_semicontinuous :
    ¬ LowerSemicontinuousOn raisedIntrinsic (Ioi 0) := by
  intro hl
  exact raised_intrinsic_not_equal
    (fenchel_lower_semicontinuous_identifies raisedIntrinsic raised_intrinsic_full_conjugate hl)

theorem raised_intrinsic_not_convex : ¬ ExtendedConvex raisedIntrinsic := by
  intro hv
  exact raised_intrinsic_not_equal
    (fenchel_convex_identifies raisedIntrinsic raised_intrinsic_full_conjugate hv)

/-- The complete no-regularity counterexample, including its actual full conjugate. -/
theorem legendre_target_without_regularity_countermodel :
    fullFenchelConjugate raisedIntrinsic = intrinsicConjugateTarget ∧
      raisedIntrinsic ≠ extendedIntrinsic ∧
      ¬ LowerSemicontinuousOn raisedIntrinsic (Ioi 0) ∧ ¬ ExtendedConvex raisedIntrinsic :=
  ⟨raised_intrinsic_full_conjugate, raised_intrinsic_not_equal,
    raised_intrinsic_not_lower_semicontinuous, raised_intrinsic_not_convex⟩

end
end Sigma
