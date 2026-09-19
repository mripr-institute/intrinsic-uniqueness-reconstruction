import SigmaArithmeticBoundaries

namespace Sigma
noncomputable section

theorem unit_collision_parameter_bound : (1:ℝ)/3 < Real.log (3/2) := by
  have h := Real.log_lt_sub_one_of_pos
    (by norm_num : 0 < ((3:ℝ)/2)⁻¹) (by norm_num : ((3:ℝ)/2)⁻¹ ≠ 1)
  rw [Real.log_inv] at h
  norm_num at h
  linarith

theorem unit_collision_code_strictAnti :
    StrictAntiOn (placedCode (Real.log (3/2)) 1 0) (Set.Ici 2) := by
  have hd (x : ℝ) (hx : 2 ≤ x) :
      HasDerivAt (placedCode (Real.log (3/2)) 1 0)
        (1/(1+x)-Real.log (3/2)) x := by
    unfold placedCode
    simp only [one_mul, add_zero]
    simpa using
      (((hasDerivAt_id x).const_add 1).log
        (by linarith : 1+x ≠ 0)).sub
          ((hasDerivAt_id x).const_mul (Real.log (3/2)))
  apply strictAntiOn_of_deriv_neg (convex_Ici 2)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx2 : 2 ≤ x := by
      simp only [interior_Ici, Set.mem_Ioi] at hx
      exact hx.le
    rw [(hd x hx2).deriv]
    have hi : 1/(1+x) ≤ (1:ℝ)/3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith [unit_collision_parameter_bound]

theorem unit_collision_original_injective :
    Function.Injective (placedIntegerCode (Real.log (3/2)) 1 0) := by
  intro a b h
  have hval := unit_collision_code_strictAnti.injOn
    (show (a.val:ℝ) ∈ Set.Ici 2 by
      change 2 ≤ (a.val:ℝ)
      exact_mod_cast a.property)
    (show (b.val:ℝ) ∈ Set.Ici 2 by
      change 2 ≤ (b.val:ℝ)
      exact_mod_cast b.property) h
  apply Subtype.ext
  exact_mod_cast hval

theorem unit_collision_at_one :
    placedCode (Real.log (3/2)) 1 0 1=
      placedIntegerCode (Real.log (3/2)) 1 0 ⟨2,le_rfl⟩ := by
  unfold placedIntegerCode placedCode
  rw [Real.log_div (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
  norm_num
  ring

/-- The original placed image is genuinely injective and has its prescribed
multiplication, but its numeric index-one value already equals an original
image point. Thus the abstract unit cannot be identified with that value. -/
theorem placed_unit_collision_witness :
    ∃ μ : ℝ, 0 < μ ∧ Function.Injective (placedIntegerCode μ 1 0) ∧
      placedCode μ 1 0 1=placedIntegerCode μ 1 0 ⟨2,le_rfl⟩ := by
  exact ⟨Real.log (3/2), by linarith [unit_collision_parameter_bound],
    unit_collision_original_injective, unit_collision_at_one⟩

end
end Sigma
