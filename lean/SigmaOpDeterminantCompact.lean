import SigmaOpDeterminantNative

namespace Sigma
noncomputable section
open Filter Metric
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Native nuclearity implies compactness by its convergent rank-one expansion. -/
theorem determinant_nuclear_compact (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    IsCompactOperator T := by
  classical
  obtain ⟨u, v, _, hrep⟩ := hT
  have hfinite (S : Finset ℕ) : IsCompactOperator (∑ n ∈ S, rankOneOperator (u n) (v n) : H →L[ℂ] H) := by
    induction S using Finset.induction_on with
    | empty => simpa using (isCompactOperator_zero (M₁ := H) (M₂ := H))
    | @insert n S hn ih =>
      have hc : IsCompactOperator (fun z : ℂ => z) :=
        ⟨closedBall 0 1, isCompact_closedBall 0 1, closedBall_mem_nhds 0 zero_lt_one⟩
      have hr : IsCompactOperator (rankOneOperator (u n) (v n)) :=
        (hc.comp_clm (innerSL ℂ (v n))).continuous_comp (continuous_id.smul continuous_const)
      simpa only [Finset.sum_insert hn, ContinuousLinearMap.coe_add] using hr.add ih
  exact isCompactOperator_of_tendsto hrep (Eventually.of_forall hfinite)

/-- The energy inequality transfers precompactness of a self-adjoint square
back to the operator itself. -/
theorem determinant_selfadjoint_compact_of_square (R : H →L[ℂ] H)
    (hself : IsSelfAdjoint R) (hsquare : IsCompactOperator (R^2 : H →L[ℂ] H)) :
    IsCompactOperator R := by
  classical
  have henergy (v : H) : ‖R v‖^2 ≤ ‖v‖ * ‖(R^2) v‖ := by
    calc
      ‖R v‖^2 = (@inner ℂ H _ (R v) (R v)).re := InnerProductSpace.norm_sq_eq_inner (𝕜 := ℂ) _
      _ = (@inner ℂ H _ v ((R^2) v)).re := by
        exact congrArg Complex.re (hself.isSymmetric v (R v))
      _ ≤ ‖v‖ * ‖(R^2) v‖ := re_inner_le_norm (𝕜 := ℂ) _ _
  have ht : TotallyBounded (R '' closedBall (0 : H) 1) := by
    apply totallyBounded_of_finite_discretization
    intro ε hε
    have hδ : 0 < ε^2/8 := by positivity
    obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp
      (hsquare.isCompact_closure_image_closedBall 1).totallyBounded (ε^2/8) hδ
    letI : Fintype t := ht.fintype
    let g (x : R '' closedBall (0 : H) 1) : H := x.property.choose
    have hg (x : R '' closedBall (0 : H) 1) :
        g x ∈ closedBall (0 : H) 1 ∧ R (g x) = x.val := x.property.choose_spec
    have hcover' (x : R '' closedBall (0 : H) 1) :
        ∃ y : t, dist ((R^2) (g x)) y.val < ε^2/8 := by
      have hh := hcover (subset_closure (Set.mem_image_of_mem _ (hg x).1))
      simp only [Set.mem_iUnion, mem_ball] at hh
      obtain ⟨y, hy, hxy⟩ := hh
      exact ⟨⟨y, hy⟩, hxy⟩
    let F (x : R '' closedBall (0 : H) 1) : t := (hcover' x).choose
    refine ⟨t, inferInstance, F, ?_⟩
    intro x y hxy
    have hdx := (hcover' x).choose_spec
    have hdy := (hcover' y).choose_spec
    change dist ((R^2) (g x)) (F x).val < ε^2/8 at hdx
    change dist ((R^2) (g y)) (F y).val < ε^2/8 at hdy
    rw [hxy] at hdx
    have hs : ‖(R^2) (g x-g y)‖ < ε^2/4 := by
      rw [map_sub, ← dist_eq_norm]
      calc
        _ ≤ dist ((R^2) (g x)) (F y).val + dist (F y).val ((R^2) (g y)) := dist_triangle _ _ _
        _ < ε^2/4 := by rw [dist_comm (F y).val]; linarith
    have hgx : ‖g x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using (hg x).1
    have hgy : ‖g y‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using (hg y).1
    have hdiff : ‖g x-g y‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
    have he := henergy (g x-g y)
    have he' : ‖R (g x-g y)‖^2 ≤ 2 * ‖(R^2) (g x-g y)‖ :=
      he.trans (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _))
    rw [dist_eq_norm, ← (hg x).2, ← (hg y).2, ← map_sub]
    nlinarith [sq_nonneg (‖R (g x-g y)‖-ε)]
  change IsCompactOperator R.toLinearMap
  rw [isCompactOperator_iff_isCompact_closure_image_closedBall R.toLinearMap zero_lt_one]
  exact isCompact_of_totallyBounded_isClosed ht.closure isClosed_closure

end
end Sigma
