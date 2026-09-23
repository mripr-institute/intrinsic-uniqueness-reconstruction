import SigmaOpLaguerreResolvent
import Mathlib.Analysis.Normed.Operator.Compact

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology

def laguerreRankOne (n : ℕ) (b : ℝ) :
    LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert :=
  (innerSL ℂ (laguerreHilbertBasis n)).smulRight ((b:ℂ) • laguerreHilbertBasis n)

theorem laguerre_rank_one_coordinate (n k : ℕ) (b : ℝ) (x : LaguerreWeightedHilbert) :
    laguerreHilbertBasis.repr (laguerreRankOne n b x) k =
      if n = k then (b:ℂ)*laguerreHilbertBasis.repr x k else 0 := by
  simp only [laguerreRankOne, ContinuousLinearMap.smulRight_apply, map_smul,
    HilbertBasis.repr_self, lp.coeFn_smul, Pi.smul_apply, lp.single_apply, smul_eq_mul]
  by_cases h : n = k
  · subst k
    rw [HilbertBasis.repr_apply_apply]
    simp [mul_comm]
  · simp [h, Ne.symm h]

theorem laguerre_rank_one_compact (n : ℕ) (b : ℝ) :
    IsCompactOperator (laguerreRankOne n b) := by
  have hc : IsCompactOperator (fun z : ℂ => z) :=
    ⟨Metric.closedBall 0 1, isCompact_closedBall 0 1,
      Metric.closedBall_mem_nhds 0 zero_lt_one⟩
  have hi := hc.comp_clm (innerSL ℂ (laguerreHilbertBasis n))
  exact hi.continuous_comp (continuous_id.smul continuous_const)

def laguerreResolventTruncation (α : ℝ) (N : ℕ) :
    LaguerreWeightedHilbert →L[ℂ] LaguerreWeightedHilbert :=
  ∑ n ∈ Finset.range N, laguerreRankOne n ((n:ℝ)+α)⁻¹

theorem laguerre_resolvent_truncation_coordinate (α : ℝ) (N k : ℕ)
    (x : LaguerreWeightedHilbert) :
    laguerreHilbertBasis.repr (laguerreResolventTruncation α N x) k =
      if k < N then (((k:ℝ)+α)⁻¹:ℂ)*laguerreHilbertBasis.repr x k else 0 := by
  simp only [laguerreResolventTruncation, ContinuousLinearMap.sum_apply, map_sum,
    lp.coeFn_sum, Finset.sum_apply, laguerre_rank_one_coordinate]
  simp

theorem laguerre_resolvent_truncation_compact (α : ℝ) (N : ℕ) :
    IsCompactOperator (laguerreResolventTruncation α N) := by
  have h (s : Finset ℕ) : IsCompactOperator
      (∑ n ∈ s, laguerreRankOne n ((n:ℝ)+α)⁻¹ : LaguerreWeightedHilbert →L[ℂ] _) := by
    induction s using Finset.induction_on with
    | empty => simpa using (isCompactOperator_zero (M₁ := LaguerreWeightedHilbert)
        (M₂ := LaguerreWeightedHilbert))
    | @insert n s hn ih =>
      simpa only [Finset.sum_insert hn, ContinuousLinearMap.coe_add] using
        (laguerre_rank_one_compact n ((n:ℝ)+α)⁻¹).add ih
  exact h _

theorem laguerre_resolvent_tail_bound (α : ℝ) (hα : 0 < α) (N n : ℕ) :
    |if n < N then 0 else ((n:ℝ)+α)⁻¹| ≤ ((N:ℝ)+α)⁻¹ := by
  split_ifs with h
  · simp only [abs_zero]
    positivity
  · rw [abs_of_pos (by positivity)]
    apply inv_anti₀ (by positivity)
    exact add_le_add_right (Nat.cast_le.mpr (Nat.le_of_not_gt h)) α

theorem laguerre_resolvent_truncation_error (α : ℝ) (hα : 0 < α) (N : ℕ) :
    ‖laguerreResolvent α hα-laguerreResolventTruncation α N‖ ≤ ((N:ℝ)+α)⁻¹ := by
  let b : ℕ → ℝ := fun n => if n < N then 0 else ((n:ℝ)+α)⁻¹
  have he : laguerreResolvent α hα-laguerreResolventTruncation α N =
      laguerreBoundedDiagonal b ((N:ℝ)+α)⁻¹ (by positivity)
        (laguerre_resolvent_tail_bound α hα N) := by
    apply ContinuousLinearMap.ext
    intro x
    apply laguerreHilbertBasis.repr.injective
    apply lp.ext
    funext n
    change laguerreHilbertBasis.repr (laguerreResolvent α hα x-
      laguerreResolventTruncation α N x) n = _
    rw [map_sub]
    simp only [lp.coeFn_sub, Pi.sub_apply, laguerre_resolvent_coordinate,
      laguerre_resolvent_truncation_coordinate, laguerre_bounded_diagonal_coordinate, b]
    split_ifs <;> simp
  rw [he]
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (laguerre_bounded_diagonal_norm _ _ _ _)

theorem laguerre_resolvent_truncation_tendsto (α : ℝ) (hα : 0 < α) :
    Tendsto (laguerreResolventTruncation α) atTop (𝓝 (laguerreResolvent α hα)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hi : Tendsto (fun N : ℕ => ((N:ℝ)+α)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop α tendsto_natCast_atTop_atTop)
  exact squeeze_zero (fun N => norm_nonneg _) (fun N => by
    rw [norm_sub_rev]
    exact laguerre_resolvent_truncation_error α hα N) hi

/-- Compactness on the original weighted L² space, obtained by operator-norm
approximation by genuinely finite-rank operators. -/
theorem laguerre_resolvent_compact (α : ℝ) (hα : 0 < α) :
    IsCompactOperator (laguerreResolvent α hα) :=
  isCompactOperator_of_tendsto (laguerre_resolvent_truncation_tendsto α hα)
    (Eventually.of_forall (laguerre_resolvent_truncation_compact α))

end
end Sigma
