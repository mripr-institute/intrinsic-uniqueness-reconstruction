import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Topology.Sequences

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem selfadjoint_square_residual_bound (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (x : H) (hx : ‖x‖ ≤ 1) :
    ‖T (T x) - (‖T‖^2 : ℂ) • x‖^2 ≤ ‖T‖^2 * (‖T‖^2 - ‖T x‖^2) := by
  have hi : (@inner ℂ H _ (T (T x)) x).re = ‖T x‖^2 := by
    have hh := T.apply_norm_sq_eq_inner_adjoint_left x
    rw [← ContinuousLinearMap.star_eq_adjoint, hT.star_eq] at hh
    exact hh.symm
  have ht := T.le_opNorm (T x)
  have ht2 : ‖T (T x)‖^2 ≤ ‖T‖^2 * ‖T x‖^2 := by
    nlinarith [norm_nonneg (T (T x)), norm_nonneg (T x), norm_nonneg T]
  have hx2 : ‖x‖^2 ≤ 1 := by nlinarith [norm_nonneg x]
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul]
  change ‖T (T x)‖^2 - 2 * (((‖T‖ : ℂ)^2) * (@inner ℂ H _ (T (T x)) x)).re +
    (‖(‖T‖ : ℂ)^2‖ * ‖x‖)^2 ≤ _
  rw [← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    hi, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖T‖)]
  nlinarith [mul_nonneg (sq_nonneg (‖T‖^2)) (sub_nonneg.mpr hx2)]

omit [CompleteSpace H] in
theorem compact_operator_norm_max_closure (T : H →L[ℂ] H) (hc : IsCompactOperator T) :
    ∃ y ∈ closure (T '' Metric.closedBall (0 : H) 1), ‖y‖ = ‖T‖ := by
  have hc' := hc.isCompact_closure_image_closedBall (f := T.toLinearMap) 1
  have hz : (0 : H) ∈ closure (T '' Metric.closedBall (0 : H) 1) := by
    apply subset_closure
    exact ⟨0, by simp, by simp⟩
  obtain ⟨y, hy, hmax⟩ := hc'.exists_isMaxOn ⟨0, hz⟩ continuous_norm.continuousOn
  refine ⟨y, hy, le_antisymm ?_ ?_⟩
  · have hsub : T '' Metric.closedBall (0 : H) 1 ⊆ Metric.closedBall 0 ‖T‖ := by
      rintro _ ⟨x, hx, rfl⟩
      simpa using T.unit_le_opNorm x (by simpa using hx)
    have hclosed : IsClosed (Metric.closedBall (0 : H) ‖T‖) := by
      simpa [Metric.closedBall, dist_eq_norm] using
        (isClosed_le (continuous_norm : Continuous (fun x : H => ‖x‖)) continuous_const)
    have hcl := closure_minimal hsub hclosed
    simpa using hcl hy
  · apply T.opNorm_le_bound (norm_nonneg y)
    intro x
    by_cases hx : x = 0
    · simp [hx]
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hm : ((‖x‖⁻¹ : ℝ) : ℂ) • x ∈ Metric.closedBall (0 : H) 1 := by
      simp [norm_smul, inv_mul_cancel₀ hn.ne']
    have hh := hmax (subset_closure ⟨_, hm, rfl⟩)
    have hh' : ‖x‖⁻¹ * ‖T x‖ ≤ ‖y‖ := by
      simpa [map_smul, norm_smul] using hh
    exact (div_le_iff₀ hn).mp (by simpa [div_eq_mul_inv, mul_comm] using hh')

theorem compact_selfadjoint_square_eigenvector (T : H →L[ℂ] H)
    (hT : IsSelfAdjoint T) (hc : IsCompactOperator T) (hne : T ≠ 0) :
    ∃ y : H, y ≠ 0 ∧ T (T y) = (‖T‖^2 : ℂ) • y := by
  obtain ⟨y, hy, hyn⟩ := compact_operator_norm_max_closure T hc
  have hr : 0 < ‖T‖ := norm_pos_iff.mpr hne
  have hyne : y ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hyn
    linarith
  obtain ⟨z, hz, hzy⟩ := mem_closure_iff_seq_limit.mp hy
  choose x hx htx using hz
  have hxy : Tendsto (fun n => T (x n)) atTop (𝓝 y) := by
    simpa only [htx] using hzy
  have hxnorm (n : ℕ) : ‖x n‖ ≤ 1 := by simpa using hx n
  have hsq : Tendsto (fun n => ‖T (T (x n)) - (‖T‖^2 : ℂ) • x n‖^2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) (fun n => selfadjoint_square_residual_bound T hT _ (hxnorm n))
    have hh := (tendsto_const_nhds (x := ‖T‖^2)).mul
      ((tendsto_const_nhds (x := ‖T‖^2)).sub (hxy.norm.pow 2))
    simpa [hyn] using hh
  have hres : Tendsto (fun n => T (T (x n)) - (‖T‖^2 : ℂ) • x n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hh := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh
  have hzero : Tendsto (fun n => T (T (T (x n))) - (‖T‖^2 : ℂ) • T (x n))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_sub, map_smul, map_zero] using T.continuous.tendsto 0 |>.comp hres
  have hlim : Tendsto (fun n => T (T (T (x n))) - (‖T‖^2 : ℂ) • T (x n))
      atTop (𝓝 (T (T y) - (‖T‖^2 : ℂ) • y)) :=
    ((T.continuous.tendsto (T y)).comp ((T.continuous.tendsto y).comp hxy)).sub
      (tendsto_const_nhds.smul hxy)
  exact ⟨y, hyne, sub_eq_zero.mp (tendsto_nhds_unique hlim hzero)⟩

/-- A nonzero compact self-adjoint operator has a nonzero real eigenvalue.
Compactness is the native compact-operator predicate; neither norm attainment
nor an eigenvector is assumed. -/
theorem compact_selfadjoint_exists_eigenvector (T : H →L[ℂ] H)
    (hT : IsSelfAdjoint T) (hc : IsCompactOperator T) (hne : T ≠ 0) :
    ∃ (r : ℝ) (x : H), r ≠ 0 ∧ x ≠ 0 ∧ T x = (r : ℂ) • x := by
  obtain ⟨y, hyne, hy⟩ := compact_selfadjoint_square_eigenvector T hT hc hne
  have hr : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  by_cases hv : T y + (‖T‖ : ℂ) • y = 0
  · refine ⟨-‖T‖, y, neg_ne_zero.mpr hr, hyne, ?_⟩
    have hh := eq_neg_of_add_eq_zero_left hv
    simpa only [Complex.ofReal_neg, neg_smul] using hh
  · refine ⟨‖T‖, T y + (‖T‖ : ℂ) • y, hr, hv, ?_⟩
    simp only [map_add, map_smul, hy, smul_add, smul_smul, pow_two]
    exact add_comm _ _

end
end Sigma
