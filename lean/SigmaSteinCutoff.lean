import SigmaStein
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

def steinBump : ContDiffBump (0 : ℝ) := ⟨1,2,by norm_num,by norm_num⟩
def steinCutoff (R t : ℝ) : ℝ := steinBump (t/R)
def steinCutoffSlope (R t : ℝ) : ℝ := (t/R) * deriv (steinBump : ℝ → ℝ) (t/R)
def steinPolynomialTest (k : ℕ) (R t : ℝ) : ℝ := t^k * (steinCutoff R t)^2

theorem steinCutoff_bounds (R t : ℝ) : 0 ≤ steinCutoff R t ∧ steinCutoff R t ≤ 1 :=
  ⟨steinBump.nonneg,steinBump.le_one⟩

theorem steinCutoff_one {R t : ℝ} (hR : 0 < R) (ht : |t| ≤ R) : steinCutoff R t = 1 := by
  apply steinBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_div, abs_of_pos hR]
  change |t|/R ≤ 1
  exact (div_le_one hR).mpr ht

theorem steinCutoff_contDiff (R : ℝ) : ContDiff ℝ ∞ (steinCutoff R) :=
  steinBump.contDiff.comp (contDiff_id.div_const R)

theorem steinCutoff_hasCompactSupport {R : ℝ} (hR : 0 < R) : HasCompactSupport (steinCutoff R) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (-2*R) (2*R)))
  intro t ht
  have hmem : t/R ∈ Function.support (steinBump : ℝ → ℝ) := ht
  rw [steinBump.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, abs_div, abs_of_pos hR] at hmem
  change |t|/R < 2 at hmem
  have hh : |t| < 2*R := (div_lt_iff₀ hR).mp hmem
  constructor
  · linarith [(abs_lt.mp hh).1]
  · exact (abs_lt.mp hh).2.le

theorem steinCutoffSlope_uniform_bound : ∃ K > 0, ∀ R t : ℝ, |steinCutoffSlope R t| ≤ K := by
  have hc : Continuous (fun t : ℝ => t*deriv (steinBump : ℝ → ℝ) t) :=
    continuous_id.mul ((steinBump.contDiff : ContDiff ℝ ∞ (steinBump : ℝ → ℝ)).continuous_deriv (by simp))
  have hs : HasCompactSupport (fun t : ℝ => t*deriv (steinBump : ℝ → ℝ) t) :=
    steinBump.hasCompactSupport.deriv.mul_left
  obtain ⟨B,hB⟩ := (hs.abs.isCompact_range hc.abs).bddAbove
  refine ⟨|B|+1,by positivity,?_⟩
  intro R t
  exact le_trans (hB (mem_range_self (t/R))) (by linarith [le_abs_self B])

theorem steinPolynomialTest_contDiff (k : ℕ) (R : ℝ) : ContDiff ℝ ∞ (steinPolynomialTest k R) :=
  (contDiff_id.pow k).mul ((steinCutoff_contDiff R).pow 2)

theorem steinPolynomialTest_hasCompactSupport (k : ℕ) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (steinPolynomialTest k R) := by
  have hh : HasCompactSupport (fun t => steinCutoff R t * steinCutoff R t) :=
    (steinCutoff_hasCompactSupport hR).mul_right
  convert (HasCompactSupport.mul_left (f := fun t : ℝ => t^k) hh) using 1
  ext t
  simp only [steinPolynomialTest, Pi.mul_apply, pow_two]

theorem steinPolynomialTest_expression (k : ℕ) (R t : ℝ) :
    t*deriv (steinPolynomialTest k R) t+(2-t)*steinPolynomialTest k R t =
      ((k : ℝ)+2)*t^k*(steinCutoff R t)^2-t^(k+1)*(steinCutoff R t)^2+
        2*t^k*steinCutoff R t*steinCutoffSlope R t := by
  have hcut : HasDerivAt (steinCutoff R) (deriv (steinBump : ℝ → ℝ) (t/R) / R) t := by
    simpa [steinCutoff, div_eq_mul_inv] using
      (((steinBump.contDiff : ContDiff ℝ ∞ (steinBump : ℝ → ℝ)).differentiable (by simp) (t/R)).hasDerivAt.comp t ((hasDerivAt_id t).div_const R))
  have hd := ((hasDerivAt_id t).pow k).mul (hcut.pow 2)
  change HasDerivAt (steinPolynomialTest k R) _ t at hd
  rw [hd.deriv]
  unfold steinPolynomialTest steinCutoffSlope
  cases k with
  | zero => norm_num; ring
  | succ k => simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ, id_eq]; ring

end
end Sigma
