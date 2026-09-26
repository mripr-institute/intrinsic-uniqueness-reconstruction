import SigmaOpDeterminantProductAnalytic
import Mathlib.Data.Set.Card

namespace Sigma
noncomputable section
open Filter Set
open scoped Topology BigOperators
variable {ι : Type*}

def determinantRootFactor (regularized : Bool) (c z : ℂ) : ℂ :=
  if regularized then c*Complex.exp (-z*c) else c

theorem determinant_root_factor_ne_zero (regularized : Bool) (c z : ℂ) (hc : c ≠ 0) :
    determinantRootFactor regularized c z ≠ 0 := by
  cases regularized <;> simp [determinantRootFactor, hc, Complex.exp_ne_zero]

theorem determinant_root_factor_differentiable (regularized : Bool) (c : ℂ) :
    Differentiable ℂ (determinantRootFactor regularized c) := by
  cases regularized
  · exact differentiable_const _
  · exact (Complex.differentiable_exp.comp (differentiable_id.neg.mul_const c)).const_mul c

theorem determinant_factor_at_root (regularized : Bool) (c z₀ z : ℂ) (h : 1+z₀*c = 0) :
    determinantFactor regularized (z*c) = (z-z₀)*determinantRootFactor regularized c z := by
  have he : 1+z*c = (z-z₀)*c := by linear_combination h
  cases regularized <;> simp only [determinantFactor, determinantRootFactor,
    Bool.false_eq_true, if_false, if_true, he] <;> ring

theorem spectral_determinant_root_set_finite (regularized : Bool) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖^(determinantSummabilityPower regularized))) (z : ℂ) :
    {i | 1+z*c i = 0}.Finite := by
  classical
  obtain ⟨S, hS⟩ := determinant_exists_finite_tail regularized c hc (‖z‖+1)
  apply S.finite_toSet.subset
  intro i hi
  by_contra hni
  have hh : ‖z*c i‖ ≤ 1/2 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (by linarith : ‖z‖ ≤ ‖z‖+1) (norm_nonneg _)).trans (hS i hni)
  exact Complex.slitPlane_ne_zero
    (Complex.mem_slitPlane_of_norm_lt_one (lt_of_le_of_lt hh (by norm_num))) hi

/-- The analytic zero multiplicity is the actual cardinality of the spectral fibre. -/
theorem spectral_determinant_zero_order (regularized : Bool) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖^(determinantSummabilityPower regularized))) (z₀ : ℂ) :
    (spectral_determinant_entire regularized c hc z₀).order =
      (Nat.card {i // 1+z₀*c i = 0} : ℕ∞) := by
  classical
  let R := ‖z₀‖+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hz : z₀ ∈ Metric.ball 0 R := by simp [R]
  obtain ⟨S, hS⟩ := determinant_exists_finite_tail regularized c hc R
  let Z := S.filter (fun i => 1+z₀*c i = 0)
  let W := S.filter (fun i => ¬ (1+z₀*c i = 0))
  have hZ : (Z : Set ι) = {i | 1+z₀*c i = 0} := by
    ext i
    simp only [Z, Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq, and_iff_right_iff_imp]
    intro hi
    by_contra hni
    have hh : ‖z₀*c i‖ ≤ 1/2 := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (by dsimp [R]; linarith) (norm_nonneg _)).trans (hS i hni)
    exact Complex.slitPlane_ne_zero
      (Complex.mem_slitPlane_of_norm_lt_one (lt_of_le_of_lt hh (by norm_num))) hi
  have hcard : Nat.card {i // 1+z₀*c i = 0} = Z.card := by
    change Nat.card ({i | 1+z₀*c i = 0} : Set ι) = Z.card
    rw [← hZ]
    simp
  rw [hcard]
  apply ((spectral_determinant_entire regularized c hc z₀).order_eq_nat_iff Z.card).mpr
  let g : ℂ → ℂ := fun z =>
    (∏ i ∈ Z, determinantRootFactor regularized (c i) z) *
      (∏ i ∈ W, determinantFactor regularized (z*c i)) *
        Complex.exp (spectralDeterminantTailLog regularized c S z)
  have hg₁ : Differentiable ℂ (fun z => ∏ i ∈ Z, determinantRootFactor regularized (c i) z) :=
    Differentiable.finset_prod (fun i _ => determinant_root_factor_differentiable regularized (c i))
  have hg₂ : Differentiable ℂ (fun z => ∏ i ∈ W, determinantFactor regularized (z*c i)) :=
    Differentiable.finset_prod (fun i _ => determinant_factor_differentiable regularized (c i))
  have hg₃ := spectral_determinant_tail_log_differentiableOn regularized c hc S R hR hS
  have hga : AnalyticAt ℂ g z₀ := by
    apply DifferentiableOn.analyticAt _ (Metric.isOpen_ball.mem_nhds hz)
    exact (hg₁.mul hg₂).differentiableOn.mul (Complex.differentiable_exp.comp_differentiableOn hg₃)
  refine ⟨g, hga, ?_, ?_⟩
  · apply mul_ne_zero (mul_ne_zero _ _) (Complex.exp_ne_zero _)
    · apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      apply determinant_root_factor_ne_zero
      intro hci
      have hh := (Finset.mem_filter.mp hi).2
      simp [hci] at hh
    · apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      exact (determinant_factor_eq_zero regularized _).not.mpr (Finset.mem_filter.mp hi).2
  · filter_upwards [Metric.isOpen_ball.mem_nhds hz] with z hz'
    rw [spectral_determinant_finite_exp regularized c hc S z (by
      intro i hi
      have hn : ‖z‖ < R := by simpa using hz'
      have hh := (mul_le_mul_of_nonneg_right hn.le (norm_nonneg (c i))).trans (hS i hi)
      exact lt_of_le_of_lt (by simpa only [norm_mul] using hh) (by norm_num))]
    have hp : (∏ i ∈ S, determinantFactor regularized (z*c i)) =
        (z-z₀)^Z.card * (∏ i ∈ Z, determinantRootFactor regularized (c i) z) *
          (∏ i ∈ W, determinantFactor regularized (z*c i)) := by
      rw [← Finset.prod_filter_mul_prod_filter_not S (fun i => 1+z₀*c i = 0)]
      change (∏ i ∈ Z, determinantFactor regularized (z*c i)) * _ = _
      congr 1
      have he : (∏ i ∈ Z, determinantFactor regularized (z*c i)) =
          ∏ i ∈ Z, ((z-z₀)*determinantRootFactor regularized (c i) z) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact determinant_factor_at_root regularized (c i) z₀ z (Finset.mem_filter.mp hi).2
      rw [he, Finset.prod_mul_distrib, Finset.prod_const]
    rw [hp]
    simp only [g, smul_eq_mul]
    ring

end
end Sigma
